import Foundation.PeriodicSlabJoint
import Foundation.PeriodicGroundHarmonic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Actual two-sided ground-transform bridge

Construct the middle-slice probability kernel for the true periodic transfer.
Prove bounded-test disintegration of two actual transitions, identify their
composed endpoint density, and recover the actual stationary middle marginal.
The intermediate positive ground factor cancels; spatial Gibbs is not
substituted for the stationary law. These statements supply a conditioning
layer for local covariance work, not a local variance rate or mass-gap theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicGroundBridge
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
attribute [local irreducible] PeriodicWilsonSlab.kernel boundaryHaar

def bridgeWeight (beta : ℝ) (U W V : State) : ℝ := kernel beta U V*kernel beta V W
def normalizer (beta : ℝ) (U W : State) : ℝ := ∫ V,bridgeWeight beta U W V ∂boundaryHaar

theorem bridgeWeight_measurable (beta : ℝ) (U W : State) : Measurable (bridgeWeight beta U W) :=
  ((kernel_joint_measurable beta).comp (measurable_const.prodMk measurable_id)).mul
    ((kernel_joint_measurable beta).comp (measurable_id.prodMk measurable_const))
theorem bridgeWeight_pos (beta : ℝ) (U W V : State) : 0<bridgeWeight beta U W V :=
  mul_pos (kernel_positive beta U V) (kernel_positive beta V W)

theorem bridgeWeight_integrable (beta : ℝ) (U W : State) :
    Integrable (bridgeWeight beta U W) boundaryHaar := by
  apply Integrable.of_bound (bridgeWeight_measurable beta U W).aestronglyMeasurable
    (Real.exp (768*|beta|)^2)
  filter_upwards with V
  rw [Real.norm_eq_abs,abs_of_pos (bridgeWeight_pos beta U W V)]
  exact (mul_le_mul (kernel_bounds beta U V).2 (kernel_bounds beta V W).2
    (kernel_positive beta V W).le (Real.exp_pos _).le).trans_eq (by ring)

theorem normalizer_lower (beta : ℝ) (U W : State) : Real.exp (-768*|beta|)^2 ≤ normalizer beta U W := by
  have hpoint (V : State) : Real.exp (-768*|beta|)^2 ≤ bridgeWeight beta U W V := by
    have h := mul_le_mul (kernel_bounds beta U V).1 (kernel_bounds beta V W).1
      (Real.exp_pos _).le (kernel_positive beta U V).le
    simpa only [pow_two,bridgeWeight] using h
  have h := integral_mono (integrable_const (Real.exp (-768*|beta|)^2))
    (bridgeWeight_integrable beta U W) hpoint
  simpa only [normalizer,integral_const,probReal_univ,one_smul] using h

theorem normalizer_pos (beta : ℝ) (U W : State) : 0<normalizer beta U W :=
  (sq_pos_of_pos (Real.exp_pos _)).trans_le (normalizer_lower beta U W)

theorem mass_identity (beta : ℝ) (U W : State) :
    SignedDensityProbabilitySampling.mass boundaryHaar (bridgeWeight beta U W)=normalizer beta U W := by
  unfold SignedDensityProbabilitySampling.mass normalizer
  simp_rw [abs_of_pos (bridgeWeight_pos beta U W _)]

def law (beta : ℝ) (U W : State) : Measure State :=
  SignedDensityProbabilitySampling.sampler boundaryHaar (bridgeWeight beta U W)

instance law_probability (beta : ℝ) (U W : State) : IsProbabilityMeasure (law beta U W) :=
  SignedDensityProbabilitySampling.sampler_probability boundaryHaar _ (bridgeWeight_integrable beta U W)
    (by rw [mass_identity]; exact normalizer_pos beta U W)

theorem integral_formula (beta : ℝ) (U W : State) (f : State → ℝ) :
    (∫ V,f V ∂law beta U W)=(∫ V,bridgeWeight beta U W V*f V ∂boundaryHaar)/normalizer beta U W := by
  have h := YMPositiveKernel.positive_sampler_integral boundaryHaar (bridgeWeight beta U W) f
    (bridgeWeight_measurable beta U W) (fun V => (bridgeWeight_pos beta U W V).le)
    (by rw [mass_identity]; exact normalizer_pos beta U W)
  rw [mass_identity] at h
  exact h

theorem bridgeWeight_joint_measurable (beta : ℝ) :
    Measurable (fun q : (State × State) × State => bridgeWeight beta q.1.1 q.1.2 q.2) :=
  ((kernel_joint_measurable beta).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
    ((kernel_joint_measurable beta).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))

theorem normalizer_measurable (beta : ℝ) :
    Measurable (fun q : State × State => normalizer beta q.1 q.2) :=
  (bridgeWeight_joint_measurable beta).stronglyMeasurable.integral_prod_right.measurable

theorem law_withDensity (beta : ℝ) (U W : State) :
    law beta U W=boundaryHaar.withDensity
      (fun V => ENNReal.ofReal (bridgeWeight beta U W V/normalizer beta U W)) := by
  unfold law SignedDensityProbabilitySampling.sampler
  rw [mass_identity]
  unfold SignedAbsoluteIntegration.absoluteDensity
  simp_rw [abs_of_pos (bridgeWeight_pos beta U W _)]
  rw [← withDensity_smul _ (bridgeWeight_measurable beta U W).ennreal_ofReal]
  apply congrArg (fun f : State → ℝ≥0∞ => boundaryHaar.withDensity f)
  funext V
  change (ENNReal.ofReal (normalizer beta U W))⁻¹*ENNReal.ofReal (bridgeWeight beta U W V)=
    ENNReal.ofReal (bridgeWeight beta U W V/normalizer beta U W)
  rw [ENNReal.ofReal_div_of_pos (normalizer_pos beta U W),div_eq_mul_inv]
  exact mul_comm _ _

def bridgeKernel (beta : ℝ) : ProbabilityTheory.Kernel (State × State) State :=
  (ProbabilityTheory.Kernel.const (State × State) boundaryHaar).withDensity
    (fun q V => ENNReal.ofReal (bridgeWeight beta q.1 q.2 V/normalizer beta q.1 q.2))

theorem bridgeKernel_apply (beta : ℝ) (q : State × State) : bridgeKernel beta q=law beta q.1 q.2 := by
  have hm : Measurable (fun p : (State × State) × State =>
      ENNReal.ofReal (bridgeWeight beta p.1.1 p.1.2 p.2/normalizer beta p.1.1 p.1.2)) :=
    ((bridgeWeight_joint_measurable beta).div ((normalizer_measurable beta).comp measurable_fst)).ennreal_ofReal
  unfold bridgeKernel
  rw [ProbabilityTheory.Kernel.withDensity_apply _ hm,law_withDensity]
  rfl

instance bridgeKernel_markov (beta : ℝ) : ProbabilityTheory.IsMarkovKernel (bridgeKernel beta) := by
  constructor
  intro q
  rw [bridgeKernel_apply]
  infer_instance

variable {beta : ℝ} (d : GroundData beta)

theorem density_product (U V W : State) :
    d.density U V*d.density V W=
      bridgeWeight beta U W V*d.function W/(d.value^2*d.function U) := by
  unfold GroundData.density bridgeWeight
  field_simp [(d.function_pos U).ne',(d.function_pos V).ne',d.value_pos.ne']
  <;> ring

def twoStepDensity (U W : State) : ℝ := ∫ V,d.density U V*d.density V W ∂boundaryHaar

theorem twoStep_factor (U W : State) :
    twoStepDensity d U W=normalizer beta U W*d.function W/(d.value^2*d.function U) := by
  unfold twoStepDensity
  simp_rw [density_product]
  rw [integral_div,integral_mul_const]
  rfl

theorem twoStep_pos (U W : State) : 0<twoStepDensity d U W := by
  rw [twoStep_factor]
  exact div_pos (mul_pos (normalizer_pos beta U W) (d.function_pos W))
    (mul_pos (sq_pos_of_pos d.value_pos) (d.function_pos U))

theorem bridge_density_cancellation (U V W : State) :
    (d.density U V*d.density V W)/twoStepDensity d U W=
      bridgeWeight beta U W V/normalizer beta U W := by
  rw [density_product,twoStep_factor]
  field_simp [(normalizer_pos beta U W).ne',(d.function_pos W).ne',
    (d.function_pos U).ne',d.value_pos.ne']

theorem bridge_transition_integral (U W : State) (f : State → ℝ) :
    (∫ V,f V ∂law beta U W)=
      (∫ V,d.density U V*d.density V W*f V ∂boundaryHaar)/twoStepDensity d U W := by
  rw [integral_formula]
  have hp : (fun V => d.density U V*d.density V W*f V)=
      (fun V => (bridgeWeight beta U W V*f V)*(d.function W/(d.value^2*d.function U))) := by
    funext V
    rw [density_product]
    ring
  rw [hp,integral_mul_const,twoStep_factor]
  field_simp [(normalizer_pos beta U W).ne',(d.function_pos W).ne',
    (d.function_pos U).ne',d.value_pos.ne']
  <;> ring

private theorem transition_density_integral (U : State) (f : State → ℝ) :
    (∫ V,f V ∂d.transition U)=∫ V,d.density U V*f V ∂boundaryHaar := by
  rw [d.transition_integral,← integral_div]
  apply integral_congr_ae
  filter_upwards with V
  unfold GroundData.density
  ring

private theorem path_probe_integrable (U : State) (f h : State → ℝ)
    (hf : Measurable f) (hh : Measurable h) (B C : ℝ)
    (hb : ∀ V,|f V| ≤ B) (hc : ∀ W,|h W| ≤ C) :
    Integrable (fun p : State × State => d.density U p.1*d.density p.1 p.2*f p.1*h p.2)
      (boundaryHaar.prod boundaryHaar) := by
  obtain ⟨m,M,hm,hd⟩ := PeriodicGroundHarmonic.density_bounds d
  have hM : 0<M := (d.density_pos U U).trans_le (hd U U).2
  have hmeas : Measurable (fun p : State × State =>
      d.density U p.1*d.density p.1 p.2*f p.1*h p.2) :=
    (((d.density_measurable.comp (measurable_const.prodMk measurable_fst)).mul d.density_measurable).mul
      (hf.comp measurable_fst)).mul (hh.comp measurable_snd)
  apply Integrable.of_bound hmeas.aestronglyMeasurable (M*M*(|B| * |C|))
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_mul,
    abs_of_pos (d.density_pos U p.1),abs_of_pos (d.density_pos p.1 p.2)]
  calc
    _ ≤ M*M*|B| * |C| := by
      have hpp := mul_le_mul (hd U p.1).2 (hd p.1 p.2).2
        (d.density_pos p.1 p.2).le hM.le
      have hpf := mul_le_mul hpp ((hb p.1).trans (le_abs_self B))
        (abs_nonneg (f p.1)) (mul_nonneg hM.le hM.le)
      exact mul_le_mul hpf ((hc p.2).trans (le_abs_self C))
        (abs_nonneg (h p.2)) (mul_nonneg (mul_nonneg hM.le hM.le) (abs_nonneg B))
    _ = _ := by ring

theorem disintegration_bounded (U : State) (f h : State → ℝ)
    (hf : Measurable f) (hh : Measurable h) (B C : ℝ)
    (hb : ∀ V,|f V| ≤ B) (hc : ∀ W,|h W| ≤ C) :
    (∫ V,∫ W,f V*h W ∂d.transition V ∂d.transition U)=
      ∫ W,twoStepDensity d U W*h W*(∫ V,f V ∂law beta U W) ∂boundaryHaar := by
  let G : State → State → ℝ := fun V W => d.density U V*d.density V W*f V*h W
  have hL : (∫ V,∫ W,f V*h W ∂d.transition V ∂d.transition U)=
      ∫ V,∫ W,G V W ∂boundaryHaar ∂boundaryHaar := by
    simp_rw [transition_density_integral]
    apply integral_congr_ae
    filter_upwards with V
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with W
    dsimp [G]
    ring
  have hswap : (∫ V,∫ W,G V W ∂boundaryHaar ∂boundaryHaar)=
      ∫ W,∫ V,G V W ∂boundaryHaar ∂boundaryHaar :=
    integral_integral_swap (path_probe_integrable d U f h hf hh B C hb hc)
  rw [hL,hswap]
  apply integral_congr_ae
  filter_upwards with W
  rw [bridge_transition_integral]
  have hp : twoStepDensity d U W*h W*
      ((∫ V,d.density U V*d.density V W*f V ∂boundaryHaar)/twoStepDensity d U W)=
      (∫ V,d.density U V*d.density V W*f V ∂boundaryHaar)*h W := by
    field_simp [(twoStep_pos d U W).ne']
  rw [hp,← integral_mul_const]

theorem endpoint_density_integral (U : State) (h : State → ℝ) (hh : Measurable h)
    (C : ℝ) (hc : ∀ W,|h W| ≤ C) :
    (∫ V,∫ W,h W ∂d.transition V ∂d.transition U)=
      ∫ W,twoStepDensity d U W*h W ∂boundaryHaar := by
  simpa only [one_mul,integral_const,probReal_univ,one_smul,mul_one] using
    disintegration_bounded d U (fun _ => 1) h measurable_const hh 1 C (fun _ => by norm_num) hc

theorem composed_transition_integral (U : State) (h : State → ℝ) (hh : Measurable h)
    (C : ℝ) (hc : ∀ W,|h W| ≤ C) :
    (∫ W,h W ∂((d.transition ∘ₖ d.transition) U))=
      ∫ W,twoStepDensity d U W*h W ∂boundaryHaar := by
  letI := d.transition_markov
  have hi : Integrable h ((d.transition ∘ₖ d.transition) U) :=
    Integrable.of_bound hh.aestronglyMeasurable C (ae_of_all _ (fun W => by simpa only [Real.norm_eq_abs] using hc W))
  rw [ProbabilityTheory.Kernel.integral_comp hi]
  exact endpoint_density_integral d U h hh C hc

theorem twoStep_integral (U : State) : (∫ W,twoStepDensity d U W ∂boundaryHaar)=1 := by
  letI := d.transition_markov
  have h := composed_transition_integral d U (fun _ => 1) measurable_const 1 (fun _ => by norm_num)
  simpa only [integral_const,probReal_univ,one_smul,mul_one] using h.symm

theorem bridge_average (U : State) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ V,|f V| ≤ B) :
    (∫ W,∫ V,f V ∂law beta U W ∂((d.transition ∘ₖ d.transition) U))=
      ∫ V,f V ∂d.transition U := by
  letI := d.transition_markov
  have hmeas : Measurable (fun q : State × State => ∫ V,f V ∂bridgeKernel beta q) :=
    hf.stronglyMeasurable.integral_kernel.measurable
  have hm : Measurable (fun W => ∫ V,f V ∂law beta U W) := by
    have hraw : Measurable (fun W : State => ∫ V,f V ∂bridgeKernel beta (U,W)) :=
      hmeas.comp (measurable_const.prodMk measurable_id)
    simpa only [bridgeKernel_apply] using hraw
  have hbound (W : State) : |∫ V,f V ∂law beta U W| ≤ |B| := by
    have hnorm : ∀ᵐ V ∂law beta U W,‖f V‖ ≤ |B| :=
      ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using (hb V).trans (le_abs_self B))
    have h := norm_integral_le_of_norm_le_const hnorm
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using h
  rw [composed_transition_integral d U _ hm |B| hbound]
  have h := disintegration_bounded d U f (fun _ => 1) hf measurable_const B 1 hb (fun _ => by norm_num)
  simpa only [mul_one,integral_const,probReal_univ,one_smul] using h.symm

theorem stationary_bridge_average (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ V,|f V| ≤ B) :
    (∫ U,∫ W,∫ V,f V ∂law beta U W ∂((d.transition ∘ₖ d.transition) U) ∂d.stationary)=
      ∫ V,f V ∂d.stationary := by
  simp_rw [bridge_average d _ f hf B hb]
  exact d.transition_stationary f hf B hb

end OperatorDerivativeRewrite.Foundation.PeriodicGroundBridge
