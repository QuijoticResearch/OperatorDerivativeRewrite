import Foundation.PeriodicSlabL2
import Foundation.PeriodicGroundMass

/-! Actual positive joint law of two spatial slices and their temporal links.
Its spatial-pair marginal is the native stationary Markov edge law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicSlabJoint
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2

abbrev Triple := (State × State) × Gauge

def reference : Measure Triple := (boundaryHaar.prod boundaryHaar).prod gaugeHaar
instance reference_probability : IsProbabilityMeasure reference := by unfold reference; infer_instance

variable {beta : ℝ} (g : GroundData beta)

def jointWeight (q : Triple) : ℝ :=
  weight beta q.1.1 q.1.2 q.2*(g.function q.1.1*g.function q.1.2)

theorem weight_measurable : Measurable (jointWeight g) :=
  (weight_joint_measurable beta).mul ((g.measurable.comp (measurable_fst.comp measurable_fst)).mul
    (g.measurable.comp (measurable_snd.comp measurable_fst)))

theorem weight_pos (q : Triple) : 0 < jointWeight g q :=
  mul_pos (Real.exp_pos _) (mul_pos (g.function_pos _) (g.function_pos _))

theorem weight_bound (q : Triple) :
    ‖jointWeight g q‖ ≤ Real.exp (768* |beta|)*(|g.upper| * |g.upper|) := by
  unfold jointWeight
  have hw : 0 < weight beta q.1.1 q.1.2 q.2 := Real.exp_pos _
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos hw,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul (weight_bounds beta _ _ _).2
    (mul_le_mul ((g.bounds _).2.trans (le_abs_self _)) ((g.bounds _).2.trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _))
    (by positivity) (Real.exp_pos _).le

theorem weight_integrable : Integrable (jointWeight g) reference :=
  Integrable.of_bound (weight_measurable g).aestronglyMeasurable _
    (ae_of_all _ (weight_bound g))

theorem probe_integrable (f : Triple → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ q,|f q| ≤ B) :
    Integrable (fun q => jointWeight g q*f q) reference := by
  apply Integrable.of_bound ((weight_measurable g).mul hf).aestronglyMeasurable
    ((Real.exp (768* |beta|)*(|g.upper| * |g.upper|))* |B|)
  filter_upwards with q
  change ‖jointWeight g q*f q‖ ≤ _
  rw [norm_mul]
  apply mul_le_mul (weight_bound g q) ?_ (norm_nonneg _) (by positivity)
  simpa only [Real.norm_eq_abs] using (hb q).trans (le_abs_self _)

theorem row_integral (p : State × State) :
    (∫ a,jointWeight g (p,a) ∂gaugeHaar)=kernel beta p.1 p.2*(g.function p.1*g.function p.2) := by
  unfold jointWeight kernel
  exact integral_mul_const (g.function p.1*g.function p.2) (weight beta p.1 p.2)

theorem row_probe (F : State × State → ℝ) (p : State × State) :
    (∫ a,jointWeight g (p,a)*F p ∂gaugeHaar)=
      kernel beta p.1 p.2*(g.function p.1*g.function p.2)*F p := by
  rw [integral_mul_const,row_integral]

theorem normalizer_identity : (∫ q,jointWeight g q ∂reference)=g.value*g.normalizer := by
  have hi : Integrable (fun p : State × State => kernel beta p.1 p.2*(g.function p.1*g.function p.2))
      (boundaryHaar.prod boundaryHaar) :=
    (weight_integrable g).integral_prod_left.congr (ae_of_all _ (row_integral g))
  change (∫ q,jointWeight g q ∂(boundaryHaar.prod boundaryHaar).prod gaugeHaar)=_
  rw [integral_prod _ (weight_integrable g)]
  simp_rw [row_integral]
  rw [integral_prod _ hi]
  have hp (U V : State) : kernel beta U V*(g.function U*g.function V)=
      g.function U*(kernel beta U V*g.function V) := by ring
  simp_rw [hp,integral_const_mul,g.eigen]
  have hq (U : State) : g.function U*(g.value*g.function U)=g.value*g.function U^2 := by ring
  simp_rw [hq]
  rw [integral_const_mul]
  rfl

theorem mass_identity : SignedDensityProbabilitySampling.mass reference (jointWeight g)=g.value*g.normalizer := by
  unfold SignedDensityProbabilitySampling.mass
  simp_rw [abs_of_pos (weight_pos g _)]
  exact normalizer_identity g

def tripleLaw : Measure Triple := SignedDensityProbabilitySampling.sampler reference (jointWeight g)

instance triple_probability : IsProbabilityMeasure (tripleLaw g) :=
  SignedDensityProbabilitySampling.sampler_probability reference _ (weight_integrable g)
    (by rw [mass_identity]; exact mul_pos g.value_pos g.normalizer_pos)

theorem integral_formula (f : Triple → ℝ) :
    (∫ q,f q ∂tripleLaw g)=(∫ q,jointWeight g q*f q ∂reference)/(g.value*g.normalizer) := by
  have h := YMPositiveKernel.positive_sampler_integral reference (jointWeight g) f
    (weight_measurable g) (fun q => (weight_pos g q).le)
    (by rw [mass_identity]; exact mul_pos g.value_pos g.normalizer_pos)
  rw [mass_identity] at h
  exact h

theorem triple_pairing (f h : State → ℝ) (hf : Measurable f) (hh : Measurable h)
    (B C : ℝ) (hb : ∀ U,|f U| ≤ B) (hc : ∀ U,|h U| ≤ C) :
    (∫ q,f q.1.1*h q.1.2 ∂tripleLaw g)=
      pairing beta (fun U => g.function U*f U) (fun U => g.function U*h U)/(g.value*g.normalizer) := by
  let F : State × State → ℝ := fun p => f p.1*h p.2
  have hF : Measurable F := (hf.comp measurable_fst).mul (hh.comp measurable_snd)
  have hbound (q : Triple) : |F q.1| ≤ |B| * |C| := by
    rw [abs_mul]
    exact mul_le_mul ((hb _).trans (le_abs_self _)) ((hc _).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  have hi := probe_integrable g (fun q => F q.1) (hF.comp measurable_fst) _ hbound
  have hip : Integrable (fun p : State × State =>
      kernel beta p.1 p.2*(g.function p.1*g.function p.2)*F p) (boundaryHaar.prod boundaryHaar) :=
    hi.integral_prod_left.congr (ae_of_all _ (row_probe g F))
  rw [integral_formula]
  change (∫ q,jointWeight g q*F q.1 ∂(boundaryHaar.prod boundaryHaar).prod gaugeHaar)/_=_
  rw [integral_prod _ hi]
  simp_rw [row_probe]
  rw [integral_prod _ hip]
  have hp (U V : State) : kernel beta U V*(g.function U*g.function V)*F (U,V)=
      (g.function U*f U)*(kernel beta U V*(g.function V*h V)) := by dsimp [F]; ring
  simp_rw [hp,integral_const_mul]
  rfl

theorem pair_preserving : MeasurePreserving Prod.fst (tripleLaw g) (edgeLaw g) := by
  refine ⟨measurable_fst,?_⟩
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f h
  have hf := f.continuous.measurable
  have hh := h.continuous.measurable
  have hm : Measurable (fun p : State × State => f p.1*h p.2) :=
    (hf.comp measurable_fst).mul (hh.comp measurable_snd)
  rw [integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable]
  change (∫ q,f q.1.1*h q.1.2 ∂tripleLaw g)=(∫ p,f p.1*h p.2 ∂edgeLaw g)
  rw [triple_pairing g f h hf hh ‖f‖ ‖h‖
      (fun U => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm U)
      (fun U => by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm U),
    edge_pairing g f h hf hh ‖f‖ ‖h‖
      (fun U => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm U)
      (fun U => by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm U),g.stationary_pairing]

end OperatorDerivativeRewrite.Foundation.PeriodicSlabJoint
