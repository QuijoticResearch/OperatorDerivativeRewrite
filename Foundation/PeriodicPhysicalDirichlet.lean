import Foundation.PeriodicLocalGroundHarnack
import Foundation.PeriodicWindingRate
/-! Exact native physical Dirichlet forms on the bounded measurable core.
The actual stationary edge law and Hilbert operator are retained. Removing
the temporal gauge average requires physical invariance and full boundary
integration. Both Haar energy integrands have proved genuine L1 domains. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicPhysicalDirichlet
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicPhysicalKineticReduction PeriodicLocalGroundHarnack
attribute [local irreducible] kernel boundaryHaar weight
variable {β : ℝ} (g : GroundData β)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance transition_markov : IsMarkovKernel g.transition := g.transition_markov
private instance edge_probability : IsProbabilityMeasure (edgeLaw g) := by unfold edgeLaw; infer_instance

private theorem delta_bound (f : State → ℝ) (B : ℝ) (hB : ∀ U,|f U| ≤ B) (U V : State) :
    |(f V-f U)^2| ≤ 4*|B|^2 := by
  have hd : |f V-f U| ≤ 2*|B| := by
    linarith [abs_sub (f V) (f U),hB U,hB V,le_abs_self B]
  have hp := pow_le_pow_left₀ (abs_nonneg (f V-f U)) hd 2
  rw [abs_pow]
  nlinarith

private theorem edge_integrable (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    Integrable (fun p : State × State => (f p.2-f p.1)^2) (edgeLaw g) :=
  Integrable.of_bound (((hf.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2).aestronglyMeasurable
    (4*|B|^2) (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using delta_bound f B hB p.1 p.2))

private theorem probe_integrable (f : State → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ U,|f U| ≤ B) (U : State) :
    Integrable (fun V => g.function V*(f V-f U)^2) boundaryHaar := by
  apply Integrable.of_bound (g.measurable.mul ((hf.sub measurable_const).pow_const 2)).aestronglyMeasurable
    (|g.upper| *(4*|B|^2))
  filter_upwards with V
  change ‖g.function V*(f V-f U)^2‖ ≤ |g.upper| * (4*|B|^2)
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul ((g.bounds V).2.trans (le_abs_self _)) (delta_bound f B hB U V)
    (abs_nonneg _) (abs_nonneg _)

/-- Genuine joint Haar domain of the bounded-core fixed-gauge energy. -/
theorem fixed_energy_integrable (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    Integrable (fun p : State × State => g.function p.1*
      (weight β p.1 p.2 1*(g.function p.2*(f p.2-f p.1)^2))) (boundaryHaar.prod boundaryHaar) := by
  have hw : Measurable (fun p : State × State => weight β p.1 p.2 1) :=
    (weight_joint_measurable β).comp (measurable_id.prodMk measurable_const)
  have hm : Measurable (fun p : State × State => g.function p.1*
      (weight β p.1 p.2 1*(g.function p.2*(f p.2-f p.1)^2))) :=
    (g.measurable.comp measurable_fst).mul (hw.mul ((g.measurable.comp measurable_snd).mul
      (((hf.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2)))
  apply Integrable.of_bound hm.aestronglyMeasurable
    (|g.upper| *(Real.exp (768*|β|)*(|g.upper| *(4*|B|^2))))
  filter_upwards with p
  have hpsi (U : State) : ‖g.function U‖ ≤ |g.upper| := by
    simpa only [Real.norm_eq_abs] using (g.bounds U).2.trans (le_abs_self _)
  have hweight : ‖weight β p.1 p.2 1‖ ≤ Real.exp (768*|β|) := by
    have hp : 0 < weight β p.1 p.2 1 := by unfold weight; exact Real.exp_pos _
    rw [Real.norm_eq_abs,abs_of_pos hp]
    exact (weight_bounds β p.1 p.2 1).2
  have hd : ‖(f p.2-f p.1)^2‖ ≤ 4*|B|^2 := by
    simpa only [Real.norm_eq_abs] using delta_bound f B hB p.1 p.2
  exact norm_mul_le_of_le (hpsi p.1) (norm_mul_le_of_le hweight (norm_mul_le_of_le (hpsi p.2) hd))

private theorem edge_haar (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    (∫ p : State × State,(f p.2-f p.1)^2 ∂edgeLaw g)=
      (∫ U,g.function U*(∫ V,kernel β U V*(g.function V*(f V-f U)^2) ∂boundaryHaar) ∂boundaryHaar)/
        (g.value*g.normalizer) := by
  change (∫ p : State × State,(f p.2-f p.1)^2 ∂(g.stationary ⊗ₘ g.transition))=_
  rw [Measure.integral_compProd (edge_integrable g f hf B hB),g.stationary_integral]
  simp_rw [g.transition_integral]
  have he (U : State) : g.function U^2*
      ((∫ V,kernel β U V*(g.function V*(f V-f U)^2) ∂boundaryHaar)/(g.value*g.function U))=
      (g.function U*(∫ V,kernel β U V*(g.function V*(f V-f U)^2) ∂boundaryHaar))/g.value := by
    field_simp [(g.function_pos U).ne',g.value_pos.ne']
  simp_rw [he]
  rw [integral_div]
  field_simp [g.value_pos.ne',g.normalizer_pos.ne']

private theorem physical_edge_haar (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    (∫ p : State × State,(f p.2-f p.1)^2 ∂edgeLaw g)=
      (∫ U,g.function U*(∫ V,weight β U V 1*(g.function V*(f V-f U)^2) ∂boundaryHaar) ∂boundaryHaar)/
        (g.value*g.normalizer) := by
  rw [edge_haar g f hf B hB]
  congr 1
  apply integral_congr_ae
  filter_upwards with U
  apply congrArg (fun x : ℝ => g.function U*x)
  exact invariant_transfer β U _ (g.measurable.mul ((hf.sub measurable_const).pow_const 2))
    (probe_integrable g f hf B hB U) (fun a V => by rw [g.invariant,hInv])

theorem native_fixed_gauge_dirichlet (f : State → ℝ) (hf : Measurable f)
    (hmem : MemLp f 2 g.stationary) (B : ℝ) (hB : ∀ U,|f U| ≤ B)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    SelfAdjointContractionIteration.dissipation (operator g) (hmem.toLp f)=
      (∫ U,g.function U*(∫ V,weight β U V 1*(g.function V*(f V-f U)^2) ∂boundaryHaar) ∂boundaryHaar)/
        (2*g.value*g.normalizer) := by
  rw [PeriodicWindingRate.native_dirichlet,PeriodicTransferVariation.edge_norm_square,
    physical_edge_haar g f hf B hB hInv]
  field_simp [g.value_pos.ne',g.normalizer_pos.ne']

/-- Genuine joint Haar domain after the exact kinetic/ground factorization. -/
theorem kinetic_energy_integrable (hb : 0 ≤ β) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    Integrable (fun p : State × State => kineticDensity β p.1 p.2*dressed g p.1*dressed g p.2*
      (f p.2-f p.1)^2) (boundaryHaar.prod boundaryHaar) := by
  have he : (fun p : State × State => kineticDensity β p.1 p.2*dressed g p.1*dressed g p.2*(f p.2-f p.1)^2)=
      (fun p => (g.function p.1*(weight β p.1 p.2 1*(g.function p.2*(f p.2-f p.1)^2)))/(CubeHaarUpper.laplace β^192)) := by
    funext p
    apply (eq_div_iff (pow_pos (CubeHaarUpper.laplace_pos β hb) 192).ne').mpr
    rw [weight_factor β hb p.1 p.2]
    unfold dressed
    ring
  rw [he]
  exact (fixed_energy_integrable g f hf B hB).div_const _

theorem native_kinetic_dirichlet (hb : 0 ≤ β) (f : State → ℝ) (hf : Measurable f)
    (hmem : MemLp f 2 g.stationary) (B : ℝ) (hB : ∀ U,|f U| ≤ B)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    SelfAdjointContractionIteration.dissipation (operator g) (hmem.toLp f)=
      (CubeHaarUpper.laplace β^192/(2*g.value*g.normalizer))*
        (∫ U,∫ V,kineticDensity β U V*dressed g U*dressed g V*(f V-f U)^2
          ∂boundaryHaar ∂boundaryHaar) := by
  rw [native_fixed_gauge_dirichlet g f hf hmem B hB hInv]
  have he (U : State) : g.function U*(∫ V,weight β U V 1*(g.function V*(f V-f U)^2) ∂boundaryHaar)=
      CubeHaarUpper.laplace β^192*
        (∫ V,kineticDensity β U V*dressed g U*dressed g V*(f V-f U)^2 ∂boundaryHaar) := by
    rw [← integral_const_mul,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with V
    rw [weight_factor β hb U V]
    unfold dressed
    ring
  simp_rw [he]
  rw [integral_const_mul]
  ring
end OperatorDerivativeRewrite.Foundation.PeriodicPhysicalDirichlet
