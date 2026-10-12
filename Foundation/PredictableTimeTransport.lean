import Foundation.L2GeneratedSubspace
import Mathlib.Probability.Process.Predictable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Finite-horizon Lebesgue transport between nonnegative and real time.
The probability sigma-algebra is unchanged; no filtration completion is used. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.PredictableTimeTransport

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Lebesgue measure on [0,T], pulled back by the actual NNReal inclusion. -/
abbrev timeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).comap (fun t : ℝ≥0 => (t : ℝ))

theorem coe_measurePreserving (T : ℝ≥0) :
    MeasurePreserving (fun t : ℝ≥0 => (t : ℝ)) (timeMeasure T)
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) := by
  have he : MeasurableEmbedding (fun t : ℝ≥0 => (t : ℝ)) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  refine ⟨he.measurable, ?_⟩
  rw [he.map_comap]
  have hr : range (fun t : ℝ≥0 => (t : ℝ)) = Ici 0 := by
    ext x
    exact ⟨fun ⟨t, ht⟩ => ht ▸ t.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hr, Measure.restrict_restrict measurableSet_Ici,
    inter_eq_right.mpr (show Icc 0 (T : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)]

def coeTime (z : ℝ≥0 × Ω) : ℝ × Ω := (z.1, z.2)

theorem coeTime_measurableEmbedding : MeasurableEmbedding (coeTime (Ω := Ω)) :=
  (MeasurableEmbedding.subtype_coe measurableSet_Ici).prodMap MeasurableEmbedding.id

theorem coeTime_measurePreserving (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    MeasurePreserving coeTime ((timeMeasure T).prod μ)
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ) :=
  (coe_measurePreserving T).prod (MeasurePreserving.id μ)

/-- Actual restriction of real-time product measure, not a rescaled time law. -/
theorem realTime_product_restrict (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ) =
      ((volume : Measure ℝ).prod μ).restrict (Icc 0 (T : ℝ) ×ˢ univ) := by
  simpa only [Measure.restrict_univ] using
    (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := μ) (Icc 0 (T : ℝ)) univ)

/-- L2 pullback preserves norms and exhausts all nonnegative-time L2 classes. -/
def L2Equiv (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Lp ℝ 2 (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ) ≃ₗᵢ[ℝ]
      Lp ℝ 2 ((timeMeasure T).prod μ) :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℝ coeTime (coeTime_measurePreserving T μ)) (by
      intro F
      apply exists_L2_pullback (coeTime_measurePreserving T μ) F
      rw [coeTime_measurableEmbedding.comap_eq]
      exact (Lp.memLp F).aestronglyMeasurable)

theorem L2Equiv_coeFn (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Lp ℝ 2 (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ)) :
    L2Equiv T μ F =ᵐ[(timeMeasure T).prod μ] F ∘ coeTime :=
  Lp.coeFn_compMeasurePreserving F (coeTime_measurePreserving T μ)

theorem L2Equiv_norm (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Lp ℝ 2 (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ)) :
    ‖L2Equiv T μ F‖ = ‖F‖ := (L2Equiv T μ).norm_map F

theorem L2Equiv_integrable (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Lp ℝ 2 (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ)) :
    Integrable F (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ) ∧
      Integrable (L2Equiv T μ F) ((timeMeasure T).prod μ) :=
  ⟨(Lp.memLp F).integrable (by simp), (Lp.memLp _).integrable (by simp)⟩

theorem L2Equiv_integral (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Lp ℝ 2 (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ)) :
    (∫ z, L2Equiv T μ F z ∂(timeMeasure T).prod μ) =
      ∫ z, F z ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ) := by
  rw [integral_congr_ae (L2Equiv_coeFn T μ F)]
  exact (coeTime_measurePreserving T μ).integral_comp coeTime_measurableEmbedding F

omit [MeasurableSpace Ω] in
theorem coeTime_preimage_Ioc (s t : ℝ≥0) (A : Set Ω) :
    coeTime ⁻¹' (Ioc (s : ℝ) (t : ℝ) ×ˢ A) = Ioc s t ×ˢ A := by
  ext z
  rfl

theorem timeMeasure_zero (T : ℝ≥0) : timeMeasure T {0} = 0 := by
  have he : MeasurableEmbedding (fun t : ℝ≥0 => (t : ℝ)) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  rw [he.comap_apply]
  simp

theorem timeZero_slice_null (T : ℝ≥0) (μ : Measure Ω) [SFinite μ] :
    ((timeMeasure T).prod μ) ({0} ×ˢ univ) = 0 := by
  rw [Measure.prod_prod, timeMeasure_zero, zero_mul]

theorem timeMeasure_horizon_zero : timeMeasure 0 = 0 := by
  simp [timeMeasure]

end OperatorDerivativeRewrite.Foundation.PredictableTimeTransport
