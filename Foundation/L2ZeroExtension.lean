import Mathlib.MeasureTheory.Function.L2Space

/-! Zero extension from a restricted measure, as an actual linear L2 isometry. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s : Set Ω}

def L2ZeroExtension (hs : MeasurableSet s) (F : Lp ℝ 2 (μ.restrict s)) : Lp ℝ 2 μ :=
  ((memLp_indicator_iff_restrict hs).2 (Lp.memLp F)).toLp _

theorem L2ZeroExtension_coeFn (hs : MeasurableSet s) (F : Lp ℝ 2 (μ.restrict s)) :
    L2ZeroExtension hs F =ᵐ[μ] s.indicator F := MemLp.coeFn_toLp _

theorem L2ZeroExtension_norm (hs : MeasurableSet s) (F : Lp ℝ 2 (μ.restrict s)) :
    ‖L2ZeroExtension hs F‖ = ‖F‖ := by
  rw [L2ZeroExtension, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs, Lp.norm_def]

def L2ZeroExtensionLinear (hs : MeasurableSet s) : Lp ℝ 2 (μ.restrict s) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := L2ZeroExtension hs
  map_add' F G := by
    apply Lp.ext
    have he := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_add F G)
    filter_upwards [L2ZeroExtension_coeFn hs (F+G), L2ZeroExtension_coeFn hs F,
      L2ZeroExtension_coeFn hs G, Lp.coeFn_add (L2ZeroExtension hs F) (L2ZeroExtension hs G), he]
      with x hsum hf hg hadd he
    change L2ZeroExtension hs (F+G) x = (L2ZeroExtension hs F + L2ZeroExtension hs G) x
    rw [hsum, hadd]
    simp only [Pi.add_apply, hf, hg]
    rw [he]
    by_cases hx : x ∈ s <;> simp [hx]
  map_smul' c F := by
    apply Lp.ext
    have he := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_smul c F)
    filter_upwards [L2ZeroExtension_coeFn hs (c • F), L2ZeroExtension_coeFn hs F,
      Lp.coeFn_smul c (L2ZeroExtension hs F), he] with x hsm hf hadd he
    change L2ZeroExtension hs (c • F) x = (c • L2ZeroExtension hs F) x
    rw [hsm, hadd]
    simp only [Pi.smul_apply, hf]
    rw [he]
    by_cases hx : x ∈ s <;> simp [hx]

def L2ZeroExtensionIsometry (hs : MeasurableSet s) :
    Lp ℝ 2 (μ.restrict s) →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toLinearMap := L2ZeroExtensionLinear hs
  norm_map' := L2ZeroExtension_norm hs

theorem L2ZeroExtension_indicator (hs : MeasurableSet s) {a : Set Ω}
    (ha : MeasurableSet a) (hfin : (μ.restrict s) a ≠ ∞) :
    L2ZeroExtension hs (indicatorConstLp 2 ha hfin (1 : ℝ)) =
      indicatorConstLp 2 (hs.inter ha)
        (by simpa only [Measure.restrict_apply ha, inter_comm] using hfin) (1 : ℝ) := by
  apply Lp.ext
  have he := (ae_eq_restrict_iff_indicator_ae_eq hs).mp
    (indicatorConstLp_coeFn (p := 2) (μ := μ.restrict s) (c := (1 : ℝ)) (hs := ha) (hμs := hfin))
  filter_upwards [L2ZeroExtension_coeFn hs (indicatorConstLp 2 ha hfin (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (c := (1 : ℝ))
      (hs := hs.inter ha)
      (hμs := (by simpa only [Measure.restrict_apply ha, inter_comm] using hfin)), he]
    with x hz hi he
  rw [hz, hi, he, indicator_indicator]

end OperatorDerivativeRewrite.Foundation
