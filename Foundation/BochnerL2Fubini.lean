import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-! A justified Bochner-L² Fubini rule on a finite parameter measure.
The uniform majorant is genuinely in L²; integrability of all scalar test pairings
and almost every column is proved before interchanging integrals. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.BochnerL2Fubini
variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

theorem columns_integrable (g : X × Y → E)
    (hg : AEStronglyMeasurable g (μ.prod ν)) (B : Y → ℝ)
    (hb : ∀ᵐ z ∂μ.prod ν, ‖g z‖ ≤ B z.2) :
    ∀ᵐ y ∂ν, Integrable (fun x => g (x, y)) μ := by
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hb
  filter_upwards [hg.prodMk_right, ae_ae_of_ae_prod hs] with y hm hy
  exact (integrable_const (B y)).mono' hm hy

theorem pairing_integrable (g : X × Y → E)
    (hg : AEStronglyMeasurable g (μ.prod ν)) (B : Y → ℝ) (hB : MemLp B 2 ν)
    (hb : ∀ᵐ z ∂μ.prod ν, ‖g z‖ ≤ B z.2) (V : Lp E 2 ν) :
    Integrable (fun z => inner ℝ (V z.2) (g z)) (μ.prod ν) := by
  have hi : Integrable (fun y => B y * ‖V y‖) ν :=
    hB.integrable_mul (Lp.memLp V).norm
  have hp : Integrable (fun z : X × Y => B z.2 * ‖V z.2‖) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := μ)).mul_prod hi
  apply hp.mono' ((Lp.aestronglyMeasurable V).comp_snd.inner hg)
  filter_upwards [hb] with z hz
  exact (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (V z.2)])

/-- Identify an actual L²-valued Bochner integral by its pointwise column integrals.
`W` is an independently supplied L² class; its column formula is a pointwise integral
calculation, not an assumption about the L²-valued integral on the left. -/
theorem integral_eq_of_slices (v : X → Lp E 2 ν) (hv : Integrable v μ)
    (g : X × Y → E) (hg : AEStronglyMeasurable g (μ.prod ν))
    (hvg : ∀ᵐ x ∂μ, v x =ᵐ[ν] fun y => g (x, y))
    (B : Y → ℝ) (hB : MemLp B 2 ν) (hb : ∀ᵐ z ∂μ.prod ν, ‖g z‖ ≤ B z.2)
    (W : Lp E 2 ν) (hW : W =ᵐ[ν] fun y => ∫ x, g (x, y) ∂μ) :
    (∫ x, v x ∂μ) = W := by
  apply ext_inner_left ℝ
  intro V
  rw [← integral_inner hv V]
  calc
    (∫ x, inner ℝ V (v x) ∂μ) = ∫ x, ∫ y, inner ℝ (V y) (g (x, y)) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [hvg] with x hx
      rw [L2.inner_def]
      exact integral_congr_ae (hx.mono fun y hy => congrArg (inner ℝ (V y)) hy)
    _ = ∫ y, ∫ x, inner ℝ (V y) (g (x, y)) ∂μ ∂ν :=
      integral_integral_swap (pairing_integrable g hg B hB hb V)
    _ = inner ℝ V W := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [columns_integrable g hg B hb, hW] with y hy hw
      rw [integral_inner hy, ← hw]

end OperatorDerivativeRewrite.Foundation.BochnerL2Fubini
