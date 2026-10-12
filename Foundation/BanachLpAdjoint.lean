import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# A bounded Banach adjoint on actual Lp spaces

The derivative here is the transpose of an *existing* bounded map into `Lp`.  Its
pairing is Mathlib's Hölder pairing, so no representation of an arbitrary dual
functional or stochastic integral is assumed.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.BanachLpAdjoint

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p q : ℝ≥0∞}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]

/-- The bounded transpose of a genuine map from `H` to scalar `Lp`. -/
def boundedBanachDerivative (δ : H →L[ℝ] Lp ℝ p μ) :
    Lp ℝ q μ →L[ℝ] StrongDual ℝ H :=
  (δ.precomp ℝ).comp ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p)

omit [Fact (1 ≤ q)] in
/-- Hölder makes the product in the duality formula genuinely integrable. -/
theorem integrable_mul (δ : H →L[ℝ] Lp ℝ p μ)
    (F : Lp ℝ q μ) (u : H) :
    Integrable (fun ω ↦ F ω * (δ u) ω) μ := by
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1 (Lp.memLp F) (Lp.memLp (δ u)))

/-- Evaluation of the transpose is the actual, integrable Hölder pairing. -/
theorem boundedBanachDerivative_apply (δ : H →L[ℝ] Lp ℝ p μ)
    (F : Lp ℝ q μ) (u : H) :
    boundedBanachDerivative δ F u = ∫ ω, F ω * (δ u) ω ∂μ := by
  exact (ContinuousLinearMap.mul ℝ ℝ).lpPairing_eq_integral F (δ u)

/-- The pairing has operator norm at most one. -/
private theorem lpPairing_norm_le_one :
    ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p‖ ≤ 1 := by
  calc
    ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p‖
        ≤ ‖(L1.integralCLM' ℝ).postcomp (Lp ℝ p μ)‖ *
            ‖(ContinuousLinearMap.mul ℝ ℝ).holderL μ q p 1‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      gcongr
      · exact (ContinuousLinearMap.norm_postcomp_le _).trans L1.norm_Integral_le_one
      · exact ((ContinuousLinearMap.mul ℝ ℝ).norm_holderL_le).trans
          (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
    _ = 1 := one_mul _

/-- The norm bound uses only the actual operator norm of `δ`. -/
theorem boundedBanachDerivative_norm_le (δ : H →L[ℝ] Lp ℝ p μ)
    (F : Lp ℝ q μ) :
    ‖boundedBanachDerivative δ F‖ ≤ ‖F‖ * ‖δ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro u
  calc
    ‖boundedBanachDerivative δ F u‖
        = ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p F (δ u)‖ := rfl
    _ ≤ ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p F‖ * ‖δ u‖ :=
          (((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p) F).le_opNorm (δ u)
    _ ≤ (‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p‖ * ‖F‖) * ‖δ u‖ :=
          mul_le_mul_of_nonneg_right
            (((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p).le_opNorm F)
            (norm_nonneg _)
    _ ≤ 1 * ‖F‖ * (‖δ‖ * ‖u‖) := by
          gcongr
          · exact lpPairing_norm_le_one
          · exact δ.le_opNorm u
    _ = (‖F‖ * ‖δ‖) * ‖u‖ := by ring

/-- The kernel is exactly the annihilator of the range of `δ`. -/
theorem boundedBanachDerivative_eq_zero_iff (δ : H →L[ℝ] Lp ℝ p μ)
    (F : Lp ℝ q μ) :
    boundedBanachDerivative δ F = 0 ↔
      ∀ u : H, ∫ ω, F ω * (δ u) ω ∂μ = 0 := by
  constructor
  · intro h u
    have hval := congrArg (fun T : StrongDual ℝ H ↦ T u) h
    simpa only [boundedBanachDerivative_apply, zero_apply] using hval
  · intro h
    apply ContinuousLinearMap.ext
    intro u
    simpa only [boundedBanachDerivative_apply, zero_apply] using h u

/-- Centering of the actual `Lp` image makes the adjoint kill constant classes. -/
theorem boundedBanachDerivative_const_eq_zero [IsFiniteMeasure μ]
    (δ : H →L[ℝ] Lp ℝ p μ)
    (hδcenter : ∀ u : H, ∫ ω, (δ u) ω ∂μ = 0)
    (c : ℝ) :
    boundedBanachDerivative δ (Lp.const q μ c) = 0 := by
  rw [boundedBanachDerivative_eq_zero_iff]
  intro u
  have hconst := Lp.coeFn_const (μ := μ) (p := q) (c := c)
  have hprod :
      (fun ω ↦ (Lp.const q μ c) ω * (δ u) ω) =ᵐ[μ]
        (fun ω ↦ c * (δ u) ω) :=
    hconst.mono fun ω hω ↦ by
      simpa only [Function.const_apply] using
        congrArg (fun x : ℝ ↦ x * (δ u) ω) hω
  rw [integral_congr_ae hprod, integral_const_mul, hδcenter u, mul_zero]

end OperatorDerivativeRewrite.Foundation.BanachLpAdjoint
