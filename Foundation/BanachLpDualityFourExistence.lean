import Foundation.BanachLpDualityFourContinuity
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Finite-dimensional solvability of the fourth-power Banach normal equation

The quartic energy has the genuine normal operator as its derivative.
A proved bounded sublevel estimate and finite-dimensional compactness give
existence by minimization. Uniform monotonicity gives uniqueness and the
one-third Hölder stability estimate. No Hilbert-space identification is used.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.BanachLpDualityFourExistence
open BanachLpDualityFour BanachLpDualityFourContinuity
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

private def pairTwo : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 2 2

private theorem pairTwo_comm (F G : Lp ℝ 2 μ) : pairTwo F G = pairTwo G F := by
  simp only [pairTwo, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply']
  congr 1
  funext ω
  ring

private theorem squareProduct_comm (F G : Lp ℝ 4 μ) :
    squareProduct F G = squareProduct G F := by
  apply Lp.ext
  filter_upwards [squareProduct_ae F G, squareProduct_ae G F] with ω h₁ h₂
  rw [h₁, h₂, mul_comm]

private theorem pairTwo_square_eq_norm (F : Lp ℝ 4 μ) :
    pairTwo (squareProduct F F) (squareProduct F F) = ‖F‖ ^ 4 := by
  rw [pairTwo, ContinuousLinearMap.lpPairing_eq_integral,
    ← quartic_integral_eq_norm]
  apply integral_congr_ae
  filter_upwards [squareProduct_ae F F] with ω hω
  simp only [ContinuousLinearMap.mul_apply', hω]
  ring

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

private theorem pairTwo_square_cross (δ : H →L[ℝ] Lp ℝ 4 μ) (u v : H) :
    pairTwo (squareProduct (δ u) (δ u)) (squareProduct (δ u) (δ v)) =
      normalFour δ u v := by
  rw [pairTwo, ContinuousLinearMap.lpPairing_eq_integral,
    normalFour, BanachLpAdjoint.boundedBanachDerivative_apply]
  apply integral_congr_ae
  filter_upwards [squareProduct_ae (δ u) (δ u),
    squareProduct_ae (δ u) (δ v), dualityFour_ae (δ u)] with ω h₁ h₂ h₃
  simp only [ContinuousLinearMap.mul_apply', h₁, h₂, h₃]
  ring

/-- The quartic potential is genuinely differentiable, with the actual normal map as derivative. -/
theorem hasFDerivAt_quarticPotential (δ : H →L[ℝ] Lp ℝ 4 μ) (u : H) :
    HasFDerivAt (fun v : H => (1 / 4 : ℝ) * ‖δ v‖ ^ 4) (normalFour δ u) u := by
  let Q := squareProduct (μ := μ)
  let S : H → Lp ℝ 2 μ := fun v => Q (δ v) (δ v)
  let S' : H →L[ℝ] Lp ℝ 2 μ :=
    Q.precompR H (δ u) δ + Q.precompL H δ (δ u)
  have hS : HasFDerivAt S S' u :=
    Q.hasFDerivAt_of_bilinear δ.hasFDerivAt δ.hasFDerivAt
  have hp := ((pairTwo (μ := μ)).hasFDerivAt_of_bilinear hS hS).const_mul (1 / 4 : ℝ)
  have hf : (fun v : H => (1 / 4 : ℝ) * pairTwo (S v) (S v)) =
      (fun v : H => (1 / 4 : ℝ) * ‖δ v‖ ^ 4) := by
    funext v
    rw [show S v = squareProduct (δ v) (δ v) from rfl, pairTwo_square_eq_norm]
  rw [hf] at hp
  convert hp using 1
  ext v
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, smul_eq_mul]
  change normalFour δ u v = (1 / 4 : ℝ) *
    (pairTwo (S u) (S' v) + pairTwo (S' v) (S u))
  have hS' : S' v = squareProduct (δ u) (δ v) + squareProduct (δ v) (δ u) := rfl
  rw [hS', squareProduct_comm (δ v) (δ u)]
  simp only [map_add, add_apply]
  rw [pairTwo_comm (squareProduct (δ u) (δ v)) (S u)]
  change normalFour δ u v = (1 / 4 : ℝ) *
    ((pairTwo (squareProduct (δ u) (δ u)) (squareProduct (δ u) (δ v)) + _) + _)
  rw [pairTwo_square_cross]
  ring

/-- Bounded-below `δ` makes every affine perturbation of its quartic potential attain a minimum. -/
theorem exists_quarticPotential_minimizer [FiniteDimensional ℝ H]
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f : StrongDual ℝ H) :
    ∃ u : H, ∀ v : H,
      (1 / 4 : ℝ) * ‖δ u‖ ^ 4 - f u ≤ (1 / 4 : ℝ) * ‖δ v‖ ^ 4 - f v := by
  let E : H → ℝ := fun u => (1 / 4 : ℝ) * ‖δ u‖ ^ 4 - f u
  have hE : Continuous E := by fun_prop
  apply hE.exists_forall_le_of_isBounded 0
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max 1 (4 * ‖f‖ / c ^ 4), ?_⟩
  intro u hu
  have hk : 0 < c ^ 4 := pow_pos hc 4
  have hfu : f u ≤ ‖f‖ * ‖u‖ := (le_abs_self _).trans (f.le_opNorm u)
  have hδ4 : c ^ 4 * ‖u‖ ^ 4 ≤ ‖δ u‖ ^ 4 := by
    calc
      c ^ 4 * ‖u‖ ^ 4 = (c * ‖u‖) ^ 4 := by ring
      _ ≤ ‖δ u‖ ^ 4 := pow_le_pow_left₀ (by positivity) (hδ u) 4
  have hsub : c ^ 4 * ‖u‖ ^ 4 ≤ 4 * ‖f‖ * ‖u‖ := by
    change E u ≤ E 0 at hu
    dsimp [E] at hu
    simp only [map_zero, norm_zero, zero_pow (by decide : 4 ≠ 0), mul_zero,
      sub_zero] at hu
    nlinarith
  by_cases hr : ‖u‖ ≤ 1
  · exact hr.trans (le_max_left _ _)
  · have hr1 : 1 < ‖u‖ := lt_of_not_ge hr
    have hr0 : 0 < ‖u‖ := lt_trans zero_lt_one hr1
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hk).mpr
    apply (mul_le_mul_iff_right₀ hr0).mp
    have hp : ‖u‖ ^ 2 ≤ ‖u‖ ^ 4 := pow_le_pow_right₀ hr1.le (by decide : 2 ≤ 4)
    have hkp := mul_le_mul_of_nonneg_left hp hk.le
    nlinarith

/-- Every continuous functional is attained by the actual nonlinear normal map
in finite dimension. -/
theorem normalFour_surjective [FiniteDimensional ℝ H]
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) : Function.Surjective (normalFour δ) := by
  intro f
  obtain ⟨u, hu⟩ := exists_quarticPotential_minimizer δ c hc hδ f
  have hmin : IsLocalMin (fun v : H => (1 / 4 : ℝ) * ‖δ v‖ ^ 4 - f v) u :=
    Filter.Eventually.of_forall hu
  have hder := (hasFDerivAt_quarticPotential δ u).sub f.hasFDerivAt
  exact ⟨u, sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hder)⟩

/-- Every right-hand side has exactly one solution under the actual lower norm bound. -/
theorem normalFour_existsUnique [FiniteDimensional ℝ H]
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f : StrongDual ℝ H) :
    ∃! u : H, normalFour δ u = f := by
  obtain ⟨u, hu⟩ := normalFour_surjective δ c hc hδ f
  exact ⟨u, hu, fun v hv => normalFour_injective δ c hc hδ (hv.trans hu.symm)⟩

/-- The nonlinear normal map as an actual bijection between the normed space and its strong dual. -/
def normalFourEquiv [FiniteDimensional ℝ H]
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) : H ≃ StrongDual ℝ H :=
  Equiv.ofBijective (normalFour δ)
    ⟨normalFour_injective δ c hc hδ, normalFour_surjective δ c hc hδ⟩

@[simp]
theorem normalFourEquiv_apply [FiniteDimensional ℝ H]
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (u : H) :
    normalFourEquiv δ c hc hδ u = normalFour δ u := rfl

/-- The chosen inverse solves the original normal equation exactly. -/
@[simp]
theorem normalFour_inverse_solves [FiniteDimensional ℝ H]
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f : StrongDual ℝ H) :
    normalFour δ ((normalFourEquiv δ c hc hδ).symm f) = f :=
  (normalFourEquiv δ c hc hδ).apply_symm_apply f

/-- Cubic stability of the actual inverse, including zero differences. -/
theorem normalFour_inverse_cubic [FiniteDimensional ℝ H]
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f g : StrongDual ℝ H) :
    ‖(normalFourEquiv δ c hc hδ).symm f -
        (normalFourEquiv δ c hc hδ).symm g‖ ^ 3 ≤ (4 / c ^ 4) * ‖f - g‖ := by
  simpa only [normalFour_inverse_solves] using
    normalFour_inverse_cubic_bound δ c hc hδ
      ((normalFourEquiv δ c hc hδ).symm f) ((normalFourEquiv δ c hc hδ).symm g)

/-- Global one-third Hölder stability of the inverse with the quantitative constant. -/
theorem normalFour_inverse_holder [FiniteDimensional ℝ H]
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f g : StrongDual ℝ H) :
    ‖(normalFourEquiv δ c hc hδ).symm f -
        (normalFourEquiv δ c hc hδ).symm g‖ ≤
      (4 / c ^ 4) ^ (1 / 3 : ℝ) * ‖f - g‖ ^ (1 / 3 : ℝ) := by
  have h := normalFour_inverse_holder_bound δ c hc hδ
    ((normalFourEquiv δ c hc hδ).symm f) ((normalFourEquiv δ c hc hδ).symm g)
  simpa only [normalFour_inverse_solves, Real.mul_rpow (by positivity : 0 ≤ 4 / c ^ 4)
    (norm_nonneg (f - g))] using h

end OperatorDerivativeRewrite.Foundation.BanachLpDualityFourExistence

