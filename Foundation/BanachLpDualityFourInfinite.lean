import Foundation.BanachLpDualityFourCoercivity
import Foundation.QuarticUniformMinimization
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Complete-space solvability of the quartic Banach normal equation

The actual quartic energy satisfies a proved uniform midpoint inequality.
An infimizing sequence is therefore norm-Cauchy, and completeness gives its
minimum. The previously verified Fréchet derivative identifies its critical
point with the original normal equation. No finite-dimensionality or
reflexivity hypothesis is required.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.BanachLpDualityFourInfinite

open BanachLpDualityFour BanachLpDualityFourContinuity BanachLpDualityFourCoercivity

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- Every affine perturbation of the actual quartic energy attains a minimum
on a complete source space when δ has a positive lower norm bound. -/
theorem exists_quarticPotential_minimizer
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f : StrongDual ℝ H) :
    ∃ u : H, ∀ v : H,
      (1 / 4 : ℝ) * ‖δ u‖ ^ 4 - f u ≤ (1 / 4 : ℝ) * ‖δ v‖ ^ 4 - f v := by
  apply QuarticUniformMinimization.exists_minimizer_of_quartic_midpoint
    (fun u : H => (1 / 4 : ℝ) * ‖δ u‖ ^ 4 - f u)
    (by fun_prop) (quarticPotential_bddBelow δ c hc hδ f) (c ^ 4 / 64)
    (by positivity)
  exact quarticEnergy_midpoint_lower δ c hc hδ f

/-- The original normal map is onto the entire continuous dual, without
any finite-dimensionality, assumed reflexivity, or assumed existence. -/
theorem normalFour_surjective
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) : Function.Surjective (normalFour δ) := by
  intro f
  obtain ⟨u, hu⟩ := exists_quarticPotential_minimizer δ c hc hδ f
  have hmin : IsLocalMin (fun v : H => (1 / 4 : ℝ) * ‖δ v‖ ^ 4 - f v) u :=
    Filter.Eventually.of_forall hu
  have hder := (BanachLpDualityFourExistence.hasFDerivAt_quarticPotential δ u).sub
    f.hasFDerivAt
  exact ⟨u, sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hder)⟩

/-- Every continuous-dual datum has exactly one solution on the complete source. -/
theorem normalFour_existsUnique
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f : StrongDual ℝ H) :
    ∃! u : H, normalFour δ u = f := by
  obtain ⟨u, hu⟩ := normalFour_surjective δ c hc hδ f
  exact ⟨u, hu, fun v hv => normalFour_injective δ c hc hδ (hv.trans hu.symm)⟩

/-- The original nonlinear normal map as a bijection on a complete source. -/
def normalFourEquiv
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) : H ≃ StrongDual ℝ H :=
  Equiv.ofBijective (normalFour δ)
    ⟨normalFour_injective δ c hc hδ, normalFour_surjective δ c hc hδ⟩

@[simp]
theorem normalFourEquiv_apply
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (u : H) :
    normalFourEquiv δ c hc hδ u = normalFour δ u := rfl

/-- The actual inverse solves the original equation for every continuous functional. -/
@[simp]
theorem normalFour_inverse_solves
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f : StrongDual ℝ H) :
    normalFour δ ((normalFourEquiv δ c hc hδ).symm f) = f :=
  (normalFourEquiv δ c hc hδ).apply_symm_apply f

/-- The previously proved cubic stability estimate holds for this full inverse. -/
theorem normalFour_inverse_cubic
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f g : StrongDual ℝ H) :
    ‖(normalFourEquiv δ c hc hδ).symm f -
        (normalFourEquiv δ c hc hδ).symm g‖ ^ 3 ≤ (4 / c ^ 4) * ‖f - g‖ := by
  simpa only [normalFour_inverse_solves] using
    normalFour_inverse_cubic_bound δ c hc hδ
      ((normalFourEquiv δ c hc hδ).symm f) ((normalFourEquiv δ c hc hδ).symm g)

/-- Global one-third Hölder stability, with the same constant as before. -/
theorem normalFour_inverse_holder
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f g : StrongDual ℝ H) :
    ‖(normalFourEquiv δ c hc hδ).symm f -
        (normalFourEquiv δ c hc hδ).symm g‖ ≤
      (4 / c ^ 4) ^ (1 / 3 : ℝ) * ‖f - g‖ ^ (1 / 3 : ℝ) := by
  have h := normalFour_inverse_holder_bound δ c hc hδ
    ((normalFourEquiv δ c hc hδ).symm f) ((normalFourEquiv δ c hc hδ).symm g)
  simpa only [normalFour_inverse_solves, Real.mul_rpow (by positivity : 0 ≤ 4 / c ^ 4)
    (norm_nonneg (f - g))] using h

/-- Specialization to the entire L4 space, for arbitrary measures and with
no restriction on its dimension. The identity operator has lower bound one. -/
theorem lpFour_normal_existsUnique (f : StrongDual ℝ (Lp ℝ 4 μ)) :
    ∃! u : Lp ℝ 4 μ, normalFour (ContinuousLinearMap.id ℝ (Lp ℝ 4 μ)) u = f := by
  exact normalFour_existsUnique (ContinuousLinearMap.id ℝ (Lp ℝ 4 μ))
    1 (by norm_num) (by intro u; simp) f

end OperatorDerivativeRewrite.Foundation.BanachLpDualityFourInfinite
