import Foundation.FiniteGammaHilbertQuotient

/-! The source's literal density claim fails, but its finite-span argument is valid. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteGammaDensityCorrection
open FiniteGammaSeed FiniteGammaTensor FiniteGammaHilbertQuotient
open scoped TensorProduct
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem scale_absorbed (f u : Algebra) :
    scale • singleForm f u = singleForm f (scale • u) := by
  apply PiLp.ext
  intro p
  simp only [PiLp.smul_apply, singleForm_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A counterexample in the actual null quotient, with its completed Hilbert norm. -/
theorem completed_single_products_not_dense : ¬ DenseRange singleClass := by
  intro hd
  have hr : DenseRange (realization ∘ singleClass) :=
    realization.surjective.denseRange.comp hd hilbertEquiv.continuous
  obtain ⟨⟨f,u⟩, h⟩ := Metric.denseRange_iff.mp hr
    FiniteGammaRankOne.target (1/2) (by norm_num)
  change dist FiniteGammaRankOne.target (realization (singleClass (f,u))) < 1/2 at h
  rw [realized_single, scale_absorbed, dist_eq_norm, norm_sub_rev] at h
  have hg := FiniteGammaRankOne.distance_squared_gap f (scale • u)
  have hn := norm_nonneg (singleForm f (scale • u) - FiniteGammaRankOne.target)
  nlinarith

/-- The corrected statement is stronger than density: finite sums already give every form. -/
theorem finite_span_eq_top : Submodule.span ℝ (Set.range singleClass) = ⊤ := by
  apply top_unique
  intro q _
  induction q using Submodule.Quotient.induction_on with
  | H t =>
    induction t using TensorProduct.inductionOn with
    | tmul f u => exact Submodule.subset_span ⟨(f,u), rfl⟩
    | add x y hx hy =>
      rw [Submodule.Quotient.mk_add]
      exact Submodule.add_mem _ (hx (by trivial)) (hy (by trivial))

def multiplier (w : Algebra) : Form →ₗ[ℝ] Form where
  toFun h := WithLp.toLp 2 (fun p => w p.1 * h p)
  map_add' h k := by
    apply PiLp.ext
    intro p
    change w p.1 * (h p + k p) = w p.1 * h p + w p.1 * k p
    ring
  map_smul' r h := by
    apply PiLp.ext
    intro p
    change w p.1 * (r * h p) = r * (w p.1 * h p)
    ring

theorem multiplier_single (w f u : Algebra) :
    multiplier w (singleForm f u) = singleForm f (w * u) := by
  apply PiLp.ext
  intro p
  change w p.1 * (u p.1 * beta f p.2) = (w p.1 * u p.1) * beta f p.2
  ring

def action (w : Algebra) : EnergyQuotient →ₗ[ℝ] EnergyQuotient :=
  realization.symm.toLinearMap.comp ((multiplier w).comp realization.toLinearMap)

theorem action_single (w f u : Algebra) :
    action w (singleClass (f,u)) = singleClass (f, w * u) := by
  apply realization.injective
  change realization (realization.symm (multiplier w (realization (singleClass (f,u))))) = _
  rw [realization.apply_symm_apply, realized_single, map_smul, multiplier_single,
    realized_single]

def D0 (f : Algebra) : EnergyQuotient := singleClass (f, 1)

theorem product_is_single (u f : Algebra) : action u (D0 f) = singleClass (f,u) := by
  rw [D0, action_single, mul_one]

end OperatorDerivativeRewrite.Foundation.FiniteGammaDensityCorrection
