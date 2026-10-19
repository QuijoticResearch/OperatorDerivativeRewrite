import Foundation.GaussianChaosLowering
import Foundation.GaussianDivergenceRecovery

/-! Shifted inverse-number regularization of an actual rank-one derivative,
identified with the existing bounded divergence recovery. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianDirectionalRecovery
open InfiniteGaussian GaussianNumberSectors GaussianChaosLowering GaussianDivergenceRecovery
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def directionalRecovery (v : CoefficientSpace) : GaussianL2 →L[ℝ] GaussianL2 :=
  (component v).comp recoveryOperator

theorem component_norm_le (v : CoefficientSpace) (u : GaussianVectorL2) :
    ‖component v u‖ ≤ ‖v‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(innerSL ℝ v).coeFn_compLpL u] with ω hω
  change ‖(innerSL ℝ v).compLpL 2 gaussianProduct u ω‖ ≤ _
  rw [hω]
  exact norm_inner_le_norm (𝕜 := ℝ) v (u ω)

theorem directionalRecovery_norm_le (v : CoefficientSpace) (f : GaussianL2) :
    ‖directionalRecovery v f‖ ≤ ‖v‖ * ‖f‖ :=
  (component_norm_le v (recovery f)).trans
    (mul_le_mul_of_nonneg_left (recovery_norm_le f) (norm_nonneg v))

theorem unit_component_tensor (v : CoefficientSpace) (hv : ‖v‖ = 1) (g : GaussianL2) :
    component v (scalarTensor v g) = g := by
  rw [component_scalarTensor, real_inner_self_eq_norm_sq, hv, one_pow, one_smul]

/-- The output is the original bounded recovery, with the exact +1 spectral
shift. The input derivative must belong to the ORIGINAL closed graph. -/
theorem shifted_derivative_hasSum (v : CoefficientSpace) (hv : ‖v‖ = 1)
    {f g : GaussianL2} (hfg : (f, scalarTensor v g) ∈ closedCylindricalDerivative.graph) :
    HasSum (fun n : ℕ => (n + 1 : ℝ)⁻¹ • projection n g) (directionalRecovery v f) := by
  have hs := (inverseGradient_summable f).hasSum.map
    (component v).toAddMonoidHom (component v).continuous
  change HasSum (fun n => component v
    (((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2)))
      (component v (recovery f)) at hs
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  have hz : component v
      (((inverseGradientComponent f 0 : (gradient 0).range) : GaussianVectorL2)) = 0 := by
    simp [inverseGradientComponent]
  simp only [Finset.sum_range_one, hz, sub_zero] at ht
  have he (n : ℕ) : component v
      (((inverseGradientComponent f (n + 1) : (gradient (n + 1)).range) : GaussianVectorL2)) =
      (n + 1 : ℝ)⁻¹ • projection n g := by
    change component v (((n + 1 : ℕ) : ℝ)⁻¹ • projectedGradient (n + 1) f) = _
    rw [map_smul, component_derivative_intertwining n v hfg, unit_component_tensor v hv g]
    simp only [Nat.cast_add, Nat.cast_one]
  change HasSum (fun n : ℕ => (n + 1 : ℝ)⁻¹ • projection n g) (component v (recovery f))
  simpa only [he] using ht

theorem shifted_derivative_projection (v : CoefficientSpace) (hv : ‖v‖ = 1)
    {f g : GaussianL2} (hfg : (f, scalarTensor v g) ∈ closedCylindricalDerivative.graph)
    (k : ℕ) :
    projection k (directionalRecovery v f) = (k + 1 : ℝ)⁻¹ • projection k g := by
  have hs := (shifted_derivative_hasSum v hv hfg).map
    (projection k).toAddMonoidHom (projection k).continuous
  change HasSum (fun n : ℕ => projection k ((n + 1 : ℝ)⁻¹ • projection n g))
    (projection k (directionalRecovery v f)) at hs
  have he (n : ℕ) : projection k ((n + 1 : ℝ)⁻¹ • projection n g) =
      if n = k then (k + 1 : ℝ)⁻¹ • projection k g else 0 := by
    rw [map_smul,GaussianNumberSectors.projection_of_sector ⟨_,projection_mem n g⟩]
    by_cases hn : n = k
    · subst n; simp
    · simp [hn,Ne.symm hn]
  simp only [he] at hs
  exact hs.unique (hasSum_ite_eq k _)

end OperatorDerivativeRewrite.Foundation.GaussianDirectionalRecovery
