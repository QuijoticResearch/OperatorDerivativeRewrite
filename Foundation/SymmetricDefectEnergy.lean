import Foundation.SymmetricFactorEnergy
import Mathlib.Topology.Order.MonotoneConvergence

/-! Bounded semigroup defects and the bounded-energy domain criterion for symmetric factors. -/
noncomputable section
open Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.SymmetricDefectEnergy
open HilbertRepresentation SymmetricFactorEnergy
set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

def defect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ) (T : E →L[ℝ] E) : E →L[ℝ] E :=
  t⁻¹ • (ContinuousLinearMap.id ℝ E - T)

omit [CompleteSpace Y] in
theorem defect_symmetric (t : ℝ) (T : Y →L[ℝ] Y)
    (hT : T.toLinearMap.IsSymmetric) : (defect t T).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℝ (t⁻¹ • (u - T u)) v = inner ℝ u (t⁻¹ • (v - T v))
  rw [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
  have h : inner ℝ (T u) v = inner ℝ u (T v) := hT u v
  rw [h]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem defect_intertwining (J : X →ₗᵢ[ℝ] Y) (T : Y →L[ℝ] Y) (S : X →L[ℝ] X)
    (hJ : ∀ x, T (J x) = J (S x)) (t : ℝ) (x : X) :
    defect t T (J x) = J (defect t S x) := by
  change t⁻¹ • (J x - T (J x)) = J (t⁻¹ • (x - S x))
  rw [hJ, map_smul, map_sub]

omit [CompleteSpace Y] in
theorem defect_nonnegative (t : ℝ) (ht : 0 < t) (T : Y →L[ℝ] Y)
    (hT : ∀ y, ‖T y‖ ≤ ‖y‖) (y : Y) : 0 ≤ inner ℝ (defect t T y) y := by
  change 0 ≤ inner ℝ (t⁻¹ • (y - T y)) y
  rw [real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]
  apply mul_nonneg (inv_nonneg.mpr (le_of_lt ht))
  have hi := real_inner_le_norm (T y) y
  have hm := mul_le_mul_of_nonneg_right (hT y) (norm_nonneg y)
  nlinarith

theorem defect_energy_contraction (J : X →ₗᵢ[ℝ] Y)
    (T : Y →L[ℝ] Y) (S : X →L[ℝ] X)
    (hTsym : T.toLinearMap.IsSymmetric) (hT : ∀ y, ‖T y‖ ≤ ‖y‖)
    (hJ : ∀ x, T (J x) = J (S x)) (t : ℝ) (ht : 0 < t) (y : Y) :
    inner ℝ (defect t S (predictableAdjoint J y)) (predictableAdjoint J y) ≤
      inner ℝ (defect t T y) y :=
  quadratic_energy_contraction J (defect t T) (defect t S) (defect_symmetric t T hTsym)
    (defect_intertwining J T S hJ t) (defect_nonnegative t ht T hT) y

def boundedEnergyDomain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : ℕ → E →L[ℝ] E) : Set E :=
  {u | ∃ M : ℝ, ∀ n, inner ℝ (A n u) u ≤ M}

theorem bounded_domain_transfer (J : X →ₗᵢ[ℝ] Y)
    (A : ℕ → Y →L[ℝ] Y) (B : ℕ → X →L[ℝ] X)
    (hA : ∀ n, (A n).toLinearMap.IsSymmetric)
    (hJ : ∀ n x, A n (J x) = J (B n x))
    (hpos : ∀ n y, 0 ≤ inner ℝ (A n y) y) {y : Y}
    (hy : y ∈ boundedEnergyDomain A) :
    predictableAdjoint J y ∈ boundedEnergyDomain B := by
  obtain ⟨M,hM⟩ := hy
  exact ⟨M,fun n => le_trans (quadratic_energy_contraction J (A n) (B n)
    (hA n) (hJ n) (hpos n) y) (hM n)⟩

theorem limiting_energy_contraction {ι : Type*} {l : Filter ι} [NeBot l]
    (J : X →ₗᵢ[ℝ] Y) (A : ι → Y →L[ℝ] Y) (B : ι → X →L[ℝ] X)
    (hA : ∀ i, (A i).toLinearMap.IsSymmetric)
    (hJ : ∀ i x, A i (J x) = J (B i x))
    (hpos : ∀ i y, 0 ≤ inner ℝ (A i y) y) (y : Y) {EX EY : ℝ}
    (hX : Tendsto (fun i => inner ℝ (B i (predictableAdjoint J y))
      (predictableAdjoint J y)) l (𝓝 EX))
    (hY : Tendsto (fun i => inner ℝ (A i y) y) l (𝓝 EY)) : EX ≤ EY :=
  le_of_tendsto_of_tendsto hX hY (Eventually.of_forall (fun i =>
    quadratic_energy_contraction J (A i) (B i) (hA i) (hJ i) (hpos i) y))

end OperatorDerivativeRewrite.Foundation.SymmetricDefectEnergy
