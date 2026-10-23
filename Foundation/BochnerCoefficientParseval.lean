import Foundation.IBMClockPhysicalOccupation
import Foundation.BochnerL2Dominated

/-! Parseval for genuine coefficient-valued Bochner L2 fields, including the
two probability factors of the original IBM clock derivative. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BochnerCoefficientParseval
open InfiniteGaussian IBMFirstSourceClockGraph IBMClockPhysicalOccupation
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem lift_hasSum {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (μ : Measure X)
    (C : ℕ → E →L[ℝ] F)
    (hc : ∀ e, HasSum (fun i => ‖C i e‖ ^ 2) (‖e‖ ^ 2)) (u : Lp E 2 μ) :
    HasSum (fun i => ‖(C i).compLpL 2 μ u‖ ^ 2) (‖u‖ ^ 2) := by
  have hi (i : ℕ) : ‖(C i).compLpL 2 μ u‖ ^ 2 = ∫ x, ‖C i (u x)‖ ^ 2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [(C i).coeFn_compLpL u] with x hx
    rw [hx]
  have he : (fun x => ∑' i, ‖C i (u x)‖ ^ 2) = fun x => ‖u x‖ ^ 2 :=
    funext fun x => (hc (u x)).tsum_eq
  have hs := hasSum_integral_of_dominated_convergence
    (μ := μ) (F := fun i x => ‖C i (u x)‖ ^ 2) (f := fun x => ‖u x‖ ^ 2)
    (fun i x => ‖C i (u x)‖ ^ 2)
    (fun i => ((C i).continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable u)).norm.pow 2
      |>.aestronglyMeasurable)
    (fun i => ae_of_all _ fun x => by
      change |‖C i (u x)‖ ^ 2| ≤ ‖C i (u x)‖ ^ 2
      rw [abs_of_nonneg (sq_nonneg ‖C i (u x)‖)])
    (ae_of_all _ fun x => (hc (u x)).summable)
    (by rw [he]; exact (Lp.memLp u).norm.integrable_sq)
    (ae_of_all _ fun x => hc (u x))
  have hfun : (fun i => ∫ x, ‖C i (u x)‖ ^ 2 ∂μ) =
      fun i => ‖(C i).compLpL 2 μ u‖ ^ 2 := funext fun i => (hi i).symm
  rw [hfun, ← BochnerL2Dominated.norm_sq_integral] at hs
  exact hs

def basis (i : ℕ) : CoefficientSpace := lp.single 2 i (1 : ℝ)

theorem basis_inner (i : ℕ) (h : CoefficientSpace) : inner ℝ (basis i) h = h i := by
  simp [basis, lp.inner_single_left]

def coordinate (i : ℕ) : CoefficientSpace →L[ℝ] ℝ := innerSL ℝ (basis i)

theorem coefficient_hasSum (h : CoefficientSpace) :
    HasSum (fun i => ‖coordinate i h‖ ^ 2) (‖h‖ ^ 2) := by
  have hs := lp.hasSum_inner (𝕜 := ℝ) h h
  simpa only [coordinate, innerSL_apply_apply, basis_inner, Real.norm_eq_abs, sq_abs,
    Real.inner_apply, ← pow_two, real_inner_self_eq_norm_sq] using hs

theorem vector_hasSum (u : GaussianVectorL2) :
    HasSum (fun i => ‖(coordinate i).compLpL 2 gaussianProduct u‖ ^ 2) (‖u‖ ^ 2) :=
  lift_hasSum gaussianProduct coordinate coefficient_hasSum u

theorem contraction_hasSum (u : VectorSpace) :
    HasSum (fun i => ‖contraction (basis i) u‖ ^ 2) (‖u‖ ^ 2) := by
  simpa only [coordinate, contraction] using
    lift_hasSum gaussianProduct (fun i => (coordinate i).compLpL 2 gaussianProduct) vector_hasSum u

theorem directional_norm (h : CoefficientSpace) (u : VectorSpace) :
    ‖directional h u‖ = ‖contraction h u‖ := by
  change ‖flip (contraction h u)‖ = _
  exact flip.norm_map _

/-- Exact nested source/clock Parseval identity, with the original directional
factor flip included. It controls all coefficient directions simultaneously. -/
theorem directional_hasSum (u : VectorSpace) :
    HasSum (fun i => ‖directional (basis i) u‖ ^ 2) (‖u‖ ^ 2) := by
  simpa only [directional_norm] using contraction_hasSum u

theorem norm_sq_le_of_directional (u v : VectorSpace)
    (h : ∀ i, ‖directional (basis i) u‖ ^ 2 ≤ ‖directional (basis i) v‖ ^ 2) :
    ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hu := directional_hasSum u
  have hv := directional_hasSum v
  exact le_of_tendsto_of_tendsto hu.tendsto_sum_nat hv.tendsto_sum_nat
    (Eventually.of_forall fun N => Finset.sum_le_sum (fun i _ => h i))

end OperatorDerivativeRewrite.Foundation.BochnerCoefficientParseval
