import Foundation.BochnerCoefficientParseval
import Mathlib.Analysis.Normed.Group.Tannery

/-! Full coefficient Cauchy convergence from actual nested-L2 Parseval,
coordinate Cauchy convergence and a summable squared-coordinate majorant. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BochnerCoefficientCauchy
open InfiniteGaussian IBMFirstSourceClockGraph IBMClockPhysicalOccupation BochnerCoefficientParseval

theorem cauchy_of_coordinates (u : ℕ → VectorSpace) (b : ℕ → ℝ)
    (hb : Summable b)
    (hbound : ∀ n i, ‖contraction (basis i) (u n)‖ ^ 2 ≤ b i)
    (hc : ∀ i, CauchySeq (fun n => contraction (basis i) (u n))) : CauchySeq u := by
  have hd (p : ℕ × ℕ) (i : ℕ) :
      ‖contraction (basis i) (u p.1) - contraction (basis i) (u p.2)‖^2 ≤ 4*b i := by
    have ht := pow_le_pow_left₀ (norm_nonneg
      (contraction (basis i) (u p.1) - contraction (basis i) (u p.2)))
      (norm_sub_le (contraction (basis i) (u p.1)) (contraction (basis i) (u p.2))) 2
    nlinarith [hbound p.1 i,hbound p.2 i,
      sq_nonneg (‖contraction (basis i) (u p.1)‖ - ‖contraction (basis i) (u p.2)‖)]
  have ht (i : ℕ) : Tendsto (fun p : ℕ × ℕ =>
      ‖contraction (basis i) (u p.1) - contraction (basis i) (u p.2)‖^2) atTop (𝓝 0) := by
    simpa only [dist_eq_norm,zero_pow (by norm_num : 2≠0)] using
      (cauchySeq_iff_tendsto_dist_atTop_0.mp (hc i)).pow 2
  have hs := tendsto_tsum_of_dominated_convergence (hb.mul_left 4) ht
    (Eventually.of_forall fun p i => by
      change |‖contraction (basis i) (u p.1) - contraction (basis i) (u p.2)‖^2| ≤ 4*b i
      rw [abs_of_nonneg (sq_nonneg ‖contraction (basis i) (u p.1) -
        contraction (basis i) (u p.2)‖)]
      exact hd p i)
  have he (p : ℕ × ℕ) :
      (∑' i, ‖contraction (basis i) (u p.1) - contraction (basis i) (u p.2)‖^2) =
        ‖u p.1-u p.2‖^2 := by
    simpa only [map_sub] using (contraction_hasSum (u p.1-u p.2)).tsum_eq
  simp only [he,tsum_zero] at hs
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,dist_eq_norm] using hr

end OperatorDerivativeRewrite.Foundation.BochnerCoefficientCauchy
