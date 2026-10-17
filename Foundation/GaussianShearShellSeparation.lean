import Foundation.GaussianShearLowAnisotropy

/-! Arbitrarily large actual shell separation with persistent low-shell anisotropy in one fixed flow. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.GaussianShearShellSeparation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianShearSectorMoments
open GaussianShearShellSplit GaussianShearLowAnisotropy FibonacciShearCentroid LabelledShearCentroid
attribute [local instance] Classical.propDecidable

def lowFraction (N : ℕ) (nu t : ℝ) : ℝ :=
  lowMoment N 1 nu t/(lowMoment N 1 nu t+highMoment N 1 nu t)

def highFraction (N : ℕ) (nu t : ℝ) : ℝ :=
  highMoment N 1 nu t/(lowMoment N 1 nu t+highMoment N 1 nu t)

theorem fractions_positive (N : ℕ) (hN : 1 ≤ N) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    0 < lowFraction N nu t ∧ 0 < highFraction N nu t := by
  have hl := low_positive N 1 hN nu t hs
  have hh := high_positive N 1 nu t hs
  exact ⟨div_pos hl (add_pos hl hh),div_pos hh (add_pos hl hh)⟩

theorem fractions_sum (N : ℕ) (hN : 1 ≤ N) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    lowFraction N nu t+highFraction N nu t=1 := by
  unfold lowFraction highFraction
  rw [← add_div]
  exact div_self (ne_of_gt (add_pos (low_positive N 1 hN nu t hs) (high_positive N 1 nu t hs)))

theorem low_centroid_le_cutoff (N : ℕ) (hN : 1 ≤ N) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    lowCentroid N nu t ≤ (N:ℝ)^2 := by
  have hp k : lowDensity N 2 nu t k ≤ (N:ℝ)^2*lowDensity N 1 nu t k := by
    unfold lowDensity
    split_ifs with hk
    · rw [density_two]
      exact mul_le_mul_of_nonneg_right hk (density_nonnegative 1 nu t k)
    · simp
  have ht := (low_summable N 2 nu t hs).tsum_le_tsum hp
    ((low_summable N 1 nu t hs).mul_left ((N:ℝ)^2))
  rw [tsum_mul_left] at ht
  exact (div_le_iff₀ (low_positive N 1 hN nu t hs)).2 ht

theorem centroids_ordered (N : ℕ) (hN : 1 ≤ N) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    0 < lowCentroid N nu t ∧ lowCentroid N nu t < highCentroid N nu t := by
  exact ⟨div_pos (low_positive N 2 hN nu t hs) (low_positive N 1 hN nu t hs),
    (low_centroid_le_cutoff N hN nu t hs).trans_lt (high_centroid_gt_cutoff N nu t hs)⟩

theorem unbounded_cutoff (B : ℝ) : ∃ N : ℕ, 1 ≤ N ∧ B < (N:ℝ)^2 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max B 1)
  have h1 : (1:ℝ) < N := (le_max_right B 1).trans_lt hN
  have hB : B < (N:ℝ) := (le_max_left B 1).trans_lt hN
  refine ⟨N,by exact_mod_cast (by linarith : (1:ℝ) ≤ N),?_⟩
  nlinarith

theorem fixed_flow_separation (nu : ℝ) (hnu : 0 < nu) (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ 0 < GaussianShearLowAnisotropy.variance N nu 0 ∧
      ∀ t : ℝ, 0 ≤ t →
        0 < lowFraction N nu t ∧ 0 < highFraction N nu t ∧
        lowFraction N nu t+highFraction N nu t=1 ∧
        0 < lowCentroid N nu t ∧ lowCentroid N nu t < highCentroid N nu t ∧
        B < highCentroid N nu t ∧
        (3:ℝ)/16 ≤ GaussianShearLowAnisotropy.variance N nu t ∧
        1 < zeroExtendedCentroid partition nu t := by
  obtain ⟨N,hN,hB⟩ := unbounded_cutoff B
  refine ⟨N,hN,initial_low_variance_positive N hN nu,?_⟩
  intro t ht
  have hs : 0 < 1+nu*t := by positivity
  have hf := fractions_positive N hN nu t hs
  have hc := centroids_ordered N hN nu t hs
  exact ⟨hf.1,hf.2,fractions_sum N hN nu t hs,hc.1,hc.2,
    hB.trans (high_centroid_gt_cutoff N nu t hs),low_variance_bound N hN nu t hs,
    zero_extended_centroid_gt_one nu t hs⟩

end OperatorDerivativeRewrite.Foundation.GaussianShearShellSeparation
