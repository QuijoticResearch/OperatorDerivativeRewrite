import Foundation.IBMConditionalIncrements

/-! Signed overlap of two oriented spatial intervals. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.IBMSpatialOverlap

/-- Signed length of the common part of the oriented intervals from `a` to `b`
and from `c` to `d`. Reversing one interval reverses the sign. -/
def signedOverlap (a b c d : ℝ) : ℝ :=
  (if a ≤ b then 1 else -1) * (if c ≤ d then 1 else -1) *
    max (min (max a b) (max c d) - max (min a b) (min c d)) 0

private theorem ordered_overlap (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    min b d - min b c - min a d + min a c =
      max (min b d - max a c) 0 := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The signed overlap equals the four-term Brownian covariance kernel
for arbitrary interval orientations. -/
theorem signedOverlap_eq_min_covariance (a b c d : ℝ) :
    signedOverlap a b c d =
      min b d - min b c - min a d + min a c := by
  by_cases hab : a ≤ b
  · by_cases hcd : c ≤ d
    · simpa [signedOverlap, hab, hcd, min_eq_left hab, max_eq_right hab,
        min_eq_left hcd, max_eq_right hcd] using
        (ordered_overlap a b c d hab hcd).symm
    · have hdc : d ≤ c := le_of_lt (lt_of_not_ge hcd)
      have h := ordered_overlap a b d c hab hdc
      simp only [signedOverlap, if_pos hab, if_neg hcd, one_mul, mul_neg,
        min_eq_left hab, max_eq_right hab, min_eq_right hdc, max_eq_left hdc]
      linarith
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    by_cases hcd : c ≤ d
    · have h := ordered_overlap b a c d hba hcd
      simp only [signedOverlap, if_neg hab, if_pos hcd, mul_one, neg_mul,
        min_eq_right hba, max_eq_left hba, min_eq_left hcd, max_eq_right hcd]
      linarith
    · have hdc : d ≤ c := le_of_lt (lt_of_not_ge hcd)
      have h := ordered_overlap b a d c hba hdc
      simp only [signedOverlap, if_neg hab, if_neg hcd, neg_mul_neg,
        min_eq_right hba, max_eq_left hba, min_eq_right hdc, max_eq_left hdc]
      linarith


open MeasureTheory ProbabilityTheory
open InfiniteGaussian IBMSourceLaws GaussianHilbertProcess FractionalSpectralKernel
attribute [local instance] spectralSpace_secondCountable

private theorem sceneryBase_memLp (r : ℝ) :
    MemLp (sceneryBase r) 2 gaussianProduct := by
  unfold sceneryBase
  exact isonormal_memLp _ 2 (by simp)

/-- On the nonnegative scenery half-line, Brownian covariance is `min`. -/
theorem sceneryBase_covariance_min (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cov[sceneryBase a, sceneryBase b; gaussianProduct] = min a b := by
  rw [sceneryBase_covariance, abs_of_nonneg ha, abs_of_nonneg hb]
  by_cases hab : a ≤ b
  · rw [abs_of_nonneg (sub_nonneg.mpr hab), min_eq_left hab]
    ring
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    rw [abs_of_nonpos (sub_nonpos.mpr hba), min_eq_right hba]
    ring

/-- Exact conditional-sceneries covariance kernel for two oriented
nonnegative spatial intervals. Temporal disjointness does not appear. -/
theorem sceneryBase_increment_covariance
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    cov[(fun ω => sceneryBase b ω - sceneryBase a ω),
        (fun ω => sceneryBase d ω - sceneryBase c ω); gaussianProduct] =
      signedOverlap a b c d := by
  rw [covariance_fun_sub_fun_sub (sceneryBase_memLp b) (sceneryBase_memLp a)
      (sceneryBase_memLp d) (sceneryBase_memLp c),
    sceneryBase_covariance_min b d hb hd,
    sceneryBase_covariance_min b c hb hc,
    sceneryBase_covariance_min a d ha hd,
    sceneryBase_covariance_min a c ha hc]
  exact (signedOverlap_eq_min_covariance a b c d).symm
end OperatorDerivativeRewrite.Foundation.IBMSpatialOverlap
