import Foundation.FibonacciAngularRealization

/-! Actual low/high radial shell decomposition of the fixed Gaussian NS shear. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.GaussianShearShellSplit
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianShearFourierTail
open GaussianShearSectorMoments GaussianShearRayMoments GaussianFourierJets
attribute [local instance] Classical.propDecidable

def lowDensity (N p : ℕ) (nu t : ℝ) (k : Wave) : ℝ :=
  if radius k ≤ (N:ℝ)^2 then density p nu t k else 0

def highDensity (N p : ℕ) (nu t : ℝ) (k : Wave) : ℝ :=
  if (N:ℝ)^2 < radius k then density p nu t k else 0

def lowMoment (N p : ℕ) (nu t : ℝ) : ℝ := ∑' k : Wave, lowDensity N p nu t k

def highMoment (N p : ℕ) (nu t : ℝ) : ℝ := ∑' k : Wave, highDensity N p nu t k

def highCentroid (N : ℕ) (nu t : ℝ) : ℝ := highMoment N 2 nu t/highMoment N 1 nu t

def lowCentroid (N : ℕ) (nu t : ℝ) : ℝ := lowMoment N 2 nu t/lowMoment N 1 nu t

theorem low_summable (N p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (lowDensity N p nu t) :=
  summable_filter _ (density_summable p nu t hs) _

theorem high_summable (N p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (highDensity N p nu t) :=
  summable_filter _ (density_summable p nu t hs) _

theorem low_nonnegative (N p : ℕ) (nu t : ℝ) (k : Wave) : 0 ≤ lowDensity N p nu t k := by
  unfold lowDensity
  split_ifs
  · exact density_nonnegative p nu t k
  · rfl

theorem high_nonnegative (N p : ℕ) (nu t : ℝ) (k : Wave) : 0 ≤ highDensity N p nu t k := by
  unfold highDensity
  split_ifs
  · exact density_nonnegative p nu t k
  · rfl

theorem density_split (N p : ℕ) (nu t : ℝ) (k : Wave) :
    lowDensity N p nu t k+highDensity N p nu t k=density p nu t k := by
  by_cases h : radius k ≤ (N:ℝ)^2 <;> simp [lowDensity,highDensity,h,not_lt.mpr,lt_of_not_ge]

theorem moments_split (N p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    lowMoment N p nu t+highMoment N p nu t=moment 0 p nu t+moment 1 p nu t := by
  rw [← total_moment_exact p nu t hs]
  change (∑' k,lowDensity N p nu t k)+(∑' k,highDensity N p nu t k)=_
  rw [← (low_summable N p nu t hs).tsum_add (high_summable N p nu t hs)]
  exact tsum_congr (density_split N p nu t)

theorem axis_radius (m : ℤ) : radius (axis m)=(m:ℝ)^2 := by
  simp [radius,axis,Fin.sum_univ_succ]

theorem axis_density_positive (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (m : ℤ) (hm : m ≠ 0) :
    0 < density p nu t (axis m) := by
  rw [density_axis p nu t hs]
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  have hp := abs_pos.mpr hmR
  unfold bound
  positivity

theorem low_positive (N p : ℕ) (hN : 1 ≤ N) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    0 < lowMoment N p nu t := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hrad : radius (axis 1) ≤ (N:ℝ)^2 := by rw [axis_radius]; norm_num; nlinarith
  have hp : 0 < lowDensity N p nu t (axis 1) := by
    rw [lowDensity,if_pos hrad]
    exact axis_density_positive p nu t hs 1 (by norm_num)
  exact (low_summable N p nu t hs).tsum_pos (low_nonnegative N p nu t) (axis 1) hp

theorem high_positive (N p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    0 < highMoment N p nu t := by
  let m : ℤ := (N:ℤ)+1
  have hm : m ≠ 0 := by dsimp [m]; omega
  have hrad : (N:ℝ)^2 < radius (axis m) := by
    rw [axis_radius]
    dsimp [m]
    push_cast
    nlinarith [sq_nonneg (N:ℝ),Nat.cast_nonneg (α := ℝ) N]
  have hp : 0 < highDensity N p nu t (axis m) := by
    rw [highDensity,if_pos hrad]
    exact axis_density_positive p nu t hs m hm
  exact (high_summable N p nu t hs).tsum_pos (high_nonnegative N p nu t) (axis m) hp

theorem density_two (nu t : ℝ) (k : Wave) : density 2 nu t k=radius k*density 1 nu t k := by
  unfold density
  ring

theorem high_centroid_gt_cutoff (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    (N:ℝ)^2 < highCentroid N nu t := by
  let g : Wave → ℝ := fun k => highDensity N 2 nu t k-(N:ℝ)^2*highDensity N 1 nu t k
  have hg : Summable g := (high_summable N 2 nu t hs).sub
    ((high_summable N 1 nu t hs).mul_left _)
  have hn k : 0 ≤ g k := by
    dsimp [g,highDensity]
    split_ifs with hk
    · rw [density_two]
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right hk.le (density_nonnegative 1 nu t k))
    · simp
  let m : ℤ := (N:ℤ)+1
  have hm : m ≠ 0 := by dsimp [m]; omega
  have hrad : (N:ℝ)^2 < radius (axis m) := by
    rw [axis_radius]
    dsimp [m]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hp : 0 < g (axis m) := by
    dsimp [g]
    rw [highDensity,if_pos hrad,highDensity,if_pos hrad,density_two,← sub_mul]
    exact mul_pos (sub_pos.mpr hrad) (axis_density_positive 1 nu t hs m hm)
  have ht := hg.tsum_pos hn (axis m) hp
  rw [show (∑' k,g k)=highMoment N 2 nu t-(N:ℝ)^2*highMoment N 1 nu t by
    change (∑' k, (highDensity N 2 nu t k-(N:ℝ)^2*highDensity N 1 nu t k))=_
    rw [(high_summable N 2 nu t hs).tsum_sub ((high_summable N 1 nu t hs).mul_left _),tsum_mul_left]
    rfl] at ht
  rw [highCentroid,lt_div_iff₀ (high_positive N 1 nu t hs)]
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianShearShellSplit
