import Foundation.GaussianShearNoScreening
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.Order.Field

/-! Actual shell-tail limits, relative centroid separation, and the high-energy denominator obstruction. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianShearTailLimits
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianShearSectorMoments
open GaussianShearFourierTail GaussianShearShellSplit
attribute [local instance] Classical.propDecidable

theorem cutoff_eventually (a : ℝ) : ∀ᶠ N : ℕ in atTop, a ≤ (N:ℝ)^2 := by
  have ht : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (max a 1)] with N hN
  have h1 : (1:ℝ) ≤ N := (le_max_right a 1).trans hN
  have ha : a ≤ (N:ℝ) := (le_max_left a 1).trans hN
  have hp := mul_nonneg (by linarith : 0 ≤ (N:ℝ)-1) (Nat.cast_nonneg (α := ℝ) N)
  nlinarith

theorem high_norm_bound (N p : ℕ) (nu t : ℝ) (k : Wave) :
    ‖highDensity N p nu t k‖ ≤ density p nu t k := by
  unfold highDensity
  split_ifs
  · rw [Real.norm_eq_abs,abs_of_nonneg (density_nonnegative p nu t k)]
  · simpa using density_nonnegative p nu t k

theorem high_density_tendsto_zero (p : ℕ) (nu t : ℝ) (k : Wave) :
    Tendsto (fun N : ℕ => highDensity N p nu t k) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [cutoff_eventually (radius k)] with N hN
  simp [highDensity,not_lt.mpr hN]

theorem high_moment_tendsto_zero (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Tendsto (fun N => highMoment N p nu t) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun N k => highDensity N p nu t k) (g := fun _ : Wave => (0:ℝ))
    (density_summable p nu t hs) (high_density_tendsto_zero p nu t)
    (Eventually.of_forall fun N k => high_norm_bound N p nu t k)
  simpa only [highMoment,tsum_zero] using h

def total (p : ℕ) (nu t : ℝ) : ℝ := moment 0 p nu t+moment 1 p nu t

theorem total_positive (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) : 0 < total p nu t := by
  rw [total,← total_moment_exact p nu t hs]
  exact (density_summable p nu t hs).tsum_pos (density_nonnegative p nu t) (axis 1)
    (axis_density_positive p nu t hs 1 (by norm_num))

theorem low_moment_tendsto_total (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Tendsto (fun N => lowMoment N p nu t) atTop (𝓝 (total p nu t)) := by
  have he (N : ℕ) : total p nu t-highMoment N p nu t=lowMoment N p nu t := by
    have h := moments_split N p nu t hs
    dsimp [total]
    linarith
  have h := (tendsto_const_nhds (x := total p nu t)).sub (high_moment_tendsto_zero p nu t hs)
  simpa only [sub_zero,he] using h

def fullCentroid (nu t : ℝ) : ℝ := total 2 nu t/total 1 nu t

theorem full_centroid_positive (nu t : ℝ) (hs : 0 < 1+nu*t) : 0 < fullCentroid nu t :=
  div_pos (total_positive 2 nu t hs) (total_positive 1 nu t hs)

theorem low_centroid_tendsto_full (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Tendsto (fun N => lowCentroid N nu t) atTop (𝓝 (fullCentroid nu t)) :=
  (low_moment_tendsto_total 2 nu t hs).div (low_moment_tendsto_total 1 nu t hs)
    (ne_of_gt (total_positive 1 nu t hs))

theorem high_centroid_tendsto_atTop (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Tendsto (fun N => highCentroid N nu t) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [cutoff_eventually B] with N hN
  exact hN.trans (high_centroid_gt_cutoff N nu t hs).le

theorem relative_centroid_tendsto_atTop (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Tendsto (fun N => highCentroid N nu t/lowCentroid N nu t) atTop atTop := by
  have hi := (low_centroid_tendsto_full nu t hs).inv₀ (ne_of_gt (full_centroid_positive nu t hs))
  have h := (high_centroid_tendsto_atTop nu t hs).atTop_mul_pos
    (inv_pos.mpr (full_centroid_positive nu t hs)) hi
  simpa only [div_eq_mul_inv] using h

theorem centroid_mass (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    highCentroid N nu t*highMoment N 1 nu t=highMoment N 2 nu t := by
  exact div_mul_cancel₀ _ (ne_of_gt (high_positive N 1 nu t hs))

theorem centroid_mass_tendsto_zero (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Tendsto (fun N => highCentroid N nu t*highMoment N 1 nu t) atTop (𝓝 0) := by
  simpa only [centroid_mass _ nu t hs] using high_moment_tendsto_zero 2 nu t hs

theorem reciprocal_denominator_tendsto_atTop (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Tendsto (fun N => 1/(highCentroid N nu t*highMoment N 1 nu t)) atTop atTop := by
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < highMoment N 2 nu t :=
    Eventually.of_forall fun N => high_positive N 2 nu t hs
  have h0 : Tendsto (fun N => highMoment N 2 nu t) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨high_moment_tendsto_zero 2 nu t hs,hpos⟩
  have h : Tendsto (fun N => (highMoment N 2 nu t)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp h0
  simpa only [one_div,centroid_mass _ nu t hs] using h

theorem positive_bound_tendsto_atTop (nu t : ℝ) (hs : 0 < 1+nu*t) (C : ℝ) (hC : 0 < C) :
    Tendsto (fun N => C/(highCentroid N nu t*highMoment N 1 nu t)) atTop atTop := by
  have h := (reciprocal_denominator_tendsto_atTop nu t hs).atTop_mul_const hC
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using h

end OperatorDerivativeRewrite.Foundation.GaussianShearTailLimits
