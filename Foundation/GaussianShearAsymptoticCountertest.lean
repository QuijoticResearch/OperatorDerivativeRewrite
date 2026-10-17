import Foundation.GaussianShearTailLimits

/-! Relative-threshold delayed-window countermodels and post-transient denominator divergence. -/
noncomputable section
open Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianShearAsymptoticCountertest
open GaussianShearShellSplit GaussianShearLowAnisotropy GaussianShearShellSeparation
open GaussianShearTailLimits FibonacciShearCentroid LabelledShearCentroid

def relativeDelayedScreening (nu : ℝ) : Prop :=
  ∃ R : ℝ, ∀ N : ℕ, 1 ≤ N → 0 < GaussianShearLowAnisotropy.variance N nu 0 →
    R < highCentroid N nu 0/lowCentroid N nu 0 →
      ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧
        ∀ t : ℝ, a < t → t ≤ b → zeroExtendedCentroid partition nu t < 1

theorem absolute_relative_counterexample (nu : ℝ) (hnu : 0 < nu) (R B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ 0 < GaussianShearLowAnisotropy.variance N nu 0 ∧
      R < highCentroid N nu 0/lowCentroid N nu 0 ∧ B < highCentroid N nu 0 ∧
      ∀ t : ℝ, 0 ≤ t → 1 < zeroExtendedCentroid partition nu t := by
  have hs : 0 < 1+nu*0 := by norm_num
  have hr := (relative_centroid_tendsto_atTop nu 0 hs).eventually_gt_atTop R
  have hb := (high_centroid_tendsto_atTop nu 0 hs).eventually_gt_atTop B
  obtain ⟨N,hN,hR,hB⟩ := ((eventually_ge_atTop 1).and (hr.and hb)).exists
  refine ⟨N,hN,initial_low_variance_positive N hN nu,hR,hB,?_⟩
  intro t ht
  exact zero_extended_centroid_gt_one nu t (by positivity)

theorem no_relative_delayed_screening (nu : ℝ) (hnu : 0 < nu) :
    ¬ relativeDelayedScreening nu := by
  rintro ⟨R,h⟩
  obtain ⟨N,hN,hvar,hR,_,hall⟩ := absolute_relative_counterexample nu hnu R 0
  obtain ⟨a,b,ha,hab,hsmall⟩ := h N hN hvar hR
  have hmid : 0 ≤ (a+b)/2 := by linarith
  have hlarge := hall ((a+b)/2) hmid
  have hbad := hsmall ((a+b)/2) (by linarith) (by linarith)
  linarith

def transient (N : ℕ) (nu t : ℝ) : ℝ := 1/(2*nu*highCentroid N nu t)

theorem transient_tendsto_zero (nu : ℝ) (hnu : 0 < nu) (t : ℝ) (hs : 0 < 1+nu*t) :
    Tendsto (fun N => transient N nu t) atTop (𝓝 0) := by
  have hp : Tendsto (fun N => (2*nu)*highCentroid N nu t) atTop atTop := by
    simpa only [mul_comm] using
      (high_centroid_tendsto_atTop nu t hs).atTop_mul_const (by positivity : 0 < 2*nu)
  have hi : Tendsto (fun N => ((2*nu)*highCentroid N nu t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hp
  simpa only [transient,one_div] using hi

theorem bound_diverges_after_transient (nu : ℝ) (hnu : 0 < nu) (t : ℝ) (ht : 0 < t)
    (C : ℝ) (hC : 0 < C) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, transient N nu t < t ∧
      B < C/(highCentroid N nu t*highMoment N 1 nu t) := by
  have hs : 0 < 1+nu*t := by positivity
  have hlag := (transient_tendsto_zero nu hnu t hs).eventually (eventually_lt_nhds ht)
  have hbound := (positive_bound_tendsto_atTop nu t hs C hC).eventually_gt_atTop B
  exact hlag.and hbound

end OperatorDerivativeRewrite.Foundation.GaussianShearAsymptoticCountertest
