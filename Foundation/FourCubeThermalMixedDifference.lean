import Foundation.FourCubeHarmonicAmplitude

/-! Actual mixed thermal-window free-energy response, obtained without derivative interchange. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeThermalMixedDifference
open FourCubeScaledBoundaryControl FourCubeCubicFreeEnergy FourCubeHarmonicAmplitude
open FourCubeIntegratedCubic

def c : ℝ := 31877443263/69438734552

def freeEnergy (β x y z : ℝ) : ℝ := -Real.log (normalizedPartition β (boundaryData x y z))

def ray (t x y z : ℝ) : ℝ := freeEnergy (1/t^2) (t*x) (t*y) (t*z)

def odd (t x y z : ℝ) : ℝ := (ray t x y z-ray (-t) x y z)/(2*t)

def cornerSum (F : ℝ → ℝ → ℝ → ℝ) (h : ℝ) : ℝ :=
  F h h h-F h (-h) h-F h h (-h)+F h (-h) (-h)-
  F (-h) (-h) (-h)+F (-h) h (-h)+F (-h) (-h) h-F (-h) h h

def difference (β h : ℝ) : ℝ := cornerSum (freeEnergy β) h/(8*h^3)

def thermalResponse (t : ℝ) : ℝ := cornerSum (freeEnergy (1/t^2)) t/(8*t)

theorem c_positive : 0 < c := by norm_num [c]

theorem ray_neg (t x y z : ℝ) : ray (-t) x y z=ray t (-x) (-y) (-z) := by
  simp only [ray,neg_sq,neg_mul,mul_neg]

theorem odd_limit (x y z : ℝ) :
    Tendsto (fun t => odd t x y z) (𝓝[≠] 0) (𝓝 (c*x*y*z)) := by
  have hh := actual_freeEnergy_harmonic_odd_limit x y z
  rw [FourCubeHarmonicAmplitude.harmonic_amplitudes] at hh
  simpa only [odd,ray,freeEnergy,movingBoundary,neg_sq,sub_eq_add_neg,neg_neg,c] using hh

theorem thermal_pairing (t : ℝ) :
    thermalResponse t=(odd t 1 1 1-odd t 1 (-1) 1-odd t 1 1 (-1)+odd t 1 (-1) (-1))/4 := by
  by_cases ht : t=0
  · subst t; simp [thermalResponse,odd]
  · simp only [odd,ray_neg,ray,mul_one,mul_neg,mul_neg_one,neg_neg,thermalResponse,cornerSum]
    field_simp [ht]
    ring

theorem actual_thermal_mixed_limit : Tendsto thermalResponse (𝓝[≠] 0) (𝓝 c) := by
  have hh := ((((odd_limit 1 1 1).sub (odd_limit 1 (-1) 1)).sub
    (odd_limit 1 1 (-1))).add (odd_limit 1 (-1) (-1))).div_const 4
  simp only [mul_one,mul_neg_one,neg_neg] at hh
  convert! hh using 1
  · funext t
    exact thermal_pairing t
  · ring

theorem thermal_scaling (t : ℝ) : t^2*difference (1/t^2) t=thermalResponse t := by
  by_cases ht : t=0
  · subst t; simp [thermalResponse]
  · unfold difference thermalResponse
    field_simp [ht]
    <;> ring

theorem actual_scaled_third_difference_limit :
    Tendsto (fun t : ℝ => t^2*difference (1/t^2) t) (𝓝[≠] 0) (𝓝 c) := by
  simpa only [thermal_scaling] using actual_thermal_mixed_limit

theorem actual_third_difference_lower :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, c/(2*t^2) < difference (1/t^2) t := by
  have hh := actual_scaled_third_difference_limit.eventually
    (eventually_gt_nhds (show c/2 < c by linarith [c_positive]))
  filter_upwards [hh,self_mem_nhdsWithin] with t ht htn
  have hp : 0 < t^2 := sq_pos_of_ne_zero htn
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) hp)).mpr
  nlinarith

theorem actual_difference_eventually_gt (R : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, R < difference (1/t^2) t := by
  have hi : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun t : ℝ => t^2*R) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ)≠0),zero_mul] using (hi.pow 2).mul_const R
  have hs := actual_scaled_third_difference_limit.eventually
    (eventually_gt_nhds (show c/2 < c by linarith [c_positive]))
  have hb := hz.eventually (eventually_lt_nhds (show (0 : ℝ)<c/2 by linarith [c_positive]))
  filter_upwards [hs,hb,self_mem_nhdsWithin] with t ht hb htn
  exact lt_of_mul_lt_mul_left (lt_trans hb ht) (sq_nonneg t)

theorem actual_third_difference_diverges :
    Tendsto (fun t : ℝ => difference (1/t^2) t) (𝓝[≠] 0) atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [actual_difference_eventually_gt R] with t ht
  exact le_of_lt ht

theorem no_uniform_thermal_bound (K : ℝ) :
    ¬ (∀ᶠ t : ℝ in 𝓝[≠] 0, |difference (1/t^2) t| ≤ K) := by
  intro hk
  have hn := (actual_difference_eventually_gt K).and hk
  obtain ⟨t,ht,hb⟩ := hn.exists
  exact (not_lt_of_ge (le_trans (le_abs_self _) hb)) ht

end OperatorDerivativeRewrite.Foundation.FourCubeThermalMixedDifference
