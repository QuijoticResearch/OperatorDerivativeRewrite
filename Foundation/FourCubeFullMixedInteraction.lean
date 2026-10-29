import Foundation.FourCubeScalarCalibration
import Foundation.FourCubeThermalMixedDifference

/-! Actual full32 thermal three-source interaction, invariant under pairwise scalar
counterterms. No physical transfer-endpoint identification is assumed. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullMixedInteraction
open FourCubeThermalMixedDifference (cornerSum)
open FourCubeActualErrorBudget (rayFreeEnergy ray_odd_limit coefficient)

def c : ℝ := 1784975/2750517
def freeEnergy (beta x y z : ℝ) : ℝ :=
  FourCubeCompletedHaar.standardFreeEnergy beta (FourCubeCompletedHaar.angles x y z)
def odd (t x y z : ℝ) : ℝ :=
  (rayFreeEnergy x y z t-rayFreeEnergy x y z (-t))/(2*t)
def thermalResponse (t : ℝ) : ℝ := cornerSum (freeEnergy (1/t^2)) t/(8*t)

theorem c_positive : 0 < c := by norm_num [c]

theorem ray_neg (t x y z : ℝ) :
    rayFreeEnergy x y z (-t)=rayFreeEnergy (-x) (-y) (-z) t := by
  simp only [rayFreeEnergy,FourCubeFullHaarGaussianLimit.parameters,neg_sq,neg_mul,mul_neg]

theorem odd_limit (x y z : ℝ) :
    Tendsto (fun t => odd t x y z) (𝓝[≠] 0) (𝓝 (c*x*y*z)) := by
  simpa only [odd,c,coefficient] using ray_odd_limit x y z

theorem thermal_pairing (t : ℝ) :
    thermalResponse t=(odd t 1 1 1-odd t 1 (-1) 1-odd t 1 1 (-1)+odd t 1 (-1) (-1))/4 := by
  by_cases ht : t=0
  · subst t; simp [thermalResponse,odd]
  · simp only [odd,ray_neg,rayFreeEnergy,FourCubeFullHaarGaussianLimit.parameters,
      mul_one,mul_neg,mul_neg_one,neg_neg,thermalResponse,cornerSum,freeEnergy]
    field_simp [ht]
    ring

theorem actual_thermal_mixed_limit : Tendsto thermalResponse (𝓝[≠] 0) (𝓝 c) := by
  have h := ((((odd_limit 1 1 1).sub (odd_limit 1 (-1) 1)).sub
    (odd_limit 1 1 (-1))).add (odd_limit 1 (-1) (-1))).div_const 4
  simp only [mul_one,mul_neg_one,neg_neg] at h
  convert! h using 1
  · funext t
    exact thermal_pairing t
  · ring

/-- All scalar terms missing at least one source cancel, with no regularity assumption. -/
theorem corner_pairwise_invariant (F : ℝ → ℝ → ℝ → ℝ)
    (A B C : ℝ → ℝ → ℝ) (h : ℝ) :
    cornerSum (fun x y z => F x y z+A x y+B y z+C z x) h=cornerSum F h := by
  unfold cornerSum
  ring

theorem actual_counterterm_limit (A B C : ℝ → ℝ → ℝ → ℝ) :
    Tendsto (fun t : ℝ => cornerSum (fun x y z =>
      freeEnergy (1/t^2) x y z+A t x y+B t y z+C t z x) t/(8*t))
      (𝓝[≠] 0) (𝓝 c) := by
  apply OperatorDerivativeRewrite.Foundation.FourCubeFullMixedInteraction.actual_thermal_mixed_limit.congr'
  filter_upwards with t
  change cornerSum (freeEnergy (1/t^2)) t/(8*t)=_
  rw [corner_pairwise_invariant]

theorem actual_counterterm_eventually_positive (A B C : ℝ → ℝ → ℝ → ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,0 < cornerSum (fun x y z =>
      freeEnergy (1/t^2) x y z+A t x y+B t y z+C t z x) t := by
  have hf : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun t ht => ne_of_gt ht)
  have h := ((actual_counterterm_limit A B C).mono_left hf).eventually (eventually_gt_nhds c_positive)
  filter_upwards [h,self_mem_nhdsWithin] with t hq ht
  exact (div_pos_iff_of_pos_right (mul_pos (by norm_num) ht)).mp hq

end OperatorDerivativeRewrite.Foundation.FourCubeFullMixedInteraction
