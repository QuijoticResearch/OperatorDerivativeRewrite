import Foundation.GaussianSwirlVelocity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Parameter-integral derivatives of every order for the regular swirl profile. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianSwirlProfileMoments
open GaussianSwirlVelocity
set_option backward.isDefEq.respectTransparency false

def moment (n : ℕ) (s : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, (-t)^n * Real.exp (-t*s))/2

theorem moment_hasDerivAt (n : ℕ) (s₀ : ℝ) :
    HasDerivAt (moment n) (moment (n+1) s₀) s₀ := by
  let F (s t : ℝ) := (-t)^n * Real.exp (-t*s)
  let G (s t : ℝ) := (-t)^(n+1) * Real.exp (-t*s)
  let B : ℝ := Real.exp (|s₀|+1)
  have hs : Ioo (s₀-1) (s₀+1) ∈ 𝓝 s₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hb : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ s ∈ Ioo (s₀-1) (s₀+1), ‖G s t‖ ≤ B := by
    filter_upwards with t ht s hs
    have htt : 0 < t ∧ t ≤ 1 := by
      simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num), mem_Ioc] using ht
    have hsa : |s| ≤ |s₀|+1 := by
      rw [abs_le]
      constructor <;> linarith [le_abs_self s₀, neg_abs_le s₀, hs.1, hs.2]
    have hexp : Real.exp (-t*s) ≤ B := by
      apply Real.exp_le_exp.mpr
      calc
        -t*s ≤ |t*s| := by rw [neg_mul]; exact neg_le_abs _
        _ = t*|s| := by rw [abs_mul, abs_of_nonneg htt.1.le]
        _ ≤ |s| := by nlinarith [abs_nonneg s]
        _ ≤ |s₀|+1 := hsa
    have hp : |(-t)^(n+1)| ≤ 1 := by
      rw [abs_pow, abs_neg, abs_of_nonneg htt.1.le]
      exact pow_le_one₀ htt.1.le htt.2
    change ‖(-t)^(n+1)*Real.exp (-t*s)‖ ≤ B
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ 1 * Real.exp (-t*s) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ ≤ B := by simpa using hexp
  have hd : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ s ∈ Ioo (s₀-1) (s₀+1),
      HasDerivAt (fun s => F s t) (G s t) s := by
    filter_upwards with t ht s hs
    have hh := (((hasDerivAt_id s).const_mul (-t)).exp).const_mul ((-t)^n)
    convert hh using 1 <;> dsimp [F, G] <;> simp only [pow_succ] <;> ring
  obtain ⟨_, hh⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall (fun s => show AEStronglyMeasurable (F s)
      (volume.restrict (Ι (0 : ℝ) 1)) from by unfold F; fun_prop))
    (show IntervalIntegrable (F s₀) volume 0 1 from
      (by unfold F; fun_prop : Continuous (F s₀)).intervalIntegrable 0 1)
    (show AEStronglyMeasurable (G s₀) (volume.restrict (Ι (0 : ℝ) 1)) from by unfold G; fun_prop)
    hb (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume 0 1) hd
  exact hh.div_const 2

theorem moment_zero : moment 0 = angularProfile := by
  funext s
  simp only [moment, angularProfile, pow_zero, one_mul]

theorem moment_one : moment 1 = angularDerivative := by
  funext s
  simp only [moment, angularDerivative, pow_one]

theorem moment_contDiff (n k : ℕ) : ContDiff ℝ k (moment n) := by
  induction k generalizing n with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun s => (moment_hasDerivAt n s).continuousAt))
  | succ k ih =>
    change ContDiff ℝ ((k : ℕ∞ω)+1) (moment n)
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun s => (moment_hasDerivAt n s).differentiableAt, by simp, ?_⟩
    have he : deriv (moment n) = moment (n+1) :=
      funext (fun s => (moment_hasDerivAt n s).deriv)
    rw [he]
    exact ih (n+1)

theorem moment_smooth (n : ℕ) : ContDiff ℝ ∞ (moment n) :=
  contDiff_infty.mpr (fun k => moment_contDiff n k)

theorem angularProfile_smooth : ContDiff ℝ ∞ angularProfile := by
  rw [← moment_zero]
  exact moment_smooth 0

theorem radialPressure_smooth : ContDiff ℝ ∞ radialPressure := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (radialPressure_hasDerivAt s).differentiableAt, ?_⟩
  have he : deriv radialPressure = fun s => angularProfile s^2/2 :=
    funext (fun s => (radialPressure_hasDerivAt s).deriv)
  rw [he]
  exact (angularProfile_smooth.pow 2).div_const 2

def angularSecond : ℝ → ℝ := moment 2

theorem angularDerivative_hasDerivAt (s : ℝ) :
    HasDerivAt angularDerivative (angularSecond s) s := by
  change HasDerivAt angularDerivative (moment (1+1) s) s
  simpa only [moment_one] using moment_hasDerivAt 1 s

theorem angular_second_identity (s : ℝ) :
    4*angularDerivative s + 2*s*angularSecond s = -Real.exp (-s) := by
  have hd := ((angularProfile_hasDerivAt s).const_mul 2).add
    (((hasDerivAt_id s).const_mul 2).mul (angularDerivative_hasDerivAt s))
  have hf : (fun t => 2*angularProfile t + 2*t*angularDerivative t) =
      fun t => Real.exp (-t) := funext angular_curl_identity
  change HasDerivAt (fun t => 2*angularProfile t+2*t*angularDerivative t)
    (2*angularDerivative s + (2*1*angularDerivative s+2*s*angularSecond s)) s at hd
  rw [hf] at hd
  have he := hd.unique ((hasDerivAt_id s).neg.exp)
  change 2*angularDerivative s + (2*1*angularDerivative s+2*s*angularSecond s) =
    Real.exp (-s)*(-1) at he
  nlinarith

theorem derivative_x (x y : ℝ) :
    HasDerivAt (fun t => angularDerivative (t^2+y^2))
      (2*x*angularSecond (x^2+y^2)) x := by
  have hs : HasDerivAt (fun t : ℝ => t^2+y^2) (2*x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y^2)
  have hh := (angularDerivative_hasDerivAt (x^2+y^2)).comp x hs
  change HasDerivAt (fun t => angularDerivative (t^2+y^2))
    (angularSecond (x^2+y^2)*(2*x)) x at hh
  convert hh using 1 <;> ring

theorem derivative_y (x y : ℝ) :
    HasDerivAt (fun t => angularDerivative (x^2+t^2))
      (2*y*angularSecond (x^2+y^2)) y := by
  have hs : HasDerivAt (fun t : ℝ => x^2+t^2) (2*y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (x^2)
  have hh := (angularDerivative_hasDerivAt (x^2+y^2)).comp y hs
  change HasDerivAt (fun t => angularDerivative (x^2+t^2))
    (angularSecond (x^2+y^2)*(2*y)) y at hh
  convert hh using 1 <;> ring

end OperatorDerivativeRewrite.Foundation.GaussianSwirlProfileMoments
