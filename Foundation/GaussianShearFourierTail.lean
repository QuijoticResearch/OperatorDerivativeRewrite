import Foundation.GaussianFourierCoefficient
import Foundation.GaussianInfiniteShear

/-! Actual three-dimensional torus Fourier coefficients on the shear axis,
and nonzero frequencies beyond every finite cutoff for one fixed flow. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianShearFourierTail
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
open GaussianFourierJets GaussianPeriodicHeat GaussianInfiniteShear GaussianFourierCoefficient
set_option backward.isDefEq.respectTransparency false

def axis (m : ℤ) : Wave := Pi.single 1 m
def fourierCoefficient (F : Space → ℂ) (k : Wave) : ℂ :=
  boxAverage (fun x => F x*character (-k) x)
def tested (nu t : ℝ) (m : ℤ) (x : Space) : ℂ :=
  (velocity nu t x 0 : ℂ)*mode (-m) (x 1)

theorem character_axis (m : ℤ) (x : Space) : character (-axis m) x = mode (-m) (x 1) := by
  simp [character, phase, axis, mode, Pi.neg_apply, Fin.sum_univ_succ, mul_assoc]

theorem circle_zero (nu t : ℝ) (m : ℤ) (x : Space) :
    circleAverage 0 (tested nu t m) x = tested nu t m x := by
  have he : (fun r => tested nu t m (Function.update x 0 r)) =
      fun _ => tested nu t m x := by
    funext r
    simp [tested, velocity, scalar]
  unfold circleAverage
  rw [he]
  simpa only [circleAverage] using circleAverage_const 0 (tested nu t m x) x

theorem circle_one (nu t : ℝ) (hs : 0 < 1+nu*t) (m : ℤ) (hm : m ≠ 0) (x : Space) :
    circleAverage 1 (tested nu t m) x = 2*(weight (1+nu*t) m : ℂ) := by
  let s := 1+nu*t
  have hj : Continuous (fun r => (jet 0 s r : ℂ)) :=
    Complex.continuous_ofReal.comp (jet_continuous 0 s hs)
  have hc : Continuous (mode (-m)) := by unfold mode; fun_prop
  have h1 : IntervalIntegrable (fun r => (2 : ℂ)*((jet 0 s r : ℂ)*mode (-m) r))
      volume 0 (2*Real.pi) :=
    (continuous_const.mul (hj.mul hc)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun r =>
      (amplitude nu t*Real.sin (x 2) : ℂ)*mode (-m) r) volume 0 (2*Real.pi) :=
    (continuous_const.mul hc).intervalIntegrable _ _
  have he : (fun r => tested nu t m (Function.update x 1 r)) =
      fun r => (2 : ℂ)*((jet 0 s r : ℂ)*mode (-m) r)+
        (amplitude nu t*Real.sin (x 2) : ℂ)*mode (-m) r := by
    funext r
    simp [tested, velocity, scalar, profile, s]
    push_cast
    ring
  have hi : (∫ r in (0 : ℝ)..2*Real.pi, (jet 0 s r : ℂ)*mode (-m) r) =
      period*(weight s m : ℂ) := by
    have h := integral_kernel s hs m
    simpa only [kernel_real s hs] using h
  have hz : (∫ r in (0 : ℝ)..2*Real.pi, mode (-m) r) = 0 := by
    have h : (∫ r in (0 : ℝ)..2*Real.pi, mode (-m) r) =
      if -m = 0 then period else 0 := exponential_integral (-m)
    simpa [hm] using h
  unfold circleAverage
  rw [he, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hi, hz]
  dsimp [s]
  field_simp [period_ne_zero]
  <;> ring

theorem full_coefficient_axis (nu t : ℝ) (hs : 0 < 1+nu*t) (m : ℤ) (hm : m ≠ 0) :
    fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (axis m) =
      2*(weight (1+nu*t) m : ℂ) := by
  have h0 : circleAverage 0 (tested nu t m) = tested nu t m :=
    funext (fun x => circle_zero nu t m x)
  have h1 : circleAverage 1 (tested nu t m) =
      fun _ => 2*(weight (1+nu*t) m : ℂ) :=
    funext (fun x => circle_one nu t hs m hm x)
  change boxAverage (fun x => (velocity nu t x 0 : ℂ)*character (-axis m) x) = _
  simp only [character_axis]
  change boxAverage (tested nu t m) = _
  rw [boxAverage, h0, h1, circleAverage_const]

theorem nonzero_tail (nu t : ℝ) (hs : 0 < 1+nu*t) (N : ℕ) :
    ∃ m : ℤ, (N : ℤ) < m ∧
      fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (axis m) ≠ 0 := by
  refine ⟨(N : ℤ)+1, by omega, ?_⟩
  rw [full_coefficient_axis nu t hs _ (by omega)]
  apply mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))

theorem nonzero_tail_nonnegative (nu t : ℝ) (hnu : 0 ≤ nu) (ht : 0 ≤ t) (N : ℕ) :
    ∃ m : ℤ, (N : ℤ) < m ∧
      fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (axis m) ≠ 0 :=
  nonzero_tail nu t (positive_parameter nu t hnu ht) N

theorem initial_tail (nu : ℝ) (N : ℕ) :
    ∃ m : ℤ, (N : ℤ) < m ∧
      fourierCoefficient (fun x => (velocity nu 0 x 0 : ℂ)) (axis m) ≠ 0 :=
  nonzero_tail nu 0 (by norm_num) N

theorem axis_normSq (nu t : ℝ) (hs : 0 < 1+nu*t) (m : ℤ) (hm : m ≠ 0) :
    Complex.normSq (fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (axis m)) =
      4*(weight (1+nu*t) m)^2 := by
  rw [full_coefficient_axis nu t hs m hm]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

theorem weight_square (s : ℝ) (m : ℤ) : (weight s m)^2 = weight (2*s) m := by
  unfold GaussianFourierCoefficient.weight
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem axis_moment_summable (nu t : ℝ) (hs : 0 < 1+nu*t) (p : ℕ) (hp : 0 < p) :
    Summable (fun m : ℤ => |(m : ℝ)|^p*
      Complex.normSq (fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (axis m))) := by
  have hb := (bound_summable p (2*(1+nu*t)) (by positivity)).mul_left 4
  convert hb using 1
  funext m
  by_cases hm : m = 0
  · subst m
    simp [bound, zero_pow (by omega : p ≠ 0)]
  · rw [axis_normSq nu t hs m hm, weight_square]
    unfold bound GaussianFourierCoefficient.weight
    ring

theorem enstrophy_axis_summable (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (fun m : ℤ => |(m : ℝ)|^2*
      Complex.normSq (fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (axis m))) :=
  axis_moment_summable nu t hs 2 (by omega)

theorem dissipation_axis_summable (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Summable (fun m : ℤ => |(m : ℝ)|^4*
      Complex.normSq (fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (axis m))) :=
  axis_moment_summable nu t hs 4 (by omega)

end OperatorDerivativeRewrite.Foundation.GaussianShearFourierTail
