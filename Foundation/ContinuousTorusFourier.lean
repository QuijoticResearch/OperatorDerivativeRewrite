import Foundation.GaussianShearFourierTail

/-! Separated-variable Fourier reduction for actual continuous torus fields,
with the same normalized interval integrals as the finite Fourier library. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.ContinuousTorusFourier
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
open GaussianFourierCoefficient GaussianShearFourierTail
set_option backward.isDefEq.respectTransparency false

def average (f : ℝ → ℂ) : ℂ := period⁻¹*(∫ r in (0 : ℝ)..2*Real.pi, f r)

theorem average_mode (n : ℤ) : average (mode n) = if n = 0 then 1 else 0 := by
  have h : (∫ r in (0 : ℝ)..2*Real.pi, mode n r) =
      if n = 0 then period else 0 := exponential_integral n
  rw [average, h]
  by_cases hn : n = 0 <;> simp [hn, period_ne_zero]

theorem update_continuous (j : Fin 3) :
    Continuous (fun p : Space × ℝ => Function.update p.1 j p.2) := by
  apply continuous_pi
  intro i
  by_cases h : i = j <;> simp [Function.update_apply, h] <;> fun_prop

theorem circle_continuous (j : Fin 3) (F : Space → ℂ) (hF : Continuous F) :
    Continuous (circleAverage j F) := by
  have hc : Continuous (Function.uncurry (fun x : Space => fun r : ℝ =>
      F (Function.update x j r))) := hF.comp (update_continuous j)
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hc (0 : ℝ) (2*Real.pi)
  change Continuous (fun x => period⁻¹*(∫ r in (0 : ℝ)..2*Real.pi, F (Function.update x j r)))
  exact continuous_const.mul h

theorem circle_add (j : Fin 3) (F G : Space → ℂ) (hF : Continuous F) (hG : Continuous G) :
    circleAverage j (fun x => F x+G x) = fun x => circleAverage j F x+circleAverage j G x := by
  funext x
  have hu : Continuous (fun r => Function.update x j r) := by
    exact (update_continuous j).comp (continuous_const.prodMk continuous_id)
  have hfi : IntervalIntegrable (fun r => F (Function.update x j r)) volume 0 (2*Real.pi) :=
    (hF.comp hu).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun r => G (Function.update x j r)) volume 0 (2*Real.pi) :=
    (hG.comp hu).intervalIntegrable _ _
  simp only [circleAverage]
  rw [intervalIntegral.integral_add hfi hgi, mul_add]

theorem box_add (F G : Space → ℂ) (hF : Continuous F) (hG : Continuous G) :
    boxAverage (fun x => F x+G x) = boxAverage F+boxAverage G := by
  rw [boxAverage, circle_add 0 F G hF hG,
    circle_add 1 _ _ (circle_continuous 0 F hF) (circle_continuous 0 G hG),
    circle_add 2 _ _ (circle_continuous 1 _ (circle_continuous 0 F hF))
      (circle_continuous 1 _ (circle_continuous 0 G hG))]
  rfl

theorem box_separable (A B C : ℝ → ℂ) :
    boxAverage (fun x => A (x 0)*B (x 1)*C (x 2)) = average A*average B*average C := by
  have h0 : circleAverage 0 (fun x => A (x 0)*B (x 1)*C (x 2)) =
      fun x => average A*B (x 1)*C (x 2) := by
    funext x
    simp [circleAverage, average, intervalIntegral.integral_mul_const, mul_assoc]
  have h1 : circleAverage 1 (fun x => average A*B (x 1)*C (x 2)) =
      fun x => average A*average B*C (x 2) := by
    funext x
    change period⁻¹*(∫ r in (0 : ℝ)..2*Real.pi, average A*B r*C (x 2)) = _
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    unfold average
    ring
  have h2 : circleAverage 2 (fun x => average A*average B*C (x 2)) =
      fun _ => average A*average B*average C := by
    funext x
    change period⁻¹*(∫ r in (0 : ℝ)..2*Real.pi, average A*average B*C r) = _
    rw [intervalIntegral.integral_const_mul]
    unfold average
    ring
  rw [boxAverage, h0, h1, h2]

theorem character_split (k : Wave) (x : Space) :
    character k x = mode (k 0) (x 0)*mode (k 1) (x 1)*mode (k 2) (x 2) := by
  simp [character, phase, mode, Fin.sum_univ_succ, mul_add, Complex.exp_add, mul_assoc]

theorem lift_one (f : ℝ → ℂ) (k : Wave) :
    fourierCoefficient (fun x => f (x 1)) k =
      if k 0 = 0 ∧ k 2 = 0 then coefficient f (k 1) else 0 := by
  have he : (fun x => f (x 1)*character (-k) x) =
      fun x => mode (-(k 0)) (x 0)*(f (x 1)*mode (-(k 1)) (x 1))*mode (-(k 2)) (x 2) := by
    funext x
    rw [character_split]
    simp only [Pi.neg_apply]
    ring
  rw [fourierCoefficient, he, box_separable (mode (-(k 0)))
    (fun r => f r*mode (-(k 1)) r) (mode (-(k 2)))]
  change average (mode (-(k 0)))*coefficient f (k 1)*average (mode (-(k 2))) = _
  rw [average_mode, average_mode]
  by_cases h0 : k 0 = 0 <;> by_cases h2 : k 2 = 0 <;> simp [h0, h2]

theorem lift_two (f : ℝ → ℂ) (k : Wave) :
    fourierCoefficient (fun x => f (x 2)) k =
      if k 0 = 0 ∧ k 1 = 0 then coefficient f (k 2) else 0 := by
  have he : (fun x => f (x 2)*character (-k) x) =
      fun x => mode (-(k 0)) (x 0)*mode (-(k 1)) (x 1)*(f (x 2)*mode (-(k 2)) (x 2)) := by
    funext x
    rw [character_split]
    simp only [Pi.neg_apply]
    ring
  rw [fourierCoefficient, he, box_separable (mode (-(k 0))) (mode (-(k 1)))
    (fun r => f r*mode (-(k 2)) r)]
  change average (mode (-(k 0)))*average (mode (-(k 1)))*coefficient f (k 2) = _
  rw [average_mode, average_mode]
  by_cases h0 : k 0 = 0 <;> by_cases h1 : k 1 = 0 <;> simp [h0, h1]

theorem fourier_add (F G : Space → ℂ) (hF : Continuous F) (hG : Continuous G) (k : Wave) :
    fourierCoefficient (fun x => F x+G x) k = fourierCoefficient F k+fourierCoefficient G k := by
  have he : (fun x => (F x+G x)*character (-k) x) =
      fun x => F x*character (-k) x+G x*character (-k) x := by funext x; ring
  rw [fourierCoefficient, he]
  exact box_add _ _ (hF.mul (character_continuous _)) (hG.mul (character_continuous _))

theorem coefficient_const_mul (c : ℂ) (f : ℝ → ℂ) (m : ℤ) :
    coefficient (fun y => c*f y) m = c*coefficient f m := by
  have he : (fun y => c*f y*mode (-m) y) = fun y => c*(f y*mode (-m) y) := by
    funext y
    ring
  rw [coefficient, he, intervalIntegral.integral_const_mul]
  simp [coefficient, mul_left_comm]

theorem coefficient_add (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) (m : ℤ) :
    coefficient (fun y => f y+g y) m = coefficient f m+coefficient g m := by
  have hm : Continuous (mode (-m)) := by unfold mode; fun_prop
  have hfi : IntervalIntegrable (fun y => f y*mode (-m) y) volume 0 (2*Real.pi) :=
    (hf.mul hm).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun y => g y*mode (-m) y) volume 0 (2*Real.pi) :=
    (hg.mul hm).intervalIntegrable _ _
  have he : (fun y => (f y+g y)*mode (-m) y) =
      fun y => f y*mode (-m) y+g y*mode (-m) y := by funext y; ring
  rw [coefficient, he, intervalIntegral.integral_add hfi hgi, mul_add]
  rfl

theorem coefficient_mode (n m : ℤ) : coefficient (mode n) m = if n = m then 1 else 0 := by
  have he : (fun y => mode n y*mode (-m) y) = mode (n-m) := by
    funext y
    rw [← mode_add]
    rfl
  change average (fun y => mode n y*mode (-m) y) = _
  rw [he, average_mode]
  simp [sub_eq_zero]

theorem mode_real (n : ℤ) (y : ℝ) : (mode n y).re = Real.cos ((n : ℝ)*y) := by
  simp [mode, Complex.exp_re, Complex.mul_re, Complex.mul_im]

theorem mode_imag (n : ℤ) (y : ℝ) : (mode n y).im = Real.sin ((n : ℝ)*y) := by
  simp [mode, Complex.exp_im, Complex.mul_re, Complex.mul_im]

theorem sine_modes (y : ℝ) : (Real.sin y : ℂ) =
    (-Complex.I/2)*mode 1 y+(Complex.I/2)*mode (-1) y := by
  apply Complex.ext
  · change Real.sin y = _
    norm_num [Complex.add_re, Complex.mul_re, mode_real, mode_imag]
    <;> ring
  · change (0 : ℝ) = _
    norm_num [Complex.add_im, Complex.mul_im, mode_real, mode_imag]
    <;> ring

theorem coefficient_sine (m : ℤ) : coefficient (fun y => (Real.sin y : ℂ)) m =
    (if m = 1 then -Complex.I/2 else 0)+(if m = -1 then Complex.I/2 else 0) := by
  have he : (fun y => (Real.sin y : ℂ)) =
      fun y => (-Complex.I/2)*mode 1 y+(Complex.I/2)*mode (-1) y := funext sine_modes
  rw [he, coefficient_add]
  · rw [coefficient_const_mul, coefficient_const_mul, coefficient_mode, coefficient_mode]
    by_cases hp : m = 1 <;> by_cases hn : m = -1 <;> simp [hp, hn, eq_comm]
  · unfold mode
    fun_prop
  · unfold mode
    fun_prop

end OperatorDerivativeRewrite.Foundation.ContinuousTorusFourier
