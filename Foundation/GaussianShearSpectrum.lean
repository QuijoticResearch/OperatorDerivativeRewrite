import Foundation.ContinuousTorusFourier

/-! Complete integral-defined Fourier spectrum of the fixed Gaussian shear.
The zero mode, both transverse sine modes and every off-axis zero are explicit. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianShearSpectrum
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianFourierJets
open GaussianPeriodicHeat GaussianInfiniteShear GaussianFourierCoefficient
open GaussianShearFourierTail ContinuousTorusFourier
set_option backward.isDefEq.respectTransparency false

def spectrumFormula (nu t : ℝ) (k : Wave) : ℂ :=
  (if k 0 = 0 ∧ k 2 = 0 then 2*(weight (1+nu*t) (k 1) : ℂ) else 0)+
  (if k 0 = 0 ∧ k 1 = 0 then (amplitude nu t : ℂ)*
    ((if k 2 = 1 then -Complex.I/2 else 0)+(if k 2 = -1 then Complex.I/2 else 0)) else 0)

theorem coefficient_formula (nu t : ℝ) (hs : 0 < 1+nu*t) (k : Wave) :
    fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) k = spectrumFormula nu t k := by
  let A : ℝ → ℂ := fun y => 2*(jet 0 (1+nu*t) y : ℂ)
  let B : ℝ → ℂ := fun y => (amplitude nu t : ℂ)*(Real.sin y : ℂ)
  have hA : Continuous A := continuous_const.mul
    (Complex.continuous_ofReal.comp (jet_continuous 0 _ hs))
  have hB : Continuous B := by dsimp [B]; fun_prop
  have h1 : Continuous (fun x : Space => A (x 1)) := hA.comp (continuous_apply 1)
  have h2 : Continuous (fun x : Space => B (x 2)) := hB.comp (continuous_apply 2)
  have he : (fun x => (velocity nu t x 0 : ℂ)) = fun x => A (x 1)+B (x 2) := by
    funext x
    simp [velocity, scalar, profile, A, B]
  rw [he, fourier_add _ _ h1 h2, lift_one, lift_two]
  simp only [A, B, coefficient_const_mul, coefficient_jet _ hs, coefficient_sine,
    spectrumFormula]

theorem coefficient_nonzero_iff (nu t : ℝ) (hs : 0 < 1+nu*t) (k : Wave) :
    fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) k ≠ 0 ↔
      (k 0 = 0 ∧ k 2 = 0) ∨
      (k 0 = 0 ∧ k 1 = 0 ∧ (k 2 = 1 ∨ k 2 = -1)) := by
  rw [coefficient_formula nu t hs]
  have hw : (weight (1+nu*t) (k 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have ha : (amplitude nu t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  by_cases h0 : k 0 = 0
  · by_cases h2 : k 2 = 0
    · simp [spectrumFormula, h0, h2, hw]
    · by_cases h1 : k 1 = 0
      · by_cases hp : k 2 = 1
        · simp [spectrumFormula, h0, h1, hp, ha, Complex.I_ne_zero]
        · by_cases hn : k 2 = -1
          · simp [spectrumFormula, h0, h1, hn, ha, Complex.I_ne_zero]
          · simp [spectrumFormula, h0, h1, h2, hp, hn]
      · simp [spectrumFormula, h0, h1, h2]
  · simp [spectrumFormula, h0]

theorem transverse_plus (nu t : ℝ) (hs : 0 < 1+nu*t) :
    fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (Pi.single 2 1) =
      (amplitude nu t : ℂ)*(-Complex.I/2) := by
  rw [coefficient_formula nu t hs]
  norm_num [spectrumFormula]

theorem transverse_minus (nu t : ℝ) (hs : 0 < 1+nu*t) :
    fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (Pi.single 2 (-1)) =
      (amplitude nu t : ℂ)*(Complex.I/2) := by
  rw [coefficient_formula nu t hs]
  norm_num [spectrumFormula]

theorem zero_mode (nu t : ℝ) (hs : 0 < 1+nu*t) :
    fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) 0 = 2 := by
  rw [coefficient_formula nu t hs]
  norm_num [spectrumFormula, GaussianFourierCoefficient.weight]

theorem axis_all (nu t : ℝ) (hs : 0 < 1+nu*t) (m : ℤ) :
    fourierCoefficient (fun x => (velocity nu t x 0 : ℂ)) (axis m) =
      2*(weight (1+nu*t) m : ℂ) := by
  rw [coefficient_formula nu t hs]
  simp [spectrumFormula, axis]

theorem transverse_plus_normSq (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Complex.normSq (fourierCoefficient (fun x => (velocity nu t x 0 : ℂ))
      (Pi.single 2 1)) = (amplitude nu t)^2/4 := by
  rw [transverse_plus nu t hs]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

theorem transverse_minus_normSq (nu t : ℝ) (hs : 0 < 1+nu*t) :
    Complex.normSq (fourierCoefficient (fun x => (velocity nu t x 0 : ℂ))
      (Pi.single 2 (-1))) = (amplitude nu t)^2/4 := by
  rw [transverse_minus nu t hs]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

theorem other_component_zero (nu t : ℝ) (k : Wave) (i : Fin 3) (hi : i ≠ 0) :
    fourierCoefficient (fun x => (velocity nu t x i : ℂ)) k = 0 := by
  fin_cases i <;> simp_all [velocity, fourierCoefficient, FiniteFourierTorusAverage.boxAverage,
    FiniteFourierTorusAverage.circleAverage]

end OperatorDerivativeRewrite.Foundation.GaussianShearSpectrum
