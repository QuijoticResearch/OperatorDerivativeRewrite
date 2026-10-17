import Foundation.FourierPathControlGradient
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Frechet derivatives of actual heat-smoothed coefficient orbits under bounded time controls. -/
noncomputable section
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathControlFrechetSeries
open L1SeriesSynthesis FourierPathBoundedControls FourierPathControlSymbols
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslations HigherHeatFourierPathSemigroup FourierPathDirectionalCharacters
open FourierPathControlGradientSeries

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def phase (i : ℕ) (u : Control) : ℂ :=
  Complex.exp (Complex.I*(frequencyMap levels ξ i u : ℂ))

theorem phase_character (i : ℕ) (u : Control) :
    phase levels ξ i u = characterTest levels ξ i (direction u) := by
  have he : scalePath 1 (direction u) = direction u := by
    apply Subtype.ext
    exact one_smul ℝ (direction u).val
  have hh := character_along levels ξ (direction u) i 1
  rw [he] at hh
  simpa only [phase, wave, one_mul, frequencyMap_apply] using hh.symm

def phaseDerivative (i : ℕ) (u : Control) : Control →L[ℝ] ℂ :=
  (frequencyMap levels ξ i).smulRight (Complex.I*phase levels ξ i u)

theorem phase_hasFDerivAt (i : ℕ) (u : Control) :
    HasFDerivAt (phase levels ξ i) (phaseDerivative levels ξ i u) u := by
  let L : Control →L[ℝ] ℂ := Complex.I • (Complex.ofRealCLM.comp (frequencyMap levels ξ i))
  have hh := (L.hasFDerivAt (x := u)).cexp
  change HasFDerivAt (fun v => Complex.exp (L v)) (phaseDerivative levels ξ i u) u
  convert hh using 1
  ext v
  simp [L, phaseDerivative, phase, Complex.real_smul]
  ring

def mode (a : Coeff) (m : ℕ) (T : ℝ≥0) (i : ℕ) (u : Control) : Coeff :=
  lp.single 1 i (a i*multiplier levels ξ m T i*phase levels ξ i u)

theorem mode_hasFDerivAt (a : Coeff) (m : ℕ) (T : ℝ≥0) (i : ℕ) (u : Control) :
    HasFDerivAt (mode levels ξ a m T i)
      ((a i*phase levels ξ i u) • atom levels ξ m T i) u := by
  have hh := (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℂ) 1 i).hasFDerivAt.comp u
    ((phase_hasFDerivAt levels ξ i u).const_mul (a i*multiplier levels ξ m T i))
  convert hh using 1
  · funext v
    change lp.single 1 i (_*_) = lp.single 1 i (_*_)
    congr 1
  · ext v j
    by_cases hj : j=i
    · subst j
      simp [atom, symbolMap, phaseDerivative, lp.coeFn_single, Complex.real_smul]
      ring
    · simp [atom, symbolMap, phaseDerivative, lp.coeFn_single, hj, Ne.symm hj]

theorem mode_bound (a : Coeff) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (i : ℕ) (u : Control) :
    ‖mode levels ξ a m T i u‖ ≤ ‖a i‖ := by
  rw [mode, lp.norm_single (by norm_num : (0:ℝ≥0∞)<1), norm_mul, norm_mul,
    phase_character, value_norm, mul_one]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (multiplier_bound levels ξ m T i) (norm_nonneg (a i))

theorem derivative_bound (a : Coeff) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (i : ℕ) (u : Control) :
    ‖(a i*phase levels ξ i u) • atom levels ξ m T i‖ ≤ ‖a i‖*(1+(T:ℝ)⁻¹) := by
  rw [norm_smul, norm_mul, phase_character, value_norm, mul_one]
  exact mul_le_mul_of_nonneg_left (atom_bound levels ξ m hm T hT i) (norm_nonneg _)

theorem mode_sum (a : Coeff) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (u : Control) :
    (∑' i, mode levels ξ a m T i u) =
      diagonal levels ξ (direction u) (coefficientEvolution levels ξ m T a) := by
  have hh := lp.hasSum_single (p := 1) (by simp)
    (diagonal levels ξ (direction u) (coefficientEvolution levels ξ m T a))
  have he : (fun i => mode levels ξ a m T i u) =
      (fun i => lp.single 1 i
        (diagonal levels ξ (direction u) (coefficientEvolution levels ξ m T a) i)) := by
    funext i
    rw [mode, phase_character]
    rfl
  rw [he]
  exact hh.tsum_eq

theorem coefficient_orbit_hasFDerivAt (a : Coeff) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (u : Control) :
    HasFDerivAt (fun v => diagonal levels ξ (direction v) (coefficientEvolution levels ξ m T a))
      (family levels ξ m hm T hT (diagonal levels ξ (direction u) a)) u := by
  have hs : Summable (fun i => mode levels ξ a m T i (0:Control)) :=
    (coeff_summable a).of_norm_bounded (mode_bound levels ξ a m hm T · 0)
  have hh := hasFDerivAt_tsum ((coeff_summable a).mul_right (1+(T:ℝ)⁻¹))
    (mode_hasFDerivAt levels ξ a m T) (derivative_bound levels ξ a m hm T hT) hs u
  have he : (fun v => ∑' i, mode levels ξ a m T i v) =
      (fun v => diagonal levels ξ (direction v) (coefficientEvolution levels ξ m T a)) := by
    funext v
    exact mode_sum levels ξ a m hm T v
  rw [he] at hh
  convert hh using 1
  change (∑' i, diagonal levels ξ (direction u) a i • atom levels ξ m T i) = _
  congr 1
  funext i
  rw [phase_character]
  rfl

end OperatorDerivativeRewrite.Foundation.FourierPathControlFrechetSeries
