import Foundation.FourierPathDualGradient
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Frechet derivatives of actual heat-smoothed coefficient orbits under conjugate-exponent time controls. -/
noncomputable section
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualFrechetSeries
open L1SeriesSynthesis FourierPathDualControls FourierPathDualDamping
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslations HigherHeatFourierPathSemigroup FourierPathDirectionalCharacters
open FourierPathDualGradientSeries

variable (m : ℕ) [h : Fact (0 < m)]

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def phase (i : ℕ) (u : Control m) : ℂ :=
  Complex.exp (Complex.I*(frequencyMap levels ξ m i u : ℂ))

theorem phase_character (i : ℕ) (u : Control m) :
    phase m levels ξ i u = characterTest levels ξ i (direction m u) := by
  have he : scalePath 1 (direction m u) = direction m u := by
    apply Subtype.ext
    exact one_smul ℝ (direction m u).val
  have hh := character_along levels ξ (direction m u) i 1
  rw [he] at hh
  simpa only [phase, wave, one_mul, frequencyMap_apply] using hh.symm

def phaseDerivative (i : ℕ) (u : Control m) : Control m →L[ℝ] ℂ :=
  (frequencyMap levels ξ m i).smulRight (Complex.I*phase m levels ξ i u)

theorem phase_hasFDerivAt (i : ℕ) (u : Control m) :
    HasFDerivAt (phase m levels ξ i) (phaseDerivative m levels ξ i u) u := by
  let L : Control m →L[ℝ] ℂ := Complex.I • (Complex.ofRealCLM.comp (frequencyMap levels ξ m i))
  have hh := (L.hasFDerivAt (x := u)).cexp
  change HasFDerivAt (fun v => Complex.exp (L v)) (phaseDerivative m levels ξ i u) u
  convert hh using 1
  ext v
  simp [L, phaseDerivative, phase, Complex.real_smul]
  ring

def mode (a : Coeff) (T : ℝ≥0) (i : ℕ) (u : Control m) : Coeff :=
  lp.single 1 i (a i*multiplier levels ξ m T i*phase m levels ξ i u)

theorem mode_hasFDerivAt (a : Coeff) (T : ℝ≥0) (i : ℕ) (u : Control m) :
    HasFDerivAt (mode m levels ξ a T i)
      ((a i*phase m levels ξ i u) • FourierPathDualGradientSeries.atom levels ξ m T i) u := by
  have hh := (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℂ) 1 i).hasFDerivAt.comp u
    ((phase_hasFDerivAt m levels ξ i u).const_mul (a i*multiplier levels ξ m T i))
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

theorem mode_bound (a : Coeff) (T : ℝ≥0) (i : ℕ) (u : Control m) :
    ‖mode m levels ξ a T i u‖ ≤ ‖a i‖ := by
  rw [mode, lp.norm_single (by norm_num : (0:ℝ≥0∞)<1), norm_mul, norm_mul,
    phase_character, value_norm, mul_one]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (multiplier_bound levels ξ m T i) (norm_nonneg (a i))

theorem derivative_bound (a : Coeff) (T : ℝ≥0) (hT : 0 < T)
    (i : ℕ) (u : Control m) :
    ‖(a i*phase m levels ξ i u) • FourierPathDualGradientSeries.atom levels ξ m T i‖ ≤ ‖a i‖*(1+(T:ℝ)⁻¹) := by
  rw [norm_smul, norm_mul, phase_character, value_norm, mul_one]
  exact mul_le_mul_of_nonneg_left (atom_bound levels ξ m T hT i) (norm_nonneg _)

theorem mode_sum (a : Coeff) (T : ℝ≥0) (u : Control m) :
    (∑' i, mode m levels ξ a T i u) =
      diagonal levels ξ (direction m u) (coefficientEvolution levels ξ m T a) := by
  have hh := lp.hasSum_single (p := 1) (by simp)
    (diagonal levels ξ (direction m u) (coefficientEvolution levels ξ m T a))
  have he : (fun i => mode m levels ξ a T i u) =
      (fun i => lp.single 1 i
        (diagonal levels ξ (direction m u) (coefficientEvolution levels ξ m T a) i)) := by
    funext i
    rw [mode, phase_character]
    rfl
  rw [he]
  exact hh.tsum_eq

theorem coefficient_orbit_hasFDerivAt (a : Coeff)
    (T : ℝ≥0) (hT : 0 < T) (u : Control m) :
    HasFDerivAt (fun v => diagonal levels ξ (direction m v) (coefficientEvolution levels ξ m T a))
      (family levels ξ m T hT (diagonal levels ξ (direction m u) a)) u := by
  have hs : Summable (fun i => mode m levels ξ a T i (0:Control m)) :=
    (coeff_summable a).of_norm_bounded (mode_bound m levels ξ a T · 0)
  have hh := hasFDerivAt_tsum ((coeff_summable a).mul_right (1+(T:ℝ)⁻¹))
    (mode_hasFDerivAt m levels ξ a T) (derivative_bound m levels ξ a T hT) hs u
  have he : (fun v => ∑' i, mode m levels ξ a T i v) =
      (fun v => diagonal levels ξ (direction m v) (coefficientEvolution levels ξ m T a)) := by
    funext v
    exact mode_sum m levels ξ a T v
  rw [he] at hh
  convert hh using 1
  rw [family_tsum]
  apply tsum_congr
  intro i
  rw [phase_character]
  rfl

end OperatorDerivativeRewrite.Foundation.FourierPathDualFrechetSeries
