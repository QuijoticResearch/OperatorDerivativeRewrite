import Foundation.GaussianBoundaryLayer
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.L2Space

/-! The persistent Gaussian endpoint layer nevertheless decays in flat boundary L2. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianBoundaryL2Decay
set_option backward.isDefEq.respectTransparency false
open CoerciveMovingBoundary GaussianBoundaryFluxBound

def envelope (c x : ℝ) : ℝ := 4*Real.exp (-3*c*(1-|x|)/2)

theorem inside_square (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 1) : x^2 < 1 := by
  have hp : 0 < (1-x)*(1+x) := mul_pos (by linarith [hx.2]) (by linarith [hx.1])
  nlinarith

theorem derivative_square_bound (a c x : ℝ) (hc : 0 ≤ c) (hx : x^2 < 1) :
    (deriv (fullSquareMean a c) x)^2 ≤ envelope c x := by
  have hd := full_derivative_exponential a c x hc hx
  have hs := (sq_le_sq₀ (abs_nonneg (deriv (fullSquareMean a c) x))
    (show 0 ≤ 2*|x| *Real.exp (-3*c*(radius x)^2/4) by positivity)).mpr hd
  have hr : (radius x)^2=1-x^2 := Real.sq_sqrt (by linarith)
  have he : (Real.exp (-3*c*(radius x)^2/4))^2=Real.exp (-3*c*(1-x^2)/2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    rw [hr]
    ring
  have hid : (2*|x| *Real.exp (-3*c*(radius x)^2/4))^2=
      4*x^2*Real.exp (-3*c*(1-x^2)/2) := by
    rw [mul_pow, mul_pow, sq_abs, he]
    norm_num
  rw [sq_abs, hid] at hs
  have ha : |x| ≤ 1 := (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0:ℝ) ≤ 1)).mp
    (by rw [sq_abs]; linarith)
  have hsq : x^2 ≤ |x| := by
    have hp := mul_nonneg (abs_nonneg x) (sub_nonneg.mpr ha)
    nlinarith [sq_abs x]
  have hm := mul_le_mul_of_nonneg_left hsq hc
  have hexp : Real.exp (-3*c*(1-x^2)/2) ≤ Real.exp (-3*c*(1-|x|)/2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ 4*x^2*Real.exp (-3*c*(1-x^2)/2) := hs
    _ ≤ 4*Real.exp (-3*c*(1-x^2)/2) := by
      nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hx) (Real.exp_pos (-3*c*(1-x^2)/2)).le]
    _ ≤ envelope c x := mul_le_mul_of_nonneg_left hexp (by norm_num)

theorem envelope_continuous (c : ℝ) : Continuous (envelope c) := by unfold envelope; fun_prop

theorem envelope_integrable (c : ℝ) : IntegrableOn (envelope c) (Ioo (-1:ℝ) 1) :=
  ((envelope_continuous c).intervalIntegrable (-1) 1).1.mono_set Ioo_subset_Ioc_self

theorem derivative_square_integrable (a c : ℝ) (hc : 0 ≤ c) :
    IntegrableOn (fun x => (deriv (fullSquareMean a c) x)^2) (Ioo (-1:ℝ) 1) := by
  apply (envelope_integrable c).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact derivative_square_bound a c x hc (inside_square x hx)

theorem derivative_memLp (a c : ℝ) (hc : 0 ≤ c) :
    MemLp (deriv (fullSquareMean a c)) 2 (volume.restrict (Ioo (-1:ℝ) 1)) :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_deriv _ _)).mpr (derivative_square_integrable a c hc)

theorem envelope_half_integral (c : ℝ) (hc : 0 < c) :
    (∫ x in (0:ℝ)..1, envelope c x)=8*(1-Real.exp (-3*c/2))/(3*c) := by
  have hk : (3*c/2) ≠ 0 := ne_of_gt (by positivity)
  have he : (∫ x in (0:ℝ)..1, envelope c x)=
      4*∫ x in (0:ℝ)..1, Real.exp ((3*c/2)*x+(-3*c/2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxi : x ∈ Icc (0:ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
    have hx0 : 0 ≤ x := hxi.1
    unfold envelope
    rw [abs_of_nonneg hx0]
    congr 2
    ring
  rw [he, intervalIntegral.integral_comp_mul_add (f := Real.exp) hk, integral_exp]
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul]
  field_simp
  all_goals ring_nf
  all_goals norm_num

theorem envelope_integral (c : ℝ) (hc : 0 < c) :
    (∫ x in Ioo (-1:ℝ) 1, envelope c x)=16*(1-Real.exp (-3*c/2))/(3*c) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  change window (envelope c) 1=_
  rw [even_window (envelope c) (envelope_continuous c) (by intro x; simp [envelope]),
    envelope_half_integral c hc]
  ring

def errorEnergy (a c : ℝ) : ℝ := ∫ x in Ioo (-1:ℝ) 1, (deriv (fullSquareMean a c) x)^2

theorem errorEnergy_nonneg (a c : ℝ) : 0 ≤ errorEnergy a c :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem errorEnergy_bound (a c : ℝ) (hc : 0 < c) : errorEnergy a c ≤ 16/(3*c) := by
  have hi : errorEnergy a c ≤ ∫ x in Ioo (-1:ℝ) 1, envelope c x := by
    apply integral_mono_ae (derivative_square_integrable a c hc.le) (envelope_integrable c)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact derivative_square_bound a c x hc.le (inside_square x hx)
  rw [envelope_integral c hc] at hi
  have he : 16*(1-Real.exp (-3*c/2))/(3*c) ≤ 16/(3*c) := by
    apply div_le_div_of_nonneg_right
    · nlinarith [Real.exp_pos (-3*c/2)]
    · positivity
  exact hi.trans he

theorem errorEnergy_tolerance (a c ε : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hscale : 16/(3*ε) ≤ c) : errorEnergy a c ≤ ε := by
  have hs := (div_le_iff₀ (by positivity : 0 < 3*ε)).mp hscale
  exact (errorEnergy_bound a c hc).trans ((div_le_iff₀ (by positivity : 0 < 3*c)).mpr (by nlinarith))

/-- The actual squared L2 error vanishes, uniformly in the boundary-potential coefficient. -/
theorem uniform_errorEnergy_decay (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, C ≤ c → ∀ a : ℝ, errorEnergy a c ≤ ε := by
  refine ⟨16/(3*ε), by positivity, ?_⟩
  intro c hc a
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  exact errorEnergy_tolerance a c ε hc0 hε hc

end OperatorDerivativeRewrite.Foundation.GaussianBoundaryL2Decay
