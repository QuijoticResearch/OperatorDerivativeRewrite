import Foundation.BochnerL2Dominated
import Mathlib.Analysis.Complex.Norm

/-! Complexification of an actual real L2 isometry. This preserves the
Hilbert norm, rather than using a sup-norm product of real and imaginary parts. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexL2Isometry
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y)

def realPart : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.reCLM.compLpL 2 μ
def imagPart : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.imCLM.compLpL 2 μ
def ofReal : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

def combine (r i : Lp ℝ 2 μ) : Lp ℂ 2 μ := ofReal μ r+Complex.I • ofReal μ i

theorem combine_ae (r i : Lp ℝ 2 μ) : combine μ r i =ᵐ[μ]
    fun x => (r x : ℂ)+Complex.I*(i x : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL r, Complex.ofRealCLM.coeFn_compLpL i,
    Lp.coeFn_add (ofReal μ r) (Complex.I • ofReal μ i),
    Lp.coeFn_smul Complex.I (ofReal μ i)] with x hr hi ha hs
  change ofReal μ r x = _ at hr
  change ofReal μ i x = _ at hi
  rw [combine, ha, Pi.add_apply, hs, Pi.smul_apply, hr, hi]
  simp only [smul_eq_mul]
  rfl

theorem norm_sq_parts (f : Lp ℂ 2 μ) :
    ‖f‖^2 = ‖realPart μ f‖^2+‖imagPart μ f‖^2 := by
  rw [BochnerL2Dominated.norm_sq_integral, BochnerL2Dominated.norm_sq_integral,
    BochnerL2Dominated.norm_sq_integral,
    ← integral_add ((Lp.memLp (realPart μ f)).norm.integrable_sq)
      ((Lp.memLp (imagPart μ f)).norm.integrable_sq)]
  apply integral_congr_ae
  filter_upwards [Complex.reCLM.coeFn_compLpL f, Complex.imCLM.coeFn_compLpL f] with x hr hi
  change realPart μ f x = _ at hr
  change imagPart μ f x = _ at hi
  rw [hr, hi, Complex.sq_norm, Complex.normSq_apply]
  simp only [Real.norm_eq_abs, sq_abs]
  change (f x).re*(f x).re+(f x).im*(f x).im = (f x).re^2+(f x).im^2
  ring

theorem realPart_combine (r i : Lp ℝ 2 μ) : realPart μ (combine μ r i) = r := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLpL (combine μ r i), combine_ae μ r i] with x hr hc
  change realPart μ (combine μ r i) x = _ at hr
  rw [hr, hc]
  simp

theorem imagPart_combine (r i : Lp ℝ 2 μ) : imagPart μ (combine μ r i) = i := by
  apply Lp.ext
  filter_upwards [Complex.imCLM.coeFn_compLpL (combine μ r i), combine_ae μ r i] with x hr hc
  change imagPart μ (combine μ r i) x = _ at hr
  rw [hr, hc]
  simp

theorem combine_parts (f : Lp ℂ 2 μ) : combine μ (realPart μ f) (imagPart μ f) = f := by
  apply Lp.ext
  filter_upwards [combine_ae μ (realPart μ f) (imagPart μ f),
    Complex.reCLM.coeFn_compLpL f, Complex.imCLM.coeFn_compLpL f] with x hc hr hi
  rw [hc]
  change realPart μ f x = (f x).re at hr
  change imagPart μ f x = (f x).im at hi
  rw [hr, hi]
  simpa only [mul_comm] using Complex.re_add_im (f x)

theorem combine_norm_sq (r i : Lp ℝ 2 μ) : ‖combine μ r i‖^2 = ‖r‖^2+‖i‖^2 := by
  rw [norm_sq_parts, realPart_combine, imagPart_combine]

def liftLinear (J : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 ν) : Lp ℂ 2 μ →ₗ[ℝ] Lp ℂ 2 ν :=
  (ofReal ν).toLinearMap.comp (J.toLinearMap.comp (realPart μ).toLinearMap)+
    Complex.I • ((ofReal ν).toLinearMap.comp (J.toLinearMap.comp (imagPart μ).toLinearMap))

theorem liftLinear_apply (J : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 ν) (f : Lp ℂ 2 μ) :
    liftLinear μ ν J f = combine ν (J (realPart μ f)) (J (imagPart μ f)) := rfl

def lift (J : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 ν) : Lp ℂ 2 μ →ₗᵢ[ℝ] Lp ℂ 2 ν where
  toLinearMap := liftLinear μ ν J
  norm_map' f := by
    have he : ‖liftLinear μ ν J f‖^2 = ‖f‖^2 := by
      rw [liftLinear_apply, combine_norm_sq, J.norm_map, J.norm_map, norm_sq_parts]
    nlinarith [norm_nonneg (liftLinear μ ν J f), norm_nonneg f]

theorem lift_apply (J : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 ν) (f : Lp ℂ 2 μ) :
    lift μ ν J f = combine ν (J (realPart μ f)) (J (imagPart μ f)) := rfl

theorem realPart_ofReal (f : Lp ℝ 2 μ) : realPart μ (ofReal μ f) = f := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLpL (ofReal μ f),
    Complex.ofRealCLM.coeFn_compLpL f] with x hr hf
  change realPart μ (ofReal μ f) x = _ at hr
  change ofReal μ f x = _ at hf
  rw [hr, hf]
  simp

theorem imagPart_ofReal (f : Lp ℝ 2 μ) : imagPart μ (ofReal μ f) = 0 := by
  apply Lp.ext
  filter_upwards [Complex.imCLM.coeFn_compLpL (ofReal μ f),
    Complex.ofRealCLM.coeFn_compLpL f, Lp.coeFn_zero ℝ 2 μ] with x hr hf hz
  change imagPart μ (ofReal μ f) x = _ at hr
  change ofReal μ f x = _ at hf
  rw [hr, hf, hz]
  simp

theorem lift_ofReal (J : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 ν) (f : Lp ℝ 2 μ) :
    lift μ ν J (ofReal μ f) = ofReal ν (J f) := by
  rw [lift_apply, realPart_ofReal, imagPart_ofReal, map_zero, combine, map_zero, smul_zero, add_zero]

end OperatorDerivativeRewrite.Foundation.ComplexL2Isometry
