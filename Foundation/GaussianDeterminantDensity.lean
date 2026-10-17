import Foundation.GaussianDeterminantLawTransport
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Direct density identification for the Gaussian determinant law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianDeterminantDensity
set_option backward.isDefEq.respectTransparency false
open GaussianDeterminantConditional GaussianDeterminantLawTransport
open InfiniteGaussian GaussianQuadraticSourceHodge DoubleSkewGaussianBridge

def density (x : ℝ) : ℝ := Real.exp (-|x|/2)/4

theorem density_nonneg (x : ℝ) : 0 ≤ density x := by unfold density; positivity

def weightedPhase (t x : ℝ) : ℂ := (density x : ℂ) * phase t x

theorem weightedPhase_pos (t x : ℝ) (hx : 0 < x) :
    weightedPhase t x = Complex.exp (((-1/2 : ℂ)+(t:ℂ)*Complex.I)*x)/4 := by
  simp only [weightedPhase, density, phase, abs_of_pos hx, Complex.ofReal_div,
    Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_mul]
  rw [div_mul_eq_mul_div, ← Complex.exp_add]
  congr 2
  ring

theorem weightedPhase_nonpos (t x : ℝ) (hx : x ≤ 0) :
    weightedPhase t x = Complex.exp (((1/2 : ℂ)+(t:ℂ)*Complex.I)*x)/4 := by
  simp only [weightedPhase, density, phase, abs_of_nonpos hx, neg_neg, Complex.ofReal_div,
    Complex.ofReal_exp, Complex.ofReal_ofNat, Complex.ofReal_mul]
  rw [div_mul_eq_mul_div, ← Complex.exp_add]
  congr 2
  ring

theorem weightedPhase_integrable (t : ℝ) : Integrable (weightedPhase t) := by
  have hp : IntegrableOn (weightedPhase t) (Ioi 0) :=
    IntegrableOn.congr_fun ((integrableOn_exp_mul_complex_Ioi (a := (-1/2 : ℂ)+(t:ℂ)*Complex.I)
      (by norm_num) 0).div_const 4)
        (fun x hx => (weightedPhase_pos t x hx).symm) measurableSet_Ioi
  have hn : IntegrableOn (weightedPhase t) (Iic 0) :=
    IntegrableOn.congr_fun ((integrableOn_exp_mul_complex_Iic (a := (1/2 : ℂ)+(t:ℂ)*Complex.I)
      (by norm_num) 0).div_const 4)
        (fun x hx => (weightedPhase_nonpos t x hx).symm) measurableSet_Iic
  have hu := hp.union hn
  simpa only [union_comm (Ioi (0:ℝ)) (Iic 0), Iic_union_Ioi, integrableOn_univ] using hu

theorem density_integrable : Integrable density := by
  have h := (weightedPhase_integrable 0).norm
  simpa [weightedPhase, phase, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (density_nonneg _)] using h

theorem weightedPhase_integral (t : ℝ) :
    (∫ x, weightedPhase t x) = ((1/(1+4*t^2) : ℝ) : ℂ) := by
  rw [← integral_add_compl measurableSet_Ioi (weightedPhase_integrable t), compl_Ioi]
  have hp : (∫ x in Ioi 0, weightedPhase t x) =
      -(1 : ℂ)/((-1/2 : ℂ)+(t:ℂ)*Complex.I)/4 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => weightedPhase_pos t x hx),
      integral_div, integral_exp_mul_complex_Ioi (by norm_num)]
    simp
  have hn : (∫ x in Iic 0, weightedPhase t x) =
      (1 : ℂ)/((1/2 : ℂ)+(t:ℂ)*Complex.I)/4 := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun x hx => weightedPhase_nonpos t x hx),
      integral_div, integral_exp_mul_complex_Iic (by norm_num)]
    simp
  rw [hp, hn]
  have hp0 : (-1/2 : ℂ)+(t:ℂ)*Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hn0 : (1/2 : ℂ)+(t:ℂ)*Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hr : (1+4*t^2 : ℝ) ≠ 0 := by positivity
  have hc0 : (1+4*(t:ℂ)^2) ≠ 0 := by exact_mod_cast hr
  push_cast
  field_simp [hp0, hn0, hc0]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  have hp2 : (-1+(t:ℂ)*Complex.I*2) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hn2 : (1+(t:ℂ)*Complex.I*2) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hc2 : (1+(t:ℂ)^2*4) ≠ 0 := by convert hc0 using 1 <;> ring
  field_simp [hp2, hn2, hc2]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

def densityMeasure : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (density x))

instance densityMeasure_finite : IsFiniteMeasure densityMeasure :=
  isFiniteMeasure_withDensity_ofReal density_integrable.2

theorem densityMeasure_charFun (t : ℝ) :
    charFun densityMeasure t = ((1/(1+4*t^2) : ℝ) : ℂ) := by
  rw [charFun_apply_real, densityMeasure,
    integral_withDensity_eq_integral_toReal_smul (by unfold density; fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (density_nonneg _), Complex.real_smul]
  simpa only [weightedPhase, phase, Complex.ofReal_mul] using weightedPhase_integral t

theorem density_integral : (∫ x, density x) = 1 := by
  have h : ((∫ x, density x) : ℂ) = 1 := by
    simpa [weightedPhase, phase, integral_complex_ofReal] using weightedPhase_integral 0
  exact_mod_cast h

/-- Characteristic-function uniqueness identifies the concrete pushforward with its density. -/
theorem determinantLaw_eq_densityMeasure : determinantLaw = densityMeasure := by
  haveI : IsFiniteMeasure determinantLaw := by unfold determinantLaw rowMeasure; infer_instance
  apply Measure.ext_of_charFun
  funext t
  rw [determinantLaw_charFun, densityMeasure_charFun]

theorem target_density_hasLaw (h : Fin 2 × Fin 2 → CoefficientSpace)
    (hh : Orthonormal ℝ h) : HasLaw (quadraticTarget h T) densityMeasure gaussianProduct := by
  rw [← determinantLaw_eq_densityMeasure]
  exact target_hasLaw h hh

theorem actual_target_density_hasLaw :
    HasLaw (quadraticTarget directions T) densityMeasure gaussianProduct :=
  target_density_hasLaw directions directions_orthonormal

instance densityMeasure_probability : IsProbabilityMeasure densityMeasure := by
  rw [← determinantLaw_eq_densityMeasure]
  unfold determinantLaw rowMeasure
  infer_instance

instance densityMeasure_noAtoms : NullSingletonClass densityMeasure := by
  unfold densityMeasure
  infer_instance

theorem target_law_singleton (h : Fin 2 × Fin 2 → CoefficientSpace)
    (hh : Orthonormal ℝ h) (x : ℝ) :
    (gaussianProduct.map (quadraticTarget h T)) {x} = 0 := by
  rw [(target_density_hasLaw h hh).map_eq]
  exact measure_singleton x

end OperatorDerivativeRewrite.Foundation.GaussianDeterminantDensity
