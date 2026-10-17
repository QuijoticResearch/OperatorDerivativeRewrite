import Foundation.IBMOneTimeFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Boundary integration identity for the actual Gaussian-clock Laplace transform. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMGaussianLaplaceBoundary
open IBMOneTimeFourier

def tilt (b x : ℝ) : ℝ := Real.exp (-x^2/2-b*x)

theorem tilt_continuous (b : ℝ) : Continuous (tilt b) := by unfold tilt; fun_prop

theorem tilt_derivative (b x : ℝ) : HasDerivAt (tilt b) (-(x+b)*tilt b x) x := by
  unfold tilt
  convert (((((hasDerivAt_id x).pow 2).neg.div_const 2).sub
    ((hasDerivAt_id x).const_mul b)).exp) using 1 <;> simp <;> ring

theorem tilt_atTop (b : ℝ) : Tendsto (tilt b) atTop (𝓝 0) := by
  apply (Asymptotics.isLittleO_one_iff ℝ).mp
  have h := rexp_neg_quadratic_isLittleO_rpow_atTop (by norm_num : (-1/2 : ℝ) < 0) (-b) 0
  have he : (fun x : ℝ => Real.exp ((-1/2)*x^2+(-b)*x))=tilt b := by
    funext x
    unfold tilt
    congr 1
    ring
  simpa only [he,Real.rpow_zero] using h

theorem tilt_integrable (b : ℝ) (hb : 0 ≤ b) : IntegrableOn (tilt b) (Ioi 0) := by
  have hi := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).integrableOn (s := Ioi 0)
  apply hi.mono' (tilt_continuous b).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖Real.exp (-x^2/2-b*x)‖ ≤ Real.exp (-(1/2)*x^2)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hb hx.le]

theorem tilt_derivative_nonpos (b : ℝ) (hb : 0 ≤ b) (x : ℝ) (hx : x ∈ Ioi 0) :
    -(x+b)*tilt b x ≤ 0 := by
  change 0 < x at hx
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_nonneg _)

theorem moment_integrable (b : ℝ) (hb : 0 ≤ b) :
    IntegrableOn (fun x : ℝ => x*tilt b x) (Ioi 0) := by
  have hd := integrableOn_Ioi_deriv_of_nonpos' (fun x _ => tilt_derivative b x)
    (fun x hx => tilt_derivative_nonpos b hb x hx) (tilt_atTop b)
  have hi := hd.neg.sub ((tilt_integrable b hb).const_mul b)
  convert hi using 1
  funext x
  simp only [Pi.sub_apply,Pi.neg_apply]
  ring

theorem halfline_boundary (b : ℝ) (hb : 0 ≤ b) :
    (∫ x in Ioi (0 : ℝ), x*tilt b x) = 1-b*(∫ x in Ioi (0 : ℝ), tilt b x) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos' (fun x _ => tilt_derivative b x)
    (fun x hx => tilt_derivative_nonpos b hb x hx) (tilt_atTop b)
  have h0 : tilt b 0=1 := by simp [tilt]
  rw [h0,zero_sub] at h
  have he : (fun x : ℝ => -(x+b)*tilt b x) =
      fun x => -(x*tilt b x+b*tilt b x) := by funext x; ring
  rw [he,integral_neg,integral_add (moment_integrable b hb)
    ((tilt_integrable b hb).const_mul b),integral_const_mul] at h
  linarith

def gaussianConstant : ℝ := (Real.sqrt (2*Real.pi))⁻¹

theorem folded_density (f : ℝ → ℝ) :
    (∫ r : ℝ, f |r| ∂gaussianReal 0 1) =
      2*gaussianConstant*(∫ r in Ioi (0 : ℝ), Real.exp (-r^2/2)*f r) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,smul_eq_mul]
  have he : (fun r : ℝ => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-r^2/(2*1))*f |r|) =
      fun r => gaussianConstant*(Real.exp (-|r|^2/2)*f |r|) := by
    funext r
    simp only [gaussianConstant,mul_one,sq_abs]
    ring
  simp only [mul_one] at he
  rw [he,integral_const_mul,integral_comp_abs (f := fun r : ℝ => Real.exp (-r^2/2)*f r)]
  ring

theorem transform_halfline (b : ℝ) :
    clockTransform 1 b = 2*gaussianConstant*(∫ x in Ioi (0 : ℝ), tilt b x) := by
  rw [clockTransform,folded_density (fun x : ℝ => Real.exp (-b*x))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [tilt,sub_eq_add_neg,Real.exp_add,neg_mul]

theorem gaussian_boundary_identity (b : ℝ) (hb : 0 ≤ b) :
    (∫ r : ℝ, |r| * Real.exp (-b*|r|) ∂gaussianReal 0 1) =
      2*gaussianConstant-b*clockTransform 1 b := by
  rw [folded_density (fun x : ℝ => x*Real.exp (-b*x)),transform_halfline]
  have he : (∫ x in Ioi (0 : ℝ), Real.exp (-x^2/2)*(x*Real.exp (-b*x))) =
      ∫ x in Ioi (0 : ℝ), x*tilt b x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [tilt,sub_eq_add_neg,Real.exp_add,neg_mul]
    ring
  rw [he,halfline_boundary b hb]
  ring

end OperatorDerivativeRewrite.Foundation.IBMGaussianLaplaceBoundary
