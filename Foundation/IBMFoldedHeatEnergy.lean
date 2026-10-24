import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Function.L2Space

/-! Exact spatial energy of the candidate folded conditional IBM coefficient.
This analytic identity does not identify a stochastic predictable projection. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedHeatEnergy

def scale (v : ℝ≥0) : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹

def difference (b : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  gaussianPDFReal b v x - gaussianPDFReal (-b) v x

private theorem square_pdf (b : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal b v x ^ 2 =
      scale v ^ 2 * Real.exp (-(v : ℝ)⁻¹ * (x-b)^2) := by
  simp only [gaussianPDFReal, scale, mul_pow, ← Real.exp_nat_mul]
  congr 1
  congr 1
  ring

private theorem cross_pdf (b : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal b v x * gaussianPDFReal (-b) v x =
      scale v ^ 2 * Real.exp (-b^2/v) * Real.exp (-(v : ℝ)⁻¹*x^2) := by
  simp only [gaussianPDFReal, scale, sub_neg_eq_add]
  rw [mul_mul_mul_comm, ← Real.exp_add]
  rw [show -(x-b)^2/(2*(v : ℝ)) + -(x+b)^2/(2*(v : ℝ)) =
    -b^2/(v : ℝ) + -(v : ℝ)⁻¹*x^2 by ring, Real.exp_add]
  ring

private theorem gaussian_integrable {v : ℝ≥0} (hv : 0 < v) :
    Integrable (fun x : ℝ => Real.exp (-(v : ℝ)⁻¹*x^2)) :=
  integrable_exp_neg_mul_sq (inv_pos.mpr hv)

private theorem square_integrable (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    Integrable (fun x => gaussianPDFReal b v x ^ 2) := by
  simp_rw [square_pdf]
  exact ((gaussian_integrable hv).comp_sub_right b).const_mul _

private theorem cross_integrable (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    Integrable (fun x => gaussianPDFReal b v x * gaussianPDFReal (-b) v x) := by
  simp_rw [cross_pdf]
  exact (gaussian_integrable hv).const_mul _

private theorem square_integral (b : ℝ) {v : ℝ≥0} (_hv : 0 < v) :
    (∫ x, gaussianPDFReal b v x ^ 2) = scale v ^ 2 * Real.sqrt (Real.pi*v) := by
  simp_rw [square_pdf]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x : ℝ => Real.exp (-(v : ℝ)⁻¹*x^2)) b]
  rw [integral_gaussian]
  simp only [div_inv_eq_mul]

private theorem cross_integral (b : ℝ) {v : ℝ≥0} (_hv : 0 < v) :
    (∫ x, gaussianPDFReal b v x * gaussianPDFReal (-b) v x) =
      scale v ^ 2 * Real.exp (-b^2/v) * Real.sqrt (Real.pi*v) := by
  simp_rw [cross_pdf]
  rw [integral_const_mul, integral_gaussian]
  simp only [div_inv_eq_mul]

theorem difference_square_integrable (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    Integrable (fun x => difference b v x ^ 2) := by
  have he (x : ℝ) : difference b v x ^ 2 =
      gaussianPDFReal b v x ^ 2 + gaussianPDFReal (-b) v x ^ 2 -
        2 * (gaussianPDFReal b v x * gaussianPDFReal (-b) v x) := by
    unfold difference
    ring
  simp_rw [he]
  exact ((square_integrable b hv).add (square_integrable (-b) hv)).sub
    ((cross_integrable b hv).const_mul 2)

theorem difference_square_integral (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    (∫ x, difference b v x ^ 2) =
      2 * scale v ^ 2 * Real.sqrt (Real.pi*v) * (1-Real.exp (-b^2/v)) := by
  have he (x : ℝ) : difference b v x ^ 2 =
      gaussianPDFReal b v x ^ 2 + gaussianPDFReal (-b) v x ^ 2 -
        2 * (gaussianPDFReal b v x * gaussianPDFReal (-b) v x) := by
    unfold difference
    ring
  simp_rw [he]
  rw [integral_sub (f := fun x => gaussianPDFReal b v x ^ 2 + gaussianPDFReal (-b) v x ^ 2)
    ((square_integrable b hv).add (square_integrable (-b) hv))
    ((cross_integrable b hv).const_mul 2),
    integral_add (square_integrable b hv) (square_integrable (-b) hv),
    integral_const_mul, square_integral b hv, square_integral (-b) hv, cross_integral b hv]
  ring

theorem difference_neg (b : ℝ) (v : ℝ≥0) (x : ℝ) :
    difference b v (-x) = -difference b v x := by
  unfold difference gaussianPDFReal
  have h1 : (-x-b)^2 = (x-(-b))^2 := by ring
  have h2 : (-x-(-b))^2 = (x-b)^2 := by ring
  rw [h1,h2]
  ring

theorem folded_square_integral (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    (∫ x in Ioi (0 : ℝ), difference b v x ^ 2) =
      scale v ^ 2 * Real.sqrt (Real.pi*v) * (1-Real.exp (-b^2/v)) := by
  have he (x : ℝ) : difference b v |x| ^ 2 = difference b v x ^ 2 := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, difference_neg, neg_sq]
  have hi := integral_comp_abs (f := fun x => difference b v x ^ 2)
  simp_rw [he] at hi
  rw [difference_square_integral b hv] at hi
  linarith

theorem folded_square_bound (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    (∫ x in Ioi (0 : ℝ), difference b v x ^ 2) ≤
      scale v ^ 2 * Real.sqrt (Real.pi*v) := by
  rw [folded_square_integral b hv]
  have h : 0 ≤ scale v ^ 2 * Real.sqrt (Real.pi*v) := by positivity
  nlinarith [Real.exp_pos (-b^2/(v : ℝ))]

theorem scale_energy {v : ℝ≥0} (hv : 0 < v) :
    scale v ^ 2 * Real.sqrt (Real.pi*v) = (2 * Real.sqrt (Real.pi*v))⁻¹ := by
  have h1 : Real.sqrt (2*Real.pi*v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have h2 : Real.sqrt (Real.pi*v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  unfold scale
  field_simp
  nlinarith [Real.sq_sqrt (show 0 ≤ 2*Real.pi*(v : ℝ) by positivity),
    Real.sq_sqrt (show 0 ≤ Real.pi*(v : ℝ) by positivity)]

theorem folded_energy (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    (∫ x in Ioi (0 : ℝ), difference b v x ^ 2) =
      (1-Real.exp (-b^2/v))/(2 * Real.sqrt (Real.pi*v)) := by
  rw [folded_square_integral b hv, scale_energy hv]
  ring

def folded (b : ℝ) (v : ℝ≥0) : ℝ → ℝ := (Ioi 0).indicator (difference b v)

theorem folded_memLp (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    MemLp (folded b v) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (((stronglyMeasurable_gaussianPDFReal b v).sub
      (stronglyMeasurable_gaussianPDFReal (-b) v)).indicator
        measurableSet_Ioi).aestronglyMeasurable).mpr
  change Integrable (fun x => folded b v x ^ 2) volume
  have he (x : ℝ) : folded b v x ^ 2 = (Ioi (0 : ℝ)).indicator
      (fun y => difference b v y ^ 2) x := by
    by_cases h : x ∈ Ioi (0 : ℝ) <;> simp [folded, h]
  simp_rw [he]
  exact (difference_square_integrable b hv).indicator measurableSet_Ioi

def spatial (b : ℝ) (v : ℝ≥0) (hv : 0 < v) : Lp ℝ 2 (volume : Measure ℝ) :=
  (folded_memLp b hv).toLp (folded b v)

theorem spatial_coeFn (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    spatial b v hv =ᵐ[volume] folded b v := (folded_memLp b hv).coeFn_toLp

theorem spatial_energy (b : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    ‖spatial b v hv‖ ^ 2 =
      (1-Real.exp (-b^2/v))/(2 * Real.sqrt (Real.pi*v)) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ x, (Ioi (0 : ℝ)).indicator (fun y => difference b v y ^ 2) x := by
      apply integral_congr_ae
      filter_upwards [spatial_coeFn b hv] with x hx
      rw [hx, Real.inner_apply]
      by_cases h : x ∈ Ioi (0 : ℝ) <;> simp [folded,h,pow_two]
    _ = _ := by rw [integral_indicator measurableSet_Ioi, folded_energy b hv]

end OperatorDerivativeRewrite.Foundation.IBMFoldedHeatEnergy
