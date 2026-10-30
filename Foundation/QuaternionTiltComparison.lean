import Foundation.QuaternionTiltWard
import Foundation.QuaternionSU2Representation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Direct comparison bounds for the actual tilted Haar mean and radial variance.
The strict barriers include the genuine zero-tilt derivative. The conclusions concern
normalized quaternion/SU2 Haar integrals, not a presumed lattice conditional law. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.QuaternionTiltComparison
open QuaternionAngularHaar QuaternionTiltWard BoundedExponentialTiltResponse
set_option backward.isDefEq.respectTransparency false

def mean (t : ℝ) : ℝ := expectation law realCoordinate realCoordinate t
def radialVariance (t : ℝ) : ℝ := variance law realCoordinate realCoordinate t
def root (t : ℝ) : ℝ := Real.sqrt (t^2 + 15/4)
def denominator (t : ℝ) : ℝ := 3/2 + root t
def upper (t : ℝ) : ℝ := t / denominator t
def upperSlope (t : ℝ) : ℝ := (3/2 + (15/4) / root t) / denominator t ^ 2
def lower (t : ℝ) : ℝ := t / (5 * (1+t))

theorem root_pos (t : ℝ) : 0 < root t := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg t]

theorem root_square (t : ℝ) : root t ^ 2 = t^2 + 15/4 := by
  apply Real.sq_sqrt
  nlinarith [sq_nonneg t]

theorem denominator_pos (t : ℝ) : 0 < denominator t := by
  unfold denominator
  linarith [root_pos t]

theorem upper_hasDerivAt (t : ℝ) : HasDerivAt upper (upperSlope t) t := by
  have hs := (((hasDerivAt_id t).pow 2).add_const (15/4)).sqrt
    (by nlinarith [sq_nonneg t] : t^2 + 15/4 ≠ 0)
  have hs' : HasDerivAt root (t / root t) t := by
    convert hs using 1
    · rfl
    · simp [root]; ring
  have hd := (hasDerivAt_id t).div (hs'.const_add (3/2)) (denominator_pos t).ne'
  convert hd using 1
  · rfl
  · simp only [one_mul, id_eq]
    change (3/2 + (15/4) / root t) / denominator t ^ 2 =
      (denominator t - t * (t / root t)) / denominator t ^ 2
    apply congrArg (fun z : ℝ => z / denominator t ^ 2)
    dsimp [denominator]
    field_simp [(root_pos t).ne']
    nlinarith [root_square t]

theorem lower_hasDerivAt (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt lower (1 / (5 * (1+t)^2)) t := by
  have hn : 5 * (1+t) ≠ 0 := by positivity
  convert (hasDerivAt_id t).div (((hasDerivAt_id t).const_add 1).const_mul 5) hn using 1
  · rfl
  · simp only [id_eq]
    field_simp
    <;> ring

private theorem variance_zero : radialVariance 0 = 1/4 := by
  simp only [radialVariance, variance, mean_zero, second_moment_zero]
  norm_num

private theorem upper_contact (t : ℝ) (ht : 0 < t) (hm : mean t = upper t) :
    radialVariance t = (3/2) / denominator t ^ 2 := by
  have h := radial_variance_identity t
  change t * radialVariance t = t * (1-mean t ^ 2) - 3 * mean t at h
  rw [hm] at h
  have hs := root_square t
  have hp := (denominator_pos t).ne'
  unfold upper at h
  field_simp [hp] at h ⊢
  dsimp [denominator] at h ⊢
  nlinarith

private theorem upper_contact_strict (t : ℝ) (ht : 0 ≤ t) (hm : mean t = upper t) :
    radialVariance t < upperSlope t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [variance_zero]
    have hs := root_pos 0
    have hsq := root_square 0
    have hd := denominator_pos 0
    have hslt : root 0 < 5/2 := by nlinarith
    unfold upperSlope
    apply (lt_div_iff₀ (sq_pos_of_pos hd)).mpr
    have hdiv : 0 < (15/4:ℝ) / root 0 := by positivity
    have hid : 3/2 + (15/4:ℝ) / root 0 = denominator 0 := by
      dsimp [denominator]
      field_simp
      nlinarith
    rw [hid]
    dsimp [denominator]
    nlinarith
  · rw [upper_contact t ht hm]
    unfold upperSlope
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos (denominator_pos t))).mpr
    have hp : 0 < (15/4:ℝ) / root t := div_pos (by norm_num) (root_pos t)
    linarith

theorem mean_le_upper (t : ℝ) (ht : 0 ≤ t) : mean t ≤ upper t := by
  have h := image_le_of_deriv_right_lt_deriv_boundary
    (f := mean) (f' := radialVariance) (a := 0) (b := t)
    (B := upper) (B' := upperSlope)
    (fun s _ => (mean_hasDerivAt s).continuousAt.continuousWithinAt)
    (fun s _ => (mean_hasDerivAt s).hasDerivWithinAt)
    (by simp [mean, upper, mean_zero]) upper_hasDerivAt
    (fun s hs he => upper_contact_strict s hs.1 he)
  exact h ⟨ht, le_rfl⟩

private theorem lower_contact_strict (t : ℝ) (ht : 0 ≤ t) (hm : mean t = lower t) :
    1 / (5 * (1+t)^2) < radialVariance t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t; rw [variance_zero]; norm_num
  · have h := radial_variance_identity t
    change t * radialVariance t = t * (1-mean t ^ 2) - 3 * mean t at h
    rw [hm] at h
    unfold lower at h
    have hp : 0 < 5 * (1+t) := by positivity
    field_simp [hp.ne'] at h
    apply (div_lt_iff₀ (by positivity : 0 < 5 * (1+t)^2)).mpr
    nlinarith [sq_nonneg t]

theorem lower_le_mean (t : ℝ) (ht : 0 ≤ t) : lower t ≤ mean t := by
  have h := image_le_of_deriv_right_lt_deriv_boundary'
    (f := fun s => -mean s) (f' := fun s => -radialVariance s) (a := 0) (b := t)
    (B := fun s => -lower s) (B' := fun s => -(1 / (5 * (1+s)^2)))
    (fun s _ => (mean_hasDerivAt s).neg.continuousAt.continuousWithinAt)
    (fun s _ => (mean_hasDerivAt s).neg.hasDerivWithinAt)
    (by simp [mean, lower, mean_zero])
    (fun s hs => (lower_hasDerivAt s hs.1).neg.continuousAt.continuousWithinAt)
    (fun s hs => (lower_hasDerivAt s hs.1).neg.hasDerivWithinAt)
    (fun s hs he => neg_lt_neg (lower_contact_strict s hs.1 (neg_injective he)))
  have hh := h ⟨ht, le_rfl⟩
  linarith

theorem mean_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ mean t := by
  have h := lower_le_mean t ht
  have hp : 0 ≤ lower t := div_nonneg ht (by positivity)
  linarith

private theorem upper_residual (t : ℝ) :
    t * (1 - upper t ^ 2) - 3 * upper t = t * ((3/2) / denominator t ^ 2) := by
  have hp := (denominator_pos t).ne'
  unfold upper
  field_simp [hp]
  dsimp [denominator]
  linear_combination 2 * t * (root_square t)

/-- A global quantitative lower bound for the radial variance of the actual Haar tilt. -/
theorem radial_variance_lower (t : ℝ) (ht : 0 ≤ t) :
    (3/2) / denominator t ^ 2 ≤ radialVariance t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [variance_zero]
    apply (div_le_iff₀ (sq_pos_of_pos (denominator_pos 0))).mpr
    dsimp [denominator]
    nlinarith [root_square 0, root_pos 0]
  · have hm := mean_le_upper t ht.le
    have hn := mean_nonneg t ht.le
    have hu : 0 ≤ upper t := div_nonneg ht.le (denominator_pos t).le
    have hsq : mean t ^ 2 ≤ upper t ^ 2 := by nlinarith
    have hv := radial_variance_identity t
    change t * radialVariance t = t * (1-mean t ^ 2) - 3 * mean t at hv
    apply (mul_le_mul_iff_right₀ ht).mp
    calc
      _ = t * (1-upper t ^ 2) - 3 * upper t := (upper_residual t).symm
      _ ≤ t * (1-mean t ^ 2) - 3 * mean t := by nlinarith
      _ = _ := hv.symm

theorem denominator_upper (t : ℝ) (ht : 0 ≤ t) : denominator t ≤ (7/2) * (1+t) := by
  have hs : root t ≤ t+2 := by
    nlinarith [root_square t, root_pos t]
  unfold denominator
  linarith

theorem radial_variance_polynomial_lower (t : ℝ) (ht : 0 ≤ t) :
    6 / (49 * (1+t)^2) ≤ radialVariance t := by
  have hp := denominator_pos t
  have hd := denominator_upper t ht
  have hsq : denominator t ^ 2 ≤ ((7/2) * (1+t))^2 := by nlinarith
  apply le_trans _ (radial_variance_lower t ht)
  apply (div_le_div_iff₀ (by positivity : 0 < 49 * (1+t)^2) (sq_pos_of_pos hp)).mpr
  nlinarith

theorem radial_variance_pos (t : ℝ) (ht : 0 ≤ t) : 0 < radialVariance t :=
  lt_of_lt_of_le (by positivity) (radial_variance_polynomial_lower t ht)

/-- Exact transport to every normalized Haar law on the actual SU(2) group. -/
theorem su2_radial_variance_lower
    (ν : Measure QuaternionSU2Representation.SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (t : ℝ) (ht : 0 ≤ t) :
    6 / (49 * (1+t)^2) ≤ variance ν QuaternionSU2Representation.halfTrace
      QuaternionSU2Representation.halfTrace t := by
  have h1 : expectation ν QuaternionSU2Representation.halfTrace
      QuaternionSU2Representation.halfTrace t = expectation law realCoordinate realCoordinate t := by
    simpa only [id_eq] using QuaternionSU2Representation.expectation_halfTrace ν id measurable_id t
  have h2 := QuaternionSU2Representation.expectation_halfTrace ν (fun x : ℝ => x^2)
    (by fun_prop) t
  have h := radial_variance_polynomial_lower t ht
  unfold radialVariance at h
  unfold variance at h ⊢
  rw [h1, h2]
  exact h

end OperatorDerivativeRewrite.Foundation.QuaternionTiltComparison
