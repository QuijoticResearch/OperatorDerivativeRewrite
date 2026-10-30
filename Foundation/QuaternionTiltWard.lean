import Foundation.QuaternionAngularHaar
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Actual unit-quaternion Haar Ward identities and the tilted radial mean equation.
These are classical compact-group identities, proved here from the actual Haar law;
they are analytic input to a one-link covariance argument, not a lattice mass-gap bound. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Quaternion
namespace OperatorDerivativeRewrite.Foundation.QuaternionTiltWard
open QuaternionAngularHaar
set_option backward.isDefEq.respectTransparency false

def imaginary (a : Fin 3) (u : Group) : ℝ :=
  if a = 0 then (u : ℍ).imI else if a = 1 then (u : ℍ).imJ else (u : ℍ).imK

variable (a : Fin 3)

theorem imaginary_measurable : Measurable (imaginary a) := by
  fin_cases a
  · exact Quaternion.continuous_imI.measurable.comp measurable_subtype_coe
  · exact Quaternion.continuous_imJ.measurable.comp measurable_subtype_coe
  · exact Quaternion.continuous_imK.measurable.comp measurable_subtype_coe

theorem imaginary_bound (u : Group) : |imaginary a u| ≤ 1 := by
  have hn : Quaternion.normSq (u : ℍ) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, one_mul]
  rw [Quaternion.normSq_def'] at hn
  fin_cases a <;> norm_num [imaginary] <;> apply abs_le.mpr <;>
    constructor <;> nlinarith [sq_nonneg (u : ℍ).re, sq_nonneg (u : ℍ).imI,
      sq_nonneg (u : ℍ).imJ, sq_nonneg (u : ℍ).imK]

def rawRotation (s : ℝ) : ℍ :=
  if a = 0 then ⟨Real.cos s, Real.sin s, 0, 0⟩ else
    if a = 1 then ⟨Real.cos s, 0, Real.sin s, 0⟩ else ⟨Real.cos s, 0, 0, Real.sin s⟩

def rotation (s : ℝ) : Group := ⟨rawRotation a s, by
  rw [Unitary.mem_iff]
  have hn : Quaternion.normSq (rawRotation a s) = 1 := by
    fin_cases a <;> norm_num [rawRotation, Quaternion.normSq_def']
  constructor
  · rw [Quaternion.star_mul_self, hn]; rfl
  · rw [Quaternion.self_mul_star, hn]; rfl⟩

theorem rotated_real (s : ℝ) (u : Group) :
    realCoordinate (rotation a s * u) = Real.cos s * realCoordinate u - Real.sin s * imaginary a u := by
  fin_cases a <;> simp [rotation, rawRotation, realCoordinate, imaginary, sub_eq_add_neg]

theorem rotated_imaginary (s : ℝ) (u : Group) :
    imaginary a (rotation a s * u) = Real.sin s * realCoordinate u + Real.cos s * imaginary a u := by
  fin_cases a <;> simp [rotation, rawRotation, realCoordinate, imaginary, add_comm]

private theorem real_derivative (s : ℝ) (u : Group) :
    HasDerivAt (fun r => realCoordinate (rotation a r * u)) (-imaginary a (rotation a s * u)) s := by
  simp_rw [rotated_real]
  convert ((Real.hasDerivAt_cos s).mul_const (realCoordinate u)).sub
    ((Real.hasDerivAt_sin s).mul_const (imaginary a u)) using 1 <;>
    simp [rotated_imaginary] <;> ring

private theorem imaginary_derivative (s : ℝ) (u : Group) :
    HasDerivAt (fun r => imaginary a (rotation a r * u)) (realCoordinate (rotation a s * u)) s := by
  simp_rw [rotated_imaginary]
  convert ((Real.hasDerivAt_sin s).mul_const (realCoordinate u)).add
    ((Real.hasDerivAt_cos s).mul_const (imaginary a u)) using 1 <;>
    simp [rotated_real] <;> ring

/-- A Ward identity for the actual unit-quaternion Haar probability, at every finite tilt. -/
theorem weighted_ward (t : ℝ) :
    (∫ u, realCoordinate u * Real.exp (t * realCoordinate u) ∂law) =
      t * ∫ u, imaginary a u ^ 2 * Real.exp (t * realCoordinate u) ∂law := by
  let X := fun s u => realCoordinate (rotation a s * u)
  let Y := fun s u => imaginary a (rotation a s * u)
  let F := fun s u => Y s u * Real.exp (t * X s u)
  let F' := fun s u => (X s u - t * Y s u ^ 2) * Real.exp (t * X s u)
  have hx : ∀ s, Measurable (X s) := fun s =>
    realCoordinate_measurable.comp (measurable_const_mul (rotation a s))
  have hy : ∀ s, Measurable (Y s) := fun s =>
    (imaginary_measurable a).comp (measurable_const_mul (rotation a s))
  have hm : ∀ s, AEStronglyMeasurable (F s) law := fun s =>
    ((hy s).mul ((measurable_const.mul (hx s)).exp)).aestronglyMeasurable
  have hb : ∀ s u, ‖F s u‖ ≤ Real.exp |t| := by
    intro s u
    have he : Real.exp (t * X s u) ≤ Real.exp |t| := by
      apply Real.exp_le_exp.mpr
      calc
        t * X s u ≤ |t| * |X s u| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (realCoordinate_bound _) (abs_nonneg _)
        _ = |t| := mul_one _
    simpa [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      mul_le_mul (imaginary_bound a (rotation a s * u)) he (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 1)
  have hi : Integrable (F 0) law :=
    Integrable.mono' (integrable_const (Real.exp |t|)) (hm 0) (Eventually.of_forall (hb 0))
  have hdm : AEStronglyMeasurable (F' 0) law :=
    (((hx 0).sub (measurable_const.mul ((hy 0).pow_const 2))).mul
      ((measurable_const.mul (hx 0)).exp)).aestronglyMeasurable
  have hbd : ∀ᵐ u ∂law, ∀ s ∈ Ioo (-1:ℝ) 1,
      ‖F' s u‖ ≤ (1 + |t|) * Real.exp |t| := by
    filter_upwards with u s _
    have hx1 := realCoordinate_bound (rotation a s * u)
    have hy1 := imaginary_bound a (rotation a s * u)
    have hy2 : |Y s u ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have hh := abs_le.mp hy1
      dsimp [Y]; nlinarith
    have hp : |X s u - t * Y s u ^ 2| ≤ 1 + |t| := by
      calc
        _ ≤ |X s u| + |t * Y s u ^ 2| := abs_sub _ _
        _ = |X s u| + |t| * |Y s u ^ 2| := by rw [abs_mul]
        _ ≤ 1 + |t| * 1 := add_le_add hx1 (mul_le_mul_of_nonneg_left hy2 (abs_nonneg _))
        _ = _ := by ring
    have he : Real.exp (t * X s u) ≤ Real.exp |t| := by
      apply Real.exp_le_exp.mpr
      calc
        t * X s u ≤ |t * X s u| := le_abs_self _
        _ = |t| * |X s u| := abs_mul _ _
        _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
        _ = _ := mul_one _
    simpa [F', Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      mul_le_mul hp he (Real.exp_pos _).le (by positivity : 0 ≤ 1 + |t|)
  have hd : ∀ᵐ u ∂law, ∀ s ∈ Ioo (-1:ℝ) 1, HasDerivAt (F · u) (F' s u) s := by
    filter_upwards with u s _
    have h := (imaginary_derivative a s u).mul
      (((real_derivative a s u).const_mul t).exp)
    convert h using 1 <;> dsimp [F, F', X, Y] <;> ring
  obtain ⟨_, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1))
    (Eventually.of_forall hm) hi hdm hbd (integrable_const _) hd
  have hc : (fun s => ∫ u, F s u ∂law) =
      fun _ => ∫ u, imaginary a u * Real.exp (t * realCoordinate u) ∂law := by
    funext s
    exact integral_mul_left_eq_self (μ := law)
      (fun u => imaginary a u * Real.exp (t * realCoordinate u)) (rotation a s)
  rw [hc] at h
  have hz := h.unique (hasDerivAt_const 0 (∫ u, imaginary a u * Real.exp (t * realCoordinate u) ∂law))
  have hzero : rotation a 0 = 1 := by apply Subtype.ext; ext <;> fin_cases a <;> norm_num [rotation, rawRotation]
  have hxx : Integrable (fun u => realCoordinate u * Real.exp (t * realCoordinate u)) law := by
    apply Integrable.mono' (integrable_const (Real.exp |t|))
      (realCoordinate_measurable.mul ((measurable_const.mul realCoordinate_measurable).exp)).aestronglyMeasurable
    filter_upwards with u
    have he' : Real.exp (t * realCoordinate u) ≤ Real.exp |t| := by
      apply Real.exp_le_exp.mpr
      calc
        t * realCoordinate u ≤ |t * realCoordinate u| := le_abs_self _
        _ = |t| * |realCoordinate u| := abs_mul _ _
        _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (realCoordinate_bound _) (abs_nonneg _)
        _ = _ := mul_one _
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      mul_le_mul (realCoordinate_bound u) he' (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 1)
  have hyy : Integrable (fun u => imaginary a u ^ 2 * Real.exp (t * realCoordinate u)) law := by
    apply Integrable.mono' (BoundedExponentialTiltResponse.exponential_integrable law
      realCoordinate realCoordinate_measurable realCoordinate_bound t)
      (((imaginary_measurable a).pow_const 2).mul
        ((measurable_const.mul realCoordinate_measurable).exp)).aestronglyMeasurable
    filter_upwards with u
    have hq : |imaginary a u ^ 2| ≤ 1 := by
      have hh := abs_le.mp (imaginary_bound a u)
      rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      mul_le_mul_of_nonneg_right hq (Real.exp_pos (t * realCoordinate u)).le
  simp only [F', X, Y, hzero, one_mul] at hz
  simp_rw [sub_mul, mul_assoc] at hz
  rw [integral_sub hxx (hyy.const_mul t), integral_const_mul] at hz
  linarith

private theorem bounded_weight_integrable (f : Group → ℝ) (hf : Measurable f)
    (hb : ∀ u, |f u| ≤ 1) (t : ℝ) :
    Integrable (fun u => f u * Real.exp (t * realCoordinate u)) law := by
  apply Integrable.mono' (BoundedExponentialTiltResponse.exponential_integrable law
    realCoordinate realCoordinate_measurable realCoordinate_bound t)
    (hf.mul ((measurable_const.mul realCoordinate_measurable).exp)).aestronglyMeasurable
  filter_upwards with u
  simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
    mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos (t * realCoordinate u)).le

private theorem square_bound {x : ℝ} (h : |x| ≤ 1) : |x ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have hh := abs_le.mp h
  nlinarith

theorem sphere_identity (u : Group) :
    realCoordinate u ^ 2 + imaginary 0 u ^ 2 + imaginary 1 u ^ 2 + imaginary 2 u ^ 2 = 1 := by
  have hn : Quaternion.normSq (u : ℍ) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, one_mul]
  simpa [Quaternion.normSq_def', realCoordinate, imaginary] using hn

/-- The exact radial second-moment relation; no Bessel-function identification is assumed. -/
theorem weighted_radial_identity (t : ℝ) :
    3 * (∫ u, realCoordinate u * Real.exp (t * realCoordinate u) ∂law) =
      t * ((∫ u, Real.exp (t * realCoordinate u) ∂law) -
        ∫ u, realCoordinate u ^ 2 * Real.exp (t * realCoordinate u) ∂law) := by
  have hi : ∀ j : Fin 3, Integrable (fun u => imaginary j u ^ 2 * Real.exp (t * realCoordinate u)) law :=
    fun j => bounded_weight_integrable _ ((imaginary_measurable j).pow_const 2)
      (fun u => square_bound (imaginary_bound j u)) t
  have hr := bounded_weight_integrable _ (realCoordinate_measurable.pow_const 2)
    (fun u => square_bound (realCoordinate_bound u)) t
  have he := BoundedExponentialTiltResponse.exponential_integrable law realCoordinate
    realCoordinate_measurable realCoordinate_bound t
  have hp : (fun u => imaginary 0 u ^ 2 * Real.exp (t * realCoordinate u) +
      imaginary 1 u ^ 2 * Real.exp (t * realCoordinate u) +
      imaginary 2 u ^ 2 * Real.exp (t * realCoordinate u)) =
      (fun u => Real.exp (t * realCoordinate u) - realCoordinate u ^ 2 * Real.exp (t * realCoordinate u)) := by
    funext u
    have hs := sphere_identity u
    calc
      _ = (imaginary 0 u ^ 2 + imaginary 1 u ^ 2 + imaginary 2 u ^ 2) *
          Real.exp (t * realCoordinate u) := by ring
      _ = (1 - realCoordinate u ^ 2) * Real.exp (t * realCoordinate u) := by
        congr 1; linarith
      _ = _ := by ring
  have hint := congrArg (fun f : Group → ℝ => ∫ u, f u ∂law) hp
  have h01 : Integrable (fun u => imaginary 0 u ^ 2 * Real.exp (t * realCoordinate u) + imaginary 1 u ^ 2 * Real.exp (t * realCoordinate u)) law := (hi 0).add (hi 1)
  rw [integral_add h01 (hi 2), integral_add (hi 0) (hi 1), integral_sub he hr] at hint
  linear_combination (weighted_ward 0 t) + (weighted_ward 1 t) + (weighted_ward 2 t) + t * hint

open BoundedExponentialTiltResponse

theorem expectation_ward (t : ℝ) :
    expectation law realCoordinate realCoordinate t =
      t * expectation law realCoordinate (fun u => imaginary a u ^ 2) t := by
  unfold expectation weighted
  rw [weighted_ward a t]
  ring

theorem radial_identity (t : ℝ) :
    3 * expectation law realCoordinate realCoordinate t =
      t * (1 - expectation law realCoordinate (fun u => realCoordinate u ^ 2) t) := by
  have hz := (partition_pos law realCoordinate realCoordinate_measurable realCoordinate_bound t).ne'
  have h := weighted_radial_identity t
  simp only [expectation, weighted, partition, one_mul] at hz ⊢
  field_simp
  simpa only [mul_comm t] using h

theorem radial_variance_identity (t : ℝ) :
    t * variance law realCoordinate realCoordinate t =
      t * (1 - expectation law realCoordinate realCoordinate t ^ 2) -
        3 * expectation law realCoordinate realCoordinate t := by
  have h := radial_identity t
  unfold variance
  nlinarith

/-- Differentiation of an actual tilted Haar integral at an arbitrary finite parameter. -/
theorem weighted_hasDerivAt (f : Group → ℝ) (hf : Measurable f)
    (hb : ∀ u, |f u| ≤ 1) (t : ℝ) :
    HasDerivAt (weighted law realCoordinate f)
      (∫ u, f u * realCoordinate u * Real.exp (t * realCoordinate u) ∂law) t := by
  let F := fun s u => f u * Real.exp (s * realCoordinate u)
  let F' := fun s u => f u * realCoordinate u * Real.exp (s * realCoordinate u)
  have hm : ∀ s, AEStronglyMeasurable (F s) law := fun s =>
    (hf.mul ((measurable_const.mul realCoordinate_measurable).exp)).aestronglyMeasurable
  have hi : Integrable (F t) law := bounded_weight_integrable f hf hb t
  have hdm : AEStronglyMeasurable (F' t) law :=
    ((hf.mul realCoordinate_measurable).mul
      ((measurable_const.mul realCoordinate_measurable).exp)).aestronglyMeasurable
  have hbd : ∀ᵐ u ∂law, ∀ s ∈ Ioo (t-1) (t+1), ‖F' s u‖ ≤ Real.exp (|t|+1) := by
    filter_upwards with u s hs
    have hst : |s| ≤ |t|+1 := by
      exact abs_le.mpr ⟨by linarith [hs.1, neg_abs_le t], by linarith [hs.2, le_abs_self t]⟩
    have he : Real.exp (s * realCoordinate u) ≤ Real.exp (|t|+1) := by
      apply Real.exp_le_exp.mpr
      calc
        s * realCoordinate u ≤ |s * realCoordinate u| := le_abs_self _
        _ = |s| * |realCoordinate u| := abs_mul _ _
        _ ≤ (|t|+1) * 1 := mul_le_mul hst (realCoordinate_bound u) (abs_nonneg _) (by positivity)
        _ = _ := mul_one _
    have hp : |f u| * |realCoordinate u| ≤ 1 := by
      simpa using mul_le_mul (hb u) (realCoordinate_bound u) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simpa [F', Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      mul_le_mul hp he (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 1)
  have hd : ∀ᵐ u ∂law, ∀ s ∈ Ioo (t-1) (t+1), HasDerivAt (F · u) (F' s u) s := by
    filter_upwards with u s _
    have h := (((hasDerivAt_id s).mul_const (realCoordinate u)).exp).const_mul (f u)
    convert h using 1 <;> dsimp [F, F'] <;> ring
  obtain ⟨_, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : t-1 < t) (by linarith : t < t+1))
    (Eventually.of_forall hm) hi hdm hbd (integrable_const _) hd
  exact h

theorem mean_hasDerivAt (t : ℝ) :
    HasDerivAt (expectation law realCoordinate realCoordinate)
      (variance law realCoordinate realCoordinate t) t := by
  have hn := weighted_hasDerivAt realCoordinate realCoordinate_measurable realCoordinate_bound t
  have hd := weighted_hasDerivAt (fun _ => 1) measurable_const (fun _ => by norm_num) t
  have hz := (partition_pos law realCoordinate realCoordinate_measurable realCoordinate_bound t).ne'
  have hd' : HasDerivAt (partition law realCoordinate)
      (weighted law realCoordinate realCoordinate t) t := by
    change HasDerivAt (weighted law realCoordinate (fun _ => 1)) _ t
    simpa only [weighted, one_mul] using hd
  have hn' : HasDerivAt (weighted law realCoordinate realCoordinate)
      (weighted law realCoordinate (fun u => realCoordinate u ^ 2) t) t := by
    simpa only [weighted, pow_two] using hn
  convert hn'.div hd' hz using 1
  · rfl
  · unfold variance expectation
    field_simp

/-- Exact Riccati equation, derived from Haar invariance and actual integral differentiation. -/
theorem mean_riccati (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (expectation law realCoordinate realCoordinate)
      (1 - expectation law realCoordinate realCoordinate t ^ 2 -
        3 * expectation law realCoordinate realCoordinate t / t) t := by
  have h := radial_variance_identity t
  have he : variance law realCoordinate realCoordinate t =
      1 - expectation law realCoordinate realCoordinate t ^ 2 -
        3 * expectation law realCoordinate realCoordinate t / t := by
    apply (mul_left_cancel₀ ht)
    field_simp
    nlinarith
  rw [← he]
  exact mean_hasDerivAt t

theorem mean_zero : expectation law realCoordinate realCoordinate 0 = 0 := by
  simpa using expectation_ward 0 0

theorem second_moment_zero :
    expectation law realCoordinate (fun u => realCoordinate u ^ 2) 0 = 1/4 := by
  rw [expectation_realCoordinate law (fun x : ℝ => x ^ 2) (by fun_prop) 0,
    expectation_zero]
  exact (GaussianAngularSphere.angular_coord_power 0 2).trans
    (GaussianAngularSphere.coord_second_moment 0)

theorem mean_hasDerivAt_zero :
    HasDerivAt (expectation law realCoordinate realCoordinate) (1/4) 0 := by
  have h := mean_hasDerivAt 0
  simpa only [variance, mean_zero, second_moment_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero] using h

end OperatorDerivativeRewrite.Foundation.QuaternionTiltWard
