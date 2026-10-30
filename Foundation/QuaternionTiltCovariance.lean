import Foundation.QuaternionTiltComparison
import Foundation.SU2StapleTiltLaw

/-! Actual tilted Haar covariance coercivity and its finite Wilson staple-law transport.
All symmetries are proved for the actual Haar measure; no lattice conditional law
or physical mass-gap assertion is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.QuaternionTiltCovariance
open QuaternionAngularHaar QuaternionTiltWard BoundedExponentialTiltResponse
set_option backward.isDefEq.respectTransparency false

private instance law_rightInvariant : law.IsMulRightInvariant := ⟨fun g => by
  letI : IsProbabilityMeasure (law.map (fun u => u*g)) := by infer_instance
  exact (law_eq_probability_haar (law.map (fun u => u*g))).symm⟩

def axis (a : Fin 3) : Group := QuaternionTiltWard.rotation a (Real.pi / 2)
def conjugate (a : Fin 3) (u : Group) : Group := axis a * u * star (axis a)

theorem conjugate_real (a : Fin 3) (u : Group) :
    realCoordinate (conjugate a u) = realCoordinate u := by
  change (((rawRotation a (Real.pi/2)) * (u:ℍ)) * star (rawRotation a (Real.pi/2))).re = (u:ℍ).re
  fin_cases a <;> norm_num [rawRotation, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

theorem conjugate_imaginary (a b : Fin 3) (u : Group) :
    imaginary b (conjugate a u) = if a = b then imaginary b u else -imaginary b u := by
  fin_cases a <;> fin_cases b <;>
    norm_num [imaginary, conjugate, axis, QuaternionTiltWard.rotation, rawRotation,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

theorem integral_conjugate (a : Fin 3) (f : Group → ℝ) :
    (∫ u, f (conjugate a u) ∂law) = ∫ u, f u ∂law := by
  change (∫ u, f (axis a * u * star (axis a)) ∂law) = _
  rw [integral_mul_left_eq_self (μ := law) (fun u => f (u * star (axis a))) (axis a),
    integral_mul_right_eq_self]

theorem weighted_odd_zero (a : Fin 3) (f : Group → ℝ)
    (hodd : ∀ u, f (conjugate a u) = -f u) (t : ℝ) :
    weighted law realCoordinate f t = 0 := by
  have h := integral_conjugate a (fun u => f u * Real.exp (t * realCoordinate u))
  have he : (fun u => f (conjugate a u) * Real.exp (t * realCoordinate (conjugate a u))) =
      fun u => -(f u * Real.exp (t * realCoordinate u)) := by
    funext u; rw [hodd, conjugate_real]; ring
  rw [he, integral_neg] at h
  unfold weighted
  linarith

private def other (a : Fin 3) : Fin 3 := if a = 0 then 1 else 0
private theorem other_ne (a : Fin 3) : other a ≠ a := by fin_cases a <;> decide

theorem imaginary_mean_zero (a : Fin 3) (t : ℝ) :
    expectation law realCoordinate (imaginary a) t = 0 := by
  unfold expectation
  rw [weighted_odd_zero (other a) (imaginary a)
    (fun u => by rw [conjugate_imaginary, if_neg (other_ne a)])]
  simp

theorem radial_imaginary_moment_zero (a : Fin 3) (t : ℝ) :
    expectation law realCoordinate (fun u => realCoordinate u * imaginary a u) t = 0 := by
  unfold expectation
  rw [weighted_odd_zero (other a) (fun u => realCoordinate u * imaginary a u)
    (fun u => by rw [conjugate_real, conjugate_imaginary, if_neg (other_ne a)]; ring)]
  simp

theorem imaginary_cross_moment_zero (a b : Fin 3) (hab : a ≠ b) (t : ℝ) :
    expectation law realCoordinate (fun u => imaginary a u * imaginary b u) t = 0 := by
  unfold expectation
  rw [weighted_odd_zero a (fun u => imaginary a u * imaginary b u)
    (fun u => by rw [conjugate_imaginary, if_pos rfl, conjugate_imaginary, if_neg hab]; ring)]
  simp

theorem imaginary_second_zero (a : Fin 3) :
    expectation law realCoordinate (fun u => imaginary a u ^ 2) 0 = 1/4 := by
  have h := integral_mul_left_eq_self (μ := law) (fun u => realCoordinate u ^ 2)
    (QuaternionTiltWard.rotation a (Real.pi/2))
  simp only [rotated_real, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul,
    zero_sub, neg_sq] at h
  rw [expectation_zero, h]
  simpa only [expectation_zero] using second_moment_zero

def coordinate (i : Fin 4) : Group → ℝ :=
  if i=0 then realCoordinate else if i=1 then imaginary 0 else if i=2 then imaginary 1 else imaginary 2

theorem coordinate_measurable (i : Fin 4) : Measurable (coordinate i) := by
  fin_cases i
  · exact realCoordinate_measurable
  · exact imaginary_measurable 0
  · exact imaginary_measurable 1
  · exact imaginary_measurable 2

theorem coordinate_bound (i : Fin 4) (u : Group) : |coordinate i u| ≤ 1 := by
  fin_cases i
  · exact realCoordinate_bound u
  · exact imaginary_bound 0 u
  · exact imaginary_bound 1 u
  · exact imaginary_bound 2 u

theorem coordinate_mean_zero (i : Fin 4) (hi : i ≠ 0) (t : ℝ) :
    expectation law realCoordinate (coordinate i) t = 0 := by
  fin_cases i <;> simp_all [coordinate, imaginary_mean_zero]

theorem coordinate_cross_zero (i j : Fin 4) (hij : i ≠ j) (t : ℝ) :
    expectation law realCoordinate (fun u => coordinate i u * coordinate j u) t = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [coordinate, mul_comm, radial_imaginary_moment_zero, imaginary_cross_moment_zero]

def tilt (t : ℝ) : Measure Group := tiltedMeasure law realCoordinate t

instance tilt_probability (t : ℝ) : IsProbabilityMeasure (tilt t) :=
  tiltedMeasure_probability law realCoordinate realCoordinate_measurable realCoordinate_bound t

theorem coordinate_memLp (t : ℝ) (i : Fin 4) : MemLp (coordinate i) 2 (tilt t) := by
  apply MemLp.of_bound (coordinate_measurable i).aestronglyMeasurable 1
  filter_upwards with u
  simpa only [Real.norm_eq_abs] using coordinate_bound i u

theorem tilt_integral (t : ℝ) (f : Group → ℝ) :
    (∫ u, f u ∂tilt t) = expectation law realCoordinate f t :=
  tilted_integral law realCoordinate f realCoordinate_measurable realCoordinate_bound t

theorem covariance_off_diagonal (t : ℝ) (i j : Fin 4) (hij : i ≠ j) :
    ProbabilityTheory.covariance (coordinate i) (coordinate j) (tilt t) = 0 := by
  rw [ProbabilityTheory.covariance_eq_sub (coordinate_memLp t i) (coordinate_memLp t j)]
  simp_rw [tilt_integral]
  change expectation law realCoordinate (fun u => coordinate i u * coordinate j u) t -
    expectation law realCoordinate (coordinate i) t * expectation law realCoordinate (coordinate j) t = 0
  rw [coordinate_cross_zero i j hij t]
  by_cases hi : i = 0
  · have hj : j ≠ 0 := by intro h; exact hij (hi.trans h.symm)
    rw [coordinate_mean_zero j hj t]; ring
  · rw [coordinate_mean_zero i hi t]; ring

theorem coordinate_variance (t : ℝ) (i : Fin 4) :
    ProbabilityTheory.variance (coordinate i) (tilt t) =
      variance law realCoordinate (coordinate i) t := by
  rw [ProbabilityTheory.variance_eq_sub (coordinate_memLp t i)]
  simp_rw [tilt_integral]
  rfl

theorem imaginary_second_lower (a : Fin 3) (t : ℝ) (ht : 0 ≤ t) :
    6/(49*(1+t)^2) ≤ expectation law realCoordinate (fun u => imaginary a u ^ 2) t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t; rw [imaginary_second_zero]; norm_num
  · have hw := expectation_ward a t
    have hm := QuaternionTiltComparison.lower_le_mean t ht.le
    change t/(5*(1+t)) ≤ expectation law realCoordinate realCoordinate t at hm
    have hlow : t*(6/(49*(1+t)^2)) ≤ t/(5*(1+t)) := by
      apply (le_div_iff₀ (by positivity : 0 < 5*(1+t))).mpr
      field_simp
      nlinarith
    have h := hlow.trans (hm.trans hw.le)
    exact (mul_le_mul_iff_right₀ ht).mp h

theorem coordinate_variance_lower (t : ℝ) (ht : 0 ≤ t) (i : Fin 4) :
    6/(49*(1+t)^2) ≤ ProbabilityTheory.variance (coordinate i) (tilt t) := by
  rw [coordinate_variance]
  have hi (j : Fin 3) : 6/(49*(1+t)^2) ≤ variance law realCoordinate (imaginary j) t := by
    simp only [variance, imaginary_mean_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero]
    exact imaginary_second_lower j t ht
  fin_cases i
  · exact QuaternionTiltComparison.radial_variance_polynomial_lower t ht
  · exact hi 0
  · exact hi 1
  · exact hi 2

def linearProbe (c : Fin 4 → ℝ) (u : Group) : ℝ := ∑ i, c i * coordinate i u

theorem linear_variance (c : Fin 4 → ℝ) (t : ℝ) :
    ProbabilityTheory.variance (linearProbe c) (tilt t) =
      ∑ i, c i ^ 2 * ProbabilityTheory.variance (coordinate i) (tilt t) := by
  unfold linearProbe
  rw [ProbabilityTheory.variance_fun_sum (fun i => (coordinate_memLp t i).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [ProbabilityTheory.covariance_const_mul_left, ProbabilityTheory.covariance_const_mul_right]
  have h : (∑ j, c i * (c j * ProbabilityTheory.covariance (coordinate i) (coordinate j) (tilt t))) =
      c i * (c i * ProbabilityTheory.variance (coordinate i) (tilt t)) := by
    rw [Finset.sum_eq_single i]
    · rw [ProbabilityTheory.covariance_self (coordinate_memLp t i).aemeasurable]
    · intro j _ hji
      rw [covariance_off_diagonal t i j (Ne.symm hji)]; ring
    · simp
  rw [h]; ring

theorem linear_variance_lower (c : Fin 4 → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (6/(49*(1+t)^2)) * (∑ i, c i ^ 2) ≤
      ProbabilityTheory.variance (linearProbe c) (tilt t) := by
  rw [linear_variance, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [coordinate_variance_lower t ht i, sq_nonneg (c i)]

def coefficients (c : Group) : Fin 4 → ℝ :=
  ![(c:ℍ).re, -(c:ℍ).imI, -(c:ℍ).imJ, -(c:ℍ).imK]

theorem coefficients_square_sum (c : Group) : (∑ i, coefficients c i ^ 2) = 1 := by
  have hn : Quaternion.normSq (c:ℍ) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, one_mul]
  simpa [coefficients, Fin.sum_univ_four, Quaternion.normSq_def'] using hn

theorem linearProbe_coefficients (c u : Group) :
    linearProbe (coefficients c) u = realCoordinate (c*u) := by
  simp [linearProbe, coefficients, coordinate, imaginary, realCoordinate, Fin.sum_univ_four,
    Quaternion.re_mul]
  ring

theorem directional_memLp (c : Group) (t : ℝ) :
    MemLp (fun u => realCoordinate (c*u)) 2 (tilt t) := by
  apply MemLp.of_bound (realCoordinate_measurable.comp (measurable_const_mul c)).aestronglyMeasurable 1
  filter_upwards with u
  simpa only [Real.norm_eq_abs, Function.comp_def] using realCoordinate_bound (c*u)

theorem directional_variance_identity (c : Group) (t : ℝ) :
    ProbabilityTheory.variance (fun u => realCoordinate (c*u)) (tilt t) =
      variance law realCoordinate (fun u => realCoordinate (c*u)) t := by
  rw [ProbabilityTheory.variance_eq_sub (directional_memLp c t)]
  simp_rw [tilt_integral]
  rfl

/-- A common lower bound in EVERY unit-quaternion half-trace direction. -/
theorem directional_variance_lower (c : Group) (t : ℝ) (ht : 0 ≤ t) :
    6/(49*(1+t)^2) ≤ variance law realCoordinate (fun u => realCoordinate (c*u)) t := by
  have h := linear_variance_lower (coefficients c) t ht
  rw [coefficients_square_sum, mul_one] at h
  have he : linearProbe (coefficients c) = fun u => realCoordinate (c*u) :=
    funext (linearProbe_coefficients c)
  rw [he, directional_variance_identity] at h
  exact h

theorem weighted_hom
    (ν : Measure QuaternionSU2Representation.SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (f : QuaternionSU2Representation.SU2 → ℝ) (hf : Measurable f) (t : ℝ) :
    weighted ν QuaternionSU2Representation.halfTrace f t =
      weighted law realCoordinate (fun u => f (QuaternionSU2Representation.hom u)) t := by
  rw [← QuaternionSU2Representation.law_eq_probability_haar ν]
  unfold weighted
  change (∫ A, f A * Real.exp (t * QuaternionSU2Representation.halfTrace A)
    ∂law.map QuaternionSU2Representation.hom) = _
  have hm : Measurable (fun A => f A * Real.exp (t * QuaternionSU2Representation.halfTrace A)) :=
    hf.mul ((measurable_const.mul QuaternionSU2Representation.halfTrace_measurable).exp)
  rw [integral_map QuaternionSU2Representation.hom_continuous.measurable.aemeasurable
    hm.aestronglyMeasurable]
  simp only [QuaternionSU2Representation.halfTrace_map]

theorem expectation_hom
    (ν : Measure QuaternionSU2Representation.SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (f : QuaternionSU2Representation.SU2 → ℝ) (hf : Measurable f) (t : ℝ) :
    expectation ν QuaternionSU2Representation.halfTrace f t =
      expectation law realCoordinate (fun u => f (QuaternionSU2Representation.hom u)) t := by
  unfold expectation
  rw [weighted_hom ν f hf, QuaternionSU2Representation.partition_halfTrace ν t]

/-- A directional covariance lower bound for the actual normalized SU2 Haar tilt. -/
theorem su2_directional_variance_lower
    (ν : Measure QuaternionSU2Representation.SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (C : QuaternionSU2Representation.SU2) (t : ℝ) (ht : 0 ≤ t) :
    6/(49*(1+t)^2) ≤ variance ν QuaternionSU2Representation.halfTrace
      (fun A => QuaternionSU2Representation.halfTrace (C*A)) t := by
  obtain ⟨c, rfl⟩ := QuaternionSU2Representation.hom_surjective C
  have hf : Measurable (fun A => QuaternionSU2Representation.halfTrace
      (QuaternionSU2Representation.hom c * A)) :=
    QuaternionSU2Representation.halfTrace_measurable.comp (measurable_const_mul _)
  unfold variance
  rw [expectation_hom ν _ (hf.pow_const 2) t, expectation_hom ν _ hf t]
  simp_rw [← QuaternionSU2Representation.hom.map_mul, QuaternionSU2Representation.halfTrace_map]
  exact directional_variance_lower c t ht

open QuaternionSU2Representation in
theorem rotated_probe_moment
    (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (V C : SU2) (t : ℝ) (k : ℕ) :
    (∫ A, halfTrace (C*A)^k ∂tiltedMeasure ν (SU2StapleTiltLaw.axis V) t) =
      expectation ν halfTrace (fun B => halfTrace ((C*V⁻¹)*B)^k) t := by
  have hm : Measurable (fun B => halfTrace ((C*V⁻¹)*B)^k) :=
    (halfTrace_measurable.comp (measurable_const_mul _)).pow_const k
  have h := integral_map (μ := tiltedMeasure ν (SU2StapleTiltLaw.axis V) t)
    (measurable_const_mul V).aemeasurable hm.aestronglyMeasurable
  rw [SU2StapleTiltLaw.tilt_map] at h
  have hg (A : SU2) : (C*V⁻¹)*(V*A) = C*A := by group
  simp only [hg] at h
  rw [tilted_integral ν halfTrace _ halfTrace_measurable halfTrace_bound] at h
  exact h.symm

open QuaternionSU2Representation in
theorem rotated_directional_variance_lower
    (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (V C : SU2) (t : ℝ) (ht : 0 ≤ t) :
    6/(49*(1+t)^2) ≤
      (∫ A, halfTrace (C*A)^2 ∂tiltedMeasure ν (SU2StapleTiltLaw.axis V) t) -
      (∫ A, halfTrace (C*A) ∂tiltedMeasure ν (SU2StapleTiltLaw.axis V) t)^2 := by
  have h1 := rotated_probe_moment ν V C t 1
  simp only [pow_one] at h1
  rw [rotated_probe_moment ν V C t 2, h1]
  exact su2_directional_variance_lower ν (C*V⁻¹) t ht

open QuaternionSU2Representation in
/-- Actual finite Wilson staple laws, including vanishing staple sums. -/
theorem staple_directional_variance_lower {ι : Type*}
    (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (s : Finset ι) (U : ι → SU2) (β : ℝ) (hβ : 0 ≤ β) (C : SU2) :
    6/(49*(1+β*(s.card:ℝ))^2) ≤
      (∫ A, halfTrace (C*A)^2 ∂SU2StapleTiltLaw.stapleLaw ν s U β) -
      (∫ A, halfTrace (C*A) ∂SU2StapleTiltLaw.stapleLaw ν s U β)^2 := by
  have ht := SU2StapleTiltLaw.concentration_bounds s U β hβ
  have hc : 0 ≤ SU2StapleTiltLaw.concentration s U β := ht.1
  have h := rotated_directional_variance_lower ν
    (SU2StaplePolar.orientation (SU2StaplePolar.quaternionSum s U)) C
    (SU2StapleTiltLaw.concentration s U β) ht.1
  change 6/(49*(1+β*(s.card:ℝ))^2) ≤ _
  apply le_trans _ h
  apply (div_le_div_iff₀ (by positivity : 0 < 49*(1+β*(s.card:ℝ))^2)
    (by positivity : 0 < 49*(1+SU2StapleTiltLaw.concentration s U β)^2)).mpr
  nlinarith

end OperatorDerivativeRewrite.Foundation.QuaternionTiltCovariance
