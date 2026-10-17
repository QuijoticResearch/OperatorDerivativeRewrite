import Foundation.PeriodicCoarseWalshBasis

/-! Exact curl and gradient coordinates on all coarse periodic edge fields. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseCurlCoordinates
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicCoarseWalshBasis
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def curlAt (q : CoarseVertex) (i j : Direction) : Field →ₗ[ℝ] ℝ where
  toFun f := coarseCurl f q i j
  map_add' f g := by simp [coarseCurl]; ring
  map_smul' r f := by simp [coarseCurl, smul_eq_mul]; ring

def curlMoment (T : Finset Direction) (i j : Direction) : Field →ₗ[ℝ] ℝ :=
  ∑ q : CoarseVertex, character T q • curlAt q i j

theorem curlMoment_apply (T : Finset Direction) (i j : Direction) (f : Field) :
    curlMoment T i j f = ∑ q : CoarseVertex, character T q * coarseCurl f q i j := by
  simp [curlMoment, LinearMap.sum_apply, LinearMap.smul_apply, curlAt, smul_eq_mul]

set_option maxHeartbeats 512000000 in
-- The finite certificate checks all character, edge-mode and direction indices.
theorem int_moment_mode : ∀ (T : Finset Direction) (a : Label) (i j : Direction),
    (∑ q : CoarseVertex, characterZ T q * coarseIntCurl (modeZ a) q i j) =
      (32 : ℤ) * ((if j ∈ T then (if a = (T,i) then (1 : ℤ) else 0) else 0) -
        (if i ∈ T then (if a = (T,j) then 1 else 0) else 0)) := by decide

theorem moment_mode (T : Finset Direction) (a : Label) (i j : Direction) :
    curlMoment T i j (mode a) =
      (32 : ℝ) * ((if j ∈ T then (if a = (T,i) then (1 : ℝ) else 0) else 0) -
        (if i ∈ T then (if a = (T,j) then 1 else 0) else 0)) := by
  rw [curlMoment_apply]
  have hc (q : CoarseVertex) : coarseCurl (mode a) q i j =
      (coarseIntCurl (modeZ a) q i j : ℝ) := coarseCurl_cast (modeZ a) q i j
  simp_rw [hc]
  simp only [character]
  exact_mod_cast int_moment_mode T a i j

theorem curlMoment_formula (T : Finset Direction) (i j : Direction) (f : Field) :
    curlMoment T i j f = 32 *
      ((if j ∈ T then coefficient (T,i) f else 0) -
        (if i ∈ T then coefficient (T,j) f else 0)) := by
  have h : curlMoment T i j = (32 : ℝ) •
      ((if j ∈ T then coefficient (T,i) else 0) -
        (if i ∈ T then coefficient (T,j) else 0)) := by
    apply basis.ext
    intro a
    rw [basis_apply, moment_mode]
    by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;>
      simp [hi, hj, coefficient_mode, smul_eq_mul]
  have he := LinearMap.congr_fun h f
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;> simpa [hi, hj, smul_eq_mul] using he

theorem int_character_gradient : ∀ (T : Finset Direction) (e : CoarseEdge),
    characterZ T (coarseShift e.1 e.2) - characterZ T e.1 =
      (-2) * ∑ i ∈ T, modeZ (T,i) e := by decide

theorem gradient_character (T : Finset Direction) :
    coarseGradient (character T) = (-2 : ℝ) • ∑ i ∈ T, mode (T,i) := by
  funext e
  have h := int_character_gradient T e
  change (character T (coarseShift e.1 e.2) - character T e.1) = _
  simp only [character, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mode]
  exact_mod_cast h

theorem curl_zero_of_incidence_zero (f : Field) (hf : coarseIncidence f = 0)
    (q : CoarseVertex) (i j : Direction) : coarseCurl f q i j = 0 := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact congrFun hf ⟨(q,i,j), hij⟩
  · subst j
    simp [coarseCurl]
  · have h := congrFun hf ⟨(q,j,i), hij⟩
    change coarseCurl f q j i = 0 at h
    simp only [coarseCurl] at h ⊢
    linarith

theorem closed_coordinate (f : Field) (hf : coarseIncidence f = 0)
    (T : Finset Direction) (p : Direction) (hp : p ∈ T) (i : Direction) :
    coefficient (T,i) f = if i ∈ T then coefficient (T,p) f else 0 := by
  have hz : curlMoment T i p f = 0 := by
    rw [curlMoment_apply]
    simp only [curl_zero_of_incidence_zero f hf, mul_zero, Finset.sum_const_zero]
  rw [curlMoment_formula, if_pos hp] at hz
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseCurlCoordinates
