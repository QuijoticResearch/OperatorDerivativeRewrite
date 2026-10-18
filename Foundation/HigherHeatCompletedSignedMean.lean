import Foundation.HigherHeatCompletedEmptyPast

/-! Completed empty-past observable projection and actual signed expectation extension. -/
noncomputable section
open scoped NNReal

open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedSignedMean
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatAnalyticCylinderDomain
open HigherHeatCylindricalConditioning HigherHeatCompletedEmptyPast
open HigherHeatCompletedCausalProjection
open MultivariateFactorialDomain MultivariateFactorialRenaming PureOrderPolynomialConditioning

def coefficient : Domain →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : Time →₀ ℕ => ℝ) 1 0).comp commonClosure.subtypeL

theorem coefficient_bound (u : Domain) : |coefficient u| ≤ ‖u‖ :=
  lp.norm_apply_le_norm (p := 1) (by norm_num : (1:ℝ≥0∞) ≠ 0) u.val 0

open Classical in
theorem coefficient_core (n : ℕ) (P : Test n) :
    coefficient (core (cylinderOf n P)) = MvPolynomial.eval (fun _ => 0) P := by
  change embedding (cylinderOf n P) 0 = _
  rw [embedding_apply, gridEmbedding_apply]
  have he := renaming_coordinate (timeEmbedding n) (encode n P) (0 : Fin (size n) →₀ ℕ)
  have hz : (0 : Fin (size n) →₀ ℕ).embDomain (timeEmbedding n) = 0 := by simp
  rw [hz] at he
  rw [he, encode_apply, polynomial_apply]
  simp only [map_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  change MvPolynomial.constantCoeff ((coordinates n).symm P) = _
  rw [← MvPolynomial.eval_zero', eval_inverse]
  exact congrArg (fun x : Fin (size n) → ℝ => MvPolynomial.eval x P)
    (map_zero (HigherHeatPositionVariation.cumulativeEquiv (size n)).symm)

def mean (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Domain →L[ℝ] ℝ :=
  coefficient.comp (emptyProjection m hm T hT)

theorem mean_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    |mean m hm T hT u| ≤ Real.exp (T:ℝ) * ‖u‖ :=
  (coefficient_bound _).trans (emptyProjection_bound m hm T hT u)

theorem mean_norm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖mean m hm T hT‖ ≤ Real.exp (T:ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (mean_bound m hm T hT)

theorem mean_core_complex (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F : Cylinder) :
    (mean m hm T hT (core F) : ℂ) = cylindricalExpectation m hm T hT F := by
  apply tail_induction 0 (fun F =>
    (mean m hm T hT (core F) : ℂ) = cylindricalExpectation m hm T hT F) _ F
  intro n hn P
  rw [mean, ContinuousLinearMap.comp_apply, emptyProjection_core,
    dyadicProjection_apply m hm T hT 0 0 n hn P, coefficient_core, cylindricalExpectation_apply]
  have he : HigherHeatDyadicConditioning.initialPast n 0 = ∅ := by
    ext i
    simp [HigherHeatDyadicConditioning.initialPast]
  simp only [zero_mul, he]
  exact actual_value_empty m hm (fun _ => HigherHeatDyadicLaws.duration T n)
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) P (fun _ => 0)

theorem mean_core_real (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F : Cylinder) :
    mean m hm T hT (core F) = (cylindricalExpectation m hm T hT F).re := by
  simpa only [Complex.ofReal_re] using congrArg Complex.re (mean_core_complex m hm T hT F)

theorem mean_one (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    mean m hm T hT (core 1) = 1 := by
  rw [mean_core_real, cylindricalExpectation_one]
  rfl

theorem mean_unique (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (L : Domain →L[ℝ] ℝ) (hL : ∀ F, (L (core F):ℂ) = cylindricalExpectation m hm T hT F) :
    L = mean m hm T hT := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer L.continuous (mean m hm T hT).continuous
  funext F
  apply Complex.ofReal_injective
  exact (hL F).trans (mean_core_complex m hm T hT F).symm

theorem mean_projection (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) :
    (mean m hm T hT).comp (completed m hm T hT b r) = mean m hm T hT := by
  rw [mean, ContinuousLinearMap.comp_assoc, emptyProjection_left]

theorem mean_emptyProjection (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (mean m hm T hT).comp (emptyProjection m hm T hT) = mean m hm T hT := by
  rw [mean, ContinuousLinearMap.comp_assoc, emptyProjection_idempotent]

theorem core_C (n : ℕ) (c : ℝ) :
    core (cylinderOf n (MvPolynomial.C c)) = c • core (1:Cylinder) := by
  simp only [MvPolynomial.C_eq_smul_one, map_smul, map_one]

theorem empty_conditioning_constant {ι : Type*} [Fintype ι]
    (p : ℕ) (a : ι → ℝ) (P : MvPolynomial ι ℝ) :
    conditioning p a ∅ P =
      MvPolynomial.C (MvPolynomial.eval (fun _ => 0) (conditioning p a ∅ P)) := by
  apply MvPolynomial.funext
  intro x
  rw [MvPolynomial.eval_C]
  have he := conditioning_dependsOn p a ∅ P x (fun _ => 0)
    (fun i hi => by simp at hi)
  exact Complex.ofReal_injective he

theorem emptyProjection_rankOne (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    emptyProjection m hm T hT =
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (core (1:Cylinder))).comp (mean m hm T hT) := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer (emptyProjection m hm T hT).continuous
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (core (1:Cylinder))).comp (mean m hm T hT)).continuous
  funext F
  simp only [Function.comp_apply, mean, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, emptyProjection_core]
  apply tail_induction 0 (fun F => core (dyadicProjection m hm T hT 0 0 F) =
    coefficient (core (dyadicProjection m hm T hT 0 0 F)) • core (1:Cylinder)) _ F
  intro n hn P
  rw [dyadicProjection_apply m hm T hT 0 0 n hn P]
  have he : HigherHeatDyadicConditioning.initialPast n 0 = ∅ := by
    ext i
    simp [HigherHeatDyadicConditioning.initialPast]
  simp only [zero_mul, he, coefficient_core]
  let Q := HigherHeatDyadicConditioning.localProjection m T n ∅ P
  have hc : Q = MvPolynomial.C (MvPolynomial.eval (fun _ => 0) Q) :=
    empty_conditioning_constant (2*m)
      (parameters m (fun _ => HigherHeatDyadicLaws.duration T n)) P
  calc
    core (cylinderOf n Q) =
        core (cylinderOf n (MvPolynomial.C (MvPolynomial.eval (fun _ => 0) Q))) :=
      congrArg (fun R : Test n => core (cylinderOf n R)) hc
    _ = MvPolynomial.eval (fun _ => 0) Q • core (1:Cylinder) := core_C n _

theorem emptyProjection_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    emptyProjection m hm T hT u = mean m hm T hT u • core (1:Cylinder) :=
  DFunLike.congr_fun (emptyProjection_rankOne m hm T hT) u

theorem mean_biharmonic_fourth (T : ℝ≥0) (hT : 0 < T) :
    mean 2 (by norm_num) T hT (core (terminalCylinder^4)) = -24*(T:ℝ) := by
  simpa using congrArg Complex.re
    ((mean_core_complex 2 (by norm_num) T hT (terminalCylinder^4)).trans (biharmonic_fourth T hT))

theorem mean_not_positive_on_squares (T : ℝ≥0) (hT : 0 < T) :
    ∃ F : Cylinder, mean 2 (by norm_num) T hT (core (F*F)) < 0 := by
  refine ⟨terminalCylinder^2, ?_⟩
  rw [← pow_add]
  rw [mean_biharmonic_fourth T hT]
  exact mul_neg_of_neg_of_pos (by norm_num) (by exact_mod_cast hT)

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedSignedMean
