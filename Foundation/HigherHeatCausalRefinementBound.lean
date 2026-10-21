import Foundation.HigherHeatConditionalCutBound
import Foundation.HigherHeatCausalJetIdentification

/-! Quantitative adjacent-refinement comparison of actual causal coefficients. -/
noncomputable section
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCausalRefinementBound
open HigherHeatPolynomialCylinders HigherHeatPolynomialRefinement HigherHeatGridDoubling
open HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing HigherHeatDyadicConditioning
open HigherHeatConditionalCutBound HigherHeatCausalJetIdentification MultivariateFactorialDomain

theorem iterate_degree {ι : Type*} (v : ι → ℝ) (q : ℕ) (P : MvPolynomial ι ℝ) :
    ((polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[q] P).totalDegree ≤
      P.totalDegree := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact MultivariatePolynomialNilpotence.derivative_degree_drop v P.totalDegree _
      (ih.trans (Nat.le_succ _))

theorem derivative_step (n : ℕ) (i : Fin (size (n+1))) (q : ℕ) (P : Test n) :
    (polynomialDerivative (Pi.single i 1) : Test (n+1) → Test (n+1))^[q] (step n P) =
      step n ((polynomialDerivative (Pi.single (pairBlock i) 1) : Test n → Test n)^[q] P) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    exact HigherHeatAffineStepCorrection.derivative_pullback (@pairBlock (size n)) i
      ((polynomialDerivative (Pi.single (pairBlock i) 1) : Test n → Test n)^[q] P)

theorem cylinder_step (n : ℕ) (P : Test n) : cylinderOf (n+1) (step n P) = cylinderOf n P := by
  have h := cylinder_refinement n (n+1) (Nat.le_succ n) P
  change cylinderOf (n+1) (transfer n (n+1) (le_rfl.trans (Nat.le_succ n)) P) = _ at h
  rw [transfer_succ n n le_rfl, transfer_self] at h
  exact h

theorem coarse_left_projection (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (P : Test n) :
    cylinderOf (n+1) (localProjection m T (n+1) (initialPast (n+1) (2*j.val)) (step n P)) =
      cylinderOf n (localProjection m T n (initialPast n j.val) P) := by
  have h := localProjection_step m hm T hT n (initialPast n j.val) P
  have he := congrArg (fun S : Finset (Fin (size (n+1))) =>
    localProjection m T (n+1) S (step n P)) (pastCells_initialPast n j.val)
  exact (congrArg (cylinderOf (n+1)) (he.symm.trans h)).trans (cylinder_step n _)

theorem causal_refinement_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n (P : Test n), P.totalDegree ≤ D →
      ∀ (i : Fin (size (n+1))) (q : ℕ),
      ‖pairing m hm T hT (core (cylinderOf (n+1) (causalJet (n+1) m T i q (step n P))))-
        pairing m hm T hT (core (cylinderOf n (causalJet n m T (pairBlock i) q P)))‖ ≤
        (q.factorial:ℝ)⁻¹*K*(HigherHeatDyadicLaws.duration 1 (n+1):ℝ)*‖core (cylinderOf n P)‖ := by
  obtain ⟨K, hK, hc⟩ := conditional_cut_bound m hm T hT D
  refine ⟨K, hK, ?_⟩
  intro n P hD i q
  let Q : Test n := (polynomialDerivative (Pi.single (pairBlock i) 1) : Test n → Test n)^[q] P
  have hdeg : (step n Q).totalDegree ≤ D :=
    (HigherHeatRefinementDegree.step_degree n Q).trans ((iterate_degree _ q P).trans hD)
  have hcore : ‖core (cylinderOf (n+1) (step n Q))‖ ≤ ‖core (cylinderOf n P)‖ := by
    rw [cylinder_step]
    exact HigherHeatPositionPairedBound.core_iterate_bound n (pairBlock i) q P
  have hlt : 2*(pairBlock i).val ≤ i.val := by simp only [pairBlock]; omega
  have hdelta : ((i.val-2*(pairBlock i).val:ℕ):ℝ) ≤ 1 := by
    exact_mod_cast (show i.val-2*(pairBlock i).val ≤ 1 by simp only [pairBlock]; omega)
  have hs := hc (n+1) (step n Q) hdeg (2*(pairBlock i).val) i.val hlt (by omega)
  have hs' : ‖pairing m hm T hT (core (cylinderOf (n+1)
      (localProjection m T (n+1) (initialPast (n+1) i.val) (step n Q)-
        localProjection m T (n+1) (initialPast (n+1) (2*(pairBlock i).val)) (step n Q))))‖ ≤
      K*(HigherHeatDyadicLaws.duration 1 (n+1):ℝ)*‖core (cylinderOf n P)‖ := by
    apply hs.trans
    calc
      _ ≤ K*1*(HigherHeatDyadicLaws.duration 1 (n+1):ℝ)*‖core (cylinderOf n P)‖ := by gcongr
      _ = _ := by ring
  simp only [causalJet, derivative_step, map_smul]
  change ‖(q.factorial:ℝ)⁻¹ • pairing m hm T hT (core (cylinderOf (n+1)
      (localProjection m T (n+1) (initialPast (n+1) i.val) (step n Q))))-
    (q.factorial:ℝ)⁻¹ • pairing m hm T hT (core (cylinderOf n
      (localProjection m T n (initialPast n (pairBlock i).val) Q)))‖ ≤ _
  rw [← coarse_left_projection n m hm T hT, ← smul_sub, ← map_sub, ← map_sub, ← map_sub,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (q.factorial:ℝ)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hs' (by positivity)).trans_eq (by ring)

end OperatorDerivativeRewrite.Foundation.HigherHeatCausalRefinementBound
