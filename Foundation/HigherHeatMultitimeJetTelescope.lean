import Foundation.HigherHeatPredictableJetDegree
import Foundation.HigherHeatCenteredPowerLimits

/-! Exact native multitime polynomial reconstruction with canonical predictable
Taylor jets, retaining every centered power before any mesh limit. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMultitimeJetTelescope
open HigherHeatPolynomialCylinders HigherHeatPredictableJetBounds HigherHeatPredictableJetIdentity
open HigherHeatPredictableJetDegree HigherHeatDyadicConditioning HigherHeatCenteredPowerLimits
open HigherHeatInnovationMoments PureOrderPolynomialConditioning

theorem cell_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (j : Fin (size n)) (P : Test n) :
    nextConditioned n m T j P-localProjection m T n (initialPast n j.val) P =
      ∑ q ∈ Finset.range (P.totalDegree+1), predictableJet n m T j q P *
        ((MvPolynomial.X j)^q-MvPolynomial.C (cellMoment n m T q)) := by
  apply MvPolynomial.funext
  intro x
  simp only [map_sub, map_sum, map_mul, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [actual_step n m hm T j P x]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (slice_degree n m T j P x)))
  intro q _ hq
  have hd : (slice n m T j P x).natDegree < q := by simp only [Finset.mem_range] at hq; omega
  rw [predictable_jet_coefficient]
  change (slice n m T j P x).coeff q * ((x j)^q-cellMoment n m T q) = 0
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd, zero_mul]

theorem initial_past_empty (n : ℕ) : initialPast n 0 = ∅ := by
  simp [initialPast]

theorem initial_past_full (n : ℕ) : initialPast n (size n) = Finset.univ := by
  ext i
  simp only [initialPast, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact i.isLt

theorem telescope (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (P : Test n) :
    P-localProjection m T n ∅ P =
      ∑ q ∈ Finset.range (P.totalDegree+1),
        centeredPower n m T q (fun j => predictableJet n m T j q P) := by
  have hs := Finset.sum_range_sub (fun c => localProjection m T n (initialPast n c) P) (size n)
  have hf := Fin.sum_univ_eq_sum_range
    (fun c => localProjection m T n (initialPast n (c+1)) P-
      localProjection m T n (initialPast n c) P) (size n)
  rw [initial_past_empty, initial_past_full, localProjection, conditioning_univ] at hs
  rw [← hs, ← hf]
  change (∑ j : Fin (size n), (nextConditioned n m T j P-
    localProjection m T n (initialPast n j.val) P)) = _
  simp only [cell_identity n m hm T]
  rw [Finset.sum_comm]
  rfl

theorem zero_innovation (n m : ℕ) (T : ℝ≥0) (F : Fin (size n) → Test n) :
    centeredPower n m T 0 F = 0 := by
  simp [centeredPower, cellMoment, PseudoPolynomialStein.moment_zero]

theorem positive_power_telescope (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (P : Test n) :
    P-localProjection m T n ∅ P =
      ∑ q ∈ Finset.range P.totalDegree,
        centeredPower n m T (q+1) (fun j => predictableJet n m T j (q+1) P) := by
  rw [telescope n m hm T P, Finset.sum_range_succ', zero_innovation, add_zero]

theorem empty_projection_actual_mean (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Test n) : localProjection m T n ∅ P =
      MvPolynomial.C ((expectation m hm T hT n P).re) := by
  apply MvPolynomial.funext
  intro x
  rw [MvPolynomial.eval_C]
  have h := congrArg Complex.re (actual_value_empty m hm
    (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) P x)
  simpa only [HigherHeatMultivariateMoments.value, Complex.ofReal_re, localProjection, expectation] using h

theorem native_dual_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (P : Test n) :
    HigherHeatCompletedPairing.pairing m hm T hT
      (HigherHeatAnalyticCylinderDomain.core (cylinderOf n P-(expectation m hm T hT n P).re • (1:Cylinder))) =
      ∑ q ∈ Finset.range P.totalDegree, HigherHeatCompletedPairing.pairing m hm T hT
        (HigherHeatAnalyticCylinderDomain.core (cylinderOf n
          (centeredPower n m T (q+1) (fun j => predictableJet n m T j (q+1) P)))) := by
  have hc (c : ℝ) : cylinderOf n (MvPolynomial.C c) = c • (1:Cylinder) := by
    change (cylinderOf n) (algebraMap ℝ (Test n) c) = _
    rw [AlgHom.commutes]
    simp only [Algebra.smul_def, mul_one]
  have h := congrArg (fun Q : Test n => HigherHeatCompletedPairing.pairing m hm T hT
    (HigherHeatAnalyticCylinderDomain.core (cylinderOf n Q))) (positive_power_telescope n m hm T P)
  simpa only [map_sub, empty_projection_actual_mean n m hm T hT P, hc, map_sum] using h

theorem actual_signed_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Test n) (G : Cylinder) :
    (((∑ q ∈ Finset.range P.totalDegree, HigherHeatCompletedPairing.pairing m hm T hT
      (HigherHeatAnalyticCylinderDomain.core (cylinderOf n
        (centeredPower n m T (q+1) (fun j => predictableJet n m T j (q+1) P)))))
      (HigherHeatAnalyticCylinderDomain.core G):ℝ):ℂ) =
      cylindricalExpectation m hm T hT ((cylinderOf n P-(expectation m hm T hT n P).re • (1:Cylinder))*G) := by
  have h := congrArg (fun φ : HigherHeatPairedDualCausality.Dual =>
    (φ (HigherHeatAnalyticCylinderDomain.core G):ℂ)) (native_dual_identity n m hm T hT P)
  exact h.symm.trans (HigherHeatCompletedPairing.pairing_core_complex m hm T hT _ G)

end OperatorDerivativeRewrite.Foundation.HigherHeatMultitimeJetTelescope
