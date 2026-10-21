import Foundation.HigherHeatAppellNativeTelescope

/-! Canonical p-1-channel reconstruction for actual signed terminal polynomial
observables. Equality is on the whole completed test dual; arbitrary completed
observable extension and multitime reconstruction are not asserted here. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatTerminalClarkOcone
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement
open HigherHeatAppellPredictableFields HigherHeatAppellInnovationLimits
open HigherHeatAppellNativeTelescope HigherHeatCenteredPowerLimits HigherHeatAllChannelNormalization

theorem native_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    pairing m hm T hT (core (terminalCylinder^N-
      PseudoPolynomialStein.moment (2*m) (parameter m T) N • (1:Cylinder))) =
      ∑ r ∈ Finset.range N, pairing m hm T hT (core (cylinderOf n
        (centeredPower n m T (r+1) (canonicalPast n m T N (r+1))))) := by
  have hc (c : ℝ) : cylinderOf n (MvPolynomial.C c) = c • (1:Cylinder) := by
    change (cylinderOf n) (algebraMap ℝ (Test n) c) = _
    rw [AlgHom.commutes]
    simp only [Algebra.smul_def, mul_one]
  have h := congrArg (fun F : Test n => pairing m hm T hT (core (cylinderOf n F)))
    (telescope n m hm T N)
  simpa only [map_sub, map_pow, hc, map_sum,
    ← HigherHeatTerminalPositions.terminal_on_grid n] using h

theorem reconstruction_finite (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    pairing m hm T hT (core (terminalCylinder^N-
      PseudoPolynomialStein.moment (2*m) (parameter m T) N • (1:Cylinder))) =
      ∑ r ∈ Finset.range N,
        if r+1 < 2*m then channel m T r (canonicalField m hm T hT N (r+1)) else 0 := by
  have hs := tendsto_finsetSum (Finset.range N) (fun r _ => canonical_native_limit m hm T hT N r)
  have hc := hs.congr' (Eventually.of_forall (fun n => (native_identity n m hm T hT N).symm))
  exact tendsto_nhds_unique tendsto_const_nhds hc

theorem canonical_field_above_degree (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (N q : ℕ) (hNq : N < q) : canonicalField m hm T hT N q = 0 := by
  rw [canonicalField, Nat.descFactorial_of_lt hNq, Nat.cast_zero, zero_div, zero_smul]

theorem power_reconstruction (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    pairing m hm T hT (core (terminalCylinder^N-
      PseudoPolynomialStein.moment (2*m) (parameter m T) N • (1:Cylinder))) =
      ∑ r ∈ Finset.range (2*m-1), channel m T r (canonicalField m hm T hT N (r+1)) := by
  rw [reconstruction_finite m hm T hT N]
  let H : ℕ → Dual := fun r =>
    if r+1 < 2*m then channel m T r (canonicalField m hm T hT N (r+1)) else 0
  have hlow : ∑ r ∈ Finset.range (2*m-1), H r =
      ∑ r ∈ Finset.range (2*m-1), channel m T r (canonicalField m hm T hT N (r+1)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.mp hr
    simp only [H, if_pos (by omega : r+1 < 2*m)]
  change ∑ r ∈ Finset.range N, H r = _
  rcases le_total N (2*m-1) with h | h
  · rw [← hlow]
    apply Finset.sum_subset (Finset.range_mono h)
    intro r _ hr
    have hN : N < r+1 := by simp only [Finset.mem_range] at hr; omega
    simp [H, canonical_field_above_degree m hm T hT N (r+1) hN]
  · rw [← hlow]
    symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro r _ hr
    have hp : ¬ r+1 < 2*m := by simp only [Finset.mem_range] at hr; omega
    simp [H, hp]

def polynomialField (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Polynomial ℝ) (q : ℕ) : Field timeMeasure :=
  ∑ N ∈ P.support, P.coeff N • canonicalField m hm T hT N q

theorem polynomial_field_mem (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Polynomial ℝ) (q : ℕ) :
    polynomialField m hm T hT P q ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  apply Submodule.sum_mem
  intro N _
  exact Submodule.smul_mem _ _ (canonical_field_mem m hm T hT N q)

theorem actual_centering_mean (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Polynomial ℝ) :
    PseudoPolynomialStein.expectation (2*m) (parameter m T) P =
      HigherHeatPolynomialRealization.kernelExpectation m hm T hT P := by
  rw [HigherHeatPolynomialRealization.kernelExpectation_eq_moments]
  rfl

theorem centered_polynomial_expansion (m : ℕ) (T : ℝ≥0) (P : Polynomial ℝ) :
    Polynomial.aeval terminalCylinder P-
      PseudoPolynomialStein.expectation (2*m) (parameter m T) P • (1:Cylinder) =
      ∑ N ∈ P.support, P.coeff N • (terminalCylinder^N-
        PseudoPolynomialStein.moment (2*m) (parameter m T) N • (1:Cylinder)) := by
  have hp : P = ∑ N ∈ P.support, P.coeff N • (Polynomial.X:Polynomial ℝ)^N := by
    simpa only [Polynomial.sum_def, Polynomial.smul_eq_C_mul] using P.sum_C_mul_X_pow_eq.symm
  conv_lhs => rw [hp]
  simp only [map_sum, map_smul, map_pow, Polynomial.aeval_X,
    PseudoPolynomialStein.expectation_X_pow, Finset.sum_smul, smul_sub, smul_smul,
    Finset.sum_sub_distrib, smul_eq_mul]

theorem polynomial_reconstruction (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Polynomial ℝ) :
    pairing m hm T hT (core (Polynomial.aeval terminalCylinder P-
      PseudoPolynomialStein.expectation (2*m) (parameter m T) P • (1:Cylinder))) =
      ∑ r ∈ Finset.range (2*m-1), channel m T r (polynomialField m hm T hT P (r+1)) := by
  simp only [centered_polynomial_expansion, map_sum, map_smul, power_reconstruction m hm T hT,
    polynomialField, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem actual_signed_identity (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Polynomial ℝ) (G : Cylinder) :
    (((∑ r ∈ Finset.range (2*m-1), channel m T r
      (polynomialField m hm T hT P (r+1))) (core G):ℝ):ℂ) =
      cylindricalExpectation m hm T hT ((Polynomial.aeval terminalCylinder P-
        PseudoPolynomialStein.expectation (2*m) (parameter m T) P • (1:Cylinder))*G) := by
  have h := congrArg (fun φ : Dual => (φ (core G):ℂ)) (polynomial_reconstruction m hm T hT P)
  exact h.symm.trans (pairing_core_complex m hm T hT _ G)

end OperatorDerivativeRewrite.Foundation.HigherHeatTerminalClarkOcone
