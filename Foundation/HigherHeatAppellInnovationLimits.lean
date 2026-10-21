import Foundation.HigherHeatAppellPredictableFields
import Foundation.HigherHeatCenteredPowerLimits

/-! Canonical backward-heat derivative coefficients and all native centered
innovation limits. Observable reconstruction is a separate finite-telescope obligation. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAppellInnovationLimits
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement
open HigherHeatAppellPredictableFields HigherHeatCenteredPowerLimits HigherHeatAdaptedStepDuality
open HigherHeatAllChannelNormalization PureOrderAppellCalculus HigherHeatQuadraticItoData

theorem appell_innovation_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (N r : ℕ) :
    Tendsto (fun n => pairing m hm T hT
      (core (cylinderOf n (centeredPower n m T (r+1) (appellPast n m T N))))) atTop
      (𝓝 (if r+1 < 2*m then channel m T r (appellField m hm T hT N) else (0:Dual))) := by
  have hM := fun n j => appellPast_bound n m hm T hT N j
  by_cases hr : r+1 < 2*m
  · rw [if_pos hr]
    exact low_centered_converge m hm T hT (fun n => appellPast n m T N)
      (fun n => appellPast_adapted n m T N) r hr _ hM
      (appellField m hm T hT N) (appell_fields_tendsto m hm T hT N)
  · rw [if_neg hr]
    by_cases he : r+1=2*m
    · simp_rw [he]
      exact critical_centered_vanish m hm T hT (fun n => appellPast n m T N)
        (fun n => appellPast_adapted n m T N) _ hM
    · exact higher_centered_vanish m hm T hT (fun n => appellPast n m T N)
        (fun n => appellPast_adapted n m T N) r (by omega) _ hM

def canonicalPast (n m : ℕ) (T : ℝ≥0) (N q : ℕ) (j : Fin (size n)) : Test n :=
  ((N.descFactorial q:ℝ)/(q.factorial:ℝ)) • appellPast n m T (N-q) j

def canonicalField (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N q : ℕ) : Field timeMeasure :=
  ((N.descFactorial q:ℝ)/(q.factorial:ℝ)) • appellField m hm T hT (N-q)

theorem canonical_derivative (n m : ℕ) (T : ℝ≥0) (N q : ℕ) (j : Fin (size n)) :
    canonicalPast n m T N q j = (q.factorial:ℝ)⁻¹ • Polynomial.aeval (past n j)
      (Polynomial.derivative^[q]
        (appell (2*m) (parameter m T*((HigherHeatWeightedPastFields.rightNode n j:ℝ)-1)) N)) := by
  rw [PureOrderAppellPairing.appell_iterate]
  simp only [canonicalPast, appellPast, map_smul, smul_smul, div_eq_mul_inv]
  rw [mul_comm]

theorem canonical_field_mem (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N q : ℕ) :
    canonicalField m hm T hT N q ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  exact Submodule.smul_mem _ _ (appell_field_mem m hm T hT (N-q))

theorem centered_smul (n m : ℕ) (T : ℝ≥0) (q : ℕ)
    (F : Fin (size n) → Test n) (c : ℝ) :
    centeredPower n m T q (fun j => c • F j) = c • centeredPower n m T q F := by
  simp only [centeredPower, smul_mul_assoc, Finset.smul_sum]

theorem canonical_native_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (N r : ℕ) :
    Tendsto (fun n => pairing m hm T hT
      (core (cylinderOf n (centeredPower n m T (r+1) (canonicalPast n m T N (r+1)))))) atTop
      (𝓝 (if r+1 < 2*m then channel m T r (canonicalField m hm T hT N (r+1)) else (0:Dual))) := by
  have h := (appell_innovation_limit m hm T hT (N-(r+1)) r).const_smul
    ((N.descFactorial (r+1):ℝ)/((r+1).factorial:ℝ))
  change Tendsto (fun n => pairing m hm T hT (core (cylinderOf n
    (centeredPower n m T (r+1) (fun j =>
      ((N.descFactorial (r+1):ℝ)/((r+1).factorial:ℝ)) • appellPast n m T (N-(r+1)) j))))) _ _
  simpa only [canonicalPast, centered_smul, map_smul, canonicalField, smul_ite,
    smul_zero] using h

end OperatorDerivativeRewrite.Foundation.HigherHeatAppellInnovationLimits
