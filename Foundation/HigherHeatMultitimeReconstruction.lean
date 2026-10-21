import Foundation.HigherHeatMultitimePredictableFields

/-! Full multitime polynomial Clark–Ocone reconstruction from actual centered
signed sums in completed test-dual norm. All convergence hypotheses are discharged. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMultitimeReconstruction
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatCompletedSignedMean HigherHeatPairedDualCausality
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatAdaptedStepDuality
open HigherHeatPredictableJetBounds HigherHeatPredictableJetFields HigherHeatPredictableJetDegree
open HigherHeatMultitimeJetTelescope HigherHeatCenteredPowerLimits HigherHeatRefinedPredictableJets
open HigherHeatMultitimePredictableFields HigherHeatAllChannelNormalization

def centered (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Domain →L[ℝ] Dual :=
  (pairing m hm T hT).comp
    (ContinuousLinearMap.id ℝ Domain - (mean m hm T hT).smulRight (core (1:Cylinder)))

theorem centered_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    centered m hm T hT u = pairing m hm T hT (u - mean m hm T hT u • core (1:Cylinder)) := rfl

def summand (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (r : ℕ) : Dual :=
  if r+1 < 2*m then channel m T r (field b P m hm T hT (r+1)) else 0

theorem centered_sums_tendsto (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    Tendsto (fun n => pairing m hm T hT (core (cylinderOf n
      (centeredPower n m T (r+1) (fun j => predictableJet n m T j (r+1) (refinedInput b P n))))))
      atTop (𝓝 (summand b P m hm T hT r)) := by
  by_cases hr : r+1 < 2*m
  · rw [summand, if_pos hr]
    exact low_centered_converge m hm T hT _
      (fun n => predictable_jets_adapted n m T (r+1) _) r hr _
      (fun n j => refined_jet_bound b P n m hm T hT j (r+1)) _
      (field_tendsto b P m hm T hT (r+1))
  · rw [summand, if_neg hr]
    by_cases he : r+1=2*m
    · simpa only [he] using critical_refined_vanish b P m hm T hT
    · exact higher_refined_vanish b P m hm T hT r (by omega)

theorem padded_telescope (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Test n) (D : ℕ) (hD : P.totalDegree ≤ D) :
    centered m hm T hT (core (cylinderOf n P)) =
      ∑ r ∈ Finset.range D, pairing m hm T hT (core (cylinderOf n
        (centeredPower n m T (r+1) (fun j => predictableJet n m T j (r+1) P)))) := by
  have hn := native_dual_identity n m hm T hT P
  have hc : centered m hm T hT (core (cylinderOf n P)) =
      pairing m hm T hT (core (cylinderOf n P-(expectation m hm T hT n P).re • (1:Cylinder))) := by
    simp only [centered_apply, mean_core_real, cylindricalExpectation_apply, map_sub, map_smul]
  rw [hc, hn]
  apply Finset.sum_subset (Finset.range_mono hD)
  intro r _ hr
  have hd : P.totalDegree < r+1 := by simp only [Finset.mem_range] at hr; omega
  simp only [jet_zero_above_degree n m T _ (r+1) P hd, centeredPower,
    zero_mul, Finset.sum_const_zero, map_zero]

theorem polynomial_reconstruction (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) :
    centered m hm T hT (core (cylinderOf b P)) =
      ∑ r ∈ Finset.range (2*m-1), channel m T r (field b P m hm T hT (r+1)) := by
  let D := max P.totalDegree (2*m-1)
  have hs := tendsto_finset_sum (Finset.range D)
    (fun r _ => centered_sums_tendsto b P m hm T hT r)
  have he : (fun n => ∑ r ∈ Finset.range D, pairing m hm T hT (core (cylinderOf n
      (centeredPower n m T (r+1) (fun j => predictableJet n m T j (r+1) (refinedInput b P n))))))
      =ᶠ[atTop] fun _ => centered m hm T hT (core (cylinderOf b P)) := by
    filter_upwards [eventually_ge_atTop b] with n hn
    rw [← padded_telescope n m hm T hT _ D
      ((HigherHeatRefinementDegree.refined_input_degree b P n).trans (le_max_left _ _)),
      refined_core b P n hn]
  have hlim := hs.congr' he
  have hh := tendsto_nhds_unique tendsto_const_nhds hlim
  change centered m hm T hT (core (cylinderOf b P)) = _ at hh
  rw [hh]
  calc
    (∑ r ∈ Finset.range D, summand b P m hm T hT r) =
        ∑ r ∈ Finset.range (2*m-1), summand b P m hm T hT r := by
      symm
      apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
      intro r _ hr
      have hn : ¬ r+1 < 2*m := by simp only [Finset.mem_range] at hr; omega
      simp [summand, hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [summand, if_pos (by have := Finset.mem_range.mp hr; omega)]

end OperatorDerivativeRewrite.Foundation.HigherHeatMultitimeReconstruction
