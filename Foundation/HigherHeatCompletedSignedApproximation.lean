import Foundation.HigherHeatCompletedClarkOcone

/-! Actual signed native sums approximate the completed multichannel theorem.
Polynomial refinement and observable completion are separately quantified limits;
no unproved unrestricted simultaneous grid/degree limit is asserted. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedSignedApproximation
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatCompletedSignedMean HigherHeatPairedDualCausality
open HigherHeatWeakTimeAdjoint HigherHeatAllChannelNormalization
open HigherHeatMultitimeReconstruction HigherHeatMultitimeFieldMaps HigherHeatCompletedClarkOcone
open HigherHeatCenteredPowerLimits HigherHeatPredictableJetBounds HigherHeatRefinedPredictableJets

theorem native_coefficients_tendsto (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    Tendsto (fun n => HigherHeatDyadicStepAgreement.adaptedField n m hm T hT
      (fun j => predictableJet n m T j q (refinedInput b P n))) atTop
      (𝓝 (completed m hm T hT q (core (cylinderOf b P)))) := by
  rw [completed_core, cylinderMap_apply]
  exact HigherHeatMultitimePredictableFields.field_tendsto b P m hm T hT q

theorem actual_channel_limit (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (r : ℕ) (hr : r+1 < 2*m) :
    Tendsto (fun n => pairing m hm T hT (core (cylinderOf n
      (centeredPower n m T (r+1) (fun j => predictableJet n m T j (r+1) (refinedInput b P n))))))
      atTop (𝓝 (channel m T r (completed m hm T hT (r+1) (core (cylinderOf b P))))) := by
  simpa only [summand, if_pos hr, completed_core, cylinderMap_apply] using
    centered_sums_tendsto b P m hm T hT r

def nativeSurviving (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : Dual :=
  ∑ r ∈ Finset.range (2*m-1), pairing m hm T hT (core (cylinderOf n
    (centeredPower n m T (r+1) (fun j => predictableJet n m T j (r+1) (refinedInput b P n)))))

theorem native_reconstruction_limit (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (nativeSurviving b P m hm T hT) atTop
      (𝓝 (centered m hm T hT (core (cylinderOf b P)))) := by
  have h := tendsto_finsetSum (Finset.range (2*m-1))
    (fun r hr => actual_channel_limit b P m hm T hT r
      (by have := Finset.mem_range.mp hr; omega))
  change Tendsto (fun n => ∑ r ∈ Finset.range (2*m-1), pairing m hm T hT (core (cylinderOf n
    (centeredPower n m T (r+1) (fun j => predictableJet n m T j (r+1) (refinedInput b P n))))))
    atTop (𝓝 (pairing m hm T hT
      (core (cylinderOf b P)-mean m hm T hT (core (cylinderOf b P)) • core (1:Cylinder))))
  rw [clark_ocone]
  exact h

theorem actual_signed_probe_limit (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (G : Cylinder) :
    Tendsto (fun n => ((nativeSurviving b P m hm T hT n (core G) : ℝ) : ℂ)) atTop
      (𝓝 (cylindricalExpectation m hm T hT
        ((cylinderOf b P-mean m hm T hT (core (cylinderOf b P)) • (1:Cylinder))*G))) := by
  have h := ((ContinuousLinearMap.apply ℝ ℝ (core G)).continuous.tendsto
    (centered m hm T hT (core (cylinderOf b P)))).comp
      (native_reconstruction_limit b P m hm T hT)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  have he := pairing_core_complex m hm T hT
    (cylinderOf b P-mean m hm T hT (core (cylinderOf b P)) • (1:Cylinder)) G
  have he' : ((centered m hm T hT (core (cylinderOf b P)) (core G):ℝ):ℂ) =
      cylindricalExpectation m hm T hT
        ((cylinderOf b P-mean m hm T hT (core (cylinderOf b P)) • (1:Cylinder))*G) := by
    simpa only [map_sub, map_smul, centered_apply] using he
  rw [← he']
  exact hc

theorem dense_polynomial_approximation (u : Domain) :
    ∃ F : ℕ → Cylinder, Tendsto (fun k => core (F k)) atTop (𝓝 u) := by
  have hu : u ∈ closure (Set.range core) := by rw [core_dense.closure_range]; trivial
  obtain ⟨f, hf, ht⟩ := mem_closure_iff_seq_limit.mp hu
  choose F hF using hf
  refine ⟨F, ?_⟩
  have he : (fun k => core (F k)) = f := funext hF
  rw [he]
  exact ht

theorem completed_reconstruction_approximation (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    ∃ F : ℕ → Cylinder,
      Tendsto (fun k => core (F k)) atTop (𝓝 u) ∧
      (∀ q, Tendsto (fun k => completed m hm T hT q (core (F k))) atTop
        (𝓝 (completed m hm T hT q u))) ∧
      Tendsto (fun k => reconstruction m hm T hT (core (F k))) atTop
        (𝓝 (centered m hm T hT u)) := by
  obtain ⟨F, hF⟩ := dense_polynomial_approximation u
  exact ⟨F, hF, (fun q => coefficient_tendsto m hm T hT q hF),
    reconstruction_tendsto m hm T hT hF⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedSignedApproximation
