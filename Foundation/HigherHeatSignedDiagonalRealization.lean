import Foundation.HigherHeatCompletedSignedApproximation

/-! A justified simultaneous diagonal of actual signed native reconstructions
and all surviving coefficient fields for every completed analytic observable. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSignedDiagonalRealization
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint HigherHeatMultitimeFieldMaps
open HigherHeatMultitimeReconstruction HigherHeatCompletedClarkOcone
open HigherHeatCompletedSignedApproximation HigherHeatPredictableJetBounds HigherHeatRefinedPredictableJets

abbrev Pack (m : ℕ) := (Fin (2*m-1) → Field timeMeasure) × Dual

def target (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Domain) : Pack m :=
  (fun r => completed m hm T hT (r.val+1) u, centered m hm T hT u)

def native (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : Pack m :=
  (fun r => HigherHeatDyadicStepAgreement.adaptedField n m hm T hT
    (fun j => predictableJet n m T j (r.val+1) (refinedInput b P n)),
    nativeSurviving b P m hm T hT n)

theorem native_tendsto (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (native b P m hm T hT) atTop (𝓝 (target m hm T hT (core (cylinderOf b P)))) := by
  unfold native target
  apply Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.mpr
    intro r
    exact native_coefficients_tendsto b P m hm T hT (r.val+1)
  · exact native_reconstruction_limit b P m hm T hT

theorem target_tendsto {f : ℕ → Domain} {u : Domain}
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (hf : Tendsto f atTop (𝓝 u)) :
    Tendsto (fun k => target m hm T hT (f k)) atTop (𝓝 (target m hm T hT u)) := by
  unfold target
  apply Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.mpr
    intro r
    exact coefficient_tendsto m hm T hT (r.val+1) hf
  · exact ((centered m hm T hT).continuous.tendsto u).comp hf

private theorem diagonal {E : Type*} [MetricSpace E] (g : ℕ → ℕ → E) (f : ℕ → E)
    (u : E) (b : ℕ → ℕ) (hg : ∀ k, Tendsto (g k) atTop (𝓝 (f k)))
    (hf : Tendsto f atTop (𝓝 u)) :
    ∃ n : ℕ → ℕ, (∀ k, k ≤ n k ∧ b k ≤ n k) ∧ Tendsto (fun k => g k (n k)) atTop (𝓝 u) := by
  have he : ∀ k, ∃ n, k ≤ n ∧ b k ≤ n ∧ dist (f k) (g k n) < 1/((k:ℝ)+1) := by
    intro k
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hg k) (1/((k:ℝ)+1)) (by positivity)
    refine ⟨max N (max k (b k)), (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _), ?_⟩
    rw [dist_comm]
    exact hN _ (le_max_left _ _)
  choose n hn using he
  refine ⟨n, (fun k => ⟨(hn k).1, (hn k).2.1⟩), hf.congr_dist ?_⟩
  exact squeeze_zero (fun k => dist_nonneg) (fun k => (hn k).2.2.le)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem completed_signed_realization (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    ∃ (data : ℕ → (b : ℕ) × Test b) (n : ℕ → ℕ),
      (∀ k, k ≤ n k ∧ (data k).1 ≤ n k) ∧
      Tendsto (fun k => core (cylinderOf (data k).1 (data k).2)) atTop (𝓝 u) ∧
      Tendsto (fun k => native (data k).1 (data k).2 m hm T hT (n k)) atTop
        (𝓝 (target m hm T hT u)) := by
  obtain ⟨F, hF⟩ := dense_polynomial_approximation u
  have hp : ∀ k, ∃ a : (b : ℕ) × Test b, cylinderOf a.1 a.2 = F k := by
    intro k
    induction F k using DirectLimit.induction with
    | _ b P => exact ⟨⟨b, P⟩, rfl⟩
  choose data hdata using hp
  have hd : Tendsto (fun k => core (cylinderOf (data k).1 (data k).2)) atTop (𝓝 u) := by
    simpa only [hdata] using hF
  obtain ⟨n, hn, ht⟩ := diagonal
    (fun k => native (data k).1 (data k).2 m hm T hT)
    (fun k => target m hm T hT (core (cylinderOf (data k).1 (data k).2)))
    (target m hm T hT u) (fun k => (data k).1)
    (fun k => native_tendsto (data k).1 (data k).2 m hm T hT)
    (target_tendsto m hm T hT hd)
  exact ⟨data, n, hn, hd, ht⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatSignedDiagonalRealization
