import Foundation.HigherHeatMultitimeFieldMaps

/-! Completed-observable multichannel Clark–Ocone in the actual signed analytic
test-dual topology, with canonical adapted coefficients and explicit duality. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedClarkOcone
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatCompletedSignedMean HigherHeatPairedDualCausality
open HigherHeatWeakTimeAdjoint HigherHeatAllChannelNormalization
open HigherHeatMultitimeReconstruction HigherHeatMultitimeFieldMaps

def reconstruction (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Domain →L[ℝ] Dual :=
  ∑ r ∈ Finset.range (2*m-1), (channel m T r).comp (completed m hm T hT (r+1))

theorem reconstruction_core (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F : Cylinder) :
    reconstruction m hm T hT (core F) = centered m hm T hT (core F) := by
  apply HigherHeatCylindricalConditioning.tail_induction 0 (fun F =>
    reconstruction m hm T hT (core F) = centered m hm T hT (core F)) _ F
  intro b _ P
  simp only [reconstruction, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    completed_core, cylinderMap_apply]
  exact (polynomial_reconstruction b P m hm T hT).symm

theorem reconstruction_eq (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    reconstruction m hm T hT = centered m hm T hT := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer (reconstruction m hm T hT).continuous (centered m hm T hT).continuous
  funext F
  exact reconstruction_core m hm T hT F

theorem clark_ocone (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    pairing m hm T hT (u-mean m hm T hT u • core (1:Cylinder)) =
      ∑ r ∈ Finset.range (2*m-1), channel m T r (completed m hm T hT (r+1) u) := by
  have h := DFunLike.congr_fun (reconstruction_eq m hm T hT) u
  simpa only [centered_apply, reconstruction, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply] using h.symm

theorem biharmonic_three_channels (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    pairing 2 (by norm_num) T hT (u-mean 2 (by norm_num) T hT u • core (1:Cylinder)) =
      channel 2 T 0 (completed 2 (by norm_num) T hT 1 u) +
      channel 2 T 1 (completed 2 (by norm_num) T hT 2 u) +
      channel 2 T 2 (completed 2 (by norm_num) T hT 3 u) := by
  simpa only [show 2*2-1=3 by norm_num, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] using clark_ocone 2 (by norm_num) T hT u

theorem coefficient_tendsto {α : Type*} {l : Filter α} {f : α → Domain} {u : Domain}
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : ℕ) (hf : Tendsto f l (𝓝 u)) :
    Tendsto (fun a => completed m hm T hT q (f a)) l (𝓝 (completed m hm T hT q u)) :=
  ((completed m hm T hT q).continuous.tendsto u).comp hf

theorem reconstruction_tendsto {α : Type*} {l : Filter α} {f : α → Domain} {u : Domain}
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (hf : Tendsto f l (𝓝 u)) :
    Tendsto (fun a => reconstruction m hm T hT (f a)) l (𝓝 (centered m hm T hT u)) := by
  rw [← reconstruction_eq]
  exact ((reconstruction m hm T hT).continuous.tendsto u).comp hf

theorem coefficient_unique (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : ℕ)
    (L : Domain →L[ℝ] Field timeMeasure)
    (hL : ∀ b (P : Test b), L (core (cylinderOf b P)) =
      HigherHeatMultitimePredictableFields.field b P m hm T hT q) :
    L = completed m hm T hT q := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer L.continuous (completed m hm T hT q).continuous
  funext F
  apply HigherHeatCylindricalConditioning.tail_induction 0
    (fun F => L (core F) = completed m hm T hT q (core F)) _ F
  intro b _ P
  rw [completed_core, cylinderMap_apply, hL]

theorem channel_duality (m : ℕ) (T : ℝ≥0) (r : ℕ) (A : Field timeMeasure) (G : Domain) :
    channel m T r A G = (coefficient m T * ((2*m-1).descFactorial r:ℝ)) *
      ∫ t : ℝ, A t (((HigherHeatTimeDerivative.atTime t)^(2*m-1-r)) G) ∂timeMeasure := by
  rw [channel_eq]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, transpose_apply]

def synthesis (m : ℕ) (T : ℝ≥0) :
    (Fin (2*m-1) → Field timeMeasure) →L[ℝ] Dual :=
  ∑ r : Fin (2*m-1), (channel m T r.val).comp (ContinuousLinearMap.proj r)

theorem synthesis_uniqueness (m : ℕ) (T : ℝ≥0)
    (A B : Fin (2*m-1) → Field timeMeasure) :
    synthesis m T A = synthesis m T B ↔ A-B ∈ (synthesis m T).ker := by
  rw [LinearMap.mem_ker]
  simp only [map_sub, sub_eq_zero]
  rfl

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedClarkOcone
