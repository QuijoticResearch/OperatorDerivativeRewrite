import Foundation.IBMPhysicalPastMeasurability

/-! The actual correction-left sums are physical L2 random variables and
agree with the EXISTING scalar predictable Ito steps under every physical
test. No convergence of these individual sums is assumed or asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectionSteps
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianPredictableFull
open IBMPhysicalWeakWiener IBMPhysicalPastMeasurability IBMConstructedSources
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul

def increment (a b : ℝ≥0) (hab : a ≤ b) : Lp Kernel 2 gaussianProduct :=
  IBMPhysicalPastIncrement.product a b hab (IBMPhysicalPointKernelIto.correctionLimit a) (correction_past a)

theorem increment_ae (a b : ℝ≥0) (hab : a ≤ b) : increment a b hab =ᵐ[gaussianProduct]
    fun Y => (clockPath Y b-clockPath Y a) • IBMPhysicalPointKernelIto.correctionLimit a Y := by
  filter_upwards [IBMPhysicalPastIncrement.product_ae a b hab
    (IBMPhysicalPointKernelIto.correctionLimit a) (correction_past a),
    clockPath_coordinate_ae a, clockPath_coordinate_ae b] with Y hp ha hb
  change increment a b hab Y = _ at hp
  rw [hp, ha, hb]

theorem increment_energy (a b : ℝ≥0) (hab : a ≤ b) :
    ‖increment a b hab‖^2 = ((b : ℝ)-a)*‖IBMPhysicalPointKernelIto.correctionLimit a‖^2 :=
  IBMPhysicalPastIncrement.product_energy a b hab _ (correction_past a)

theorem increment_past (a b : ℝ≥0) (hab : a ≤ b) :
    AEStronglyMeasurable[naturalFiltration b] (increment a b hab) gaussianProduct :=
  (((clock_past b).sub ((clock_past a).mono (naturalFiltration.mono hab))).smul
    ((correction_past a).mono (naturalFiltration.mono hab))).congr (increment_ae a b hab).symm

def scalarStep (a b : ℝ≥0) (L : Tests) : fullPredictable :=
  ⟨productTensor (GaussianTimeHilbert.intervalVector a b)
    (L.compLpL 2 gaussianProduct (IBMPhysicalPointKernelIto.correctionLimit a)),
    past_step_mem_fullPredictable a b _
      ((L.continuous.comp_aestronglyMeasurable (correction_past a)).congr
        (L.coeFn_compLpL (IBMPhysicalPointKernelIto.correctionLimit a)).symm)⟩

theorem increment_scalarization (a b : ℝ≥0) (hab : a ≤ b) (L : Tests) :
    L.compLpL 2 gaussianProduct (increment a b hab) = itoIntegral (scalarStep a b L) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (increment a b hab), increment_ae a b hab,
    itoIntegral_past_step a b hab
      (L.compLpL 2 gaussianProduct (IBMPhysicalPointKernelIto.correctionLimit a))
      ((L.continuous.comp_aestronglyMeasurable (correction_past a)).congr
        (L.coeFn_compLpL (IBMPhysicalPointKernelIto.correctionLimit a)).symm),
    L.coeFn_compLpL (IBMPhysicalPointKernelIto.correctionLimit a),
    clockPath_coordinate_ae a, clockPath_coordinate_ae b] with Y hl hi hs hc ha hb
  change (itoIntegral (scalarStep a b L)) Y = _ at hs
  rw [hl, hi, hs, hc, ha, hb, map_smul]
  change (process b Y-process a Y)*L (IBMPhysicalPointKernelIto.correctionLimit a Y) =
    L (IBMPhysicalPointKernelIto.correctionLimit a Y)*(process b Y-process a Y)
  ring

def partitionClass {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) : Lp Kernel 2 gaussianProduct :=
  ∑ i : Fin n, increment (τ i.castSucc) (τ i.succ) (hτ (Fin.castSucc_le_succ i))

theorem partitionClass_ae {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    partitionClass τ hτ =ᵐ[gaussianProduct] IBMPhysicalClockProductRule.leftCorrectionSum τ := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n =>
    increment (τ i.castSucc) (τ i.succ) (hτ (Fin.castSucc_le_succ i))),
    ae_all_iff.mpr (fun i : Fin n => increment_ae (τ i.castSucc) (τ i.succ)
      (hτ (Fin.castSucc_le_succ i)))] with Y hs hi
  change partitionClass τ hτ Y = _ at hs
  rw [hs, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _hi => hi i

theorem partition_scalarization {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) (L : Tests) :
    L.compLpL 2 gaussianProduct (partitionClass τ hτ) =
      itoIntegral (∑ i : Fin n, scalarStep (τ i.castSucc) (τ i.succ) L) := by
  change L.compLpL 2 gaussianProduct (∑ i : Fin n,
    increment (τ i.castSucc) (τ i.succ) (hτ (Fin.castSucc_le_succ i))) = _
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _hi =>
    increment_scalarization (τ i.castSucc) (τ i.succ) (hτ (Fin.castSucc_le_succ i)) L

theorem partition_scalar_mean_zero {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) (L : Tests) :
    (∫ Y, (L.compLpL 2 gaussianProduct (partitionClass τ hτ)) Y ∂gaussianProduct) = 0 := by
  rw [partition_scalarization]
  exact itoIntegral_centered _

theorem partition_past {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hend : τ (Fin.last n) ≤ T) :
    AEStronglyMeasurable[naturalFiltration T] (partitionClass τ hτ) gaussianProduct := by
  change (∑ i : Fin n, increment (τ i.castSucc) (τ i.succ) (hτ (Fin.castSucc_le_succ i))) ∈
    lpMeas Kernel ℝ (naturalFiltration T) 2 gaussianProduct
  apply Submodule.sum_mem
  intro i _hi
  exact (increment_past (τ i.castSucc) (τ i.succ) (hτ (Fin.castSucc_le_succ i))).mono
    (naturalFiltration.mono ((hτ (Fin.le_last i.succ)).trans hend))

theorem partition_mean_zero {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    (∫ Y, partitionClass τ hτ Y ∂gaussianProduct) = 0 := by
  let U := partitionClass τ hτ
  let V : Kernel := ∫ Y, U Y ∂gaussianProduct
  let L : Tests := innerSL ℝ V
  have hs : (∫ Y, L (U Y) ∂gaussianProduct) = 0 := by
    calc
      _ = ∫ Y, (L.compLpL 2 gaussianProduct U) Y ∂gaussianProduct :=
        integral_congr_ae (L.coeFn_compLpL U).symm
      _ = 0 := partition_scalar_mean_zero τ hτ L
  have hc := L.integral_comp_comm ((Lp.memLp U).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hV : inner ℝ V V = 0 := hc.symm.trans hs
  exact inner_self_eq_zero.mp hV

end OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectionSteps
