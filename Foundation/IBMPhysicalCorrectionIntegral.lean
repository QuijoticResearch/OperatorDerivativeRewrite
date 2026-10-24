import Foundation.IBMPhysicalContinuousFields

/-! The actual correction-left sums converge to the ORIGINAL physical Ito map
of a proved predictable physical time-L2 field. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectionIntegral
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMPhysicalWeakWiener IBMPhysicalContinuousFields IBMPhysicalCorrectionContinuity
open IBMPhysicalNativeCorrectionSteps IBMPhysicalPredictableSteps
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : SecondCountableTopology Kernel :=
  (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).isometry.isEmbedding.secondCountableTopology

theorem fieldClass_eq_tensor (a b : ℝ≥0) (U : Lp Kernel 2 gaussianProduct) :
    fieldClass a b U = ProductL2Curry.productTensor volume gaussianProduct
      (GaussianTimeHilbert.intervalVector a b) U := by
  apply Lp.ext
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp
      (GaussianTimeHilbert.intervalVector_coeFn a b)
  filter_upwards [fieldClass_ae a b U,
    ProductL2Curry.productTensor_coeFn volume gaussianProduct
      (GaussianTimeHilbert.intervalVector a b) U, ht] with z hf hp ht
  simp only [Function.comp_apply] at ht
  rw [hf, hp, ht]
  by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ) <;>
    simp [IBMPhysicalPredictableSteps.field, hz]

theorem partitionInput_val {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) :
    (partitionInput T τ).val = IBMSchwartzPhysicalClockIntegral.restriction T
      (partition τ (fun i => IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc))) := by
  simp only [partitionInput, Submodule.coe_sum]
  rw [partition, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  change IBMSchwartzPhysicalClockIntegral.restriction T (fieldClass _ _ _) = _
  rw [fieldClass_eq_tensor]

def rawField (T : ℝ≥0) : Lp Kernel 2 GaussianTimeProductL2.timeProbability :=
  IBMPhysicalContinuousFields.field IBMPhysicalPointKernelIto.correctionLimit
    correction_continuous T

theorem rawField_slices (T : ℝ≥0) : ∀ᵐ t ∂(volume : Measure ℝ),
    (fun Y => rawField T (t, Y)) =ᵐ[gaussianProduct]
      fun Y => (Ioc 0 (T : ℝ)).indicator
        (fun r => IBMPhysicalPointKernelIto.correctionLimit r.toNNReal Y) t := by
  have hc := ProductL2Curry.curryEquiv_coeFn volume gaussianProduct (rawField T)
  filter_upwards [hc, field_slices _ correction_continuous T] with t hc ht
  change curry (rawField T) t = _ at ht
  change curry (rawField T) t =ᵐ[gaussianProduct] _ at hc
  rw [ht, horizonValue] at hc
  by_cases hp : t ∈ Ioc 0 (T : ℝ)
  · rw [indicator_of_mem hp] at hc
    simpa only [indicator_of_mem hp] using hc.symm
  · rw [indicator_of_notMem hp] at hc
    filter_upwards [hc, Lp.coeFn_zero Kernel 2 gaussianProduct] with Y hc hz
    simpa only [indicator_of_notMem hp, Pi.zero_apply] using hc.symm.trans hz

def rawInput (T : ℝ≥0) : Lp Kernel 2 (PredictableRealL2.horizonMeasure T gaussianProduct) :=
  IBMSchwartzPhysicalClockIntegral.restriction T (rawField T)

theorem input_values_tendsto (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ : ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => (partitionInput T (τ N)).val) atTop (𝓝 (rawInput T)) := by
  simp only [partitionInput_val, rawInput, rawField]
  exact (IBMSchwartzPhysicalClockIntegral.restriction T).continuous.tendsto _ |>.comp
    (partition_tendsto _ correction_continuous m τ hτ T hstart hend ε hlim hmesh)

theorem rawInput_predictable (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (rawInput T) (PredictableRealL2.horizonMeasure T gaussianProduct) := by
  have hc := input_values_tendsto (fun N => N+1) (uniformTime T)
    (uniformTime_monotone T) T (fun N => (uniformTime_endpoints T N).1)
    (fun N => (uniformTime_endpoints T N).2) (fun N => (T : ℝ)/(N+1))
    (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    (fun N k => (uniformTime_step T N k).le)
  apply (isClosed_aestronglyMeasurable (F := Kernel) (p := (2 : ℝ≥0∞))
    (PredictableRealL2.predictable_le naturalFiltration)).mem_of_tendsto hc
  exact Eventually.of_forall fun N => (partitionInput T (uniformTime T N)).property

def integrand (T : ℝ≥0) : IBMPhysicalClockIto.Domain T :=
  ⟨rawInput T, rawInput_predictable T⟩

theorem integrand_tendsto (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ : ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => partitionInput T (τ N)) atTop (𝓝 (integrand T)) :=
  tendsto_subtype_rng.mpr (input_values_tendsto m τ hτ T hstart hend ε hlim hmesh)

def integralValue (T : ℝ≥0) : Lp Kernel 2 gaussianProduct :=
  IBMPhysicalClockIto.integral T (integrand T)

theorem native_tendsto (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ : ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => IBMPhysicalCorrectionSteps.partitionClass (τ N) (hτ N))
      atTop (𝓝 (integralValue T)) := by
  have hc := (IBMPhysicalClockIto.integral_isometry T).continuous.tendsto (integrand T) |>.comp
    (integrand_tendsto m τ hτ T hstart hend ε hlim hmesh)
  simpa only [Function.comp_def, partition_integral T _ (hτ _) (le_of_eq (hend _)),
    integralValue] using hc

end OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectionIntegral
