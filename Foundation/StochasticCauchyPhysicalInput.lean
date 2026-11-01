import Foundation.StochasticCauchyJointPastIntegral
import Foundation.GaussianSourceClockIto

/-! Physical time/source representatives for the completed joint-past core.
No equality with the full joint predictable sigma-space is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyPhysicalInput
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent

abbrev timeMeasure (T : ℝ≥0) := PredictableRealL2.horizonMeasure T gaussianProduct
abbrev Field (T : ℝ≥0) := Lp ℝ 2 ((timeMeasure T).prod gaussianProduct)

/-- The actual restricted scalar predictable step, before trimming. -/
def scalarStep (T s t : ℝ≥0) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    GaussianPredictableHorizon.PredictableDomain T :=
  GaussianRoughFiniteHorizon.restrictPredictable T
    ⟨GaussianTimeProductL2.productTensor (GaussianTimeHilbert.intervalVector s t) A,
      GaussianPredictableFull.past_step_mem_fullPredictable s t A hA⟩

theorem scalarStep_integral (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : GaussianL2) (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    GaussianPredictableHorizon.itoIntegral T (scalarStep T s t A hA) =
      GaussianPastStepCompletion.pastIncrement s t hst A hA := by
  rw [scalarStep, GaussianRoughFiniteHorizon.restricted_integral]
  have hc : GaussianPredictableCutoff.predictableCut T
      ⟨GaussianTimeProductL2.productTensor (GaussianTimeHilbert.intervalVector s t) A,
        GaussianPredictableFull.past_step_mem_fullPredictable s t A hA⟩ =
      (⟨GaussianTimeProductL2.productTensor (GaussianTimeHilbert.intervalVector s t) A,
        GaussianPredictableFull.past_step_mem_fullPredictable s t A hA⟩ :
          GaussianPredictableFull.fullPredictable) := by
    apply Subtype.ext
    exact (GaussianPredictableCutoff.cut_tensor T s t A).trans
      (by simp only [min_eq_left (show (t : ℝ) ≤ T from htT)])
  rw [hc]
  apply Lp.ext
  exact (GaussianPredictableFull.itoIntegral_past_step s t hst A hA).trans
    (GaussianPastStepCompletion.pastIncrement_coeFn s t hst A hA).symm

/-- The earlier inverse-defined mode is the actual scalar time field. -/
theorem stepMode_eq_trim (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : GaussianL2) (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    stepMode T s t hst A hA = GaussianComplexHorizonIto.trimEquiv T (scalarStep T s t A hA) := by
  apply (realIto T).injective
  rw [stepMode_integral T s t hst htT, realIto_trim, scalarStep_integral T s t hst htT]

/-- Actual representative, including the interval endpoints modulo time null sets. -/
theorem scalarStep_ae (T s t : ℝ≥0) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    (scalarStep T s t A hA).val =ᵐ[timeMeasure T]
      fun z => (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => A z.2) z.1 := by
  have hr := LpToLpRestrictCLM_coeFn ℝ (PredictableRealL2.horizon T)
    (GaussianTimeProductL2.productTensor (GaussianTimeHilbert.intervalVector s t) A)
  have hp := (GaussianTimeProductL2.productTensor_coeFn
    (GaussianTimeHilbert.intervalVector s t) A).restrict (s := PredictableRealL2.horizon T)
  have ht := ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (GaussianTimeHilbert.intervalVector_coeFn s t)).restrict
        (s := PredictableRealL2.horizon T)
  filter_upwards [hr,hp,ht] with z hr hp ht
  change (scalarStep T s t A hA).val z = _ at hr
  simp only [Function.comp_apply] at ht
  rw [hr,hp,ht]
  by_cases hz : z.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [hz]

/-- Scalar untrimming is an actual isometric embedding, with no change of values. -/
def scalarUntrim (T : ℝ≥0) :
    Lp ℝ 2 (predictableMeasure T) →ₗᵢ[ℝ] Lp ℝ 2 (timeMeasure T) :=
  (GaussianPredictableHorizon.PredictableDomain T).subtypeₗᵢ.comp
    (GaussianComplexHorizonIto.trimEquiv T).symm.toLinearIsometry

private def rawUncurry (T : ℝ≥0) :
    Lp GaussianL2 2 (timeMeasure T) ≃ₗᵢ[ℝ] Field T :=
  (ProductL2Curry.curryEquiv (timeMeasure T) gaussianProduct).symm

private def nativeCurry (T : ℝ≥0) :
    StochasticCauchyParameterizedObstruction.Domain T ≃ₗᵢ[ℝ]
      Lp GaussianL2 2 (predictableMeasure T) := by
  letI : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  exact ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct

private theorem nativeCurry_tensor (T : ℝ≥0)
    (a : Lp ℝ 2 (predictableMeasure T)) (B : GaussianL2) :
    nativeCurry T (tensorInput T a B) =
      GaussianSourceClockIto.trimEquiv T (GaussianSourceClockIto.tensor T a B) := by
  let : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  change ProductL2Curry.curry (predictableMeasure T) gaussianProduct
    (ProductL2Curry.productTensor (predictableMeasure T) gaussianProduct a B) =
      (GaussianSourceClockIto.trimEquiv T) ((GaussianSourceClockIto.trimEquiv T).symm _)
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact ProductL2Curry.curry_productTensor (predictableMeasure T) gaussianProduct a B

/-- Existing Bochner trim and product equivalences realize the native parameter
input as an actual physical time/source/source field. -/
def nativeField (T : ℝ≥0) : StochasticCauchyParameterizedObstruction.Domain T →ₗᵢ[ℝ] Field T :=
  (rawUncurry T).toLinearIsometry.comp
    (((GaussianSourceClockIto.Domain T).subtypeₗᵢ.comp
      (GaussianSourceClockIto.trimEquiv T).symm.toLinearIsometry).comp
        (nativeCurry T).toLinearIsometry)

theorem nativeField_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (B : GaussianL2) :
    nativeField T (tensorInput T a B) =
      ProductL2Curry.productTensor (timeMeasure T) gaussianProduct (scalarUntrim T a) B := by
  apply (ProductL2Curry.curryEquiv (timeMeasure T) gaussianProduct).injective
  change (ProductL2Curry.curryEquiv (timeMeasure T) gaussianProduct)
    ((ProductL2Curry.curryEquiv (timeMeasure T) gaussianProduct).symm _) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change ((GaussianSourceClockIto.trimEquiv T).symm
    (nativeCurry T (tensorInput T a B))).val = _
  rw [nativeCurry_tensor, LinearIsometryEquiv.symm_apply_apply]
  change (GaussianSourceClockIto.tensor T a B).val =
    ProductL2Curry.curry (timeMeasure T) gaussianProduct
      (ProductL2Curry.productTensor (timeMeasure T) gaussianProduct (scalarUntrim T a) B)
  rw [ProductL2Curry.curry_productTensor]
  apply Lp.ext
  have hu := lpMeasToLpTrim_ae_eq (𝕜 := ℝ)
    (PredictableRealL2.predictable_le naturalFiltration) (GaussianSourceClockIto.tensor T a B)
  have ha := lpTrimToLpMeas_ae_eq (𝕜 := ℝ)
    (PredictableRealL2.predictable_le naturalFiltration) a
  have ht : GaussianSourceClockIto.trimEquiv T (GaussianSourceClockIto.tensor T a B)
      =ᵐ[timeMeasure T]
      fun z => a z • B := by
    let : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
    change (GaussianSourceClockIto.trimEquiv T)
      ((GaussianSourceClockIto.trimEquiv T).symm _) =ᵐ[_] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact ae_eq_of_ae_eq_trim (hm := PredictableRealL2.predictable_le naturalFiltration)
      (BochnerClosedOperator.tensor_coeFn (predictableMeasure T) a B)
  filter_upwards [hu,ha,ht,
    BochnerClosedOperator.tensor_coeFn (timeMeasure T) (scalarUntrim T a) B]
    with z hu ha ht hout
  change GaussianSourceClockIto.trimEquiv T (GaussianSourceClockIto.tensor T a B) z =
    (GaussianSourceClockIto.tensor T a B).val z at hu
  change scalarUntrim T a z = a z at ha
  rw [← hu,ht,hout,ha]

/-- The completed common input is embedded without norm loss into actual fields. -/
def fieldEmbedding (T : ℝ≥0) : Input T →ₗᵢ[ℝ] Field T :=
  (nativeField T).comp (Input T).subtypeₗᵢ

theorem fieldEmbedding_step (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    fieldEmbedding T (stepInput T s t hst htT A B hA hB) =
      ProductL2Curry.productTensor (timeMeasure T) gaussianProduct
        (scalarStep T s t A hA).val B := by
  change nativeField T (tensorInput T (stepMode T s t hst A hA) B) = _
  rw [nativeField_tensor,stepMode_eq_trim T s t hst htT]
  congr 1
  exact congrArg Subtype.val ((GaussianComplexHorizonIto.trimEquiv T).symm_apply_apply _)

theorem fieldEmbedding_step_ae (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    fieldEmbedding T (stepInput T s t hst htT A B hA hB) =ᵐ[(timeMeasure T).prod gaussianProduct]
      fun z => (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => A z.1.2 * B z.2) z.1.1 := by
  rw [fieldEmbedding_step]
  have ha := (Measure.quasiMeasurePreserving_fst
    (μ := timeMeasure T) (ν := gaussianProduct)).ae_eq_comp
    (scalarStep_ae T s t A hA)
  filter_upwards [ha,ProductL2Curry.productTensor_coeFn (timeMeasure T) gaussianProduct
    (scalarStep T s t A hA).val B] with z ha hp
  simp only [Function.comp_apply] at ha
  rw [hp,ha]
  by_cases hz : z.1.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [hz,smul_eq_mul]

attribute [local instance] input_complete

theorem fieldEmbedding_closed_range (T : ℝ≥0) :
    IsClosed ((fieldEmbedding T).toLinearMap.range : Set (Field T)) :=
  (fieldEmbedding T).isometry.isClosedEmbedding.isClosed_range

theorem physical_integral_energy (T : ℝ≥0) (u v : Input T) :
    ‖integralX T u + integralY T v‖ ^ 2 =
      ‖fieldEmbedding T u‖ ^ 2 + ‖fieldEmbedding T v‖ ^ 2 := by
  rw [joint_integral_energy,(fieldEmbedding T).norm_map,(fieldEmbedding T).norm_map]


/-- Exchange the two physical Gaussian sources, retaining the actual time. -/
def sourceSwap (z : (ℝ × SampleSpace) × SampleSpace) : (ℝ × SampleSpace) × SampleSpace :=
  ((z.1.1,z.2),z.1.2)

theorem sourceSwap_preserving (T : ℝ≥0) :
    MeasurePreserving sourceSwap ((timeMeasure T).prod gaussianProduct)
      ((timeMeasure T).prod gaussianProduct) := by
  rw [timeMeasure,PredictableRealL2.horizonMeasure_eq_product]
  let ρ : Measure ℝ := volume.restrict (Ioc 0 (T : ℝ))
  have ha := measurePreserving_prodAssoc ρ gaussianProduct gaussianProduct
  have hb := (MeasurePreserving.id ρ).prod
    (Measure.measurePreserving_swap (μ := gaussianProduct) (ν := gaussianProduct))
  exact ha.symm.comp (hb.comp ha)

def swapField (T : ℝ≥0) : Field T →ₗᵢ[ℝ] Field T :=
  Lp.compMeasurePreservingₗᵢ ℝ sourceSwap (sourceSwap_preserving T)

theorem swapField_ae (T : ℝ≥0) (F : Field T) :
    swapField T F =ᵐ[(timeMeasure T).prod gaussianProduct] fun z => F (sourceSwap z) :=
  Lp.coeFn_compMeasurePreserving F (sourceSwap_preserving T)

theorem swapField_step (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    swapField T (fieldEmbedding T (stepInput T s t hst htT B A hB hA)) =
      fieldEmbedding T (stepInput T s t hst htT A B hA hB) := by
  apply Lp.ext
  have hs := (sourceSwap_preserving T).quasiMeasurePreserving.ae_eq_comp
    (fieldEmbedding_step_ae T s t hst htT B A hB hA)
  filter_upwards [swapField_ae T (fieldEmbedding T (stepInput T s t hst htT B A hB hA)),
    hs,fieldEmbedding_step_ae T s t hst htT A B hA hB] with z hswap hs ho
  rw [hswap,ho]
  change fieldEmbedding T (stepInput T s t hst htT B A hB hA) (sourceSwap z) = _ at hs
  rw [hs]
  change (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => B z.2 * A z.1.2) z.1.1 = _
  by_cases hz : z.1.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [hz,mul_comm]

attribute [local irreducible] nativeField swapField

/-- Source transport preserves the SAME actual time/source field, not merely its norm. -/
theorem relation_same_field (T : ℝ≥0)
    (z : StochasticCauchyParameterizedObstruction.Domain T ×
      StochasticCauchyParameterizedObstruction.Domain T) (hz : z ∈ relation T) :
    swapField T (nativeField T z.2) = nativeField T z.1 := by
  refine Submodule.span_induction
    (p := fun z _ => swapField T (nativeField T z.2) = nativeField T z.1) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨s,t,A,B,hst,htT,hA,hB,rfl⟩
    exact swapField_step T s t hst htT A B hA hB
  · simp
  · intro z w hz hw iz iw
    change swapField T (nativeField T (z.2+w.2)) = nativeField T (z.1+w.1)
    rw [map_add,map_add,map_add,iz,iw]
  · intro a z hz iz
    change swapField T (nativeField T (a • z.2)) = nativeField T (a • z.1)
    rw [map_smul,map_smul,map_smul,iz]

/-- Both completed native representations are the same physical integrand. -/
theorem completed_same_field (T : ℝ≥0) (u : Input T) :
    swapField T (nativeField T ((swapInput T u : SwappedInput T) :
      StochasticCauchyParameterizedObstruction.Domain T)) = fieldEmbedding T u := by
  refine (assemble_dense T).induction_on u ?_ (fun z => ?_)
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · rw [swapInput_assemble]
    exact relation_same_field T z.val z.property

/-- The physical input range is exactly the native step-span image closure. -/
theorem field_range_eq_closure (T : ℝ≥0) :
    (fieldEmbedding T).toLinearMap.range =
      ((inputSpan T).map (nativeField T).toLinearMap).topologicalClosure := by
  have he : (fieldEmbedding T).toLinearMap.range = (Input T).map (nativeField T).toLinearMap := by
    ext F
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨u.val,u.property,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u,hu⟩,rfl⟩
  apply le_antisymm
  · rw [he]
    exact (inputSpan T).topologicalClosure_map (nativeField T).toContinuousLinearMap
  · apply Submodule.topologicalClosure_minimal
    · rintro F ⟨u,hu,rfl⟩
      exact ⟨⟨u,(inputSpan T).le_topologicalClosure hu⟩,rfl⟩
    · exact fieldEmbedding_closed_range T

end OperatorDerivativeRewrite.Foundation.StochasticCauchyPhysicalInput
