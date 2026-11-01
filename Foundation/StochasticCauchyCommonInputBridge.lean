import Foundation.StochasticCauchyTensorReconstruction

/-! Delayed predictable parameter fields belong to the EXISTING common input.
This identifies chronological coefficients without replacing the completed domain. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyCommonInputBridge
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianTimeHilbert
open GaussianPredictableFull GaussianPredictableCutoff GaussianPredictableAdjoint
open GaussianConditionalIto GaussianConditionalClarkOcone GaussianBrownianGeneratedSpace
open GaussianPredictableL2Completion GaussianTimeDivergence
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyTensorReconstruction
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete

/-- Existing actual finite-horizon restriction, expressed through bounded maps. -/
def nativeMode (T : ℝ≥0) : fullPredictable →L[ℝ]
    Lp ℝ 2 (GaussianComplexHorizonIto.predictableMeasure T) :=
  (GaussianComplexHorizonIto.trimEquiv T).toLinearIsometry.toContinuousLinearMap.comp
    ((GaussianFiniteHorizonAdjoint.finiteAdjoint T).comp GaussianPredictableFull.itoIntegral.toContinuousLinearMap)

theorem nativeMode_apply (T : ℝ≥0) (U : fullPredictable) :
    nativeMode T U=GaussianComplexHorizonIto.trimEquiv T
      (GaussianRoughFiniteHorizon.restrictPredictable T U) := by
  change GaussianComplexHorizonIto.trimEquiv T
    (GaussianFiniteHorizonAdjoint.finiteAdjoint T (GaussianPredictableFull.itoIntegral U)) = _
  rw [GaussianFiniteHorizonAdjoint.finiteAdjoint_eq_restriction,predictableAdjoint_integral]

theorem nativeMode_cut (T : ℝ≥0) (U : fullPredictable) :
    nativeMode T (predictableCut T U)=nativeMode T U := by
  change GaussianComplexHorizonIto.trimEquiv T
    (GaussianFiniteHorizonAdjoint.finiteAdjoint T (GaussianPredictableFull.itoIntegral (predictableCut T U))) = _
  rw [← pastProjection_integral,GaussianFiniteHorizonAdjoint.finiteAdjoint_pastProjection]
  rfl

/-- The other-source parameter is fixed; this uses only a bounded rank-one tensor map. -/
def tensorMap (T : ℝ≥0) (B : GaussianL2) :
    Lp ℝ 2 (GaussianComplexHorizonIto.predictableMeasure T) →L[ℝ]
      StochasticCauchyParameterizedObstruction.Domain T := by
  letI : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  exact (ProductL2Curry.curryEquiv (GaussianComplexHorizonIto.predictableMeasure T) gaussianProduct (E := ℝ)).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((ContinuousLinearMap.toSpanSingleton ℝ B).compLpL 2 (GaussianComplexHorizonIto.predictableMeasure T))

theorem tensorMap_apply (T : ℝ≥0)
    (a : Lp ℝ 2 (GaussianComplexHorizonIto.predictableMeasure T)) (B : GaussianL2) :
    tensorMap T B a=tensorInput T a B := by
  let : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  apply (ProductL2Curry.curryEquiv (GaussianComplexHorizonIto.predictableMeasure T) gaussianProduct (E := ℝ)).injective
  change ProductL2Curry.curryEquiv (GaussianComplexHorizonIto.predictableMeasure T) gaussianProduct
    ((ProductL2Curry.curryEquiv (GaussianComplexHorizonIto.predictableMeasure T) gaussianProduct).symm _) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (ProductL2Curry.curry_productTensor (GaussianComplexHorizonIto.predictableMeasure T) gaussianProduct a B).symm

def delayedMode (T s : ℝ≥0) : fullPredictable →L[ℝ]
    Lp ℝ 2 (GaussianComplexHorizonIto.predictableMeasure T) :=
  (nativeMode T).comp (ContinuousLinearMap.id ℝ fullPredictable-predictableCut s)

def delayedInput (T s : ℝ≥0) (B : GaussianL2) : fullPredictable →L[ℝ]
    StochasticCauchyParameterizedObstruction.Domain T := (tensorMap T B).comp (delayedMode T s)

theorem delayedMode_apply (T s : ℝ≥0) (U : fullPredictable) :
    delayedMode T s U=nativeMode T (U-predictableCut s U) := rfl

theorem delayedInput_apply (T s : ℝ≥0) (B : GaussianL2) (U : fullPredictable) :
    delayedInput T s B U=tensorInput T (delayedMode T s U) B := tensorMap_apply T _ B

private def stepField (a b : ℝ≥0) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration a] A gaussianProduct) : fullPredictable :=
  ⟨GaussianTimeProductL2.productTensor (intervalVector a b) A,past_step_mem_fullPredictable a b A hA⟩

private theorem nativeMode_step (T a b : ℝ≥0) (hab : a ≤ b) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration a] A gaussianProduct) :
    nativeMode T (stepField a b A hA)=stepMode T a b hab A hA := by
  have hi : GaussianPredictableFull.itoIntegral (stepField a b A hA)=
      GaussianPastStepCompletion.pastIncrement a b hab A hA := by
    apply Lp.ext
    exact (GaussianPredictableFull.itoIntegral_past_step a b hab A hA).trans
      (GaussianPastStepCompletion.pastIncrement_coeFn a b hab A hA).symm
  change GaussianComplexHorizonIto.trimEquiv T
    (GaussianFiniteHorizonAdjoint.finiteAdjoint T (GaussianPredictableFull.itoIntegral (stepField a b A hA))) = _
  rw [hi]
  rfl

private theorem delayedMode_step (T s a b : ℝ≥0) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration a] A gaussianProduct) :
    delayedMode T s (stepField a b A hA)=nativeMode T
      (stepField (max a s) (min b T) A (hA.mono (naturalFiltration.mono (le_max_left a s)))) := by
  have hs : stepField a b A hA-predictableCut s (stepField a b A hA)=
      stepField (max a s) b A (hA.mono (naturalFiltration.mono (le_max_left a s))) := by
    apply Subtype.ext
    change GaussianTimeProductL2.productTensor (intervalVector a b) A-
      cut s (GaussianTimeProductL2.productTensor (intervalVector a b) A)=
      GaussianTimeProductL2.productTensor (intervalVector (max a s) b) A
    simpa only [NNReal.coe_max] using sub_cut_tensor s a b A
  have ht : predictableCut T
      (stepField (max a s) b A (hA.mono (naturalFiltration.mono (le_max_left a s))))=
      stepField (max a s) (min b T) A (hA.mono (naturalFiltration.mono (le_max_left a s))) := by
    apply Subtype.ext
    change cut T (GaussianTimeProductL2.productTensor (intervalVector (max a s) b) A)=
      GaussianTimeProductL2.productTensor (intervalVector (max a s) (min b T)) A
    simpa only [NNReal.coe_max,NNReal.coe_min] using cut_tensor T (max a s) b A
  rw [delayedMode_apply,hs,← nativeMode_cut T _,ht]

private theorem delayed_step_mem (T s a b : ℝ≥0) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration a] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    delayedInput T s B (stepField a b A hA) ∈ Input T := by
  change tensorMap T B (delayedMode T s (stepField a b A hA)) ∈ Input T
  rw [delayedMode_step]
  by_cases hab : max a s ≤ min b T
  · rw [nativeMode_step T _ _ hab,tensorMap_apply]
    exact (stepInput T (max a s) (min b T) hab (min_le_right b T) A B
      (hA.mono (naturalFiltration.mono (le_max_left a s)))
      (hB.mono (naturalFiltration.mono (le_max_right a s)))).property
  · have hz : stepField (max a s) (min b T) A
        (hA.mono (naturalFiltration.mono (le_max_left a s)))=0 := by
      apply Subtype.ext
      exact tensor_eq_zero_of_le _ _ (le_of_not_ge hab) A
    rw [hz,map_zero,map_zero]
    exact (Input T).zero_mem

attribute [local irreducible] nativeMode tensorMap delayedMode delayedInput

/-- Full delayed predictable fields with other-source past parameters lie in
THE EXISTING closed joint-past core; no full joint predictable density is assumed. -/
theorem delayedInput_mem (T s : ℝ≥0) (B : GaussianL2)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) (U : fullPredictable) :
    delayedInput T s B U ∈ Input T := by
  have hall (W : closedProductSteps) : delayedInput T s B (domainEquiv.symm W) ∈ Input T := by
    refine productAssembly_dense.induction_on W ?_ (fun z => ?_)
    · exact (inputSpan T).isClosed_topologicalClosure.preimage
        ((delayedInput T s B).continuous.comp domainEquiv.symm.continuous)
    · let L := (delayedInput T s B).toLinearMap.comp (domainEquiv.symm.toLinearMap.comp productAssembly)
      change L z ∈ Input T
      generalize hL : L = M
      have hz := z.property
      change M ⟨z.val,hz⟩ ∈ Input T
      refine Submodule.span_induction
        (p := fun z hz => M ⟨z,hz⟩ ∈ Input T) ?_ ?_ ?_ ?_ hz
      · rintro z ⟨n,r,p,a,b,hr,hab,rfl⟩
        rw [← hL]
        exact delayed_step_mem T s a b (pastCoefficient r p) B
          (GaussianPastStepCompletion.past_polynomial_measurable a r hr p) hB
      · change M 0 ∈ Input T
        rw [map_zero]
        exact (Input T).zero_mem
      · intro x y hx hy ihx ihy
        change M (⟨x,hx⟩+⟨y,hy⟩) ∈ Input T
        rw [map_add]
        exact (Input T).add_mem ihx ihy
      · intro c x hx ihx
        change M (c • ⟨x,hx⟩) ∈ Input T
        rw [map_smul]
        exact (Input T).smul_mem c ihx
  simpa only [domainEquiv.symm_apply_apply] using hall (domainEquiv U)

private theorem predictableCut_cut (s t : ℝ≥0) (U : fullPredictable) :
    predictableCut s (predictableCut t U)=predictableCut (min s t) U := by
  apply Subtype.ext
  exact cut_cut s t U

/-- Conditional increment modes are actual delayed predictable fields. -/
theorem incrementMode_delayed (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F : GaussianL2) (hF : F ∈ brownianL2) (i : ℕ) :
    incrementMode T τ F i=delayedMode T (τ i) (predictableCut (τ (i + 1)) (predictableAdjoint F)) := by
  rw [incrementMode,cell,GaussianFiniteHorizonAdjoint.finiteAdjoint_eq_restriction,
    map_sub,predictableAdjoint_pastProjection _ F hF,predictableAdjoint_pastProjection _ F hF,
    delayedMode_apply,nativeMode_apply,predictableCut_cut,min_eq_left (hτ (Nat.le_succ i))]

theorem increment_tensor_mem (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F : GaussianL2) (hF : F ∈ brownianL2) (i : ℕ) (B : GaussianL2)
    (hB : AEStronglyMeasurable[naturalFiltration (τ i)] B gaussianProduct) :
    tensorInput T (incrementMode T τ F i) B ∈ Input T := by
  rw [incrementMode_delayed T τ hτ F hF i,← delayedInput_apply]
  exact delayedInput_mem T (τ i) B hB _

theorem leftInput_mem (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F G : GaussianL2) (hF : F ∈ brownianL2) (n : ℕ) : leftInput T τ F G n ∈ Input T := by
  apply Submodule.sum_mem
  intro i hi
  exact increment_tensor_mem T τ hτ F hF i (pastProjection (τ i) G)
    ((pastL2 (τ i)).starProjection_apply_mem G)

theorem rightInput_mem (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F G : GaussianL2) (hG : G ∈ brownianL2) (n : ℕ) : rightInput T τ F G n ∈ Input T :=
  leftInput_mem T τ hτ G F hG n


private theorem relation_swap (T : ℝ≥0)
    (z : StochasticCauchyParameterizedObstruction.Domain T × StochasticCauchyParameterizedObstruction.Domain T)
    (hz : z ∈ relation T) : (z.2,z.1) ∈ relation T := by
  refine Submodule.span_induction (p := fun z _ => (z.2,z.1) ∈ relation T) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨s,t,A,B,hst,htT,hA,hB,rfl⟩
    exact Submodule.subset_span ⟨s,t,B,A,hst,htT,hB,hA,rfl⟩
  · exact (relation T).zero_mem
  · intro x y hx hy ihx ihy
    exact (relation T).add_mem ihx ihy
  · intro c x hx ihx
    exact (relation T).smul_mem c ihx

theorem inputSpan_eq_swappedSpan (T : ℝ≥0) : inputSpan T=swappedSpan T := by
  ext x
  change x ∈ (relation T).map (LinearMap.fst ℝ _ _) ↔
    x ∈ (relation T).map (LinearMap.snd ℝ _ _)
  constructor
  · rintro ⟨z,hz,he⟩
    exact ⟨(z.2,z.1),relation_swap T z hz,he⟩
  · rintro ⟨z,hz,he⟩
    exact ⟨(z.2,z.1),relation_swap T z hz,he⟩

/-- Equality of the two completed COORDINATE SPACES, not identity of swapInput. -/
theorem Input_eq_SwappedInput (T : ℝ≥0) : Input T=SwappedInput T := by
  unfold Input SwappedInput
  rw [inputSpan_eq_swappedSpan]

def leftCommon (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F G : GaussianL2) (hF : F ∈ brownianL2) (n : ℕ) : Input T :=
  ⟨leftInput T τ F G n,leftInput_mem T τ hτ F G hF n⟩

def rightCommon (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F G : GaussianL2) (hG : G ∈ brownianL2) (n : ℕ) : Input T :=
  (swapInput T).symm ⟨rightInput T τ F G n,by
    rw [← Input_eq_SwappedInput]
    exact rightInput_mem T τ hτ F G hG n⟩

theorem integralX_leftCommon (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F G : GaussianL2) (hF : F ∈ brownianL2) (n : ℕ) :
    integralX T (leftCommon T τ hτ F G hF n)=firstIntegral T (leftInput T τ F G n) := rfl

theorem integralY_rightCommon (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F G : GaussianL2) (hG : G ∈ brownianL2) (n : ℕ) :
    integralY T (rightCommon T τ hτ F G hG n)=secondIntegral T (rightInput T τ F G n) := by
  change secondIntegral T ((swapInput T ((swapInput T).symm _):SwappedInput T):
    StochasticCauchyParameterizedObstruction.Domain T) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

def uniformLeft (T : ℝ≥0) (F G : GaussianL2) (hF : F ∈ pastL2 T) (n : ℕ) : Input T :=
  leftCommon T (uniformGrid T n) (uniformGrid_monotone T n) F G (past_mem_brownian T hF) (n + 1)

def uniformRight (T : ℝ≥0) (F G : GaussianL2) (hG : G ∈ pastL2 T) (n : ℕ) : Input T :=
  rightCommon T (uniformGrid T n) (uniformGrid_monotone T n) F G (past_mem_brownian T hG) (n + 1)

def centeredTensor (F G : GaussianL2) : JointL2 :=
  ProductL2Curry.productTensor gaussianProduct gaussianProduct F G-
    ProductL2Curry.productTensor gaussianProduct gaussianProduct
      ((∫ w, F w ∂gaussianProduct) • gaussianOne) ((∫ w, G w ∂gaussianProduct) • gaussianOne)

/-- The actual sums now have coefficients in the EXISTING synchronized domain. -/
theorem common_sums_tendsto (T : ℝ≥0) (F G : GaussianL2)
    (hF : F ∈ pastL2 T) (hG : G ∈ pastL2 T) :
    Tendsto (fun n => integralX T (uniformLeft T F G hF n)+
      integralY T (uniformRight T F G hG n)) atTop (𝓝 (centeredTensor F G)) := by
  have he := native_past_tensor_reconstruction T F G hF hG
  apply he.congr'
  apply Eventually.of_forall
  intro n
  exact (congrArg₂ (fun x y : JointL2 => x+y)
    (integralX_leftCommon T _ (uniformGrid_monotone T n) F G (past_mem_brownian T hF) (n + 1))
    (integralY_rightCommon T _ (uniformGrid_monotone T n) F G (past_mem_brownian T hG) (n + 1))).symm

/-- Existing bounded adjoints construct the orthogonal pair-range projection. -/
def realProjection (T : ℝ≥0) : JointL2 →L[ℝ] JointL2 :=
  (integralX T).toContinuousLinearMap.comp (adjointX T)+
    (integralY T).toContinuousLinearMap.comp (adjointY T)

theorem realProjection_sum (T : ℝ≥0) (u v : Input T) :
    realProjection T (integralX T u+integralY T v)=integralX T u+integralY T v := by
  change integralX T (adjointX T (integralX T u+integralY T v))+
    integralY T (adjointY T (integralX T u+integralY T v)) = _
  rw [(adjoints_recover T u v).1,(adjoints_recover T u v).2]

/-- The reconstruction limit belongs to the actual CLOSED synchronized pair range. -/
theorem realProjection_tensor (T : ℝ≥0) (F G : GaussianL2)
    (hF : F ∈ pastL2 T) (hG : G ∈ pastL2 T) :
    realProjection T (centeredTensor F G)=centeredTensor F G := by
  have he := common_sums_tendsto T F G hF hG
  have hp := (realProjection T).continuous.continuousAt.tendsto.comp he
  change Tendsto (fun n => realProjection T (integralX T (uniformLeft T F G hF n) +
    integralY T (uniformRight T F G hG n))) atTop _ at hp
  simp only [realProjection_sum] at hp
  exact tendsto_nhds_unique hp he

/-- Exact representation of ALL independent-source past L2 tensors, with canonical coefficients. -/
theorem tensor_representation (T : ℝ≥0) (F G : GaussianL2)
    (hF : F ∈ pastL2 T) (hG : G ∈ pastL2 T) :
    integralX T (adjointX T (centeredTensor F G))+
      integralY T (adjointY T (centeredTensor F G))=centeredTensor F G :=
  realProjection_tensor T F G hF hG

/-- The actual chronological coefficients converge strongly in the SAME completed domain. -/
theorem tensor_coefficients_tendsto (T : ℝ≥0) (F G : GaussianL2)
    (hF : F ∈ pastL2 T) (hG : G ∈ pastL2 T) :
    Tendsto (uniformLeft T F G hF) atTop (𝓝 (adjointX T (centeredTensor F G))) ∧
      Tendsto (uniformRight T F G hG) atTop (𝓝 (adjointY T (centeredTensor F G))) := by
  have he := common_sums_tendsto T F G hF hG
  have hx (n : ℕ) : adjointX T (integralX T (uniformLeft T F G hF n)+
      integralY T (uniformRight T F G hG n))=uniformLeft T F G hF n :=
    (adjoints_recover T _ _).1
  have hy (n : ℕ) : adjointY T (integralX T (uniformLeft T F G hF n)+
      integralY T (uniformRight T F G hG n))=uniformRight T F G hG n :=
    (adjoints_recover T _ _).2
  constructor
  · have hp := (adjointX T).continuous.continuousAt.tendsto.comp he
    change Tendsto (fun n => adjointX T (integralX T (uniformLeft T F G hF n) +
      integralY T (uniformRight T F G hG n))) atTop _ at hp
    simpa only [hx] using hp
  · have hp := (adjointY T).continuous.continuousAt.tendsto.comp he
    change Tendsto (fun n => adjointY T (integralX T (uniformLeft T F G hF n) +
      integralY T (uniformRight T F G hG n))) atTop _ at hp
    simpa only [hy] using hp

theorem tensor_representation_unique (T : ℝ≥0) (F G : GaussianL2) (u v : Input T)
    (he : integralX T u+integralY T v=centeredTensor F G) :
    u=adjointX T (centeredTensor F G) ∧ v=adjointY T (centeredTensor F G) := by
  have hx := congrArg (adjointX T) he
  have hy := congrArg (adjointY T) he
  rw [(adjoints_recover T u v).1] at hx
  rw [(adjoints_recover T u v).2] at hy
  exact ⟨hx,hy⟩

theorem tensor_coefficient_energy (T : ℝ≥0) (F G : GaussianL2)
    (hF : F ∈ pastL2 T) (hG : G ∈ pastL2 T) :
    ‖adjointX T (centeredTensor F G)‖ ^ 2+‖adjointY T (centeredTensor F G)‖ ^ 2=
      ‖centeredTensor F G‖ ^ 2 := by
  have he := joint_integral_energy T (adjointX T (centeredTensor F G)) (adjointY T (centeredTensor F G))
  rw [tensor_representation T F G hF hG] at he
  exact he.symm

end OperatorDerivativeRewrite.Foundation.StochasticCauchyCommonInputBridge
