import Foundation.StochasticCauchyParameterizedObstruction

/-! A completed joint-past core for the actual two-source integral.  Its scalar
step modes and transport use existing verified integrals and dense isometries.
Identification with every jointly predictable field is a separate obligation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyJointPastIntegral
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto
open StochasticCauchyParameterizedObstruction
attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  GaussianComplexHorizonIto.realPredictableL2_secondCountable
  GaussianComplexHorizonIto.predictableL2_secondCountable

private def fullStep (s t : ℝ≥0) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    GaussianPredictableFull.fullPredictable :=
  ⟨GaussianTimeProductL2.productTensor (GaussianTimeHilbert.intervalVector s t) A,
    GaussianPredictableFull.past_step_mem_fullPredictable s t A hA⟩

private theorem fullStep_integral (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    GaussianPredictableFull.itoIntegral (fullStep s t A hA) =
      GaussianPastStepCompletion.pastIncrement s t hst A hA := by
  apply Lp.ext
  exact (GaussianPredictableFull.itoIntegral_past_step s t hst A hA).trans
    (GaussianPastStepCompletion.pastIncrement_coeFn s t hst A hA).symm

private theorem increment_mem_past (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : GaussianL2) (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    GaussianPastStepCompletion.pastIncrement s t hst A hA ∈ GaussianConditionalIto.pastL2 T := by
  have hAT := hA.mono (naturalFiltration.mono (hst.trans htT))
  have ht : AEStronglyMeasurable[naturalFiltration T] (process t) gaussianProduct :=
    ((process_stronglyAdapted t).mono (naturalFiltration.mono htT)).aestronglyMeasurable
  have hs : AEStronglyMeasurable[naturalFiltration T] (process s) gaussianProduct :=
    ((process_stronglyAdapted s).mono
      (naturalFiltration.mono (hst.trans htT))).aestronglyMeasurable
  exact (hAT.mul (ht.sub hs)).congr
    (GaussianPastStepCompletion.pastIncrement_coeFn s t hst A hA).symm

/-- Native predictable scalar mode of the actual stochastic step. -/
def stepMode (T s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    Lp ℝ 2 (predictableMeasure T) :=
  GaussianComplexHorizonIto.trimEquiv T (GaussianFiniteHorizonAdjoint.finiteAdjoint T
    (GaussianPastStepCompletion.pastIncrement s t hst A hA))

theorem stepMode_integral (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : GaussianL2) (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    realIto T (stepMode T s t hst A hA) =
      GaussianPastStepCompletion.pastIncrement s t hst A hA := by
  rw [stepMode, realIto_trim, GaussianFiniteHorizonAdjoint.finiteAdjoint_representation T _
    (increment_mem_past s t T hst htT A hA)]
  have hm : (∫ w, GaussianPastStepCompletion.pastIncrement s t hst A hA w ∂gaussianProduct)=0 := by
    rw [← fullStep_integral]
    exact GaussianPredictableFull.itoIntegral_centered _
  rw [hm, zero_smul, sub_zero]

/-- All scalar step pairings, including overlapping intervals, use the OLD
actual predictable integral isometry and its time-probability input pairing. -/
theorem stepMode_inner (T s t u v : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (huv : u ≤ v) (hvT : v ≤ T) (A C : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hC : AEStronglyMeasurable[naturalFiltration u] C gaussianProduct) :
    inner ℝ (stepMode T s t hst A hA) (stepMode T u v huv C hC) =
      inner ℝ (GaussianTimeHilbert.intervalVector s t) (GaussianTimeHilbert.intervalVector u v) *
        inner ℝ A C := by
  calc
    _ = inner ℝ (realIto T (stepMode T s t hst A hA))
        (realIto T (stepMode T u v huv C hC)) := ((realIto T).inner_map_map _ _).symm
    _ = inner ℝ (GaussianPredictableFull.itoIntegral (fullStep s t A hA))
        (GaussianPredictableFull.itoIntegral (fullStep u v C hC)) := by
      rw [stepMode_integral T s t hst htT, stepMode_integral T u v huv hvT,
        fullStep_integral s t hst, fullStep_integral u v huv]
    _ = _ := by
      rw [GaussianPredictableFull.itoIntegral.inner_map_map]
      exact GaussianTimeProductL2.productTensor_inner _ _ _ _

/-- Exact native input tensor pairing, obtained by transporting through the
existing native integral isometry rather than reproving product integration. -/
theorem tensorInput_inner (T : ℝ≥0) (a b : Lp ℝ 2 (predictableMeasure T)) (h k : GaussianL2) :
    inner ℝ (tensorInput T a h) (tensorInput T b k) = inner ℝ a b * inner ℝ h k := by
  calc
    _ = inner ℝ (firstIntegral T (tensorInput T a h))
        (firstIntegral T (tensorInput T b k)) := ((firstIntegral T).inner_map_map _ _).symm
    _ = _ := by
      rw [first_tensor, first_tensor]
      exact (StochasticCauchyParameterizedObstruction.tensor_inner _ _ _ _).trans
        (congrArg (fun x : ℝ => x * inner ℝ h k) ((realIto T).inner_map_map a b))

/-- Paired native inputs for the SAME physical joint-past step A(w1)B(w2).
The second native input is expressed in reversed source/parameter order. -/
def generators (T : ℝ≥0) : Set (Domain T × Domain T) :=
  {z | ∃ s t : ℝ≥0, ∃ A B : GaussianL2, ∃ hst : s ≤ t, ∃ _htT : t ≤ T,
    ∃ hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct,
    ∃ hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct,
      z = (tensorInput T (stepMode T s t hst A hA) B,
        tensorInput T (stepMode T s t hst B hB) A)}

def relation (T : ℝ≥0) : Submodule ℝ (Domain T × Domain T) := Submodule.span ℝ (generators T)

def inputSpan (T : ℝ≥0) : Submodule ℝ (Domain T) :=
  (relation T).map (LinearMap.fst ℝ (Domain T) (Domain T))

def swappedSpan (T : ℝ≥0) : Submodule ℝ (Domain T) :=
  (relation T).map (LinearMap.snd ℝ (Domain T) (Domain T))

def Input (T : ℝ≥0) : Submodule ℝ (Domain T) := (inputSpan T).topologicalClosure

def SwappedInput (T : ℝ≥0) : Submodule ℝ (Domain T) := (swappedSpan T).topologicalClosure

theorem input_complete (T : ℝ≥0) : CompleteSpace (Input T) :=
  (inputSpan T).isClosed_topologicalClosure.completeSpace_coe

theorem swapped_complete (T : ℝ≥0) : CompleteSpace (SwappedInput T) :=
  (swappedSpan T).isClosed_topologicalClosure.completeSpace_coe

attribute [local instance] input_complete swapped_complete

/-- Gram preservation proves the source swap is single-valued on finite
sums, even when different stochastic-step presentations give the same input. -/
theorem relation_pairing (T : ℝ≥0) (z w : Domain T × Domain T)
    (hz : z ∈ relation T) (hw : w ∈ relation T) :
    inner ℝ z.1 w.1 = inner ℝ z.2 w.2 := by
  refine Submodule.span_induction₂
    (p := fun z w _ _ => inner ℝ z.1 w.1 = inner ℝ z.2 w.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hw
  · rintro z w ⟨s,t,A,B,hst,htT,hA,hB,rfl⟩ ⟨u,v,C,D,huv,hvT,hC,hD,rfl⟩
    rw [tensorInput_inner, tensorInput_inner,
      stepMode_inner T s t u v hst htT huv hvT A C hA hC,
      stepMode_inner T s t u v hst htT huv hvT B D hB hD]
    ring
  · intro y hy; simp
  · intro x hx; simp
  · intro x y z hx hy hz hxz hyz
    simp only [Prod.fst_add, Prod.snd_add, inner_add_left, hxz, hyz]
  · intro x y z hx hy hz hxy hxz
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, hxy, hxz]
  · intro a x y hx hy hxy
    change inner ℝ (a • x.1) y.1 = inner ℝ (a • x.2) y.2
    simp only [real_inner_smul_left, hxy]
  · intro a x y hx hy hxy
    change inner ℝ x.1 (a • y.1) = inner ℝ x.2 (a • y.2)
    simp only [real_inner_smul_right, hxy]

theorem relation_norm (T : ℝ≥0) (z : Domain T × Domain T) (hz : z ∈ relation T) :
    ‖z.2‖ = ‖z.1‖ := by
  have he := relation_pairing T z z hz hz
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg z.1, norm_nonneg z.2]

attribute [local irreducible] StochasticCauchyParameterizedObstruction.firstIntegral
  StochasticCauchyParameterizedObstruction.secondIntegral

/-- The mixed ACTUAL stochastic integrals vanish on the whole algebraic core. -/
theorem relation_mixed (T : ℝ≥0) (z w : Domain T × Domain T)
    (hz : z ∈ relation T) (hw : w ∈ relation T) :
    inner ℝ (firstIntegral T z.1) (secondIntegral T w.2) = 0 := by
  refine Submodule.span_induction₂
    (p := fun z w _ _ => inner ℝ (firstIntegral T z.1) (secondIntegral T w.2) = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hw
  · rintro z w ⟨s,t,A,B,hst,htT,hA,hB,rfl⟩ ⟨u,v,C,D,huv,hvT,hC,hD,rfl⟩
    rw [first_tensor, second_tensor, stepMode_integral T s t hst htT,
      stepMode_integral T u v huv hvT]
    exact joint_past_steps_orthogonal s t u v hst huv A B D C hA hB hD hC
  · intro y hy; simp
  · intro x hx; simp
  · intro x y z hx hy hz hxz hyz
    simp only [Prod.fst_add, map_add, inner_add_left, hxz, hyz, add_zero]
  · intro x y z hx hy hz hxy hxz
    simp only [Prod.snd_add, map_add, inner_add_right, hxy, hxz, add_zero]
  · intro a x y hx hy hxy
    change inner ℝ (firstIntegral T (a • x.1)) (secondIntegral T y.2) = 0
    simp only [map_smul, real_inner_smul_left, hxy, mul_zero]
  · intro a x y hx hy hxy
    change inner ℝ (firstIntegral T x.1) (secondIntegral T (a • y.2)) = 0
    simp only [map_smul, real_inner_smul_right, hxy, mul_zero]

def assemble (T : ℝ≥0) : relation T →ₗ[ℝ] Input T where
  toFun z := ⟨z.val.1, (inputSpan T).le_topologicalClosure
    (Submodule.mem_map.mpr ⟨z.val, z.property, rfl⟩)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def assembleSwap (T : ℝ≥0) : relation T →ₗ[ℝ] SwappedInput T where
  toFun z := ⟨z.val.2, (swappedSpan T).le_topologicalClosure
    (Submodule.mem_map.mpr ⟨z.val, z.property, rfl⟩)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem assemble_dense (T : ℝ≥0) : DenseRange (assemble T) := by
  have hd : DenseRange (Submodule.inclusion (inputSpan T).le_topologicalClosure) :=
    (denseRange_inclusion_iff (inputSpan T).le_topologicalClosure).2 (by intro x hx; exact hx)
  apply hd.mono
  rintro x ⟨u,rfl⟩
  obtain ⟨z,hz,he⟩ := Submodule.mem_map.mp u.property
  exact ⟨⟨z,hz⟩,Subtype.ext he⟩

theorem assembleSwap_dense (T : ℝ≥0) : DenseRange (assembleSwap T) := by
  have hd : DenseRange (Submodule.inclusion (swappedSpan T).le_topologicalClosure) :=
    (denseRange_inclusion_iff (swappedSpan T).le_topologicalClosure).2 (by intro x hx; exact hx)
  apply hd.mono
  rintro x ⟨u,rfl⟩
  obtain ⟨z,hz,he⟩ := Submodule.mem_map.mp u.property
  exact ⟨⟨z,hz⟩,Subtype.ext he⟩

theorem assembly_norm (T : ℝ≥0) (z : relation T) : ‖assembleSwap T z‖ = ‖assemble T z‖ :=
  relation_norm T z.val z.property

/-- Existing dense-isometry extension, instantiated on actual native inputs. -/
def swapInput (T : ℝ≥0) : Input T ≃ₗᵢ[ℝ] SwappedInput T :=
  (LinearEquiv.refl ℝ (relation T)).extendOfIsometry (assemble T) (assembleSwap T)
    (assemble_dense T) (assembleSwap_dense T) (assembly_norm T)

theorem swapInput_assemble (T : ℝ≥0) (z : relation T) :
    swapInput T (assemble T z) = assembleSwap T z := by
  unfold swapInput
  exact (LinearEquiv.refl ℝ (relation T)).extendOfIsometry_eq (assemble T) (assembleSwap T)
    (assemble_dense T) (assembleSwap_dense T) (assembly_norm T) z

/-- Both source integrals now act on ONE completed, explicit joint-past input. -/
def integralX (T : ℝ≥0) : Input T →ₗᵢ[ℝ] JointL2 :=
  (firstIntegral T).comp (Input T).subtypeₗᵢ

def integralY (T : ℝ≥0) : Input T →ₗᵢ[ℝ] JointL2 :=
  (secondIntegral T).comp ((SwappedInput T).subtypeₗᵢ.comp (swapInput T).toLinearIsometry)

theorem integralX_assemble (T : ℝ≥0) (z : relation T) :
    integralX T (assemble T z) = firstIntegral T z.val.1 := rfl

theorem integralY_assemble (T : ℝ≥0) (z : relation T) :
    integralY T (assemble T z) = secondIntegral T z.val.2 := by
  change secondIntegral T ((swapInput T (assemble T z) : SwappedInput T) : Domain T) = _
  rw [swapInput_assemble]
  rfl

/-- Orthogonality survives genuine native L2 closure by density and continuity. -/
theorem integrals_orthogonal (T : ℝ≥0) (u v : Input T) :
    inner ℝ (integralX T u) (integralY T v) = 0 := by
  refine (assemble_dense T).induction_on₂ ?_ (fun z w => ?_) u v
  · exact isClosed_eq (by fun_prop) continuous_const
  · rw [integralX_assemble, integralY_assemble]
    exact relation_mixed T z.val w.val z.property w.property

/-- Actual completed two-source Ito isometry on the explicitly constructed core. -/
theorem joint_integral_energy (T : ℝ≥0) (u v : Input T) :
    ‖integralX T u + integralY T v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, integrals_orthogonal, (integralX T).norm_map,
    (integralY T).norm_map, mul_zero, add_zero]

/-- An actual joint-past generator in the algebraic native transport relation. -/
def stepPair (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) : relation T :=
  ⟨(tensorInput T (stepMode T s t hst A hA) B,
    tensorInput T (stepMode T s t hst B hB) A),
    Submodule.subset_span ⟨s,t,A,B,hst,htT,hA,hB,rfl⟩⟩

def stepInput (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) : Input T :=
  assemble T (stepPair T s t hst htT A B hA hB)

theorem integralX_stepInput (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    integralX T (stepInput T s t hst htT A B hA hB) =
      ProductL2Curry.productTensor gaussianProduct gaussianProduct
        (GaussianPastStepCompletion.pastIncrement s t hst A hA) B := by
  rw [stepInput, integralX_assemble]
  change firstIntegral T (tensorInput T (stepMode T s t hst A hA) B) = _
  rw [first_tensor, stepMode_integral T s t hst htT]

theorem integralY_stepInput (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    integralY T (stepInput T s t hst htT A B hA hB) =
      ProductL2Curry.productTensor gaussianProduct gaussianProduct A
        (GaussianPastStepCompletion.pastIncrement s t hst B hB) := by
  rw [stepInput, integralY_assemble]
  change secondIntegral T (tensorInput T (stepMode T s t hst B hB) A) = _
  rw [second_tensor, stepMode_integral T s t hst htT]

theorem stepInput_energy (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    ‖stepInput T s t hst htT A B hA hB‖ ^ 2 = ((t : ℝ)-s) * ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
  rw [← (integralX T).norm_map, integralX_stepInput]
  exact step_tensor_energy s t hst A B hA

/-- The completed joint-past pair has no spurious cancelling coefficient pair. -/
theorem joint_integral_zero_iff (T : ℝ≥0) (u v : Input T) :
    integralX T u + integralY T v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro hz
    have he := joint_integral_energy T u v
    rw [hz, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at he
    have hu : ‖u‖ = 0 := by nlinarith [sq_nonneg ‖v‖, norm_nonneg u]
    have hv : ‖v‖ = 0 := by nlinarith [sq_nonneg ‖u‖, norm_nonneg v]
    exact ⟨norm_eq_zero.mp hu,norm_eq_zero.mp hv⟩
  · rintro ⟨rfl,rfl⟩
    simp

/-- Actual bounded adjoints on ALL target L2, using the existing Hilbert
representation machinery and the proved complete native input domain. -/
def adjointX (T : ℝ≥0) : JointL2 →L[ℝ] Input T :=
  HilbertRepresentation.predictableAdjoint (integralX T)

def adjointY (T : ℝ≥0) : JointL2 →L[ℝ] Input T :=
  HilbertRepresentation.predictableAdjoint (integralY T)

theorem adjointX_integralX (T : ℝ≥0) (u : Input T) : adjointX T (integralX T u) = u :=
  HilbertRepresentation.predictableAdjoint_isometry_apply (integralX T) u

theorem adjointY_integralY (T : ℝ≥0) (u : Input T) : adjointY T (integralY T u) = u :=
  HilbertRepresentation.predictableAdjoint_isometry_apply (integralY T) u

theorem adjointX_integralY (T : ℝ≥0) (v : Input T) : adjointX T (integralY T v) = 0 := by
  apply ext_inner_right ℝ
  intro u
  rw [show adjointX T = HilbertRepresentation.predictableAdjoint (integralX T) from rfl,
    HilbertRepresentation.predictableAdjoint_pairing, real_inner_comm,
    integrals_orthogonal, inner_zero_left]

theorem adjointY_integralX (T : ℝ≥0) (u : Input T) : adjointY T (integralX T u) = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [show adjointY T = HilbertRepresentation.predictableAdjoint (integralY T) from rfl,
    HilbertRepresentation.predictableAdjoint_pairing, integrals_orthogonal, inner_zero_left]

/-- Exact two-source reconstruction of coefficients on the ACTUAL represented
range. Surjectivity onto all centered target L2 is NOT assumed or asserted. -/
theorem adjoints_recover (T : ℝ≥0) (u v : Input T) :
    adjointX T (integralX T u + integralY T v) = u ∧
    adjointY T (integralX T u + integralY T v) = v := by
  constructor <;> rw [map_add]
  · rw [adjointX_integralX, adjointX_integralY, add_zero]
  · rw [adjointY_integralX, adjointY_integralY, zero_add]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyJointPastIntegral
