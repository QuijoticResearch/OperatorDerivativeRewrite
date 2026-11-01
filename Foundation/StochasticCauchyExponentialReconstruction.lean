import Foundation.StochasticCauchyExponentialInput
import Foundation.GaussianTerminalBracketPrediction

/-! Actual chronological exponential reconstruction from original derivative
graphs, full-past prediction and the native input constructed previously. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyExponentialReconstruction
open InfiniteGaussian ProductL2Curry ComplexL2Isometry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels StochasticCauchyMalliavinBridge
open StochasticCauchyCausalRotation StochasticCauchyMeanResidual
open StochasticCauchyExponentialPrediction StochasticCauchyExponentialInput
open GaussianTimeProcess GaussianTimeHilbert GaussianTimeDivergence
open GaussianComplexHorizonIto GaussianFiniteHorizonAdjoint GaussianPredictableAdjoint
open GaussianPredictableFull GaussianContinuousRigidity GaussianTimeFieldNorm
open GaussianBrownianQuadraticVariation
attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete
  GaussianProductDerivative.coefficientSpace_secondCountable timeHilbert_secondCountable
  GaussianComplexHorizonIto.realPredictableL2_secondCountable

private theorem finiteField_step (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : GaussianL2) (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    finiteField T (stepMode T s t hst A hA)=scalarTensor (incrementDirection s t) A := by
  have he : extendPredictable T ((trimEquiv T).symm (stepMode T s t hst A hA))=
      ⟨GaussianTimeProductL2.productTensor (intervalVector s t) A,
        past_step_mem_fullPredictable s t A hA⟩ := by
    apply GaussianPredictableFull.itoIntegral.injective
    rw [← finite_integral_eq_extended]
    change realIto T (stepMode T s t hst A hA)=_
    rw [stepMode_integral T s t hst htT]
    exact Lp.ext ((GaussianPastStepCompletion.pastIncrement_coeFn s t hst A hA).trans
      (itoIntegral_past_step s t hst A hA).symm)
  change predictableField (extendPredictable T ((trimEquiv T).symm _))=_
  rw [he]
  exact GaussianContinuousRigidity.fieldEmbedding_tensor (intervalVector s t) A

attribute [local irreducible] directionField StochasticCauchyMalliavinBridge.nativeField
  stepMode finiteField fieldX

/-- Exact causal pairing with an OLD actual stochastic past-step input. -/
theorem causal_step_pairing (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (h : CoefficientSpace) (a : JointL2) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    inner ℝ (causalX T (directionField h a)) (stepInput T s t hst htT A B hA hB)=
      inner ℝ h (incrementDirection s t)*inner ℝ a
        (productTensor gaussianProduct gaussianProduct A B) := by
  change inner ℝ (HilbertRepresentation.predictableAdjoint (fieldX T) _) _=_
  rw [HilbertRepresentation.predictableAdjoint_pairing]
  rw [fieldX]
  change inner ℝ (directionField h a)
    (StochasticCauchyMalliavinBridge.nativeField T (tensorInput T (stepMode T s t hst A hA) B))=_
  rw [nativeField_tensor,finiteField_step T s t hst htT,directionField_pairing]

theorem step_ibp_X (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (h : CoefficientSpace) (F a : JointL2)
    (hF : (F,directionField h a) ∈ sourceDerivative.graph) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    inner ℝ F (integralX T (stepInput T s t hst htT A B hA hB))=
      inner ℝ h (incrementDirection s t)*inner ℝ a
        (productTensor gaussianProduct gaussianProduct A B) := by
  rw [← HilbertRepresentation.predictableAdjoint_pairing (integralX T)]
  change inner ℝ (adjointX T F) _=_
  rw [adjointX_derivative T F _ hF]
  exact causal_step_pairing T s t hst htT h a A B hA hB

/-- The Y graph is the ORIGINAL exchanged-source graph, not an adapted surrogate. -/
theorem step_ibp_Y (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (h : CoefficientSpace) (F a : JointL2)
    (hF : (swap gaussianProduct gaussianProduct F,
      directionField h (swap gaussianProduct gaussianProduct a)) ∈ sourceDerivative.graph)
    (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    inner ℝ F (integralY T (stepInput T s t hst htT A B hA hB))=
      inner ℝ h (incrementDirection s t)*inner ℝ a
        (productTensor gaussianProduct gaussianProduct A B) := by
  rw [← HilbertRepresentation.predictableAdjoint_pairing (integralY T)]
  change inner ℝ (adjointY T F) _=_
  rw [adjointY_derivative T F _ hF,causal_rotation]
  exact causal_step_pairing T s t hst htT h a A B hA hB

theorem normalized_channel_combine (T : ℝ≥0) (a b : Input T) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • combineInput T a b)=
      combine (gaussianProduct.prod gaussianProduct)
        (integralX T a-integralY T b) (integralX T b+integralY T a) := by
  have hs : (((Real.sqrt 2:ℝ):ℂ)*(((Real.sqrt 2)⁻¹:ℝ):ℂ))=1 := by
    rw [← Complex.ofReal_mul,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))),
      Complex.ofReal_one]
  rw [map_smul]
  change ((Real.sqrt 2:ℝ):ℂ) • ((((Real.sqrt 2)⁻¹:ℝ):ℂ) •
    (liftInput T (integralX T) (combineInput T a b)+
      Complex.I • liftInput T (integralY T) (combineInput T a b)))=_
  rw [smul_smul,hs,one_smul,liftInput_combine,liftInput_combine]
  simp only [combine,map_sub,map_add,smul_add,smul_sub,smul_smul,
    Complex.I_mul_I,neg_one_smul]
  abel

private theorem complex_inner_re (F : JointComplex) (a b : JointL2) :
    (inner ℂ F (combine (gaussianProduct.prod gaussianProduct) a b)).re=
      inner ℝ (realPart (gaussianProduct.prod gaussianProduct) F) a+
        inner ℝ (imagPart (gaussianProduct.prod gaussianProduct) F) b := by
  rw [L2.inner_def]
  have hi := Complex.reCLM.integral_comp_comm
    (L2.integrable_inner (𝕜 := ℂ) F (combine (gaussianProduct.prod gaussianProduct) a b))
  change (∫ w,(inner ℂ (F w) (combine (gaussianProduct.prod gaussianProduct) a b w)).re
    ∂gaussianProduct.prod gaussianProduct)=
      (∫ w,inner ℂ (F w) (combine (gaussianProduct.prod gaussianProduct) a b w)
        ∂gaussianProduct.prod gaussianProduct).re at hi
  rw [← hi]
  change (∫ w,(inner ℂ (F w) (combine (gaussianProduct.prod gaussianProduct) a b w)).re
    ∂gaussianProduct.prod gaussianProduct)=_
  have he : (∫ w,(inner ℂ (F w) (combine (gaussianProduct.prod gaussianProduct) a b w)).re
      ∂gaussianProduct.prod gaussianProduct)=
      ∫ w,(realPart (gaussianProduct.prod gaussianProduct) F w)*a w+
        (imagPart (gaussianProduct.prod gaussianProduct) F w)*b w
        ∂gaussianProduct.prod gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct) a b,
      Complex.reCLM.coeFn_compLpL F,Complex.imCLM.coeFn_compLpL F] with w hc hr hi
    change realPart (gaussianProduct.prod gaussianProduct) F w=(F w).re at hr
    change imagPart (gaussianProduct.prod gaussianProduct) F w=(F w).im at hi
    rw [hc,hr,hi]
    simp only [RCLike.inner_apply,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Complex.conj_re,Complex.conj_im]
    ring
  have ha : Integrable (fun w => realPart (gaussianProduct.prod gaussianProduct) F w*a w)
      (gaussianProduct.prod gaussianProduct) := (Lp.memLp _).integrable_mul (Lp.memLp a)
  have hb : Integrable (fun w => imagPart (gaussianProduct.prod gaussianProduct) F w*b w)
      (gaussianProduct.prod gaussianProduct) := (Lp.memLp _).integrable_mul (Lp.memLp b)
  rw [he,integral_add ha hb,L2_inner_eq_integral,L2_inner_eq_integral]
  simp only [Real.inner_apply,mul_comm]

private def horizonDirection (T : ℝ≥0) : CoefficientSpace :=
  SeparableHilbertEmbedding.hilbertEmbedding TimeHilbert (timeVector T)

private theorem observable_eq (T : ℝ≥0) :
    observable T=StochasticCauchyExponential.exponential (horizonDirection T) := rfl

private theorem horizon_inner (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    inner ℝ (horizonDirection T) (incrementDirection s t)=(t:ℝ)-s := by
  rw [real_inner_comm]
  exact GaussianTerminalBracketPrediction.increment_terminal_inner s t T hst htT

private theorem past_energy_pairing (S T : ℝ≥0) (hST : S ≤ T) :
    inner ℝ (realCurve T) (realCurve S)+inner ℝ (imagCurve T) (imagCurve S)=
      Real.exp (2*(S:ℝ)) := by
  have hs : AEStronglyMeasurable[StochasticCauchyPastReconstruction.jointPast S]
      (observable S) (gaussianProduct.prod gaussianProduct) :=
    (value_stronglyMeasurable S).aestronglyMeasurable.congr (observable_ae S).symm
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℂ)
    (StochasticCauchyPastReconstruction.jointPast_le S) (observable T) (observable S) hs
  rw [observable_prediction S T hST,inner_self_eq_norm_sq_to_K] at hi
  have hr := congrArg (RCLike.re (K := ℂ)) hi
  rw [RCLike.re_ofReal_pow,observable_energy] at hr
  change inner ℝ (realPart (gaussianProduct.prod gaussianProduct) (observable T))
      (realPart (gaussianProduct.prod gaussianProduct) (observable S))+
    inner ℝ (imagPart (gaussianProduct.prod gaussianProduct) (observable T))
      (imagPart (gaussianProduct.prod gaussianProduct) (observable S))=_
  rw [← complex_inner_re]
  rw [combine_parts]
  exact hr.symm

attribute [local irreducible] sourceDerivative integralX integralY causalX causalY horizonDirection
  componentStep realCurve imagCurve observable

private theorem pair_RX (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    inner ℝ (realCurve T) (integralX T (componentStep T s t hst htT false))=
      ((t:ℝ)-s)*inner ℝ (realCurve T) (realCurve s) := by
  have hg : (realCurve T,directionField (horizonDirection T) (realCurve T))
      ∈ sourceDerivative.graph := by
    simpa only [realCurve,observable_eq] using
      (StochasticCauchyExponential.exponential_graphs (horizonDirection T)).1
  simpa only [componentStep,Bool.false_eq_true,ite_false,horizon_inner T s t hst htT,← realCurve_tensor] using
    step_ibp_X T s t hst htT (horizonDirection T) (realCurve T) (realCurve T) hg
      (expClass s) (cosClass s) (expClass_past s) (cosClass_past s)

private theorem pair_RY (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    inner ℝ (realCurve T) (integralY T (componentStep T s t hst htT true))=
      -(((t:ℝ)-s)*inner ℝ (imagCurve T) (imagCurve s)) := by
  have hg : (swap gaussianProduct gaussianProduct (realCurve T),
      directionField (horizonDirection T) (swap gaussianProduct gaussianProduct (-imagCurve T)))
      ∈ sourceDerivative.graph := by
    simpa only [realCurve,imagCurve,observable_eq,map_neg] using
      (StochasticCauchyExponential.exponential_graphs (horizonDirection T)).2.1
  simpa only [componentStep,ite_true,horizon_inner T s t hst htT,← imagCurve_tensor,
    inner_neg_left,mul_neg] using
    step_ibp_Y T s t hst htT (horizonDirection T) (realCurve T) (-imagCurve T) hg
      (expClass s) (sinClass s) (expClass_past s) (sinClass_past s)

private theorem pair_JX (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    inner ℝ (imagCurve T) (integralX T (componentStep T s t hst htT true))=
      ((t:ℝ)-s)*inner ℝ (imagCurve T) (imagCurve s) := by
  have hg : (imagCurve T,directionField (horizonDirection T) (imagCurve T))
      ∈ sourceDerivative.graph := by
    simpa only [imagCurve,observable_eq] using
      (StochasticCauchyExponential.exponential_graphs (horizonDirection T)).2.2.1
  simpa only [componentStep,ite_true,horizon_inner T s t hst htT,← imagCurve_tensor] using
    step_ibp_X T s t hst htT (horizonDirection T) (imagCurve T) (imagCurve T) hg
      (expClass s) (sinClass s) (expClass_past s) (sinClass_past s)

private theorem pair_JY (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    inner ℝ (imagCurve T) (integralY T (componentStep T s t hst htT false))=
      ((t:ℝ)-s)*inner ℝ (realCurve T) (realCurve s) := by
  have hg : (swap gaussianProduct gaussianProduct (imagCurve T),
      directionField (horizonDirection T) (swap gaussianProduct gaussianProduct (realCurve T)))
      ∈ sourceDerivative.graph := by
    simpa only [realCurve,imagCurve,observable_eq] using
      (StochasticCauchyExponential.exponential_graphs (horizonDirection T)).2.2.2
  simpa only [componentStep,Bool.false_eq_true,ite_false,horizon_inner T s t hst htT,← realCurve_tensor] using
    step_ibp_Y T s t hst htT (horizonDirection T) (imagCurve T) (realCurve T) hg
      (expClass s) (cosClass s) (expClass_past s) (cosClass_past s)

private theorem centered_channel_pairing (T : ℝ≥0) (F : JointComplex) (u : ComplexInput T) :
    inner ℂ (complexCenter F) (channel T false u)=inner ℂ F (channel T false u) := by
  rw [complexCenter_apply,inner_sub_left,inner_smul_left,complexOne_inner,
    channel_centered,mul_zero,sub_zero]

/-- The missing mixed pairing, on an actual chronological stochastic step. -/
theorem finite_step_mixed (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    (inner ℂ (complexCenter (observable T)) (channel T false
      (((Real.sqrt 2:ℝ):ℂ) • combineInput T (componentStep T s t hst htT false)
        (componentStep T s t hst htT true)))).re=
      2*((t:ℝ)-s)*Real.exp (2*(s:ℝ)) := by
  rw [centered_channel_pairing,normalized_channel_combine,complex_inner_re]
  rw [← realCurve,← imagCurve]
  rw [inner_sub_right,inner_add_right]
  rw [pair_RX T s t hst htT,pair_RY T s t hst htT,
    pair_JX T s t hst htT,pair_JY T s t hst htT]
  calc
    _=2*((t:ℝ)-s)*(inner ℝ (realCurve T) (realCurve s)+
      inner ℝ (imagCurve T) (imagCurve s)) := by ring
    _=_ := by rw [past_energy_pairing s T (hst.trans htT)]

private theorem combineInput_sum (T : ℝ≥0) {I : Type*} [Fintype I] (a b : I → Input T) :
    combineInput T (∑ i,a i) (∑ i,b i)=∑ i,combineInput T (a i) (b i) := by
  apply Subtype.ext
  simp only [combineInput,Submodule.coe_sum,combine,map_sum,Finset.smul_sum,Finset.sum_add_distrib]

private def grid (T : ℝ≥0) (N : ℕ) (i : Fin (N+1)) (b : Bool) : Input T :=
  componentStep T (uniformTime T N i.castSucc) (uniformTime T N i.succ)
    (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    (by simpa only [(uniformTime_endpoints T N).2] using
      uniformTime_monotone T N (Fin.le_last i.succ)) b

private theorem normalizedSteps_sum (T : ℝ≥0) (N : ℕ) :
    normalizedSteps T N=∑ i : Fin (N+1),
      ((Real.sqrt 2:ℝ):ℂ) • combineInput T (grid T N i false) (grid T N i true) := by
  have he (b : Bool) : componentSteps T N b=∑ i,grid T N i b := rfl
  rw [normalizedSteps,he false,he true,combineInput_sum,Finset.smul_sum]

def leftEnergySum (T : ℝ≥0) (N : ℕ) : ℝ := ∑ i : Fin (N+1),
  2*((uniformTime T N i.succ:ℝ)-uniformTime T N i.castSucc)*
    Real.exp (2*(uniformTime T N i.castSucc:ℝ))

theorem chronological_mixed (T : ℝ≥0) (N : ℕ) :
    (inner ℂ (complexCenter (observable T)) (channel T false (normalizedSteps T N))).re=
      leftEnergySum T N := by
  rw [normalizedSteps_sum,map_sum,inner_sum]
  change Complex.reCLM (∑ i : Fin (N+1), inner ℂ (complexCenter (observable T))
    (channel T false (((Real.sqrt 2:ℝ):ℂ) • combineInput T (grid T N i false)
      (grid T N i true))))=_
  rw [map_sum]
  unfold leftEnergySum
  apply Finset.sum_congr rfl
  intro i _
  exact finite_step_mixed T _ _ _ _

private theorem normalized_norm_parts (T : ℝ≥0) :
    ‖normalizedInput T‖^2=2*(‖componentInput T false‖^2+‖componentInput T true‖^2) := by
  rw [normalizedInput,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (by norm_num : (0:ℝ)≤2),input_norm_sq,realInput_combine,imagInput_combine]

/-- The old deterministic left-grid theorem is instantiated on a genuine
one-source constant Gaussian curve, then tested by its bounded mean functional. -/
theorem leftEnergySum_tendsto (T : ℝ≥0) :
    Tendsto (leftEnergySum T) atTop (𝓝 (Real.exp (2*(T:ℝ))-1)) := by
  let v : ℝ≥0 → GaussianL2 := fun t => (2*Real.exp (2*(t:ℝ))) • gaussianOne
  have hv : Continuous v := by fun_prop
  let L : GaussianL2 →L[ℝ] ℝ := innerSL ℝ gaussianOne
  have hs (N : ℕ) : L (∑ i : Fin (N+1),
      ((uniformTime T N i.succ:ℝ)-uniformTime T N i.castSucc) •
        v (uniformTime T N i.castSucc))=leftEnergySum T N := by
    rw [map_sum]
    unfold leftEnergySum
    apply Finset.sum_congr rfl
    intro i _
    change inner ℝ gaussianOne (_ • ((2*Real.exp _) • gaussianOne))=_
    rw [inner_smul_right,inner_smul_right,GaussianDeterministicGraphCore.gaussianOne_inner_self]
    ring
  have hi : IntervalIntegrable (fun r : ℝ => v r.toNNReal) volume 0 T :=
    (hv.comp continuous_real_toNNReal).intervalIntegrable _ _
  have hl : L (∫ r in (0:ℝ)..(T:ℝ),v r.toNNReal)=‖normalizedInput T‖^2 := by
    rw [← L.intervalIntegral_comp_comm hi]
    have he : (fun r : ℝ => L (v r.toNNReal))=
        fun r => 2*Real.exp (2*(r.toNNReal:ℝ)) := by
      funext r
      change inner ℝ gaussianOne ((2*Real.exp _) • gaussianOne)=_
      rw [inner_smul_right,GaussianDeterministicGraphCore.gaussianOne_inner_self,mul_one]
    rw [he,intervalIntegral.integral_of_le T.coe_nonneg,integral_const_mul]
    change 2*(∫ r,Real.exp (2*(r.toNNReal:ℝ)) ∂timeLaw T)=_
    rw [← componentInput_energy,← normalized_norm_parts]
  have ht := L.continuous.continuousAt.tendsto.comp
    (GaussianContinuousIntegrands.drift_sum_tendsto v hv T)
  simpa only [Function.comp_def,hs,hl,normalizedInput_energy] using ht

theorem mixed_pairing (T : ℝ≥0) :
    (inner ℂ (complexCenter (observable T)) (channel T false (normalizedInput T))).re=
      Real.exp (2*(T:ℝ))-1 := by
  have ht := ((innerSL ℂ (complexCenter (observable T))).continuous.tendsto _).comp
    (normalized_integrals_tendsto T)
  have hr := (Complex.continuous_re.tendsto
    (inner ℂ (complexCenter (observable T)) (channel T false (normalizedInput T)))).comp ht
  change Tendsto (fun N => (inner ℂ (complexCenter (observable T))
    (channel T false (normalizedSteps T N))).re) atTop
      (𝓝 (inner ℂ (complexCenter (observable T)) (channel T false (normalizedInput T))).re) at hr
  simp only [chronological_mixed] at hr
  exact tendsto_nhds_unique hr (leftEnergySum_tendsto T)

/-- Genuine stochastic reconstruction with the actual running native input. -/
theorem exponential_reconstruction (T : ℝ≥0) :
    channel T false (normalizedInput T)=complexCenter (observable T) := by
  have hk : ‖complexCenter (observable T)‖^2=Real.exp (2*(T:ℝ))-1 := by
    rw [observable_eq]
    simpa only [horizonDirection] using StochasticCauchyExponential.terminal_exponential_energy T
  have hi : ‖channel T false (normalizedInput T)‖^2=Real.exp (2*(T:ℝ))-1 := by
    rw [(channel T false).norm_map,normalizedInput_energy]
  have he : ‖complexCenter (observable T)-channel T false (normalizedInput T)‖^2=0 := by
    rw [@norm_sub_sq ℂ]
    change ‖complexCenter (observable T)‖^2-
      2*(inner ℂ (complexCenter (observable T)) (channel T false (normalizedInput T))).re+
        ‖channel T false (normalizedInput T)‖^2=0
    rw [hk,hi,mixed_pairing]
    ring
  have hz : ‖complexCenter (observable T)-channel T false (normalizedInput T)‖=0 := by
    nlinarith [norm_nonneg (complexCenter (observable T)-channel T false (normalizedInput T))]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem exponential_reconstruction_ae (T : ℝ≥0) :
    channel T false (normalizedInput T) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => Complex.exp ((process T w.1:ℂ)+Complex.I*(process T w.2:ℂ))-1 := by
  rw [exponential_reconstruction]
  have hm : (∫ w,observable T w ∂gaussianProduct.prod gaussianProduct)=1 := by
    rw [observable_eq]
    exact StochasticCauchyExponential.exponential_mean (horizonDirection T)
  have hc := complexCenter_ae (observable T)
  rw [hm] at hc
  filter_upwards [hc,observable_ae T] with w hc ho
  rw [hc,ho]
  rfl

/-- The actual temporal input is the canonical adjoint input, not just a
different same-energy representer. -/
theorem canonical_identification (T : ℝ≥0) :
    normalizedInput T=channelAdjoint T false (observable T) := by
  have he := congrArg (channelAdjoint T false) (exponential_reconstruction T)
  rw [channelAdjoint_self,channelAdjoint_center] at he
  exact he

private theorem stepX_ae (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    integralX T (stepInput T s t hst htT A B hA hB) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => (A w.1*B w.2)*(process t w.1-process s w.1) := by
  rw [integralX_stepInput]
  have hp := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (GaussianPastStepCompletion.pastIncrement_coeFn s t hst A hA)
  filter_upwards [hp,productTensor_coeFn gaussianProduct gaussianProduct
    (GaussianPastStepCompletion.pastIncrement s t hst A hA) B] with w hp ht
  simp only [Function.comp_apply] at hp
  rw [ht,hp]
  simp only [smul_eq_mul]
  ring

private theorem stepY_ae (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    integralY T (stepInput T s t hst htT A B hA hB) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => (A w.1*B w.2)*(process t w.2-process s w.2) := by
  rw [integralY_stepInput]
  have hp := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (GaussianPastStepCompletion.pastIncrement_coeFn s t hst B hB)
  filter_upwards [hp,productTensor_coeFn gaussianProduct gaussianProduct A
    (GaussianPastStepCompletion.pastIncrement s t hst B hB)] with w hp ht
  simp only [Function.comp_apply] at hp
  rw [ht,hp]
  simp only [smul_eq_mul]
  ring

private theorem coefficient_ae (s : ℝ≥0) (b : Bool) :
    (fun w : SampleSpace × SampleSpace => expClass s w.1*
      (if b then sinClass s else cosClass s) w.2) =ᵐ[gaussianProduct.prod gaussianProduct]
        componentValue b s := by
  have he := component_ae b s
  have ht : component b s=productTensor gaussianProduct gaussianProduct (expClass s)
      (if b then sinClass s else cosClass s) := by
    cases b
    · simpa only [component,Bool.false_eq_true,ite_false] using realCurve_tensor s
    · simpa only [component,ite_true] using imagCurve_tensor s
  rw [ht] at he
  have hp := productTensor_coeFn gaussianProduct gaussianProduct (expClass s)
    (if b then sinClass s else cosClass s)
  simp only [smul_eq_mul] at hp
  exact hp.symm.trans he

private theorem componentX_ae (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (b : Bool) :
    integralX T (componentStep T s t hst htT b) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => componentValue b s w*(process t w.1-process s w.1) := by
  have he := stepX_ae T s t hst htT (expClass s) (if b then sinClass s else cosClass s)
    (expClass_past s) (by cases b <;> first | exact cosClass_past _ | exact sinClass_past _)
  have hc := coefficient_ae s b
  rw [componentStep]
  filter_upwards [he,hc] with w he hc
  rw [he,hc]

private theorem componentY_ae (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (b : Bool) :
    integralY T (componentStep T s t hst htT b) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => componentValue b s w*(process t w.2-process s w.2) := by
  have he := stepY_ae T s t hst htT (expClass s) (if b then sinClass s else cosClass s)
    (expClass_past s) (by cases b <;> first | exact cosClass_past _ | exact sinClass_past _)
  have hc := coefficient_ae s b
  rw [componentStep]
  filter_upwards [he,hc] with w he hc
  rw [he,hc]

/-- Agreement with the actual complex left-step stochastic product. -/
theorem finite_step_ae (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • combineInput T
      (componentStep T s t hst htT false) (componentStep T s t hst htT true))
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w => value s w*
        (((process t w.1-process s w.1):ℝ):ℂ)+value s w*
          (Complex.I*(((process t w.2-process s w.2):ℝ):ℂ)) := by
  rw [normalized_channel_combine]
  filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct) _ _,
    Lp.coeFn_sub (integralX T (componentStep T s t hst htT false))
      (integralY T (componentStep T s t hst htT true)),
    Lp.coeFn_add (integralX T (componentStep T s t hst htT true))
      (integralY T (componentStep T s t hst htT false)),
    componentX_ae T s t hst htT false,componentY_ae T s t hst htT true,
    componentX_ae T s t hst htT true,componentY_ae T s t hst htT false]
      with w hc hd ha hxr hyj hxj hyr
  rw [hc,hd,ha]
  simp only [Pi.sub_apply,Pi.add_apply]
  rw [hxr,hyj,hxj,hyr]
  apply Complex.ext <;> simp [componentValue,Complex.mul_re,Complex.mul_im] <;> ring

theorem chronological_reconstruction (T : ℝ≥0) :
    Tendsto (fun N => channel T false (normalizedSteps T N)) atTop
      (𝓝 (complexCenter (observable T))) := by
  simpa only [exponential_reconstruction] using normalized_integrals_tendsto T

def riemannSum (T : ℝ≥0) (N : ℕ) (w : SampleSpace × SampleSpace) : ℂ :=
  ∑ i : Fin (N+1), value (uniformTime T N i.castSucc) w*
    ((((process (uniformTime T N i.succ) w.1-process (uniformTime T N i.castSucc) w.1):ℝ):ℂ)+
      Complex.I*(((process (uniformTime T N i.succ) w.2-process (uniformTime T N i.castSucc) w.2):ℝ):ℂ))

theorem chronological_ae (T : ℝ≥0) (N : ℕ) :
    channel T false (normalizedSteps T N) =ᵐ[gaussianProduct.prod gaussianProduct] riemannSum T N := by
  rw [normalizedSteps_sum,map_sum]
  have he (i : Fin (N+1)) :
      channel T false (((Real.sqrt 2:ℝ):ℂ) • combineInput T (grid T N i false) (grid T N i true))
        =ᵐ[gaussianProduct.prod gaussianProduct] fun w => value (uniformTime T N i.castSucc) w*
          ((((process (uniformTime T N i.succ) w.1-process (uniformTime T N i.castSucc) w.1):ℝ):ℂ)+
            Complex.I*(((process (uniformTime T N i.succ) w.2-process (uniformTime T N i.castSucc) w.2):ℝ):ℂ)) := by
    simpa only [grid,mul_add] using finite_step_ae T _ _
      (uniformTime_monotone T N (Fin.castSucc_le_succ i))
      (by simpa only [(uniformTime_endpoints T N).2] using
        uniformTime_monotone T N (Fin.le_last i.succ))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (N+1) => channel T false
    (((Real.sqrt 2:ℝ):ℂ) • combineInput T (grid T N i false) (grid T N i true))),
    ae_all_iff.mpr he] with w hs he
  rw [hs]
  simp only [Finset.sum_apply,riemannSum]
  exact Finset.sum_congr rfl (fun i _ => he i)

theorem riemannSum_memLp (T : ℝ≥0) (N : ℕ) :
    MemLp (riemannSum T N) 2 (gaussianProduct.prod gaussianProduct) :=
  (Lp.memLp (channel T false (normalizedSteps T N))).ae_eq (chronological_ae T N)

/-- Actual process sums converge in mean square, for every fixed horizon.
This is not a claim of almost-sure convergence of the whole grid sequence. -/
theorem mean_square_reconstruction (T : ℝ≥0) :
    Tendsto (fun N => ∫ w,‖riemannSum T N w-(value T w-1)‖^2
      ∂gaussianProduct.prod gaussianProduct) atTop (𝓝 0) := by
  have hk : complexCenter (observable T) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => value T w-1 := by
    rw [← exponential_reconstruction]
    exact exponential_reconstruction_ae T
  have he (N : ℕ) : ‖channel T false (normalizedSteps T N)-complexCenter (observable T)‖^2=
      ∫ w,‖riemannSum T N w-(value T w-1)‖^2 ∂gaussianProduct.prod gaussianProduct := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (channel T false (normalizedSteps T N))
      (complexCenter (observable T)),chronological_ae T N,hk] with w hd hs hk
    simp only [Pi.sub_apply] at hd
    rw [hd,hs,hk]
  have ht := ((chronological_reconstruction T).sub
    (tendsto_const_nhds (x := complexCenter (observable T)))).norm.pow 2
  simpa only [he,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using ht

end OperatorDerivativeRewrite.Foundation.StochasticCauchyExponentialReconstruction
