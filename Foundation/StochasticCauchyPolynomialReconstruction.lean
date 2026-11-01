import Foundation.StochasticCauchyPolynomialInput
import Foundation.StochasticCauchyExponentialReconstruction
import Foundation.StochasticCauchyGaussianStein
/-! Canonical running-polynomial reconstruction on the original two-source
Brownian native domain. Prediction is on the full raw joint past; convergence
is strong L2, and physical coefficients have AE-time/AE-source quantifiers. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialReconstruction
open InfiniteGaussian ProductL2Curry ComplexL2Isometry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPhysicalInput StochasticCauchyExponentialInput
open StochasticCauchyPolynomialInput StochasticCauchyPolynomialPrediction
open StochasticCauchyPastReconstruction StochasticCauchyMalliavinBridge
open StochasticCauchyCausalRotation StochasticCauchyExponentialReconstruction
open StochasticCauchyComplexChannels GaussianTimeProcess
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete

theorem valuePart_projection (S T : ℝ≥0) (hST : S ≤ T) (p : Polynomial ℂ) (b : Bool) :
    (condExpL2 ℝ ℝ (jointPast_le S) (valuePart p b T) : JointL2) = valuePart p b S := by
  cases b
  · have hc := condExpL2_comp_continuousLinearMap ℂ ℝ (jointPast_le S)
      Complex.reCLM (polynomialClass T p)
    rw [polynomialClass_prediction S T hST p] at hc
    have hT : Complex.reCLM.compLp (polynomialClass T p) = valuePart p false T :=
      realPart_combine _ _ _
    have hS : Complex.reCLM.compLp (polynomialClass S p) = valuePart p false S :=
      realPart_combine _ _ _
    rw [hT,hS] at hc
    exact Lp.ext hc
  · have hc := condExpL2_comp_continuousLinearMap ℂ ℝ (jointPast_le S)
      Complex.imCLM (polynomialClass T p)
    rw [polynomialClass_prediction S T hST p] at hc
    have hT : Complex.imCLM.compLp (polynomialClass T p) = valuePart p true T :=
      imagPart_combine _ _ _
    have hS : Complex.imCLM.compLp (polynomialClass S p) = valuePart p true S :=
      imagPart_combine _ _ _
    rw [hT,hS] at hc
    exact Lp.ext hc

theorem valuePart_past_pairing (S T : ℝ≥0) (hST : S ≤ T) (p : Polynomial ℂ) (b : Bool)
    (H : JointL2) (hH : AEStronglyMeasurable[jointPast S] H (gaussianProduct.prod gaussianProduct)) :
    inner ℝ (valuePart p b T) H = inner ℝ (valuePart p b S) H := by
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (jointPast_le S) (valuePart p b T) H hH
  rw [valuePart_projection S T hST p b] at hi
  exact hi.symm

theorem valuePart_past (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) :
    valuePart p b T ∈ jointPastL2 T := by
  rw [← valuePart_projection T T le_rfl p b]
  exact (condExpL2 ℝ ℝ (jointPast_le T) (valuePart p b T)).property

/-- Actual source/time sections determine the original native step pairing. -/
theorem running_step_pairing (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (v : ℝ≥0 → JointL2) (hv : Continuous v) (a : JointL2) (u : Input T)
    (hu : timeSections T (fieldEmbedding T u) = running v hv T)
    (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct)
    (hp : ∀ r ∈ Ioc (s:ℝ) (t:ℝ), inner ℝ (v r.toNNReal)
      (productTensor gaussianProduct gaussianProduct A B) =
        inner ℝ a (productTensor gaussianProduct gaussianProduct A B)) :
    inner ℝ u (stepInput T s t hst htT A B hA hB) =
      ((t:ℝ)-s)*inner ℝ a (productTensor gaussianProduct gaussianProduct A B) := by
  let J := (timeSections T).comp (fieldEmbedding T)
  rw [← J.inner_map_map]
  change inner ℝ (timeSections T (fieldEmbedding T u))
    (timeSections T (fieldEmbedding T (stepInput T s t hst htT A B hA hB))) = _
  rw [hu,L2.inner_def]
  have he : (fun r => inner ℝ (running v hv T r)
      (timeSections T (fieldEmbedding T (stepInput T s t hst htT A B hA hB)) r))
      =ᵐ[timeLaw T] (Ioc (s:ℝ) (t:ℝ)).indicator
        (fun _ => inner ℝ a (productTensor gaussianProduct gaussianProduct A B)) := by
    filter_upwards [running_ae v hv T,timeSections_step T s t hst htT A B hA hB]
      with r hvv hs
    rw [hvv,hs]
    by_cases hr : r ∈ Ioc (s:ℝ) (t:ℝ)
    · rw [indicator_of_mem hr,indicator_of_mem hr,hp r hr]
    · simp only [indicator_of_notMem hr,inner_zero_right]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioc]
  have hsub : Ioc (s:ℝ) (t:ℝ) ⊆ Ioc 0 (T:ℝ) := by
    intro r hr
    exact ⟨lt_of_le_of_lt s.coe_nonneg hr.1,le_trans hr.2 htT⟩
  rw [timeLaw,Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr hsub,
    integral_const,measureReal_restrict_apply_univ,Real.volume_real_Ioc,smul_eq_mul,
    max_eq_left (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst))]

theorem tensor_past (s : ℝ≥0) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    AEStronglyMeasurable[jointPast s] (productTensor gaussianProduct gaussianProduct A B)
      (gaussianProduct.prod gaussianProduct) := by
  have ha := hA.stronglyMeasurable_mk.comp_measurable
    (show @Measurable (SampleSpace × SampleSpace) SampleSpace
      (jointPast s) (naturalFiltration s) Prod.fst from measurable_fst)
  have hb := hB.stronglyMeasurable_mk.comp_measurable
    (show @Measurable (SampleSpace × SampleSpace) SampleSpace
      (jointPast s) (naturalFiltration s) Prod.snd from measurable_snd)
  apply (ha.mul hb).aestronglyMeasurable.congr
  filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct A B,
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp hA.ae_eq_mk,
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp hB.ae_eq_mk]
    with w ht ha hb
  change hA.mk A w.1*hB.mk B w.2 = productTensor gaussianProduct gaussianProduct A B w
  simp only [Function.comp_apply] at ha hb
  rw [← ha,← hb,ht]
  rfl

theorem partInput_step_pairing (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (p : Polynomial ℂ) (b : Bool) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    inner ℝ (partInput T p b) (stepInput T s t hst htT A B hA hB) =
      ((t:ℝ)-s)*inner ℝ (valuePart p b T) (productTensor gaussianProduct gaussianProduct A B) := by
  apply running_step_pairing T s t hst htT (valuePart p b) (valuePart_continuous p b)
    (valuePart p b T) (partInput T p b) (partInput_sections T p b) A B hA hB
  intro r hr
  have hsr : s ≤ r.toNNReal := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hr.1.le
  exact (valuePart_past_pairing s r.toNNReal hsr p b _ (tensor_past s A B hA hB)).trans
    (valuePart_past_pairing s T (hst.trans htT) p b _ (tensor_past s A B hA hB)).symm

attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime

/-- Density of the original generating steps; no larger predictable domain is assumed. -/
theorem native_ext_steps (T : ℝ≥0) (u v : Input T)
    (h : ∀ s t : ℝ≥0, ∀ hst : s ≤ t, ∀ htT : t ≤ T, ∀ A B : GaussianL2,
      ∀ hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct,
      ∀ hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct,
      inner ℝ u (stepInput T s t hst htT A B hA hB) =
        inner ℝ v (stepInput T s t hst htT A B hA hB)) : u = v := by
  apply ext_inner_right ℝ
  intro w
  refine (assemble_dense T).induction_on w ?_ (fun z => ?_)
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  have hz := z.property
  refine Submodule.span_induction (p := fun z hz =>
    inner ℝ u (assemble T ⟨z,hz⟩) = inner ℝ v (assemble T ⟨z,hz⟩)) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨s,t,A,B,hst,htT,hA,hB,rfl⟩
    exact h s t hst htT A B hA hB
  · simp [assemble]
  · intro z w hz hw iz iw
    change inner ℝ u (assemble T ⟨z,hz⟩+assemble T ⟨w,hw⟩) =
      inner ℝ v (assemble T ⟨z,hz⟩+assemble T ⟨w,hw⟩)
    rw [inner_add_right,inner_add_right,iz,iw]
  · intro c z hz iz
    change z ∈ relation T at hz
    change inner ℝ u (c • assemble T ⟨z,hz⟩) = inner ℝ v (c • assemble T ⟨z,hz⟩)
    exact ((innerSL ℝ u).map_smul c (assemble T ⟨z,hz⟩)).trans
      ((congrArg (c • ·) iz).trans ((innerSL ℝ v).map_smul c (assemble T ⟨z,hz⟩)).symm)

theorem partInput_causal (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) :
    partInput T p b = causalX T (directionField (timeDirection T) (valuePart p b T)) := by
  apply native_ext_steps
  intro s t hst htT A B hA hB
  have hh : inner ℝ (timeDirection T) (GaussianTimeDivergence.incrementDirection s t) = (t:ℝ)-s := by
    rw [real_inner_comm]
    exact GaussianTerminalBracketPrediction.increment_terminal_inner s t T hst htT
  rw [partInput_step_pairing,causal_step_pairing,hh]

open StochasticCauchyPolynomials StochasticCauchyAnalyticPowers

theorem slope_parts (T : ℝ≥0) (p : Polynomial ℂ) :
    realSlope (timeDirection T) p = valuePart p.derivative false T ∧
    imagSlope (timeDirection T) p = valuePart p.derivative true T := by
  have he : combine (gaussianProduct.prod gaussianProduct) (realSlope (timeDirection T) p)
      (imagSlope (timeDirection T) p) = polynomialClass T p.derivative :=
    Lp.ext ((slope_value_ae (timeDirection T) p).trans
      (polynomial_value_ae (timeDirection T) p.derivative).symm)
  constructor
  · have hr := congrArg (realPart (gaussianProduct.prod gaussianProduct)) he
    simpa only [realPart_combine,polynomialClass,polynomialValue,valuePart,ite_false,
      Bool.false_eq_true] using hr
  · have hr := congrArg (imagPart (gaussianProduct.prod gaussianProduct)) he
    simpa only [imagPart_combine,polynomialClass,polynomialValue,valuePart,ite_true] using hr

theorem slope_causal (T : ℝ≥0) (p : Polynomial ℂ) :
    causalX T (directionField (timeDirection T) (realSlope (timeDirection T) p)) = partInput T p.derivative false ∧
    causalX T (directionField (timeDirection T) (imagSlope (timeDirection T) p)) = partInput T p.derivative true := by
  constructor
  · rw [(slope_parts T p).1]
    exact (partInput_causal T p.derivative false).symm
  · rw [(slope_parts T p).2]
    exact (partInput_causal T p.derivative true).symm

private theorem combineInput_rotate (T : ℝ≥0) (a b : Input T) :
    combineInput T (-b) a = Complex.I • combineInput T a b := by
  apply Subtype.ext
  change combine (nativeMeasure T) (-b.val) a.val = Complex.I • combine (nativeMeasure T) a.val b.val
  simp only [combine,map_neg,smul_add,smul_smul,Complex.I_mul_I,neg_one_smul]
  abel

attribute [local irreducible] sourceDerivative directionField causalX causalY channel combineInput
  realPolynomial imagPolynomial realSlope imagSlope

private theorem twice_scale : channelScale*2 = ((Real.sqrt 2:ℝ):ℂ) := by
  have hr : (Real.sqrt 2)⁻¹*2 = Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_ne_zero'.mpr (show (0:ℝ) < 2 by norm_num)
    apply mul_left_cancel₀ hn
    calc
      Real.sqrt 2*((Real.sqrt 2)⁻¹*2) = 2 := by rw [← mul_assoc,mul_inv_cancel₀ hn,one_mul]
      _ = Real.sqrt 2*Real.sqrt 2 := by nlinarith
  unfold channelScale
  exact_mod_cast hr

private theorem native_CR_algebra (T : ℝ≥0) (a b r s : Input T) (K : JointComplex)
    (hr : r= -b) (hs : s=a)
    (he : channel T false (channelScale • (combineInput T a b-Complex.I • combineInput T r s)) +
      channel T true (channelScale • (combineInput T a b+Complex.I • combineInput T r s))=K) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • combineInput T a b)=K := by
  subst r
  subst s
  rw [combineInput_rotate,smul_smul,Complex.I_mul_I,neg_one_smul,
    add_neg_cancel,smul_zero,map_zero,add_zero] at he
  have hnorm (u : ComplexInput T) : channelScale • (u-(-u)) = ((Real.sqrt 2:ℝ):ℂ) • u := by
    rw [sub_neg_eq_add,← two_smul ℂ u,smul_smul,twice_scale]
  rw [hnorm] at he
  exact he

theorem analytic_native_reconstruction (T : ℝ≥0) (h : CoefficientSpace) (F G a b : JointL2)
    (hF : F ∈ jointPastL2 T) (hG : G ∈ jointPastL2 T)
    (hFX : (F,directionField h a) ∈ sourceDerivative.graph)
    (hFY : (swap gaussianProduct gaussianProduct F,
      -directionField h (swap gaussianProduct gaussianProduct b)) ∈ sourceDerivative.graph)
    (hGX : (G,directionField h b) ∈ sourceDerivative.graph)
    (hGY : (swap gaussianProduct gaussianProduct G,
      directionField h (swap gaussianProduct gaussianProduct a)) ∈ sourceDerivative.graph) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • combineInput T
      (causalX T (directionField h a)) (causalX T (directionField h b))) =
      combine (gaussianProduct.prod gaussianProduct) (center F) (center G) := by
  let p := causalX T (directionField h a)
  let q := causalX T (directionField h b)
  have hyb : causalY T (-directionField h (swap gaussianProduct gaussianProduct b))= -q := by
    rw [map_neg,causal_rotation]
  have hya : causalY T (directionField h (swap gaussianProduct gaussianProduct a))=p :=
    causal_rotation T h a
  have he := malliavin_complex_joint_past T F G hF hG
    (directionField h a) (-directionField h (swap gaussianProduct gaussianProduct b))
    (directionField h b) (directionField h (swap gaussianProduct gaussianProduct a)) hFX hFY hGX hGY
  exact native_CR_algebra T p q _ _ _ hyb hya he

attribute [local irreducible] StochasticCauchyPolynomialInput.normalizedInput polynomialClass

theorem polynomial_reconstruction (T : ℝ≥0) (p : Polynomial ℂ) :
    channel T false (StochasticCauchyPolynomialInput.normalizedInput T p) =
      StochasticCauchyMeanResidual.complexCenter (polynomialClass T p) := by
  have hr : realPolynomial (timeDirection T) p ∈ jointPastL2 T := valuePart_past T p false
  have hi : imagPolynomial (timeDirection T) p ∈ jointPastL2 T := valuePart_past T p true
  have hg := polynomial_graphs (timeDirection T) p
  have he := analytic_native_reconstruction T (timeDirection T)
    (realPolynomial (timeDirection T) p) (imagPolynomial (timeDirection T) p)
    (realSlope (timeDirection T) p) (imagSlope (timeDirection T) p)
    hr hi hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  rw [(slope_causal T p).1,(slope_causal T p).2] at he
  rw [StochasticCauchyPolynomialInput.normalizedInput,polynomialClass,polynomialValue,
    StochasticCauchyMeanResidual.complexCenter_combine]
  exact he

open StochasticCauchyMeanResidual

/-- Identification with the ORIGINAL canonical channel adjoint. -/
theorem canonical_identification (T : ℝ≥0) (p : Polynomial ℂ) :
    StochasticCauchyPolynomialInput.normalizedInput T p = channelAdjoint T false (polynomialClass T p) := by
  have he := congrArg (channelAdjoint T false) (polynomial_reconstruction T p)
  rw [channelAdjoint_self,channelAdjoint_center] at he
  exact he

/-- Actual Brownian stochastic identity, with deterministic initial value. -/
theorem polynomial_reconstruction_ae (T : ℝ≥0) (p : Polynomial ℂ) :
    channel T false (StochasticCauchyPolynomialInput.normalizedInput T p)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w => p.eval (position T w)-p.eval 0 := by
  rw [polynomial_reconstruction]
  have hm : (∫ w,polynomialClass T p w ∂gaussianProduct.prod gaussianProduct) = p.eval 0 := by
    rw [polynomialClass,integral_congr_ae (polynomial_value_ae (timeDirection T) p)]
    exact StochasticCauchyGaussianStein.polynomial_mean (timeDirection T) p
  have hc := complexCenter_ae (polynomialClass T p)
  rw [hm] at hc
  filter_upwards [hc,polynomialClass_ae T p] with w hc hp
  rw [hc,hp]

/-- Strong convergence through the ORIGINAL stochastic channel, now to the
actual centered terminal polynomial. No pathwise/AS convergence is asserted. -/
theorem chronological_reconstruction (T : ℝ≥0) (p : Polynomial ℂ) :
    Tendsto (fun N => channel T false (StochasticCauchyPolynomialInput.normalizedSteps T p N)) atTop
      (𝓝 (complexCenter (polynomialClass T p))) := by
  rw [← polynomial_reconstruction]
  exact normalized_integrals_tendsto T p

/-- Physical slices of the CANONICAL adjoint, AE in time and then source. -/
theorem canonical_slices (T : ℝ≥0) (p : Polynomial ℂ) :
    ∀ᵐ r ∂timeLaw T, ∀ᵐ w : SampleSpace × SampleSpace ∂gaussianProduct.prod gaussianProduct,
      (fieldEmbedding T (realInput T (channelAdjoint T false (polynomialClass T p))) ((r,w.1),w.2) : ℂ)+
        Complex.I*(fieldEmbedding T (imagInput T (channelAdjoint T false (polynomialClass T p))) ((r,w.1),w.2) : ℂ) =
        (Real.sqrt 2:ℂ)*p.derivative.eval (position r.toNNReal w) := by
  rw [← canonical_identification T p]
  exact normalizedInput_slices T p

end OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialReconstruction
