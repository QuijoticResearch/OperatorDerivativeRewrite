import Foundation.StochasticCauchyPolynomials

/-! True complex means, constant annihilation, and the raw observed-past
Cauchy decomposition on the actual two-source Brownian model. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyMeanResidual
open InfiniteGaussian ProductL2Curry ComplexL2Isometry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyMalliavinBridge StochasticCauchyPastReconstruction
open StochasticCauchyComplexChannels StochasticCauchyPolynomials
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete GaussianTimeHilbert.timeHilbert_secondCountable

def complexOne : JointComplex := combine (gaussianProduct.prod gaussianProduct) jointOne 0

theorem complexOne_ae : complexOne =ᵐ[gaussianProduct.prod gaussianProduct] fun _ => (1:ℂ) := by
  filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct) jointOne 0,jointOne_ae,
    Lp.coeFn_zero ℝ 2 (gaussianProduct.prod gaussianProduct)] with w hc h1 hz
  change complexOne w=_ at hc
  change (0:JointL2) w=0 at hz
  simp only [h1,hz,Complex.ofReal_one,Complex.ofReal_zero,mul_zero,add_zero] at hc
  exact hc

theorem complexOne_inner (H : JointComplex) :
    inner ℂ complexOne H=∫ w,H w ∂gaussianProduct.prod gaussianProduct := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [complexOne_ae] with w hw
  simp [hw,RCLike.inner_apply]

def complexCenter : JointComplex →L[ℂ] JointComplex :=
  ContinuousLinearMap.id ℂ JointComplex-
    (ContinuousLinearMap.toSpanSingleton ℂ complexOne).comp (innerSL ℂ complexOne)

theorem complexCenter_apply (H : JointComplex) :
    complexCenter H=H-(∫ w,H w ∂gaussianProduct.prod gaussianProduct) • complexOne := by
  change H-inner ℂ complexOne H • complexOne=_
  rw [complexOne_inner]

theorem complexCenter_ae (H : JointComplex) :
    complexCenter H =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      H w-∫ x,H x ∂gaussianProduct.prod gaussianProduct := by
  rw [complexCenter_apply]
  filter_upwards [Lp.coeFn_sub H ((∫ x,H x ∂gaussianProduct.prod gaussianProduct) • complexOne),
    Lp.coeFn_smul (∫ x,H x ∂gaussianProduct.prod gaussianProduct) complexOne,complexOne_ae] with w hd hs h1
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hd hs
  rw [hd,hs,h1,mul_one]

theorem complexCenter_combine (F G : JointL2) :
    complexCenter (combine (gaussianProduct.prod gaussianProduct) F G)=
      combine (gaussianProduct.prod gaussianProduct) (center F) (center G) := by
  apply Lp.ext
  exact (complexCenter_ae _).trans (centered_combine_ae F G).symm

private theorem integral_combine (F G : JointL2) :
    ∫ w,combine (gaussianProduct.prod gaussianProduct) F G w ∂gaussianProduct.prod gaussianProduct=
      (∫ w,F w ∂gaussianProduct.prod gaussianProduct:ℝ)+Complex.I*(∫ w,G w ∂gaussianProduct.prod gaussianProduct:ℝ) := by
  have hf : Integrable (fun w => (F w:ℂ)) (gaussianProduct.prod gaussianProduct) :=
    Complex.ofRealCLM.integrable_comp ((Lp.memLp F).integrable (by norm_num))
  have hg : Integrable (fun w => (G w:ℂ)) (gaussianProduct.prod gaussianProduct) :=
    Complex.ofRealCLM.integrable_comp ((Lp.memLp G).integrable (by norm_num))
  rw [integral_congr_ae (combine_ae _ F G),integral_add hf (hg.const_mul Complex.I),
    integral_const_mul,integral_complex_ofReal,integral_complex_ofReal]

private theorem real_sources_centered (T : ℝ≥0) (u : Input T) :
    (∫ w,integralX T u w ∂gaussianProduct.prod gaussianProduct)=0 ∧
    (∫ w,integralY T u w ∂gaussianProduct.prod gaussianProduct)=0 := by
  have hx := HilbertRepresentation.predictableAdjoint_pairing (integralX T) jointOne u
  have hy := HilbertRepresentation.predictableAdjoint_pairing (integralY T) jointOne u
  change inner ℝ (adjointX T jointOne) u=_ at hx
  change inner ℝ (adjointY T jointOne) u=_ at hy
  rw [(adjoints_one T).1,inner_zero_left,jointOne_inner] at hx
  rw [(adjoints_one T).2,inner_zero_left,jointOne_inner] at hy
  exact ⟨hx.symm,hy.symm⟩

private theorem complex_sources_centered (T : ℝ≥0) (u : ComplexInput T) :
    (∫ w,integralXComplex T u w ∂gaussianProduct.prod gaussianProduct)=0 ∧
    (∫ w,integralYComplex T u w ∂gaussianProduct.prod gaussianProduct)=0 := by
  unfold integralXComplex integralYComplex
  rw [liftInput_apply,liftInput_apply,integral_combine,integral_combine,
    (real_sources_centered T (realInput T u)).1,(real_sources_centered T (imagInput T u)).1,
    (real_sources_centered T (realInput T u)).2,(real_sources_centered T (imagInput T u)).2]
  simp

/-- Every actual normalized channel integral has true complex mean zero. -/
theorem channel_centered (T : ℝ≥0) (b : Bool) (u : ComplexInput T) :
    (∫ w,channel T b u w ∂gaussianProduct.prod gaussianProduct)=0 := by
  rw [← complexOne_inner]
  change inner ℂ complexOne ((((Real.sqrt 2)⁻¹:ℝ):ℂ) •
    (integralXComplex T u+(if b then -Complex.I else Complex.I) • integralYComplex T u))=0
  rw [inner_smul_right,inner_add_right,inner_smul_right,complexOne_inner,complexOne_inner,
    (complex_sources_centered T u).1,(complex_sources_centered T u).2]
  simp

theorem channelAdjoint_one (T : ℝ≥0) (b : Bool) : channelAdjoint T b complexOne=0 := by
  apply ext_inner_right ℂ
  intro u
  rw [channelAdjoint_pairing,inner_zero_left,complexOne_inner,channel_centered]

theorem channelAdjoint_center (T : ℝ≥0) (b : Bool) (H : JointComplex) :
    channelAdjoint T b (complexCenter H)=channelAdjoint T b H := by
  rw [complexCenter_apply,map_sub,map_smul,channelAdjoint_one,smul_zero,sub_zero]

theorem cauchyProjection_center (T : ℝ≥0) (b : Bool) (H : JointComplex) :
    cauchyProjection T b (complexCenter H)=cauchyProjection T b H := by
  rw [cauchyProjection_apply,cauchyProjection_apply,channelAdjoint_center]

theorem cauchyProjection_one (T : ℝ≥0) (b : Bool) : cauchyProjection T b complexOne=0 := by
  rw [cauchyProjection_apply,channelAdjoint_one,map_zero]

theorem residual_one (T : ℝ≥0) : residual T complexOne=complexOne := by
  change complexOne-cauchyProjection T false complexOne-cauchyProjection T true complexOne=complexOne
  rw [cauchyProjection_one,cauchyProjection_one,sub_zero,sub_zero]

/-- On the ACTUAL observed joint past the raw residual is exactly the true mean.
No claim is made for targets with future dependence. -/
theorem joint_past_residual (T : ℝ≥0) (F G : JointL2)
    (hF : F ∈ jointPastL2 T) (hG : G ∈ jointPastL2 T) :
    residual T (combine (gaussianProduct.prod gaussianProduct) F G)=
      (∫ w,combine (gaussianProduct.prod gaussianProduct) F G w ∂gaussianProduct.prod gaussianProduct) • complexOne := by
  have hz := complex_joint_past_reconstruction T F G hF hG
  rw [← complexCenter_combine,complexCenter_apply,map_sub,map_smul,residual_one] at hz
  exact sub_eq_zero.mp hz

/-- The raw two-channel projection sum is actual mean subtraction. -/
theorem joint_past_raw_formula (T : ℝ≥0) (F G : JointL2)
    (hF : F ∈ jointPastL2 T) (hG : G ∈ jointPastL2 T) :
    cauchyProjection T false (combine (gaussianProduct.prod gaussianProduct) F G)+
      cauchyProjection T true (combine (gaussianProduct.prod gaussianProduct) F G)=
      complexCenter (combine (gaussianProduct.prod gaussianProduct) F G) := by
  have he := complex_joint_past_formula T F G hF hG
  rw [← complexCenter_combine,cauchyProjection_center,cauchyProjection_center] at he
  exact he

/-- Both projections act on the RAW polynomial, with the exact actual mean. -/
theorem polynomial_raw_projections (T : ℝ≥0) (h : CoefficientSpace) (p : Polynomial ℂ)
    (ha : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] (firstChaosEmbedding h) gaussianProduct) :
    cauchyProjection T false (polynomialValue h p)=complexCenter (polynomialValue h p) ∧
    cauchyProjection T true (polynomialValue h p)=0 := by
  have he := polynomial_projections T h p ha
  rw [← complexCenter_combine,cauchyProjection_center,cauchyProjection_center] at he
  exact he

theorem terminal_raw_projections (T : ℝ≥0) (p : Polynomial ℂ) :
    let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector T)
    cauchyProjection T false (polynomialValue h p)=complexCenter (polynomialValue h p) ∧
    cauchyProjection T true (polynomialValue h p)=0 := by
  dsimp only
  exact polynomial_raw_projections T _ p (GaussianTimeProcess.process_stronglyAdapted T).aestronglyMeasurable

/-- The source's forward Cauchy identity, on actual arbitrary Brownian terminal
polynomials, not merely on an already centered or abstract target. -/
theorem terminal_raw_cauchy_ae (T : ℝ≥0) (p : Polynomial ℂ) :
    let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector T)
    cauchyProjection T false (polynomialValue h p) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => p.eval ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))-
        ∫ x,p.eval ((GaussianTimeProcess.process T x.1:ℂ)+Complex.I*(GaussianTimeProcess.process T x.2:ℂ)) ∂gaussianProduct.prod gaussianProduct := by
  dsimp only
  rw [(terminal_raw_projections T p).1]
  rw [polynomialValue,complexCenter_combine]
  exact centered_polynomial_ae _ p

end OperatorDerivativeRewrite.Foundation.StochasticCauchyMeanResidual
