import Foundation.StochasticCauchyCovarianceObstruction
import Foundation.GaussianTimePolynomialPairing

/-! An actual synchronized Cauchy channel can contain a full-domain observable
whose genuine Gaussian directional derivatives violate Cauchy--Riemann. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyHolomorphicObstruction
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeDivergence
open GaussianTimePolynomialPairing GaussianTimeFieldNorm SeparableHilbertEmbedding
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels StochasticCauchyPastReconstruction StochasticCauchyMalliavinBridge
open ProductL2Curry ComplexL2Isometry
attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  GaussianProductDerivative.coefficientSpace_secondCountable timeHilbert_secondCountable

def earlyDirection : CoefficientSpace := hilbertEmbedding TimeHilbert (timeVector 1)
def lateDirection : CoefficientSpace := incrementDirection 1 2
def early : polynomialCylindricalDomain := firstChaosPolynomial earlyDirection
def late : polynomialCylindricalDomain := firstChaosPolynomial lateDirection
def quadratic : polynomialCylindricalDomain := polynomialProduct early late

private theorem directions_inner : inner ℝ earlyDirection lateDirection=0 :=
  pastDirection_inner_increment 1 1 2 le_rfl (by norm_num)
private theorem early_inner : inner ℝ earlyDirection earlyDirection=1 := by
  change inner ℝ (hilbertEmbedding TimeHilbert (timeVector 1)) (hilbertEmbedding TimeHilbert (timeVector 1))=1
  rw [(hilbertEmbedding TimeHilbert).inner_map_map,timeVector_inner]
  norm_num

/-- Actual contraction of the original coefficient-valued Gaussian derivative. -/
def contract : GaussianVectorL2 →L[ℝ] GaussianL2 := (innerSL ℝ earlyDirection).compLpL 2 gaussianProduct

/-- Return the contracted derivative to the ORIGINAL physical source order. -/
def physicalX : DerivativeField →L[ℝ] JointL2 :=
  sourceCurry.symm.toLinearIsometry.toContinuousLinearMap.comp (contract.compLpL 2 gaussianProduct)
def physicalY : DerivativeField →L[ℝ] JointL2 :=
  (swap gaussianProduct gaussianProduct).toContinuousLinearMap.comp physicalX

private theorem map_tensor (L : GaussianVectorL2 →L[ℝ] GaussianL2) (B : GaussianL2) (H : GaussianVectorL2) :
    L.compLpL 2 gaussianProduct (BochnerClosedOperator.tensor gaussianProduct B H)=
      BochnerClosedOperator.tensor gaussianProduct B (L H) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (BochnerClosedOperator.tensor gaussianProduct B H),
    BochnerClosedOperator.tensor_coeFn gaussianProduct B H,
    BochnerClosedOperator.tensor_coeFn gaussianProduct B (L H)] with w hm ht ho
  rw [hm,ht,ho,map_smul]

theorem physicalX_tensor (B : GaussianL2) (H : GaussianVectorL2) :
    physicalX (BochnerClosedOperator.tensor gaussianProduct B H)=
      productTensor gaussianProduct gaussianProduct (contract H) B := by
  change sourceCurry.symm (contract.compLpL 2 gaussianProduct (BochnerClosedOperator.tensor gaussianProduct B H))=_
  rw [map_tensor]
  apply sourceCurry.injective
  rw [sourceCurry.apply_symm_apply,sourceCurry_tensor]

theorem physicalY_tensor (B : GaussianL2) (H : GaussianVectorL2) :
    physicalY (BochnerClosedOperator.tensor gaussianProduct B H)=
      productTensor gaussianProduct gaussianProduct B (contract H) := by
  change swap gaussianProduct gaussianProduct (physicalX _)=_
  rw [physicalX_tensor,swap_productTensor]

private theorem contract_early : contract (polynomialDerivative early)=gaussianOne := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ earlyDirection).coeFn_compLpL (polynomialDerivative early),
    firstChaosPolynomial_derivative_coeFn earlyDirection,gaussianOne_coeFn] with w hc hd ho
  change contract (polynomialDerivative early) w=inner ℝ earlyDirection (polynomialDerivative early w) at hc
  change polynomialDerivative early w=earlyDirection at hd
  rw [hc,hd,early_inner,ho]

private theorem contract_late : contract (polynomialDerivative late)=0 := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ earlyDirection).coeFn_compLpL (polynomialDerivative late),
    firstChaosPolynomial_derivative_coeFn lateDirection,Lp.coeFn_zero ℝ 2 gaussianProduct] with w hc hd hz
  change contract (polynomialDerivative late) w=inner ℝ earlyDirection (polynomialDerivative late w) at hc
  change polynomialDerivative late w=lateDirection at hd
  rw [hc,hd,directions_inner,hz]
  rfl

private theorem contract_quadratic : contract (polynomialDerivative quadratic)=(late : GaussianL2) := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ earlyDirection).coeFn_compLpL (polynomialDerivative quadratic),
    polynomialDerivative_product_ae early late,firstChaosPolynomial_derivative_coeFn earlyDirection,
    firstChaosPolynomial_derivative_coeFn lateDirection] with w hc hq he hl
  change contract (polynomialDerivative quadratic) w=inner ℝ earlyDirection (polynomialDerivative quadratic w) at hc
  change polynomialDerivative early w=earlyDirection at he
  change polynomialDerivative late w=lateDirection at hl
  change polynomialDerivative quadratic w=(early : GaussianL2) w • polynomialDerivative late w +
    (late : GaussianL2) w • polynomialDerivative early w at hq
  rw [hc,hq,he,hl,inner_add_right,inner_smul_right,inner_smul_right,directions_inner,early_inner,
    mul_zero,mul_one,zero_add]

private theorem tensor_zero_left (F : GaussianL2) : productTensor gaussianProduct gaussianProduct (0 : GaussianL2) F=0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [tensor_inner]
  simp
private theorem tensor_zero_right (F : GaussianL2) : productTensor gaussianProduct gaussianProduct F (0 : GaussianL2)=0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [tensor_inner]
  simp

def realPartValue : JointL2 :=
  productTensor gaussianProduct gaussianProduct (quadratic : GaussianL2) gaussianOne +
    productTensor gaussianProduct gaussianProduct gaussianOne (quadratic : GaussianL2)
def imagPartValue : JointL2 :=
  productTensor gaussianProduct gaussianProduct (early : GaussianL2) (late : GaussianL2) -
    productTensor gaussianProduct gaussianProduct (late : GaussianL2) (early : GaussianL2)

def realGradient : DerivativeField :=
  BochnerClosedOperator.tensor gaussianProduct gaussianOne (polynomialDerivative quadratic) +
    BochnerClosedOperator.tensor gaussianProduct (quadratic : GaussianL2) (0 : GaussianVectorL2)
def imagGradientX : DerivativeField :=
  BochnerClosedOperator.tensor gaussianProduct (late : GaussianL2) (polynomialDerivative early) -
    BochnerClosedOperator.tensor gaussianProduct (early : GaussianL2) (polynomialDerivative late)
def imagGradientY : DerivativeField :=
  BochnerClosedOperator.tensor gaussianProduct (early : GaussianL2) (polynomialDerivative late) -
    BochnerClosedOperator.tensor gaussianProduct (late : GaussianL2) (polynomialDerivative early)

private theorem one_graph : (gaussianOne,(0 : GaussianVectorL2)) ∈ closedCylindricalDerivative.graph := by
  simpa only [one_smul] using closedDerivative_constant_graph 1

theorem real_graph : (realPartValue,realGradient) ∈ sourceDerivative.graph :=
  sourceDerivative.graph.add_mem
    (sourceDerivative_tensor _ _ _ (closedCylindricalDerivative_core_graph quadratic))
    (sourceDerivative_tensor _ _ _ one_graph)

theorem real_swapped_graph : (swap gaussianProduct gaussianProduct realPartValue,realGradient) ∈ sourceDerivative.graph := by
  have hs : swap gaussianProduct gaussianProduct realPartValue=realPartValue := by
    unfold realPartValue
    rw [map_add,swap_productTensor,swap_productTensor]
    abel
  rw [hs]
  exact real_graph

theorem imag_graph : (imagPartValue,imagGradientX) ∈ sourceDerivative.graph :=
  sourceDerivative.graph.sub_mem
    (sourceDerivative_tensor _ _ _ (closedCylindricalDerivative_core_graph early))
    (sourceDerivative_tensor _ _ _ (closedCylindricalDerivative_core_graph late))

theorem imag_swapped_graph : (swap gaussianProduct gaussianProduct imagPartValue,imagGradientY) ∈ sourceDerivative.graph := by
  unfold imagPartValue
  rw [map_sub,swap_productTensor,swap_productTensor]
  exact sourceDerivative.graph.sub_mem
    (sourceDerivative_tensor _ _ _ (closedCylindricalDerivative_core_graph late))
    (sourceDerivative_tensor _ _ _ (closedCylindricalDerivative_core_graph early))

theorem physical_real_gradient : physicalX realGradient=
    productTensor gaussianProduct gaussianProduct (late : GaussianL2) gaussianOne := by
  rw [realGradient,map_add,physicalX_tensor,physicalX_tensor,contract_quadratic,map_zero,tensor_zero_left,add_zero]

theorem physical_imag_gradient : physicalY imagGradientY=
    -productTensor gaussianProduct gaussianProduct (late : GaussianL2) gaussianOne := by
  rw [imagGradientY,map_sub,physicalY_tensor,physicalY_tensor,contract_late,contract_early,
    tensor_zero_right,zero_sub]

private theorem terminal_energy :
    ‖productTensor gaussianProduct gaussianProduct (late : GaussianL2) gaussianOne‖^2=1 := by
  have hl : (late : GaussianL2)=firstChaosEmbedding lateDirection := Lp.ext (firstChaosPolynomial_coeFn lateDirection)
  have ho : ‖gaussianOne‖^2=(1 : ℝ) := by
    rw [← GaussianPolynomialProcess.brownianCore_zero_degree (0 : ℝ≥0),
      GaussianTimeSpaceHermite.brownianCore_norm_sq]
    norm_num
  rw [← real_inner_self_eq_norm_sq,tensor_inner,real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq,ho,hl,firstChaosEmbedding.norm_map]
  change ‖incrementDirection 1 2‖^2*1=1
  rw [incrementDirection_norm_sq 1 2 (by norm_num)]
  norm_num

/-- Exact nonzero Cauchy--Riemann defect in an ACTUAL early Cameron--Martin direction. -/
theorem directional_cr_energy : ‖physicalX realGradient-physicalY imagGradientY‖^2=4 := by
  rw [physical_real_gradient,physical_imag_gradient,sub_neg_eq_add,← two_smul ℝ _]
  rw [norm_smul,mul_pow,terminal_energy]
  norm_num

/-- No alternative full closed derivative values can make even this necessary CR equation hold. -/
theorem full_directional_cr_impossible :
    ¬ ∃ HX HY : DerivativeField,
      (realPartValue,HX) ∈ sourceDerivative.graph ∧
      (swap gaussianProduct gaussianProduct imagPartValue,HY) ∈ sourceDerivative.graph ∧
      physicalX HX=physicalY HY := by
  rintro ⟨HX,HY,hX,hY,he⟩
  have hx := sourceDerivative.mem_graph_snd_inj hX real_graph rfl
  have hy := sourceDerivative.mem_graph_snd_inj hY imag_swapped_graph rfl
  rw [hx,hy] at he
  have hn := directional_cr_energy
  rw [he,sub_self] at hn
  norm_num at hn

private theorem early_eq : (early : GaussianL2)=wienerL2 1 :=
  Lp.ext (firstChaosPolynomial_coeFn earlyDirection)
private theorem late_ae : (late : GaussianL2) =ᵐ[gaussianProduct]
    fun w => process 2 w-process 1 w :=
  (firstChaosPolynomial_coeFn lateDirection).trans (process_increment_ae 1 2 (by norm_num))
private theorem early_past : AEStronglyMeasurable[naturalFiltration 1] (early : GaussianL2) gaussianProduct := by
  rw [early_eq]
  exact (process_stronglyAdapted 1).aestronglyMeasurable
private theorem one_past : AEStronglyMeasurable[naturalFiltration 1] gaussianOne gaussianProduct :=
  aestronglyMeasurable_const.congr gaussianOne_coeFn.symm

private theorem increment_early :
    GaussianPastStepCompletion.pastIncrement 1 2 (by norm_num) (early : GaussianL2) early_past=
      (quadratic : GaussianL2) := by
  apply Lp.ext
  filter_upwards [GaussianPastStepCompletion.pastIncrement_coeFn 1 2 (by norm_num)
    (early : GaussianL2) early_past,polynomialProductL2_coeFn early late,late_ae] with w hi hq hl
  change (quadratic : GaussianL2) w=(early : GaussianL2) w*(late : GaussianL2) w at hq
  rw [hi,hq,hl]
private theorem increment_one :
    GaussianPastStepCompletion.pastIncrement 1 2 (by norm_num) gaussianOne one_past=(late : GaussianL2) := by
  apply Lp.ext
  filter_upwards [GaussianPastStepCompletion.pastIncrement_coeFn 1 2 (by norm_num)
    gaussianOne one_past,gaussianOne_coeFn,late_ae] with w hi ho hl
  rw [hi,ho,one_mul]
  exact hl.symm

def stepX : Input 2 := stepInput 2 1 2 (by norm_num) le_rfl (early : GaussianL2) gaussianOne early_past one_past
def stepY : Input 2 := stepInput 2 1 2 (by norm_num) le_rfl gaussianOne (early : GaussianL2) one_past early_past

theorem real_stochastic : integralX 2 stepX+integralY 2 stepY=realPartValue := by
  rw [stepX,stepY,integralX_stepInput,integralY_stepInput,increment_early]
  rfl

theorem imag_stochastic : integralY 2 stepX-integralX 2 stepY=imagPartValue := by
  rw [stepX,stepY,integralY_stepInput,integralX_stepInput,increment_one]
  rfl

attribute [local irreducible] stepX stepY realPartValue imagPartValue

/-- Both adapted CR equations hold for the actual projected full derivative values. -/
theorem adapted_cr : causalX 2 realGradient=causalY 2 imagGradientY ∧
    causalX 2 imagGradientX+causalY 2 realGradient=0 := by
  have hRX : adjointX 2 realPartValue=stepX := by
    rw [← real_stochastic,map_add,adjointX_integralX,adjointX_integralY,add_zero]
  have hRY : adjointY 2 realPartValue=stepY := by
    rw [← real_stochastic,map_add,adjointY_integralX,adjointY_integralY,zero_add]
  have hIX : adjointX 2 imagPartValue=-stepY := by
    rw [← imag_stochastic,map_sub,adjointX_integralY,adjointX_integralX,zero_sub]
  have hIY : adjointY 2 imagPartValue=stepX := by
    rw [← imag_stochastic,map_sub,adjointY_integralY,adjointY_integralX,sub_zero]
  have h1 := (adjointX_derivative 2 realPartValue realGradient real_graph).symm.trans hRX
  have h2 := (adjointY_derivative 2 imagPartValue imagGradientY imag_swapped_graph).symm.trans hIY
  have h3 := (adjointX_derivative 2 imagPartValue imagGradientX imag_graph).symm.trans hIX
  have h4 := (adjointY_derivative 2 realPartValue realGradient real_swapped_graph).symm.trans hRY
  refine ⟨h1.trans h2.symm,?_⟩
  rw [h3,h4,neg_add_cancel]

private theorem combine_i (A B C D : JointL2) :
    combine (gaussianProduct.prod gaussianProduct) A B+Complex.I • combine (gaussianProduct.prod gaussianProduct) C D=
      combine (gaussianProduct.prod gaussianProduct) (A-D) (B+C) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (combine (gaussianProduct.prod gaussianProduct) A B)
      (Complex.I • combine (gaussianProduct.prod gaussianProduct) C D),
    Lp.coeFn_smul Complex.I (combine (gaussianProduct.prod gaussianProduct) C D),
    combine_ae (gaussianProduct.prod gaussianProduct) A B,
    combine_ae (gaussianProduct.prod gaussianProduct) C D,
    combine_ae (gaussianProduct.prod gaussianProduct) (A-D) (B+C),
    Lp.coeFn_sub A D,Lp.coeFn_add B C] with w hs hm hab hcd ho hd ha
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply] at hs hm hd ha
  rw [hs,hm,hab,hcd,ho,hd,ha]
  simp only [smul_eq_mul]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem raw_complex_input (T : ℝ≥0) (a b : Input T) :
    rawChannel T Complex.I (combineInput T a b)=
      combine (gaussianProduct.prod gaussianProduct)
        (integralX T a-integralY T b) (integralX T b+integralY T a) := by
  change integralXComplex T (combineInput T a b)+Complex.I • integralYComplex T (combineInput T a b)=_
  unfold integralXComplex integralYComplex
  rw [liftInput_combine,liftInput_combine]
  exact combine_i _ _ _ _

def observable : JointComplex := combine (gaussianProduct.prod gaussianProduct) realPartValue imagPartValue

/-- The SAME full-domain CR-defective observable is an ACTUAL adapted dZ step integral. -/
theorem observable_stochastic : rawChannel 2 Complex.I (combineInput 2 stepX (-stepY))=observable := by
  rw [raw_complex_input,map_neg,map_neg,sub_neg_eq_add,real_stochastic]
  change combine (gaussianProduct.prod gaussianProduct) realPartValue (-integralX 2 stepY+integralY 2 stepX)=_
  congr 1
  exact (add_comm _ _).trans (by simpa only [sub_eq_add_neg] using imag_stochastic)

/-- Actual normalized Cauchy fixed point, despite the genuine full CR obstruction above. -/
theorem observable_fixed : cauchyProjection 2 false observable=observable := by
  apply (cauchyProjection_eq_self_iff 2 false observable).mpr
  have hq : channelScale ≠ 0 := by
    unfold channelScale
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  refine ⟨channelScale⁻¹ • combineInput 2 stepX (-stepY),?_⟩
  change channelScale • rawChannel 2 Complex.I (channelScale⁻¹ • combineInput 2 stepX (-stepY))=observable
  rw [map_smul,smul_smul,mul_inv_cancel₀ hq,one_smul,observable_stochastic]

/-- A concrete fixed point has all four genuine closed partial graphs but cannot satisfy full CR. -/
theorem fixed_point_not_full_cr : cauchyProjection 2 false observable=observable ∧
    (realPartValue,realGradient) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct realPartValue,realGradient) ∈ sourceDerivative.graph ∧
    (imagPartValue,imagGradientX) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct imagPartValue,imagGradientY) ∈ sourceDerivative.graph ∧
    ¬ ∃ HX HY : DerivativeField,
      (realPartValue,HX) ∈ sourceDerivative.graph ∧
      (swap gaussianProduct gaussianProduct imagPartValue,HY) ∈ sourceDerivative.graph ∧
      physicalX HX=physicalY HY :=
  ⟨observable_fixed,real_graph,real_swapped_graph,imag_graph,imag_swapped_graph,full_directional_cr_impossible⟩

/-- The concrete nonzero adapted integral has genuine complex L2 energy four. -/
theorem observable_energy : ‖observable‖^2=4 := by
  have he : ‖(early : GaussianL2)‖^2=(1 : ℝ) := by
    have h : (early : GaussianL2)=firstChaosEmbedding earlyDirection :=
      Lp.ext (firstChaosPolynomial_coeFn earlyDirection)
    rw [h,firstChaosEmbedding.norm_map,← real_inner_self_eq_norm_sq,early_inner]
  have ho : ‖gaussianOne‖^2=(1 : ℝ) := by
    rw [← GaussianPolynomialProcess.brownianCore_zero_degree (0 : ℝ≥0),
      GaussianTimeSpaceHermite.brownianCore_norm_sq]
    norm_num
  have hc : ‖combineInput 2 stepX (-stepY)‖^2=2 := by
    rw [input_norm_sq,realInput_combine,imagInput_combine,norm_neg]
    unfold stepX stepY
    rw [stepInput_energy,stepInput_energy,he,ho]
    norm_num
  rw [← observable_stochastic,rawChannel_energy,hc]
  norm_num

end OperatorDerivativeRewrite.Foundation.StochasticCauchyHolomorphicObstruction
