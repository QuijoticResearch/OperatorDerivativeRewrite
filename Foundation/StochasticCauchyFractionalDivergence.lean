import Foundation.StochasticCauchyMalliavinBridge
import Foundation.GaussianMixedQuadraticFourthMoment
import Foundation.FractionalWickCovariance

/-! Genuine Gaussian divergence of correlated first-chaos steps. These are full
adjoint graphs, not Brownian predictable integrals or an asserted fBM causal
projection. The Wick correction survives in the complex conjugate pairing. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyFractionalDivergence
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuadraticSourceHodge
open GaussianTimePolynomialPairing GaussianTimeSensitivity IBMCubicFirstChaos
open StochasticCauchyMalliavinBridge StochasticCauchyParameterizedObstruction
open StochasticCauchyJointPastIntegral ProductL2Curry ComplexL2Isometry
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable

/-- Transport an ACTUAL Gaussian divergence graph to one physical source.
The parameter factor requires only L2, without a derivative assumption. -/
theorem divergence_tensor (u : GaussianVectorL2) (f B : GaussianL2)
    (hg : (u, f) ∈ hilbertDivergence.graph) :
    (BochnerClosedOperator.tensor gaussianProduct B u,
      productTensor gaussianProduct gaussianProduct f B) ∈ sourceDerivative.adjoint.graph := by
  have ht := BochnerClosedOperator.tensor_graph gaussianProduct hilbertDivergence B u f hg
  have hl := LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct
      closedCylindricalDerivative closedCylindricalDerivative_dense_domain) ht
  have hd := BochnerClosedOperator.lift_dense_domain gaussianProduct
    closedCylindricalDerivative closedCylindricalDerivative_dense_domain
  obtain ⟨v,hv,he⟩ := (BochnerClosedOperator.lift gaussianProduct
    closedCylindricalDerivative).adjoint.mem_graph_iff.mp hl
  have hm := (AdjointUnitaryTransport.mem_pullback_adjoint_domain sourceCurry _ hd _).mpr v.property
  apply sourceDerivative.adjoint.mem_graph_iff.mpr
  refine ⟨⟨_,hm⟩,hv,?_⟩
  change (AdjointUnitaryTransport.pullback sourceCurry _).adjoint ⟨_,hm⟩ = _
  rw [AdjointUnitaryTransport.pullback_adjoint_apply sourceCurry _ hd _ hm v.property,he]
  apply sourceCurry.injective
  rw [sourceCurry.apply_symm_apply,sourceCurry_tensor]

def realValue (h k : CoefficientSpace) : JointL2 :=
  productTensor gaussianProduct gaussianProduct (mixedTarget k h) gaussianOne +
    productTensor gaussianProduct gaussianProduct gaussianOne (mixedTarget k h)

def imagValue (h k : CoefficientSpace) : JointL2 :=
  productTensor gaussianProduct gaussianProduct (firstChaosEmbedding h) (firstChaosEmbedding k) -
    productTensor gaussianProduct gaussianProduct (firstChaosEmbedding k) (firstChaosEmbedding h)

def plusValue (h k : CoefficientSpace) :=
  combine (gaussianProduct.prod gaussianProduct) (realValue h k) (imagValue h k)

def minusValue (h k : CoefficientSpace) :=
  combine (gaussianProduct.prod gaussianProduct) (realValue h k) (-imagValue h k)

/-- Own-source random step has the Wick product, including its covariance subtraction. -/
theorem own_step_graph (h k : CoefficientSpace) :
    (BochnerClosedOperator.tensor gaussianProduct gaussianOne
        (scalarTensor k (firstChaosEmbedding h)),
      productTensor gaussianProduct gaussianProduct (mixedTarget k h) gaussianOne)
      ∈ sourceDerivative.adjoint.graph :=
  divergence_tensor _ _ _ (mixed_divergence_graph k h)

/-- Other-source step is an ordinary independent tensor; no own derivative correction. -/
theorem other_step_graph (h k : CoefficientSpace) :
    (BochnerClosedOperator.tensor gaussianProduct (firstChaosEmbedding h)
        (scalarTensor k gaussianOne),
      productTensor gaussianProduct gaussianProduct (firstChaosEmbedding k) (firstChaosEmbedding h))
      ∈ sourceDerivative.adjoint.graph :=
  divergence_tensor _ _ _ (GaussianFirstChaosRecovery.firstChaos_divergence_graph k)

private theorem mixed_centered (h k : CoefficientSpace) :
    inner ℝ (mixedTarget k h) gaussianOne = 0 := by
  have he := GaussianNumberSectors.graph_duality
    (closedDerivative_constant_graph 1) (mixed_divergence_graph k h)
  simpa only [one_smul,inner_zero_left,real_inner_comm] using he.symm

theorem real_energy (h k : CoefficientSpace) :
    ‖realValue h k‖^2 = 2*(‖h‖^2*‖k‖^2+(inner ℝ h k)^2) := by
  rw [realValue,norm_add_sq_real]
  simp only [← real_inner_self_eq_norm_sq, tensor_inner,
    GaussianDeterministicGraphCore.gaussianOne_inner_self,mixed_centered,
    mul_zero,zero_mul,mul_one,one_mul]
  rw [real_inner_self_eq_norm_sq,GaussianMixedQuadraticFourthMoment.mixedTarget_variance,
    real_inner_comm k h]
  simp only [real_inner_self_eq_norm_sq]
  ring

theorem imag_energy (h k : CoefficientSpace) :
    ‖imagValue h k‖^2 = 2*(‖h‖^2*‖k‖^2-(inner ℝ h k)^2) := by
  rw [imagValue,norm_sub_sq_real]
  simp only [← real_inner_self_eq_norm_sq,tensor_inner,firstChaosEmbedding.inner_map_map]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_comm k h]
  ring

theorem real_imag_orthogonal (h k : CoefficientSpace) :
    inner ℝ (realValue h k) (imagValue h k)=0 := by
  have hc (v : CoefficientSpace) : inner ℝ gaussianOne (firstChaosEmbedding v)=0 := by
    rw [← wick_one_eq_embedding]
    exact wick_centered v 0
  simp only [realValue,imagValue,inner_add_left,inner_sub_right,tensor_inner,hc,
    mul_zero,zero_mul,sub_self,zero_add]

theorem plus_energy (h k : CoefficientSpace) :
    ‖plusValue h k‖^2=4*‖h‖^2*‖k‖^2 := by
  rw [plusValue,combine_norm_sq,real_energy,imag_energy]
  ring

theorem minus_energy (h k : CoefficientSpace) :
    ‖minusValue h k‖^2=4*‖h‖^2*‖k‖^2 := by
  rw [minusValue,combine_norm_sq,norm_neg,real_energy,imag_energy]
  ring

private theorem ofReal_inner (a b : JointL2) :
    inner ℂ (ofReal (gaussianProduct.prod gaussianProduct) a)
      (ofReal (gaussianProduct.prod gaussianProduct) b) = (inner ℝ a b : ℂ) := by
  rw [L2.inner_def,L2_inner_eq_integral,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL a,
    Complex.ofRealCLM.coeFn_compLpL b] with w ha hb
  change ofReal (gaussianProduct.prod gaussianProduct) a w = _ at ha
  change ofReal (gaussianProduct.prod gaussianProduct) b w = _ at hb
  rw [ha,hb]
  simp [RCLike.inner_apply]

theorem conjugate_pairing (h k : CoefficientSpace) :
    inner ℂ (plusValue h k) (minusValue h k) = ((4*(inner ℝ h k)^2 : ℝ) : ℂ) := by
  have ho := real_imag_orthogonal h k
  have hor : inner ℝ (imagValue h k) (realValue h k)=0 := by
    rw [real_inner_comm]
    exact ho
  simp only [plusValue,minusValue,combine,map_neg,smul_neg,inner_add_left,
    inner_add_right,inner_neg_right,inner_smul_left,inner_smul_right,ofReal_inner,
    real_inner_self_eq_norm_sq,ho,hor,Complex.ofReal_zero,mul_zero,
    add_zero,zero_add,Complex.conj_I]
  rw [real_energy,imag_energy]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Zero past/increment covariance is exactly the step-level orthogonality criterion. -/
theorem conjugate_pairing_zero_iff (h k : CoefficientSpace) :
    inner ℂ (plusValue h k) (minusValue h k)=0 ↔ inner ℝ h k=0 := by
  rw [conjugate_pairing]
  norm_cast
  constructor
  · intro he
    nlinarith [sq_nonneg (inner ℝ h k)]
  · intro he
    rw [he]
    norm_num

def fractionalPast (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) : CoefficientSpace :=
  FractionalGaussianProcess.direction H hH0 hH1 1

def fractionalIncrement (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) : CoefficientSpace :=
  FractionalGaussianProcess.direction H hH0 hH1 2-fractionalPast H hH0 hH1

theorem fractional_step_covariance (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    inner ℝ (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1)=
      (2:ℝ)^(2*H)/2-1 := by
  simp only [fractionalPast,fractionalIncrement,inner_sub_right,
    FractionalWickCovariance.direction_inner,FractionalSpectralGeometry.covariance]
  norm_num [Real.zero_rpow (by linarith : 2*H ≠ 0)]

theorem fractional_pairing (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    inner ℂ (plusValue (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1))
      (minusValue (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1))=
      ((4*((2:ℝ)^(2*H)/2-1)^2 : ℝ) : ℂ) := by
  rw [conjugate_pairing,fractional_step_covariance]

theorem fractional_pairing_zero_iff (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    inner ℂ (plusValue (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1))
      (minusValue (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1))=0 ↔ H=1/2 := by
  rw [conjugate_pairing_zero_iff,fractional_step_covariance]
  have hr := Real.rpow_right_inj (x := (2:ℝ)) (y := 2*H) (z := 1) (by norm_num) (by norm_num)
  rw [Real.rpow_one] at hr
  constructor
  · intro he
    have heq : (2:ℝ)^(2*H)=2 := by linarith
    have := hr.mp heq
    linarith
  · intro he
    rw [he]
    norm_num

/-- The missing derivative contribution in the real divergence is exactly c^2.
Both norms refer to the original Gaussian Hilbert spaces. -/
theorem rank_divergence_correction (h k : CoefficientSpace) :
    ‖mixedTarget k h‖^2-‖scalarTensor k (firstChaosEmbedding h)‖^2=(inner ℝ h k)^2 := by
  rw [GaussianMixedQuadraticFourthMoment.mixedTarget_variance,
    ← real_inner_self_eq_norm_sq (x := scalarTensor k (firstChaosEmbedding h)),
    GaussianTimeFieldNorm.scalarTensor_pair_inner,firstChaosEmbedding.inner_map_map,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  rw [real_inner_comm k h]
  ring

/-- Exact identification from genuine adjoint graphs, with physical source
exchange for the second divergence. No predictable isometry is assumed. -/
theorem step_graphs_determine_output (h k : CoefficientSpace) (F G : JointL2)
    (hF : (BochnerClosedOperator.tensor gaussianProduct gaussianOne
      (scalarTensor k (firstChaosEmbedding h)), F) ∈ sourceDerivative.adjoint.graph)
    (hG : (BochnerClosedOperator.tensor gaussianProduct (firstChaosEmbedding h)
      (scalarTensor k gaussianOne), G) ∈ sourceDerivative.adjoint.graph) :
    plusValue h k=combine (gaussianProduct.prod gaussianProduct)
      (F+swap gaussianProduct gaussianProduct F) (swap gaussianProduct gaussianProduct G-G) := by
  have hf := sourceDerivative.adjoint.mem_graph_snd_inj (own_step_graph h k) hF rfl
  have hg := sourceDerivative.adjoint.mem_graph_snd_inj (other_step_graph h k) hG rfl
  rw [← hf,← hg,swap_productTensor,swap_productTensor]
  rfl

/-- For every non-Brownian H, even this past-coefficient/future-increment
Gaussian divergence fails the covariance-only real isometry. -/
theorem fractional_divergence_not_isometry (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (hH : H ≠ 1/2) :
    ‖mixedTarget (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1)‖^2 ≠
      ‖scalarTensor (fractionalIncrement H hH0 hH1)
        (firstChaosEmbedding (fractionalPast H hH0 hH1))‖^2 := by
  have hc : inner ℝ (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1) ≠ 0 := by
    intro he
    exact hH ((fractional_pairing_zero_iff H hH0 hH1).mp
      ((conjugate_pairing_zero_iff _ _).mpr he))
  intro hn
  have he := rank_divergence_correction (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1)
  rw [hn,sub_self] at he
  exact (pow_ne_zero 2 hc) he.symm

end OperatorDerivativeRewrite.Foundation.StochasticCauchyFractionalDivergence
