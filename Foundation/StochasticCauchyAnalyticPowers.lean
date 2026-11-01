import Foundation.StochasticCauchyCausalRotation
import Foundation.GaussianTimeSpaceHermite

/-! Actual holomorphic terminal powers: finite binomial tensors of the
existing raw Gaussian powers, with original closed partial derivative graphs. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyAnalyticPowers
open InfiniteGaussian GaussianTimeSpaceHermite ProductL2Curry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyMalliavinBridge StochasticCauchyCausalRotation
open StochasticCauchyPastReconstruction StochasticCauchyComplexChannels ComplexL2Isometry
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete GaussianTimeHilbert.timeHilbert_secondCountable

def power (h : CoefficientSpace) (n : ℕ) : polynomialCylindricalDomain := core h 0 n
def term (h : CoefficientSpace) (a b : ℕ) : JointL2 :=
  productTensor gaussianProduct gaussianProduct (power h a : GaussianL2) (power h b : GaussianL2)

theorem power_ae (h : CoefficientSpace) (n : ℕ) :
    (power h n : GaussianL2) =ᵐ[gaussianProduct] fun w => firstChaosEmbedding h w^n := by
  simpa only [power,value,polynomial_at_zero,MvPolynomial.eval_pow,MvPolynomial.eval_X] using core_coeFn h 0 n

theorem term_swap (h : CoefficientSpace) (a b : ℕ) :
    swap gaussianProduct gaussianProduct (term h a b)=term h b a := swap_productTensor _ _ _ _

private theorem tensor_smul (B : GaussianL2) (v : GaussianVectorL2) (c : ℝ) :
    BochnerClosedOperator.tensor gaussianProduct B (c • v)=c • BochnerClosedOperator.tensor gaussianProduct B v := by
  apply Lp.ext
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct B (c • v),
    BochnerClosedOperator.tensor_coeFn gaussianProduct B v,
    Lp.coeFn_smul c (BochnerClosedOperator.tensor gaussianProduct B v)] with w hl hr hs
  rw [hl,hs]
  simp only [Pi.smul_apply]
  rw [hr]
  exact smul_comm _ _ _

private theorem tensor_zero (B : GaussianL2) : BochnerClosedOperator.tensor gaussianProduct B (0:GaussianVectorL2)=0 := by
  apply Lp.ext
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct B (0:GaussianVectorL2),
    Lp.coeFn_zero GaussianVectorL2 2 gaussianProduct] with w ht hz
  rw [ht,hz,smul_zero]
  rfl

theorem term_x_graph (h : CoefficientSpace) (a b : ℕ) :
    (term h a b,directionField h ((a:ℝ) • term h (a-1) b)) ∈ sourceDerivative.graph := by
  cases a with
  | zero =>
    have hg := sourceDerivative_tensor (power h 0) (power h b) 0
      (by simpa only [power,core_zero_derivative] using closedCylindricalDerivative_core_graph (power h 0))
    simpa only [term,tensor_zero,Nat.cast_zero,zero_smul,map_zero] using hg
  | succ a =>
    have hg := sourceDerivative_tensor (power h (a+1)) (power h b)
      ((a+1:ℝ) • scalarTensor h (power h a))
      (by simpa only [power,core_derivative] using closedCylindricalDerivative_core_graph (power h (a+1)))
    simpa only [term,Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,
      map_smul,directionField_tensor,tensor_smul] using hg

theorem term_y_graph (h : CoefficientSpace) (a b : ℕ) :
    (swap gaussianProduct gaussianProduct (term h a b),
      directionField h ((b:ℝ) • swap gaussianProduct gaussianProduct (term h a (b-1)))) ∈ sourceDerivative.graph := by
  rw [term_swap,term_swap]
  exact term_x_graph h b a

def binomial (h : CoefficientSpace) (n : ℕ) (a : ℕ → ℝ) : JointL2 :=
  ∑ j ∈ Finset.range (n+1), ((n.choose j:ℝ)*a j) • term h (n-j) j

private theorem coefficient_x (n j : ℕ) (a : ℝ) :
    ((n+1).choose j:ℝ)*a*(n+1-j:ℕ)=(n+1:ℝ)*((n.choose j:ℝ)*a) := by
  have he : (n.choose j:ℝ)*(n+1:ℕ)=((n+1).choose j:ℝ)*(n+1-j:ℕ) := by
    exact_mod_cast Nat.choose_mul_succ_eq n j
  push_cast at he
  calc
    _ = (((n+1).choose j:ℝ)*(n+1-j:ℕ))*a := by ring
    _ = ((n.choose j:ℝ)*(n+1:ℝ))*a := by rw [← he]
    _ = _ := by ring

private theorem coefficient_y (n j : ℕ) (a : ℝ) :
    ((n+1).choose (j+1):ℝ)*a*(j+1:ℕ)=(n+1:ℝ)*((n.choose j:ℝ)*a) := by
  have he : (n+1:ℕ)*(n.choose j:ℝ)=((n+1).choose (j+1):ℝ)*(j+1:ℕ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n j
  push_cast at he
  calc
    _ = (((n+1).choose (j+1):ℝ)*(j+1:ℝ))*a := by push_cast; ring
    _ = ((n+1:ℝ)*(n.choose j:ℝ))*a := by rw [← he]
    _ = _ := by ring

attribute [local irreducible] term directionField sourceDerivative

private theorem binomial_x_sum (h : CoefficientSpace) (n : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+2), (((n+1).choose j:ℝ)*a j*(n+1-j:ℕ)) • term h (n+1-j-1) j)=
      (n+1:ℝ) • binomial h n a := by
  rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ]
  simp only [Nat.sub_self,Nat.cast_zero,mul_zero,zero_smul,add_zero]
  rw [binomial,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_smul,coefficient_x]
  congr 2
  omega

private theorem binomial_y_sum (h : CoefficientSpace) (n : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+2), (((n+1).choose j:ℝ)*a j*(j:ℝ)) • term h (n+1-j) (j-1))=
      (n+1:ℝ) • binomial h n (fun j => a (j+1)) := by
  rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ']
  simp only [Nat.cast_zero,mul_zero,zero_smul,add_zero]
  rw [binomial,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_sub_add_right,Nat.add_sub_cancel,coefficient_y,smul_smul]

theorem binomial_x_graph (h : CoefficientSpace) (n : ℕ) (a : ℕ → ℝ) :
    (binomial h (n+1) a,directionField h ((n+1:ℝ) • binomial h n a)) ∈ sourceDerivative.graph := by
  have hg := sourceDerivative.graph.sum_mem (fun j (_hj : j ∈ Finset.range (n+2)) =>
    sourceDerivative.graph.smul_mem (((n+1).choose j:ℝ)*a j) (term_x_graph h (n+1-j) j))
  simpa only [Prod.smul_mk,← prod_mk_sum,← map_smul,← map_sum,smul_smul,
    binomial_x_sum,binomial,Nat.add_assoc,Nat.reduceAdd] using hg

theorem binomial_y_graph (h : CoefficientSpace) (n : ℕ) (a : ℕ → ℝ) :
    (swap gaussianProduct gaussianProduct (binomial h (n+1) a),
      directionField h (swap gaussianProduct gaussianProduct ((n+1:ℝ) • binomial h n (fun j => a (j+1)))))
      ∈ sourceDerivative.graph := by
  have hg := sourceDerivative.graph.sum_mem (fun j (_hj : j ∈ Finset.range (n+2)) =>
    sourceDerivative.graph.smul_mem (((n+1).choose j:ℝ)*a j) (term_y_graph h (n+1-j) j))
  simpa only [Prod.smul_mk,← prod_mk_sum,← map_smul,← map_sum,smul_smul,
    binomial_y_sum,binomial,Nat.add_assoc,Nat.reduceAdd] using hg

def realPower (h : CoefficientSpace) (n : ℕ) : JointL2 := binomial h n (fun j => (Complex.I^j).re)
def imagPower (h : CoefficientSpace) (n : ℕ) : JointL2 := binomial h n (fun j => (Complex.I^j).im)

private theorem re_shift (j : ℕ) : (Complex.I^(j+1)).re= -(Complex.I^j).im := by
  simp [pow_succ,Complex.mul_re]
private theorem im_shift (j : ℕ) : (Complex.I^(j+1)).im=(Complex.I^j).re := by
  simp [pow_succ,Complex.mul_im]

private theorem real_shift (h : CoefficientSpace) (n : ℕ) :
    binomial h n (fun j => (Complex.I^(j+1)).re)= -imagPower h n := by
  simp only [re_shift,binomial,imagPower,mul_neg,neg_smul,Finset.sum_neg_distrib]
private theorem imag_shift (h : CoefficientSpace) (n : ℕ) :
    binomial h n (fun j => (Complex.I^(j+1)).im)=realPower h n := by
  simp only [im_shift,realPower]

/-- Every positive degree has ALL FOUR original full partial derivative graphs. -/
theorem power_graphs (h : CoefficientSpace) (n : ℕ) :
    (realPower h (n+1),directionField h ((n+1:ℝ) • realPower h n)) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct (realPower h (n+1)),
      -directionField h (swap gaussianProduct gaussianProduct ((n+1:ℝ) • imagPower h n))) ∈ sourceDerivative.graph ∧
    (imagPower h (n+1),directionField h ((n+1:ℝ) • imagPower h n)) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct (imagPower h (n+1)),
      directionField h (swap gaussianProduct gaussianProduct ((n+1:ℝ) • realPower h n))) ∈ sourceDerivative.graph := by
  refine ⟨binomial_x_graph h n _,?_,binomial_x_graph h n _,?_⟩
  · have he := binomial_y_graph h n (fun j => (Complex.I^j).re)
    simpa only [real_shift,smul_neg,map_neg,realPower] using he
  · have he := binomial_y_graph h n (fun j => (Complex.I^j).im)
    simpa only [imag_shift,imagPower] using he

theorem term_ae (h : CoefficientSpace) (a b : ℕ) : term h a b =ᵐ[gaussianProduct.prod gaussianProduct]
    fun w => firstChaosEmbedding h w.1^a*firstChaosEmbedding h w.2^b := by
  rw [term]
  have hx := (Measure.quasiMeasurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp (power_ae h a)
  have hy := (Measure.quasiMeasurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp (power_ae h b)
  filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct (power h a : GaussianL2) (power h b : GaussianL2),hx,hy] with w ht hx hy
  simp only [Function.comp_apply] at hx hy
  rw [ht,hx,hy]
  rfl

private theorem sum_ae (s : Finset ℕ) (f : ℕ → JointL2) :
    (∑ j ∈ s, f j) =ᵐ[gaussianProduct.prod gaussianProduct] fun w => ∑ j ∈ s, f j w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 (gaussianProduct.prod gaussianProduct)] with w hw
    simpa using hw
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k),ih] with w ha hs
    simp only [Pi.add_apply] at ha
    rw [ha,hs]

theorem binomial_ae (h : CoefficientSpace) (n : ℕ) (a : ℕ → ℝ) :
    binomial h n a =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*a j*
        firstChaosEmbedding h w.1^(n-j)*firstChaosEmbedding h w.2^j := by
  have ht (j : ℕ) : (((n.choose j:ℝ)*a j) • term h (n-j) j) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => (n.choose j:ℝ)*a j*firstChaosEmbedding h w.1^(n-j)*firstChaosEmbedding h w.2^j := by
    filter_upwards [Lp.coeFn_smul ((n.choose j:ℝ)*a j) (term h (n-j) j),term_ae h (n-j) j] with w hs ht
    simp only [Pi.smul_apply,smul_eq_mul] at hs
    rw [hs,ht]
    ring
  filter_upwards [sum_ae (Finset.range (n+1)) (fun j => ((n.choose j:ℝ)*a j) • term h (n-j) j),
    ae_all_iff.mpr ht] with w hs ht
  change binomial h n a w=_ at hs
  rw [hs]
  exact Finset.sum_congr rfl (fun j _ => ht j)

private theorem binomial_identity (X Y : ℝ) (n : ℕ) :
    ((∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*(Complex.I^j).re*X^(n-j)*Y^j : ℝ) : ℂ)+
      Complex.I*((∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*(Complex.I^j).im*X^(n-j)*Y^j : ℝ) : ℂ)=
      ((X:ℂ)+Complex.I*(Y:ℂ))^n := by
  push_cast
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ Finset.range (n+1), (Complex.I*(Y:ℂ))^j*(X:ℂ)^(n-j)*(n.choose j:ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hi : ((Complex.I^j).re:ℂ)+Complex.I*((Complex.I^j).im:ℂ)=Complex.I^j := by
        simpa only [mul_comm] using Complex.re_add_im (Complex.I^j)
      rw [mul_pow]
      linear_combination (n.choose j:ℂ)*(X:ℂ)^(n-j)*(Y:ℂ)^j*hi
    _ = _ := by rw [← add_pow,add_comm]

/-- The verified full-domain cylinder really is Z^n on the original product law. -/
theorem power_value_ae (h : CoefficientSpace) (n : ℕ) :
    combine (gaussianProduct.prod gaussianProduct) (realPower h n) (imagPower h n)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      ((firstChaosEmbedding h w.1:ℂ)+Complex.I*(firstChaosEmbedding h w.2:ℂ))^n := by
  filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct) (realPower h n) (imagPower h n),
    binomial_ae h n (fun j => (Complex.I^j).re),binomial_ae h n (fun j => (Complex.I^j).im)] with w hc hr hi
  change realPower h n w=_ at hr
  change imagPower h n w=_ at hi
  rw [hc,hr,hi]
  exact binomial_identity _ _ n

private theorem tensor_past (T : ℝ≥0) (a b : GaussianL2)
    (ha : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] a gaussianProduct)
    (hb : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] b gaussianProduct) :
    productTensor gaussianProduct gaussianProduct a b ∈ jointPastL2 T := by
  have hm : StronglyMeasurable[jointPast T]
      (fun w : SampleSpace × SampleSpace => ha.mk a w.1*hb.mk b w.2) :=
    (ha.stronglyMeasurable_mk.comp_measurable
      (show @Measurable (SampleSpace × SampleSpace) SampleSpace (jointPast T)
        (GaussianTimeProcess.naturalFiltration T) Prod.fst from measurable_fst)).mul
    (hb.stronglyMeasurable_mk.comp_measurable
      (show @Measurable (SampleSpace × SampleSpace) SampleSpace (jointPast T)
        (GaussianTimeProcess.naturalFiltration T) Prod.snd from measurable_snd))
  have hx := (Measure.quasiMeasurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp ha.ae_eq_mk
  have hy := (Measure.quasiMeasurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp hb.ae_eq_mk
  have he : productTensor gaussianProduct gaussianProduct a b =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => ha.mk a w.1*hb.mk b w.2 := by
    filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct a b,hx,hy] with w ht hx hy
    rw [ht]
    simpa only [smul_eq_mul,Function.comp_apply] using congrArg₂ (·*·) hx hy
  exact hm.aestronglyMeasurable.congr he.symm

theorem binomial_past (T : ℝ≥0) (h : CoefficientSpace)
    (ha : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] (firstChaosEmbedding h) gaussianProduct)
    (n : ℕ) (a : ℕ → ℝ) : binomial h n a ∈ jointPastL2 T := by
  apply (jointPastL2 T).sum_mem
  intro j hj
  apply (jointPastL2 T).smul_mem
  simpa only [term] using tensor_past T _ _ ((ha.pow (n-j)).congr (power_ae h (n-j)).symm)
    ((ha.pow j).congr (power_ae h j).symm)

/-- Every positive holomorphic power has genuine centered plus reconstruction
and zero anti projection, with its observed target-domain premise checked. -/
theorem power_projections (T : ℝ≥0) (h : CoefficientSpace) (n : ℕ)
    (ha : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] (firstChaosEmbedding h) gaussianProduct) :
    cauchyProjection T false (combine (gaussianProduct.prod gaussianProduct)
      (center (realPower h (n+1))) (center (imagPower h (n+1))))=
      combine (gaussianProduct.prod gaussianProduct) (center (realPower h (n+1))) (center (imagPower h (n+1))) ∧
    cauchyProjection T true (combine (gaussianProduct.prod gaussianProduct)
      (center (realPower h (n+1))) (center (imagPower h (n+1))))=0 := by
  have hg := power_graphs h n
  exact analytic_graph_projections T h (realPower h (n+1)) (imagPower h (n+1))
    ((n+1:ℝ) • realPower h n) ((n+1:ℝ) • imagPower h n)
    (binomial_past T h ha (n+1) _) (binomial_past T h ha (n+1) _)
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2

/-- Instantiation at the ACTUAL terminal Brownian coordinate, for every horizon
and every positive degree; no abstract measurability hypothesis remains. -/
theorem terminal_power_projections (T : ℝ≥0) (n : ℕ) :
    let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector T)
    cauchyProjection T false (combine (gaussianProduct.prod gaussianProduct)
      (center (realPower h (n+1))) (center (imagPower h (n+1))))=
      combine (gaussianProduct.prod gaussianProduct) (center (realPower h (n+1))) (center (imagPower h (n+1))) ∧
    cauchyProjection T true (combine (gaussianProduct.prod gaussianProduct)
      (center (realPower h (n+1))) (center (imagPower h (n+1))))=0 := by
  dsimp only
  exact power_projections T _ n (GaussianTimeProcess.process_stronglyAdapted T).aestronglyMeasurable

end OperatorDerivativeRewrite.Foundation.StochasticCauchyAnalyticPowers
