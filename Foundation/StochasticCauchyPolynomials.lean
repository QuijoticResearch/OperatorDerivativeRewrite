import Foundation.StochasticCauchyAnalyticPowers
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Derivative

/-! Actual complex polynomial cylinders with their full original partial graphs
and actual complex mean subtraction. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomials
open InfiniteGaussian ProductL2Curry GaussianTimeSpaceHermite
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyMalliavinBridge StochasticCauchyCausalRotation
open StochasticCauchyPastReconstruction StochasticCauchyComplexChannels ComplexL2Isometry
open StochasticCauchyAnalyticPowers
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete GaussianTimeHilbert.timeHilbert_secondCountable

private theorem all_power_graphs (h : CoefficientSpace) (n : ℕ) :
    (realPower h n,directionField h ((n:ℝ) • realPower h (n-1))) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct (realPower h n),
      -directionField h (swap gaussianProduct gaussianProduct ((n:ℝ) • imagPower h (n-1)))) ∈ sourceDerivative.graph ∧
    (imagPower h n,directionField h ((n:ℝ) • imagPower h (n-1))) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct (imagPower h n),
      directionField h (swap gaussianProduct gaussianProduct ((n:ℝ) • realPower h (n-1)))) ∈ sourceDerivative.graph := by
  cases n with
  | zero =>
    have hx := term_x_graph h 0 0
    have hy := term_y_graph h 0 0
    simp only [Nat.cast_zero,zero_smul,map_zero,neg_zero]
    refine ⟨?_,?_,?_,?_⟩
    · simpa [realPower,binomial] using hx
    · simpa [realPower,binomial] using hy
    · simpa [imagPower,binomial] using sourceDerivative.graph.zero_mem
    · simpa [imagPower,binomial] using sourceDerivative.graph.zero_mem
  | succ n => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using power_graphs h n

private def reMix (c : ℂ) (F G : JointL2) : JointL2 := c.re • F-c.im • G
private def imMix (c : ℂ) (F G : JointL2) : JointL2 := c.re • G+c.im • F

def realPolynomial (h : CoefficientSpace) (p : Polynomial ℂ) : JointL2 :=
  ∑ n ∈ Finset.range (p.natDegree+1), reMix (p.coeff n) (realPower h n) (imagPower h n)
def imagPolynomial (h : CoefficientSpace) (p : Polynomial ℂ) : JointL2 :=
  ∑ n ∈ Finset.range (p.natDegree+1), imMix (p.coeff n) (realPower h n) (imagPower h n)
def realSlope (h : CoefficientSpace) (p : Polynomial ℂ) : JointL2 :=
  ∑ n ∈ Finset.range (p.natDegree+1),
    reMix (p.coeff n) ((n:ℝ) • realPower h (n-1)) ((n:ℝ) • imagPower h (n-1))
def imagSlope (h : CoefficientSpace) (p : Polynomial ℂ) : JointL2 :=
  ∑ n ∈ Finset.range (p.natDegree+1),
    imMix (p.coeff n) ((n:ℝ) • realPower h (n-1)) ((n:ℝ) • imagPower h (n-1))

attribute [local irreducible] sourceDerivative directionField

private theorem mix_graphs (h : CoefficientSpace) (c : ℂ) (F G a b : JointL2)
    (hFX : (F,directionField h a) ∈ sourceDerivative.graph)
    (hFY : (swap gaussianProduct gaussianProduct F,-directionField h (swap gaussianProduct gaussianProduct b)) ∈ sourceDerivative.graph)
    (hGX : (G,directionField h b) ∈ sourceDerivative.graph)
    (hGY : (swap gaussianProduct gaussianProduct G,directionField h (swap gaussianProduct gaussianProduct a)) ∈ sourceDerivative.graph) :
    (reMix c F G,directionField h (reMix c a b)) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct (reMix c F G),
      -directionField h (swap gaussianProduct gaussianProduct (imMix c a b))) ∈ sourceDerivative.graph ∧
    (imMix c F G,directionField h (imMix c a b)) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct (imMix c F G),
      directionField h (swap gaussianProduct gaussianProduct (reMix c a b))) ∈ sourceDerivative.graph := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Prod.smul_mk,Prod.mk_sub_mk,reMix,map_sub,map_smul] using
      sourceDerivative.graph.sub_mem (sourceDerivative.graph.smul_mem c.re hFX) (sourceDerivative.graph.smul_mem c.im hGX)
  · have he : (swap gaussianProduct gaussianProduct (reMix c F G),
        -directionField h (swap gaussianProduct gaussianProduct (imMix c a b)))=
        c.re • (swap gaussianProduct gaussianProduct F,-directionField h (swap gaussianProduct gaussianProduct b))-
        c.im • (swap gaussianProduct gaussianProduct G,directionField h (swap gaussianProduct gaussianProduct a)) := by
      apply Prod.ext <;> simp only [Prod.smul_mk,Prod.mk_sub_mk,reMix,imMix,map_sub,map_add,map_smul,smul_neg] <;> module
    rw [he]
    exact sourceDerivative.graph.sub_mem (sourceDerivative.graph.smul_mem c.re hFY) (sourceDerivative.graph.smul_mem c.im hGY)
  · simpa only [Prod.smul_mk,Prod.mk_add_mk,imMix,map_add,map_smul] using
      sourceDerivative.graph.add_mem (sourceDerivative.graph.smul_mem c.re hGX) (sourceDerivative.graph.smul_mem c.im hFX)
  · have he : (swap gaussianProduct gaussianProduct (imMix c F G),
        directionField h (swap gaussianProduct gaussianProduct (reMix c a b)))=
        c.re • (swap gaussianProduct gaussianProduct G,directionField h (swap gaussianProduct gaussianProduct a))+
        c.im • (swap gaussianProduct gaussianProduct F,-directionField h (swap gaussianProduct gaussianProduct b)) := by
      apply Prod.ext <;> simp only [Prod.smul_mk,Prod.mk_add_mk,reMix,imMix,map_sub,map_add,map_smul,smul_neg] <;> module
    rw [he]
    exact sourceDerivative.graph.add_mem (sourceDerivative.graph.smul_mem c.re hGY) (sourceDerivative.graph.smul_mem c.im hFY)

/-- Every complex polynomial has all four original partial graphs. -/
theorem polynomial_graphs (h : CoefficientSpace) (p : Polynomial ℂ) :
    (realPolynomial h p,directionField h (realSlope h p)) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct (realPolynomial h p),
      -directionField h (swap gaussianProduct gaussianProduct (imagSlope h p))) ∈ sourceDerivative.graph ∧
    (imagPolynomial h p,directionField h (imagSlope h p)) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct (imagPolynomial h p),
      directionField h (swap gaussianProduct gaussianProduct (realSlope h p))) ∈ sourceDerivative.graph := by
  have hg (n : ℕ) := mix_graphs h (p.coeff n) _ _ _ _ (all_power_graphs h n).1
    (all_power_graphs h n).2.1 (all_power_graphs h n).2.2.1 (all_power_graphs h n).2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [← prod_mk_sum,← map_sum,realPolynomial,realSlope] using
      sourceDerivative.graph.sum_mem (fun n (_ : n ∈ Finset.range (p.natDegree+1)) => (hg n).1)
  · simpa only [← prod_mk_sum,realPolynomial,imagSlope,map_sum,Finset.sum_neg_distrib] using
      sourceDerivative.graph.sum_mem (fun n (_ : n ∈ Finset.range (p.natDegree+1)) => (hg n).2.1)
  · simpa only [← prod_mk_sum,← map_sum,imagPolynomial,imagSlope] using
      sourceDerivative.graph.sum_mem (fun n (_ : n ∈ Finset.range (p.natDegree+1)) => (hg n).2.2.1)
  · simpa only [← prod_mk_sum,← map_sum,imagPolynomial,realSlope] using
      sourceDerivative.graph.sum_mem (fun n (_ : n ∈ Finset.range (p.natDegree+1)) => (hg n).2.2.2)

private theorem combine_mix (c : ℂ) (F G : JointL2) :
    combine (gaussianProduct.prod gaussianProduct) (reMix c F G) (imMix c F G)=
      c • combine (gaussianProduct.prod gaussianProduct) F G := by
  apply Lp.ext
  filter_upwards [combine_ae _ (reMix c F G) (imMix c F G),combine_ae _ F G,
    Lp.coeFn_smul c (combine (gaussianProduct.prod gaussianProduct) F G),
    Lp.coeFn_sub (c.re • F) (c.im • G),Lp.coeFn_add (c.re • G) (c.im • F),
    Lp.coeFn_smul c.re F,Lp.coeFn_smul c.im G,Lp.coeFn_smul c.re G,Lp.coeFn_smul c.im F]
    with w hl hr hs hd ha h1 h2 h3 h4
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at *
  change reMix c F G w=_ at hd
  change imMix c F G w=_ at ha
  rw [hl,hs,hr,hd,ha,h1,h2,h3,h4]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring

private theorem combine_sum (s : Finset ℕ) (F G : ℕ → JointL2) :
    combine (gaussianProduct.prod gaussianProduct) (∑ n ∈ s,F n) (∑ n ∈ s,G n)=
      ∑ n ∈ s,combine (gaussianProduct.prod gaussianProduct) (F n) (G n) := by
  simp only [combine,map_sum,Finset.smul_sum,Finset.sum_add_distrib]

private theorem sum_ae (s : Finset ℕ) (f : ℕ → JointComplex) :
    (∑ n ∈ s,f n)=ᵐ[gaussianProduct.prod gaussianProduct] fun w => ∑ n ∈ s,f n w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 (gaussianProduct.prod gaussianProduct)] with w hw
    simpa using hw
  | @insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    filter_upwards [Lp.coeFn_add (f n) (∑ j ∈ s,f j),ih] with w ha hs
    simp only [Pi.add_apply] at ha
    rw [ha,hs]

def polynomialValue (h : CoefficientSpace) (p : Polynomial ℂ) : JointComplex :=
  combine (gaussianProduct.prod gaussianProduct) (realPolynomial h p) (imagPolynomial h p)

theorem polynomial_value_ae (h : CoefficientSpace) (p : Polynomial ℂ) :
    polynomialValue h p =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      p.eval ((firstChaosEmbedding h w.1:ℂ)+Complex.I*(firstChaosEmbedding h w.2:ℂ)) := by
  have he : polynomialValue h p=∑ n ∈ Finset.range (p.natDegree+1),
      (p.coeff n) • combine (gaussianProduct.prod gaussianProduct) (realPower h n) (imagPower h n) := by
    simp only [polynomialValue,realPolynomial,imagPolynomial,combine_sum,combine_mix]
  rw [he]
  have ht (n : ℕ) : (p.coeff n) • combine (gaussianProduct.prod gaussianProduct) (realPower h n) (imagPower h n)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w => p.coeff n *
        ((firstChaosEmbedding h w.1:ℂ)+Complex.I*(firstChaosEmbedding h w.2:ℂ))^n := by
    filter_upwards [Lp.coeFn_smul (p.coeff n) (combine (gaussianProduct.prod gaussianProduct) (realPower h n) (imagPower h n)),power_value_ae h n] with w hs hp
    simp only [Pi.smul_apply,smul_eq_mul] at hs
    rw [hs,hp]
  filter_upwards [sum_ae (Finset.range (p.natDegree+1)) _,ae_all_iff.mpr ht] with w hs ht
  rw [hs,Polynomial.eval_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => ht n)

/-- The lowering coefficient is the actual ordinary polynomial derivative. -/
theorem slope_value_ae (h : CoefficientSpace) (p : Polynomial ℂ) :
    combine (gaussianProduct.prod gaussianProduct) (realSlope h p) (imagSlope h p)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      p.derivative.eval ((firstChaosEmbedding h w.1:ℂ)+Complex.I*(firstChaosEmbedding h w.2:ℂ)) := by
  have hn (n : ℕ) : combine (gaussianProduct.prod gaussianProduct)
      ((n:ℝ) • realPower h (n-1)) ((n:ℝ) • imagPower h (n-1))=
      (n:ℂ) • combine (gaussianProduct.prod gaussianProduct) (realPower h (n-1)) (imagPower h (n-1)) := by
    simpa only [reMix,imMix,Complex.natCast_re,Complex.natCast_im,zero_smul,sub_zero,add_zero] using
      combine_mix (n:ℂ) (realPower h (n-1)) (imagPower h (n-1))
  have he : combine (gaussianProduct.prod gaussianProduct) (realSlope h p) (imagSlope h p)=
      ∑ n ∈ Finset.range (p.natDegree+1), (p.coeff n*(n:ℂ)) •
        combine (gaussianProduct.prod gaussianProduct) (realPower h (n-1)) (imagPower h (n-1)) := by
    simp only [realSlope,imagSlope,combine_sum,combine_mix,hn,smul_smul]
  rw [he]
  have ht (n : ℕ) : (p.coeff n*(n:ℂ)) •
      combine (gaussianProduct.prod gaussianProduct) (realPower h (n-1)) (imagPower h (n-1))
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w => p.coeff n*(n:ℂ)*
        ((firstChaosEmbedding h w.1:ℂ)+Complex.I*(firstChaosEmbedding h w.2:ℂ))^(n-1) := by
    filter_upwards [Lp.coeFn_smul (p.coeff n*(n:ℂ)) (combine (gaussianProduct.prod gaussianProduct)
      (realPower h (n-1)) (imagPower h (n-1))),power_value_ae h (n-1)] with w hs hp
    simp only [Pi.smul_apply,smul_eq_mul] at hs
    rw [hs,hp]
  filter_upwards [sum_ae (Finset.range (p.natDegree+1)) _,ae_all_iff.mpr ht] with w hs ht
  rw [hs,Polynomial.derivative_eval,p.sum_over_range (fun n => by simp)]
  exact Finset.sum_congr rfl (fun n _ => ht n)

/-- The unbounded evaluated polynomial is genuinely square integrable. -/
theorem polynomial_memLp (h : CoefficientSpace) (p : Polynomial ℂ) :
    MemLp (fun w => p.eval ((firstChaosEmbedding h w.1:ℂ)+Complex.I*(firstChaosEmbedding h w.2:ℂ)))
      2 (gaussianProduct.prod gaussianProduct) :=
  (Lp.memLp (polynomialValue h p)).ae_eq (polynomial_value_ae h p)

/-- Actual componentwise centering equals subtraction of the true complex mean. -/
theorem centered_combine_ae (F G : JointL2) :
    combine (gaussianProduct.prod gaussianProduct) (center F) (center G)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      combine (gaussianProduct.prod gaussianProduct) F G w -
        ∫ x,combine (gaussianProduct.prod gaussianProduct) F G x ∂gaussianProduct.prod gaussianProduct := by
  have hF := (Lp.memLp F).integrable (by norm_num)
  have hG := (Lp.memLp G).integrable (by norm_num)
  have hi : ∫ w,combine (gaussianProduct.prod gaussianProduct) F G w ∂gaussianProduct.prod gaussianProduct=
      (∫ w,F w ∂gaussianProduct.prod gaussianProduct:ℝ)+Complex.I*(∫ w,G w ∂gaussianProduct.prod gaussianProduct:ℝ) := by
    have hf : Integrable (fun w => (F w:ℂ)) (gaussianProduct.prod gaussianProduct) := by
      exact Complex.ofRealCLM.integrable_comp hF
    have hg : Integrable (fun w => (G w:ℂ)) (gaussianProduct.prod gaussianProduct) := by
      exact Complex.ofRealCLM.integrable_comp hG
    rw [integral_congr_ae (combine_ae _ F G),integral_add hf (hg.const_mul Complex.I),integral_const_mul,
      integral_complex_ofReal,integral_complex_ofReal]
  rw [hi]
  have hc (A : JointL2) : center A =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      A w-∫ x,A x ∂gaussianProduct.prod gaussianProduct := by
    rw [center_apply]
    filter_upwards [Lp.coeFn_sub A ((∫ x,A x ∂gaussianProduct.prod gaussianProduct) • jointOne),
      Lp.coeFn_smul (∫ x,A x ∂gaussianProduct.prod gaussianProduct) jointOne,jointOne_ae] with w hd hs h1
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hd hs
    rw [hd,hs,h1,mul_one]
  filter_upwards [combine_ae _ (center F) (center G),combine_ae _ F G,hc F,hc G] with w hl hr hf hg
  rw [hl,hr,hf,hg]
  push_cast
  ring

/-- Genuine centered polynomial target, identified against its actual law. -/
theorem centered_polynomial_ae (h : CoefficientSpace) (p : Polynomial ℂ) :
    combine (gaussianProduct.prod gaussianProduct) (center (realPolynomial h p)) (center (imagPolynomial h p))
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      p.eval ((firstChaosEmbedding h w.1:ℂ)+Complex.I*(firstChaosEmbedding h w.2:ℂ))-
        ∫ x,p.eval ((firstChaosEmbedding h x.1:ℂ)+Complex.I*(firstChaosEmbedding h x.2:ℂ)) ∂gaussianProduct.prod gaussianProduct := by
  have he := polynomial_value_ae h p
  have hi := integral_congr_ae he
  filter_upwards [centered_combine_ae (realPolynomial h p) (imagPolynomial h p),he] with w hc he
  change polynomialValue h p w=_ at he
  change _=polynomialValue h p w-_ at hc
  rw [hc,he]
  exact congrArg (_-·) hi

theorem polynomial_projections (T : ℝ≥0) (h : CoefficientSpace) (p : Polynomial ℂ)
    (ha : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] (firstChaosEmbedding h) gaussianProduct) :
    cauchyProjection T false (combine (gaussianProduct.prod gaussianProduct)
      (center (realPolynomial h p)) (center (imagPolynomial h p)))=
      combine (gaussianProduct.prod gaussianProduct) (center (realPolynomial h p)) (center (imagPolynomial h p)) ∧
    cauchyProjection T true (combine (gaussianProduct.prod gaussianProduct)
      (center (realPolynomial h p)) (center (imagPolynomial h p)))=0 := by
  have hp (n : ℕ) := binomial_past T h ha n
  have hr : realPolynomial h p ∈ jointPastL2 T := by
    apply (jointPastL2 T).sum_mem
    intro n hn
    exact (jointPastL2 T).sub_mem ((jointPastL2 T).smul_mem _ (hp n _)) ((jointPastL2 T).smul_mem _ (hp n _))
  have hi : imagPolynomial h p ∈ jointPastL2 T := by
    apply (jointPastL2 T).sum_mem
    intro n hn
    exact (jointPastL2 T).add_mem ((jointPastL2 T).smul_mem _ (hp n _)) ((jointPastL2 T).smul_mem _ (hp n _))
  have hg := polynomial_graphs h p
  exact analytic_graph_projections T h _ _ _ _ hr hi hg.1 hg.2.1 hg.2.2.1 hg.2.2.2

theorem terminal_polynomial_projections (T : ℝ≥0) (p : Polynomial ℂ) :
    let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector T)
    cauchyProjection T false (combine (gaussianProduct.prod gaussianProduct)
      (center (realPolynomial h p)) (center (imagPolynomial h p)))=
      combine (gaussianProduct.prod gaussianProduct) (center (realPolynomial h p)) (center (imagPolynomial h p)) ∧
    cauchyProjection T true (combine (gaussianProduct.prod gaussianProduct)
      (center (realPolynomial h p)) (center (imagPolynomial h p)))=0 := by
  dsimp only
  exact polynomial_projections T _ p (GaussianTimeProcess.process_stronglyAdapted T).aestronglyMeasurable

/-- Actual plus-channel stochastic reconstruction of any terminal polynomial,
with its true mean and all source-domain premises already established. -/
theorem terminal_polynomial_reconstruction (T : ℝ≥0) (p : Polynomial ℂ) :
    ∃ u : ComplexInput T, channel T false u =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => p.eval ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))-
        ∫ x,p.eval ((GaussianTimeProcess.process T x.1:ℂ)+Complex.I*(GaussianTimeProcess.process T x.2:ℂ)) ∂gaussianProduct.prod gaussianProduct := by
  let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
    (GaussianTimeHilbert.timeVector T)
  obtain ⟨u,hu⟩ := (cauchyProjection_eq_self_iff T false _).mp (terminal_polynomial_projections T p).1
  refine ⟨u,?_⟩
  change channel T false u=_ at hu
  rw [hu]
  exact centered_polynomial_ae h p

end OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomials
