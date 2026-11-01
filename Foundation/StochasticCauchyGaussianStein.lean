import Foundation.StochasticCauchyMeanResidual
import Foundation.GaussianFirstChaosRecovery

/-! Actual complex Gaussian Stein identities from the original closed partial
derivative graphs. Polynomial means and native initial-value centering follow;
conditional prediction and the running stochastic coefficient remain separate. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyGaussianStein
open InfiniteGaussian ProductL2Curry ComplexL2Isometry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyMalliavinBridge StochasticCauchyCausalRotation
open StochasticCauchyPastReconstruction StochasticCauchyComplexChannels
open StochasticCauchyMeanResidual StochasticCauchyPolynomials
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete GaussianTimeHilbert.timeHilbert_secondCountable

def xClass (h : CoefficientSpace) : JointL2 :=
  productTensor gaussianProduct gaussianProduct (firstChaosEmbedding h) gaussianOne

def yClass (h : CoefficientSpace) : JointL2 :=
  productTensor gaussianProduct gaussianProduct gaussianOne (firstChaosEmbedding h)

attribute [local irreducible] sourceCurry directionField sourceDerivative xClass yClass
  scalarTensor BochnerClosedOperator.tensor

theorem source_stein_X (h : CoefficientSpace) (F a : JointL2)
    (hF : (F, directionField h a) ∈ sourceDerivative.graph) :
    inner ℝ F (xClass h) = ‖h‖ ^ 2 * inner ℝ a jointOne := by
  have he : inner ℝ (directionField h a)
      (BochnerClosedOperator.tensor gaussianProduct gaussianOne (scalarTensor h gaussianOne)) =
      inner ℝ (sourceCurry F)
        (BochnerClosedOperator.tensor gaussianProduct gaussianOne (firstChaosEmbedding h)) := by
    rw [L2_inner_eq_integral, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [(sourceDerivative_graph F _).mp hF,
      BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne (scalarTensor h gaussianOne),
      BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne (firstChaosEmbedding h),
      gaussianOne_coeFn] with w hw hu hv ho
    have hu' : BochnerClosedOperator.tensor gaussianProduct gaussianOne
        (scalarTensor h gaussianOne) w = scalarTensor h gaussianOne :=
      hu.trans (by rw [ho, one_smul])
    have hv' : BochnerClosedOperator.tensor gaussianProduct gaussianOne
        (firstChaosEmbedding h) w = firstChaosEmbedding h :=
      hv.trans (by rw [ho, one_smul])
    rw [hu', hv']
    exact GaussianNumberSectors.graph_duality (f := sourceCurry F w)
      (g := directionField h a w) hw
      (GaussianFirstChaosRecovery.firstChaos_divergence_graph h)
  rw [← sourceCurry_tensor, sourceCurry.inner_map_map,
    directionField_pairing, real_inner_self_eq_norm_sq] at he
  rw [xClass]
  exact he.symm

theorem source_stein_Y (h : CoefficientSpace) (F a : JointL2)
    (hF : (swap gaussianProduct gaussianProduct F,
      directionField h (swap gaussianProduct gaussianProduct a)) ∈ sourceDerivative.graph) :
    inner ℝ F (yClass h) = ‖h‖ ^ 2 * inner ℝ a jointOne := by
  have he := source_stein_X h (swap gaussianProduct gaussianProduct F)
    (swap gaussianProduct gaussianProduct a) hF
  have hx : xClass h = swap gaussianProduct gaussianProduct (yClass h) := by
    rw [xClass, yClass, swap_productTensor]
  have h1 : jointOne = swap gaussianProduct gaussianProduct jointOne := by
    change productTensor gaussianProduct gaussianProduct gaussianOne gaussianOne =
      swap gaussianProduct gaussianProduct
        (productTensor gaussianProduct gaussianProduct gaussianOne gaussianOne)
    rw [swap_productTensor]
  rw [hx, (swap gaussianProduct gaussianProduct).inner_map_map, h1,
    (swap gaussianProduct gaussianProduct).inner_map_map] at he
  exact he

private theorem ofReal_inner (F G : JointL2) :
    inner ℂ (ofReal (gaussianProduct.prod gaussianProduct) F)
      (ofReal (gaussianProduct.prod gaussianProduct) G) = (inner ℝ F G : ℂ) := by
  rw [L2.inner_def, L2_inner_eq_integral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL F,
    Complex.ofRealCLM.coeFn_compLpL G] with w hf hg
  change ofReal (gaussianProduct.prod gaussianProduct) F w = (F w : ℂ) at hf
  change ofReal (gaussianProduct.prod gaussianProduct) G w = (G w : ℂ) at hg
  rw [hf, hg]
  simp [RCLike.inner_apply]

private theorem combine_inner (x y F G : JointL2) :
    inner ℂ (combine (gaussianProduct.prod gaussianProduct) x y)
      (combine (gaussianProduct.prod gaussianProduct) F G) =
    ((inner ℝ x F + inner ℝ y G : ℝ) : ℂ) +
      Complex.I * ((inner ℝ x G - inner ℝ y F : ℝ) : ℂ) := by
  simp only [combine, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, ofReal_inner]
  apply Complex.ext <;> simp <;> ring

/-- Exact complex Gaussian Stein identities on the original four partial
graphs. Multiplication by the holomorphic coordinate has zero mean; its
conjugate contracts to twice the component variance times the slope mean. -/
theorem analytic_stein (h : CoefficientSpace) (F G a b : JointL2)
    (hFX : (F, directionField h a) ∈ sourceDerivative.graph)
    (hFY : (swap gaussianProduct gaussianProduct F,
      -directionField h (swap gaussianProduct gaussianProduct b)) ∈ sourceDerivative.graph)
    (hGX : (G, directionField h b) ∈ sourceDerivative.graph)
    (hGY : (swap gaussianProduct gaussianProduct G,
      directionField h (swap gaussianProduct gaussianProduct a)) ∈ sourceDerivative.graph) :
    inner ℂ (combine (gaussianProduct.prod gaussianProduct) (xClass h) (-yClass h))
      (combine (gaussianProduct.prod gaussianProduct) F G) = 0 ∧
    inner ℂ (combine (gaussianProduct.prod gaussianProduct) (xClass h) (yClass h))
      (combine (gaussianProduct.prod gaussianProduct) F G) =
      ((2 * ‖h‖ ^ 2 : ℝ) : ℂ) * inner ℂ complexOne
        (combine (gaussianProduct.prod gaussianProduct) a b) := by
  have hxF : inner ℝ (xClass h) F = ‖h‖ ^ 2 * inner ℝ a jointOne := by
    rw [real_inner_comm]; exact source_stein_X h F a hFX
  have hxG : inner ℝ (xClass h) G = ‖h‖ ^ 2 * inner ℝ b jointOne := by
    rw [real_inner_comm]; exact source_stein_X h G b hGX
  have hyG : inner ℝ (yClass h) G = ‖h‖ ^ 2 * inner ℝ a jointOne := by
    rw [real_inner_comm]; exact source_stein_Y h G a hGY
  have hyF : inner ℝ (yClass h) F = -(‖h‖ ^ 2 * inner ℝ b jointOne) := by
    rw [real_inner_comm]
    have hh := source_stein_Y h F (-b) (by simpa only [map_neg] using hFY)
    simpa only [inner_neg_left, mul_neg] using hh
  simp only [combine_inner, complexOne, inner_neg_left, hxF, hxG, hyF, hyG,
    inner_zero_left, sub_zero]
  rw [real_inner_comm jointOne a, real_inner_comm jointOne b]
  constructor <;> push_cast <;> ring

def zValue (h : CoefficientSpace) (w : SampleSpace × SampleSpace) : ℂ :=
  (firstChaosEmbedding h w.1 : ℂ) + Complex.I * (firstChaosEmbedding h w.2 : ℂ)

theorem zValue_memLp (h : CoefficientSpace) :
    MemLp (zValue h) 2 (gaussianProduct.prod gaussianProduct) := by
  have hh := polynomial_memLp h Polynomial.X
  simp only [Polynomial.eval_X] at hh
  change MemLp (fun w => zValue h w) 2 (gaussianProduct.prod gaussianProduct) at hh
  exact hh

theorem polynomial_product_integrable (h : CoefficientSpace) (p : Polynomial ℂ) :
    Integrable (fun w => zValue h w * p.eval (zValue h w))
      (gaussianProduct.prod gaussianProduct) :=
  (zValue_memLp h).integrable_mul (polynomial_memLp h p)

theorem polynomial_conjugate_product_integrable (h : CoefficientSpace) (p : Polynomial ℂ) :
    Integrable (fun w => starRingEnd ℂ (zValue h w) * p.eval (zValue h w))
      (gaussianProduct.prod gaussianProduct) := by
  exact (zValue_memLp h).star.integrable_mul (polynomial_memLp h p)

private theorem coordinates_ae (h : CoefficientSpace) :
    xClass h =ᵐ[gaussianProduct.prod gaussianProduct] (fun w => firstChaosEmbedding h w.1) ∧
    yClass h =ᵐ[gaussianProduct.prod gaussianProduct] (fun w => firstChaosEmbedding h w.2) := by
  have hoX := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    gaussianOne_coeFn
  have hoY := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    gaussianOne_coeFn
  constructor
  · rw [xClass]
    filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct (firstChaosEmbedding h)
      gaussianOne, hoY] with w ht ho
    change gaussianOne w.2 = 1 at ho
    simpa only [smul_eq_mul, ho, mul_one] using ht
  · rw [yClass]
    filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct gaussianOne
      (firstChaosEmbedding h), hoX] with w ht ho
    change gaussianOne w.1 = 1 at ho
    simpa only [smul_eq_mul, ho, one_mul] using ht

private theorem conjugate_coordinate_ae (h : CoefficientSpace) :
    combine (gaussianProduct.prod gaussianProduct) (xClass h) (-yClass h)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w => starRingEnd ℂ (zValue h w) := by
  filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct) (xClass h) (-yClass h),
    Lp.coeFn_neg (yClass h), (coordinates_ae h).1, (coordinates_ae h).2] with w hc hn hx hy
  rw [hc, hn]
  simp only [Pi.neg_apply]
  rw [hx, hy]
  simp [zValue]

/-- All polynomial first holomorphic moments vanish, with actual Gaussian L2
representatives and integrals; no formal Gaussian averaging is substituted. -/
theorem polynomial_first_moment (h : CoefficientSpace) (p : Polynomial ℂ) :
    (∫ w, zValue h w * p.eval (zValue h w) ∂gaussianProduct.prod gaussianProduct) = 0 := by
  have hg := polynomial_graphs h p
  have hs := (analytic_stein h _ _ _ _ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).1
  have he : (∫ w, zValue h w * p.eval (zValue h w) ∂gaussianProduct.prod gaussianProduct) =
      inner ℂ (combine (gaussianProduct.prod gaussianProduct) (xClass h) (-yClass h))
        (polynomialValue h p) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [conjugate_coordinate_ae h, polynomial_value_ae h p] with w hz hp
    change polynomialValue h p w = p.eval (zValue h w) at hp
    rw [hz, hp]
    simp only [RCLike.inner_apply, Complex.conj_conj]
    exact mul_comm _ _
  exact he.trans hs

theorem polynomial_mean (h : CoefficientSpace) (p : Polynomial ℂ) :
    (∫ w, p.eval (zValue h w) ∂gaussianProduct.prod gaussianProduct) = p.eval 0 := by
  have hint (q : Polynomial ℂ) : Integrable (fun w => q.eval (zValue h w))
      (gaussianProduct.prod gaussianProduct) :=
    (polynomial_memLp h q).integrable (by norm_num)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp_rw [Polynomial.eval_add]
    rw [integral_add (hint p) (hint q), hp, hq]
  | monomial n c =>
    cases n with
    | zero => simp
    | succ n =>
      have hi := polynomial_first_moment h (Polynomial.X ^ n)
      simp only [Polynomial.eval_pow, Polynomial.eval_X] at hi
      have hm : (∫ w, (zValue h w) ^ (n+1) ∂gaussianProduct.prod gaussianProduct) = 0 := by
        convert hi using 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun w => by ring)
      simp only [Polynomial.eval_monomial]
      rw [integral_const_mul, hm]
      simp

theorem polynomial_center (h : CoefficientSpace) (p : Polynomial ℂ) :
    complexCenter (polynomialValue h p) = polynomialValue h p - p.eval 0 • complexOne := by
  have hm : (∫ w, polynomialValue h p w ∂gaussianProduct.prod gaussianProduct) = p.eval 0 :=
    (integral_congr_ae (polynomial_value_ae h p)).trans (polynomial_mean h p)
  rw [complexCenter_apply, hm]

theorem polynomial_conjugate_moment (h : CoefficientSpace) (p : Polynomial ℂ) :
    (∫ w, starRingEnd ℂ (zValue h w) * p.eval (zValue h w)
      ∂gaussianProduct.prod gaussianProduct) =
      ((2 * ‖h‖ ^ 2 : ℝ) : ℂ) * p.derivative.eval 0 := by
  have hg := polynomial_graphs h p
  have hs := (analytic_stein h _ _ _ _ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).2
  have hz : combine (gaussianProduct.prod gaussianProduct) (xClass h) (yClass h)
      =ᵐ[gaussianProduct.prod gaussianProduct] zValue h := by
    filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct) (xClass h) (yClass h),
      (coordinates_ae h).1, (coordinates_ae h).2] with w hc hx hy
    rw [hc, hx, hy]
    rfl
  have he : (∫ w, starRingEnd ℂ (zValue h w) * p.eval (zValue h w)
      ∂gaussianProduct.prod gaussianProduct) =
      inner ℂ (combine (gaussianProduct.prod gaussianProduct) (xClass h) (yClass h))
        (polynomialValue h p) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hz, polynomial_value_ae h p] with w hz hp
    change polynomialValue h p w = p.eval (zValue h w) at hp
    rw [hz, hp]
    simp only [RCLike.inner_apply]
    exact mul_comm _ _
  rw [he, polynomialValue, hs, complexOne_inner]
  have hm : (∫ w, combine (gaussianProduct.prod gaussianProduct) (realSlope h p)
      (imagSlope h p) w ∂gaussianProduct.prod gaussianProduct) = p.derivative.eval 0 :=
    (integral_congr_ae (slope_value_ae h p)).trans (polynomial_mean h p.derivative)
  rw [hm]

/-- Actual native terminal representation with the deterministic initial value.
This does not yet identify its running input with p'(Z_t). -/
theorem terminal_polynomial_initial_reconstruction (T : ℝ≥0) (p : Polynomial ℂ) :
    ∃ u : ComplexInput T, channel T false u =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => p.eval ((GaussianTimeProcess.process T w.1 : ℂ) +
        Complex.I * (GaussianTimeProcess.process T w.2 : ℂ)) - p.eval 0 := by
  let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
    (GaussianTimeHilbert.timeVector T)
  obtain ⟨u, hu⟩ := terminal_polynomial_reconstruction T p
  refine ⟨u, ?_⟩
  change channel T false u =ᵐ[gaussianProduct.prod gaussianProduct]
    (fun w => p.eval (zValue h w) - ∫ x, p.eval (zValue h x)
      ∂gaussianProduct.prod gaussianProduct) at hu
  change channel T false u =ᵐ[gaussianProduct.prod gaussianProduct]
    (fun w => p.eval (zValue h w) - p.eval 0)
  simpa only [polynomial_mean] using hu

end OperatorDerivativeRewrite.Foundation.StochasticCauchyGaussianStein
