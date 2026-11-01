import Foundation.StochasticCauchyMeanResidual
import Foundation.GaussianExponentialSobolevObstruction
import Foundation.StochasticCauchyGaussianNormalization
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Actual complex Gaussian exponentials: dominated strong L2 Taylor limits
and their original closed partial derivative graphs. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyExponential
open InfiniteGaussian ProductL2Curry ComplexL2Isometry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPastReconstruction StochasticCauchyComplexChannels
open StochasticCauchyMalliavinBridge StochasticCauchyCausalRotation
open StochasticCauchyPolynomials StochasticCauchyMeanResidual
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete GaussianTimeHilbert.timeHilbert_secondCountable

def coordinate (h : CoefficientSpace) (w : SampleSpace × SampleSpace) : ℂ :=
  (firstChaosEmbedding h w.1:ℂ)+Complex.I*(firstChaosEmbedding h w.2:ℂ)

theorem coordinate_measurable (h : CoefficientSpace) : Measurable (coordinate h) := by
  have hW : Measurable (firstChaosEmbedding h) := (Lp.stronglyMeasurable _).measurable
  unfold coordinate
  fun_prop

theorem coordinate_norm_le (h : CoefficientSpace) (w : SampleSpace × SampleSpace) :
    ‖coordinate h w‖ ≤ |firstChaosEmbedding h w.1|+|firstChaosEmbedding h w.2| := by
  calc
    _ ≤ ‖(firstChaosEmbedding h w.1:ℂ)‖+‖Complex.I*(firstChaosEmbedding h w.2:ℂ)‖ := norm_add_le _ _
    _ = _ := by simp [norm_mul,Complex.norm_real,Real.norm_eq_abs]

private theorem real_exp_memLp (h : CoefficientSpace) (a : ℝ) :
    MemLp (fun w => Real.exp (a*firstChaosEmbedding h w)) 2 gaussianProduct := by
  let v : ℝ≥0 := ⟨‖h‖^2,sq_nonneg _⟩
  have hl : HasLaw (firstChaosEmbedding h) (gaussianReal 0 v) gaussianProduct :=
    ⟨(Lp.stronglyMeasurable _).aemeasurable,firstChaos_law h⟩
  have hg : MemLp (fun x : ℝ => Real.exp (a*x)) 2 (gaussianReal 0 v) := by
    rw [← integrable_norm_rpow_iff (by fun_prop) (by simp) (by simp)]
    convert integrable_exp_mul_gaussianReal (μ := 0) (v := v) (2*a) using 1
    funext x
    simp only [ENNReal.toReal_ofNat,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.rpow_two]
    rw [sq,← Real.exp_add]
    congr 1
    ring
  exact hl.memLp_comp hg

theorem absolute_exp_memLp (h : CoefficientSpace) :
    MemLp (fun w => Real.exp |firstChaosEmbedding h w|) 2 gaussianProduct := by
  have hW : Measurable (firstChaosEmbedding h) := (Lp.stronglyMeasurable _).measurable
  apply ((real_exp_memLp h 1).add (real_exp_memLp h (-1))).mono' (by fun_prop)
  apply Eventually.of_forall
  intro w
  simp only [one_mul,neg_one_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Pi.add_apply]
  by_cases hw : 0 ≤ firstChaosEmbedding h w
  · rw [abs_of_nonneg hw]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos (le_of_not_ge hw)]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

private def absoluteClass (h : CoefficientSpace) : GaussianL2 :=
  (absolute_exp_memLp h).toLp (fun w => Real.exp |firstChaosEmbedding h w|)

def envelope (h : CoefficientSpace) (w : SampleSpace × SampleSpace) : ℝ :=
  Real.exp (|firstChaosEmbedding h w.1|+|firstChaosEmbedding h w.2|)

theorem envelope_memLp (h : CoefficientSpace) :
    MemLp (envelope h) 2 (gaussianProduct.prod gaussianProduct) := by
  have ha : (absoluteClass h) =ᵐ[gaussianProduct] fun w => Real.exp |firstChaosEmbedding h w| :=
    (absolute_exp_memLp h).coeFn_toLp
  have hx := (Measure.quasiMeasurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp ha
  have hy := (Measure.quasiMeasurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp ha
  apply (Lp.memLp (productTensor gaussianProduct gaussianProduct (absoluteClass h) (absoluteClass h))).ae_eq
  filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct (absoluteClass h) (absoluteClass h),hx,hy] with w ht hx hy
  simp only [Function.comp_apply] at hx hy
  rw [ht,hx,hy]
  simp only [envelope,Real.exp_add,smul_eq_mul]

private theorem exp_norm_bound (h : CoefficientSpace) (w : SampleSpace × SampleSpace) :
    ‖Complex.exp (coordinate h w)‖ ≤ envelope h w := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (coordinate_norm_le h w))

theorem exponential_memLp (h : CoefficientSpace) :
    MemLp (fun w => Complex.exp (coordinate h w)) 2 (gaussianProduct.prod gaussianProduct) := by
  have hm := coordinate_measurable h
  apply (envelope_memLp h).mono' (by fun_prop)
  apply Eventually.of_forall
  intro w
  simpa only [envelope,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using exp_norm_bound h w

def exponential (h : CoefficientSpace) : JointComplex :=
  (exponential_memLp h).toLp (fun w => Complex.exp (coordinate h w))

theorem exponential_ae (h : CoefficientSpace) : exponential h =ᵐ[gaussianProduct.prod gaussianProduct]
    fun w => Complex.exp (coordinate h w) := (exponential_memLp h).coeFn_toLp

def approximation (N : ℕ) : Polynomial ℂ :=
  (GaussianExponentialSobolevObstruction.taylorPolynomial 1 N).map (algebraMap ℝ ℂ)

theorem approximation_derivative (N : ℕ) : (approximation (N+1)).derivative=approximation N := by
  simp only [approximation,Polynomial.derivative_map,GaussianExponentialSobolevObstruction.taylor_derivative,one_smul]

theorem approximation_eval (N : ℕ) (z : ℂ) :
    (approximation N).eval z=∑ n ∈ Finset.range N,z^n/(n.factorial:ℂ) := by
  simp only [approximation,Polynomial.eval_map,GaussianExponentialSobolevObstruction.taylorPolynomial,
    Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,one_pow,one_div,map_inv₀,map_natCast]
  apply Finset.sum_congr rfl
  intro n hn
  rw [div_eq_mul_inv,mul_comm]

private theorem real_series (x : ℝ) : HasSum (fun n : ℕ => x^n/(n.factorial:ℝ)) (Real.exp x) := by
  simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

private theorem complex_series (z : ℂ) : HasSum (fun n : ℕ => z^n/(n.factorial:ℂ)) (Complex.exp z) := by
  simpa only [← Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z

theorem approximation_bound (N : ℕ) (z : ℂ) : ‖(approximation N).eval z‖ ≤ Real.exp ‖z‖ := by
  rw [approximation_eval]
  have hs := real_series ‖z‖
  calc
    _ ≤ ∑ n ∈ Finset.range N,‖z^n/(n.factorial:ℂ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N,‖z‖^n/(n.factorial:ℝ) := by simp [norm_div,norm_pow]
    _ ≤ ∑' n : ℕ,‖z‖^n/(n.factorial:ℝ) := hs.summable.sum_le_tsum _ (fun n _ => by positivity)
    _ = _ := hs.tsum_eq

/-- Strong L2 convergence on the actual original product law, including zero
variance; neither pointwise convergence alone nor an abstract completion. -/
theorem approximation_tendsto (h : CoefficientSpace) :
    Tendsto (fun N => polynomialValue h (approximation N)) atTop (𝓝 (exponential h)) := by
  let fN := fun N w => (approximation N).eval (coordinate h w)
  have hm := coordinate_measurable h
  have hp (N : ℕ) : MemLp (fN N) 2 (gaussianProduct.prod gaussianProduct) := polynomial_memLp h _
  have hc : UnifIntegrable (fun _ : ℕ => fun w => (envelope h w:ℂ)) 2 (gaussianProduct.prod gaussianProduct) :=
    unifIntegrable_const (by norm_num) (by simp) (envelope_memLp h).ofReal
  have hui : UnifIntegrable fN 2 (gaussianProduct.prod gaussianProduct) := by
    apply hc.ae_mono (fun N => (hp N).aestronglyMeasurable)
    intro N
    apply Eventually.of_forall
    intro w
    rw [enorm_le_iff_norm_le]
    have hb := (approximation_bound N (coordinate h w)).trans
      (Real.exp_le_exp.mpr (coordinate_norm_le h w))
    simpa only [fN,envelope,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hb
  have ht (w : SampleSpace × SampleSpace) : Tendsto (fun N => fN N w) atTop
      (𝓝 (Complex.exp (coordinate h w))) := by
    simpa only [fN,approximation_eval] using (complex_series (coordinate h w)).tendsto_sum_nat
  have hd := tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1:ℝ≥0∞)≤2) (by simp : (2:ℝ≥0∞)≠∞)
    (fun N => (hp N).aestronglyMeasurable) (exponential_memLp h) hui (Eventually.of_forall ht)
  have hh := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fN hp (fun w => Complex.exp (coordinate h w)) (exponential_memLp h)).2 hd
  have he (N : ℕ) : (hp N).toLp (fN N)=polynomialValue h (approximation N) := by
    apply Lp.ext
    exact (hp N).coeFn_toLp.trans (polynomial_value_ae h (approximation N)).symm
  simpa only [he,exponential] using hh

/-- Genuine matched product Gaussian law, including zero variance. -/
theorem coordinate_hasLaw (h : CoefficientSpace) : HasLaw (coordinate h)
    (StochasticCauchyGaussianNormalization.complexLaw ⟨‖h‖^2,sq_nonneg _⟩)
      (gaussianProduct.prod gaussianProduct) := by
  let v : ℝ≥0 := ⟨‖h‖^2,sq_nonneg _⟩
  have hm : MeasurePreserving (firstChaosEmbedding h) gaussianProduct (gaussianReal 0 v) :=
    ⟨(Lp.stronglyMeasurable _).measurable,firstChaos_law h⟩
  have hp := hm.prod hm
  have hl : HasLaw (Prod.map (firstChaosEmbedding h) (firstChaosEmbedding h))
      (StochasticCauchyGaussianNormalization.law v) (gaussianProduct.prod gaussianProduct) :=
    ⟨hp.measurable.aemeasurable,hp.map_eq⟩
  change HasLaw (StochasticCauchyGaussianNormalization.z ∘
    Prod.map (firstChaosEmbedding h) (firstChaosEmbedding h))
      (StochasticCauchyGaussianNormalization.complexLaw v) (gaussianProduct.prod gaussianProduct)
  exact (StochasticCauchyGaussianNormalization.hasLaw_z v).comp hl

theorem exponential_mean (h : CoefficientSpace) :
    (∫ w,exponential h w ∂gaussianProduct.prod gaussianProduct)=1 := by
  rw [integral_congr_ae (exponential_ae h)]
  exact StochasticCauchyGaussianNormalization.exponential_mean_of_hasLaw _ (coordinate_hasLaw h)

theorem centered_exponential_ae (h : CoefficientSpace) :
    complexCenter (exponential h) =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      Complex.exp (coordinate h w)-1 := by
  have hc := complexCenter_ae (exponential h)
  rw [exponential_mean] at hc
  filter_upwards [hc,exponential_ae h] with w hc he
  rw [hc,he]

theorem centered_exponential_energy (h : CoefficientSpace) :
    ‖complexCenter (exponential h)‖^2=Real.exp (2*‖h‖^2)-1 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  have he : (∫ w,‖complexCenter (exponential h) w‖^2 ∂gaussianProduct.prod gaussianProduct)=
      ∫ w,‖Complex.exp (coordinate h w)-1‖^2 ∂gaussianProduct.prod gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [centered_exponential_ae h] with w hw
    rw [hw]
  rw [he]
  exact StochasticCauchyGaussianNormalization.centered_energy_of_hasLaw _ (coordinate_hasLaw h)

private theorem component_tendsto (h : CoefficientSpace) :
    Tendsto (fun N => realPolynomial h (approximation N)) atTop
      (𝓝 (realPart (gaussianProduct.prod gaussianProduct) (exponential h))) ∧
    Tendsto (fun N => imagPolynomial h (approximation N)) atTop
      (𝓝 (imagPart (gaussianProduct.prod gaussianProduct) (exponential h))) := by
  constructor
  · simpa only [Function.comp_def,polynomialValue,realPart_combine] using
      (realPart (gaussianProduct.prod gaussianProduct)).continuous.continuousAt.tendsto.comp (approximation_tendsto h)
  · simpa only [Function.comp_def,polynomialValue,imagPart_combine] using
      (imagPart (gaussianProduct.prod gaussianProduct)).continuous.continuousAt.tendsto.comp (approximation_tendsto h)

private theorem slopes (h : CoefficientSpace) (N : ℕ) :
    realSlope h (approximation (N+1))=realPolynomial h (approximation N) ∧
    imagSlope h (approximation (N+1))=imagPolynomial h (approximation N) := by
  have he := slope_value_ae h (approximation (N+1))
  rw [approximation_derivative] at he
  have hh : combine (gaussianProduct.prod gaussianProduct)
      (realSlope h (approximation (N+1))) (imagSlope h (approximation (N+1)))=
      polynomialValue h (approximation N) :=
    Lp.ext (he.trans (polynomial_value_ae h (approximation N)).symm)
  constructor
  · simpa only [polynomialValue,realPart_combine] using congrArg (realPart (gaussianProduct.prod gaussianProduct)) hh
  · simpa only [polynomialValue,imagPart_combine] using congrArg (imagPart (gaussianProduct.prod gaussianProduct)) hh

attribute [local irreducible] sourceDerivative directionField

/-- All FOUR ORIGINAL full partial graphs, obtained from simultaneous strong
limits of targets AND derivative coefficients, with physical Y exchange. -/
theorem exponential_graphs (h : CoefficientSpace) :
    let R := realPart (gaussianProduct.prod gaussianProduct) (exponential h)
    let J := imagPart (gaussianProduct.prod gaussianProduct) (exponential h)
    (R,directionField h R) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct R,-directionField h (swap gaussianProduct gaussianProduct J)) ∈ sourceDerivative.graph ∧
    (J,directionField h J) ∈ sourceDerivative.graph ∧
    (swap gaussianProduct gaussianProduct J,directionField h (swap gaussianProduct gaussianProduct R)) ∈ sourceDerivative.graph := by
  dsimp only
  have hr := (component_tendsto h).1
  have hi := (component_tendsto h).2
  have hrs := hr.comp (tendsto_add_atTop_nat 1)
  have his := hi.comp (tendsto_add_atTop_nat 1)
  have hsr := (swap gaussianProduct gaussianProduct).continuous.continuousAt.tendsto.comp hr
  have hsi := (swap gaussianProduct gaussianProduct).continuous.continuousAt.tendsto.comp hi
  have hdir := (directionField h).continuous
  have hswap := (swap gaussianProduct gaussianProduct).continuous
  have hc : IsClosed (sourceDerivative.graph : Set (JointL2 × DerivativeField)) := sourceDerivative_closed
  refine ⟨hc.mem_of_tendsto (hrs.prodMk_nhds ((hdir.tendsto _).comp hr)) ?_,
    hc.mem_of_tendsto (((hswap.tendsto _).comp hrs).prodMk_nhds ((hdir.tendsto _).comp hsi).neg) ?_,
    hc.mem_of_tendsto (his.prodMk_nhds ((hdir.tendsto _).comp hi)) ?_,
    hc.mem_of_tendsto (((hswap.tendsto _).comp his).prodMk_nhds ((hdir.tendsto _).comp hsr)) ?_⟩
  all_goals
    apply Eventually.of_forall
    intro N
  · simpa only [SetLike.mem_coe,Function.comp_apply,(slopes h N).1] using (polynomial_graphs h (approximation (N+1))).1
  · simpa only [SetLike.mem_coe,Function.comp_apply,(slopes h N).2] using (polynomial_graphs h (approximation (N+1))).2.1
  · simpa only [SetLike.mem_coe,Function.comp_apply,(slopes h N).2] using (polynomial_graphs h (approximation (N+1))).2.2.1
  · simpa only [SetLike.mem_coe,Function.comp_apply,(slopes h N).1] using (polynomial_graphs h (approximation (N+1))).2.2.2

/-- Raw actual exponential projections on the checked observed coefficient
class; continuity is used in the actual strong L2 topology. -/
theorem exponential_projections (T : ℝ≥0) (h : CoefficientSpace)
    (ha : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] (firstChaosEmbedding h) gaussianProduct) :
    cauchyProjection T false (exponential h)=complexCenter (exponential h) ∧
    cauchyProjection T true (exponential h)=0 := by
  have ht := approximation_tendsto h
  have hp (N : ℕ) := polynomial_raw_projections T h (approximation N) ha
  constructor
  · have hc := complexCenter.continuous.continuousAt.tendsto.comp ht
    have he : (fun N => cauchyProjection T false (polynomialValue h (approximation N)))=
        (fun N => complexCenter (polynomialValue h (approximation N))) := funext (fun N => (hp N).1)
    simp only [Function.comp_def] at hc
    rw [← he] at hc
    exact tendsto_nhds_unique ((cauchyProjection T false).continuous.continuousAt.tendsto.comp ht) hc
  · have he : (fun N => cauchyProjection T true (polynomialValue h (approximation N)))=(fun _ => 0) :=
      funext (fun N => (hp N).2)
    have hc : Tendsto (fun N => cauchyProjection T true (polynomialValue h (approximation N))) atTop (𝓝 0) := by
      rw [he]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique ((cauchyProjection T true).continuous.continuousAt.tendsto.comp ht) hc

theorem exponential_integrand_energy (T : ℝ≥0) (h : CoefficientSpace)
    (ha : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] (firstChaosEmbedding h) gaussianProduct) :
    ‖channelAdjoint T false (exponential h)‖^2=Real.exp (2*‖h‖^2)-1 := by
  rw [← (channel T false).norm_map]
  change ‖cauchyProjection T false (exponential h)‖^2=_
  rw [(exponential_projections T h ha).1,centered_exponential_energy]

/-- Native stochastic reconstruction of the actual unbounded exponential, with
mean1. This does NOT identify the temporal representative of its integrand. -/
theorem terminal_exponential_reconstruction (T : ℝ≥0) :
    ∃ u : ComplexInput T,channel T false u =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      Complex.exp ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))-1 := by
  let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
    (GaussianTimeHilbert.timeVector T)
  have hp := exponential_projections T h (GaussianTimeProcess.process_stronglyAdapted T).aestronglyMeasurable
  refine ⟨channelAdjoint T false (exponential h),?_⟩
  change cauchyProjection T false (exponential h) =ᵐ[gaussianProduct.prod gaussianProduct] _
  rw [hp.1]
  exact centered_exponential_ae h

/-- The raw normalized Cauchy projection of the actual terminal exponential. -/
theorem terminal_exponential_cauchy (T : ℝ≥0) :
    let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector T)
    (cauchyProjection T false (exponential h) =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
      Complex.exp ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))-1) ∧
    cauchyProjection T true (exponential h)=0 := by
  dsimp only
  let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
    (GaussianTimeHilbert.timeVector T)
  have hp := exponential_projections T h (GaussianTimeProcess.process_stronglyAdapted T).aestronglyMeasurable
  refine ⟨?_,hp.2⟩
  rw [hp.1]
  exact centered_exponential_ae h

theorem terminal_exponential_energy (T : ℝ≥0) :
    let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector T)
    ‖complexCenter (exponential h)‖^2=Real.exp (2*(T:ℝ))-1 := by
  dsimp only
  rw [centered_exponential_energy,LinearIsometry.norm_map,← real_inner_self_eq_norm_sq,GaussianTimeHilbert.timeVector_inner,min_self]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyExponential
