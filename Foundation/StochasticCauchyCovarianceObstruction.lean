import Foundation.StochasticCauchyMalliavinBridge
import Foundation.GaussianPolynomialProcess
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Martingale.Basic

/-! Independence is not isotropy: actual anisotropic Gaussian paths and stochastic channel Gram terms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyCovarianceObstruction
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels ComplexL2Isometry StochasticCauchyPastReconstruction
attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete

def stretch (a : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM + (Complex.I*(a : ℂ)) • (Complex.ofRealCLM.comp Complex.imCLM)

def value (a : ℝ) (t : ℝ≥0) (w : IBMSourceLaws.JointSample) : ℂ :=
  stretch a (StochasticCauchyBrownianRealization.value t w)

theorem value_re (a : ℝ) (t : ℝ≥0) (w : IBMSourceLaws.JointSample) :
    (value a t w).re=(StochasticCauchyBrownianRealization.value t w).re := by
  simp [value,stretch]

theorem value_im (a : ℝ) (t : ℝ≥0) (w : IBMSourceLaws.JointSample) :
    (value a t w).im=a*(StochasticCauchyBrownianRealization.value t w).im := by
  simp [value,stretch]

theorem value_continuous (a : ℝ) (w : IBMSourceLaws.JointSample) : Continuous (fun t => value a t w) :=
  (stretch a).continuous.comp (StochasticCauchyBrownianRealization.value_continuous w)

theorem value_measurable (a : ℝ) (t : ℝ≥0) : Measurable (value a t) :=
  (stretch a).measurable.comp (StochasticCauchyBrownianRealization.value_measurable t)

theorem value_gaussian (a : ℝ) : IsGaussianProcess (value a) IBMSourceLaws.jointMeasure :=
  StochasticCauchyBrownianRealization.isGaussianProcess.comp_left (fun _ => stretch a)

theorem components_independent (a : ℝ) :
    IndepFun (fun w : IBMSourceLaws.JointSample => fun t => (value a t w).re)
      (fun w : IBMSourceLaws.JointSample => fun t => (value a t w).im) IBMSourceLaws.jointMeasure := by
  have hm : Measurable (fun f : ℝ≥0 → ℝ => fun t => a*f t) :=
    Measurable.of_eval fun t => measurable_const.mul (measurable_pi_apply t)
  simpa only [Function.comp_def,id_eq,value_re,value_im] using
    StochasticCauchyBrownianRealization.components_independent.comp measurable_id hm

theorem real_covariance (a : ℝ) (s t : ℝ≥0) :
    cov[(fun w => (value a s w).re),(fun w => (value a t w).re); IBMSourceLaws.jointMeasure]=
      (min s t : ℝ≥0) := by
  simp only [value_re]
  exact StochasticCauchyBrownianRealization.real_isBrownian.toIsPreBrownianReal.covariance_fun_eval s t

theorem imag_covariance (a : ℝ) (s t : ℝ≥0) :
    cov[(fun w => (value a s w).im),(fun w => (value a t w).im); IBMSourceLaws.jointMeasure]=
      a^2*(min s t : ℝ≥0) := by
  simp only [value_im]
  change cov[a • (fun w => (StochasticCauchyBrownianRealization.value s w).im),
    a • (fun w => (StochasticCauchyBrownianRealization.value t w).im); IBMSourceLaws.jointMeasure]=_
  rw [covariance_smul_left,covariance_smul_right,
    StochasticCauchyBrownianRealization.imag_isBrownian.toIsPreBrownianReal.covariance_fun_eval]
  ring

/-- The complete Hermitian Gram term of the ACTUAL stochastic maps. -/
theorem raw_pairing (T : ℝ≥0) (c d : ℂ) (u v : ComplexInput T) :
    inner ℂ (rawChannel T c u) (rawChannel T d v)=
      (1+star c*d)*inner ℂ u v := by
  have hyx : inner ℂ (integralYComplex T u) (integralXComplex T v)=0 :=
    (inner_eq_zero_symm).mp (complex_sources_orthogonal T v u)
  change inner ℂ (integralXComplex T u+c • integralYComplex T u)
    (integralXComplex T v+d • integralYComplex T v)=_
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    complex_sources_orthogonal,hyx,mul_zero,add_zero,zero_add,
    (integralXComplex T).inner_map_map,(integralYComplex T).inner_map_map]
  change inner ℂ u v + d*(star c*inner ℂ u v) = _
  ring

/-- Conjugate noises are orthogonal only with matched source metric. -/
theorem conjugate_pairing (T : ℝ≥0) (a : ℝ) (u v : ComplexInput T) :
    inner ℂ (rawChannel T (Complex.I*(a : ℂ)) u) (rawChannel T (-Complex.I*(a : ℂ)) v)=
      ((1-a^2 : ℝ) : ℂ)*inner ℂ u v := by
  rw [raw_pairing]
  simp only [star_mul,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
  push_cast
  ring_nf
  simp [Complex.I_sq]

private theorem one_past (s : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration s] gaussianOne gaussianProduct :=
  aestronglyMeasurable_const.congr gaussianOne_coeFn.symm

/-- The actual constant predictable integrand on(0,T], not an assumed nonzero vector. -/
def constantInput (T : ℝ≥0) : ComplexInput T :=
  combineInput T (stepInput T 0 T (by positivity) le_rfl gaussianOne gaussianOne (one_past 0) (one_past 0)) 0

theorem constantInput_energy (T : ℝ≥0) : ‖constantInput T‖^2=(T : ℝ) := by
  have ho : ‖gaussianOne‖^2=(1 : ℝ) := by
    rw [← GaussianPolynomialProcess.brownianCore_zero_degree (0 : ℝ≥0),
      GaussianTimeSpaceHermite.brownianCore_norm_sq]
    norm_num
  rw [constantInput,input_norm_sq,realInput_combine,imagInput_combine,stepInput_energy,ho]
  simp

theorem constant_conjugate_pairing (T : ℝ≥0) (a : ℝ) :
    inner ℂ (rawChannel T (Complex.I*(a : ℂ)) (constantInput T))
      (rawChannel T (-Complex.I*(a : ℂ)) (constantInput T)) = ((1-a^2)*(T : ℝ) : ℝ) := by
  rw [conjugate_pairing,inner_self_eq_norm_sq_to_K]
  norm_cast
  rw [constantInput_energy]
  push_cast
  rfl

/-- Sharp condition, including negative source orientation, at EVERY positive horizon. -/
theorem conjugate_orthogonal_iff (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    (∀ u v : ComplexInput T,
      inner ℂ (rawChannel T (Complex.I*(a : ℂ)) u) (rawChannel T (-Complex.I*(a : ℂ)) v)=0) ↔
      a^2=1 := by
  constructor
  · intro h
    have he := h (constantInput T) (constantInput T)
    rw [constant_conjugate_pairing] at he
    have hr : (1-a^2)*(T : ℝ)=0 := by exact_mod_cast he
    have ht : (T : ℝ) ≠ 0 := ne_of_gt hT
    exact sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right ht) |>.symm
  · intro ha u v
    rw [conjugate_pairing,ha,sub_self,Complex.ofReal_zero,zero_mul]

/-- Covariance-weighted orthogonal complement: reciprocal scale, not conjugation. -/
theorem reciprocal_orthogonal (T : ℝ≥0) (a : ℝ) (ha : a ≠ 0) (u v : ComplexInput T) :
    inner ℂ (rawChannel T (Complex.I*(a : ℂ)) u)
      (rawChannel T (-Complex.I*((a⁻¹ : ℝ) : ℂ)) v)=0 := by
  rw [raw_pairing]
  have h : (1+star (Complex.I*(a : ℂ))*(-Complex.I*((a⁻¹ : ℝ) : ℂ)))=0 := by
    simp only [star_mul,Complex.star_def,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_inv]
    have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    field_simp
    simp [Complex.I_sq]
  rw [h,zero_mul]

/-- Correct energy includes the covariance cross term unless the source scales match. -/
theorem conjugate_sum_energy (T : ℝ≥0) (a : ℝ) (u v : ComplexInput T) :
    ‖rawChannel T (Complex.I*(a : ℂ)) u + rawChannel T (-Complex.I*(a : ℂ)) v‖^2 =
      (1+a^2)*(‖u‖^2+‖v‖^2)+2*(1-a^2)*(inner ℂ u v).re := by
  rw [norm_add_sq (𝕜 := ℂ),rawChannel_energy,rawChannel_energy,conjugate_pairing]
  have hr : RCLike.re (((1-a^2 : ℝ) : ℂ)*inner ℂ u v)=(1-a^2)*(inner ℂ u v).re := by
    change (((1-a^2 : ℝ) : ℂ)*inner ℂ u v).re = _
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hr]
  simp only [norm_mul,Complex.norm_I,norm_neg,one_mul,Complex.norm_real,Real.norm_eq_abs,
    sq_abs,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- Conjugate channels still reconstruct at every nonzero scale; they need not be orthogonal. -/
theorem conjugate_reconstruction (T : ℝ≥0) (a : ℝ) (ha : a ≠ 0) (u v : ComplexInput T) :
    rawChannel T (Complex.I*(a : ℂ))
      ((2 : ℂ)⁻¹ • (u-(Complex.I*((a⁻¹ : ℝ) : ℂ)) • v)) +
    rawChannel T (-Complex.I*(a : ℂ))
      ((2 : ℂ)⁻¹ • (u+(Complex.I*((a⁻¹ : ℝ) : ℂ)) • v)) =
      integralXComplex T u+integralYComplex T v := by
  change integralXComplex T ((2 : ℂ)⁻¹ • (u-(Complex.I*((a⁻¹ : ℝ) : ℂ)) • v)) +
    (Complex.I*(a : ℂ)) • integralYComplex T ((2 : ℂ)⁻¹ • (u-(Complex.I*((a⁻¹ : ℝ) : ℂ)) • v)) +
    (integralXComplex T ((2 : ℂ)⁻¹ • (u+(Complex.I*((a⁻¹ : ℝ) : ℂ)) • v)) +
    (-Complex.I*(a : ℂ)) • integralYComplex T ((2 : ℂ)⁻¹ • (u+(Complex.I*((a⁻¹ : ℝ) : ℂ)) • v))) = _
  simp only [map_smul,map_sub,map_add,smul_add,smul_sub,smul_smul,Complex.ofReal_inv]
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  match_scalars <;> field_simp <;> norm_num [Complex.I_sq] <;> ring

theorem raw_real_input (T : ℝ≥0) (a : ℝ) (u : Input T) :
    rawChannel T (Complex.I*(a : ℂ)) (combineInput T u 0)=
      combine (gaussianProduct.prod gaussianProduct) (integralX T u) (a • integralY T u) := by
  change integralXComplex T (combineInput T u 0) +
    (Complex.I*(a : ℂ)) • integralYComplex T (combineInput T u 0) = _
  unfold integralXComplex integralYComplex
  rw [liftInput_combine,liftInput_combine,map_zero,map_zero]
  simp only [combine,map_zero,smul_zero,add_zero,map_smul]
  change _ = ofReal _ (integralX T u)+Complex.I • ((a : ℂ) • ofReal _ (integralY T u))
  rw [smul_smul]

private theorem increment_one (T : ℝ≥0) :
    GaussianPastStepCompletion.pastIncrement 0 T (by positivity) gaussianOne (one_past 0)=wienerL2 T := by
  apply Lp.ext
  have hz : process 0 =ᵐ[gaussianProduct] fun _ => 0 := by
    change (wienerL2 0 : SampleSpace → ℝ) =ᵐ[gaussianProduct] _
    rw [wienerL2_zero]
    exact Lp.coeFn_zero ℝ 2 gaussianProduct
  filter_upwards [GaussianPastStepCompletion.pastIncrement_coeFn 0 T (by positivity)
    gaussianOne (one_past 0),gaussianOne_coeFn,hz] with w hi hone hz
  change _=process T w
  simpa only [hone,hz,sub_zero,one_mul] using hi

/-- Exact stochastic-step agreement with the ACTUAL continuous anisotropic Gaussian process. -/
theorem constant_raw_ae (a : ℝ) (T : ℝ≥0) :
    rawChannel T (Complex.I*(a : ℂ)) (constantInput T) =ᵐ[IBMSourceLaws.jointMeasure] value a T := by
  rw [constantInput,raw_real_input,integralX_stepInput,integralY_stepInput,increment_one]
  have hx := (Measure.quasiMeasurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp
    (IBMConstructedSources.clockPath_coordinate_ae T)
  have hy := (Measure.quasiMeasurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp
    (IBMConstructedSources.clockPath_coordinate_ae T)
  have ho1 := (Measure.quasiMeasurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp gaussianOne_coeFn
  have ho2 := (Measure.quasiMeasurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp gaussianOne_coeFn
  filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct)
      (ProductL2Curry.productTensor gaussianProduct gaussianProduct (wienerL2 T) gaussianOne)
      (a • ProductL2Curry.productTensor gaussianProduct gaussianProduct gaussianOne (wienerL2 T)),
    Lp.coeFn_smul a (ProductL2Curry.productTensor gaussianProduct gaussianProduct gaussianOne (wienerL2 T)),
    ProductL2Curry.productTensor_coeFn gaussianProduct gaussianProduct (wienerL2 T) gaussianOne,
    ProductL2Curry.productTensor_coeFn gaussianProduct gaussianProduct gaussianOne (wienerL2 T),hx,hy,ho1,ho2]
    with w hc hs hp hq hx hy ho1 ho2
  simp only [Function.comp_apply] at hx hy ho1 ho2
  simp only [Pi.smul_apply] at hs
  rw [hc,hs,hp,hq,ho1,ho2]
  simp only [Pi.smul_apply,smul_eq_mul,one_mul,mul_one]
  simp [value,stretch,StochasticCauchyBrownianRealization.value_eq,hx,hy,process]
  ring

theorem value_neg_scale (a : ℝ) (T : ℝ≥0) (w : IBMSourceLaws.JointSample) :
    value (-a) T w=star (value a T w) := by
  apply Complex.ext <;> simp [value_re,value_im,Complex.star_def]

theorem square_integrable (a : ℝ) (T : ℝ≥0) :
    Integrable (fun w => value a T w^2) IBMSourceLaws.jointMeasure := by
  have h := ((value_gaussian a).hasGaussianLaw_eval T).memLp_two
  exact (h.integrable_mul h).congr (Eventually.of_forall fun w => (pow_two (value a T w)).symm)

/-- The true analytic quadratic moment exposes the unmatched covariance drift. -/
theorem square_mean (a : ℝ) (T : ℝ≥0) :
    (∫ w, value a T w^2 ∂IBMSourceLaws.jointMeasure)=(((1-a^2)*(T : ℝ) : ℝ) : ℂ) := by
  have hp := constant_raw_ae a T
  have hm : rawChannel T (-Complex.I*(a : ℂ)) (constantInput T) =ᵐ[IBMSourceLaws.jointMeasure]
      fun w => star (value a T w) := by
    have h : rawChannel T (-Complex.I*(a : ℂ)) (constantInput T) =ᵐ[IBMSourceLaws.jointMeasure] value (-a) T := by
      simpa only [Complex.ofReal_neg,mul_neg,neg_mul] using constant_raw_ae (-a) T
    exact h.trans (Eventually.of_forall (value_neg_scale a T))
  have hi : inner ℂ (rawChannel T (Complex.I*(a : ℂ)) (constantInput T))
      (rawChannel T (-Complex.I*(a : ℂ)) (constantInput T)) =
      star (∫ w, value a T w^2 ∂IBMSourceLaws.jointMeasure) := by
    rw [L2.inner_def]
    calc
      _ = ∫ w, star (value a T w^2) ∂IBMSourceLaws.jointMeasure := by
        apply integral_congr_ae
        filter_upwards [hp,hm] with w hp hm
        rw [hp,hm]
        simp [Complex.inner,pow_two]
      _ = _ := integral_conj
  rw [constant_conjugate_pairing] at hi
  have hc := congrArg star hi
  simpa [Complex.star_def] using hc.symm

/-- No filtration can turn the uncorrected analytic square into a martingale at unmatched scale. -/
theorem square_not_martingale (a : ℝ) (ha : a^2 ≠ 1)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace IBMSourceLaws.JointSample)) :
    ¬ Martingale (fun t w => value a t w^2) 𝓕 IBMSourceLaws.jointMeasure := by
  intro hm
  have he := hm.setIntegral_eq (show (0 : ℝ≥0) ≤ 1 by norm_num) (s := univ) MeasurableSet.univ
  simp only [setIntegral_univ] at he
  rw [square_mean,square_mean] at he
  have hc : (0 : ℂ)=1-(a : ℂ)^2 := by simpa using he
  have hh : (0 : ℝ)=1-a^2 := by exact_mod_cast hc
  exact ha (by linarith)

end OperatorDerivativeRewrite.Foundation.StochasticCauchyCovarianceObstruction
