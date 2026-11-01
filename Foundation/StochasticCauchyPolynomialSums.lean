import Foundation.StochasticCauchyPolynomialReconstruction
/-! Actual finite polynomial Brownian stochastic sums and their mean-square
reconstruction limit, on the existing native two-source integration domain.
All coefficient transport below is finite real-linear AE algebra. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialSums
open InfiniteGaussian ProductL2Curry ComplexL2Isometry GaussianTimeProcess
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels StochasticCauchyPolynomialInput
open StochasticCauchyPolynomialPrediction StochasticCauchyAnalyticPowers StochasticCauchyPolynomials
open StochasticCauchyExponentialInput StochasticCauchyPolynomialReconstruction
open GaussianBrownianQuadraticVariation
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete

private def noiseIntegral (T : ℝ≥0) (j : Bool) : Input T →ₗᵢ[ℝ] JointL2 :=
  if j then integralY T else integralX T

private def noiseIncrement (s t : ℝ≥0) (j : Bool) (w : SampleSpace × SampleSpace) : ℝ :=
  if j then process t w.2-process s w.2 else process t w.1-process s w.1

/-- Only a finite real-linear AE relation. No closedness, bounded multiplication
or enlarged stochastic domain is asserted. -/
private def multiplicationGraph (T s t : ℝ≥0) (j : Bool) : Submodule ℝ (Input T × JointL2) where
  carrier := {q | noiseIntegral T j q.1 =ᵐ[gaussianProduct.prod gaussianProduct]
    fun w => q.2 w*noiseIncrement s t j w}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℝ 2 (gaussianProduct.prod gaussianProduct)] with w hz
    simpa only [map_zero,Prod.fst_zero,Prod.snd_zero,hz,Pi.zero_apply,zero_mul]
  add_mem' := by
    intro q r hq hr
    change noiseIntegral T j (q.1+r.1) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => (q.2+r.2) w*noiseIncrement s t j w
    rw [map_add]
    filter_upwards [hq,hr,Lp.coeFn_add (noiseIntegral T j q.1) (noiseIntegral T j r.1),
      Lp.coeFn_add q.2 r.2] with w hq hr hi hc
    simp only [Pi.add_apply] at hi hc
    rw [hi,hc,hq,hr,add_mul]
  smul_mem' := by
    intro c q hq
    change noiseIntegral T j (c • q.1) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => (c • q.2) w*noiseIncrement s t j w
    rw [map_smul]
    filter_upwards [hq,Lp.coeFn_smul c (noiseIntegral T j q.1),Lp.coeFn_smul c q.2]
      with w hq hi hc
    simp only [Pi.smul_apply,smul_eq_mul] at hi hc
    rw [hi,hc,hq,mul_assoc]

private theorem termStep_graph (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (a b : ℕ) (j : Bool) :
    (termStep T s t hst htT a b,term (timeDirection s) a b) ∈ multiplicationGraph T s t j := by
  have hc : term (timeDirection s) a b =
      productTensor gaussianProduct gaussianProduct (scalarPower a s) (scalarPower b s) := by
    rw [term,← scalarPower_eq,← scalarPower_eq]
  cases j
  · change integralX T (termStep T s t hst htT a b) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => term (timeDirection s) a b w*(process t w.1-process s w.1)
    rw [termStep,integralX_stepInput,hc]
    filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct
      (GaussianPastStepCompletion.pastIncrement s t hst (scalarPower a s) (scalarPower_past a s)) (scalarPower b s),
      productTensor_coeFn gaussianProduct gaussianProduct (scalarPower a s) (scalarPower b s),
      (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
        (GaussianPastStepCompletion.pastIncrement_coeFn s t hst (scalarPower a s) (scalarPower_past a s))]
        with w ht hc hi
    simp only [Function.comp_apply] at hi
    rw [ht,hc,hi]
    simp only [smul_eq_mul]
    ring
  · change integralY T (termStep T s t hst htT a b) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => term (timeDirection s) a b w*(process t w.2-process s w.2)
    rw [termStep,integralY_stepInput,hc]
    filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct (scalarPower a s)
      (GaussianPastStepCompletion.pastIncrement s t hst (scalarPower b s) (scalarPower_past b s)),
      productTensor_coeFn gaussianProduct gaussianProduct (scalarPower a s) (scalarPower b s),
      (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
        (GaussianPastStepCompletion.pastIncrement_coeFn s t hst (scalarPower b s) (scalarPower_past b s))]
        with w ht hc hi
    simp only [Function.comp_apply] at hi
    rw [ht,hc,hi]
    simp only [smul_eq_mul]
    ring

private theorem powerStep_graph (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) (b j : Bool) :
    (powerStep T s t hst htT n b,if b then imagPower (timeDirection s) n else realPower (timeDirection s) n)
      ∈ multiplicationGraph T s t j := by
  have hm := (multiplicationGraph T s t j).sum_mem (fun i (_ : i ∈ Finset.range (n+1)) =>
    (multiplicationGraph T s t j).smul_mem
      ((n.choose i:ℝ)*(if b then (Complex.I^i).im else (Complex.I^i).re))
      (termStep_graph T s t hst htT (n-i) i j))
  cases b <;> simpa only [Prod.smul_mk,← prod_mk_sum,powerStep,Bool.false_eq_true,
    ite_false,ite_true,realPower,imagPower,binomial] using hm

private theorem polynomialStep_graph (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (p : Polynomial ℂ) (b j : Bool) :
    (polynomialStep T s t hst htT p b,valuePart p b s) ∈ multiplicationGraph T s t j := by
  have hp (n : ℕ) (b : Bool) := powerStep_graph T s t hst htT n b j
  cases b
  · change (∑ n ∈ Finset.range (p.natDegree+1),
        ((p.coeff n).re • powerStep T s t hst htT n false-(p.coeff n).im • powerStep T s t hst htT n true),
      ∑ n ∈ Finset.range (p.natDegree+1),
        ((p.coeff n).re • realPower (timeDirection s) n-(p.coeff n).im • imagPower (timeDirection s) n))
        ∈ multiplicationGraph T s t j
    have hm := (multiplicationGraph T s t j).sum_mem (fun n (_ : n ∈ Finset.range (p.natDegree+1)) =>
      (multiplicationGraph T s t j).sub_mem
        ((multiplicationGraph T s t j).smul_mem (p.coeff n).re (hp n false))
        ((multiplicationGraph T s t j).smul_mem (p.coeff n).im (hp n true)))
    simpa only [Prod.smul_mk,Prod.mk_sub_mk,← prod_mk_sum,polynomialStep,valuePart,
      Bool.false_eq_true,ite_false,ite_true,realPolynomial] using hm
  · change (∑ n ∈ Finset.range (p.natDegree+1),
        ((p.coeff n).re • powerStep T s t hst htT n true+(p.coeff n).im • powerStep T s t hst htT n false),
      ∑ n ∈ Finset.range (p.natDegree+1),
        ((p.coeff n).re • imagPower (timeDirection s) n+(p.coeff n).im • realPower (timeDirection s) n))
        ∈ multiplicationGraph T s t j
    have hm := (multiplicationGraph T s t j).sum_mem (fun n (_ : n ∈ Finset.range (p.natDegree+1)) =>
      (multiplicationGraph T s t j).add_mem
        ((multiplicationGraph T s t j).smul_mem (p.coeff n).re (hp n true))
        ((multiplicationGraph T s t j).smul_mem (p.coeff n).im (hp n false)))
    simpa only [Prod.smul_mk,Prod.mk_add_mk,← prod_mk_sum,polynomialStep,valuePart,
      Bool.false_eq_true,ite_false,ite_true,imagPolynomial] using hm

/-- Actual component stochastic integral, including unbounded polynomial coefficients. -/
theorem polynomial_step_ae (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (p : Polynomial ℂ) (b : Bool) :
    (integralX T (polynomialStep T s t hst htT p b) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => valuePartValue p b s w*(process t w.1-process s w.1)) ∧
    (integralY T (polynomialStep T s t hst htT p b) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => valuePartValue p b s w*(process t w.2-process s w.2)) := by
  constructor
  · have h := polynomialStep_graph T s t hst htT p b false
    change integralX T (polynomialStep T s t hst htT p b) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => valuePart p b s w*(process t w.1-process s w.1) at h
    filter_upwards [h,valuePart_ae p b s] with w hi hc
    rw [hi,hc]
  · have h := polynomialStep_graph T s t hst htT p b true
    change integralY T (polynomialStep T s t hst htT p b) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => valuePart p b s w*(process t w.2-process s w.2) at h
    filter_upwards [h,valuePart_ae p b s] with w hi hc
    rw [hi,hc]

attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime

/-- Exact finite sample-function identity for the original complex stochastic channel. -/
theorem finite_step_ae (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (p : Polynomial ℂ) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • combineInput T
      (polynomialStep T s t hst htT p false) (polynomialStep T s t hst htT p true))
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w => p.eval (position s w)*(position t w-position s w) := by
  rw [StochasticCauchyExponentialReconstruction.normalized_channel_combine]
  filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct) _ _,
    Lp.coeFn_sub (integralX T (polynomialStep T s t hst htT p false))
      (integralY T (polynomialStep T s t hst htT p true)),
    Lp.coeFn_add (integralX T (polynomialStep T s t hst htT p true))
      (integralY T (polynomialStep T s t hst htT p false)),
    (polynomial_step_ae T s t hst htT p false).1,(polynomial_step_ae T s t hst htT p true).2,
    (polynomial_step_ae T s t hst htT p true).1,(polynomial_step_ae T s t hst htT p false).2]
      with w hc hd ha hxr hyj hxj hyr
  rw [hc,hd,ha]
  simp only [Pi.sub_apply,Pi.add_apply]
  rw [hxr,hyj,hxj,hyr]
  apply Complex.ext <;> simp [valuePartValue,position,Complex.mul_re,Complex.mul_im] <;> ring

private theorem combineInput_sum (T : ℝ≥0) {I : Type*} [Fintype I] (a b : I → Input T) :
    combineInput T (∑ i,a i) (∑ i,b i)=∑ i,combineInput T (a i) (b i) := by
  apply Subtype.ext
  simp only [combineInput,Submodule.coe_sum,combine,map_sum,Finset.smul_sum,Finset.sum_add_distrib]

private def grid (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) (i : Fin (N+1)) (b : Bool) : Input T :=
  polynomialStep T (uniformTime T N i.castSucc) (uniformTime T N i.succ)
    (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    (by simpa only [(uniformTime_endpoints T N).2] using
      uniformTime_monotone T N (Fin.le_last i.succ)) p.derivative b

private theorem normalizedSteps_sum (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) :
    StochasticCauchyPolynomialInput.normalizedSteps T p N=∑ i : Fin (N+1),
      ((Real.sqrt 2:ℝ):ℂ) • combineInput T (grid T p N i false) (grid T p N i true) := by
  have he (b : Bool) : gridInput T p.derivative b N=∑ i,grid T p N i b := rfl
  rw [StochasticCauchyPolynomialInput.normalizedSteps,he false,he true,combineInput_sum,Finset.smul_sum]

/-- Actual left-point polynomial derivative sums along the uniform grid. -/
def riemannSum (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) (w : SampleSpace × SampleSpace) : ℂ :=
  ∑ i : Fin (N+1), p.derivative.eval (position (uniformTime T N i.castSucc) w)*
    (position (uniformTime T N i.succ) w-position (uniformTime T N i.castSucc) w)

/-- Finite equality with actual process sums, not merely agreement of expectations. -/
theorem chronological_ae (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) :
    channel T false (StochasticCauchyPolynomialInput.normalizedSteps T p N)
      =ᵐ[gaussianProduct.prod gaussianProduct] riemannSum T p N := by
  rw [normalizedSteps_sum,map_sum]
  have he (i : Fin (N+1)) :
      channel T false (((Real.sqrt 2:ℝ):ℂ) • combineInput T (grid T p N i false) (grid T p N i true))
        =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
          p.derivative.eval (position (uniformTime T N i.castSucc) w)*
            (position (uniformTime T N i.succ) w-position (uniformTime T N i.castSucc) w) :=
    finite_step_ae T _ _ (uniformTime_monotone T N (Fin.castSucc_le_succ i))
      (by simpa only [(uniformTime_endpoints T N).2] using
        uniformTime_monotone T N (Fin.le_last i.succ)) p.derivative
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (N+1) => channel T false
    (((Real.sqrt 2:ℝ):ℂ) • combineInput T (grid T p N i false) (grid T p N i true))),
    ae_all_iff.mpr he] with w hs he
  rw [hs]
  simp only [Finset.sum_apply,riemannSum]
  exact Finset.sum_congr rfl (fun i _ => he i)

theorem riemannSum_memLp (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) :
    MemLp (riemannSum T p N) 2 (gaussianProduct.prod gaussianProduct) :=
  (Lp.memLp (channel T false (StochasticCauchyPolynomialInput.normalizedSteps T p N))).ae_eq
    (chronological_ae T p N)

/-- The squared errors are integrable; the mean-square claim is not a
consequence of the convention assigning zero to nonintegrable integrals. -/
theorem squared_error_integrable (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) :
    Integrable (fun w => ‖riemannSum T p N w-(p.eval (position T w)-p.eval 0)‖^2)
      (gaussianProduct.prod gaussianProduct) :=
  ((riemannSum_memLp T p N).sub ((polynomial_position_memLp T p).sub (memLp_const (p.eval 0)))).norm.integrable_sq

/-- Mean-square convergence of the explicit actual process sums, for every
finite polynomial and every fixed horizon. No full-sequence AS claim. -/
theorem mean_square_reconstruction (T : ℝ≥0) (p : Polynomial ℂ) :
    Tendsto (fun N => ∫ w,‖riemannSum T p N w-(p.eval (position T w)-p.eval 0)‖^2
      ∂gaussianProduct.prod gaussianProduct) atTop (𝓝 0) := by
  have hk : StochasticCauchyMeanResidual.complexCenter (polynomialClass T p)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w => p.eval (position T w)-p.eval 0 := by
    rw [← polynomial_reconstruction]
    exact polynomial_reconstruction_ae T p
  have he (N : ℕ) :
      ‖channel T false (StochasticCauchyPolynomialInput.normalizedSteps T p N)-
        StochasticCauchyMeanResidual.complexCenter (polynomialClass T p)‖^2 =
      ∫ w,‖riemannSum T p N w-(p.eval (position T w)-p.eval 0)‖^2
        ∂gaussianProduct.prod gaussianProduct := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (channel T false (StochasticCauchyPolynomialInput.normalizedSteps T p N))
      (StochasticCauchyMeanResidual.complexCenter (polynomialClass T p)),chronological_ae T p N,hk]
      with w hd hs hk
    simp only [Pi.sub_apply] at hd
    rw [hd,hs,hk]
  have ht := ((StochasticCauchyPolynomialReconstruction.chronological_reconstruction T p).sub
    (tendsto_const_nhds (x := StochasticCauchyMeanResidual.complexCenter (polynomialClass T p)))).norm.pow 2
  simpa only [he,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using ht

end OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialSums
