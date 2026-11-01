import Foundation.StochasticCauchyPolynomialPrediction
import Foundation.StochasticCauchyExponentialInput
import Foundation.GaussianScalarPolynomialIto

/-! Actual polynomial time curves and native stochastic input construction.
The physical coefficient and strong chronological native convergence are proved;
terminal/canonical Clark–Ocone identification is a separate next obligation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialInput
open InfiniteGaussian ProductL2Curry ComplexL2Isometry
open GaussianTimeProcess GaussianTimeHilbert GaussianBrownianQuadraticVariation
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPolynomialPrediction StochasticCauchyAnalyticPowers
open StochasticCauchyPhysicalInput StochasticCauchyExponentialInput
attribute [local instance] StochasticCauchyJointPastIntegral.input_complete
  StochasticCauchyJointPastIntegral.swapped_complete timeHilbert_secondCountable
  StochasticCauchyParameterizedObstruction.finiteL2Exponent

def scalarPower (n : ℕ) (t : ℝ≥0) : GaussianL2 :=
  GaussianScalarPolynomialIto.polynomialValue t (Polynomial.X^n)

theorem scalarPower_ae (n : ℕ) (t : ℝ≥0) :
    scalarPower n t =ᵐ[gaussianProduct] fun w => (process t w)^n := by
  have hh := GaussianScalarPolynomialIto.polynomialValue_coeFn t (Polynomial.X^n)
  simp only [Polynomial.eval_pow,Polynomial.eval_X] at hh
  exact hh

theorem scalarPower_eq (n : ℕ) (t : ℝ≥0) :
    scalarPower n t = (power (timeDirection t) n : GaussianL2) :=
  Lp.ext ((scalarPower_ae n t).trans (power_ae (timeDirection t) n).symm)

theorem scalarPower_continuous (n : ℕ) : Continuous (scalarPower n) :=
  GaussianPolynomialProcess.valueL2_continuous
    (GaussianPolynomialDifferentiation.spatialPolynomial (Polynomial.X^n))

theorem scalarPower_past (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration t] (scalarPower n t) gaussianProduct :=
  ((process_stronglyAdapted t).pow n).aestronglyMeasurable.congr (scalarPower_ae n t).symm

/-- Joint continuity uses the existing bounded Bochner scalar-action map. -/
theorem tensor_curve_continuous (A B : ℝ≥0 → GaussianL2)
    (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun t => productTensor gaussianProduct gaussianProduct (A t) (B t)) := by
  let L : GaussianL2 →L[ℝ] GaussianL2 →L[ℝ] Lp GaussianL2 2 gaussianProduct :=
    (ContinuousLinearMap.lsmul ℝ ℝ).flip.compLpL₂ 2 gaussianProduct
  have he (a b : GaussianL2) : productTensor gaussianProduct gaussianProduct a b =
      (curryEquiv gaussianProduct gaussianProduct).symm (L b a) := by
    apply (curryEquiv gaussianProduct gaussianProduct).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    change ProductL2Curry.curry gaussianProduct gaussianProduct
      (productTensor gaussianProduct gaussianProduct a b) = L b a
    rw [curry_productTensor]
    apply Lp.ext
    filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct a b,
      ((ContinuousLinearMap.lsmul ℝ ℝ).flip b).coeFn_compLp a] with w ht hl
    exact ht.trans hl.symm
  have hc : Continuous (fun t => L (B t) (A t)) := (L.continuous.comp hB).clm_apply hA
  have hh := (curryEquiv gaussianProduct gaussianProduct).symm.continuous.comp hc
  convert hh using 1
  funext t
  exact he (A t) (B t)

theorem term_continuous (a b : ℕ) : Continuous (fun t => term (timeDirection t) a b) := by
  have he : (fun t => term (timeDirection t) a b) =
      (fun t => productTensor gaussianProduct gaussianProduct (scalarPower a t) (scalarPower b t)) := by
    funext t
    rw [term,← scalarPower_eq,← scalarPower_eq]
  rw [he]
  exact tensor_curve_continuous _ _ (scalarPower_continuous a) (scalarPower_continuous b)

theorem realPower_continuous (n : ℕ) : Continuous (fun t => realPower (timeDirection t) n) := by
  unfold realPower binomial
  apply continuous_finsetSum
  intro j hj
  exact (continuous_const : Continuous (fun _ : ℝ≥0 =>
    (n.choose j : ℝ)*(Complex.I^j).re)).smul (term_continuous (n-j) j)

theorem imagPower_continuous (n : ℕ) : Continuous (fun t => imagPower (timeDirection t) n) := by
  unfold imagPower binomial
  apply continuous_finsetSum
  intro j hj
  exact (continuous_const : Continuous (fun _ : ℝ≥0 =>
    (n.choose j : ℝ)*(Complex.I^j).im)).smul (term_continuous (n-j) j)

theorem realPolynomial_continuous (p : Polynomial ℂ) :
    Continuous (fun t => StochasticCauchyPolynomials.realPolynomial (timeDirection t) p) := by
  change Continuous (fun t => ∑ n ∈ Finset.range (p.natDegree+1),
    ((p.coeff n).re • realPower (timeDirection t) n-(p.coeff n).im • imagPower (timeDirection t) n))
  apply continuous_finsetSum
  intro n hn
  exact ((continuous_const : Continuous (fun _ : ℝ≥0 => (p.coeff n).re)).smul
    (realPower_continuous n)).sub
    ((continuous_const : Continuous (fun _ : ℝ≥0 => (p.coeff n).im)).smul (imagPower_continuous n))

theorem imagPolynomial_continuous (p : Polynomial ℂ) :
    Continuous (fun t => StochasticCauchyPolynomials.imagPolynomial (timeDirection t) p) := by
  change Continuous (fun t => ∑ n ∈ Finset.range (p.natDegree+1),
    ((p.coeff n).re • imagPower (timeDirection t) n+(p.coeff n).im • realPower (timeDirection t) n))
  apply continuous_finsetSum
  intro n hn
  exact ((continuous_const : Continuous (fun _ : ℝ≥0 => (p.coeff n).re)).smul
    (imagPower_continuous n)).add
    ((continuous_const : Continuous (fun _ : ℝ≥0 => (p.coeff n).im)).smul (realPower_continuous n))

def valuePart (p : Polynomial ℂ) (b : Bool) (t : ℝ≥0) : JointL2 :=
  if b then StochasticCauchyPolynomials.imagPolynomial (timeDirection t) p
  else StochasticCauchyPolynomials.realPolynomial (timeDirection t) p

theorem valuePart_continuous (p : Polynomial ℂ) (b : Bool) : Continuous (valuePart p b) := by
  cases b
  · exact realPolynomial_continuous p
  · exact imagPolynomial_continuous p

private theorem finite_timeLaw (T : ℝ≥0) : IsFiniteMeasure (timeLaw T) :=
  ⟨by simp [timeLaw]⟩
attribute [local instance] finite_timeLaw

private def cellScalar (T s t : ℝ≥0) : Lp ℝ 2 (timeLaw T) :=
  indicatorConstLp 2 (measurableSet_Ioc (a := (s:ℝ)) (b := (t:ℝ))) (measure_ne_top _ _) 1

private def cellMap (T s t : ℝ≥0) : JointL2 →L[ℝ] Lp JointL2 2 (timeLaw T) :=
  ((ContinuousLinearMap.lsmul ℝ ℝ).flip.compLpL₂ 2 (timeLaw T)).flip (cellScalar T s t)

private theorem cellMap_ae (T s t : ℝ≥0) (C : JointL2) :
    cellMap T s t C =ᵐ[timeLaw T] (Ioc (s:ℝ) (t:ℝ)).indicator (fun _ => C) := by
  have hs : cellScalar T s t =ᵐ[timeLaw T]
      (Ioc (s:ℝ) (t:ℝ)).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have hm : cellMap T s t C =ᵐ[timeLaw T] fun r => cellScalar T s t r • C :=
    ((ContinuousLinearMap.lsmul ℝ ℝ).flip C).coeFn_compLp (cellScalar T s t)
  filter_upwards [hs,hm] with r hs hm
  rw [hm,hs]
  by_cases hr : r ∈ Ioc (s:ℝ) (t:ℝ)
  · simp only [indicator_of_mem hr,one_smul]
  · simp only [indicator_of_notMem hr,zero_smul]

def termStep (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (a b : ℕ) : Input T :=
  stepInput T s t hst htT (scalarPower a s) (scalarPower b s)
    (scalarPower_past a s) (scalarPower_past b s)

private theorem termStep_sections (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (a b : ℕ) :
    timeSections T (fieldEmbedding T (termStep T s t hst htT a b)) =
      cellMap T s t (term (timeDirection s) a b) := by
  rw [term,← scalarPower_eq,← scalarPower_eq]
  apply Lp.ext
  exact (timeSections_step T s t hst htT _ _ (scalarPower_past a s) (scalarPower_past b s)).trans
    (cellMap_ae T s t _).symm

def powerStep (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) (b : Bool) : Input T :=
  ∑ j ∈ Finset.range (n+1), ((n.choose j:ℝ)*(if b then (Complex.I^j).im else (Complex.I^j).re)) •
    termStep T s t hst htT (n-j) j

private theorem powerStep_sections (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) (b : Bool) :
    timeSections T (fieldEmbedding T (powerStep T s t hst htT n b)) =
      cellMap T s t (if b then imagPower (timeDirection s) n else realPower (timeDirection s) n) := by
  cases b <;> simp only [powerStep,Bool.false_eq_true,ite_false,ite_true,
    map_sum,map_smul,termStep_sections,realPower,imagPower,binomial]

def polynomialStep (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (p : Polynomial ℂ) (b : Bool) : Input T :=
  if b then ∑ n ∈ Finset.range (p.natDegree+1),
    ((p.coeff n).re • powerStep T s t hst htT n true+(p.coeff n).im • powerStep T s t hst htT n false)
  else ∑ n ∈ Finset.range (p.natDegree+1),
    ((p.coeff n).re • powerStep T s t hst htT n false-(p.coeff n).im • powerStep T s t hst htT n true)

private theorem polynomialStep_sections (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (p : Polynomial ℂ) (b : Bool) :
    timeSections T (fieldEmbedding T (polynomialStep T s t hst htT p b)) =
      cellMap T s t (valuePart p b s) := by
  cases b
  · change _ = cellMap T s t (∑ n ∈ Finset.range (p.natDegree+1),
      ((p.coeff n).re • realPower (timeDirection s) n-(p.coeff n).im • imagPower (timeDirection s) n))
    simp only [polynomialStep,Bool.false_eq_true,ite_false,map_sum,map_sub,map_smul,
      powerStep_sections,ite_true]
  · change _ = cellMap T s t (∑ n ∈ Finset.range (p.natDegree+1),
      ((p.coeff n).re • imagPower (timeDirection s) n+(p.coeff n).im • realPower (timeDirection s) n))
    simp only [polynomialStep,ite_true,map_sum,map_add,map_smul,powerStep_sections,
      Bool.false_eq_true,ite_false]

def gridInput (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) (N : ℕ) : Input T :=
  ∑ i : Fin (N+1), polynomialStep T (uniformTime T N i.castSucc) (uniformTime T N i.succ)
    (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    (by simpa only [(uniformTime_endpoints T N).2] using
      uniformTime_monotone T N (Fin.le_last i.succ)) p b

theorem gridInput_sections (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) (N : ℕ) :
    timeSections T (fieldEmbedding T (gridInput T p b N)) =ᵐ[timeLaw T]
      fun r => ∑ i : Fin (N+1),
        (Ioc (uniformTime T N i.castSucc:ℝ) (uniformTime T N i.succ:ℝ)).indicator
          (fun _ => valuePart p b (uniformTime T N i.castSucc)) r := by
  simp only [gridInput,map_sum,polynomialStep_sections]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin (N+1) => cellMap T (uniformTime T N i.castSucc) (uniformTime T N i.succ)
      (valuePart p b (uniformTime T N i.castSucc))),
    ae_all_iff.mpr (fun i : Fin (N+1) => cellMap_ae T
      (uniformTime T N i.castSucc) (uniformTime T N i.succ)
      (valuePart p b (uniformTime T N i.castSucc)))] with r hs ht
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => ht i)

theorem running_part_native (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) :
    ∃ u : Input T, timeSections T (fieldEmbedding T u) =
      running (valuePart p b) (valuePart_continuous p b) T ∧
      Tendsto (gridInput T p b) atTop (𝓝 u) :=
  running_native_of_steps _ (valuePart_continuous p b) T (gridInput T p b)
    (gridInput_sections T p b)

def partInput (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) : Input T :=
  (running_part_native T p b).choose

theorem partInput_sections (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) :
    timeSections T (fieldEmbedding T (partInput T p b)) =
      running (valuePart p b) (valuePart_continuous p b) T :=
  (running_part_native T p b).choose_spec.1

theorem partInput_tendsto (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) :
    Tendsto (gridInput T p b) atTop (𝓝 (partInput T p b)) :=
  (running_part_native T p b).choose_spec.2

def valuePartValue (p : Polynomial ℂ) (b : Bool) (t : ℝ≥0)
    (w : SampleSpace × SampleSpace) : ℝ :=
  if b then (p.eval (position t w)).im else (p.eval (position t w)).re

theorem valuePart_ae (p : Polynomial ℂ) (b : Bool) (t : ℝ≥0) :
    valuePart p b t =ᵐ[gaussianProduct.prod gaussianProduct] valuePartValue p b t := by
  cases b
  · have he : realPart (gaussianProduct.prod gaussianProduct) (polynomialClass t p) =
        valuePart p false t := realPart_combine _ _ _
    have hr : realPart (gaussianProduct.prod gaussianProduct) (polynomialClass t p)
        =ᵐ[gaussianProduct.prod gaussianProduct] fun w => (polynomialClass t p w).re :=
      Complex.reCLM.coeFn_compLpL _
    rw [he] at hr
    exact hr.trans ((polynomialClass_ae t p).mono (fun w hw => congrArg Complex.re hw))
  · have he : imagPart (gaussianProduct.prod gaussianProduct) (polynomialClass t p) =
        valuePart p true t := imagPart_combine _ _ _
    have hr : imagPart (gaussianProduct.prod gaussianProduct) (polynomialClass t p)
        =ᵐ[gaussianProduct.prod gaussianProduct] fun w => (polynomialClass t p w).im :=
      Complex.imCLM.coeFn_compLpL _
    rw [he] at hr
    exact hr.trans ((polynomialClass_ae t p).mono (fun w hw => congrArg Complex.im hw))

/-- The actual globally measurable native physical field has these polynomial
slices AE in time and then AE in the actual two-source probability space. -/
theorem partInput_slices (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) :
    ∀ᵐ r ∂timeLaw T, (fun w : SampleSpace × SampleSpace =>
      fieldEmbedding T (partInput T p b) ((r,w.1),w.2))
        =ᵐ[gaussianProduct.prod gaussianProduct] valuePartValue p b r.toNNReal := by
  have hs := timeSections_ae T (fieldEmbedding T (partInput T p b))
  rw [partInput_sections] at hs
  filter_upwards [hs,running_ae (valuePart p b) (valuePart_continuous p b) T] with r hs hr
  rw [hr] at hs
  exact hs.symm.trans (valuePart_ae p b r.toNNReal)

private theorem scaled_partInput_slices (T : ℝ≥0) (p : Polynomial ℂ) (b : Bool) (c : ℝ) :
    ∀ᵐ r ∂timeLaw T, (fun w : SampleSpace × SampleSpace =>
      fieldEmbedding T (c • partInput T p b) ((r,w.1),w.2))
        =ᵐ[gaussianProduct.prod gaussianProduct] fun w => c*valuePartValue p b r.toNNReal w := by
  rw [map_smul]
  have hs := timeSections_ae T (fieldEmbedding T (c • partInput T p b))
  rw [map_smul,map_smul,partInput_sections] at hs
  filter_upwards [hs,Lp.coeFn_smul c (running (valuePart p b) (valuePart_continuous p b) T),
    running_ae (valuePart p b) (valuePart_continuous p b) T] with r hs hc hr
  rw [hc,Pi.smul_apply,hr] at hs
  refine hs.symm.trans ?_
  filter_upwards [Lp.coeFn_smul c (valuePart p b r.toNNReal),valuePart_ae p b r.toNNReal]
    with w hc hv
  rw [hc,Pi.smul_apply,hv]
  rfl

-- Activate the existing trimmed predictable instance only AFTER the physical
-- time/source transport declarations, preserving their original measure spaces.
open StochasticCauchyComplexChannels
attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyComplexChannels.complexInput_complete

def normalizedInput (T : ℝ≥0) (p : Polynomial ℂ) : ComplexInput T :=
  ((Real.sqrt 2:ℝ):ℂ) • combineInput T (partInput T p.derivative false) (partInput T p.derivative true)

def normalizedSteps (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) : ComplexInput T :=
  ((Real.sqrt 2:ℝ):ℂ) • combineInput T (gridInput T p.derivative false N) (gridInput T p.derivative true N)

theorem normalizedInput_parts (T : ℝ≥0) (p : Polynomial ℂ) :
    realInput T (normalizedInput T p) = Real.sqrt 2 • partInput T p.derivative false ∧
    imagInput T (normalizedInput T p) = Real.sqrt 2 • partInput T p.derivative true := by
  constructor
  · simp only [normalizedInput,realInput_smul,realInput_combine,imagInput_combine,
      Complex.ofReal_re,Complex.ofReal_im,zero_smul,sub_zero]
  · simp only [normalizedInput,imagInput_smul,realInput_combine,imagInput_combine,
      Complex.ofReal_re,Complex.ofReal_im,zero_smul,add_zero]

/-- The candidate's ACTUAL physical complex coefficient is sqrt2*p'(Z_t).
The factor cancels the existing channel's dZ/sqrt2 convention. This is an
AE-time/AE-source identity, not a simultaneous pointwise path claim. -/
theorem normalizedInput_slices (T : ℝ≥0) (p : Polynomial ℂ) :
    ∀ᵐ r ∂timeLaw T, ∀ᵐ w : SampleSpace × SampleSpace ∂gaussianProduct.prod gaussianProduct,
      (fieldEmbedding T (realInput T (normalizedInput T p)) ((r,w.1),w.2) : ℂ)+
        Complex.I*(fieldEmbedding T (imagInput T (normalizedInput T p)) ((r,w.1),w.2) : ℂ) =
        (Real.sqrt 2 : ℂ)*p.derivative.eval (position r.toNNReal w) := by
  rw [(normalizedInput_parts T p).1,(normalizedInput_parts T p).2]
  filter_upwards [scaled_partInput_slices T p.derivative false (Real.sqrt 2),
    scaled_partInput_slices T p.derivative true (Real.sqrt 2)] with r hx hy
  filter_upwards [hx,hy] with w hx hy
  rw [hx,hy]
  simp only [valuePartValue,Bool.false_eq_true,ite_false,ite_true]
  apply Complex.ext <;> simp

private theorem combineInput_tendsto (T : ℝ≥0) (a b : ℕ → Input T) (u v : Input T)
    (ha : Tendsto a atTop (𝓝 u)) (hb : Tendsto b atTop (𝓝 v)) :
    Tendsto (fun N => combineInput T (a N) (b N)) atTop (𝓝 (combineInput T u v)) := by
  apply tendsto_subtype_rng.mpr
  have har := (continuous_subtype_val.tendsto u).comp ha
  have hbr := (continuous_subtype_val.tendsto v).comp hb
  change Tendsto (fun N => ofReal (nativeMeasure T) (a N).val+
      Complex.I • ofReal (nativeMeasure T) (b N).val) atTop
    (𝓝 (ofReal (nativeMeasure T) u.val+Complex.I • ofReal (nativeMeasure T) v.val))
  exact (((ofReal (nativeMeasure T)).continuous.tendsto _).comp har).add
    (tendsto_const_nhds.smul (((ofReal (nativeMeasure T)).continuous.tendsto _).comp hbr))

theorem normalizedSteps_tendsto (T : ℝ≥0) (p : Polynomial ℂ) :
    Tendsto (normalizedSteps T p) atTop (𝓝 (normalizedInput T p)) :=
  tendsto_const_nhds.smul (combineInput_tendsto T _ _ _ _
    (partInput_tendsto T p.derivative false) (partInput_tendsto T p.derivative true))

theorem normalized_integrals_tendsto (T : ℝ≥0) (p : Polynomial ℂ) :
    Tendsto (fun N => channel T false (normalizedSteps T p N)) atTop
      (𝓝 (channel T false (normalizedInput T p))) :=
  ((channel T false).continuous.tendsto _).comp (normalizedSteps_tendsto T p)

end OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialInput
