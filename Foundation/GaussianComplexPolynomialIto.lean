import Foundation.BiharmonicGaussianBranches
import Foundation.GaussianScalarPolynomialIto
import Foundation.ComplexL2Isometry
import Foundation.EvenEntirePolynomialApproximation
import Foundation.RealRootedLaguerreLimit
/-! Native complexification of the actual predictable Brownian integral and
branchwise polynomial Ito for the constructed biharmonic complex process. -/
noncomputable section
open MeasureTheory Polynomial Set Filter Complex
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianComplexPolynomialIto
open InfiniteGaussian GaussianPredictableFull GaussianTimeProductL2
open GaussianScalarPolynomialIto GaussianTimeProcess ComplexL2Isometry

def realPolynomial (Q : ℂ[X]) : ℝ[X] := EvenEntirePolynomialApproximation.realPolynomial Q

def imagPolynomial (Q : ℂ[X]) : ℝ[X] := realPolynomial (C (-I)*Q)

theorem real_coeff (Q : ℂ[X]) (n : ℕ) : (realPolynomial Q).coeff n=(Q.coeff n).re :=
  EvenEntirePolynomialApproximation.realPolynomial_coeff Q n

theorem imag_coeff (Q : ℂ[X]) (n : ℕ) : (imagPolynomial Q).coeff n=(Q.coeff n).im := by
  simp [imagPolynomial,real_coeff,coeff_C_mul,Complex.mul_re]

theorem polynomial_recombine (Q : ℂ[X]) :
    (realPolynomial Q).map (algebraMap ℝ ℂ)+C I*(imagPolynomial Q).map (algebraMap ℝ ℂ)=Q := by
  ext n
  simp only [coeff_add,coeff_map,coeff_C_mul,real_coeff,imag_coeff,Complex.coe_algebraMap]
  simpa only [mul_comm] using Complex.re_add_im (Q.coeff n)

theorem eval_recombine (Q : ℂ[X]) (x : ℝ) :
    (((realPolynomial Q).eval x:ℝ):ℂ)+I*(((imagPolynomial Q).eval x:ℝ):ℂ)=Q.eval (x:ℂ) := by
  have h := congrArg (fun p : ℂ[X] => p.eval (x:ℂ)) (polynomial_recombine Q)
  simp only [eval_add,eval_mul,eval_C] at h
  rw [RealRootedLaguerreLimit.map_eval_real,RealRootedLaguerreLimit.map_eval_real] at h
  exact h

theorem real_derivative (Q : ℂ[X]) : realPolynomial Q.derivative=(realPolynomial Q).derivative := by
  ext n
  simp [real_coeff,coeff_derivative,Complex.mul_re]

theorem imag_derivative (Q : ℂ[X]) : imagPolynomial Q.derivative=(imagPolynomial Q).derivative := by
  ext n
  simp [imag_coeff,coeff_derivative,Complex.mul_im]

abbrev Native := fullPredictable × fullPredictable

def field (U : Native) : Lp ℂ 2 timeProbability :=
  combine timeProbability U.1.val U.2.val

def integral (U : Native) : Lp ℂ 2 gaussianProduct :=
  combine gaussianProduct (itoIntegral U.1) (itoIntegral U.2)

theorem integral_norm_sq (U : Native) : ‖integral U‖^2=‖field U‖^2 := by
  rw [integral,field,combine_norm_sq,combine_norm_sq,itoIntegral_norm,itoIntegral_norm]
  rfl

def value (T : ℝ≥0) (Q : ℂ[X]) : Lp ℂ 2 gaussianProduct :=
  combine gaussianProduct (polynomialValue T (realPolynomial Q)) (polynomialValue T (imagPolynomial Q))

theorem value_coeFn (T : ℝ≥0) (Q : ℂ[X]) :
    value T Q =ᵐ[gaussianProduct] fun w => Q.eval (IBMConstructedSources.clockPath w T:ℂ) := by
  filter_upwards [combine_ae gaussianProduct (polynomialValue T (realPolynomial Q))
      (polynomialValue T (imagPolynomial Q)),polynomialValue_coeFn T (realPolynomial Q),
    polynomialValue_coeFn T (imagPolynomial Q),IBMConstructedSources.clockPath_coordinate_ae T]
      with w hc hr hi hb
  change (combine gaussianProduct (polynomialValue T (realPolynomial Q)) (polynomialValue T (imagPolynomial Q))) w=_
  rw [hc,hr,hi,←hb]
  exact eval_recombine Q _

def constant (z : ℂ) : Lp ℂ 2 gaussianProduct :=
  combine gaussianProduct (z.re • gaussianOne) (z.im • gaussianOne)

theorem value_zero (Q : ℂ[X]) : value 0 Q=constant (Q.eval 0) := by
  rw [value,polynomialValue_zero,polynomialValue_zero]
  have h := eval_recombine Q 0
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  norm_num only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,Complex.add_im,Complex.mul_im,
    one_mul,zero_add] at hr hi
  rw [hr,hi]
  rfl
def complexify : GaussianL2 × GaussianL2 →L[ℝ] Lp ℂ 2 gaussianProduct :=
  (ofReal gaussianProduct).comp (ContinuousLinearMap.fst ℝ GaussianL2 GaussianL2)+
    I • ((ofReal gaussianProduct).comp (ContinuousLinearMap.snd ℝ GaussianL2 GaussianL2))

theorem complexify_apply (r i : GaussianL2) : complexify (r,i)=combine gaussianProduct r i := rfl

theorem value_continuous (Q : ℂ[X]) : Continuous (fun T : ℝ≥0 => value T Q) := by
  have hr : Continuous (fun T : ℝ≥0 => polynomialValue T (realPolynomial Q)) :=
    GaussianPolynomialProcess.valueL2_continuous _
  have hi : Continuous (fun T : ℝ≥0 => polynomialValue T (imagPolynomial Q)) :=
    GaussianPolynomialProcess.valueL2_continuous _
  exact complexify.continuous.comp (hr.prodMk hi)

theorem value_intervalIntegrable (Q : ℂ[X]) (T : ℝ≥0) :
    IntervalIntegrable (fun t : ℝ => value t.toNNReal Q) volume 0 T :=
  ((value_continuous Q).comp continuous_real_toNNReal).intervalIntegrable 0 T

theorem value_integral (Q : ℂ[X]) (T : ℝ≥0) :
    (∫ t in 0..(T:ℝ), value t.toNNReal Q)=
      complexify ((∫ t in 0..(T:ℝ), polynomialValue t.toNNReal (realPolynomial Q)),
        (∫ t in 0..(T:ℝ), polynomialValue t.toNNReal (imagPolynomial Q))) := by
  have hr := polynomialValue_intervalIntegrable (realPolynomial Q) T
  have hi := polynomialValue_intervalIntegrable (imagPolynomial Q) T
  have hp : IntervalIntegrable (fun t : ℝ =>
      (polynomialValue t.toNNReal (realPolynomial Q),polynomialValue t.toNNReal (imagPolynomial Q))) volume 0 T :=
    ⟨hr.1.prodMk hi.1,hr.2.prodMk hi.2⟩
  have he := complexify.intervalIntegral_comp_comm hp
  have he' : (∫ t in 0..(T:ℝ),
      (polynomialValue t.toNNReal (realPolynomial Q),polynomialValue t.toNNReal (imagPolynomial Q)))=
      ((∫ t in 0..(T:ℝ), polynomialValue t.toNNReal (realPolynomial Q)),
        (∫ t in 0..(T:ℝ), polynomialValue t.toNNReal (imagPolynomial Q))) := by
    simp only [intervalIntegral,integral_pair hr.1 hi.1,integral_pair hr.2 hi.2]
    rfl
  rw [he'] at he
  exact he

theorem polynomial_ito (Q : ℂ[X]) (T : ℝ≥0) :
    ∃! U : Native,
      (GaussianProductDerivative.scalarCurry U.1.val =ᵐ[volume]
        (Ioc 0 (T:ℝ)).indicator (fun t => polynomialValue t.toNNReal (realPolynomial Q.derivative))) ∧
      (GaussianProductDerivative.scalarCurry U.2.val =ᵐ[volume]
        (Ioc 0 (T:ℝ)).indicator (fun t => polynomialValue t.toNNReal (imagPolynomial Q.derivative))) ∧
      value T Q-constant (Q.eval 0)=integral U+
        (1/2:ℝ) • ∫ t in 0..(T:ℝ), value t.toNNReal Q.derivative.derivative := by
  obtain ⟨U,⟨hUr,hUi⟩,hUu⟩ := scalar_polynomial_ito (realPolynomial Q) T
  obtain ⟨V,⟨hVr,hVi⟩,hVu⟩ := scalar_polynomial_ito (imagPolynomial Q) T
  have hp : (polynomialValue T (realPolynomial Q),polynomialValue T (imagPolynomial Q))-
      ((realPolynomial Q).eval 0 • gaussianOne,(imagPolynomial Q).eval 0 • gaussianOne)=
      (itoIntegral U,itoIntegral V)+(1/2:ℝ) •
        ((∫ t in 0..(T:ℝ), polynomialValue t.toNNReal (realPolynomial Q).derivative.derivative),
        (∫ t in 0..(T:ℝ), polynomialValue t.toNNReal (imagPolynomial Q).derivative.derivative)) := by
    exact Prod.ext hUi hVi
  have he := congrArg complexify hp
  simp only [map_sub,map_add,map_smul,complexify_apply] at he
  have hd : combine gaussianProduct
      (∫ t in 0..(T:ℝ), polynomialValue t.toNNReal (realPolynomial Q).derivative.derivative)
      (∫ t in 0..(T:ℝ), polynomialValue t.toNNReal (imagPolynomial Q).derivative.derivative)=
      ∫ t in 0..(T:ℝ), value t.toNNReal Q.derivative.derivative := by
    rw [value_integral,real_derivative,real_derivative,imag_derivative,imag_derivative]
    rfl
  rw [hd] at he
  refine ⟨(U,V),⟨?_,?_,?_⟩,?_⟩
  · simpa only [real_derivative] using hUr
  · simpa only [imag_derivative] using hVr
  · rw [←value_zero]
    simpa only [value,polynomialValue_zero,integral] using he
  · intro W hW
    apply Prod.ext
    · apply Subtype.ext
      apply GaussianProductDerivative.scalarCurry.injective
      have hw : GaussianProductDerivative.scalarCurry W.1.val =ᵐ[volume]
          (Ioc 0 (T:ℝ)).indicator (fun t => polynomialValue t.toNNReal (realPolynomial Q).derivative) := by
        simpa only [real_derivative] using hW.1
      exact Lp.ext (hw.trans hUr.symm)
    · apply Subtype.ext
      apply GaussianProductDerivative.scalarCurry.injective
      have hw : GaussianProductDerivative.scalarCurry W.2.val =ᵐ[volume]
          (Ioc 0 (T:ℝ)).indicator (fun t => polynomialValue t.toNNReal (imagPolynomial Q).derivative) := by
        simpa only [imag_derivative] using hW.2.1
      exact Lp.ext (hw.trans hVr.symm)

theorem value_C_mul (T : ℝ≥0) (c : ℂ) (Q : ℂ[X]) : value T (C c*Q)=c • value T Q := by
  apply Lp.ext
  filter_upwards [value_coeFn T (C c*Q),value_coeFn T Q,Lp.coeFn_smul c (value T Q)] with w hl hr hs
  rw [hl,hs,Pi.smul_apply,hr]
  simp only [eval_mul,eval_C,smul_eq_mul]

def slice (U : Native) (t : ℝ) : Lp ℂ 2 gaussianProduct :=
  combine gaussianProduct (GaussianProductDerivative.scalarCurry U.1.val t)
    (GaussianProductDerivative.scalarCurry U.2.val t)

theorem native_unique_of_slice (U V : Native) (h : slice U =ᵐ[volume] slice V) : U=V := by
  apply Prod.ext
  · apply Subtype.ext
    apply GaussianProductDerivative.scalarCurry.injective
    apply Lp.ext
    filter_upwards [h] with t ht
    have he := congrArg (realPart gaussianProduct) ht
    simpa only [slice,realPart_combine] using he
  · apply Subtype.ext
    apply GaussianProductDerivative.scalarCurry.injective
    apply Lp.ext
    filter_upwards [h] with t ht
    have he := congrArg (imagPart gaussianProduct) ht
    simpa only [slice,imagPart_combine] using he

def branchPolynomial (b : Bool) (P : ℝ[X]) : ℂ[X] :=
  (P.map (algebraMap ℝ ℂ)).comp (C (BiharmonicGaussianBranches.phase b)*X)

def branchValue (T : ℝ≥0) (b : Bool) (P : ℝ[X]) : Lp ℂ 2 gaussianProduct :=
  value T (branchPolynomial b P)

theorem branchValue_coeFn (T : ℝ≥0) (b : Bool) (P : ℝ[X]) :
    branchValue T b P =ᵐ[gaussianProduct] fun w =>
      (P.map (algebraMap ℝ ℂ)).eval (BiharmonicGaussianBranches.value T (b,w)) := by
  filter_upwards [value_coeFn T (branchPolynomial b P)] with w hw
  change value T (branchPolynomial b P) w=_
  rw [hw]
  simp only [branchPolynomial,eval_comp,eval_mul,eval_C,eval_X,BiharmonicGaussianBranches.value_eq]

theorem branch_derivative (b : Bool) (P : ℝ[X]) :
    (branchPolynomial b P).derivative=C (BiharmonicGaussianBranches.phase b)*branchPolynomial b P.derivative := by
  simp only [branchPolynomial,derivative_comp,derivative_map,derivative_mul,derivative_C,
    derivative_X,zero_mul,zero_add,mul_one]

theorem branch_second_derivative (b : Bool) (P : ℝ[X]) :
    (branchPolynomial b P).derivative.derivative=
      C ((BiharmonicGaussianBranches.phase b)^2)*branchPolynomial b P.derivative.derivative := by
  rw [branch_derivative,derivative_mul,derivative_C,zero_mul,zero_add,branch_derivative]
  rw [map_pow]
  ring

theorem phase_square (b : Bool) : (BiharmonicGaussianBranches.phase b)^2=
    2*I*(BiharmonicGaussianBranches.sign b:ℂ) := by
  cases b <;> simp only [BiharmonicGaussianBranches.phase,BiharmonicGaussianBranches.sign,
    Bool.false_eq_true,ite_false,ite_true,Complex.ofReal_neg,Complex.ofReal_one]
  all_goals ring_nf;norm_num <;> ring

theorem branch_initial (b : Bool) (P : ℝ[X]) : (branchPolynomial b P).eval 0=(P.eval 0:ℝ) := by
  unfold branchPolynomial
  rw [eval_comp]
  simp only [eval_mul,eval_C,eval_X,mul_zero]
  exact RealRootedLaguerreLimit.map_eval_real P 0

theorem branch_drift_integrable (b : Bool) (P : ℝ[X]) (T : ℝ≥0) :
    IntervalIntegrable (fun t : ℝ => branchValue t.toNNReal b P.derivative.derivative) volume 0 T :=
  value_intervalIntegrable _ T

theorem branch_polynomial_ito (b : Bool) (P : ℝ[X]) (T : ℝ≥0) :
    ∃! U : Native,
      (slice U =ᵐ[volume] (Ioc 0 (T:ℝ)).indicator
        (fun t => BiharmonicGaussianBranches.phase b • branchValue t.toNNReal b P.derivative)) ∧
      branchValue T b P-constant (P.eval 0:ℝ)=integral U+
        (I*(BiharmonicGaussianBranches.sign b:ℂ)) •
          ∫ t in 0..(T:ℝ), branchValue t.toNNReal b P.derivative.derivative := by
  obtain ⟨U,hU,huniq⟩ := polynomial_ito (branchPolynomial b P) T
  have hs : slice U =ᵐ[volume] (Ioc 0 (T:ℝ)).indicator
      (fun t => BiharmonicGaussianBranches.phase b • branchValue t.toNNReal b P.derivative) := by
    filter_upwards [hU.1,hU.2.1] with t hr hi
    change combine gaussianProduct (GaussianProductDerivative.scalarCurry U.1.val t)
      (GaussianProductDerivative.scalarCurry U.2.val t)=_
    rw [hr,hi]
    by_cases ht : t∈Ioc 0 (T:ℝ)
    · simp only [indicator_of_mem ht]
      change value t.toNNReal (branchPolynomial b P).derivative=_
      rw [branch_derivative,value_C_mul]
      rfl
    · simp only [indicator_of_notMem ht,combine,map_zero,smul_zero,add_zero]
  have hh := hU.2.2
  rw [branch_initial,branch_second_derivative] at hh
  simp only [value_C_mul] at hh
  rw [intervalIntegral.integral_smul,←smul_assoc] at hh
  have hc : (1/2:ℝ) • (BiharmonicGaussianBranches.phase b)^2=
      I*(BiharmonicGaussianBranches.sign b:ℂ) := by
    rw [phase_square,Complex.real_smul]
    push_cast
    ring
  rw [hc] at hh
  refine ⟨U,⟨hs,hh⟩,?_⟩
  intro V hV
  exact native_unique_of_slice V U (hV.1.trans hs.symm)

def pastStep (s t : ℝ≥0) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) : Native :=
  (⟨productTensor (GaussianTimeHilbert.intervalVector s t) A,past_step_mem_fullPredictable s t A hA⟩,
    ⟨productTensor (GaussianTimeHilbert.intervalVector s t) B,past_step_mem_fullPredictable s t B hB⟩)

theorem integral_pastStep (s t : ℝ≥0) (hst : s≤t) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    integral (pastStep s t A B hA hB) =ᵐ[gaussianProduct] fun w =>
      ((A w:ℂ)+I*(B w:ℂ))*((IBMConstructedSources.clockPath w t-IBMConstructedSources.clockPath w s:ℝ):ℂ) := by
  have hr := itoIntegral_past_step s t hst A hA
  have hi := itoIntegral_past_step s t hst B hB
  filter_upwards [combine_ae gaussianProduct (itoIntegral (pastStep s t A B hA hB).1)
      (itoIntegral (pastStep s t A B hA hB).2),hr,hi,
      IBMConstructedSources.clockPath_coordinate_ae t,IBMConstructedSources.clockPath_coordinate_ae s]
    with w hc hR hI ht hs
  change combine gaussianProduct (itoIntegral (pastStep s t A B hA hB).1)
    (itoIntegral (pastStep s t A B hA hB).2) w=_
  simp only [pastStep] at hc ⊢
  rw [hc,hR,hI,←ht,←hs]
  push_cast
  ring

theorem integral_centered (U : Native) : (∫ w, integral U w ∂gaussianProduct)=0 := by
  have hi : Integrable (integral U) gaussianProduct := (Lp.memLp (integral U)).integrable (by norm_num)
  have hr : (fun w => (integral U w).re)=ᵐ[gaussianProduct] (itoIntegral U.1) := by
    filter_upwards [combine_ae gaussianProduct (itoIntegral U.1) (itoIntegral U.2)] with w hw
    change (combine gaussianProduct (itoIntegral U.1) (itoIntegral U.2) w).re=_
    rw [hw]
    simp
  have hm : (fun w => (integral U w).im)=ᵐ[gaussianProduct] (itoIntegral U.2) := by
    filter_upwards [combine_ae gaussianProduct (itoIntegral U.1) (itoIntegral U.2)] with w hw
    change (combine gaussianProduct (itoIntegral U.1) (itoIntegral U.2) w).im=_
    rw [hw]
    simp
  apply Complex.ext
  · calc
      _ = ∫ w, (integral U w).re ∂gaussianProduct := (Complex.reCLM.integral_comp_comm hi).symm
      _ = ∫ w, itoIntegral U.1 w ∂gaussianProduct := integral_congr_ae hr
      _ = _ := itoIntegral_centered U.1
  · calc
      _ = ∫ w, (integral U w).im ∂gaussianProduct := (Complex.imCLM.integral_comp_comm hi).symm
      _ = ∫ w, itoIntegral U.2 w ∂gaussianProduct := integral_congr_ae hm
      _ = _ := itoIntegral_centered U.2

theorem branch_square_no_native (b : Bool) (T : ℝ≥0) (hT : 0<T) :
    ¬∃ U : Native, branchValue T b (X^2)=integral U := by
  rintro ⟨U,hU⟩
  have hc := branchValue_coeFn T b (X^2)
  simp only [Polynomial.map_pow,Polynomial.map_X,eval_pow,eval_X] at hc
  have he := integral_congr_ae hc
  rw [BiharmonicGaussianBranches.branch_square,hU,integral_centered] at he
  have ht : (T:ℂ)≠0 := by exact_mod_cast (ne_of_gt hT)
  have hb : (BiharmonicGaussianBranches.sign b:ℂ)≠0 := by cases b <;> norm_num [BiharmonicGaussianBranches.sign]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) ht) hb) he.symm

end OperatorDerivativeRewrite.Foundation.GaussianComplexPolynomialIto
