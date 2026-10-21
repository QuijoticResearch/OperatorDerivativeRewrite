import Foundation.PureOrderPolynomialTransport
import Foundation.PseudoMomentGaussianBoundary
import Foundation.RiemannQuadraticGaussian
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! Genuine complex Gaussian averages of real polynomials agree exactly with the
existing order-two polynomial transport. Integrability precedes integral algebra;
the clock is s*c², so imaginary shifts give transport at -s. No completed
factorial-analytic domain for the Xi function is asserted here. -/
noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Set Filter Complex
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexGaussianPolynomialTransport
open PseudoPolynomialStein PureOrderPolynomialTransport

theorem scaled_standard_law (s : ℝ≥0) :
    GaussianCore.γ.map (fun x : ℝ => Real.sqrt (2*(s:ℝ))*x)=
      RiemannQuadraticGaussian.law s := by
  have hv : (NNReal.mk ((Real.sqrt (2*(s:ℝ)))^2) (sq_nonneg _) : ℝ≥0)=2*s := by
    apply Subtype.ext
    change (Real.sqrt (2*(s:ℝ)))^2=2*(s:ℝ)
    exact Real.sq_sqrt (by positivity)
  change (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (2*(s:ℝ))*x)=gaussianReal 0 (2*s)
  rw [gaussianReal_map_const_mul,hv]
  simp only [mul_zero,mul_one]

theorem real_polynomial_average (s : ℝ≥0) (P : ℝ[X]) :
    (∫ y : ℝ,P.eval y ∂RiemannQuadraticGaussian.law s)=expectation 2 (s:ℝ) P := by
  have hl : HasLaw (fun x : ℝ => Real.sqrt (2*(s:ℝ))*x)
      (RiemannQuadraticGaussian.law s) GaussianCore.γ := ⟨by fun_prop,scaled_standard_law s⟩
  have he := hl.integral_comp (f:=fun y : ℝ => P.eval y) (by fun_prop)
  dsimp only [Function.comp_apply] at he
  rw [← PseudoMomentGaussianBoundary.expectation_nonnegative_gaussian (s:ℝ) s.property P] at he
  exact he.symm

theorem complex_power_integrable (s : ℝ≥0) (n : ℕ) :
    Integrable (fun y : ℝ => (y:ℂ)^n) (RiemannQuadraticGaussian.law s) := by
  let : IsGaussian (RiemannQuadraticGaussian.law s) := by
    change IsGaussian (gaussianReal 0 (2*s))
    infer_instance
  have hi := (IsGaussian.memLp_id (RiemannQuadraticGaussian.law s) (n:ENNReal)
    (by simp)).integrable_norm_pow'
  apply hi.mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun y => by simp [norm_pow,Complex.norm_real])

theorem complex_polynomial_integrable (s : ℝ≥0) (Q : ℂ[X]) :
    Integrable (fun y : ℝ => Q.eval (y:ℂ)) (RiemannQuadraticGaussian.law s) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    convert hP.add hQ using 1
    funext y
    simp
  | monomial n c => simpa only [eval_monomial] using (complex_power_integrable s n).const_mul c

theorem complex_power_average (s : ℝ≥0) (n : ℕ) :
    (∫ y : ℝ,(y:ℂ)^n ∂RiemannQuadraticGaussian.law s)=(moment 2 (s:ℝ) n:ℂ) := by
  have he := real_polynomial_average s (X^n:ℝ[X])
  rw [expectation_X_pow] at he
  simp only [eval_pow,eval_X] at he
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal,he]

theorem complex_polynomial_stein (s : ℝ≥0) (Q : ℂ[X]) :
    (∫ y : ℝ,(y:ℂ)*Q.eval (y:ℂ) ∂RiemannQuadraticGaussian.law s)=
      (2*(s:ℝ):ℂ)*(∫ y : ℝ,Q.derivative.eval (y:ℂ) ∂RiemannQuadraticGaussian.law s) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have hXP := complex_polynomial_integrable s (X*P)
    have hXQ := complex_polynomial_integrable s (X*Q)
    simp only [eval_mul,eval_X] at hXP hXQ
    simp_rw [eval_add,mul_add,derivative_add,eval_add]
    rw [integral_add hXP hXQ,integral_add (complex_polynomial_integrable s P.derivative)
      (complex_polynomial_integrable s Q.derivative),hP,hQ]
    ring
  | monomial n c =>
    have he (y : ℝ) : (y:ℂ)*(monomial n c).eval (y:ℂ)=c*(y:ℂ)^(n+1) := by
      simp only [eval_monomial,pow_succ]
      ring
    simp_rw [he]
    rw [integral_const_mul,complex_power_average,derivative_monomial]
    simp_rw [eval_monomial]
    rw [integral_const_mul,complex_power_average,moment_succ]
    norm_num only [Nat.reduceSub,Nat.descFactorial_one,Nat.cast_ofNat]
    push_cast
    ring

theorem transport_mul_X (a : ℝ) (P : ℝ[X]) :
    transport 2 a (X*P)=X*transport 2 a P+C (2*a)*(transport 2 a P).derivative := by
  apply Polynomial.funext
  intro x
  have hd : (taylor x P).derivative=taylor x P.derivative := by
    simp [taylor_apply,derivative_comp]
  have hc := LinearMap.congr_fun (transport_derivative 2 a) P
  change (transport 2 a P).derivative=transport 2 a P.derivative at hc
  rw [eval_add,eval_mul,eval_X,eval_mul,eval_C,hc,
    transport_eval 2 (by norm_num),transport_eval 2 (by norm_num),transport_eval 2 (by norm_num),
    taylor_mul,taylor_X,add_mul,map_add,polynomial_stein]
  rw [show C x*taylor x P=x • taylor x P by simp [smul_eq_C_mul],map_smul]
  simp only [Nat.reduceSub,Function.iterate_one,smul_eq_mul]
  rw [hd]
  ring

theorem shifted_polynomial_integrable (s : ℝ≥0) (P : ℂ[X]) (z c : ℂ) :
    Integrable (fun y : ℝ => P.eval (z+c*(y:ℂ))) (RiemannQuadraticGaussian.law s) := by
  have hi := complex_polynomial_integrable s (P.comp (C z+C c*X))
  simpa only [eval_comp,eval_add,eval_C,eval_mul,eval_X] using hi

theorem shifted_complex_stein (s : ℝ≥0) (P : ℂ[X]) (z c : ℂ) :
    (∫ y : ℝ,(y:ℂ)*P.eval (z+c*(y:ℂ)) ∂RiemannQuadraticGaussian.law s)=
      (2*(s:ℝ):ℂ)*c*(∫ y : ℝ,P.derivative.eval (z+c*(y:ℂ))
        ∂RiemannQuadraticGaussian.law s) := by
  let B : ℂ[X] := C z+C c*X
  have hh := complex_polynomial_stein s (P.comp B)
  have he (y : ℝ) : (P.comp B).eval (y:ℂ)=P.eval (z+c*(y:ℂ)) := by simp [B]
  have hd (y : ℝ) : (P.comp B).derivative.eval (y:ℂ)=
      c*P.derivative.eval (z+c*(y:ℂ)) := by
    simp [B,derivative_comp]
  simp_rw [he,hd] at hh
  rw [integral_const_mul] at hh
  simpa only [mul_assoc] using hh

def average (s : ℝ≥0) (z c : ℂ) : ℝ[X] →ₗ[ℝ] ℂ where
  toFun P := ∫ y : ℝ,(P.map (algebraMap ℝ ℂ)).eval (z+c*(y:ℂ))
    ∂RiemannQuadraticGaussian.law s
  map_add' P Q := by
    simp only [Polynomial.map_add,eval_add]
    exact integral_add (shifted_polynomial_integrable s _ z c)
      (shifted_polynomial_integrable s _ z c)
  map_smul' a P := by
    simp only [smul_eq_C_mul,Polynomial.map_mul,Polynomial.map_C,eval_mul,eval_C,
      integral_const_mul,RingHom.id_apply,Complex.coe_algebraMap,Complex.real_smul]

theorem average_apply (s : ℝ≥0) (z c : ℂ) (P : ℝ[X]) :
    average s z c P=(∫ y : ℝ,(P.map (algebraMap ℝ ℂ)).eval (z+c*(y:ℂ))
      ∂RiemannQuadraticGaussian.law s) := rfl

theorem average_one (s : ℝ≥0) (z c : ℂ) : average s z c 1=1 := by
  simp [average]

theorem average_mul_X (s : ℝ≥0) (z c : ℂ) (P : ℝ[X]) :
    average s z c (X*P)=z*average s z c P+
      (2*(s:ℝ):ℂ)*c^2*average s z c P.derivative := by
  let Q := P.map (algebraMap ℝ ℂ)
  have hI := shifted_polynomial_integrable s Q z c
  have hY : Integrable (fun y : ℝ => (y:ℂ)*Q.eval (z+c*(y:ℂ)))
      (RiemannQuadraticGaussian.law s) := by
    have hh := complex_polynomial_integrable s (X*Q.comp (C z+C c*X))
    simpa only [eval_mul,eval_X,eval_comp,eval_add,eval_C] using hh
  have he (y : ℝ) : ((X*P).map (algebraMap ℝ ℂ)).eval (z+c*(y:ℂ))=
      z*Q.eval (z+c*(y:ℂ))+c*((y:ℂ)*Q.eval (z+c*(y:ℂ))) := by
    simp only [Polynomial.map_mul,Polynomial.map_X,eval_mul,eval_X]
    dsimp [Q]
    ring
  rw [average_apply]
  simp_rw [he]
  rw [integral_add (hI.const_mul z) (hY.const_mul c),integral_const_mul,integral_const_mul,
    shifted_complex_stein]
  change z*average s z c P+c*((2*(s:ℝ):ℂ)*c*
    (∫ y : ℝ,Q.derivative.eval (z+c*(y:ℂ)) ∂RiemannQuadraticGaussian.law s))=_
  have hd : Q.derivative=P.derivative.map (algebraMap ℝ ℂ) := by
    dsimp [Q]
    exact derivative_map ..
  rw [hd]
  change z*average s z c P+c*((2*(s:ℝ):ℂ)*c*average s z c P.derivative)=_
  ring


theorem drift_stein_unique (z b : ℂ) (E T : ℝ[X] →ₗ[ℝ] ℂ)
    (hone : E 1=T 1)
    (hE : ∀ P : ℝ[X],E (X*P)=z*E P+b*E P.derivative)
    (hT : ∀ P : ℝ[X],T (X*P)=z*T P+b*T P.derivative) : E=T := by
  have hpow (n : ℕ) : E ((X:ℝ[X])^n)=T ((X:ℝ[X])^n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [pow_zero] using hone
      | succ n =>
        rw [pow_succ',hE,hT,derivative_X_pow,
          show C (n:ℝ)*X^(n-1)=(n:ℝ) • (X:ℝ[X])^(n-1) by simp [smul_eq_C_mul],
          map_smul,map_smul,ih n (by omega),ih (n-1) (by omega)]
  apply LinearMap.ext
  intro P
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add,map_add,hP,hQ]
  | monomial n a =>
    rw [show monomial n a=a • (X:ℝ[X])^n by simp [smul_eq_C_mul, C_mul_X_pow_eq_monomial],map_smul,map_smul,hpow]

theorem transport_one (a : ℝ) : transport 2 a 1=1 := by
  simpa only [PureOrderAppellCalculus.appell] using transport_basis 2 a 0

theorem transported_eval_stein (a : ℝ) (z : ℂ) (P : ℝ[X]) :
    ((transport 2 a (X*P)).map (algebraMap ℝ ℂ)).eval z=
      z*((transport 2 a P).map (algebraMap ℝ ℂ)).eval z+
        (2*a:ℝ)*((transport 2 a P.derivative).map (algebraMap ℝ ℂ)).eval z := by
  have hd := LinearMap.congr_fun (transport_derivative 2 a) P
  change (transport 2 a P).derivative=transport 2 a P.derivative at hd
  rw [transport_mul_X,Polynomial.map_add,eval_add,Polynomial.map_mul,Polynomial.map_X,
    eval_mul,eval_X,Polynomial.map_mul,Polynomial.map_C,eval_mul,eval_C,hd]
  rfl

theorem average_eq_transport (s : ℝ≥0) (z c : ℂ) (delta : ℝ)
    (hc : c^2=(delta:ℂ)) (P : ℝ[X]) :
    average s z c P=((transport 2 ((s:ℝ)*delta) P).map (algebraMap ℝ ℂ)).eval z := by
  let a : ℝ := (s:ℝ)*delta
  let T : ℝ[X] →ₗ[ℝ] ℂ := (aeval z).toLinearMap.comp (transport 2 a)
  have hTapply (Q : ℝ[X]) : T Q=((transport 2 a Q).map (algebraMap ℝ ℂ)).eval z := by
    simp only [T,LinearMap.comp_apply,AlgHom.toLinearMap_apply,aeval_def,eval₂_eq_eval_map]
  have hone : average s z c 1=T 1 := by rw [average_one,hTapply,transport_one]; simp
  have hE (Q : ℝ[X]) : average s z c (X*Q)=
      z*average s z c Q+(2*a:ℝ)*average s z c Q.derivative := by
    rw [average_mul_X,hc]
    dsimp [a]
    push_cast
    ring
  have hT (Q : ℝ[X]) : T (X*Q)=z*T Q+(2*a:ℝ)*T Q.derivative := by
    simp_rw [hTapply]
    exact transported_eval_stein a z Q
  have he := drift_stein_unique z (2*a:ℝ) (average s z c) T hone hE hT
  rw [LinearMap.congr_fun he P,hTapply]

theorem actual_gaussian_transport (s : ℝ≥0) (z c : ℂ) (delta : ℝ)
    (hc : c^2=(delta:ℂ)) (P : ℝ[X]) :
    (∫ y : ℝ,(P.map (algebraMap ℝ ℂ)).eval (z+c*(y:ℂ))
      ∂RiemannQuadraticGaussian.law s)=
      ((transport 2 ((s:ℝ)*delta) P).map (algebraMap ℝ ℂ)).eval z :=
  average_eq_transport s z c delta hc P


theorem imaginary_gaussian_transport (s : ℝ≥0) (z : ℂ) (P : ℝ[X]) :
    (∫ y : ℝ,(P.map (algebraMap ℝ ℂ)).eval (z+I*(y:ℂ))
      ∂RiemannQuadraticGaussian.law s)=
      ((transport 2 (-(s:ℝ)) P).map (algebraMap ℝ ℂ)).eval z := by
  simpa only [mul_neg_one] using actual_gaussian_transport s z I (-1)
    (by simpa using Complex.I_sq) P

theorem real_gaussian_transport (s : ℝ≥0) (z : ℂ) (P : ℝ[X]) :
    (∫ y : ℝ,(P.map (algebraMap ℝ ℂ)).eval (z+(y:ℂ))
      ∂RiemannQuadraticGaussian.law s)=
      ((transport 2 (s:ℝ) P).map (algebraMap ℝ ℂ)).eval z := by
  simpa only [one_mul,mul_one] using actual_gaussian_transport s z 1 1 (by simp) P

end OperatorDerivativeRewrite.Foundation.ComplexGaussianPolynomialTransport
