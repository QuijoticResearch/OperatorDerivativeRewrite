import Foundation.QuaternionTiltWard
import Foundation.PeriodicLinkDisintegration
import Foundation.SU2RadialLaplacian
/-! Actual Wilson conditional radial Langevin integration by parts.
A differential core identity, not a constructed stochastic process or closed generator. -/
noncomputable section
open MeasureTheory Filter Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.WilsonRadialLangevin
open OperatorDerivativeRewrite.Foundation QuaternionAngularHaar QuaternionTiltWard

def moment (n : ℕ) (t : ℝ) : ℝ :=
 ∫ u,realCoordinate u^n*Real.exp (t*realCoordinate u) ∂QuaternionAngularHaar.law

theorem moment_derivative (n : ℕ) (t : ℝ) : HasDerivAt (moment n) (moment (n+1) t) t := by
 have hb : ∀ u : QuaternionAngularHaar.Group, |realCoordinate u^n|≤1 := by
   intro u
   rw [abs_pow]
   exact pow_le_one₀ (abs_nonneg _) (realCoordinate_bound u)
 have hd:=weighted_hasDerivAt (fun u => realCoordinate u^n)
   (realCoordinate_measurable.pow_const n) hb t
 convert hd using 1
 · rfl
 · simp only [moment,pow_succ,mul_assoc]

theorem moment_ward (n : ℕ) (t : ℝ) :
 t*(moment n t-moment (n+2) t)+(n:ℝ)*(moment (n-1) t-moment (n+1) t)=3*moment (n+1) t := by
 induction n generalizing t with
 | zero =>
   have h:=weighted_radial_identity t
   simpa only [Nat.zero_add,moment,Nat.zero_sub,Nat.cast_zero,zero_mul,add_zero,pow_zero,pow_one,one_mul] using h.symm
 | succ n ih =>
   have hL:=((hasDerivAt_id t).mul ((moment_derivative n t).sub (moment_derivative (n+2) t))).add
     (((moment_derivative (n-1) t).sub (moment_derivative (n+1) t)).const_mul (n:ℝ))
   have he : (fun s : ℝ => s*(moment n s-moment (n+2) s)+
     (n:ℝ)*(moment (n-1) s-moment (n+1) s))=fun s => 3*moment (n+1) s := funext ih
   change HasDerivAt (fun s : ℝ => s*(moment n s-moment (n+2) s)+
     (n:ℝ)*(moment (n-1) s-moment (n+1) s)) _ t at hL
   rw [he] at hL
   have hd:=hL.unique ((moment_derivative (n+1) t).const_mul 3)
   simp only [Pi.sub_apply,id_eq,one_mul] at hd
   cases n with
   | zero =>
     norm_num only [Nat.cast_zero,zero_mul,add_zero,one_mul,Nat.zero_sub,Nat.reduceAdd] at hd ⊢
     nlinarith [hd]
   | succ n =>
     simp only [Nat.add_sub_cancel, Nat.cast_add,Nat.cast_one] at hd ⊢
     nlinarith [hd]

theorem polynomial_integrable (t : ℝ) (P : ℝ[X]) :
 Integrable (fun u : Group => P.eval (realCoordinate u)*Real.exp (t*realCoordinate u)) QuaternionAngularHaar.law := by
 have hc : Continuous (fun u : Group => P.eval (realCoordinate u)*Real.exp (t*realCoordinate u)) := by
   have hr : Continuous (realCoordinate : Group → ℝ) := Quaternion.continuous_re.comp continuous_subtype_val
   exact (P.continuous.comp hr).mul (Real.continuous_exp.comp (continuous_const.mul hr))
 exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def weighted (t : ℝ) : ℝ[X] →ₗ[ℝ] ℝ where
 toFun P:=∫ u : Group,P.eval (realCoordinate u)*Real.exp (t*realCoordinate u) ∂QuaternionAngularHaar.law
 map_add' P Q:=by
   simp only [Polynomial.eval_add,add_mul]
   exact integral_add (polynomial_integrable t P) (polynomial_integrable t Q)
 map_smul' c P:=by
   simp only [Polynomial.eval_smul,smul_eq_mul,mul_assoc]
   exact integral_const_mul c _

theorem weighted_power (t : ℝ) (n : ℕ) : weighted t (X^n)=moment n t := by
 change (∫ u : Group,(X^n:ℝ[X]).eval (realCoordinate u)*Real.exp (t*realCoordinate u)
   ∂QuaternionAngularHaar.law)=_
 simp only [Polynomial.eval_X_pow]
 rfl

theorem weighted_C_mul (t c : ℝ) (P : ℝ[X]) : weighted t (C c*P)=c*weighted t P := by
 rw [←smul_eq_C_mul]
 rw [map_smul]
 rfl

def stein (t : ℝ) (P : ℝ[X]) : ℝ[X] :=
 (1-X^2)*P.derivative+(C t*(1-X^2)-C 3*X)*P

theorem stein_power (t : ℝ) (n : ℕ) :
 stein t (X^n)=C (n:ℝ)*(X^(n-1)-X^(n+1))+C t*(X^n-X^(n+2))-C 3*X^(n+1) := by
 cases n with
 | zero=>simp [stein]
 | succ n=>
   simp only [stein,Polynomial.derivative_X_pow,Nat.add_sub_cancel]
   simp only [pow_add,pow_one]
   ring

theorem weighted_stein_power (t : ℝ) (n : ℕ) : weighted t (stein t (X^n))=0 := by
 rw [stein_power,map_sub,map_add,weighted_C_mul,weighted_C_mul,weighted_C_mul,map_sub,map_sub,
   ]
 simp only [weighted_power]
 have h:=moment_ward n t
 nlinarith [h]

theorem stein_add (t : ℝ) (P Q : ℝ[X]) : stein t (P+Q)=stein t P+stein t Q := by
 simp only [stein,derivative_add]
 ring

theorem stein_C_mul (t c : ℝ) (P : ℝ[X]) : stein t (C c*P)=C c*stein t P := by
 simp only [stein,derivative_mul,derivative_C,zero_mul,zero_add]
 ring

theorem weighted_stein (t : ℝ) (P : ℝ[X]) : weighted t (stein t P)=0 := by
 induction P using Polynomial.induction_on' with
 | add P Q hP hQ =>rw [stein_add,map_add,hP,hQ,add_zero]
 | monomial n c =>
   rw [←C_mul_X_pow_eq_monomial,stein_C_mul,weighted_C_mul,weighted_stein_power,mul_zero]

def generator (t : ℝ) (P : ℝ[X]) : ℝ[X] := C (1/4)*stein t P.derivative

theorem weighted_generator (t : ℝ) (P : ℝ[X]) : weighted t (generator t P)=0 := by
 rw [generator,weighted_C_mul,weighted_stein,mul_zero]

theorem weighted_ibp (t : ℝ) (P Q : ℝ[X]) :
 weighted t (P*generator t Q)= -(1/4)*weighted t ((1-X^2)*P.derivative*Q.derivative) := by
 have hp : P*generator t Q=C (1/4)*(stein t (P*Q.derivative)-(1-X^2)*P.derivative*Q.derivative) := by
   simp only [generator,stein,derivative_mul]
   ring
 rw [hp,weighted_C_mul,map_sub,weighted_stein,zero_sub]
 ring

open QuaternionSU2Representation

theorem su2_integral (t : ℝ) (P : ℝ[X]) :
 (∫ A : SU2,P.eval (halfTrace A) ∂BoundedExponentialTiltResponse.tiltedMeasure
   QuaternionSU2Representation.law halfTrace t)=
 weighted t P/BoundedExponentialTiltResponse.partition QuaternionAngularHaar.law realCoordinate t := by
 rw [BoundedExponentialTiltResponse.tilted_integral QuaternionSU2Representation.law _ _
   halfTrace_measurable halfTrace_bound t,
   expectation_halfTrace QuaternionSU2Representation.law (fun x => P.eval x) P.continuous.measurable t]
 rfl

theorem generator_frame_formula (t : ℝ) (P : ℝ[X]) (A : SU2) :
 (generator t P).eval (halfTrace A)=
 SU2RadialLaplacian.laplacian (SU2RadialFrameCalculus.radial (fun x => P.eval x)) A+
 t*P.derivative.eval (halfTrace A)*(1-(halfTrace A)^2)/4 := by
 rw [SU2RadialLaplacian.radial_formula (fun x => P.eval x)
   (fun x => P.derivative.eval x) (fun x => P.derivative.derivative.eval x)
   (fun x => P.hasDerivAt x) (fun x => P.derivative.hasDerivAt x)]
 simp only [generator,stein,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_sub,
   Polynomial.eval_one,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]
 ring

open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicLinkStaples

def linkOrientation (e : SpatialEdge) (U W : State) (r : PeriodicLinkDisintegration.Rest e) : SU2 :=
 SU2StaplePolar.orientation (SU2StaplePolar.quaternionSum (stapleSet e)
  (stapleWord U (PeriodicLinkDisintegration.baseField e r) W r.2.1 r.2.2 e))

def linkParameter (e : SpatialEdge) (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) : ℝ :=
 SU2StapleTiltLaw.concentration (stapleSet e)
  (stapleWord U (PeriodicLinkDisintegration.baseField e r) W r.2.1 r.2.2 e) β

theorem link_map (e : SpatialEdge) (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) :
 (PeriodicLinkDisintegration.conditionalKernel e β U W r).map (fun A => linkOrientation e U W r*A)=
 BoundedExponentialTiltResponse.tiltedMeasure QuaternionSU2Representation.law halfTrace (linkParameter e β U W r) := by
 rw [PeriodicLinkDisintegration.kernel_eq_linkLaw,linkLaw_eq_stapleLaw]
 exact SU2StapleTiltLaw.stapleLaw_map QuaternionSU2Representation.law _ _ β

theorem link_integral (e : SpatialEdge) (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) (P : ℝ[X]) :
 (∫ A,P.eval (halfTrace (linkOrientation e U W r*A)) ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
 weighted (linkParameter e β U W r) P/
  BoundedExponentialTiltResponse.partition QuaternionAngularHaar.law realCoordinate (linkParameter e β U W r) := by
 have he:=integral_map (μ:=PeriodicLinkDisintegration.conditionalKernel e β U W r)
   (measurable_const_mul (linkOrientation e U W r)).aemeasurable
   (P.continuous.measurable.comp halfTrace_measurable).aestronglyMeasurable
 rw [link_map] at he
 exact he.symm.trans (su2_integral _ P)

theorem link_generator_stationary (e : SpatialEdge) (β : ℝ) (U W : State)
 (r : PeriodicLinkDisintegration.Rest e) (P : ℝ[X]) :
 (∫ A,(generator (linkParameter e β U W r) P).eval (halfTrace (linkOrientation e U W r*A))
  ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=0 := by
 rw [link_integral,weighted_generator,zero_div]

theorem link_generator_ibp (e : SpatialEdge) (β : ℝ) (U W : State)
 (r : PeriodicLinkDisintegration.Rest e) (P Q : ℝ[X]) :
 (∫ A,(P*generator (linkParameter e β U W r) Q).eval (halfTrace (linkOrientation e U W r*A))
  ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
 -(1/4)*(∫ A,((1-X^2)*P.derivative*Q.derivative).eval (halfTrace (linkOrientation e U W r*A))
  ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
 rw [link_integral,link_integral,weighted_ibp]
 ring

open SU2BoundedObservableGradient SU2RadialFrameCalculus SU2TiltEnergyResponse

def frameGenerator (t : ℝ) (P : ℝ[X]) (A : SU2) : ℝ :=
 SU2RadialLaplacian.laplacian (radial (fun x => P.eval x)) A+
 t*∑ a : Fin 3, traceSlope (A : SU2TraceHessianModel.M2) a*
   deriv (fun s => radial (fun x => P.eval x) (groupCurve A a s)) 0

theorem frameGenerator_polynomial (t : ℝ) (P : ℝ[X]) (A : SU2) :
 frameGenerator t P A=(generator t P).eval (halfTrace A) := by
 have hd (a : Fin 3) : deriv (fun s => radial (fun x => P.eval x) (groupCurve A a s)) 0=
   P.derivative.eval (halfTrace A)*traceSlope (A : SU2TraceHessianModel.M2) a :=
   (radial_derivative (fun x => P.eval x) _ A a (P.hasDerivAt _)).deriv
 unfold frameGenerator
 simp_rw [hd]
 have hs : (∑ a : Fin 3,traceSlope (A : SU2TraceHessianModel.M2) a*
   (P.derivative.eval (halfTrace A)*traceSlope (A : SU2TraceHessianModel.M2) a))=
   P.derivative.eval (halfTrace A)*(1-(halfTrace A)^2)/4 := by
   calc
    _ = P.derivative.eval (halfTrace A)*(∑ a : Fin 3,traceSlope (A : SU2TraceHessianModel.M2) a^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [traceSlope_square_sum];ring
 rw [hs,generator_frame_formula]
 ring

def axisObservable (C : SU2) (P : ℝ[X]) (A : SU2) : ℝ := P.eval (halfTrace (C*A))

theorem groupCurve_left (C A : SU2) (a : Fin 3) (s : ℝ) : groupCurve (C*A) a s=C*groupCurve A a s := by
 apply Subtype.ext
 change ((C : SU2TraceHessianModel.M2)*(A : SU2TraceHessianModel.M2))*NormedSpace.exp (s • SU2TraceHessianModel.tangent a)=
   (C : SU2TraceHessianModel.M2)*((A : SU2TraceHessianModel.M2)*NormedSpace.exp (s • SU2TraceHessianModel.tangent a))
 exact mul_assoc _ _ _

def axisGenerator (C : SU2) (t : ℝ) (P : ℝ[X]) (A : SU2) : ℝ :=
 SU2RadialLaplacian.laplacian (axisObservable C P) A+
 t*∑ a : Fin 3, deriv (fun s => axisObservable C X (groupCurve A a s)) 0*
   deriv (fun s => axisObservable C P (groupCurve A a s)) 0

theorem axisGenerator_polynomial (C : SU2) (t : ℝ) (P : ℝ[X]) (A : SU2) :
 axisGenerator C t P A=(generator t P).eval (halfTrace (C*A)) := by
 have hx (a : Fin 3) : deriv (fun s => axisObservable C X (groupCurve A a s)) 0=
   traceSlope ((C*A : SU2) : SU2TraceHessianModel.M2) a := by
   simp only [axisObservable,Polynomial.eval_X,←groupCurve_left]
   exact (traceCurve_derivative ((C*A : SU2) : SU2TraceHessianModel.M2) a).deriv
 change _= (generator t P).eval (halfTrace (C*A))
 rw [←frameGenerator_polynomial]
 unfold axisGenerator frameGenerator SU2RadialLaplacian.laplacian
 simp_rw [hx]
 simp only [axisObservable,←groupCurve_left,radial]

theorem actual_link_generator_stationary (e : SpatialEdge) (β : ℝ) (U W : State)
 (r : PeriodicLinkDisintegration.Rest e) (P : ℝ[X]) :
 (∫ A,axisGenerator (linkOrientation e U W r) (linkParameter e β U W r) P A
   ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=0 := by
 simp_rw [axisGenerator_polynomial]
 exact link_generator_stationary e β U W r P

theorem actual_link_generator_ibp (e : SpatialEdge) (β : ℝ) (U W : State)
 (r : PeriodicLinkDisintegration.Rest e) (P Q : ℝ[X]) :
 (∫ A,axisObservable (linkOrientation e U W r) P A*
   axisGenerator (linkOrientation e U W r) (linkParameter e β U W r) Q A
   ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
 -(1/4)*(∫ A,((1-X^2)*P.derivative*Q.derivative).eval (halfTrace (linkOrientation e U W r*A))
   ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
 have he : (fun A => axisObservable (linkOrientation e U W r) P A*
   axisGenerator (linkOrientation e U W r) (linkParameter e β U W r) Q A)=
   fun A => (P*generator (linkParameter e β U W r) Q).eval (halfTrace (linkOrientation e U W r*A)) := by
   funext A
   rw [axisGenerator_polynomial]
   simp only [axisObservable,Polynomial.eval_mul]
 rw [he]
 exact link_generator_ibp e β U W r P Q

theorem actual_link_generator_dissipative (e : SpatialEdge) (β : ℝ) (U W : State)
 (r : PeriodicLinkDisintegration.Rest e) (P : ℝ[X]) :
 (∫ A,axisObservable (linkOrientation e U W r) P A*
   axisGenerator (linkOrientation e U W r) (linkParameter e β U W r) P A
   ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)≤0 := by
 rw [actual_link_generator_ibp]
 apply mul_nonpos_of_nonpos_of_nonneg (by norm_num)
 apply integral_nonneg
 intro A
 simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_pow,Polynomial.eval_X]
 have hx : 0≤1-(halfTrace (linkOrientation e U W r*A))^2 := by
   have hb:=(sq_le_one_iff_abs_le_one _).mpr (halfTrace_bound (linkOrientation e U W r*A))
   linarith
 convert mul_nonneg hx (sq_nonneg (P.derivative.eval (halfTrace (linkOrientation e U W r*A)))) using 1; ring

theorem axisObservable_continuous (C : SU2) (P : ℝ[X]) : Continuous (axisObservable C P) := by
 have hm : Continuous (fun A : SU2 => ((C*A : SU2) : SU2TraceHessianModel.M2)) :=
   continuous_subtype_val.comp (continuous_const.mul continuous_id)
 have ht : Continuous (fun A : SU2 => halfTrace (C*A)) :=
   (SU2ProductCurveHessian.realTraceCLM.continuous.comp hm).div_const 2
 exact P.continuous.comp ht

theorem actual_link_observable_integrable (e : SpatialEdge) (β : ℝ) (U W : State)
 (r : PeriodicLinkDisintegration.Rest e) (P : ℝ[X]) :
 Integrable (axisObservable (linkOrientation e U W r) P)
  (PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
 let _:=PeriodicLinkDisintegration.kernel_markov e β U W
 exact (axisObservable_continuous _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem actual_link_generator_integrable (e : SpatialEdge) (β : ℝ) (U W : State)
 (r : PeriodicLinkDisintegration.Rest e) (P : ℝ[X]) :
 Integrable (axisGenerator (linkOrientation e U W r) (linkParameter e β U W r) P)
  (PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
 have he : axisGenerator (linkOrientation e U W r) (linkParameter e β U W r) P=
   axisObservable (linkOrientation e U W r) (generator (linkParameter e β U W r) P) :=
   funext (axisGenerator_polynomial _ _ _)
 rw [he]
 exact actual_link_observable_integrable e β U W r _

theorem actual_link_product_integrable (e : SpatialEdge) (β : ℝ) (U W : State)
 (r : PeriodicLinkDisintegration.Rest e) (P Q : ℝ[X]) :
 Integrable (fun A => axisObservable (linkOrientation e U W r) P A*
   axisGenerator (linkOrientation e U W r) (linkParameter e β U W r) Q A)
  (PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
 have he : (fun A => axisObservable (linkOrientation e U W r) P A*
   axisGenerator (linkOrientation e U W r) (linkParameter e β U W r) Q A)=
   axisObservable (linkOrientation e U W r) (P*generator (linkParameter e β U W r) Q) := by
   funext A
   rw [axisGenerator_polynomial]
   simp only [axisObservable,Polynomial.eval_mul]
 rw [he]
 exact actual_link_observable_integrable e β U W r _

theorem weighted_transverse_zero (t : ℝ) (P : ℝ[X]) :
 (∫ u : Group,imaginary 0 u*P.eval (realCoordinate u)*Real.exp (t*realCoordinate u)
   ∂QuaternionAngularHaar.law)=0 := by
 apply QuaternionTiltCovariance.weighted_odd_zero 1
 intro u
 rw [QuaternionTiltCovariance.conjugate_imaginary,QuaternionTiltCovariance.conjugate_real]
 norm_num

theorem radial_core_distance (P : ℝ[X]) :
 (1/4:ℝ)≤∫ u : Group,(imaginary 0 u-P.eval (realCoordinate u))^2 ∂QuaternionAngularHaar.law := by
 have hi : Continuous (imaginary 0) := by
   change Continuous (fun u : Group => (u : Quaternion ℝ).imI)
   exact Quaternion.continuous_imI.comp continuous_subtype_val
 have hr : Continuous (realCoordinate : Group → ℝ) := Quaternion.continuous_re.comp continuous_subtype_val
 have hp:=P.continuous.comp hr
 have hi2 : Integrable (fun u : Group => imaginary 0 u^2) QuaternionAngularHaar.law := (hi.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hp2 : Integrable (fun u : Group => (P.eval (realCoordinate u))^2) QuaternionAngularHaar.law := (hp.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hip : Integrable (fun u : Group => imaginary 0 u*P.eval (realCoordinate u)) QuaternionAngularHaar.law := (hi.mul hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hz : (∫ u : Group,imaginary 0 u*P.eval (realCoordinate u) ∂QuaternionAngularHaar.law)=0 := by
   simpa only [zero_mul,Real.exp_zero,mul_one] using weighted_transverse_zero 0 P
 have h2:=QuaternionTiltCovariance.imaginary_second_zero 0
 rw [BoundedExponentialTiltResponse.expectation_zero] at h2
 have he : (∫ u : Group,(imaginary 0 u-P.eval (realCoordinate u))^2 ∂QuaternionAngularHaar.law)=
   (1/4:ℝ)+(∫ u : Group,(P.eval (realCoordinate u))^2 ∂QuaternionAngularHaar.law) := by
   simp_rw [sub_sq,mul_assoc]
   have ha:=integral_add (hi2.sub (hip.const_mul 2)) hp2
   have hb:=integral_sub hi2 (hip.const_mul 2)
   simp only [Pi.sub_apply] at ha hb
   rw [ha,hb]
   rw [integral_const_mul,hz,h2]
   ring
 rw [he]
 have hn : 0≤∫ u : Group,(P.eval (realCoordinate u))^2 ∂QuaternionAngularHaar.law :=
   integral_nonneg (fun u => sq_nonneg (P.eval (realCoordinate u)))
 linarith [hn]
end OperatorDerivativeRewrite.Foundation.WilsonRadialLangevin
