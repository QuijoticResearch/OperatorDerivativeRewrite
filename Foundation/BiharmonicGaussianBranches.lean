import Foundation.AnalyticInverseClock
import Foundation.ComplexGaussianPolynomialTransport
import Foundation.IBMConstructedSources
import Foundation.ComplexFourthRootNoise
/-! A persistent-branch genuine complex Brownian process realizes the biharmonic
analytic polynomial means. It is not a real signed path measure or inverse clock. -/
noncomputable section
open Polynomial MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BiharmonicGaussianBranches
open ComplexGaussianPolynomialTransport PseudoPolynomialStein

def plus (t : ℝ≥0) : ℝ[X] →ₗ[ℝ] ℂ := average (t/2) 0 (1+I)
def minus (t : ℝ≥0) : ℝ[X] →ₗ[ℝ] ℂ := average (t/2) 0 (1-I)
def mean (t : ℝ≥0) : ℝ[X] →ₗ[ℝ] ℂ := (1/2:ℝ) • (plus t+minus t)
def contrast (t : ℝ≥0) : ℝ[X] →ₗ[ℝ] ℂ := (1/2:ℝ) • (plus t-minus t)

theorem plus_apply (t : ℝ≥0) (P : ℝ[X]) :
    plus t P=∫ y : ℝ,(P.map (algebraMap ℝ ℂ)).eval ((1+I)*(y:ℂ)) ∂RiemannQuadraticGaussian.law (t/2) := by
  simp only [plus,average_apply,zero_add]

theorem minus_apply (t : ℝ≥0) (P : ℝ[X]) :
    minus t P=∫ y : ℝ,(P.map (algebraMap ℝ ℂ)).eval ((1-I)*(y:ℂ)) ∂RiemannQuadraticGaussian.law (t/2) := by
  simp only [minus,average_apply,zero_add]

theorem mean_apply (t : ℝ≥0) (P : ℝ[X]) : mean t P=(plus t P+minus t P)/2 := by
  simp only [mean,LinearMap.smul_apply,LinearMap.add_apply,Complex.real_smul]
  push_cast
  ring

theorem contrast_apply (t : ℝ≥0) (P : ℝ[X]) : contrast t P=(plus t P-minus t P)/2 := by
  simp only [contrast,LinearMap.smul_apply,LinearMap.sub_apply,Complex.real_smul]
  push_cast
  ring

theorem plus_stein (t : ℝ≥0) (P : ℝ[X]) :
    plus t (X*P)=2*I*(t:ℂ)*plus t P.derivative := by
  have h := average_mul_X (t/2) 0 (1+I) P
  change plus t (X*P)=0*plus t P+(2*((t/2:ℝ≥0):ℝ):ℂ)*(1+I)^2*plus t P.derivative at h
  have he : (1+I)^2=(2:ℂ)*I := by
    calc
      _ = 1+2*I+I^2 := by ring
      _ = _ := by rw [Complex.I_sq];ring
  rw [he,zero_mul,zero_add] at h
  convert h using 1;push_cast;ring

theorem minus_stein (t : ℝ≥0) (P : ℝ[X]) :
    minus t (X*P)= -(2*I*(t:ℂ))*minus t P.derivative := by
  have h := average_mul_X (t/2) 0 (1-I) P
  change minus t (X*P)=0*minus t P+(2*((t/2:ℝ≥0):ℝ):ℂ)*(1-I)^2*minus t P.derivative at h
  have he : (1-I)^2= -(2:ℂ)*I := by
    calc
      _ = 1-2*I+I^2 := by ring
      _ = _ := by rw [Complex.I_sq];ring
  rw [he,zero_mul,zero_add] at h
  convert h using 1;push_cast;ring

theorem mean_stein (t : ℝ≥0) (P : ℝ[X]) :
    mean t (X*P)=2*I*(t:ℂ)*contrast t P.derivative := by
  rw [mean_apply,plus_stein,minus_stein,contrast_apply]
  ring

theorem contrast_stein (t : ℝ≥0) (P : ℝ[X]) :
    contrast t (X*P)=2*I*(t:ℂ)*mean t P.derivative := by
  rw [contrast_apply,plus_stein,minus_stein,mean_apply]
  ring

theorem branch_power (t : ℝ≥0) (a : ℂ) (n : ℕ) :
    average (t/2) 0 a (X^n)=a^n*(moment 2 ((t:ℝ)/2) n:ℂ) := by
  rw [average_apply]
  simp only [Polynomial.map_pow,Polynomial.map_X,eval_pow,eval_X,zero_add,mul_pow]
  rw [integral_const_mul,complex_power_average]
  rfl

theorem mean_power (t : ℝ≥0) (n : ℕ) :
    mean t (X^n)=((1+I)^n+(1-I)^n)/2*(moment 2 ((t:ℝ)/2) n:ℂ) := by
  rw [mean_apply]
  change (average (t/2) 0 (1+I) (X^n)+average (t/2) 0 (1-I) (X^n))/2=_
  rw [branch_power,branch_power]
  ring
theorem phase_fourth_plus : (1+I)^4=(-4:ℂ) := by
  simpa [ComplexFourthRootNoise.root] using ComplexFourthRootNoise.root_fourth (0:Fin 4)

theorem phase_fourth_minus : (1-I)^4=(-4:ℂ) := by
  simpa [ComplexFourthRootNoise.root] using ComplexFourthRootNoise.root_fourth (3:Fin 4)

theorem mean_multiple (t : ℝ≥0) (k : ℕ) :
    mean t (X^(4*k))=(((4*k).factorial:ℂ)*(-1)^k*(t:ℂ)^(2*k)/( (2*k).factorial:ℂ)) := by
  have hp : (1+I)^(4*k)=(-4:ℂ)^k := by rw [pow_mul,phase_fourth_plus]
  have hn : (1-I)^(4*k)=(-4:ℂ)^k := by rw [pow_mul,phase_fourth_minus]
  have hm := moment_multiple 2 (by norm_num) ((t:ℝ)/2) (2*k)
  rw [show 2*(2*k)=4*k from by omega] at hm
  rw [mean_power,hp,hn,hm]
  push_cast
  have hscale : (-4:ℂ)^k*((t:ℂ)/2)^(2*k)=(-1:ℂ)^k*(t:ℂ)^(2*k) := by
    rw [pow_mul,←mul_pow,show (-4:ℂ)*((t:ℂ)/2)^2= -((t:ℂ)^2) from by ring,neg_pow,pow_mul]
  calc
    _ = ((4*k).factorial:ℂ)/((2*k).factorial:ℂ)*((-4:ℂ)^k*((t:ℂ)/2)^(2*k)) := by ring
    _ = _ := by rw [hscale];ring

theorem mean_off (t : ℝ≥0) (n : ℕ) (hn : ¬4∣n) : mean t (X^n)=0 := by
  rcases n.even_or_odd' with ⟨k,rfl | rfl⟩
  · rcases k.even_or_odd' with ⟨j,rfl | rfl⟩
    · exact (hn ⟨j,by omega⟩).elim
    · have hp : (1+I)^(2*(2*j+1))=(-4:ℂ)^j*(1+I)^2 := by
        rw [show 2*(2*j+1)=4*j+2 from by omega,pow_add,pow_mul,phase_fourth_plus]
      have hm : (1-I)^(2*(2*j+1))=(-4:ℂ)^j*(1-I)^2 := by
        rw [show 2*(2*j+1)=4*j+2 from by omega,pow_add,pow_mul,phase_fourth_minus]
      rw [mean_power,hp,hm]
      have he : (1+I)^2+(1-I)^2=(0:ℂ) := by ring_nf;norm_num
      have hz : (-4:ℂ)^j*(1+I)^2+(-4:ℂ)^j*(1-I)^2=0 := by rw [←mul_add,he,mul_zero]
      rw [hz,zero_div,zero_mul]
  · rw [mean_power,moment_off_order 2 (by norm_num) _ _ (by rintro ⟨j,hj⟩;omega)]
    simp

open FactorialAnalyticDomain in
def analyticMean (t : ℝ≥0) : ℝ[X] →ₗ[ℝ] ℂ :=
  Complex.ofRealCLM.toLinearMap.comp
    ((AnalyticInverseClock.composed 4 (by norm_num) (-1) (by norm_num) t).toLinearMap.comp polynomialMap)

open FactorialAnalyticDomain in
theorem analyticMean_multiple (t : ℝ≥0) (k : ℕ) :
    analyticMean t (X^(4*k))=((4*k).factorial:ℂ)*(-1)^k*(t:ℂ)^(2*k)/((2*k).factorial:ℂ) := by
  have hs := AnalyticInverseClock.composed_series 4 (by norm_num) (-1) (by norm_num) t (polynomial (X^(4*k)))
  have hv : AnalyticInverseClock.composed 4 (by norm_num) (-1) (by norm_num) t (polynomial (X^(4*k)))=
      ((4*k).factorial:ℝ)*(-1)^k*(t:ℝ)^(2*k)/((2*k).factorial:ℝ) := by
    rw [←hs.tsum_eq,tsum_eq_single k]
    · simp only [polynomial_apply,coeff_X_pow_self,mul_one]
      ring
    · intro n hn
      have he : 4*n≠4*k := by omega
      simp only [polynomial_apply,coeff_X_pow,ite_eq_right he,mul_zero,zero_mul,zero_div]
  change (AnalyticInverseClock.composed 4 _ (-1) _ t (polynomial (X^(4*k))):ℂ)=_
  rw [hv]
  push_cast
  rfl

open FactorialAnalyticDomain in
theorem analyticMean_off (t : ℝ≥0) (n : ℕ) (hn : ¬4∣n) : analyticMean t (X^n)=0 := by
  have hs := AnalyticInverseClock.composed_series 4 (by norm_num) (-1) (by norm_num) t (polynomial (X^n))
  have he (k : ℕ) : (-1:ℝ)^k*polynomial (X^n) (4*k)*(t:ℝ)^(2*k)/((2*k).factorial:ℝ)=0 := by
    have hz : 4*k≠n := by intro h;exact hn ⟨k,h.symm⟩
    simp only [polynomial_apply,coeff_X_pow,ite_eq_right hz,mul_zero,zero_mul,zero_div]
  simp_rw [he] at hs
  have hv : AnalyticInverseClock.composed 4 (by norm_num) (-1) (by norm_num) t (polynomial (X^n))=0 :=
    hs.unique hasSum_zero
  change (AnalyticInverseClock.composed 4 _ (-1) _ t (polynomial (X^n)):ℂ)=0
  rw [hv];rfl

theorem mean_eq_analyticMean (t : ℝ≥0) : mean t=analyticMean t := by
  have hp (n : ℕ) : mean t (X^n)=analyticMean t (X^n) := by
    by_cases hn : 4∣n
    · obtain ⟨k,rfl⟩ := hn
      rw [mean_multiple,analyticMean_multiple]
    · rw [mean_off t n hn,analyticMean_off t n hn]
  apply LinearMap.ext
  intro P
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add,map_add,hP,hQ]
  | monomial n c =>
    rw [show monomial n c=c • (X:ℝ[X])^n by simp [smul_eq_C_mul,C_mul_X_pow_eq_monomial],map_smul,map_smul,hp]

open InfiniteGaussian IBMConstructedSources

def fair : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance fair_probability : IsProbabilityMeasure fair := by unfold fair;infer_instance

theorem fair_integral (f : Bool → ℂ) : (∫ b, f b ∂fair)=(f true+f false)/2 := by
  rw [fair,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,Fintype.card_bool,Fintype.sum_bool]
  norm_num [Complex.real_smul]
  ring

abbrev Sample := Bool × SampleSpace

def probability : Measure Sample := fair.prod gaussianProduct

instance probability_isProbability : IsProbabilityMeasure probability := by unfold probability;infer_instance

def phase (b : Bool) : ℂ := if b then 1+I else 1-I

theorem phase_measurable : Measurable phase := measurable_of_countable _

def path (w : Sample) : C(ℝ≥0,ℂ) :=
  ⟨fun t => phase w.1*(clockPath w.2 t:ℂ),by fun_prop⟩

def value (t : ℝ≥0) (w : Sample) : ℂ := path w t

theorem value_eq (t : ℝ≥0) (w : Sample) : value t w=phase w.1*(clockPath w.2 t:ℂ) := rfl

theorem value_continuous (w : Sample) : Continuous (fun t => value t w) := (path w).continuous

theorem value_measurable (t : ℝ≥0) : Measurable (value t) := by
  exact (phase_measurable.comp measurable_fst).mul
    (Complex.continuous_ofReal.measurable.comp
      ((ContinuousMap.measurable_eval t).comp (clockPath_measurable.comp measurable_snd)))

theorem path_measurable : Measurable path := ContinuousMap.measurable_iff_eval.mpr value_measurable

theorem value_jointly_measurable : Measurable (fun p : ℝ≥0 × Sample => value p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable value_continuous value_measurable

theorem brownian_law (t : ℝ≥0) : HasLaw (fun w => clockPath w t)
    (RiemannQuadraticGaussian.law (t/2)) gaussianProduct := by
  have h := clock_isBrownian.toIsPreBrownianReal.hasLaw_eval t
  have he : RiemannQuadraticGaussian.law (t/2)=gaussianReal 0 t := by
    unfold RiemannQuadraticGaussian.law
    congr 1
    field_simp
  rw [he]
  exact h

theorem branch_integrable (t : ℝ≥0) (b : Bool) (P : ℝ[X]) :
    Integrable (fun w : SampleSpace => (P.map (algebraMap ℝ ℂ)).eval
      (phase b*(clockPath w t:ℂ))) gaussianProduct := by
  have hi := shifted_polynomial_integrable (t/2) (P.map (algebraMap ℝ ℂ)) 0 (phase b)
  simpa only [Function.comp_def,zero_add] using (brownian_law t).integrable_comp hi

theorem branch_integral (t : ℝ≥0) (b : Bool) (P : ℝ[X]) :
    (∫ w : SampleSpace, (P.map (algebraMap ℝ ℂ)).eval (phase b*(clockPath w t:ℂ)) ∂gaussianProduct)=
      average (t/2) 0 (phase b) P := by
  have h := (brownian_law t).integral_comp (f:=fun y : ℝ =>
    (P.map (algebraMap ℝ ℂ)).eval (phase b*(y:ℂ))) (by fun_prop)
  simpa only [Function.comp_def,average_apply,zero_add] using h

theorem polynomial_integrable (t : ℝ≥0) (P : ℝ[X]) :
    Integrable (fun w => (P.map (algebraMap ℝ ℂ)).eval (value t w)) probability := by
  have hm : Measurable (fun w => (P.map (algebraMap ℝ ℂ)).eval (value t w)) :=
    (by fun_prop : Continuous (fun z : ℂ => (P.map (algebraMap ℝ ℂ)).eval z)).measurable.comp (value_measurable t)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun b => branch_integrable t b P
  · exact Integrable.of_finite

theorem process_mean (t : ℝ≥0) (P : ℝ[X]) :
    (∫ w, (P.map (algebraMap ℝ ℂ)).eval (value t w) ∂probability)=analyticMean t P := by
  rw [probability,integral_prod _ (polynomial_integrable t P),fair_integral]
  change ((∫ w, (P.map (algebraMap ℝ ℂ)).eval (phase true*(clockPath w t:ℂ)) ∂gaussianProduct)+
    (∫ w, (P.map (algebraMap ℝ ℂ)).eval (phase false*(clockPath w t:ℂ)) ∂gaussianProduct))/2=_
  rw [branch_integral,branch_integral]
  change (plus t P+minus t P)/2=_
  rw [←mean_apply,mean_eq_analyticMean]

def pathLaw : Measure C(ℝ≥0,ℂ) := probability.map path

theorem pathLaw_isProbability : IsProbabilityMeasure pathLaw := by
  unfold pathLaw
  infer_instance

def sign (b : Bool) : ℝ := if b then 1 else -1

def observation (z : ℂ) : ℝ := z.im/z.re

theorem observation_measurable : Measurable observation :=
  Complex.continuous_im.measurable.div Complex.continuous_re.measurable

theorem value_re (t : ℝ≥0) (w : Sample) : (value t w).re=clockPath w.2 t := by
  rcases w with ⟨b,w⟩
  cases b <;> simp [value_eq,phase,Complex.mul_re]

theorem value_im (t : ℝ≥0) (w : Sample) : (value t w).im=sign w.1*clockPath w.2 t := by
  rcases w with ⟨b,w⟩
  cases b <;> simp [value_eq,phase,sign,Complex.mul_im]

theorem observed_sign (t : ℝ≥0) (w : Sample) (hw : clockPath w.2 t≠0) :
    observation (value t w)=sign w.1 := by
  rw [observation,value_im,value_re,mul_div_cancel_right₀ _ hw]

theorem observed_sign_ae (t : ℝ≥0) (ht : 0<t) :
    (fun w => observation (value t w))=ᵐ[probability] (fun w => sign w.1) := by
  let : NullSingletonClass (gaussianReal 0 t) := nullSingletonClass_gaussianReal (ne_of_gt ht)
  have hb := clock_isBrownian.toIsPreBrownianReal.hasLaw_eval t
  have hl : HasLaw (fun w : Sample => clockPath w.2 t) (gaussianReal 0 t) probability := by
    simpa only [probability,Function.comp_def] using hb.comp
      (measurePreserving_snd (μ:=fair) (ν:=gaussianProduct)).hasLaw
  have hz : probability {w | clockPath w.2 t=0}=0 := by
    rw [hl.measure_eq (p:=fun x : ℝ => x=0) (by simpa using measurableSet_singleton (0:ℝ))]
    simp
  have hn : ∀ᵐ w ∂probability, clockPath w.2 t≠0 := by
    rw [ae_iff]
    simpa only [not_not] using hz
  filter_upwards [hn] with w hw
  exact observed_sign t w hw

theorem mean_square (t : ℝ≥0) : mean t (X^2)=0 := by
  rw [mean_off t 2 (by omega)]

theorem contrast_square (t : ℝ≥0) : contrast t (X^2)=2*I*(t:ℂ) := by
  rw [show (X^2:ℝ[X])=X*X from by ring,contrast_stein]
  simp only [derivative_X,mean_apply,plus,minus,average_one]
  ring

theorem plus_from_channels (t : ℝ≥0) (P : ℝ[X]) : plus t P=mean t P+contrast t P := by
  rw [mean_apply,contrast_apply]
  ring

theorem minus_from_channels (t : ℝ≥0) (P : ℝ[X]) : minus t P=mean t P-contrast t P := by
  rw [mean_apply,contrast_apply]
  ring

theorem branch_square (t : ℝ≥0) (b : Bool) :
    (∫ w : SampleSpace, value t (b,w)^2 ∂gaussianProduct)=2*I*(t:ℂ)*(sign b:ℂ) := by
  have h := branch_integral t b (X^2)
  simp only [Polynomial.map_pow,Polynomial.map_X,eval_pow,eval_X] at h
  change (∫ w : SampleSpace, value t (b,w)^2 ∂gaussianProduct)=_ at h
  cases b
  · change _=minus t (X^2) at h
    rw [h,minus_from_channels,mean_square,contrast_square]
    simp [sign]
  · change _=plus t (X^2) at h
    rw [h,plus_from_channels,mean_square,contrast_square]
    simp [sign]

theorem square_not_branch_centered (t : ℝ≥0) (ht : 0<t) :
    ¬∀ b : Bool, (∫ w : SampleSpace, value t (b,w)^2 ∂gaussianProduct)=0 := by
  intro h
  have hh := h true
  rw [branch_square] at hh
  have he : (t:ℂ)≠0 := by exact_mod_cast (ne_of_gt ht)
  simp only [sign,ite_true,Complex.ofReal_one,mul_one] at hh
  exact (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) he) hh

end OperatorDerivativeRewrite.Foundation.BiharmonicGaussianBranches
