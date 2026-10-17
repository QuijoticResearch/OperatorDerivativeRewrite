import Foundation.GaussianSwirlPressureDomain
import Foundation.GaussianDeterminantConditional

/-! Actual Gaussian quadratic Laplace kernels for the constructed swirl pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Interval ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianSwirlLaplace
set_option backward.isDefEq.respectTransparency false
open GaussianSwirlVelocity GaussianSwirlPressureDomain HelicalRadialGaussianBridge
open HelicalWeightedPressureIBP HelicalPressureProjection

local instance : IsProbabilityMeasure physicalGaussian := by unfold physicalGaussian; infer_instance

def damping (a : ℝ) (x : ℝ × ℝ) : ℝ := Real.exp (-a*radiusSq x)

theorem damping_pos (a : ℝ) (x : ℝ × ℝ) : 0 < damping a x := Real.exp_pos _

theorem damping_le_one {a : ℝ} (ha : 0 ≤ a) (x : ℝ × ℝ) : damping a x ≤ 1 := by
  unfold damping
  rw [neg_mul]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha (radiusSq_nonneg x)))

theorem standard_radial_laplace (c : ℝ) (hc : 0 ≤ c) :
    (∫ x : ℝ × ℝ, Real.exp (-c*(x.1^2+x.2^2)) ∂GaussianDeterminantConditional.rowMeasure)=
      1/(1+2*c) := by
  have he (x : ℝ × ℝ) : Real.exp (-c*(x.1^2+x.2^2))=
      Real.exp (-c*x.1^2)*Real.exp (-c*x.2^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [GaussianDeterminantConditional.rowMeasure,integral_prod_mul (fun t : ℝ => Real.exp (-c*t^2))
    (fun t : ℝ => Real.exp (-c*t^2)),← pow_two,
    GaussianDeterminantConditional.square_laplace_squared c hc]

theorem physical_radial_laplace (a : ℝ) (ha : 0 ≤ a) :
    (∫ x, damping a x ∂physicalGaussian)=2/(2+a) := by
  have hm : MeasurePreserving (fun x : ℝ => x/2) (gaussianReal 0 1) (gaussianReal 0 (1/4)) := by
    refine ⟨by fun_prop,?_⟩
    have he := gaussianReal_map_div_const (μ := 0) (v := 1) (2 : ℝ)
    norm_num at he
    exact he
  have hi := (hm.prod hm).hasLaw.integral_comp
    (show AEStronglyMeasurable (damping a) physicalGaussian from by unfold damping radiusSq; fun_prop)
  have he (x : ℝ × ℝ) : damping a (x.1/2,x.2/2)=Real.exp (-(a/4)*(x.1^2+x.2^2)) := by
    unfold damping radiusSq
    congr 1
    ring
  change (∫ x : ℝ × ℝ, damping a (x.1/2,x.2/2) ∂GaussianDeterminantConditional.rowMeasure)=
    (∫ x, damping a x ∂physicalGaussian) at hi
  rw [← hi]
  simp_rw [he]
  rw [standard_radial_laplace (a/4) (by positivity)]
  have hd : 0 < 2+a := by positivity
  field_simp
  ring

theorem polynomial_damping_memLp (q : HelicalPolynomialPressureIBP.PlanePolynomial)
    (a : ℝ) (ha : 0 ≤ a) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun x : ℝ × ℝ => MvPolynomial.eval ![x.1,x.2] q*damping a x) r physicalGaussian := by
  have hq := HelicalPolynomialPressureIBP.polynomial_memLp q r hr
  refine hq.mono ?_ (ae_of_all _ (fun x => ?_))
  · exact ((q.continuous_eval.comp (by fun_prop)).mul
      (by unfold damping radiusSq; fun_prop)).aestronglyMeasurable
  · rw [norm_mul,Real.norm_eq_abs (damping a x),abs_of_pos (damping_pos a x)]
    exact mul_le_of_le_one_right (norm_nonneg _) (damping_le_one ha x)

theorem damping_memLp (a : ℝ) (ha : 0 ≤ a) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (damping a) r physicalGaussian := by
  simpa using polynomial_damping_memLp 1 a ha r hr

theorem x_damping_memLp (a : ℝ) (ha : 0 ≤ a) :
    MemLp (fun x : ℝ × ℝ => x.1*damping a x) 2 physicalGaussian := by
  simpa using polynomial_damping_memLp (MvPolynomial.X (0 : Fin 2)) a ha 2 (by simp)

theorem y_damping_memLp (a : ℝ) (ha : 0 ≤ a) :
    MemLp (fun x : ℝ × ℝ => x.2*damping a x) 2 physicalGaussian := by
  simpa using polynomial_damping_memLp (MvPolynomial.X (1 : Fin 2)) a ha 2 (by simp)

theorem x_square_damping_integrable (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun x : ℝ × ℝ => x.1^2*damping a x) physicalGaussian := by
  have h := polynomial_damping_memLp
    ((MvPolynomial.X (0 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^(2 : ℕ)) a ha 1 (by simp)
  simpa only [MvPolynomial.eval_pow,MvPolynomial.eval_X,Matrix.cons_val_zero] using h.integrable (by simp)

theorem y_square_damping_integrable (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun x : ℝ × ℝ => x.2^2*damping a x) physicalGaussian := by
  have h := polynomial_damping_memLp
    ((MvPolynomial.X (1 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^(2 : ℕ)) a ha 1 (by simp)
  simpa only [MvPolynomial.eval_pow,MvPolynomial.eval_X,Matrix.cons_val_one,Matrix.cons_val_zero] using h.integrable (by simp)

theorem damping_x (a x y : ℝ) : HasDerivAt (fun t => damping a (t,y))
    (-2*a*x*damping a (x,y)) x := by
  have hs : HasDerivAt (fun t : ℝ => t^2+y^2) (2*x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y^2)
  have hh := (hs.const_mul (-a)).exp
  change HasDerivAt (fun t => damping a (t,y)) (damping a (x,y)*(-a*(2*x))) x at hh
  convert hh using 1 <;> ring

theorem damping_y (a x y : ℝ) : HasDerivAt (fun t => damping a (x,t))
    (-2*a*y*damping a (x,y)) y := by
  have hs : HasDerivAt (fun t : ℝ => x^2+t^2) (2*y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (x^2)
  have hh := (hs.const_mul (-a)).exp
  change HasDerivAt (fun t => damping a (x,t)) (damping a (x,y)*(-a*(2*y))) y at hh
  convert hh using 1 <;> ring

theorem weighted_x_laplace (a : ℝ) (ha : 0 ≤ a) :
    (∫ x, x.1^2*damping a x ∂physicalGaussian)=1/(2+a)^2 := by
  have hd (x y : ℝ) : HasDerivAt (fun t => t*damping a (t,y))
      (damping a (x,y)-2*a*(x^2*damping a (x,y))) x := by
    have hh := (hasDerivAt_id x).mul (damping_x a x y)
    change HasDerivAt (fun t => t*damping a (t,y))
      (1*damping a (x,y)+x*(-2*a*x*damping a (x,y))) x at hh
    convert hh using 1 <;> ring
  have hi := x_square_damping_integrable a ha
  have hk := (damping_memLp a ha 1 (by simp)).integrable (by simp) |>.sub (hi.const_mul (2*a))
  have hs := stein_x hd (x_damping_memLp a ha) hk
  simp only [Pi.sub_apply] at hs
  rw [integral_sub ((damping_memLp a ha 1 (by simp)).integrable (by simp)) (hi.const_mul _),
    integral_const_mul,physical_radial_laplace a ha] at hs
  have he : (fun x : ℝ × ℝ => x.1*(x.1*damping a x))=fun x => x.1^2*damping a x := by funext x; ring
  rw [he] at hs
  have hpos : 0 < 2+a := by positivity
  field_simp at hs ⊢
  nlinarith [hs]

theorem weighted_y_laplace (a : ℝ) (ha : 0 ≤ a) :
    (∫ x, x.2^2*damping a x ∂physicalGaussian)=1/(2+a)^2 := by
  have hd (x y : ℝ) : HasDerivAt (fun t => t*damping a (x,t))
      (damping a (x,y)-2*a*(y^2*damping a (x,y))) y := by
    have hh := (hasDerivAt_id y).mul (damping_y a x y)
    change HasDerivAt (fun t => t*damping a (x,t))
      (1*damping a (x,y)+y*(-2*a*y*damping a (x,y))) y at hh
    convert hh using 1 <;> ring
  have hi := y_square_damping_integrable a ha
  have hk := (damping_memLp a ha 1 (by simp)).integrable (by simp) |>.sub (hi.const_mul (2*a))
  have hs := stein_y hd (y_damping_memLp a ha) hk
  simp only [Pi.sub_apply] at hs
  rw [integral_sub ((damping_memLp a ha 1 (by simp)).integrable (by simp)) (hi.const_mul _),
    integral_const_mul,physical_radial_laplace a ha] at hs
  have he : (fun x : ℝ × ℝ => x.2*(x.2*damping a x))=fun x => x.2^2*damping a x := by funext x; ring
  rw [he] at hs
  have hpos : 0 < 2+a := by positivity
  field_simp at hs ⊢
  nlinarith [hs]

theorem weighted_radial_laplace (a : ℝ) (ha : 0 ≤ a) :
    (∫ x, radiusSq x*damping a x ∂physicalGaussian)=2/(2+a)^2 := by
  have he : (fun x : ℝ × ℝ => radiusSq x*damping a x)=
      fun x => x.1^2*damping a x+x.2^2*damping a x := by funext x; unfold radiusSq; ring
  rw [he,integral_add (x_square_damping_integrable a ha) (y_square_damping_integrable a ha),
    weighted_x_laplace a ha,weighted_y_laplace a ha]
  ring

abbrev unitMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
abbrev parameterMeasure : Measure (ℝ × ℝ) := unitMeasure.prod unitMeasure

local instance : IsProbabilityMeasure unitMeasure := ⟨by simp [unitMeasure]⟩
local instance : IsProbabilityMeasure parameterMeasure := by infer_instance

theorem unit_nonneg : ∀ᵐ t ∂unitMeasure, 0 ≤ t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ht.1.le

theorem angularProfile_unit (s : ℝ) :
    angularProfile s=(∫ t, Real.exp (-|t| *s) ∂unitMeasure)/2 := by
  unfold angularProfile
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  apply congrArg (fun z : ℝ => z/2)
  apply integral_congr_ae
  filter_upwards [unit_nonneg] with t ht
  rw [abs_of_nonneg ht]

theorem parameter_damping_integral (x : ℝ × ℝ) :
    (∫ v, damping (|v.1|+|v.2|) x ∂parameterMeasure)=
      (∫ t, Real.exp (-|t| *radiusSq x) ∂unitMeasure)^2 := by
  have he (v : ℝ × ℝ) : damping (|v.1|+|v.2|) x=
      Real.exp (-|v.1| *radiusSq x)*Real.exp (-|v.2| *radiusSq x) := by
    unfold damping
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_prod_mul (fun t : ℝ => Real.exp (-|t| *radiusSq x))
    (fun t : ℝ => Real.exp (-|t| *radiusSq x)),pow_two]

theorem profile_square_mixture (x : ℝ × ℝ) : angularProfile (radiusSq x)^2=
    (1/4 : ℝ)*(∫ v, damping (|v.1|+|v.2|) x ∂parameterMeasure) := by
  rw [angularProfile_unit,parameter_damping_integral]
  ring

def mixtureKernel (v x : ℝ × ℝ) : ℝ := radiusSq x*damping (|v.1|+|v.2|) x

theorem radialEnergy_mixture (x : ℝ × ℝ) : radialEnergy x=
    (1/4 : ℝ)*(∫ v, mixtureKernel v x ∂parameterMeasure) := by
  rw [radialEnergy,profile_square_mixture]
  unfold mixtureKernel
  rw [integral_const_mul]
  ring

theorem radiusSq_integrable : Integrable radiusSq physicalGaussian := by
  have hx := x_square_damping_integrable 0 (by norm_num)
  have hy := y_square_damping_integrable 0 (by norm_num)
  change Integrable (fun x : ℝ × ℝ => x.1^2+x.2^2) physicalGaussian
  have hi := hx.add hy
  change Integrable (fun x : ℝ × ℝ => x.1^2*damping 0 x+x.2^2*damping 0 x) physicalGaussian at hi
  simpa only [damping,neg_zero,zero_mul,Real.exp_zero,mul_one] using hi

/-- Uniform Gaussian domination justifies the parameter/Gaussian interchange. -/
theorem mixtureKernel_integrable : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => mixtureKernel z.1 z.2)
    (parameterMeasure.prod physicalGaussian) := by
  have hi : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => radiusSq z.2)
      (parameterMeasure.prod physicalGaussian) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := parameterMeasure)).mul_prod radiusSq_integrable
  refine hi.mono' (by unfold mixtureKernel damping radiusSq; fun_prop) (ae_of_all _ (fun z => ?_))
  rw [mixtureKernel,norm_mul,Real.norm_eq_abs (radiusSq z.2),abs_of_nonneg (radiusSq_nonneg z.2),
    Real.norm_eq_abs (damping (|z.1.1|+|z.1.2|) z.2),abs_of_pos (damping_pos _ _)]
  exact mul_le_of_le_one_right (radiusSq_nonneg _) (damping_le_one (by positivity) _)

def rationalKernel (v : ℝ × ℝ) : ℝ := 1/(2+(|v.1|+|v.2|))^2

theorem mixtureKernel_integral (v : ℝ × ℝ) :
    (∫ x, mixtureKernel v x ∂physicalGaussian)=2*rationalKernel v := by
  unfold mixtureKernel
  rw [weighted_radial_laplace (|v.1|+|v.2|) (by positivity)]
  unfold rationalKernel
  ring

theorem rationalKernel_integrable : Integrable rationalKernel parameterMeasure := by
  have hi := mixtureKernel_integrable.integral_prod_left
  have hr : Integrable (fun v => 2*rationalKernel v) parameterMeasure :=
    hi.congr (ae_of_all _ mixtureKernel_integral)
  convert hr.const_mul (1/2 : ℝ) using 1
  funext v
  change rationalKernel v=(1/2 : ℝ)*(2*rationalKernel v)
  ring

theorem response_rationalKernel : physicalResponse (pressureL2 pressure_domain)=
    (1/4 : ℝ)*(∫ v, rationalKernel v ∂parameterMeasure) := by
  rw [swirl_response]
  simp_rw [radialEnergy_mixture]
  rw [integral_const_mul,← integral_integral_swap mixtureKernel_integrable]
  simp_rw [mixtureKernel_integral]
  rw [integral_const_mul]
  ring

theorem rationalKernel_interval : (∫ v, rationalKernel v ∂parameterMeasure)=
    ∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, 1/(2+(t+u))^2 := by
  rw [integral_prod _ rationalKernel_integrable]
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  apply integral_congr_ae
  filter_upwards [unit_nonneg] with t ht
  apply integral_congr_ae
  filter_upwards [unit_nonneg] with u hu
  simp only [rationalKernel,abs_of_nonneg ht,abs_of_nonneg hu]

private theorem unitInterval_nonneg {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) : 0 ≤ t := by
  rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
  exact ht.1

theorem inner_inverse_square (t : ℝ) (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..1, 1/(2+(t+u))^2)=1/(2+t)-1/(3+t) := by
  have hd (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v => -(2+(t+v))⁻¹) (1/(2+(t+u))^2) u := by
    have hp : 0 < 2+(t+u) := by linarith [unitInterval_nonneg hu]
    have hh : HasDerivAt (fun v : ℝ => 2+(t+v)) 1 u := by
      simpa using ((hasDerivAt_id u).const_add t).const_add 2
    have hi := (hh.inv (ne_of_gt hp)).neg
    have hf : -(fun v : ℝ => 2+(t+v))⁻¹=(fun v => -(2+(t+v))⁻¹) := by
      funext v
      simp only [Pi.neg_apply,Pi.inv_apply]
    rw [hf] at hi
    simpa only [neg_div,neg_neg] using hi
  have hc : ContinuousOn (fun u : ℝ => 1/(2+(t+u))^2) (uIcc (0 : ℝ) 1) := by
    refine continuousOn_const.div (by fun_prop) ?_
    intro u hu
    exact pow_ne_zero _ (ne_of_gt (show 0 < 2+(t+u) by linarith [unitInterval_nonneg hu]))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [show 2+(t+1)=3+t by ring,add_zero] at he
  calc
    _ = -(3+t)⁻¹ - -(2+t)⁻¹ := he
    _ = _ := by simp only [one_div]; ring

theorem parameter_interval_value :
    (∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, 1/(2+(t+u))^2)=Real.log (9/8 : ℝ) := by
  have hi : (∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, 1/(2+(t+u))^2)=
      ∫ t in (0 : ℝ)..1, (1/(2+t)-1/(3+t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact inner_inverse_square t (unitInterval_nonneg ht)
  rw [hi]
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun u : ℝ => Real.log (2+u)-Real.log (3+u)) (1/(2+t)-1/(3+t)) t := by
    have h2 : 2+t ≠ 0 := ne_of_gt (by linarith [unitInterval_nonneg ht])
    have h3 : 3+t ≠ 0 := ne_of_gt (by linarith [unitInterval_nonneg ht])
    have hh := (((hasDerivAt_id t).const_add 2).log h2).sub
      (((hasDerivAt_id t).const_add 3).log h3)
    have hf : ((fun u : ℝ => Real.log (2+u))-(fun u => Real.log (3+u)))=
        (fun u => Real.log (2+u)-Real.log (3+u)) := by
      funext u
      simp only [Pi.sub_apply]
    simp only [id_eq] at hh
    rw [hf] at hh
    simpa only [one_div] using hh
  have hc2 : ContinuousOn (fun t : ℝ => 1/(2+t)) (uIcc (0 : ℝ) 1) := by
    refine continuousOn_const.div (by fun_prop) ?_
    intro t ht
    exact ne_of_gt (by linarith [unitInterval_nonneg ht])
  have hc3 : ContinuousOn (fun t : ℝ => 1/(3+t)) (uIcc (0 : ℝ) 1) := by
    refine continuousOn_const.div (by fun_prop) ?_
    intro t ht
    exact ne_of_gt (by linarith [unitInterval_nonneg ht])
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc2.sub hc3).intervalIntegrable
  norm_num only [show (2 : ℝ)+1=3 by norm_num,show (3 : ℝ)+1=4 by norm_num,add_zero] at he
  have h9 : Real.log (9 : ℝ)=2*Real.log 3 := by
    rw [show (9 : ℝ)=(3 : ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  have h8 : Real.log (8 : ℝ)=Real.log 4+Real.log 2 := by
    rw [show (8 : ℝ)=(4 : ℝ)*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  rw [Real.log_div (by norm_num) (by norm_num),h9,h8]
  linarith [he]

theorem swirl_response_exact : physicalResponse (pressureL2 pressure_domain)=Real.log (9/8 : ℝ)/4 := by
  rw [response_rationalKernel,rationalKernel_interval,parameter_interval_value]
  ring

theorem swirl_leadingPressure_exact (ε : ℝ) : leadingPressure ε (pressureL2 pressure_domain)=
    Real.pi^2*ε^2*Real.log (9/8 : ℝ) := by
  rw [leadingPressure_formula,swirl_response_exact]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianSwirlLaplace
