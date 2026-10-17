import Foundation.GaussianSwirlVelocity

/-! Gaussian domain and radial observation of the pressure constructed from a swirl. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianSwirlPressureDomain
set_option backward.isDefEq.respectTransparency false
open GaussianSwirlVelocity HelicalRadialGaussianBridge HelicalPressureProjection
open HelicalWeightedPressureIBP

local instance : IsProbabilityMeasure physicalGaussian := by unfold physicalGaussian; infer_instance

theorem angular_bounds {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-s)/2 ≤ angularProfile s ∧ angularProfile s ≤ 1/2 := by
  have hc : IntervalIntegrable (fun t : ℝ => Real.exp (-t*s)) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t*s))).intervalIntegrable 0 1
  have hl := intervalIntegral.integral_mono_on (μ := volume) (show (0 : ℝ) ≤ 1 by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.exp (-s)) volume 0 1) hc
    (fun t ht => Real.exp_le_exp.mpr (by nlinarith [ht.2]))
  have hu := intervalIntegral.integral_mono_on (μ := volume) (show (0 : ℝ) ≤ 1 by norm_num)
    hc (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1)
    (fun t ht => Real.exp_le_one_iff.mpr (by nlinarith [ht.1]))
  norm_num at hl hu
  unfold angularProfile
  simp only [neg_mul]
  constructor <;> linarith

theorem angular_pos {s : ℝ} (hs : 0 ≤ s) : 0 < angularProfile s :=
  lt_of_lt_of_le (by positivity) (angular_bounds hs).1

theorem angularDerivative_bounds {s : ℝ} (hs : 0 ≤ s) :
    -(1/4 : ℝ) ≤ angularDerivative s ∧ angularDerivative s ≤ 0 := by
  have hc : IntervalIntegrable (fun t : ℝ => -t*Real.exp (-t*s)) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => -t*Real.exp (-t*s))).intervalIntegrable 0 1
  have hl := intervalIntegral.integral_mono_on (μ := volume) (show (0 : ℝ) ≤ 1 by norm_num)
    ((by fun_prop : Continuous (fun t : ℝ => -t)).intervalIntegrable 0 1) hc
    (fun t ht => by
      have he := Real.exp_le_one_iff.mpr (show -t*s ≤ 0 by nlinarith [ht.1])
      nlinarith [ht.1])
  have hu := intervalIntegral.integral_mono_on (μ := volume) (show (0 : ℝ) ≤ 1 by norm_num)
    hc (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1)
    (fun t ht => by nlinarith [ht.1,Real.exp_pos (-t*s)])
  rw [intervalIntegral.integral_neg,integral_id] at hl
  norm_num at hl hu
  unfold angularDerivative
  simp only [neg_mul,intervalIntegral.integral_neg]
  constructor <;> linarith

theorem angularDerivative_abs {s : ℝ} (hs : 0 ≤ s) : |angularDerivative s| ≤ 1/4 := by
  rw [abs_le]
  have hb := angularDerivative_bounds hs
  constructor <;> linarith

theorem radialPressure_bounds {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ radialPressure s ∧ radialPressure s ≤ s/8 := by
  have hc : Continuous (fun t : ℝ => angularProfile t^2/2) :=
    angularProfile_continuous.pow 2 |>.div_const 2
  have hl := intervalIntegral.integral_nonneg_of_forall (μ := volume) hs
    (fun t : ℝ => show 0 ≤ angularProfile t^2/2 by positivity)
  have hu := intervalIntegral.integral_mono_on (μ := volume) hs (hc.intervalIntegrable 0 s)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/8 : ℝ)) volume 0 s)
    (fun t ht => by
      have hb := angular_bounds ht.1
      have hp := angular_pos ht.1
      nlinarith [sq_nonneg (angularProfile t-1/2)])
  norm_num at hu
  constructor
  · exact hl
  · simpa only [radialPressure,intervalIntegral.integral_div] using hu

theorem angularDerivative_measurable : Measurable angularDerivative := by
  have he : angularDerivative=deriv angularProfile :=
    funext (fun s => (angularProfile_hasDerivAt s).deriv.symm)
  rw [he]
  exact measurable_deriv _

def radiusSq (x : ℝ × ℝ) : ℝ := x.1^2+x.2^2
def P (x : ℝ × ℝ) : ℝ := pressure x.1 x.2
def Dx (x : ℝ × ℝ) : ℝ := x.1*angularProfile (radiusSq x)^2
def Dy (x : ℝ × ℝ) : ℝ := x.2*angularProfile (radiusSq x)^2
def Dxx (x : ℝ × ℝ) : ℝ := angularProfile (radiusSq x)^2+
  4*x.1^2*angularProfile (radiusSq x)*angularDerivative (radiusSq x)
def Dyy (x : ℝ × ℝ) : ℝ := angularProfile (radiusSq x)^2+
  4*x.2^2*angularProfile (radiusSq x)*angularDerivative (radiusSq x)

theorem radiusSq_nonneg (x : ℝ × ℝ) : 0 ≤ radiusSq x := by unfold radiusSq; positivity

theorem P_continuous : Continuous P := by
  have hr : Continuous radialPressure := continuous_iff_continuousAt.mpr
    (fun s => (radialPressure_hasDerivAt s).continuousAt)
  exact hr.comp (by fun_prop)

theorem Dx_continuous : Continuous Dx := by
  unfold Dx
  exact continuous_fst.mul ((angularProfile_continuous.comp (by unfold radiusSq; fun_prop)).pow 2)

theorem Dy_continuous : Continuous Dy := by
  unfold Dy
  exact continuous_snd.mul ((angularProfile_continuous.comp (by unfold radiusSq; fun_prop)).pow 2)

theorem Dxx_measurable : Measurable Dxx := by
  have hh := angularProfile_continuous.measurable.comp (show Measurable radiusSq by unfold radiusSq; fun_prop)
  have hd := angularDerivative_measurable.comp (show Measurable radiusSq by unfold radiusSq; fun_prop)
  exact (hh.pow_const 2).add (((measurable_const.mul (measurable_fst.pow_const 2)).mul hh).mul hd)

theorem Dyy_measurable : Measurable Dyy := by
  have hh := angularProfile_continuous.measurable.comp (show Measurable radiusSq by unfold radiusSq; fun_prop)
  have hd := angularDerivative_measurable.comp (show Measurable radiusSq by unfold radiusSq; fun_prop)
  exact (hh.pow_const 2).add (((measurable_const.mul (measurable_snd.pow_const 2)).mul hh).mul hd)

theorem P_norm_bound (x : ℝ × ℝ) : ‖P x‖ ≤ radiusSq x := by
  have hb := radialPressure_bounds (radiusSq_nonneg x)
  change |radialPressure (radiusSq x)| ≤ radiusSq x
  rw [abs_of_nonneg hb.1]
  linarith [radiusSq_nonneg x]

theorem Dx_norm_bound (x : ℝ × ℝ) : ‖Dx x‖ ≤ ‖x.1‖ := by
  have hb := angular_bounds (radiusSq_nonneg x)
  have hp := angular_pos (radiusSq_nonneg x)
  rw [Dx,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg (angularProfile (radiusSq x)))]
  have hh : angularProfile (radiusSq x)^2 ≤ 1/4 := by nlinarith
  nlinarith [abs_nonneg x.1,mul_nonneg (abs_nonneg x.1) (sub_nonneg.mpr hh)]

theorem Dy_norm_bound (x : ℝ × ℝ) : ‖Dy x‖ ≤ ‖x.2‖ := by
  have hb := angular_bounds (radiusSq_nonneg x)
  have hp := angular_pos (radiusSq_nonneg x)
  rw [Dy,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg (angularProfile (radiusSq x)))]
  have hh : angularProfile (radiusSq x)^2 ≤ 1/4 := by nlinarith
  nlinarith [abs_nonneg x.2,mul_nonneg (abs_nonneg x.2) (sub_nonneg.mpr hh)]

theorem Dxx_norm_bound (x : ℝ × ℝ) : ‖Dxx x‖ ≤ 1+x.1^2 := by
  have hb := angular_bounds (radiusSq_nonneg x)
  have hp := angular_pos (radiusSq_nonneg x)
  have hd := angularDerivative_abs (radiusSq_nonneg x)
  calc
    ‖Dxx x‖ ≤ angularProfile (radiusSq x)^2+
        4*x.1^2*angularProfile (radiusSq x)*|angularDerivative (radiusSq x)| := by
      unfold Dxx
      rw [Real.norm_eq_abs]
      calc
        _ ≤ |angularProfile (radiusSq x)^2|+
            |4*x.1^2*angularProfile (radiusSq x)*angularDerivative (radiusSq x)| := abs_add_le _ _
        _ = _ := by
          rw [abs_of_nonneg (sq_nonneg (angularProfile (radiusSq x))),abs_mul,
            abs_of_nonneg (show 0 ≤ 4*x.1^2*angularProfile (radiusSq x) by positivity)]
    _ ≤ 1+x.1^2 := by
      have hh : angularProfile (radiusSq x)^2 ≤ 1/4 := by nlinarith
      have hm : angularProfile (radiusSq x)*|angularDerivative (radiusSq x)| ≤ 1/8 := by
        nlinarith [abs_nonneg (angularDerivative (radiusSq x))]
      nlinarith [sq_nonneg x.1,mul_nonneg (sq_nonneg x.1) (sub_nonneg.mpr hm)]

theorem Dyy_norm_bound (x : ℝ × ℝ) : ‖Dyy x‖ ≤ 1+x.2^2 := by
  have hb := angular_bounds (radiusSq_nonneg x)
  have hp := angular_pos (radiusSq_nonneg x)
  have hd := angularDerivative_abs (radiusSq_nonneg x)
  calc
    ‖Dyy x‖ ≤ angularProfile (radiusSq x)^2+
        4*x.2^2*angularProfile (radiusSq x)*|angularDerivative (radiusSq x)| := by
      unfold Dyy
      rw [Real.norm_eq_abs]
      calc
        _ ≤ |angularProfile (radiusSq x)^2|+
            |4*x.2^2*angularProfile (radiusSq x)*angularDerivative (radiusSq x)| := abs_add_le _ _
        _ = _ := by
          rw [abs_of_nonneg (sq_nonneg (angularProfile (radiusSq x))),abs_mul,
            abs_of_nonneg (show 0 ≤ 4*x.2^2*angularProfile (radiusSq x) by positivity)]
    _ ≤ 1+x.2^2 := by
      have hh : angularProfile (radiusSq x)^2 ≤ 1/4 := by nlinarith
      have hm : angularProfile (radiusSq x)*|angularDerivative (radiusSq x)| ≤ 1/8 := by
        nlinarith [abs_nonneg (angularDerivative (radiusSq x))]
      nlinarith [sq_nonneg x.2,mul_nonneg (sq_nonneg x.2) (sub_nonneg.mpr hm)]

theorem P_memLp : MemLp P 2 physicalGaussian := by
  have hr : MemLp radiusSq 2 physicalGaussian := by
    change MemLp (fun x : ℝ × ℝ => x.1^2+x.2^2) 2 physicalGaussian
    simpa only [radiusSq,MvPolynomial.eval_add,MvPolynomial.eval_pow,MvPolynomial.eval_X,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.head_cons] using HelicalPolynomialPressureIBP.polynomial_memLp
        (((MvPolynomial.X (0 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^(2 : ℕ))+((MvPolynomial.X (1 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^(2 : ℕ))) 2 (by simp)
  exact hr.mono' P_continuous.aestronglyMeasurable (ae_of_all _ P_norm_bound)

theorem Dx_memLp : MemLp Dx 2 physicalGaussian := by
  have hx : MemLp (fun x : ℝ × ℝ => x.1) 2 physicalGaussian := by
    simpa using HelicalPolynomialPressureIBP.polynomial_memLp (MvPolynomial.X (0 : Fin 2)) 2 (by simp)
  exact hx.norm.mono' Dx_continuous.aestronglyMeasurable (ae_of_all _ Dx_norm_bound)

theorem Dy_memLp : MemLp Dy 2 physicalGaussian := by
  have hy : MemLp (fun x : ℝ × ℝ => x.2) 2 physicalGaussian := by
    simpa using HelicalPolynomialPressureIBP.polynomial_memLp (MvPolynomial.X (1 : Fin 2)) 2 (by simp)
  exact hy.norm.mono' Dy_continuous.aestronglyMeasurable (ae_of_all _ Dy_norm_bound)

theorem Dxx_integrable : Integrable Dxx physicalGaussian := by
  have hi : MemLp (fun x : ℝ × ℝ => 1+x.1^2) 1 physicalGaussian := by
    simpa only [MvPolynomial.eval_add,map_one,MvPolynomial.eval_pow,MvPolynomial.eval_X,Matrix.cons_val_zero]
      using HelicalPolynomialPressureIBP.polynomial_memLp (1+((MvPolynomial.X (0 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^(2 : ℕ))) 1 (by simp)
  exact (hi.mono' Dxx_measurable.aestronglyMeasurable (ae_of_all _ Dxx_norm_bound)).integrable (by simp)

theorem Dyy_integrable : Integrable Dyy physicalGaussian := by
  have hi : MemLp (fun x : ℝ × ℝ => 1+x.2^2) 1 physicalGaussian := by
    simpa only [MvPolynomial.eval_add,map_one,MvPolynomial.eval_pow,MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one]
      using HelicalPolynomialPressureIBP.polynomial_memLp (1+((MvPolynomial.X (1 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^(2 : ℕ))) 1 (by simp)
  exact (hi.mono' Dyy_measurable.aestronglyMeasurable (ae_of_all _ Dyy_norm_bound)).integrable (by simp)

theorem pressure_domain : PressureDomain P Dx Dy Dxx Dyy :=
  ⟨pressure_x,pressure_y,pressure_xx,pressure_yy,P_memLp,Dx_memLp,Dy_memLp,Dxx_integrable,Dyy_integrable⟩

theorem stein_x {G K : ℝ × ℝ → ℝ}
    (hd : ∀ x y, HasDerivAt (fun t => G (t,y)) (K (x,y)) x)
    (hg : MemLp G 2 physicalGaussian) (hk : Integrable K physicalGaussian) :
    (∫ x, K x ∂physicalGaussian)=4*(∫ x, x.1*G x ∂physicalGaussian) := by
  have hi := hg.integrable (by norm_num)
  have hx := (x_weights_integrable hg).1
  change Integrable G (ν.prod ν) at hi
  change Integrable K (ν.prod ν) at hk
  change Integrable (fun x => x.1*G x) (ν.prod ν) at hx
  change (∫ x, K x ∂ν.prod ν)=4*(∫ x, x.1*G x ∂ν.prod ν)
  rw [integral_prod_symm _ hk,integral_prod_symm _ hx,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae,hk.prod_left_ae,hx.prod_left_ae] with y h0 h1 h2
  exact stein_integrable (fun x => hd x y) h0 h1 h2

theorem stein_y {G K : ℝ × ℝ → ℝ}
    (hd : ∀ x y, HasDerivAt (fun t => G (x,t)) (K (x,y)) y)
    (hg : MemLp G 2 physicalGaussian) (hk : Integrable K physicalGaussian) :
    (∫ x, K x ∂physicalGaussian)=4*(∫ x, x.2*G x ∂physicalGaussian) := by
  have hi := hg.integrable (by norm_num)
  have hy := (y_weights_integrable hg).1
  change Integrable G (ν.prod ν) at hi
  change Integrable K (ν.prod ν) at hk
  change Integrable (fun x => x.2*G x) (ν.prod ν) at hy
  change (∫ x, K x ∂ν.prod ν)=4*(∫ x, x.2*G x ∂ν.prod ν)
  rw [integral_prod _ hk,integral_prod _ hy,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae,hk.prod_right_ae,hy.prod_right_ae] with x h0 h1 h2
  exact stein_integrable (fun y => hd x y) h0 h1 h2

/-- The first/Euler pressure pairing on the nonpolynomial actual derivative domain. -/
theorem domain_euler {F Fx Fy Fxx Fyy : ℝ × ℝ → ℝ} (h : PressureDomain F Fx Fy Fxx Fyy) :
    physicalResponse (pressureL2 h)=(1/2 : ℝ)*
      (∫ x, x.1*Fx x+x.2*Fy x ∂physicalGaussian) := by
  have hx := stein_x h.dxx h.dx_memLp h.dxx_integrable
  have hy := stein_y h.dyy h.dy_memLp h.dyy_integrable
  have hxi := (x_weights_integrable h.dx_memLp).1
  have hyi := (y_weights_integrable h.dy_memLp).1
  rw [pressure_response,integral_add h.dxx_integrable h.dyy_integrable,hx,hy,
    integral_add hxi hyi]
  ring

def radialEnergy (x : ℝ × ℝ) : ℝ := radiusSq x*angularProfile (radiusSq x)^2

theorem radialEnergy_eq (x : ℝ × ℝ) : x.1*Dx x+x.2*Dy x=radialEnergy x := by
  unfold Dx Dy radialEnergy radiusSq
  ring

theorem radialEnergy_integrable : Integrable radialEnergy physicalGaussian := by
  have hi := (x_weights_integrable Dx_memLp).1.add (y_weights_integrable Dy_memLp).1
  exact hi.congr (ae_of_all _ radialEnergy_eq)

theorem radialEnergy_continuous : Continuous radialEnergy := by
  unfold radialEnergy
  exact (show Continuous radiusSq by unfold radiusSq; fun_prop).mul
    ((angularProfile_continuous.comp (by unfold radiusSq; fun_prop)).pow 2)

theorem radialEnergy_nonneg (x : ℝ × ℝ) : 0 ≤ radialEnergy x := by
  exact mul_nonneg (radiusSq_nonneg x) (sq_nonneg _)

theorem radialEnergy_at_one : 0 < radialEnergy (1,0) := by
  have hp := angular_pos (show (0 : ℝ) ≤ 1 by norm_num)
  simpa only [radialEnergy,radiusSq,one_pow,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    add_zero,one_mul] using sq_pos_of_pos hp

local instance : Measure.IsOpenPosMeasure ν :=
  (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num : (1/4 : NNReal) ≠ 0)).isOpenPosMeasure

local instance : Measure.IsOpenPosMeasure physicalGaussian := by
  change Measure.IsOpenPosMeasure (ν.prod ν)
  infer_instance

theorem radialEnergy_integral_pos : 0 < ∫ x, radialEnergy x ∂physicalGaussian :=
  integral_pos_of_integrable_nonneg_nonzero radialEnergy_continuous radialEnergy_integrable
    radialEnergy_nonneg (ne_of_gt radialEnergy_at_one)

theorem swirl_response : physicalResponse (pressureL2 pressure_domain)=
    (1/2 : ℝ)*(∫ x, radialEnergy x ∂physicalGaussian) := by
  rw [domain_euler]
  simp_rw [radialEnergy_eq]

theorem swirl_response_pos : 0 < physicalResponse (pressureL2 pressure_domain) := by
  rw [swirl_response]
  exact mul_pos (by norm_num) radialEnergy_integral_pos

theorem swirl_leadingPressure_pos (ε : ℝ) (hε : ε ≠ 0) :
    0 < leadingPressure ε (pressureL2 pressure_domain) := by
  rw [leadingPressure_formula]
  have hp := swirl_response_pos
  positivity

end OperatorDerivativeRewrite.Foundation.GaussianSwirlPressureDomain
