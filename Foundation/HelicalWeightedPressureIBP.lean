import Foundation.HelicalPolynomialPressureIBP
import Foundation.GaussianSteinBounded

/-! Physical Gaussian IBP from genuine derivatives and weighted integrability. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.HelicalWeightedPressureIBP
set_option backward.isDefEq.respectTransparency false
open HelicalRadialGaussianBridge HelicalPressureProjection

abbrev ν : Measure ℝ := gaussianReal 0 (1/4)

theorem quarter_density_derivative (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 (1/4)) (-4*x*gaussianPDFReal 0 (1/4) x) x := by
  have he : gaussianPDFReal 0 (1/4)=fun t => (Real.sqrt (Real.pi/2))⁻¹*Real.exp (-2*t^2) :=
    funext quarter_pdf
  rw [he]
  have hg : HasDerivAt (fun t : ℝ => -2*t^2) (-4*x) x := by
    convert (hasDerivAt_pow 2 x).const_mul (-2 : ℝ) using 1 <;> ring
  convert hg.exp.const_mul (Real.sqrt (Real.pi/2))⁻¹ using 1 <;> ring

theorem integrable_density_mul {f : ℝ → ℝ} (hf : Integrable f ν) :
    Integrable (fun x => gaussianPDFReal 0 (1/4) x*f x) := by
  rw [ν, gaussianReal_of_var_ne_zero 0 (by norm_num)] at hf
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using hf

/-- Boundary decay is a consequence of integrability, with no assumed endpoint values. -/
theorem density_boundary_zero {f g : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (g x) x)
    (hf : Integrable f ν) (hg : Integrable g ν)
    (hxf : Integrable (fun x => x*f x) ν) :
    Tendsto (fun x => f x*gaussianPDFReal 0 (1/4) x) atBot (𝓝 0) ∧
    Tendsto (fun x => f x*gaussianPDFReal 0 (1/4) x) atTop (𝓝 0) := by
  have hi : Integrable (fun x => f x*gaussianPDFReal 0 (1/4) x) := by
    simpa only [mul_comm] using integrable_density_mul hf
  have hgi : Integrable (fun x => g x*gaussianPDFReal 0 (1/4) x) := by
    simpa only [mul_comm] using integrable_density_mul hg
  have hni : Integrable (fun x => f x*(-4*x*gaussianPDFReal 0 (1/4) x)) := by
    convert (integrable_density_mul hxf).const_mul (-4 : ℝ) using 1
    funext x
    try dsimp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hprod (x : ℝ) := (hd x).mul (quarter_density_derivative x)
  exact ⟨tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
      (fun x _ => hprod x) (hgi.add hni).integrableOn hi.integrableOn,
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (fun x _ => hprod x) (hgi.add hni).integrableOn hi.integrableOn⟩

theorem stein_integrable {f g : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (g x) x)
    (hf : Integrable f ν) (hg : Integrable g ν)
    (hxf : Integrable (fun x => x*f x) ν) :
    (∫ x, g x ∂ν)=4*(∫ x, x*f x ∂ν) := by
  have hgi : Integrable (fun x => g x*gaussianPDFReal 0 (1/4) x) := by
    simpa only [mul_comm] using integrable_density_mul hg
  have hni : Integrable (fun x => f x*(-4*x*gaussianPDFReal 0 (1/4) x)) := by
    convert (integrable_density_mul hxf).const_mul (-4 : ℝ) using 1
    funext x
    try dsimp only [Pi.sub_apply, Pi.mul_apply]
    ring
  obtain ⟨hbot,htop⟩ := density_boundary_zero hd hf hg hxf
  have hb := integral_mul_deriv_eq_deriv_mul (fun x _ => hd x)
    (fun x _ => quarter_density_derivative x) hni hgi hbot htop
  have he : (fun x => f x*(-4*x*gaussianPDFReal 0 (1/4) x))=
      fun x => -4*(gaussianPDFReal 0 (1/4) x*(x*f x)) := by funext x; ring
  rw [he, integral_const_mul] at hb
  have hs : (∫ x, g x ∂ν)=(∫ x, gaussianPDFReal 0 (1/4) x*g x) := by
    exact integral_gaussianReal_eq_integral_smul (by norm_num)
  have hx : (∫ x, x*f x ∂ν)=(∫ x, gaussianPDFReal 0 (1/4) x*(x*f x)) := by
    exact integral_gaussianReal_eq_integral_smul (by norm_num)
  rw [hs,hx]
  have hcomm : (∫ x, g x*gaussianPDFReal 0 (1/4) x)=
      (∫ x, gaussianPDFReal 0 (1/4) x*g x) := by congr 1; funext x; ring
  rw [hcomm] at hb
  linarith

theorem centered_first {f g : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (g x) x)
    (hf : Integrable f ν) (hxf : Integrable (fun x => x*f x) ν)
    (hxxf : Integrable (fun x => x^2*f x) ν)
    (hxg : Integrable (fun x => x*g x) ν) :
    (∫ x, (x^2-1/4)*f x ∂ν)=(1/4 : ℝ)*(∫ x, x*g x ∂ν) := by
  have hp (x : ℝ) : HasDerivAt (fun t => t*f t) (f x+x*g x) x := by
    have hh := (hasDerivAt_id x).mul (hd x)
    change HasDerivAt (fun t => t*f t) (1*f x+x*g x) x at hh
    convert hh using 1 <;> ring
  have hx2 : Integrable (fun x => x*(x*f x)) ν := by
    convert hxxf using 1
    funext x
    try dsimp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hi := stein_integrable hp hxf (hf.add hxg) hx2
  rw [integral_add hf hxg] at hi
  have he : (fun x => (x^2-1/4)*f x)=fun x => x*(x*f x)-(1/4 : ℝ)*f x := by
    funext x
    try dsimp only [Pi.sub_apply, Pi.mul_apply]
    ring
  rw [he, integral_sub hx2 (hf.const_mul _), integral_const_mul]
  linarith

theorem centered_second {f g k : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hdd : ∀ x, HasDerivAt g (k x) x)
    (hf : Integrable f ν) (hg : Integrable g ν) (hk : Integrable k ν)
    (hxf : Integrable (fun x => x*f x) ν)
    (hxxf : Integrable (fun x => x^2*f x) ν)
    (hxg : Integrable (fun x => x*g x) ν) :
    (∫ x, (x^2-1/4)*f x ∂ν)=(1/16 : ℝ)*(∫ x, k x ∂ν) := by
  have h1 := centered_first hd hf hxf hxxf hxg
  have h2 := stein_integrable hdd hg hk hxg
  linarith

local instance : IsProbabilityMeasure physicalGaussian := by
  unfold physicalGaussian
  infer_instance

theorem polynomial_weight_integrable {P : ℝ × ℝ → ℝ} (hp : MemLp P 2 physicalGaussian)
    (q : HelicalPolynomialPressureIBP.PlanePolynomial) :
    Integrable (fun x => MvPolynomial.eval ![x.1,x.2] q*P x) physicalGaussian :=
  (HelicalPolynomialPressureIBP.polynomial_memLp q 2 (by simp)).integrable_mul hp

theorem x_weights_integrable {P : ℝ × ℝ → ℝ} (hp : MemLp P 2 physicalGaussian) :
    Integrable (fun x => x.1*P x) physicalGaussian ∧
    Integrable (fun x => x.1^2*P x) physicalGaussian := by
  constructor
  · simpa using polynomial_weight_integrable hp (MvPolynomial.X 0)
  · simpa only [MvPolynomial.eval_pow, MvPolynomial.eval_X, Matrix.cons_val_zero] using polynomial_weight_integrable hp ((MvPolynomial.X (0 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^ (2 : ℕ))

theorem y_weights_integrable {P : ℝ × ℝ → ℝ} (hp : MemLp P 2 physicalGaussian) :
    Integrable (fun x => x.2*P x) physicalGaussian ∧
    Integrable (fun x => x.2^2*P x) physicalGaussian := by
  constructor
  · simpa using polynomial_weight_integrable hp (MvPolynomial.X 1)
  · simpa only [MvPolynomial.eval_pow, MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.cons_val_zero] using polynomial_weight_integrable hp ((MvPolynomial.X (1 : Fin 2) : HelicalPolynomialPressureIBP.PlanePolynomial)^ (2 : ℕ))

theorem centered_x {P G K : ℝ × ℝ → ℝ}
    (hd : ∀ x y, HasDerivAt (fun t => P (t,y)) (G (x,y)) x)
    (hdd : ∀ x y, HasDerivAt (fun t => G (t,y)) (K (x,y)) x)
    (hp : MemLp P 2 physicalGaussian) (hg : MemLp G 2 physicalGaussian)
    (hk : Integrable K physicalGaussian) :
    (∫ x, (x.1^2-1/4)*P x ∂physicalGaussian)=(1/16 : ℝ)*(∫ x, K x ∂physicalGaussian) := by
  have hi := hp.integrable (by norm_num)
  have hgi := hg.integrable (by norm_num)
  obtain ⟨hx,hxx⟩ := x_weights_integrable hp
  have hxg := (x_weights_integrable hg).1
  have hc : Integrable (fun x => (x.1^2-1/4)*P x) physicalGaussian := by
    convert hxx.sub (hi.const_mul (1/4 : ℝ)) using 1
    funext x
    try dsimp only [Pi.sub_apply, Pi.mul_apply]
    ring
  change Integrable P (ν.prod ν) at hi
  change Integrable G (ν.prod ν) at hgi
  change Integrable K (ν.prod ν) at hk
  change Integrable (fun x => x.1*P x) (ν.prod ν) at hx
  change Integrable (fun x => x.1^2*P x) (ν.prod ν) at hxx
  change Integrable (fun x => x.1*G x) (ν.prod ν) at hxg
  change Integrable (fun x => (x.1^2-1/4)*P x) (ν.prod ν) at hc
  change (∫ x, (x.1^2-1/4)*P x ∂ν.prod ν)=(1/16 : ℝ)*(∫ x, K x ∂ν.prod ν)
  rw [integral_prod_symm _ hc, integral_prod_symm _ hk, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae,hgi.prod_left_ae,hk.prod_left_ae,
    hx.prod_left_ae,hxx.prod_left_ae,hxg.prod_left_ae] with y h0 h1 h2 h3 h4 h5
  exact centered_second (fun x => hd x y) (fun x => hdd x y) h0 h1 h2 h3 h4 h5

theorem centered_y {P G K : ℝ × ℝ → ℝ}
    (hd : ∀ x y, HasDerivAt (fun t => P (x,t)) (G (x,y)) y)
    (hdd : ∀ x y, HasDerivAt (fun t => G (x,t)) (K (x,y)) y)
    (hp : MemLp P 2 physicalGaussian) (hg : MemLp G 2 physicalGaussian)
    (hk : Integrable K physicalGaussian) :
    (∫ x, (x.2^2-1/4)*P x ∂physicalGaussian)=(1/16 : ℝ)*(∫ x, K x ∂physicalGaussian) := by
  have hi := hp.integrable (by norm_num)
  have hgi := hg.integrable (by norm_num)
  obtain ⟨hy,hyy⟩ := y_weights_integrable hp
  have hyg := (y_weights_integrable hg).1
  have hc : Integrable (fun x => (x.2^2-1/4)*P x) physicalGaussian := by
    convert hyy.sub (hi.const_mul (1/4 : ℝ)) using 1
    funext x
    try dsimp only [Pi.sub_apply, Pi.mul_apply]
    ring
  change Integrable P (ν.prod ν) at hi
  change Integrable G (ν.prod ν) at hgi
  change Integrable K (ν.prod ν) at hk
  change Integrable (fun x => x.2*P x) (ν.prod ν) at hy
  change Integrable (fun x => x.2^2*P x) (ν.prod ν) at hyy
  change Integrable (fun x => x.2*G x) (ν.prod ν) at hyg
  change Integrable (fun x => (x.2^2-1/4)*P x) (ν.prod ν) at hc
  change (∫ x, (x.2^2-1/4)*P x ∂ν.prod ν)=(1/16 : ℝ)*(∫ x, K x ∂ν.prod ν)
  rw [integral_prod _ hc, integral_prod _ hk, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae,hgi.prod_right_ae,hk.prod_right_ae,
    hy.prod_right_ae,hyy.prod_right_ae,hyg.prod_right_ae] with x h0 h1 h2 h3 h4 h5
  exact centered_second (fun y => hd x y) (fun y => hdd x y) h0 h1 h2 h3 h4 h5

/-- Actual slice derivatives, Gaussian L2 for P and first derivatives, and L1 for pure seconds. -/
structure PressureDomain (P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ) : Prop where
  dx : ∀ x y, HasDerivAt (fun t => P (t,y)) (Dx (x,y)) x
  dy : ∀ x y, HasDerivAt (fun t => P (x,t)) (Dy (x,y)) y
  dxx : ∀ x y, HasDerivAt (fun t => Dx (t,y)) (Dxx (x,y)) x
  dyy : ∀ x y, HasDerivAt (fun t => Dy (x,t)) (Dyy (x,y)) y
  pressure_memLp : MemLp P 2 physicalGaussian
  dx_memLp : MemLp Dx 2 physicalGaussian
  dy_memLp : MemLp Dy 2 physicalGaussian
  dxx_integrable : Integrable Dxx physicalGaussian
  dyy_integrable : Integrable Dyy physicalGaussian

theorem radial_laplacian_integral {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ}
    (h : PressureDomain P Dx Dy Dxx Dyy) :
    (∫ x, radial x.1 x.2*P x ∂physicalGaussian)=
      (1/8 : ℝ)*(∫ x, Dxx x+Dyy x ∂physicalGaussian) := by
  have hx := centered_x h.dx h.dxx h.pressure_memLp h.dx_memLp h.dxx_integrable
  have hy := centered_y h.dy h.dyy h.pressure_memLp h.dy_memLp h.dyy_integrable
  have hi := h.pressure_memLp.integrable (by norm_num)
  have hxi : Integrable (fun x => (x.1^2-1/4)*P x) physicalGaussian := by
    convert (x_weights_integrable h.pressure_memLp).2.sub (hi.const_mul (1/4 : ℝ)) using 1
    funext x
    try dsimp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hyi : Integrable (fun x => (x.2^2-1/4)*P x) physicalGaussian := by
    convert (y_weights_integrable h.pressure_memLp).2.sub (hi.const_mul (1/4 : ℝ)) using 1
    funext x
    try dsimp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have he : (fun x => radial x.1 x.2*P x)=
      fun x => 2*((x.1^2-1/4)*P x)+2*((x.2^2-1/4)*P x) := by
    funext x
    unfold radial
    ring
  rw [he, integral_add (hxi.const_mul _) (hyi.const_mul _), integral_const_mul,
    integral_const_mul, integral_add h.dxx_integrable h.dyy_integrable, hx,hy]
  ring

def pressureL2 {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ} (h : PressureDomain P Dx Dy Dxx Dyy) : PhysicalL2 :=
  h.pressure_memLp.toLp P

theorem pressureL2_ae {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ} (h : PressureDomain P Dx Dy Dxx Dyy) :
    pressureL2 h =ᵐ[physicalGaussian] P := MemLp.coeFn_toLp _

theorem pressure_response {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ} (h : PressureDomain P Dx Dy Dxx Dyy) :
    physicalResponse (pressureL2 h)=(1/8 : ℝ)*(∫ x, Dxx x+Dyy x ∂physicalGaussian) := by
  rw [physicalResponse_integral]
  have he : (∫ x, radial x.1 x.2*pressureL2 h x ∂physicalGaussian)=
      (∫ x, radial x.1 x.2*P x ∂physicalGaussian) := by
    apply integral_congr_ae
    filter_upwards [pressureL2_ae h] with x hx
    rw [hx]
  rw [he]
  exact radial_laplacian_integral h

theorem leading_pressure_laplacian (ε : ℝ) {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ}
    (h : PressureDomain P Dx Dy Dxx Dyy) :
    leadingPressure ε (pressureL2 h)=(Real.pi^2*ε^2/2)*
      (∫ x, Dxx x+Dyy x ∂physicalGaussian) := by
  rw [leadingPressure_formula, pressure_response]
  ring

def actualLaplacian (P : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  deriv (fun t => deriv (fun s => P (s,x.2)) t) x.1+
    deriv (fun t => deriv (fun s => P (x.1,s)) t) x.2

theorem actualLaplacian_eq {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ}
    (h : PressureDomain P Dx Dy Dxx Dyy) (x : ℝ × ℝ) :
    actualLaplacian P x=Dxx x+Dyy x := by
  have hx (a b : ℝ) : deriv (fun t => P (t,b)) a=Dx (a,b) := (h.dx a b).deriv
  have hy (a b : ℝ) : deriv (fun t => P (a,t)) b=Dy (a,b) := (h.dy a b).deriv
  unfold actualLaplacian
  simp_rw [hx,hy]
  rw [(h.dxx x.1 x.2).deriv,(h.dyy x.1 x.2).deriv]

theorem actualLaplacian_integrable {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ}
    (h : PressureDomain P Dx Dy Dxx Dyy) : Integrable (actualLaplacian P) physicalGaussian := by
  have he : actualLaplacian P=Dxx+Dyy := funext (fun x => actualLaplacian_eq h x)
  rw [he]
  exact h.dxx_integrable.add h.dyy_integrable

theorem response_actual_laplacian {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ}
    (h : PressureDomain P Dx Dy Dxx Dyy) :
    physicalResponse (pressureL2 h)=(1/8 : ℝ)*(∫ x, actualLaplacian P x ∂physicalGaussian) := by
  simp_rw [actualLaplacian_eq h]
  exact pressure_response h

theorem harmonic_response_zero {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ}
    (h : PressureDomain P Dx Dy Dxx Dyy) (hh : ∀ x, actualLaplacian P x=0) :
    physicalResponse (pressureL2 h)=0 := by
  rw [response_actual_laplacian h]
  simp only [hh, integral_zero, mul_zero]

theorem response_negative_iff {P Dx Dy Dxx Dyy : ℝ × ℝ → ℝ}
    (h : PressureDomain P Dx Dy Dxx Dyy) :
    physicalResponse (pressureL2 h)<0 ↔ (∫ x, actualLaplacian P x ∂physicalGaussian)<0 := by
  rw [response_actual_laplacian h]
  constructor <;> intro hi <;> linarith

theorem cosine_domain : PressureDomain (fun x => Real.cos x.1)
    (fun x => -Real.sin x.1) (fun _ => 0) (fun x => -Real.cos x.1) (fun _ => 0) := by
  have hc : MemLp (fun x : ℝ × ℝ => Real.cos x.1) 2 physicalGaussian :=
    MemLp.of_bound (by fun_prop) 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x.1))
  have hs : MemLp (fun x : ℝ × ℝ => Real.sin x.1) 2 physicalGaussian :=
    MemLp.of_bound (by fun_prop) 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x.1))
  refine ⟨?_,?_,?_,?_,hc,hs.neg,memLp_const 0,hc.neg.integrable (by norm_num),integrable_const 0⟩
  · intro x y
    exact Real.hasDerivAt_cos x
  · intro x y
    exact hasDerivAt_const y (Real.cos x)
  · intro x y
    exact (Real.hasDerivAt_sin x).neg
  · intro x y
    exact hasDerivAt_const y 0

theorem cosine_laplacian (x : ℝ × ℝ) :
    actualLaplacian (fun x => Real.cos x.1) x= -Real.cos x.1 := by
  simpa only [add_zero] using actualLaplacian_eq cosine_domain x

theorem cosine_response : physicalResponse (pressureL2 cosine_domain)=
    -(1/8 : ℝ)*(∫ x : ℝ × ℝ, Real.cos x.1 ∂physicalGaussian) := by
  rw [response_actual_laplacian]
  simp_rw [cosine_laplacian]
  rw [integral_neg]
  ring

end OperatorDerivativeRewrite.Foundation.HelicalWeightedPressureIBP
