import Foundation.HelicalPressureProjection
import Foundation.GaussianPolynomialDifferentiation

/-! Physical quarter-variance Gaussian IBP on the genuine polynomial domain. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.HelicalPolynomialPressureIBP
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian FiniteGaussian HelicalRadialGaussianBridge HelicalPressureProjection

local instance : IsProbabilityMeasure physicalGaussian := by
  unfold physicalGaussian
  infer_instance

abbrev PlanePolynomial := MvPolynomial (Fin 2) ℝ

def scale : PlanePolynomial →ₐ[ℝ] PlanePolynomial :=
  aeval (fun i => (1/2 : ℝ) • X i)

theorem scale_eval (p : PlanePolynomial) (x : Fin 2 → ℝ) :
    eval x (scale p)=eval (fun i => x i/2) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [scale]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    simp [scale, smul_eval, div_eq_mul_inv, mul_comm]

theorem scale_pderiv (p : PlanePolynomial) (i : Fin 2) :
    pderiv i (scale p)=(1/2 : ℝ) • scale (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [scale]
  | add p q hp hq => simp [hp, hq, smul_add]
  | mul_X p j hp =>
    simp only [map_mul, pderiv_mul, hp, map_add]
    simp [scale, pderiv_X, Pi.single_apply, Algebra.smul_def]
    split_ifs <;> ring

def moment : PlanePolynomial →ₗ[ℝ] ℝ := productPolynomialIntegral.comp scale.toLinearMap

theorem moment_integral (p : PlanePolynomial) :
    moment p=∫ x : ℝ × ℝ, eval ![x.1,x.2] p ∂physicalGaussian := by
  have hs := GaussianOrthonormalPolynomialLaw.polynomial_integral_transport
    directions directions_orthonormal (scale p)
  have he (ω : SampleSpace) : isonormalCylinder directions (scale p) ω=
      eval ![firstChaosEmbedding (directions 0) ω/2,
        firstChaosEmbedding (directions 1) ω/2] p := by
    rw [isonormalCylinder, scale_eval]
    apply congrArg (fun v : Fin 2 → ℝ => eval v p)
    funext i
    fin_cases i <;> rfl
  change productPolynomialIntegral (scale p)=_
  rw [← hs]
  simp_rw [he]
  exact scaled_pair_law.integral_comp (show AEStronglyMeasurable (fun x : ℝ × ℝ => eval ![x.1,x.2] p) physicalGaussian from (p.continuous_eval.comp (by fun_prop)).aestronglyMeasurable)

theorem polynomial_memLp (p : PlanePolynomial) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun x : ℝ × ℝ => eval ![x.1,x.2] p) r physicalGaussian := by
  have hi := isonormalCylinder_memLp directions (scale p) r hr
  have he : (fun ω : SampleSpace => eval ![firstChaosEmbedding (directions 0) ω/2,
      firstChaosEmbedding (directions 1) ω/2] p)=isonormalCylinder directions (scale p) := by
    funext ω
    rw [isonormalCylinder, scale_eval]
    apply congrArg (fun v : Fin 2 → ℝ => eval v p)
    funext i
    fin_cases i <;> rfl
  rw [← scaled_pair_law.map_eq]
  apply (memLp_map_measure_iff ((p.continuous_eval.comp (by fun_prop)).aestronglyMeasurable) scaled_pair_law.aemeasurable).mpr
  simpa only [Function.comp_def, he] using hi

theorem stein (p : PlanePolynomial) (i : Fin 2) :
    moment (X i*p)=(1/4 : ℝ)*moment (pderiv i p) := by
  have h := GaussianDiagonalQuadraticMoments.stein (scale p) i
  rw [scale_pderiv, map_smul, smul_eq_mul] at h
  change productPolynomialIntegral (scale (X i*p))=_
  rw [map_mul]
  simp only [scale, aeval_X, smul_mul_assoc, map_smul, smul_eq_mul]
  change (1/2 : ℝ)*productPolynomialIntegral (X i*scale p)=_
  rw [h]
  change (1/2 : ℝ)*((1/2 : ℝ)*productPolynomialIntegral (scale (pderiv i p)))=(1/4 : ℝ)*productPolynomialIntegral (scale (pderiv i p))
  ring

theorem centered_stein (p : PlanePolynomial) (i : Fin 2) :
    moment ((X i^2-(1/4 : ℝ) • 1)*p)=(1/16 : ℝ)*moment (pderiv i (pderiv i p)) := by
  have h := stein (X i*p) i
  have hs := stein (pderiv i p) i
  have hd : pderiv i (X i*p)=p+X i*pderiv i p := by simp [add_comm]
  have hl : X i*(X i*p)=X i^2*p := by ring
  rw [hl, hd, map_add, hs] at h
  have he : (X i^2-(1/4 : ℝ) • 1)*p=X i^2*p-(1/4 : ℝ) • p := by
    simp [Algebra.smul_def]
    ring
  rw [he, map_sub, map_smul, smul_eq_mul]
  linarith

def radialPolynomial : PlanePolynomial := (2 : ℝ) • (X 0^2+X 1^2)-1

theorem radialPolynomial_eval (x y : ℝ) : eval ![x,y] radialPolynomial=radial x y := by
  simp [radialPolynomial, radial]
  ring

theorem radial_laplacian_pairing (p : PlanePolynomial) :
    moment (radialPolynomial*p)=(1/8 : ℝ)*
      moment (pderiv 0 (pderiv 0 p)+pderiv 1 (pderiv 1 p)) := by
  have h0 := centered_stein p 0
  have h1 := centered_stein p 1
  have he : radialPolynomial*p=(2 : ℝ) • ((X 0^2-(1/4 : ℝ) • 1)*p)+
      (2 : ℝ) • ((X 1^2-(1/4 : ℝ) • 1)*p) := by
    simp only [radialPolynomial, sub_mul, add_mul, smul_mul_assoc, one_mul]
    module
  rw [he, map_add, map_smul, map_smul, map_add]
  simp only [smul_eq_mul]
  linarith

def polynomialPressure (p : PlanePolynomial) : PhysicalL2 :=
  (polynomial_memLp p 2 (by simp)).toLp (fun x => eval ![x.1,x.2] p)

theorem polynomialPressure_ae (p : PlanePolynomial) :
    polynomialPressure p =ᵐ[physicalGaussian] fun x => eval ![x.1,x.2] p :=
  MemLp.coeFn_toLp _

theorem polynomial_response (p : PlanePolynomial) :
    physicalResponse (polynomialPressure p)=moment (radialPolynomial*p) := by
  rw [physicalResponse_integral, moment_integral]
  apply integral_congr_ae
  filter_upwards [polynomialPressure_ae p] with x hx
  rw [hx, map_mul, radialPolynomial_eval]

theorem polynomial_response_laplacian (p : PlanePolynomial) :
    physicalResponse (polynomialPressure p)=(1/8 : ℝ)*
      (∫ x : ℝ × ℝ, eval ![x.1,x.2]
        (pderiv 0 (pderiv 0 p)+pderiv 1 (pderiv 1 p)) ∂physicalGaussian) := by
  rw [polynomial_response, radial_laplacian_pairing, moment_integral]

theorem radial_euler_pairing (p : PlanePolynomial) :
    moment (radialPolynomial*p)=(1/2 : ℝ)*moment (X 0*pderiv 0 p+X 1*pderiv 1 p) := by
  rw [radial_laplacian_pairing, map_add, map_add, stein, stein]
  ring

theorem polynomial_response_euler (p : PlanePolynomial) :
    physicalResponse (polynomialPressure p)=(1/2 : ℝ)*
      (∫ x : ℝ × ℝ, x.1*eval ![x.1,x.2] (pderiv 0 p)+
        x.2*eval ![x.1,x.2] (pderiv 1 p) ∂physicalGaussian) := by
  rw [polynomial_response, radial_euler_pairing, moment_integral]
  simp only [map_add, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]

def pressureFunction (p : PlanePolynomial) (x y : ℝ) : ℝ := eval ![x,y] p

theorem pressure_dx (p : PlanePolynomial) (x y : ℝ) :
    deriv (fun t => pressureFunction p t y) x=pressureFunction (pderiv 0 p) x y :=
  (GaussianPolynomialDifferentiation.eval_hasDerivAt_time p x y).deriv

theorem pressure_dy (p : PlanePolynomial) (x y : ℝ) :
    deriv (fun t => pressureFunction p x t) y=pressureFunction (pderiv 1 p) x y :=
  (GaussianPolynomialDifferentiation.eval_hasDerivAt_space p x y).deriv

def physicalLaplacian (p : PlanePolynomial) (x y : ℝ) : ℝ :=
  deriv (fun t => deriv (fun s => pressureFunction p s y) t) x+
    deriv (fun t => deriv (fun s => pressureFunction p x s) t) y

theorem physicalLaplacian_eval (p : PlanePolynomial) (x y : ℝ) :
    physicalLaplacian p x y=eval ![x,y]
      (pderiv 0 (pderiv 0 p)+pderiv 1 (pderiv 1 p)) := by
  unfold physicalLaplacian
  simp_rw [pressure_dx, pressure_dy]
  simp only [pressureFunction, map_add]

theorem physicalLaplacian_integrable (p : PlanePolynomial) :
    Integrable (fun x : ℝ × ℝ => physicalLaplacian p x.1 x.2) physicalGaussian := by
  simp_rw [physicalLaplacian_eval]
  exact (polynomial_memLp _ 1 (by simp)).integrable (by simp)

theorem response_actual_laplacian (p : PlanePolynomial) :
    physicalResponse (polynomialPressure p)=(1/8 : ℝ)*
      (∫ x : ℝ × ℝ, physicalLaplacian p x.1 x.2 ∂physicalGaussian) := by
  simp_rw [physicalLaplacian_eval]
  exact polynomial_response_laplacian p

theorem response_actual_euler (p : PlanePolynomial) :
    physicalResponse (polynomialPressure p)=(1/2 : ℝ)*
      (∫ x : ℝ × ℝ, x.1*deriv (fun t => pressureFunction p t x.2) x.1+
        x.2*deriv (fun t => pressureFunction p x.1 t) x.2 ∂physicalGaussian) := by
  simp_rw [pressure_dx, pressure_dy]
  exact polynomial_response_euler p

theorem actual_euler_integrable (p : PlanePolynomial) :
    Integrable (fun x : ℝ × ℝ => x.1*deriv (fun t => pressureFunction p t x.2) x.1+
      x.2*deriv (fun t => pressureFunction p x.1 t) x.2) physicalGaussian := by
  have hi := (polynomial_memLp (X 0*pderiv 0 p+X 1*pderiv 1 p) 1 (by simp)).integrable (by simp)
  simp_rw [pressure_dx, pressure_dy]
  simpa only [pressureFunction, map_add, map_mul, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hi

theorem leadingPressure_laplacian (ε : ℝ) (p : PlanePolynomial) :
    leadingPressure ε (polynomialPressure p)=(Real.pi^2*ε^2/2)*
      (∫ x : ℝ × ℝ, physicalLaplacian p x.1 x.2 ∂physicalGaussian) := by
  rw [leadingPressure_formula, response_actual_laplacian]
  ring

theorem harmonic_response_zero (p : PlanePolynomial)
    (hp : ∀ x y, physicalLaplacian p x y=0) :
    physicalResponse (polynomialPressure p)=0 := by
  rw [response_actual_laplacian]
  simp only [hp, integral_zero, mul_zero]

theorem harmonic_leadingPressure_zero (ε : ℝ) (p : PlanePolynomial)
    (hp : ∀ x y, physicalLaplacian p x y=0) :
    leadingPressure ε (polynomialPressure p)=0 := by
  rw [leadingPressure_formula, harmonic_response_zero p hp, mul_zero]

theorem harmonic_gauge_invariance (p h : PlanePolynomial)
    (hh : ∀ x y, physicalLaplacian h x y=0) :
    physicalResponse (polynomialPressure (p+h))=physicalResponse (polynomialPressure p) := by
  rw [polynomial_response, mul_add, map_add, ← polynomial_response p,
    ← polynomial_response h, harmonic_response_zero h hh, add_zero]

theorem subharmonic_response_nonneg (p : PlanePolynomial)
    (hp : ∀ x y, 0 ≤ physicalLaplacian p x y) :
    0 ≤ physicalResponse (polynomialPressure p) := by
  rw [response_actual_laplacian]
  exact mul_nonneg (by norm_num) (integral_nonneg (fun x => hp x.1 x.2))

theorem response_negative_iff (p : PlanePolynomial) :
    physicalResponse (polynomialPressure p)<0 ↔
      (∫ x : ℝ × ℝ, physicalLaplacian p x.1 x.2 ∂physicalGaussian)<0 := by
  rw [response_actual_laplacian]
  constructor <;> intro h <;> linarith

theorem leadingPressure_negative_iff (ε : ℝ) (hε : ε ≠ 0) (p : PlanePolynomial) :
    leadingPressure ε (polynomialPressure p)<0 ↔
      (∫ x : ℝ × ℝ, physicalLaplacian p x.1 x.2 ∂physicalGaussian)<0 := by
  rw [leadingPressure_laplacian]
  have hc : 0 < Real.pi^2*ε^2/2 := by positivity
  constructor
  · intro h
    by_contra hn
    have hi := mul_nonneg hc.le (le_of_not_gt hn)
    linarith
  · exact mul_neg_of_pos_of_neg hc

def harmonicQuadratic : PlanePolynomial := X 0^2-X 1^2

theorem harmonicQuadratic_eval (x y : ℝ) :
    pressureFunction harmonicQuadratic x y=x^2-y^2 := by
  simp [pressureFunction, harmonicQuadratic]

theorem harmonicQuadratic_laplacian (x y : ℝ) :
    physicalLaplacian harmonicQuadratic x y=0 := by
  rw [physicalLaplacian_eval]
  have htwo (i : Fin 2) : pderiv i (2 : PlanePolynomial)=0 := by
    rw [show (2 : PlanePolynomial)=1+1 by ring, map_add]
    simp
  norm_num [harmonicQuadratic, pderiv_pow, pderiv_X, Pi.single_apply, htwo]

theorem harmonicQuadratic_response : physicalResponse (polynomialPressure harmonicQuadratic)=0 :=
  harmonic_response_zero harmonicQuadratic harmonicQuadratic_laplacian

theorem radialPolynomial_laplacian (x y : ℝ) :
    physicalLaplacian radialPolynomial x y=8 := by
  rw [physicalLaplacian_eval]
  have htwo (i : Fin 2) : pderiv i (2 : PlanePolynomial)=0 := by
    rw [show (2 : PlanePolynomial)=1+1 by ring, map_add]
    simp
  norm_num [radialPolynomial, pderiv_pow, pderiv_X, Pi.single_apply, htwo]

theorem radialPolynomial_response : physicalResponse (polynomialPressure radialPolynomial)=1 := by
  rw [response_actual_laplacian]
  simp only [radialPolynomial_laplacian, integral_const, probReal_univ, smul_eq_mul, one_mul]
  norm_num

end OperatorDerivativeRewrite.Foundation.HelicalPolynomialPressureIBP
