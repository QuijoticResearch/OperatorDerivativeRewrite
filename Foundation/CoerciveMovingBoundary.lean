import Foundation.MovingBoundaryCovarianceCounterexample
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The moving-cutoff term persists for uniformly convex quadratic potentials. -/
noncomputable section
open MeasureTheory Set
open scoped Topology
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.CoerciveMovingBoundary
set_option backward.isDefEq.respectTransparency false

def window (f : ℝ → ℝ) (r : ℝ) : ℝ := ∫ y in (-r)..r, f y

theorem even_window (f : ℝ → ℝ) (hf : Continuous f) (he : ∀ y, f (-y)=f y) (r : ℝ) :
    window f r=2*∫ y in (0:ℝ)..r, f y := by
  have hn := intervalIntegral.integral_comp_neg (f := f) (a := (0:ℝ)) (b := r)
  simp only [he, neg_zero] at hn
  rw [window, ← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-r) 0) (hf.intervalIntegrable 0 r), ← hn]
  ring

theorem window_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (he : ∀ y, f (-y)=f y) (r : ℝ) :
    HasDerivAt (window f) (2*f r) r := by
  have h := (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 r)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_mul 2
  have heq : window f=(fun s => 2*∫ y in (0:ℝ)..s, f y) := funext (even_window f hf he)
  rw [heq]
  exact h

def weight (c y : ℝ) : ℝ := Real.exp (-c*y^2)
def normalizer (c r : ℝ) : ℝ := window (weight c) r
def numerator (c r : ℝ) : ℝ := window (fun y => y^2*weight c y) r
def squareMean (c r : ℝ) : ℝ := numerator c r/normalizer c r
def gap (c r : ℝ) : ℝ := r^2*normalizer c r-numerator c r

theorem weight_pos (c y : ℝ) : 0 < weight c y := Real.exp_pos _

theorem normalizer_pos (c r : ℝ) (hr : 0 < r) : 0 < normalizer c r := by
  apply intervalIntegral.integral_pos (by linarith)
  · unfold weight; fun_prop
  · intro y _; exact (weight_pos c y).le
  · exact ⟨0, ⟨by linarith, hr.le⟩, weight_pos c 0⟩

theorem gap_integral (c r : ℝ) :
    gap c r=∫ y in (-r)..r, (r^2-y^2)*weight c y := by
  have hw : Continuous (weight c) := by unfold weight; fun_prop
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (f := fun y => r^2*weight c y) (g := fun y => y^2*weight c y)
    ((hw.const_mul _).intervalIntegrable _ _)
    ((continuous_id.pow 2).mul hw |>.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  rfl

theorem gap_pos (c r : ℝ) (hr : 0 < r) : 0 < gap c r := by
  rw [gap_integral]
  apply intervalIntegral.integral_pos (by linarith)
  · unfold weight; fun_prop
  · intro y hy
    apply mul_nonneg
    · have hp : 0 ≤ (r-y)*(r+y) := mul_nonneg (by linarith [hy.2]) (by linarith [hy.1])
      nlinarith
    · exact (weight_pos c y).le
  · refine ⟨0, ⟨by linarith, hr.le⟩, ?_⟩
    simpa using mul_pos (sq_pos_of_pos hr) (weight_pos c 0)

theorem squareMean_hasDerivAt (c r : ℝ) (hr : 0 < r) :
    HasDerivAt (squareMean c) (2*weight c r*gap c r/(normalizer c r)^2) r := by
  have hw : Continuous (weight c) := by unfold weight; fun_prop
  have hd := window_hasDerivAt (weight c) hw (by intro y; simp [weight]) r
  have hn := window_hasDerivAt (fun y => y^2*weight c y) ((continuous_id.pow 2).mul hw)
    (by intro y; simp [weight]) r
  have h := hn.div hd (ne_of_gt (normalizer_pos c r hr))
  change HasDerivAt (squareMean c)
    ((2*(r^2*weight c r)*normalizer c r-numerator c r*(2*weight c r))/(normalizer c r)^2) r at h
  convert h using 1
  unfold gap
  ring

def radius (x : ℝ) : ℝ := Real.sqrt (1-x^2)
def corridorMean (c x : ℝ) : ℝ := squareMean c (radius x)
def boundarySlope (c x : ℝ) : ℝ :=
  (2*weight c (radius x)*gap c (radius x)/(normalizer c (radius x))^2)*
    ((-2*x)/(2*radius x))

theorem radius_pos (x : ℝ) (hx : x^2 < 1) : 0 < radius x :=
  Real.sqrt_pos.mpr (by linarith)

theorem corridor_slice (x y : ℝ) (hx : x^2 < 1) :
    y ∈ Icc (-radius x) (radius x) ↔ x^2+y^2 ≤ 1 := by
  have hr := radius_pos x hx
  have hs : (radius x)^2=1-x^2 := Real.sq_sqrt (by linarith)
  constructor
  · intro hy
    have he := (sq_le_sq₀ (abs_nonneg y) hr.le).mpr (abs_le.mpr hy)
    rw [sq_abs, hs] at he
    linarith
  · intro hy
    apply abs_le.mp
    apply (sq_le_sq₀ (abs_nonneg y) hr.le).mp
    rw [sq_abs, hs]
    linarith

theorem corridorMean_hasDerivAt (c x : ℝ) (hx : x^2 < 1) :
    HasDerivAt (corridorMean c) (boundarySlope c x) x := by
  have hi : HasDerivAt (fun z : ℝ => 1-z^2) (-2*x) x := by
    convert (hasDerivAt_pow 2 x).const_sub 1 using 1 <;> simp
  have hr := hi.sqrt (by linarith : 1-x^2 ≠ 0)
  exact (squareMean_hasDerivAt c (radius x) (radius_pos x hx)).comp x hr

theorem boundarySlope_neg (c x : ℝ) (hx : 0 < x) (hxx : x^2 < 1) : boundarySlope c x < 0 := by
  have hr := radius_pos x hxx
  have hz := normalizer_pos c (radius x) hr
  have hg := gap_pos c (radius x) hr
  unfold boundarySlope
  apply mul_neg_of_pos_of_neg
  · apply div_pos
    · exact mul_pos (mul_pos (by norm_num) (weight_pos c _)) hg
    · exact sq_pos_of_pos hz
  · apply div_neg_of_neg_of_pos <;> nlinarith

theorem corridor_derivative_neg (c x : ℝ) (hx : 0 < x) (hxx : x^2 < 1) :
    deriv (corridorMean c) x < 0 := by
  rw [(corridorMean_hasDerivAt c x hxx).deriv]
  exact boundarySlope_neg c x hx hxx

def potential (a c x y : ℝ) : ℝ := a*x^2+c*y^2

def expectation (c r : ℝ) (F : ℝ → ℝ) : ℝ := window (fun y => F y*weight c y) r/normalizer c r

def fullExpectation (a c x : ℝ) (F : ℝ → ℝ) : ℝ :=
  window (fun y => F y*Real.exp (-potential a c x y)) (radius x)/
    window (fun y => Real.exp (-potential a c x y)) (radius x)

theorem potential_exp_factor (a c x y : ℝ) :
    Real.exp (-potential a c x y)=Real.exp (-a*x^2)*weight c y := by
  rw [weight, ← Real.exp_add]
  congr 1
  unfold potential
  ring

theorem window_const_mul (f : ℝ → ℝ) (k r : ℝ) :
    window (fun y => k*f y) r=k*window f r := intervalIntegral.integral_const_mul ..

theorem fullExpectation_eq (a c x : ℝ) (F : ℝ → ℝ) :
    fullExpectation a c x F=expectation c (radius x) F := by
  have he (y : ℝ) : F y*Real.exp (-potential a c x y)=
      Real.exp (-a*x^2)*(F y*weight c y) := by rw [potential_exp_factor]; ring
  unfold fullExpectation
  simp_rw [he, potential_exp_factor]
  rw [window_const_mul, window_const_mul]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

theorem full_normalizer_pos (a c x : ℝ) (hx : x^2 < 1) :
    0 < window (fun y => Real.exp (-potential a c x y)) (radius x) := by
  simp_rw [potential_exp_factor]
  rw [window_const_mul]
  exact mul_pos (Real.exp_pos _) (normalizer_pos c (radius x) (radius_pos x hx))

/-- The windows are exactly the Euclidean unit-ball cutoff slices used by the source. -/
theorem fullExpectation_ball (a c x : ℝ) (F : ℝ → ℝ) (hx : x^2 < 1) :
    fullExpectation a c x F =
      (∫ y in {y : ℝ | x^2+y^2 ≤ 1}, F y*Real.exp (-potential a c x y))/
        (∫ y in {y : ℝ | x^2+y^2 ≤ 1}, Real.exp (-potential a c x y)) := by
  have hs : {y : ℝ | x^2+y^2 ≤ 1}=Icc (-radius x) (radius x) := by
    ext y
    exact (corridor_slice x y hx).symm
  rw [hs]
  simp only [fullExpectation, window, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith [radius_pos x hx] : -radius x ≤ radius x)]

theorem expectation_const (c r k : ℝ) (hr : 0 < r) : expectation c r (fun _ => k)=k := by
  rw [expectation, window_const_mul]
  change k*normalizer c r/normalizer c r=k
  exact mul_div_cancel_right₀ k (ne_of_gt (normalizer_pos c r hr))

theorem expectation_mul_const (c r k : ℝ) (F : ℝ → ℝ) :
    expectation c r (fun y => F y*k)=expectation c r F*k := by
  have he (y : ℝ) : (F y*k)*weight c y=k*(F y*weight c y) := by ring
  unfold expectation
  simp_rw [he]
  rw [window_const_mul]
  ring

def fullSquareMean (a c x : ℝ) : ℝ := fullExpectation a c x (fun y => y^2)

theorem fullSquareMean_eq (a c x : ℝ) : fullSquareMean a c x=corridorMean c x := by
  rw [fullSquareMean, fullExpectation_eq]
  rfl

theorem fullSquareMean_derivative_neg (a c x : ℝ) (hx : 0 < x) (hxx : x^2 < 1) :
    deriv (fullSquareMean a c) x < 0 := by
  have he : fullSquareMean a c=corridorMean c := funext (fullSquareMean_eq a c)
  rw [he]
  exact corridor_derivative_neg c x hx hxx

theorem potential_boundary_derivative (a c x y : ℝ) :
    deriv (fun z => potential a c z y) x=2*a*x := by
  have h := ((hasDerivAt_pow 2 x).const_mul a).add_const (c*y^2)
  have hd := h.deriv
  change deriv (fun z => a*z^2+c*y^2) x=a*(2*x^(2-1)) at hd
  simpa [potential, mul_assoc, mul_comm, mul_left_comm] using hd

theorem potential_interior_derivative (a c x y : ℝ) : deriv (potential a c x) y=2*c*y := by
  have he : potential a c x=(fun z => potential c a z x) := by
    funext z
    unfold potential
    ring
  rw [he]
  exact potential_boundary_derivative c a y x

def hessian (a c x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![deriv (fun z => deriv (fun t => potential a c t y) z) x,
     deriv (fun z => deriv (fun t => potential a c t z) x) y;
     deriv (fun z => deriv (potential a c z) y) x,
     deriv (deriv (potential a c x)) y]

theorem hessian_eq (a c x y : ℝ) : hessian a c x y=!![2*a,0;0,2*c] := by
  have hxx : deriv (fun z => deriv (fun t => potential a c t y) z) x=2*a := by
    have he : (fun z => deriv (fun t => potential a c t y) z)=(fun z => 2*a*z) :=
      funext (fun z => potential_boundary_derivative a c z y)
    rw [he]
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (2*a)).deriv
  have hyy : deriv (deriv (potential a c x)) y=2*c := by
    have he : deriv (potential a c x)=(fun z => 2*c*z) :=
      funext (fun z => potential_interior_derivative a c x z)
    rw [he]
    simpa only [id_eq, mul_one] using ((hasDerivAt_id y).const_mul (2*c)).deriv
  have hxy : deriv (fun z => deriv (fun t => potential a c t z) x) y=0 := by
    have he : (fun z => deriv (fun t => potential a c t z) x)=(fun _ : ℝ => 2*a*x) :=
      funext (fun z => potential_boundary_derivative a c x z)
    rw [he]
    simp
  have hyx : deriv (fun z => deriv (potential a c z) y) x=0 := by
    have he : (fun z => deriv (potential a c z) y)=(fun _ : ℝ => 2*c*y) :=
      funext (fun z => potential_interior_derivative a c z y)
    rw [he]
    simp
  rw [hessian, hxx, hyy, hxy, hyx]

def scoreCovariance (a c x : ℝ) : ℝ :=
  fullExpectation a c x (fun y => y^2*deriv (fun z => potential a c z y) x)-
    fullSquareMean a c x*fullExpectation a c x (fun y => deriv (fun z => potential a c z y) x)

theorem scoreCovariance_zero (a c x : ℝ) (hx : x^2 < 1) : scoreCovariance a c x=0 := by
  unfold scoreCovariance fullSquareMean
  simp_rw [potential_boundary_derivative, fullExpectation_eq]
  rw [expectation_mul_const, expectation_const c (radius x) _ (radius_pos x hx)]
  ring

theorem covariance_identity_fails (a c : ℝ) :
    deriv (fullSquareMean a c) (1/2) ≠ -scoreCovariance a c (1/2) := by
  rw [scoreCovariance_zero a c (1/2) (by norm_num), neg_zero]
  exact ne_of_lt (fullSquareMean_derivative_neg a c (1/2) (by norm_num) (by norm_num))

/-- The defect survives arbitrary positive uniform convexity and zero mixed Hessian. -/
theorem uniformly_convex_counterexample (β : ℝ) (hβ : 0 < β) :
    0 < 2*β ∧ (∀ x y, hessian β β x y=(2*β) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      deriv (fullSquareMean β β) (1/2) ≠ -scoreCovariance β β (1/2) := by
  refine ⟨by positivity, ?_, covariance_identity_fails β β⟩
  intro x y
  rw [hessian_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end OperatorDerivativeRewrite.Foundation.CoerciveMovingBoundary
