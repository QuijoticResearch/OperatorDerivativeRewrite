import Foundation.SU2RadialLaplacian

/-! Actual two-mode classical heat trajectories for the verified SU(2) frame
Laplacian. This constructs solutions, not a heat kernel on all observables. -/
noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2PolynomialHeatTrajectory
set_option backward.isDefEq.respectTransparency false
open QuaternionSU2Representation SU2TraceHessianModel
open SU2BoundedObservableGradient SU2RadialFrameCalculus SU2RadialLaplacian

def profile (a b r : ℝ) : ℝ := a*quarticMode r+b*quadraticMode r
def profileDr (a b r : ℝ) : ℝ := a*(64*r^3-24*r)+b*(8*r)
def profileDrr (a b r : ℝ) : ℝ := a*(192*r^2-24)+8*b

theorem profile_derivative (a b r : ℝ) :
    HasDerivAt (profile a b) (profileDr a b r) r := by
  have h4 := (((hasDerivAt_id' r).pow 4).const_mul 16).sub
    (((hasDerivAt_id' r).pow 2).const_mul 12) |>.add_const 1
  have h2 := ((hasDerivAt_id' r).pow 2).const_mul 4 |>.sub_const 1
  convert (h4.const_mul a).add (h2.const_mul b) using 1 <;>
    first | rfl | (dsimp [profile, profileDr, quarticMode, quadraticMode]; ring)

theorem profile_second (a b r : ℝ) :
    HasDerivAt (profileDr a b) (profileDrr a b r) r := by
  have h3 := (((hasDerivAt_id' r).pow 3).const_mul 64).sub
    ((hasDerivAt_id' r).const_mul 24)
  have h1 := (hasDerivAt_id' r).const_mul 8
  convert (h3.const_mul a).add (h1.const_mul b) using 1 <;>
    first | rfl | (dsimp [profileDr, profileDrr]; ring)

theorem profile_laplacian (a b : ℝ) (A : SU2) :
    laplacian (radial (profile a b)) A =
      -6*a*quarticMode (halfTrace A)-2*b*quadraticMode (halfTrace A) := by
  rw [radial_formula (profile a b) (profileDr a b) (profileDrr a b)
    (profile_derivative a b) (profile_second a b)]
  unfold profileDr profileDrr quarticMode quadraticMode
  ring

def evolve (t a b : ℝ) (A : SU2) : ℝ :=
  profile (a*Real.exp (-6*t)) (b*Real.exp (-2*t)) (halfTrace A)

theorem evolve_initial (a b : ℝ) (A : SU2) : evolve 0 a b A = profile a b (halfTrace A) := by
  simp [evolve]

theorem evolve_time_derivative (t a b : ℝ) (A : SU2) :
    HasDerivAt (fun t => evolve t a b A)
      (-6*a*Real.exp (-6*t)*quarticMode (halfTrace A)-
        2*b*Real.exp (-2*t)*quadraticMode (halfTrace A)) t := by
  have h6 := ((hasDerivAt_id' t).const_mul (-6)).exp
  have h2 := ((hasDerivAt_id' t).const_mul (-2)).exp
  have h := ((h6.const_mul a).mul_const (quarticMode (halfTrace A))).add
    ((h2.const_mul b).mul_const (quadraticMode (halfTrace A)))
  have hc : a*(Real.exp (-6*t)*(-6*1))*quarticMode (halfTrace A)+
      b*(Real.exp (-2*t)*(-2*1))*quadraticMode (halfTrace A) =
      -6*a*Real.exp (-6*t)*quarticMode (halfTrace A)-
        2*b*Real.exp (-2*t)*quadraticMode (halfTrace A) := by ring
  rw [hc] at h
  exact h

theorem evolve_laplacian (t a b : ℝ) (A : SU2) :
    laplacian (evolve t a b) A =
      -6*a*Real.exp (-6*t)*quarticMode (halfTrace A)-
        2*b*Real.exp (-2*t)*quadraticMode (halfTrace A) := by
  have h := profile_laplacian (a*Real.exp (-6*t)) (b*Real.exp (-2*t)) A
  convert h using 1 <;> first | rfl | ring

theorem heat_equation (t a b : ℝ) (A : SU2) :
    deriv (fun t => evolve t a b A) t = laplacian (evolve t a b) A := by
  rw [(evolve_time_derivative t a b A).deriv, evolve_laplacian]

theorem coefficient_composition (s t a b : ℝ) (A : SU2) :
    evolve (s+t) a b A = evolve s (a*Real.exp (-6*t)) (b*Real.exp (-2*t)) A := by
  unfold evolve profile
  rw [show -6*(s+t)=(-6*s)+(-6*t) by ring,
    show -2*(s+t)=(-2*s)+(-2*t) by ring, Real.exp_add, Real.exp_add]
  ring

theorem evolve_measurable (a b : ℝ) :
    Measurable (fun p : ℝ × SU2 => evolve p.1 a b p.2) := by
  have hq4 : Measurable (fun A : SU2 => quarticMode (halfTrace A)) := by
    have hm : Measurable quarticMode := by unfold quarticMode; fun_prop
    exact hm.comp halfTrace_measurable
  have hq2 : Measurable (fun A : SU2 => quadraticMode (halfTrace A)) := by
    have hm : Measurable quadraticMode := by unfold quadraticMode; fun_prop
    exact hm.comp halfTrace_measurable
  have h6 : Measurable (fun p : ℝ × SU2 => a*Real.exp (-6*p.1)) := by fun_prop
  have h2 : Measurable (fun p : ℝ × SU2 => b*Real.exp (-2*p.1)) := by fun_prop
  exact (h6.mul (hq4.comp measurable_snd)).add (h2.mul (hq2.comp measurable_snd))

theorem quadratic_bound (A : SU2) : |quadraticMode (halfTrace A)| ≤ 3 := by
  have hh := (sq_le_one_iff_abs_le_one (halfTrace A)).mpr (halfTrace_bound A)
  rw [abs_le]
  unfold quadraticMode
  constructor <;> nlinarith [sq_nonneg (halfTrace A)]

theorem quartic_bound (A : SU2) : |quarticMode (halfTrace A)| ≤ 5 := by
  have he : quarticMode (halfTrace A) = 2*observable A+quadraticMode (halfTrace A) := by
    have h := observable_decomposition A
    linarith
  rw [he]
  calc
    _ ≤ |2*observable A|+|quadraticMode (halfTrace A)| := abs_add_le _ _
    _ ≤ 5 := by rw [abs_mul]; norm_num; nlinarith [observable_bound A, quadratic_bound A]

theorem evolve_bound (t a b : ℝ) (A : SU2) :
    |evolve t a b A| ≤ 5 * |a| * Real.exp (-6*t)+3 * |b| * Real.exp (-2*t) := by
  unfold evolve profile
  calc
    _ ≤ |a*Real.exp (-6*t)*quarticMode (halfTrace A)|+
        |b*Real.exp (-2*t)*quadraticMode (halfTrace A)| := abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith [mul_nonneg (abs_nonneg a) (Real.exp_pos (-6*t)).le,
        mul_nonneg (abs_nonneg b) (Real.exp_pos (-2*t)).le,
        mul_le_mul_of_nonneg_left (quartic_bound A)
          (mul_nonneg (abs_nonneg a) (Real.exp_pos (-6*t)).le),
        mul_le_mul_of_nonneg_left (quadratic_bound A)
          (mul_nonneg (abs_nonneg b) (Real.exp_pos (-2*t)).le)]

theorem evolve_uniform_decay (t a b : ℝ) (ht : 0 ≤ t) (A : SU2) :
    |evolve t a b A| ≤ (5 * |a| + 3 * |b|) * Real.exp (-2*t) := by
  have he : Real.exp (-6*t) ≤ Real.exp (-2*t) := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ 5 * |a| * Real.exp (-6*t)+3 * |b| * Real.exp (-2*t) := evolve_bound t a b A
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 5 * |a|)]

def observableTrajectory (t : ℝ) (A : SU2) : ℝ := evolve t (1/2) (-1/2) A

theorem observable_initial (A : SU2) : observableTrajectory 0 A = observable A := by
  rw [observableTrajectory, evolve_initial, observable_decomposition]
  unfold profile
  ring

theorem observable_heat_equation (t : ℝ) (A : SU2) :
    deriv (fun t => observableTrajectory t A) t = laplacian (observableTrajectory t) A :=
  heat_equation t (1/2) (-1/2) A

theorem observable_decay (t : ℝ) (ht : 0 ≤ t) (A : SU2) :
    |observableTrajectory t A| ≤ 4*Real.exp (-2*t) := by
  convert evolve_uniform_decay t (1/2) (-1/2) ht A using 1 <;> norm_num [observableTrajectory]

theorem observable_log_two_value : observableTrajectory (Real.log 2) (1 : SU2) = -43/128 := by
  have h2 : Real.exp (-2*Real.log 2) = 1/4 := by
    rw [show -2*Real.log 2 = -(Real.log 2+Real.log 2) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h6 : Real.exp (-6*Real.log 2) = 1/64 := by
    rw [show -6*Real.log 2 = (-2*Real.log 2)+(-2*Real.log 2)+(-2*Real.log 2) by ring,
      Real.exp_add, Real.exp_add, h2]
    norm_num
  unfold observableTrajectory evolve profile
  rw [h2, h6]
  norm_num [halfTrace, traceReal, Matrix.trace_one, quarticMode, quadraticMode]

theorem observable_sign_change :
    0 < observableTrajectory 0 (1 : SU2) ∧ observableTrajectory (Real.log 2) 1 < 0 := by
  rw [observable_initial, observable_log_two_value]
  norm_num [observable, ambient, polynomial, halfTrace, traceReal, Matrix.trace_one]

end OperatorDerivativeRewrite.Foundation.SU2PolynomialHeatTrajectory
