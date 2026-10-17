import Foundation.HelicalWeightedPressureIBP
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! An axis-regular Gaussian swirl and a pressure constructed by radial integration. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace OperatorDerivativeRewrite.Foundation.GaussianSwirlVelocity
set_option backward.isDefEq.respectTransparency false

def angularProfile (s : ℝ) : ℝ := (∫ t in (0 : ℝ)..1, Real.exp (-t*s))/2
def angularDerivative (s : ℝ) : ℝ := (∫ t in (0 : ℝ)..1, -t*Real.exp (-t*s))/2

theorem angularProfile_hasDerivAt (s₀ : ℝ) :
    HasDerivAt angularProfile (angularDerivative s₀) s₀ := by
  let F (s t : ℝ) := Real.exp (-t*s)
  let G (s t : ℝ) := -t*Real.exp (-t*s)
  let B : ℝ := Real.exp (|s₀|+1)
  have hs : Ioo (s₀-1) (s₀+1) ∈ 𝓝 s₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hb : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ s ∈ Ioo (s₀-1) (s₀+1), ‖G s t‖ ≤ B := by
    filter_upwards with t ht s hs
    have htt : 0 < t ∧ t ≤ 1 := by simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num), mem_Ioc] using ht
    have ht0 : 0 ≤ t := htt.1.le
    have ht1 : t ≤ 1 := htt.2
    have hsa : |s| ≤ |s₀|+1 := by
      rw [abs_le]
      constructor <;> linarith [le_abs_self s₀, neg_abs_le s₀, hs.1, hs.2]
    have hexp : Real.exp (-t*s) ≤ B := by
      apply Real.exp_le_exp.mpr
      calc
        -t*s = -(t*s) := by ring
        _ ≤ |t*s| := neg_le_abs _
        _ = t*|s| := by rw [abs_mul, abs_of_nonneg ht0]
        _ ≤ |s| := by nlinarith [abs_nonneg s]
        _ ≤ |s₀|+1 := hsa
    change ‖-t*Real.exp (-t*s)‖ ≤ B
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg ht0, abs_of_pos (Real.exp_pos _)]
    calc
      t*Real.exp (-t*s) ≤ Real.exp (-t*s) := by nlinarith [Real.exp_pos (-t*s)]
      _ ≤ B := hexp
  have hd : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ s ∈ Ioo (s₀-1) (s₀+1),
      HasDerivAt (fun s => F s t) (G s t) s := by
    filter_upwards with t ht s hs
    have hh := ((hasDerivAt_id s).const_mul (-t)).exp
    simp only [id_eq, mul_one] at hh
    change HasDerivAt (fun s => F s t) (Real.exp (-t*s)*(-t)) s at hh
    convert hh using 1 <;> unfold G <;> ring
  obtain ⟨_,hh⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall (fun s => show AEStronglyMeasurable (F s) (volume.restrict (Ι (0 : ℝ) 1)) from by unfold F; fun_prop))
    (show IntervalIntegrable (F s₀) volume 0 1 from (by unfold F; fun_prop : Continuous (F s₀)).intervalIntegrable 0 1)
    (show AEStronglyMeasurable (G s₀) (volume.restrict (Ι (0 : ℝ) 1)) from by unfold G; fun_prop)
    hb (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume 0 1) hd
  exact hh.div_const 2

theorem angularProfile_continuous : Continuous angularProfile :=
  continuous_iff_continuousAt.mpr (fun s => (angularProfile_hasDerivAt s).continuousAt)

theorem angularProfile_zero : angularProfile 0=1/2 := by simp [angularProfile]

theorem angularDerivative_zero : angularDerivative 0= -1/4 := by
  simp only [angularDerivative, mul_zero, neg_zero, Real.exp_zero, mul_one]
  rw [intervalIntegral.integral_neg, integral_id]
  norm_num

theorem angularProfile_quotient (s : ℝ) (hs : s ≠ 0) :
    angularProfile s=(1-Real.exp (-s))/(2*s) := by
  have hd (t : ℝ) : HasDerivAt (fun t => Real.exp (-t*s)) (-s*Real.exp (-t*s)) t := by
    convert ((hasDerivAt_id t).mul_const (-s)).exp using 1 <;> (try funext u) <;> simp <;> ring
  have hi : IntervalIntegrable (fun t => -s*Real.exp (-t*s)) volume 0 1 :=
    (by fun_prop : Continuous (fun t => -s*Real.exp (-t*s))).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at he
  simp only [neg_zero, zero_mul, Real.exp_zero, neg_mul, one_mul] at he
  unfold angularProfile
  field_simp
  nlinarith

theorem angular_curl_identity (s : ℝ) :
    2*angularProfile s+2*s*angularDerivative s=Real.exp (-s) := by
  have hd (t : ℝ) : HasDerivAt (fun t => t*Real.exp (-t*s))
      (Real.exp (-t*s)+s*(-t*Real.exp (-t*s))) t := by
    have hg : HasDerivAt (fun t => Real.exp (-t*s)) (-s*Real.exp (-t*s)) t := by
      convert ((hasDerivAt_id t).mul_const (-s)).exp using 1 <;> (try funext u) <;> simp <;> ring
    have hp := (hasDerivAt_id t).mul hg
    change HasDerivAt (fun u => u*Real.exp (-u*s))
      (1*Real.exp (-t*s)+t*(-s*Real.exp (-t*s))) t at hp
    convert hp using 1 <;> ring
  have hi : IntervalIntegrable (fun t => Real.exp (-t*s)+s*(-t*Real.exp (-t*s))) volume 0 1 :=
    (by fun_prop : Continuous (fun t => Real.exp (-t*s)+s*(-t*Real.exp (-t*s)))).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-t*s))).intervalIntegrable 0 1) ((by fun_prop : Continuous (fun t : ℝ => s*(-t*Real.exp (-t*s)))).intervalIntegrable 0 1), intervalIntegral.integral_const_mul] at he
  simp only [one_mul, zero_mul, sub_zero, neg_mul] at he
  unfold angularProfile angularDerivative
  simp only [neg_mul]
  nlinarith [he]

def radialPressure (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, angularProfile t^2/2

theorem radialPressure_hasDerivAt (s : ℝ) :
    HasDerivAt radialPressure (angularProfile s^2/2) s := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (angularProfile_continuous.pow 2 |>.div_const 2).intervalIntegrable 0 s
  · exact (angularProfile_continuous.pow 2 |>.div_const 2).stronglyMeasurable.stronglyMeasurableAtFilter
  · exact (angularProfile_continuous.pow 2 |>.div_const 2).continuousAt

def pressure (x y : ℝ) : ℝ := radialPressure (x^2+y^2)
def velocity (x y _z : ℝ) : Fin 3 → ℝ :=
  ![-y*angularProfile (x^2+y^2),x*angularProfile (x^2+y^2),0]

theorem pressure_x (x y : ℝ) : HasDerivAt (fun t => pressure t y)
    (x*angularProfile (x^2+y^2)^2) x := by
  have hs : HasDerivAt (fun t : ℝ => t^2+y^2) (2*x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y^2)
  have hh := (radialPressure_hasDerivAt (x^2+y^2)).comp x hs
  change HasDerivAt (fun t => pressure t y) ((angularProfile (x^2+y^2)^2/2)*(2*x)) x at hh
  convert hh using 1 <;> ring

theorem pressure_y (x y : ℝ) : HasDerivAt (fun t => pressure x t)
    (y*angularProfile (x^2+y^2)^2) y := by
  have hs : HasDerivAt (fun t : ℝ => x^2+t^2) (2*y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (x^2)
  have hh := (radialPressure_hasDerivAt (x^2+y^2)).comp y hs
  change HasDerivAt (fun t => pressure x t) ((angularProfile (x^2+y^2)^2/2)*(2*y)) y at hh
  convert hh using 1 <;> ring

theorem profile_x (x y : ℝ) : HasDerivAt (fun t => angularProfile (t^2+y^2))
    (2*x*angularDerivative (x^2+y^2)) x := by
  have hs : HasDerivAt (fun t : ℝ => t^2+y^2) (2*x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y^2)
  have hh := (angularProfile_hasDerivAt (x^2+y^2)).comp x hs
  change HasDerivAt (fun t => angularProfile (t^2+y^2))
    (angularDerivative (x^2+y^2)*(2*x)) x at hh
  convert hh using 1 <;> ring

theorem profile_y (x y : ℝ) : HasDerivAt (fun t => angularProfile (x^2+t^2))
    (2*y*angularDerivative (x^2+y^2)) y := by
  have hs : HasDerivAt (fun t : ℝ => x^2+t^2) (2*y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (x^2)
  have hh := (angularProfile_hasDerivAt (x^2+y^2)).comp y hs
  change HasDerivAt (fun t => angularProfile (x^2+t^2))
    (angularDerivative (x^2+y^2)*(2*y)) y at hh
  convert hh using 1 <;> ring

def jacobian (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![deriv (fun t => velocity t y z 0) x,deriv (fun t => velocity x t z 0) y,
        deriv (fun t => velocity x y t 0) z],
    ![deriv (fun t => velocity t y z 1) x,deriv (fun t => velocity x t z 1) y,
        deriv (fun t => velocity x y t 1) z],
    ![deriv (fun t => velocity t y z 2) x,deriv (fun t => velocity x t z 2) y,
        deriv (fun t => velocity x y t 2) z] ]

theorem jacobian_eq (x y z : ℝ) : jacobian x y z=
    ![![-2*x*y*angularDerivative (x^2+y^2),
          -angularProfile (x^2+y^2)-2*y^2*angularDerivative (x^2+y^2),0],
      ![angularProfile (x^2+y^2)+2*x^2*angularDerivative (x^2+y^2),
          2*x*y*angularDerivative (x^2+y^2),0],![0,0,0] ] := by
  have h00 : HasDerivAt (fun t => -y*angularProfile (t^2+y^2))
      (-2*x*y*angularDerivative (x^2+y^2)) x := by
    convert (profile_x x y).const_mul (-y) using 1 <;> ring
  have h01 : HasDerivAt (fun t => -t*angularProfile (x^2+t^2))
      (-angularProfile (x^2+y^2)-2*y^2*angularDerivative (x^2+y^2)) y := by
    have hh := (hasDerivAt_id y).neg.mul (profile_y x y)
    change HasDerivAt (fun t => -t*angularProfile (x^2+t^2))
      (-1*angularProfile (x^2+y^2)+ -y*(2*y*angularDerivative (x^2+y^2))) y at hh
    convert hh using 1 <;> ring
  have h10 : HasDerivAt (fun t => t*angularProfile (t^2+y^2))
      (angularProfile (x^2+y^2)+2*x^2*angularDerivative (x^2+y^2)) x := by
    have hh := (hasDerivAt_id x).mul (profile_x x y)
    change HasDerivAt (fun t => t*angularProfile (t^2+y^2))
      (1*angularProfile (x^2+y^2)+x*(2*x*angularDerivative (x^2+y^2))) x at hh
    convert hh using 1 <;> ring
  have h11 : HasDerivAt (fun t => x*angularProfile (x^2+t^2))
      (2*x*y*angularDerivative (x^2+y^2)) y := by
    convert (profile_y x y).const_mul x using 1 <;> ring
  simp only [jacobian,velocity,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,h00.deriv,h01.deriv,h10.deriv,h11.deriv,deriv_const]

theorem divergence_zero (x y z : ℝ) : Matrix.trace (jacobian x y z)=0 := by
  rw [jacobian_eq]
  norm_num [Matrix.trace,Fin.sum_univ_succ]

def curl (x y z : ℝ) : Fin 3 → ℝ :=
  ![jacobian x y z 2 1-jacobian x y z 1 2,
    jacobian x y z 0 2-jacobian x y z 2 0,
    jacobian x y z 1 0-jacobian x y z 0 1]

theorem curl_gaussian (x y z : ℝ) : curl x y z=![0,0,Real.exp (-(x^2+y^2))] := by
  rw [curl,jacobian_eq]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,sub_self,sub_zero]
  have he := angular_curl_identity (x^2+y^2)
  have hc : angularProfile (x^2+y^2)+2*x^2*angularDerivative (x^2+y^2)-
      (-angularProfile (x^2+y^2)-2*y^2*angularDerivative (x^2+y^2))=Real.exp (-(x^2+y^2)) := by
    nlinarith [he]
  rw [hc]
def pressureGradient (x y z : ℝ) : Fin 3 → ℝ :=
  ![deriv (fun t => pressure t y) x,deriv (fun t => pressure x t) y,
    deriv (fun _ : ℝ => pressure x y) z]

theorem pressureGradient_eq (x y z : ℝ) : pressureGradient x y z=
    ![x*angularProfile (x^2+y^2)^2,y*angularProfile (x^2+y^2)^2,0] := by
  simp only [pressureGradient,(pressure_x x y).deriv,(pressure_y x y).deriv,deriv_const]

def acceleration (x y z : ℝ) : Fin 3 → ℝ :=
  fun i => ∑ j, velocity x y z j*jacobian x y z i j

/-- Pointwise stationary incompressible Euler balance, with the constructed pressure. -/
theorem steady_euler (x y z : ℝ) : acceleration x y z+pressureGradient x y z=0 := by
  rw [pressureGradient_eq]
  unfold acceleration
  rw [jacobian_eq]
  ext i
  fin_cases i <;> simp [velocity,Fin.sum_univ_succ] <;> ring

theorem pressure_radial_energy (x y z : ℝ) :
    x*deriv (fun t => pressure t y) x+y*deriv (fun t => pressure x t) y=
      (velocity x y z 0)^2+(velocity x y z 1)^2 := by
  rw [(pressure_x x y).deriv,(pressure_y x y).deriv]
  simp [velocity]
  ring

theorem pressure_radial_nonneg (x y : ℝ) :
    0 ≤ x*deriv (fun t => pressure t y) x+y*deriv (fun t => pressure x t) y := by
  rw [pressure_radial_energy x y 0]
  positivity

theorem pressure_xx (x y : ℝ) : HasDerivAt (fun t => t*angularProfile (t^2+y^2)^2)
    (angularProfile (x^2+y^2)^2+4*x^2*angularProfile (x^2+y^2)*angularDerivative (x^2+y^2)) x := by
  have hh := (hasDerivAt_id x).mul ((profile_x x y).pow 2)
  have hf : id*(fun t : ℝ => angularProfile (t^2+y^2))^2=(fun t => t*angularProfile (t^2+y^2)^2) := by
    funext t
    simp only [Pi.mul_apply,Pi.pow_apply,id_eq]
  rw [hf] at hh
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq,one_mul,Nat.reduceSub,pow_one] at hh
  convert hh using 1 <;> ring

theorem pressure_yy (x y : ℝ) : HasDerivAt (fun t => t*angularProfile (x^2+t^2)^2)
    (angularProfile (x^2+y^2)^2+4*y^2*angularProfile (x^2+y^2)*angularDerivative (x^2+y^2)) y := by
  have hh := (hasDerivAt_id y).mul ((profile_y x y).pow 2)
  have hf : id*(fun t : ℝ => angularProfile (x^2+t^2))^2=(fun t => t*angularProfile (x^2+t^2)^2) := by
    funext t
    simp only [Pi.mul_apply,Pi.pow_apply,id_eq]
  rw [hf] at hh
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq,one_mul,Nat.reduceSub,pow_one] at hh
  convert hh using 1 <;> ring

theorem pressure_laplacian (x y : ℝ) :
    HelicalWeightedPressureIBP.actualLaplacian (fun p => pressure p.1 p.2) (x,y)=
      2*angularProfile (x^2+y^2)^2+
        4*(x^2+y^2)*angularProfile (x^2+y^2)*angularDerivative (x^2+y^2) := by
  have hx (a b : ℝ) : deriv (fun t => pressure t b) a=a*angularProfile (a^2+b^2)^2 :=
    (pressure_x a b).deriv
  have hy (a b : ℝ) : deriv (fun t => pressure a t) b=b*angularProfile (a^2+b^2)^2 :=
    (pressure_y a b).deriv
  unfold HelicalWeightedPressureIBP.actualLaplacian
  simp only [Prod.fst,Prod.snd]
  simp_rw [hx,hy]
  rw [(pressure_xx x y).deriv,(pressure_yy x y).deriv]
  ring

theorem velocity_trace_square (x y z : ℝ) :
    Matrix.trace (jacobian x y z*jacobian x y z)=
      -2*angularProfile (x^2+y^2)^2-
        4*(x^2+y^2)*angularProfile (x^2+y^2)*angularDerivative (x^2+y^2) := by
  rw [jacobian_eq]
  norm_num [Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ]
  ring

/-- Actual velocity-pressure Poisson compatibility for this stationary Euler swirl. -/
theorem pressure_poisson (x y z : ℝ) :
    HelicalWeightedPressureIBP.actualLaplacian (fun p => pressure p.1 p.2) (x,y)=
      -Matrix.trace (jacobian x y z*jacobian x y z) := by
  rw [pressure_laplacian,velocity_trace_square]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianSwirlVelocity
