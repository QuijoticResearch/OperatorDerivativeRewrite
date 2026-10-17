import Foundation.FiniteFourierDifferentialTrace
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Actual periodic exponential synthesis realizes the convolution algebra
and its ik_j derivations as multiplication and real coordinate derivatives. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteFourierSynthesis
open FiniteFourierDifferentialTrace
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

abbrev Space := Fin 3 → ℝ
def phase (k : Wave) (x : Space) : ℝ := ∑ i, (k i : ℝ)*x i
def character (k : Wave) (x : Space) : ℂ := Complex.exp (Complex.I*(phase k x : ℂ))

theorem phase_add (k l : Wave) (x : Space) : phase (k+l) x=phase k x+phase l x := by
  simp [phase,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem character_add (k l : Wave) (x : Space) : character (k+l) x=character k x*character l x := by
  simp only [character,phase_add,Complex.ofReal_add,mul_add,Complex.exp_add]

theorem character_zero (x : Space) : character 0 x=1 := by simp [character,phase]

def synthesis (x : Space) : Fourier →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ (fun k : Wave => character k x)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem synthesis_single (x : Space) (k : Wave) (c : ℂ) :
    synthesis x (AddMonoidAlgebra.single k c)=c*character k x := by
  simp [synthesis,Finsupp.linearCombination_single,smul_eq_mul]

theorem synthesis_one (x : Space) : synthesis x (1 : Fourier)=1 := by
  rw [AddMonoidAlgebra.one_def,synthesis_single,character_zero,one_mul]

theorem synthesis_mul (x : Space) (f g : Fourier) :
    synthesis x (f*g)=synthesis x f*synthesis x g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [add_mul,map_add,hf,hf'] <;> ring
  | single k c =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp only [mul_add,map_add,hg,hg'] <;> ring
    | single l d =>
      rw [AddMonoidAlgebra.single_mul_single,synthesis_single,synthesis_single,synthesis_single,character_add]
      ring

theorem phase_update (k : Wave) (x : Space) (j : Fin 3) (r : ℝ) :
    phase k (Function.update x j r)=phase k x+(k j : ℝ)*(r-x j) := by
  fin_cases j <;> norm_num [phase,Function.update_apply,Fin.sum_univ_succ] <;> ring

theorem phase_coordinate_derivative (k : Wave) (x : Space) (j : Fin 3) :
    HasDerivAt (fun r => phase k (Function.update x j r)) (k j : ℝ) (x j) := by
  have h := (((hasDerivAt_id (x j)).sub_const (x j)).const_mul (k j : ℝ)).const_add (phase k x)
  simpa only [phase_update,mul_one,id_eq] using! h

theorem character_coordinate_derivative (k : Wave) (x : Space) (j : Fin 3) :
    HasDerivAt (fun r => character k (Function.update x j r))
      (weight j k*character k x) (x j) := by
  have h := ((phase_coordinate_derivative k x j).ofReal_comp.const_mul Complex.I).cexp
  simpa [character,weight,mul_comm,mul_left_comm,mul_assoc] using h

theorem synthesis_coordinate_derivative (f : Fourier) (x : Space) (j : Fin 3) :
    HasDerivAt (fun r => synthesis (Function.update x j r) f)
      (synthesis x (derivative j f)) (x j) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simpa using hasDerivAt_const (x j) (0 : ℂ)
  | add f g hf hg => simpa only [map_add,Pi.add_apply] using! hf.add hg
  | single k c =>
    have h := (character_coordinate_derivative k x j).const_mul c
    simpa [synthesis_single,derivative_apply,d_single,mul_comm,mul_left_comm,mul_assoc] using h

def coordinateDerivative (j : Fin 3) (f : Space → ℂ) (x : Space) : ℂ :=
  deriv (fun r => f (Function.update x j r)) (x j)

theorem partial_synthesis (f : Fourier) (x : Space) (j : Fin 3) :
    coordinateDerivative j (fun y => synthesis y f) x=synthesis x (derivative j f) :=
  (synthesis_coordinate_derivative f x j).deriv

theorem character_coordinate_periodic (k : Wave) (x : Space) (j : Fin 3) :
    Function.Periodic (fun r : ℝ => character k (Function.update x j r)) (2*Real.pi) := by
  intro r
  simp only [character,phase_update]
  have he : Complex.I*((phase k x+(k j : ℝ)*(r+2*Real.pi-x j) : ℝ) : ℂ)=
      Complex.I*((phase k x+(k j : ℝ)*(r-x j) : ℝ) : ℂ)+
        (k j : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]

theorem synthesis_coordinate_periodic (f : Fourier) (x : Space) (j : Fin 3) :
    Function.Periodic (fun r : ℝ => synthesis (Function.update x j r) f) (2*Real.pi) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => intro r; simp
  | add f g hf hg => intro r; simpa only [map_add] using congrArg₂ (·+·) (hf r) (hg r)
  | single k c => intro r; simp only [synthesis_single,character_coordinate_periodic k x j r]

theorem character_continuous (k : Wave) : Continuous (character k) := by
  unfold character phase
  fun_prop

theorem synthesis_continuous (f : Fourier) : Continuous (fun x => synthesis x f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simpa using continuous_const (y := (0 : ℂ))
  | add f g hf hg =>
    have he : (fun x => synthesis x (f+g))=
        (fun x => synthesis x f)+(fun x => synthesis x g) := by
      funext x
      exact map_add (synthesis x) f g
    rw [he]
    exact hf.add hg
  | single k c => simpa only [synthesis_single] using (character_continuous k).const_mul c

end OperatorDerivativeRewrite.Foundation.FiniteFourierSynthesis
