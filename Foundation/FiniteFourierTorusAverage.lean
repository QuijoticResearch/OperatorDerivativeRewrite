import Foundation.FiniteFourierSynthesis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The actual normalized three-coordinate periodic integral of a finite
Fourier synthesis is its constant coefficient. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.FiniteFourierTorusAverage
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def period : ℂ := (2*Real.pi : ℝ)
theorem period_ne_zero : period ≠ 0 := by
  unfold period
  exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)

def circleAverage (j : Fin 3) (F : Space → ℂ) (x : Space) : ℂ :=
  period⁻¹*(∫ r in (0 : ℝ)..2*Real.pi, F (Function.update x j r))

def boxAverage (F : Space → ℂ) : ℂ :=
  circleAverage 2 (circleAverage 1 (circleAverage 0 F)) 0

theorem exponential_integral (n : ℤ) :
    (∫ r in (0 : ℝ)..2*Real.pi, Complex.exp ((Complex.I*(n : ℂ))*(r : ℂ)))=
      if n=0 then period else 0 := by
  by_cases hn : n=0
  · subst n
    simp [period]
  · have hc : Complex.I*(n : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hn)
    rw [integral_exp_mul_complex hc]
    have he : (Complex.I*(n : ℂ))*((2*Real.pi : ℝ) : ℂ)=
        (n : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by push_cast; ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I]
    simp [hn]

theorem character_update_factor (k : Wave) (x : Space) (j : Fin 3) (r : ℝ) :
    character k (Function.update x j r)=
      character k (Function.update x j 0)*Complex.exp (weight j k*(r : ℂ)) := by
  have hp : phase k (Function.update x j r)=phase k (Function.update x j 0)+(k j : ℝ)*r := by
    simp only [phase_update]
    ring
  have he : Complex.I*(phase k (Function.update x j r) : ℂ)=
      Complex.I*(phase k (Function.update x j 0) : ℂ)+weight j k*(r : ℂ) := by
    rw [hp]
    unfold weight
    push_cast
    ring
  unfold character
  rw [he,Complex.exp_add]

theorem circleAverage_const (j : Fin 3) (c : ℂ) (x : Space) :
    circleAverage j (fun _ => c) x=c := by
  unfold circleAverage
  have hi : (∫ r in (0 : ℝ)..2*Real.pi, c)=period*c := by
    simp [period,Complex.real_smul]
  rw [hi,← mul_assoc,inv_mul_cancel₀ period_ne_zero,one_mul]

theorem monomial_average (k : Wave) (c : ℂ) (j : Fin 3) (x : Space) :
    circleAverage j (fun y => c*character k y) x=
      if k j=0 then c*character k x else 0 := by
  by_cases hk : k j=0
  · have hf : (fun r => c*character k (Function.update x j r))=fun _ => c*character k x := by
      funext r
      simp [character,phase_update,hk]
    change period⁻¹*(∫ r in (0 : ℝ)..2*Real.pi, c*character k (Function.update x j r))=_
    rw [hf]
    have hc := circleAverage_const j (c*character k x) x
    simpa only [circleAverage,if_pos hk] using hc
  · have hf : (fun r => c*character k (Function.update x j r))=
        fun r : ℝ => (c*character k (Function.update x j 0))*Complex.exp (weight j k*(r : ℂ)) := by
      funext r
      rw [character_update_factor]
      ring
    change period⁻¹*(∫ r in (0 : ℝ)..2*Real.pi, c*character k (Function.update x j r))=_
    rw [hf,intervalIntegral.integral_const_mul]
    change period⁻¹*((c*character k (Function.update x j 0))*
      (∫ r in (0 : ℝ)..2*Real.pi, Complex.exp ((Complex.I*(k j : ℂ))*(r : ℂ))))=_
    rw [exponential_integral,if_neg hk,mul_zero,mul_zero,if_neg hk]

def cut (j : Fin 3) : Fourier →ₗ[ℂ] Fourier :=
  (Finsupp.linearCombination ℂ (fun k : Wave =>
    if k j=0 then (AddMonoidAlgebra.single k 1 : Fourier) else 0)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem cut_single (j : Fin 3) (k : Wave) (c : ℂ) :
    cut j (AddMonoidAlgebra.single k c)=
      if k j=0 then AddMonoidAlgebra.single k c else 0 := by
  by_cases h : k j=0 <;> simp [cut,h,Finsupp.linearCombination_single]

theorem cut_coeff (j : Fin 3) (f : Fourier) (k : Wave) :
    (cut j f).coeff k=if k j=0 then f.coeff k else 0 := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => by_cases h : k j=0 <;> simp [hf,hg,h]
  | single l c =>
    by_cases he : l=k
    · subst l
      by_cases h : k j=0 <;> simp [cut_single,h]
    · by_cases h : l j=0 <;> simp [cut_single,h,Finsupp.single_apply,he,Ne.symm he]

theorem coordinate_integrable (f : Fourier) (x : Space) (j : Fin 3) :
    IntervalIntegrable (fun r => synthesis (Function.update x j r) f) volume 0 (2*Real.pi) := by
  have hu : Continuous (fun r : ℝ => Function.update x j r) := by
    apply continuous_pi
    intro i
    by_cases h : i=j <;> simp [Function.update_apply,h] <;> fun_prop
  exact ((synthesis_continuous f).comp hu).intervalIntegrable _ _

theorem circleAverage_synthesis_add (j : Fin 3) (x : Space) (f g : Fourier) :
    circleAverage j (fun y => synthesis y (f+g)) x=
      circleAverage j (fun y => synthesis y f) x+circleAverage j (fun y => synthesis y g) x := by
  simp only [circleAverage,map_add]
  rw [intervalIntegral.integral_add (coordinate_integrable f x j) (coordinate_integrable g x j),mul_add]

theorem circleAverage_synthesis (j : Fin 3) (x : Space) (f : Fourier) :
    circleAverage j (fun y => synthesis y f) x=synthesis x (cut j f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [circleAverage]
  | add f g hf hg => rw [circleAverage_synthesis_add,hf,hg,map_add,map_add]
  | single k c =>
    simp only [synthesis_single]
    rw [monomial_average,cut_single]
    by_cases h : k j=0 <;> simp [h,synthesis_single]

theorem circleAverage_synthesis_function (j : Fin 3) (f : Fourier) :
    circleAverage j (fun y => synthesis y f)=fun y => synthesis y (cut j f) :=
  funext (fun x => circleAverage_synthesis j x f)

theorem cut_all (f : Fourier) : cut 2 (cut 1 (cut 0 f))=AddMonoidAlgebra.single 0 (f.coeff 0) := by
  ext k
  by_cases h : k=0
  · subst k
    simp [cut_coeff]
  · simp only [cut_coeff,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,if_neg (Ne.symm h)]
    split_ifs with h₂ h₁ h₀ <;> try rfl
    exfalso
    apply h
    funext i
    fin_cases i <;> assumption

theorem boxAverage_synthesis (f : Fourier) :
    boxAverage (fun x => synthesis x f)=constantTrace f := by
  rw [boxAverage,circleAverage_synthesis_function,circleAverage_synthesis_function,
    circleAverage_synthesis_function,cut_all]
  change synthesis (0 : Space) (AddMonoidAlgebra.single 0 (f.coeff 0))=constantTrace f
  rw [synthesis_single,character_zero,mul_one,constantTrace_apply]

end OperatorDerivativeRewrite.Foundation.FiniteFourierTorusAverage
