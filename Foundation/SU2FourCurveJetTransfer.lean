import Foundation.FourCubeAmbientAction
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! Transfer of the actual four-link Wilson action through matching matrix two-jets. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2FourCurveJetTransfer
open SU2TraceHessianModel SU2MatrixExponentialBridge SU2ProductCurveHessian
open SU2FourWordVariation FourCubeAmbientAction

abbrev WordField := Fin 4 → M2

def traceAction (Z : WordField) : ℝ := 1-traceReal (Z 0*Z 1*(Z 2)ᴴ*(Z 3)ᴴ)/2

theorem traceAction_contDiff : ContDiff ℝ 2 traceAction := by
  have h0 : ContDiff ℝ 2 (fun Z : WordField => Z 0) := _root_.contDiff_apply ℝ M2 (0 : Fin 4)
  have h1 : ContDiff ℝ 2 (fun Z : WordField => Z 1) := _root_.contDiff_apply ℝ M2 (1 : Fin 4)
  have h2 := adjoint_contDiff.comp (_root_.contDiff_apply ℝ M2 (2 : Fin 4))
  have h3 := adjoint_contDiff.comp (_root_.contDiff_apply ℝ M2 (3 : Fin 4))
  exact contDiff_const.sub ((realTraceCLM.contDiff.comp (((h0.mul h1).mul h2).mul h3)).div_const 2)

def model (v : Fin 4 → Fin 3 → ℝ) (t : ℝ) : WordField :=
  fun i => NormedSpace.exp (t • algebraElement (v i))

theorem exponential_contDiff (B : M2) :
    ContDiff ℝ 2 (fun t : ℝ => NormedSpace.exp (t • B)) := by
  have hh : ContDiff ℝ 2 (NormedSpace.exp : M2 → M2) :=
    contDiff_iff_contDiffAt.mpr (fun M => (NormedSpace.exp_analytic (𝕂 := ℝ) M).contDiffAt)
  exact hh.comp (contDiff_id.smul contDiff_const)

theorem model_contDiff (v : Fin 4 → Fin 3 → ℝ) : ContDiff ℝ 2 (model v) :=
  contDiff_pi.mpr (fun i => exponential_contDiff (algebraElement (v i)))

theorem model_zero (v : Fin 4 → Fin 3 → ℝ) : model v 0=(fun _ => 1) := by
  funext i
  simp [model]

theorem model_first (v : Fin 4 → Fin 3 → ℝ) (t : ℝ) :
    deriv (model v) t=(fun i => algebraElement (v i)*NormedSpace.exp (t • algebraElement (v i))) := by
  have hh := deriv_pi (fun i : Fin 4 =>
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (algebraElement (v i)) t).differentiableAt)
  calc
    _ = (fun i => deriv (fun u : ℝ => NormedSpace.exp (u • algebraElement (v i))) t) := by
      convert! hh using 1
    _ = _ := funext (fun i => (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (algebraElement (v i)) t).deriv)

theorem model_first_zero (v : Fin 4 → Fin 3 → ℝ) :
    deriv (model v) 0=(fun i => algebraElement (v i)) := by
  rw [model_first]
  simp only [zero_smul,NormedSpace.exp_zero,mul_one]

theorem model_second_zero (v : Fin 4 → Fin 3 → ℝ) :
    deriv (deriv (model v)) 0=(fun i => (algebraElement (v i))^2) := by
  have he := funext (model_first v)
  rw [he]
  have hh := deriv_pi (fun i : Fin 4 =>
    ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) (algebraElement (v i)) (0 : ℝ)).const_mul
      (algebraElement (v i))).differentiableAt)
  calc
    _ = (fun i => deriv (fun t : ℝ => algebraElement (v i)*
        NormedSpace.exp (t • algebraElement (v i))) 0) := by convert! hh using 1
    _ = _ := by
      funext i
      convert! ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) (algebraElement (v i)) (0 : ℝ)).const_mul
        (algebraElement (v i))).deriv using 1 <;>
        simp only [zero_smul,NormedSpace.exp_zero,mul_one,pow_two]

theorem trace_model (v : Fin 4 → Fin 3 → ℝ) (t : ℝ) :
    traceAction (model v t)=SU2FourWordVariation.action (algebraElement (v 0))
      (algebraElement (v 1)) (-algebraElement (v 2)) (-algebraElement (v 3)) t := by
  unfold traceAction model
  rw [← Matrix.exp_conjTranspose,← Matrix.exp_conjTranspose]
  simp only [Matrix.conjTranspose_smul,algebraElement_skewHermitian,star_trivial]
  unfold SU2FourWordVariation.action SU2FourWordVariation.path
    SU2NullPlaquetteWord.threePath SU2OrderedLinkHessian.matrixPath wilson
  simp only [smul_neg]

theorem trace_model_first_zero (v : Fin 4 → Fin 3 → ℝ) :
    deriv (traceAction ∘ model v) 0=0 := by
  have he : traceAction ∘ model v=SU2FourWordVariation.action (algebraElement (v 0))
      (algebraElement (v 1)) (-algebraElement (v 2)) (-algebraElement (v 3)) :=
    funext (trace_model v)
  rw [he,(SU2FourWordVariation.action_hasDerivAt _ _ _ _ 0).deriv,signed_first_zero]

theorem trace_model_second_zero (v : Fin 4 → Fin 3 → ℝ) :
    deriv (deriv (traceAction ∘ model v)) 0=lengthSq (v 0+v 1-v 2-v 3)/4 := by
  have he : traceAction ∘ model v=SU2FourWordVariation.action (algebraElement (v 0))
      (algebraElement (v 1)) (-algebraElement (v 2)) (-algebraElement (v 3)) :=
    funext (trace_model v)
  rw [he,signed_second_zero]

theorem trace_first_of_two_jet (P : ℝ → WordField) (v : Fin 4 → Fin 3 → ℝ)
    (hP : ContDiff ℝ 2 P) (h0 : P 0=(fun _ => 1))
    (h1 : deriv P 0=(fun i => algebraElement (v i))) : deriv (traceAction ∘ P) 0=0 := by
  have hp : (P 0,deriv P 0)=(model v 0,deriv (model v) 0) := by
    rw [h0,h1,model_zero,model_first_zero]
  have hr := ((traceAction_contDiff.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0
    (hP.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have he := ((traceAction_contDiff.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0
    ((model_contDiff v).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hj := congrArg (fun z : WordField × WordField => fderiv ℝ traceAction z.1 z.2) hp
  exact hr.deriv.trans ((hj.trans he.deriv.symm).trans (trace_model_first_zero v))

theorem trace_second_of_two_jet (P : ℝ → WordField) (v : Fin 4 → Fin 3 → ℝ)
    (hP : ContDiff ℝ 2 P) (h0 : P 0=(fun _ => 1))
    (h1 : deriv P 0=(fun i => algebraElement (v i)))
    (h2 : deriv (deriv P) 0=(fun i => (algebraElement (v i))^2)) :
    deriv (deriv (traceAction ∘ P)) 0=lengthSq (v 0+v 1-v 2-v 3)/4 := by
  have hp : (P 0,deriv P 0,deriv (deriv P) 0)=
      (model v 0,deriv (model v) 0,deriv (deriv (model v)) 0) := by
    rw [h0,h1,h2,model_zero,model_first_zero,model_second_zero]
  have hr := iteratedDeriv_vcomp_two traceAction_contDiff.contDiffAt hP.contDiffAt (x := (0 : ℝ))
  have he := iteratedDeriv_vcomp_two traceAction_contDiff.contDiffAt (model_contDiff v).contDiffAt (x := (0 : ℝ))
  have hj := congrArg (fun z : WordField × WordField × WordField =>
    iteratedFDeriv ℝ 2 traceAction z.1 (fun _ : Fin 2 => z.2.1)+fderiv ℝ traceAction z.1 z.2.2) hp
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hr he
  dsimp only at hj
  exact hr.trans ((hj.trans he.symm).trans (trace_model_second_zero v))

theorem trace_component_jets (P : ℝ → WordField) (v : Fin 4 → Fin 3 → ℝ)
    (hP : ∀ i,ContDiff ℝ 2 (fun t : ℝ => P t i))
    (h0 : ∀ i,P 0 i=1)
    (h1 : ∀ i,deriv (fun t : ℝ => P t i) 0=algebraElement (v i))
    (h2 : ∀ i,deriv (deriv (fun t : ℝ => P t i)) 0=(algebraElement (v i))^2) :
    ContDiff ℝ 2 (traceAction ∘ P) ∧ deriv (traceAction ∘ P) 0=0 ∧
      deriv (deriv (traceAction ∘ P)) 0=lengthSq (v 0+v 1-v 2-v 3)/4 := by
  have hp : ContDiff ℝ 2 P := contDiff_pi.mpr hP
  have hd : deriv P=(fun t i => deriv (fun u : ℝ => P u i) t) := by
    funext t
    convert! deriv_pi (fun i => ((hP i).differentiable (by norm_num)).differentiableAt) using 1
  have hd0 : deriv P 0=(fun i => algebraElement (v i)) := by
    rw [hd]
    exact funext h1
  have hd2 : deriv (deriv P) 0=(fun i => (algebraElement (v i))^2) := by
    rw [hd]
    calc
      _ = (fun i => deriv (deriv (fun u : ℝ => P u i)) 0) := by
        convert! deriv_pi (fun i => (hP i).differentiable_deriv_two.differentiableAt) using 1
      _ = _ := funext h2
  exact ⟨traceAction_contDiff.comp hp,trace_first_of_two_jet P v hp (funext h0) hd0,
    trace_second_of_two_jet P v hp (funext h0) hd0 hd2⟩

end OperatorDerivativeRewrite.Foundation.SU2FourCurveJetTransfer
