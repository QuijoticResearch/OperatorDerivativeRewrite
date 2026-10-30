import Foundation.SU2FourCurveJetTransfer

/-! Four-link trace second variation for arbitrary skew-Hermitian matrix velocities.
This permits the actual free-root conjugation without postulating Pauli coordinates. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2MatrixJetTransfer
open SU2TraceHessianModel SU2MatrixExponentialBridge SU2ProductCurveHessian
open SU2FourWordVariation SU2FourCurveJetTransfer

private def model (B : WordField) (t : ℝ) : WordField := fun i => NormedSpace.exp (t • B i)

private theorem model_contDiff (B : WordField) : ContDiff ℝ 2 (model B) :=
  contDiff_pi.mpr (fun i => exponential_contDiff (B i))

private theorem model_zero (B : WordField) : model B 0=(fun _ => 1) := by
  funext i
  simp [model]

private theorem model_first (B : WordField) (t : ℝ) :
    deriv (model B) t=(fun i => B i*NormedSpace.exp (t • B i)) := by
  have hh := deriv_pi (fun i : Fin 4 =>
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (B i) t).differentiableAt)
  calc
    _ = (fun i => deriv (fun u : ℝ => NormedSpace.exp (u • B i)) t) := by convert! hh using 1
    _ = _ := funext (fun i => (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (B i) t).deriv)

private theorem model_first_zero (B : WordField) : deriv (model B) 0=B := by
  rw [model_first]
  simp only [zero_smul,NormedSpace.exp_zero,mul_one]

private theorem model_second_zero (B : WordField) :
    deriv (deriv (model B)) 0=(fun i => (B i)^2) := by
  rw [show deriv (model B)=(fun t i => B i*NormedSpace.exp (t • B i)) from funext (model_first B)]
  have hh := deriv_pi (fun i : Fin 4 =>
    ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) (B i) (0 : ℝ)).const_mul (B i)).differentiableAt)
  calc
    _ = (fun i => deriv (fun t : ℝ => B i*NormedSpace.exp (t • B i)) 0) := by convert! hh using 1
    _ = _ := by
      funext i
      convert! ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) (B i) (0 : ℝ)).const_mul (B i)).deriv using 1 <;>
        simp only [zero_smul,NormedSpace.exp_zero,mul_one,pow_two]

private theorem trace_model (B : WordField) (hB : ∀ i,(B i)ᴴ= -B i) (t : ℝ) :
    traceAction (model B t)=action (B 0) (B 1) (-B 2) (-B 3) t := by
  unfold traceAction model
  rw [← Matrix.exp_conjTranspose,← Matrix.exp_conjTranspose]
  simp only [Matrix.conjTranspose_smul,hB,star_trivial]
  unfold action SU2FourWordVariation.path SU2NullPlaquetteWord.threePath
    SU2OrderedLinkHessian.matrixPath wilson
  simp only [smul_neg]

private theorem trace_model_second (B : WordField) (hB : ∀ i,(B i)ᴴ= -B i) :
    deriv (deriv (traceAction ∘ model B)) 0= -traceReal ((B 0+B 1-B 2-B 3)^2)/2 := by
  have he : traceAction ∘ model B=action (B 0) (B 1) (-B 2) (-B 3) := funext (trace_model B hB)
  rw [he,action_second_zero]
  simp only [sub_eq_add_neg]

/-- Exact second derivative from actual component jets, including conjugated velocities. -/
theorem trace_second (P : ℝ → WordField) (B : WordField)
    (hB : ∀ i,(B i)ᴴ= -B i)
    (hP : ∀ i,ContDiff ℝ 2 (fun t : ℝ => P t i))
    (h0 : ∀ i,P 0 i=1)
    (h1 : ∀ i,deriv (fun t : ℝ => P t i) 0=B i)
    (h2 : ∀ i,deriv (deriv (fun t : ℝ => P t i)) 0=(B i)^2) :
    deriv (deriv (traceAction ∘ P)) 0= -traceReal ((B 0+B 1-B 2-B 3)^2)/2 := by
  have hp : ContDiff ℝ 2 P := contDiff_pi.mpr hP
  have hd : deriv P=(fun t i => deriv (fun u : ℝ => P u i) t) := by
    funext t
    convert! deriv_pi (fun i => ((hP i).differentiable (by norm_num)).differentiableAt) using 1
  have hd0 : deriv P 0=B := by rw [hd]; exact funext h1
  have hd2 : deriv (deriv P) 0=(fun i => (B i)^2) := by
    rw [hd]
    calc
      _ = (fun i => deriv (deriv (fun u : ℝ => P u i)) 0) := by
        convert! deriv_pi (fun i => (hP i).differentiable_deriv_two.differentiableAt) using 1
      _ = _ := funext h2
  have hjets : (P 0,deriv P 0,deriv (deriv P) 0)=
      (model B 0,deriv (model B) 0,deriv (deriv (model B)) 0) := by
    rw [funext h0,hd0,hd2,model_zero,model_first_zero,model_second_zero]
  have hr := iteratedDeriv_vcomp_two traceAction_contDiff.contDiffAt hp.contDiffAt (x := (0 : ℝ))
  have he := iteratedDeriv_vcomp_two traceAction_contDiff.contDiffAt (model_contDiff B).contDiffAt (x := (0 : ℝ))
  have hj := congrArg (fun z : WordField × WordField × WordField =>
    iteratedFDeriv ℝ 2 traceAction z.1 (fun _ : Fin 2 => z.2.1)+fderiv ℝ traceAction z.1 z.2.2) hjets
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hr he
  dsimp only at hj
  exact hr.trans ((hj.trans he.symm).trans (trace_model_second B hB))

end OperatorDerivativeRewrite.Foundation.SU2MatrixJetTransfer
