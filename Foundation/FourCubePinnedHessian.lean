import Foundation.FourCubePinnedSecondVariation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Actual Frechet-Hessian diagonal of the pinned Wilson action in logarithmic coordinates. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubePinnedHessian
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge
open SU2ExponentialMembership SU2ProductCurveHessian SU2NullPlaquetteWord SU2OrderedLinkHessian
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open FourCubePinnedHaar FourCubePinnedCoercivity FourCubePinnedSecondVariation
attribute [local irreducible] edges upperFaces innerFaces

def coordinateAction (V : PinnedVelocity) : ℝ := pinnedRay V 1

private theorem coefficient_contDiff (e : EdgeData) (a : Fin 3) :
    ContDiff ℝ 2 (fun V : PinnedVelocity => extended (liftVelocity V) e a) := by
  by_cases he : e∈edges
  · by_cases hp : (⟨e,he⟩ : Interior)=OneSidedPinnedInterior.pole
    · simpa [extended,extend,he,liftVelocity,OneSidedPinnedInterior.lift,hp] using
        (contDiff_const : ContDiff ℝ 2 (fun _ : PinnedVelocity => (0 : ℝ)))
    · simpa only [extended,extend,dif_pos he,liftVelocity,OneSidedPinnedInterior.lift,
        LinearMap.coe_mk,AddHom.coe_mk,dif_neg hp,Function.comp_def] using
        ((_root_.contDiff_apply ℝ ℝ a).comp (_root_.contDiff_apply ℝ (Fin 3 → ℝ) (⟨⟨e,he⟩,hp⟩ : OneSidedPinnedInterior.Free)))
  · simpa [extended,extend,he] using
      (contDiff_const : ContDiff ℝ 2 (fun _ : PinnedVelocity => (0 : ℝ)))

private theorem generator_contDiff (e : EdgeData) :
    ContDiff ℝ 2 (fun V : PinnedVelocity => algebraElement (extended (liftVelocity V) e)) := by
  unfold algebraElement
  apply ContDiff.sum
  intro a _
  exact (Complex.ofRealCLM.contDiff.comp (coefficient_contDiff e a)).smul contDiff_const

private theorem matrixExp_contDiff : ContDiff ℝ 2 (NormedSpace.exp : M2 → M2) :=
  contDiff_iff_contDiffAt.mpr (fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).contDiffAt)

private theorem face_contDiff (p : FaceData) :
    ContDiff ℝ 2 (fun V : PinnedVelocity => faceModel (liftVelocity V) p 1) := by
  have h0 := matrixExp_contDiff.comp (generator_contDiff (p.1,p.2.1))
  have h1 := matrixExp_contDiff.comp (generator_contDiff (shifted p.1 p.2.1,p.2.2))
  have h2 := matrixExp_contDiff.comp ((generator_contDiff (shifted p.1 p.2.2,p.2.1)).neg)
  have h3 := matrixExp_contDiff.comp ((generator_contDiff (p.1,p.2.2)).neg)
  have hm := ((h0.mul h1).mul h2).mul h3
  have ht := (contDiff_const (c := (1 : ℝ))).sub ((realTraceCLM.contDiff.comp hm).div_const 2)
  convert ht using 1
  funext V
  simp [faceModel,faceVectors,SU2FourWordVariation.action,SU2FourWordVariation.path,
    threePath,matrixPath,wilson,Function.comp_def,realTraceCLM_apply]
  rfl

private theorem ribbon_contDiff (p : Upper) :
    ContDiff ℝ 2 (fun V : PinnedVelocity => curve 1
      (algebraElement (liftVelocity V (ribbonInterior p))) 1) := by
  have ha : ContDiff ℝ 2 (fun V : PinnedVelocity =>
      algebraElement (liftVelocity V (ribbonInterior p))) := by
    simpa only [extended_on] using generator_contDiff (ribbonInterior p).val
  have hm := matrixExp_contDiff.comp ha
  have ht := (contDiff_const (c := (1 : ℝ))).sub ((realTraceCLM.contDiff.comp hm).div_const 2)
  convert ht using 1
  funext V
  simp [curve,wilson,Function.comp_def,realTraceCLM_apply]
  rfl

theorem coordinateAction_contDiff : ContDiff ℝ 2 coordinateAction := by
  have he : coordinateAction=(fun V : PinnedVelocity =>
      (∑ p∈innerFaces,faceModel (liftVelocity V) p 1)+
        ∑ p : Upper,curve 1 (algebraElement (liftVelocity V (ribbonInterior p))) 1) := by
    funext V
    rw [coordinateAction,pinnedRay_eq,ray_model]
  rw [he]
  exact (ContDiff.sum (fun p _ => face_contDiff p)).add
    (ContDiff.sum (fun p _ => ribbon_contDiff p))

def line (V : PinnedVelocity) : ℝ →L[ℝ] PinnedVelocity :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight V

theorem coordinateAction_line (V : PinnedVelocity) : coordinateAction ∘ line V=pinnedRay V := by
  funext t
  change pinnedAction (pinnedChart (t • V) 1)=pinnedAction (pinnedChart V t)
  congr 1
  funext e
  apply Subtype.ext
  change NormedSpace.exp (1 • algebraElement (t • V e))=
    NormedSpace.exp (t • algebraElement (V e))
  rw [one_smul,algebraElement_smul]

theorem hessian_diagonal_ray (V : PinnedVelocity) :
    iteratedFDeriv ℝ 2 coordinateAction 0 (fun _ : Fin 2 => V)=
      deriv (deriv (pinnedRay V)) 0 := by
  have hh := (line V).iteratedFDeriv_comp_right coordinateAction_contDiff (0 : ℝ)
    (i := 2) (by norm_num)
  rw [coordinateAction_line] at hh
  have he := congrArg (fun m : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ) ℝ =>
    m (fun _ => 1)) hh
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at he
  simp only [Finset.prod_const_one,one_smul,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    line,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,zero_smul] at he
  simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using he.symm

theorem hessian_diagonal_gram (V : PinnedVelocity) :
    iteratedFDeriv ℝ 2 coordinateAction 0 (fun _ : Fin 2 => V)=
      (∑ a : Fin 3,dotProduct (fun e => V e a)
        (OneSidedPinnedInterior.localGram.mulVec (fun e => V e a)))/4 := by
  rw [hessian_diagonal_ray,pinned_second_gram]

theorem hessian_positive (V : PinnedVelocity) (hV : V ≠ 0) :
    0 < iteratedFDeriv ℝ 2 coordinateAction 0 (fun _ : Fin 2 => V) := by
  rw [hessian_diagonal_ray]
  exact pinned_second_positive V hV

end OperatorDerivativeRewrite.Foundation.FourCubePinnedHessian
