import Foundation.FourCubePinnedSecondVariation
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! A finite polynomial ambient realization of the actual72-face action.
Used only to transfer actual matrix jets; no noncompact gauge measure is asserted. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeAmbientAction
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge SU2ProductCurveHessian
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open FourCubeHaarParity FourCubeHaarChannels FourCubeIntegratedCubic
open FourCubePinnedHaar FourCubePinnedCoercivity
attribute [local irreducible] edges upperFaces innerFaces

abbrev MatrixField := Interior → M2

def adjointLinear : M2 →ₗ[ℝ] M2 where
  toFun := Matrix.conjTranspose
  map_add' := Matrix.conjTranspose_add
  map_smul' := by intro r M; simp [Matrix.conjTranspose_smul]

def adjointCLM : M2 →L[ℝ] M2 := adjointLinear.toContinuousLinearMap

theorem adjoint_contDiff : ContDiff ℝ 2 (fun M : M2 => Mᴴ) := adjointCLM.contDiff

def core (Z : MatrixField) (e : EdgeData) : M2 :=
  if h : e∈edges then Z ⟨e,h⟩ else 1

def face (Z : MatrixField) (p : FaceData) : ℝ :=
  1-traceReal (core Z (p.1,p.2.1)*core Z (shifted p.1 p.2.1,p.2.2)*
    (core Z (shifted p.1 p.2.2,p.2.1))ᴴ*(core Z (p.1,p.2.2))ᴴ)/2

def action (Z : MatrixField) : ℝ :=
  (∑ p∈innerFaces,face Z p)+∑ p : Upper,(1-traceReal (Z (ribbonInterior p))/2)

theorem core_contDiff (e : EdgeData) : ContDiff ℝ 2 (fun Z : MatrixField => core Z e) := by
  by_cases he : e∈edges
  · simpa only [core,dif_pos he] using (_root_.contDiff_apply ℝ M2 (⟨e,he⟩ : Interior))
  · simpa only [core,dif_neg he] using (contDiff_const : ContDiff ℝ 2 (fun _ : MatrixField => (1 : M2)))

theorem face_contDiff (p : FaceData) : ContDiff ℝ 2 (fun Z : MatrixField => face Z p) := by
  have h0 := core_contDiff (p.1,p.2.1)
  have h1 := core_contDiff (shifted p.1 p.2.1,p.2.2)
  have h2 := adjoint_contDiff.comp (core_contDiff (shifted p.1 p.2.2,p.2.1))
  have h3 := adjoint_contDiff.comp (core_contDiff (p.1,p.2.2))
  exact contDiff_const.sub ((realTraceCLM.contDiff.comp (((h0.mul h1).mul h2).mul h3)).div_const 2)

theorem action_contDiff : ContDiff ℝ 2 action := by
  exact (ContDiff.sum (fun p _ => face_contDiff p)).add
    (ContDiff.sum (fun p _ => contDiff_const.sub
      ((realTraceCLM.contDiff.comp (_root_.contDiff_apply ℝ M2 (ribbonInterior p))).div_const 2)))

theorem core_actual (s : InteriorState) (e : EdgeData) :
    core (fun k => (s k : M2)) e=(coreField s e : M2) := by
  by_cases he : e∈edges
  · simp [core,coreField,he]
  · simp [core,coreField,he]

theorem face_actual (s : InteriorState) (p : FaceData) :
    face (fun k => (s k : M2)) p=FourCubeWilsonCubic.faceAction (coreField s) p := by
  unfold face FourCubeWilsonCubic.faceAction halfTrace
  simp only [core_actual]
  rfl

theorem action_actual (s : InteriorState) : action (fun k => (s k : M2))=vacuumAction s := by
  rw [vacuum_decomposition]
  simp only [action,internalAction,FourCubeWilsonCubic.innerAction,face_actual,
    ribbonEnergy,defect,halfTrace]

end OperatorDerivativeRewrite.Foundation.FourCubeAmbientAction
