import Foundation.CubeMixedForm

/-! Actual root adjoint coordinates through the existing quaternion representation. -/
noncomputable section
open scoped Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2RootAdjoint
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2TraceHessianModel
open SU2MatrixExponentialBridge SU2HemisphereJets ChristoffelSkewCancellation

private def pure (y : Triple) : ℍ := ⟨0,y 0,y 1,y 2⟩
private def conjugated (c : SU2) (y : Triple) : ℍ :=
  recover (c : M2)*pure y*star (recover (c : M2))

def rotate (c : SU2) (y : Triple) : Triple :=
  ![(conjugated c y).imI,(conjugated c y).imJ,(conjugated c y).imK]

private theorem pure_rotate (c : SU2) (y : Triple) : pure (rotate c y)=conjugated c y := by
  apply Quaternion.ext <;>
    norm_num [pure,rotate,conjugated,Quaternion.re_mul,Quaternion.imI_mul,
      Quaternion.imJ_mul,Quaternion.imK_mul] <;> ring

private theorem generator_repr (y : Triple) : SU2HemisphereJets.generator y=QuaternionSU2Representation.repr (pure y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [SU2HemisphereJets.generator,frame,algebraElement,tangent,
      SU2TraceHessianModel.generator,generatorX,generatorY,generatorZ,QuaternionSU2Representation.repr,pure,
      Fin.sum_univ_three,Complex.mul_re,Complex.mul_im] <;> ring

/-- The root rotation represents EXACTLY the actual matrix conjugation. -/
theorem generator_rotate (c : SU2) (y : Triple) :
    SU2HemisphereJets.generator (rotate c y)=
      CubeMixedForm.adjointVelocity c (SU2HemisphereJets.generator y) := by
  rw [generator_repr,pure_rotate]
  unfold conjugated CubeMixedForm.adjointVelocity
  rw [repr_mul,repr_mul,repr_star,repr_recover _ c.property,generator_repr]

theorem rotate_add (c : SU2) (y z : Triple) : rotate c (y+z)=rotate c y+rotate c z := by
  ext i
  fin_cases i <;> norm_num [rotate,conjugated,pure,Quaternion.re_mul,
    Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] <;> ring

theorem rotate_smul (c : SU2) (a : ℝ) (y : Triple) : rotate c (a • y)=a • rotate c y := by
  ext i
  fin_cases i <;> norm_num [rotate,conjugated,pure,Quaternion.re_mul,
    Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] <;> ring

private theorem pure_normSq (y : Triple) : Quaternion.normSq (pure y)=sizeSq y := by
  norm_num [Quaternion.normSq_def',pure,sizeSq]

/-- The actual root adjoint preserves the Euclidean triple norm, with no new axiom. -/
theorem rotate_sizeSq (c : SU2) (y : Triple) : sizeSq (rotate c y)=sizeSq y := by
  have hn : Quaternion.normSq (recover (c : M2))=1 := by
    rw [Quaternion.normSq_eq_norm_mul_self,
      CStarRing.norm_of_mem_unitary (recover_mem c),one_mul]
  rw [← pure_normSq,pure_rotate]
  unfold conjugated
  rw [map_mul,map_mul,Quaternion.normSq_star,hn,one_mul,mul_one,pure_normSq]

end OperatorDerivativeRewrite.Foundation.SU2RootAdjoint
