import Foundation.SU2WilsonConvolution
import Foundation.SU2OpenLinkGaugeObstruction

/-! A joint holonomy-trace bound. Commuting holonomies cannot make all three
characters vanish, even though either individual winding trace can vanish. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.SU2HolonomyTraceObstruction
open QuaternionSU2Representation SU2WilsonConvolution

def commutator (A B : SU2) : SU2 := A*B*A⁻¹*B⁻¹

def jointSquare (A B : SU2) : ℝ :=
  halfTrace A^2+halfTrace B^2+halfTrace (A*B)^2

theorem trace_commutator (A B : SU2) :
    halfTrace (commutator A B)=2*jointSquare A B-
      4*halfTrace A*halfTrace B*halfTrace (A*B)-1 := by
  have h1 := trace_pair (A*B) (A⁻¹*B⁻¹)
  have h2 := trace_pair (A*B*B) A
  have h3 := trace_pair (A*B) B
  have h4 := trace_pair B B
  have he1 : A*B*(A⁻¹*B⁻¹)=commutator A B := by unfold commutator; group
  have he2 : A*B*(A⁻¹*B⁻¹)⁻¹=A*B*B*A := by group
  have ht : halfTrace (A⁻¹*B⁻¹)=halfTrace (A*B) := by
    rw [← mul_inv_rev,halfTrace_inv,halfTrace_mul_comm]
  have he3 : A*B*B*A⁻¹=A*(B*B)*A⁻¹ := by group
  have he4 : A*B*B⁻¹=A := by group
  have he5 : B*B⁻¹=(1 : SU2) := by group
  rw [he1,he2,ht] at h1
  rw [he3,halfTrace_conjugate] at h2
  rw [he4] at h3
  rw [he5,SU2OpenLinkGaugeObstruction.halfTrace_one] at h4
  have h5 := congrArg (fun x : ℝ => 2*halfTrace A*x) h3
  unfold jointSquare
  nlinarith [h5]

theorem joint_lower (A B : SU2) :
    (1+halfTrace (commutator A B))/4 ≤ jointSquare A B := by
  have hc := abs_le.mp (halfTrace_bound (A*B))
  have hc2 : halfTrace (A*B)^2 ≤ 1 := by nlinarith
  have h := trace_commutator A B
  unfold jointSquare at *
  nlinarith [sq_nonneg (halfTrace A+halfTrace B*halfTrace (A*B)),
    mul_nonneg (sq_nonneg (halfTrace B)) (sub_nonneg.mpr hc2),
    sq_nonneg (halfTrace (A*B))]

theorem commuting_joint_lower (A B : SU2) (h : A*B=B*A) :
    (1/2 : ℝ) ≤ jointSquare A B := by
  have he : commutator A B=1 := by unfold commutator; rw [h]; group
  have hb := joint_lower A B
  rw [he,SU2OpenLinkGaugeObstruction.halfTrace_one] at hb
  linarith

theorem commuting_not_all_zero (A B : SU2) (h : A*B=B*A) :
    ¬ (halfTrace A=0 ∧ halfTrace B=0 ∧ halfTrace (A*B)=0) := by
  intro hz
  have hl := commuting_joint_lower A B h
  simp only [jointSquare,hz.1,hz.2.1,hz.2.2,zero_pow (by decide : 2≠0),
    zero_add] at hl
  norm_num at hl

private def imaginaryI : SU2 := hom ⟨⟨0,1,0,0⟩,by
  rw [Unitary.mem_iff]
  constructor <;> norm_num [Quaternion.star_mul_self,Quaternion.self_mul_star,Quaternion.normSq_def'] <;> rfl⟩

private def imaginaryJ : SU2 := hom ⟨⟨0,0,1,0⟩,by
  rw [Unitary.mem_iff]
  constructor <;> norm_num [Quaternion.star_mul_self,Quaternion.self_mul_star,Quaternion.normSq_def'] <;> rfl⟩

theorem two_traces_can_vanish :
    ∃ A B : SU2,A*B=B*A ∧ halfTrace A=0 ∧ halfTrace B=0 ∧ halfTrace (A*B)= -1 := by
  refine ⟨imaginaryI,imaginaryI,rfl,?_,?_,?_⟩
  all_goals
    norm_num [imaginaryI,halfTrace,hom,QuaternionSU2Representation.repr,SU2TraceHessianModel.traceReal,
      Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im]

theorem noncommuting_zero_joint : ∃ A B : SU2,jointSquare A B=0 ∧ halfTrace (commutator A B)= -1 := by
  refine ⟨imaginaryI,imaginaryJ,?_,?_⟩
  · norm_num [jointSquare,imaginaryI,imaginaryJ,halfTrace,hom,QuaternionSU2Representation.repr,
      SU2TraceHessianModel.traceReal,Matrix.trace_fin_two,Matrix.mul_apply,
      Fin.sum_univ_two,Complex.mul_re,Complex.mul_im]
  · have h := trace_commutator imaginaryI imaginaryJ
    have ha : halfTrace imaginaryI=0 := by norm_num [imaginaryI,halfTrace,hom,QuaternionSU2Representation.repr,
      SU2TraceHessianModel.traceReal,Matrix.trace_fin_two]
    have hb : halfTrace imaginaryJ=0 := by norm_num [imaginaryJ,halfTrace,hom,QuaternionSU2Representation.repr,
      SU2TraceHessianModel.traceReal,Matrix.trace_fin_two]
    have hc : jointSquare imaginaryI imaginaryJ=0 := by
      norm_num [jointSquare,imaginaryI,imaginaryJ,halfTrace,hom,QuaternionSU2Representation.repr,
        SU2TraceHessianModel.traceReal,Matrix.trace_fin_two,Matrix.mul_apply,
        Fin.sum_univ_two,Complex.mul_re,Complex.mul_im]
    rw [ha,hb,hc] at h
    simpa using h

end OperatorDerivativeRewrite.Foundation.SU2HolonomyTraceObstruction
