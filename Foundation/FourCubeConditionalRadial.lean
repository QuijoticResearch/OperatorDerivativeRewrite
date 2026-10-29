import Foundation.FourCubeConditionalAction
import Foundation.SU2StapleTiltLaw

/-! Exact five-staple polar reduction needed for the conditional cell test. -/
noncomputable section
open scoped Quaternion Matrix
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.FourCubeConditionalRadial
open QuaternionSU2Representation SU2TraceHessianModel

def fiveStaples (A : SU2) : Fin 5 → SU2 := ![1,1,1,1,A]
def fiveRaw (A : SU2) : ℍ := SU2StaplePolar.quaternionSum Finset.univ (fiveStaples A)
def stapleRadius (A : SU2) : ℝ := ‖fiveRaw A‖
def stapleOrientation (A : SU2) : SU2 := SU2StaplePolar.orientation (fiveRaw A)

theorem fiveRaw_eq (A : SU2) : fiveRaw A=(⟨4,0,0,0⟩ : ℍ)+recover (A : M2) := by
  ext <;> norm_num [fiveRaw,SU2StaplePolar.quaternionSum,fiveStaples,Fin.sum_univ_succ,recover] <;> ring

private theorem recover_normSq (A : SU2) : Quaternion.normSq (recover (A : M2))=1 := by
  rw [Quaternion.normSq_eq_norm_mul_self,CStarRing.norm_of_mem_unitary (recover_mem A)]
  norm_num

private theorem recover_real (A : SU2) : (recover (A : M2)).re=halfTrace A := by
  have h := repr_halfTrace (recover (A : M2))
  rw [repr_recover _ A.property] at h
  exact h.symm

theorem stapleRadius_sq (A : SU2) : stapleRadius A^2=17+8*halfTrace A := by
  have hq := recover_normSq A
  have hn : Quaternion.normSq ((⟨4,0,0,0⟩ : ℍ)+recover (A : M2))=17+8*(recover (A : M2)).re := by
    norm_num [Quaternion.normSq_def'] at hq ⊢
    nlinarith
  unfold stapleRadius
  rw [pow_two,← Quaternion.normSq_eq_norm_mul_self,fiveRaw_eq,hn,recover_real]

theorem stapleRadius_bounds (A : SU2) : 3 ≤ stapleRadius A ∧ stapleRadius A ≤ 5 := by
  have h := abs_le.mp (halfTrace_bound A)
  have hn : 0 ≤ stapleRadius A := norm_nonneg _
  have hs := stapleRadius_sq A
  constructor <;> nlinarith

theorem stapleRadius_sqrt (A : SU2) : stapleRadius A=Real.sqrt (17+8*halfTrace A) := by
  rw [← stapleRadius_sq]
  symm
  exact Real.sqrt_sq (norm_nonneg _)

theorem five_trace (A U : SU2) :
    4*halfTrace U+halfTrace (U*A)=stapleRadius A*halfTrace (stapleOrientation A*U) := by
  have ht := SU2StaplePolar.trace_tilt Finset.univ (fiveStaples A) U
  have hl : traceReal ((U : M2)*SU2StaplePolar.staple Finset.univ (fiveStaples A))/2=
      4*halfTrace U+halfTrace (U*A) := by
    norm_num [SU2StaplePolar.staple,fiveStaples,Fin.sum_univ_succ,Matrix.mul_add,
      traceReal,Matrix.trace_add,halfTrace]
    ring
  rw [hl] at ht
  exact ht

theorem radial_integral (β : ℝ) (A : SU2) :
    (∫ U, Real.exp (β*(4*halfTrace U+halfTrace (U*A))) ∂law)=mgf halfTrace law (β*stapleRadius A) := by
  simp_rw [five_trace]
  have h := SU2StapleTiltLaw.partition_axis law (stapleOrientation A) (β*stapleRadius A)
  simpa only [BoundedExponentialTiltResponse.partition,BoundedExponentialTiltResponse.weighted,
    one_mul,SU2StapleTiltLaw.axis,mgf,mul_assoc] using h

end OperatorDerivativeRewrite.Foundation.FourCubeConditionalRadial
