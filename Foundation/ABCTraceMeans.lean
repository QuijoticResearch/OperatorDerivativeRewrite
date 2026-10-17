import Foundation.ABCNavierStokesFlow
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.ABCTraceMeans
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality RealFiniteFourierAnalysis RealPeriodicViscousCancellation
  ABCFourierProfile BeltramiAdvection RealBeltramiEuler ABCNavierStokesFlow
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem abc_kinetic_gradient : gradient derivative (kinetic (𝕜 := ℂ) abc)=
    ![cosine 0*cosine 2-sine 0*sine 1,
      cosine 1*cosine 0-sine 1*sine 2,
      cosine 2*cosine 1-sine 2*sine 0] := by
  rw [gradient_kinetic]
  apply funext
  intro i
  fin_cases i <;>
    norm_num [Matrix.mulVec,Matrix.transpose_apply,dotProduct,jacobian,abc,map_add,
      derivative_sine,derivative_cosine,Fin.sum_univ_succ] <;> ring

theorem abc_gradient_trace : constantTrace
    (dotProduct (gradient derivative (kinetic (𝕜 := ℂ) abc))
      (gradient derivative (kinetic (𝕜 := ℂ) abc)))=3/2 := by
  rw [abc_kinetic_gradient]
  simp only [dotProduct,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Finset.sum_empty,add_zero,map_add]
  norm_num [cosine,sine,add_mul,mul_add,sub_mul,mul_sub,neg_mul,mul_neg,
    AddMonoidAlgebra.single_mul_single,map_add,map_sub,map_neg,constantTrace_apply,
    AddMonoidAlgebra.coeff_single,Finsupp.single_apply,frequency,funext_iff,
    Fin.forall_fin_succ,Pi.single_apply]

  ring_nf
  norm_num [pow_succ,Complex.I_mul_I]

theorem abc_amplification_trace : constantTrace
    (dotProduct (Matrix.mulVec (strain derivative abc) abc)
      (Matrix.mulVec (strain derivative abc) abc))=3/2 := by
  rw [beltrami_strain derivative abc abc_curl,abc_gradient_trace]

theorem abc_pressure_trace : constantTrace
    (linearContraction derivative abc (gradient derivative (-kinetic (𝕜 := ℂ) abc)))=3/2 := by
  rw [beltrami_pressure_trace derivative constantTrace constantTrace_derivative abc
    abc_curl abc_divergence,abc_gradient_trace]

theorem abc_stretching_trace : constantTrace
    (dotProduct (Matrix.mulVec (strain derivative abc) abc) abc)=0 :=
  beltrami_stretching_trace derivative constantTrace constantTrace_derivative abc
    abc_curl abc_divergence

end OperatorDerivativeRewrite.Foundation.ABCTraceMeans
