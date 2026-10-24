import Foundation.IBMSchwartzNativeCauchyCriterion
import Foundation.NormalizedSignedScoreCounterexample

/-! A concrete Schwartz counterexample: g(x)=x exp(-x^2), shift zero.
The actual native integral and correction are both non-Cauchy although their
compensated sum converges in actual joint L2 to g(IBM_T). -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeCounterexample
open InfiniteGaussian IBMIntrinsicOperators IBMTimeAveragedObservable
open NormalizedSignedScoreCounterexample IBMSchwartzNativeJointIto

theorem odd_jet_zero : IBMCorrectionStein.jet oddPart 1 0 = 1 := by
  change deriv (fun x : ℝ => oddPart x) 0 = 1
  have he : (fun x : ℝ => oddPart x) =
      fun x : ℝ => x*GaussianSchwartzKernel.gaussian x := by
    funext x
    exact odd_apply x
  rw [he]
  simpa [Pi.mul_def, id_eq, GaussianSchwartzKernel.gaussian] using
    ((hasDerivAt_id (0 : ℝ)).mul (GaussianSchwartzKernel.gaussian_hasDerivAt 0)).deriv

theorem actual_integral_not_cauchy (T : ℝ≥0) (hT : 0 < T) :
    ¬ CauchySeq (fun n => clockDerivative.adjoint
      ⟨field oddPart 0 n T,clock_mem oddPart 0 n T⟩) :=
  IBMSchwartzNativeCauchyCriterion.integral_not_cauchy oddPart 0 T hT
    (by rw [odd_jet_zero]; norm_num)

theorem actual_correction_not_cauchy (T : ℝ≥0) (hT : 0 < T) :
    ¬ CauchySeq (fun n => correction oddPart 0 n T) :=
  IBMSchwartzNativeCauchyCriterion.correction_not_cauchy oddPart 0 T hT
    (by rw [odd_jet_zero]; norm_num)

theorem actual_integral_no_L2_limit (T : ℝ≥0) (hT : 0 < T) (v : JointL2) :
    ¬ Tendsto (fun n => clockDerivative.adjoint
      ⟨field oddPart 0 n T,clock_mem oddPart 0 n T⟩) atTop (𝓝 v) :=
  fun h => actual_integral_not_cauchy T hT h.cauchySeq

theorem actual_correction_no_L2_limit (T : ℝ≥0) (hT : 0 < T) (v : JointL2) :
    ¬ Tendsto (fun n => correction oddPart 0 n T) atTop (𝓝 v) :=
  fun h => actual_correction_not_cauchy T hT h.cauchySeq

end OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeCounterexample
