import Foundation.GaussianClockNativeDomain
import Foundation.IBMClockFractionalCalculus
import Foundation.IBMIntrinsicOperators

/-! Genuine original joint Gaussian CLOCK derivatives of regularized actual IBM
endpoints: exact sharp domain threshold, actual vector values, energy, native
adjoint IBP and strong finite-chaos graph approximation. Intrinsic adapted
observable membership and physical Ito identification are separate obligations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockNativeSmoothing
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
open InfiniteGaussian GaussianClockValueOperators GaussianClockNativeDomain
open IBMClockFractionalDomain IBMClockFractionalCalculus

theorem clockUnitary_jointRealization (f : Field) :
    IBMIntrinsicOperators.clockUnitary (IBMTimeAveragedObservable.jointRealization f) =
      ProductL2Curry.flip gaussianProduct gaussianProduct f := rfl

theorem joint_clock_domain (f : Field) :
    IBMTimeAveragedObservable.jointRealization f ∈ IBMIntrinsicOperators.clockDerivative.domain ↔
      f ∈ (bessel 1).domain := by
  change IBMIntrinsicOperators.clockUnitary (IBMTimeAveragedObservable.jointRealization f) ∈
    IBMClockAverageGraph.clockDerivative.domain ↔ _
  rw [clockUnitary_jointRealization]
  exact (bessel_native_domain f).symm

theorem joint_clock_energy (f : Field) (hf : f ∈ (bessel 1).domain) :
    ‖bessel 1 ⟨f,hf⟩‖^2 = ‖IBMTimeAveragedObservable.jointRealization f‖^2+
      ‖IBMIntrinsicOperators.clockDerivative ⟨IBMTimeAveragedObservable.jointRealization f,
        (joint_clock_domain f).2 hf⟩‖^2 := by
  have hv : IBMIntrinsicOperators.clockDerivative ⟨IBMTimeAveragedObservable.jointRealization f,
      (joint_clock_domain f).2 hf⟩ =
      IBMClockAverageGraph.clockDerivative ⟨ProductL2Curry.flip gaussianProduct gaussianProduct f,
        (bessel_native_domain f).1 hf⟩ := by
    change IBMFiniteAverageCore.partialDerivative
      ⟨IBMIntrinsicOperators.clockUnitary (IBMTimeAveragedObservable.jointRealization f),_⟩ = _
    rfl
  rw [hv,IBMTimeAveragedObservable.jointRealization.norm_map]
  exact bessel_native_energy f hf

def regularizedEndpoint (β : ℝ) (hβ : 0 ≤ β) (T : ℝ≥0) (hT : 0 < T) : Field :=
  bessel (-2*β) ⟨IBMRandomTimeHilbert.randomSourceL2 T,
    (actual_bessel_domain (-2*β) T hT).2 (by linarith)⟩

theorem actual_native_smoothing_threshold (β : ℝ) (hβ : 0 ≤ β) (T : ℝ≥0) (hT : 0 < T) :
    IBMTimeAveragedObservable.jointRealization (regularizedEndpoint β hβ T hT)
      ∈ IBMIntrinsicOperators.clockDerivative.domain ↔ 1/4 < β := by
  rw [joint_clock_domain]
  exact actual_smoothing_threshold β hβ T hT

theorem actual_unsmoothed_not_clock_domain (T : ℝ≥0) (hT : 0 < T) :
    IBMTimeAveragedObservable.jointRealization (IBMRandomTimeHilbert.randomSourceL2 T)
      ∉ IBMIntrinsicOperators.clockDerivative.domain := by
  rw [joint_clock_domain,actual_bessel_domain 1 T hT]
  norm_num



def regularizedGradient (β : ℝ) (hβ : 0 ≤ β) (T : ℝ≥0) (hT : 0 < T) (hb : 1/4 < β) :
    IBMIntrinsicOperators.FieldSpace :=
  IBMIntrinsicOperators.clockDerivative
    ⟨IBMTimeAveragedObservable.jointRealization (regularizedEndpoint β hβ T hT),
      (actual_native_smoothing_threshold β hβ T hT).2 hb⟩

theorem regularized_gradient_graph (β : ℝ) (hβ : 0 ≤ β) (T : ℝ≥0) (hT : 0 < T) (hb : 1/4 < β) :
    (IBMTimeAveragedObservable.jointRealization (regularizedEndpoint β hβ T hT),
      regularizedGradient β hβ T hT hb) ∈ IBMIntrinsicOperators.clockDerivative.graph :=
  IBMIntrinsicOperators.clockDerivative.mem_graph
    ⟨_,(actual_native_smoothing_threshold β hβ T hT).2 hb⟩

theorem regularized_gradient_energy (β : ℝ) (hβ : 0 ≤ β) (T : ℝ≥0) (hT : 0 < T) (hb : 1/4 < β) :
    ‖bessel 1 ⟨regularizedEndpoint β hβ T hT,
      (joint_clock_domain _).1 ((actual_native_smoothing_threshold β hβ T hT).2 hb)⟩‖^2 =
      ‖IBMTimeAveragedObservable.jointRealization (regularizedEndpoint β hβ T hT)‖^2+
        ‖regularizedGradient β hβ T hT hb‖^2 :=
  joint_clock_energy _ _

theorem regularized_ibp (β : ℝ) (hβ : 0 ≤ β) (T : ℝ≥0) (hT : 0 < T) (hb : 1/4 < β)
    (u : IBMIntrinsicOperators.clockDerivative.adjoint.domain) :
    inner ℝ (regularizedGradient β hβ T hT hb) (u:IBMIntrinsicOperators.FieldSpace) =
      inner ℝ (IBMTimeAveragedObservable.jointRealization (regularizedEndpoint β hβ T hT))
        (IBMIntrinsicOperators.clockDerivative.adjoint u) := by
  have h := IBMIntrinsicOperators.clockDerivative.adjoint_isFormalAdjoint
    IBMIntrinsicOperators.clockDerivative_dense u
    ⟨_,(actual_native_smoothing_threshold β hβ T hT).2 hb⟩
  calc
    _ = inner ℝ (u:IBMIntrinsicOperators.FieldSpace) (regularizedGradient β hβ T hT hb) := real_inner_comm _ _
    _ = inner ℝ (IBMIntrinsicOperators.clockDerivative.adjoint u)
      (IBMTimeAveragedObservable.jointRealization (regularizedEndpoint β hβ T hT)) := h.symm
    _ = _ := real_inner_comm _ _



theorem regularized_graph_approximation (β : ℝ) (hβ : 0 ≤ β) (T : ℝ≥0) (hT : 0 < T) (hb : 1/4 < β) :
    Tendsto (fun N =>
      ((GaussianNumberSectors.truncation N).compLpL 2 gaussianProduct
          (ProductL2Curry.flip gaussianProduct gaussianProduct (regularizedEndpoint β hβ T hT)),
        (GaussianNumberSectors.gradientTruncation N).compLpL 2 gaussianProduct
          (ProductL2Curry.flip gaussianProduct gaussianProduct (regularizedEndpoint β hβ T hT))))
      atTop (𝓝 (ProductL2Curry.flip gaussianProduct gaussianProduct (regularizedEndpoint β hβ T hT),
        regularizedGradient β hβ T hT hb)) := by
  have hg : (IBMIntrinsicOperators.clockUnitary
      (IBMTimeAveragedObservable.jointRealization (regularizedEndpoint β hβ T hT)),
      regularizedGradient β hβ T hT hb) ∈ IBMClockAverageGraph.clockDerivative.graph :=
    (AdjointUnitaryTransport.mem_pullback_graph IBMIntrinsicOperators.clockUnitary
      IBMFiniteAverageCore.partialDerivative _ _).1 (regularized_gradient_graph β hβ T hT hb)
  rw [clockUnitary_jointRealization] at hg
  exact native_graph_truncation_tendsto _ _ hg

end OperatorDerivativeRewrite.Foundation.IBMClockNativeSmoothing
