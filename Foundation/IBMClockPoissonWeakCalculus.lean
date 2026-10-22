import Foundation.IBMNativeWeakGeneratorChain

/-! Concrete nonconstant original-generator observables from the actual clock channel. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockPoissonWeakCalculus
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMClockLinearDivergence
open IBMIntrinsicPoisson IBMIntrinsicPoincare IBMNativeWeakGeneratorChain

def target (T : ℝ≥0) : IntrinsicSpace := IBMQuadraticClockMartingale.terminal T

theorem target_mean (T : ℝ≥0) : mean (target T) = 0 := by
  have h0 := IBMCenteredSourceRepresentation.divergence_mean_zero
    ⟨nativeField (timeDirection T) (timeDirection T),native_mem _ _⟩
  rw [native_value] at h0
  rw [mean,jointOne_eq_old_one,IBMGlobalVacuum.one_inner_mean]
  exact h0

def centeredTarget (T : ℝ≥0) : centered := ⟨target T,(centered_mem _).mpr (target_mean T)⟩

def potential (T : ℝ≥0) : jointDerivative.domain := solutionElement (centeredTarget T)

theorem potential_graph (T : ℝ≥0) :
    (jointDerivative (potential T),target T) ∈ jointDivergence.graph :=
  poisson_graph (centeredTarget T)

theorem target_ne_zero (T : ℝ≥0) (hT : 0 < T) : target T ≠ 0 := output_ne_zero T hT

theorem potential_gradient_ne_zero (T : ℝ≥0) (hT : 0 < T) :
    jointDerivative (potential T) ≠ 0 := by
  intro hz
  have hg := potential_graph T
  have hm := LinearPMap.mem_domain_of_mem_graph hg
  have hv : jointDivergence ⟨jointDerivative (potential T),hm⟩ = target T :=
    ((jointDivergence.image_iff hm).mpr hg).symm
  have hu : (⟨jointDerivative (potential T),hm⟩ : jointDivergence.domain) = 0 := Subtype.ext hz
  have hzero : jointDivergence (0 : jointDivergence.domain) = 0 := jointDivergence.map_zero
  rw [hu,hzero] at hv
  exact target_ne_zero T hT hv.symm

theorem potential_not_constant (T : ℝ≥0) (hT : 0 < T) (c : ℝ) :
    (potential T : IntrinsicSpace) ≠ c • IBMCenteredSourceRepresentation.intrinsicOne := by
  intro hc
  have he : potential T = c • oneElement := Subtype.ext hc
  have hd := potential_gradient_ne_zero T hT
  rw [he,jointDerivative.map_smul,one_derivative,smul_zero] at hd
  exact hd rfl

theorem actual_potential_sine_weak (T : ℝ≥0) :
    WeakChainResult (potential T) (target T) Real.sin Real.cos (fun z => -Real.sin z) :=
  poisson_sine_weak (centeredTarget T)

end OperatorDerivativeRewrite.Foundation.IBMClockPoissonWeakCalculus
