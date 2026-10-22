import Foundation.IBMRightGermDeterministicIntegral
import Mathlib.Analysis.Normed.Operator.Extend

/-! An actual stochastic integral on the CLOSED time-L2 span of bounded
interval indicators. No full time-L2 density or random domain is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRightGermIntegralCompletion
open IBMTimeAveragedObservable IBMIntrinsicRightGerm
open IBMRightGermDeterministicIntegral
set_option backward.isDefEq.respectTransparency false

def domain : Submodule ℝ TimeL2 := timeDictionary.range.topologicalClosure

def embedding : (ℝ≥0 →₀ ℝ) →ₗ[ℝ] domain :=
  timeDictionary.codRestrict domain (fun a =>
    timeDictionary.range.le_topologicalClosure (LinearMap.mem_range_self _ a))

theorem embedding_dense : DenseRange embedding := by
  have hd := ((denseRange_inclusion_iff
    (subset_closure : Set.range timeDictionary ⊆ closure (Set.range timeDictionary))).2
      subset_rfl).comp (rangeFactorization_surjective.denseRange)
        (continuous_inclusion subset_closure)
  exact hd

def integral : domain →ₗᵢ[ℝ] JointL2 :=
  stochasticDictionary.extendOfIsometry embedding_dense dictionary_norm

theorem integral_dictionary (a : ℝ≥0 →₀ ℝ) :
    integral (embedding a) = stochasticDictionary a :=
  LinearMap.extendOfIsometry_eq _ _ _ _

theorem integral_dictionary_ae (a : ℝ≥0 →₀ ℝ) :
    integral (embedding a) =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => ∑ t ∈ a.support, a t * rightValue t ω) := by
  rw [integral_dictionary]
  exact stochasticDictionary_ae a

theorem integral_interval (s t : ℝ≥0) (c : ℝ) :
    integral (embedding (Finsupp.single t c - Finsupp.single s c)) =
      c • (rightLimitClass t - rightLimitClass s) := by
  rw [integral_dictionary, interval_dictionary]

theorem integral_norm (f : domain) : ‖integral f‖ = ‖(f : TimeL2)‖ := integral.norm_map f

theorem actual_integral_isometry (f : domain) :
    (∫ ω, (integral f ω) ^ 2 ∂IBMSourceLaws.jointMeasure) = ‖(f : TimeL2)‖ ^ 2 := by
  rw [← integral_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    change (integral f ω) ^ 2 = inner ℝ (integral f ω) (integral f ω)
    rw [Real.inner_apply, pow_two]

theorem integral_limit {α : Type*} {l : Filter α} (a : α → (ℝ≥0 →₀ ℝ)) (f : domain)
    (ha : Tendsto (fun n => embedding (a n)) l (𝓝 f)) :
    Tendsto (fun n => stochasticDictionary (a n)) l (𝓝 (integral f)) := by
  simpa only [Function.comp_def, integral_dictionary] using
    integral.continuous.continuousAt.tendsto.comp ha

theorem integral_unique (J : domain →ₗᵢ[ℝ] JointL2)
    (hJ : ∀ a, J (embedding a) = stochasticDictionary a) : J = integral := by
  symm
  apply LinearMap.extendOfIsometry_unique stochasticDictionary embedding_dense dictionary_norm J
  apply LinearMap.ext
  intro a
  exact hJ a

end OperatorDerivativeRewrite.Foundation.IBMRightGermIntegralCompletion
