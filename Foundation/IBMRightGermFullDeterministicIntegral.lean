import Foundation.IBMRightGermIntervalDensity

/-! The actual deterministic stochastic integral on ALL L2 of the verified
IBM right-germ energy measure. Random predictable integration is separate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRightGermFullDeterministicIntegral
open IBMTimeAveragedObservable IBMIntrinsicRightGerm
open IBMRightGermDeterministicIntegral IBMRightGermIntervalDensity
set_option backward.isDefEq.respectTransparency false

def integral : TimeL2 →ₗᵢ[ℝ] JointL2 :=
  stochasticDictionary.extendOfIsometry timeDictionary_dense dictionary_norm

theorem integral_dictionary (a : ℝ≥0 →₀ ℝ) :
    integral (timeDictionary a) = stochasticDictionary a :=
  LinearMap.extendOfIsometry_eq _ _ _ _

theorem integral_dictionary_ae (a : ℝ≥0 →₀ ℝ) :
    integral (timeDictionary a) =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => ∑ t ∈ a.support, a t * rightValue t ω) := by
  rw [integral_dictionary]
  exact stochasticDictionary_ae a

theorem integral_interval {s t : ℝ≥0} (hst : s ≤ t) :
    integral (indicatorConstLp 2 measurableSet_Ioc
      (IBMRightGermEnergyMeasure.energyMeasure_Ioc_finite s t).ne (1 : ℝ)) =
        rightLimitClass t - rightLimitClass s := by
  rw [← interval_time_dictionary hst, integral_dictionary, interval_dictionary, one_smul]

theorem integral_norm (f : TimeL2) : ‖integral f‖ = ‖f‖ := integral.norm_map f

theorem integral_inner (f g : TimeL2) :
    inner ℝ (integral f) (integral g) = inner ℝ f g := integral.inner_map_map f g

theorem actual_integral_isometry (f : TimeL2) :
    (∫ ω, (integral f ω) ^ 2 ∂IBMSourceLaws.jointMeasure) = ‖f‖ ^ 2 := by
  rw [← integral_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    change (integral f ω) ^ 2 = inner ℝ (integral f ω) (integral f ω)
    rw [Real.inner_apply, pow_two]

theorem integral_limit {α : Type*} {l : Filter α} (a : α → (ℝ≥0 →₀ ℝ)) (f : TimeL2)
    (ha : Tendsto (fun n => timeDictionary (a n)) l (𝓝 f)) :
    Tendsto (fun n => stochasticDictionary (a n)) l (𝓝 (integral f)) := by
  simpa only [Function.comp_def, integral_dictionary] using
    integral.continuous.continuousAt.tendsto.comp ha

theorem integral_unique (J : TimeL2 →ₗᵢ[ℝ] JointL2)
    (hJ : ∀ a, J (timeDictionary a) = stochasticDictionary a) : J = integral := by
  symm
  apply LinearMap.extendOfIsometry_unique stochasticDictionary timeDictionary_dense dictionary_norm J
  apply LinearMap.ext
  intro a
  exact hJ a

theorem exists_dictionary_approximation (f : TimeL2) :
    ∃ a : ℕ → (ℝ≥0 →₀ ℝ),
      Tendsto (fun n => timeDictionary (a n)) atTop (𝓝 f) ∧
      Tendsto (fun n => stochasticDictionary (a n)) atTop (𝓝 (integral f)) := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (timeDictionary_dense f)
  choose a ha using hu
  have he : (fun n => timeDictionary (a n)) = u := funext ha
  have ht : Tendsto (fun n => timeDictionary (a n)) atTop (𝓝 f) := he ▸ hlim
  exact ⟨a, ht, integral_limit a f ht⟩

theorem agrees_previous (f : IBMRightGermIntegralCompletion.domain) :
    integral (f : TimeL2) = IBMRightGermIntegralCompletion.integral f := by
  have hu := IBMRightGermIntegralCompletion.integral_unique
    (integral.comp IBMRightGermIntegralCompletion.domain.subtypeₗᵢ) (fun a => integral_dictionary a)
  exact DFunLike.congr_fun hu f

end OperatorDerivativeRewrite.Foundation.IBMRightGermFullDeterministicIntegral
