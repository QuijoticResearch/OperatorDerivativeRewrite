import Foundation.IBMRandomBlockQuartic

/-! Continuous functions of genuine IBM observations supply the finite random
coefficient envelope automatically, without a global spatial bound or moments.
The number of blocks remains fixed while the underlying grid is refined. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMContinuousBlockWeights
open IBMSourceLaws IBMConstructedSources IBMRandomBlockQuartic
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

private theorem exists_path_bound (φ : ℝ → ℝ) (hφ : Continuous φ) (T : ℝ≥0)
    (ω : JointSample) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, t ≤ T → |φ (ibmValue t ω)| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).exists_bound_of_continuousOn
    (hφ.comp (ibmValue_continuous ω)).continuousOn
  refine ⟨M, (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le⟩), ?_⟩
  intro t ht
  simpa only [Function.comp_def, Real.norm_eq_abs] using hM t ⟨zero_le, ht⟩

/-- A pointwise compact-path envelope. No measurability or integrability of
this chosen bound is asserted or needed in the domination theorem. -/
def pathBound (φ : ℝ → ℝ) (hφ : Continuous φ) (T : ℝ≥0) (ω : JointSample) : ℝ :=
  Classical.choose (exists_path_bound φ hφ T ω)

theorem pathBound_nonneg (φ : ℝ → ℝ) (hφ : Continuous φ) (T : ℝ≥0) (ω : JointSample) :
    0 ≤ pathBound φ hφ T ω :=
  (Classical.choose_spec (exists_path_bound φ hφ T ω)).1

theorem pathBound_bound (φ : ℝ → ℝ) (hφ : Continuous φ) (T : ℝ≥0)
    (ω : JointSample) (t : ℝ≥0) (ht : t ≤ T) :
    |φ (ibmValue t ω)| ≤ pathBound φ hφ T ω :=
  (Classical.choose_spec (exists_path_bound φ hφ T ω)).2 t ht

variable {ι : Type*}

def coefficient (φ : ℝ → ℝ) (τ : ℕ → ι → JointSample → ℝ≥0)
    (n : ℕ) (j : ι) (ω : JointSample) : ℝ := φ (ibmValue (τ n j ω) ω)

theorem coefficient_measurable (φ : ℝ → ℝ) (hφ : Continuous φ)
    (τ : ℕ → ι → JointSample → ℝ≥0) (hτ : ∀ n j, Measurable (τ n j))
    (n : ℕ) (j : ι) : Measurable (coefficient φ τ n j) :=
  hφ.measurable.comp (ibmValue_jointly_measurable.comp ((hτ n j).prodMk measurable_id))

theorem coefficient_envelope (φ : ℝ → ℝ) (hφ : Continuous φ) (T : ℝ≥0)
    (I : Finset ι) (τ : ℕ → ι → JointSample → ℝ≥0)
    (hτT : ∀ n j ω, τ n j ω ≤ T) (n : ℕ) (ω : JointSample) :
    (∑ j ∈ I, |coefficient φ τ n j ω|) ≤ (I.card : ℝ) * pathBound φ hφ T ω := by
  calc
    _ ≤ ∑ j ∈ I, pathBound φ hφ T ω :=
      Finset.sum_le_sum fun j _ => pathBound_bound φ hφ T ω _ (hτT n j ω)
    _ = _ := by simp

/-- Continuous (possibly globally unbounded) spatial weights at measurable
sample-dependent observation times in the horizon satisfy the genuine
finite-block quartic/Lebesgue comparison. No adaptedness or moment premise. -/
theorem actual_weighted_step_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (I : Finset ι) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (τ : ℕ → ι → JointSample → ℝ≥0) (hτ : ∀ n j, Measurable (τ n j))
    (hτT : ∀ n j ω, τ n j ω ≤ T)
    (l u : ℕ → ι → JointSample → ℕ)
    (hl : ∀ n j, Measurable (l n j)) (hu : ∀ n j, Measurable (u n j))
    (hlN : ∀ n j ω, l n j ω ≤ n + 1) (huN : ∀ n j ω, u n j ω ≤ n + 1)
    (hlu : ∀ n j ω, l n j ω ≤ u n j ω) :
    TendstoInMeasure jointMeasure
      (fun n ω => weightedQuartic T I (coefficient φ τ) l u n ω -
        3 * ∫ t, stepWeight T I (coefficient φ τ) l u n ω t)
      Filter.atTop (fun _ => (0 : ℝ)) :=
  weighted_step_tendstoInMeasure hT I _ l u (coefficient_measurable φ hφ τ hτ)
    hl hu hlN huN hlu (fun ω => (I.card : ℝ) * pathBound φ hφ T ω)
    (coefficient_envelope φ hφ T I τ hτT)

end OperatorDerivativeRewrite.Foundation.IBMContinuousBlockWeights
