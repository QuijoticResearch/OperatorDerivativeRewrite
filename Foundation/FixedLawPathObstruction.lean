import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecificLimits.Basic

/-! A fixed diffuse marginal law obstructs convergence to a deterministic start.
Existing Mathlib convergence-in-distribution machinery supplies the foundations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FixedLawPathObstruction
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

theorem fixed_law_distribution (X : ℕ → Ω → ℝ) (hX : ∀ n, HasLaw (X n) ν μ) :
    TendstoInDistribution X atTop (id : ℝ → ℝ) (fun _ => μ) ν where
  forall_aemeasurable := fun n => (hX n).aemeasurable
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    simp only [(hX _).map_eq, Measure.map_id]
    exact tendsto_const_nhds

theorem not_distribution_constant [NullSingletonClass ν]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, HasLaw (X n) ν μ) (x : ℝ) :
    ¬ TendstoInDistribution X atTop (fun _ : Ω => x) (fun _ => μ) μ := by
  intro hd
  have he := tendstoInDistribution_unique X (fixed_law_distribution μ ν X hX) hd
  have hs := congrArg (fun ρ : Measure ℝ => ρ {x}) he
  simpa [Measure.map_const] using hs

theorem not_in_measure_constant [NullSingletonClass ν]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, HasLaw (X n) ν μ) (x : ℝ) :
    ¬ TendstoInMeasure μ X atTop (fun _ => x) := by
  intro hd
  exact not_distribution_constant μ ν X hX x
    (hd.tendstoInDistribution (fun n => (hX n).aemeasurable))

theorem not_ae_constant [NullSingletonClass ν]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, HasLaw (X n) ν μ) (x : ℝ) :
    ¬ ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 x) := by
  intro hd
  exact not_distribution_constant μ ν X hX x
    (tendstoInDistribution_of_ae_tendsto (fun n => (hX n).aemeasurable)
      aemeasurable_const hd)

def smallTime (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem smallTime_positive (n : ℕ) : 0 < smallTime n := by
  unfold smallTime
  positivity

theorem smallTime_tendsto : Tendsto smallTime atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem smallTime_tendsto_right : Tendsto smallTime atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨smallTime_tendsto, .of_forall smallTime_positive⟩

theorem not_right_continuous [NullSingletonClass ν]
    (X : ℝ → Ω → ℝ) (x : ℝ) (hzero : X 0 =ᵐ[μ] fun _ => x)
    (hlaw : ∀ t, 0 < t → HasLaw (X t) ν μ) :
    ¬ ∀ᵐ ω ∂μ, ContinuousWithinAt (fun t => X t ω) (Ici 0) 0 := by
  intro hc
  apply not_ae_constant μ ν (fun n => X (smallTime n))
    (fun n => hlaw _ (smallTime_positive n)) x
  filter_upwards [hc, hzero] with ω hω hzeroω
  have ht : Tendsto smallTime atTop (𝓝[Ici 0] (0 : ℝ)) :=
    smallTime_tendsto_right.mono_right (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h := hω.tendsto.comp ht
  simpa only [Function.comp_def, hzeroω] using h

end OperatorDerivativeRewrite.Foundation.FixedLawPathObstruction
