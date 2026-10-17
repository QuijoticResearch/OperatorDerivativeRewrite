import Foundation.GaussianBrownianPRP
import Foundation.GaussianConditionalCompactness
import Foundation.GaussianChaosGraphConvergence
import Foundation.SPDEWickModes

/-! An actual one-observation L2 target has predictable representation but is
outside the full closed Gaussian derivative domain. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictableDomainGap
open InfiniteGaussian GaussianNumberSectors GaussianConditionalCompactness
open GaussianTimeSpaceHermite GaussianPredictableFull GaussianPredictableAdjoint GaussianBrownianPRP
open GaussianBrownianGeneratedSpace GaussianConditionalGraph GaussianWickConditionalProjection
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def harmonicSequence : CoefficientSpace :=
  ⟨SPDEWickModes.harmonicCoefficient, memℓp_gen (by
    simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs] using SPDEWickModes.harmonic_square_summable)⟩

theorem harmonic_weighted_not_summable :
    ¬ Summable (fun n : ℕ => (n : ℝ) * (harmonicSequence n)^2) := by
  intro hs
  have ht := hs.add SPDEWickModes.harmonic_square_summable
  have he (n : ℕ) : (n : ℝ) * (harmonicSequence n)^2 +
      (SPDEWickModes.harmonicCoefficient n)^2 = SPDEWickModes.harmonicCoefficient n := by
    change (n : ℝ) * (1/((n:ℝ)+1))^2 + (1/((n:ℝ)+1))^2 = 1/((n:ℝ)+1)
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    field_simp
  exact SPDEWickModes.harmonic_not_summable (by simpa only [he] using ht)

theorem projection_terminalEmbedding (u : CoefficientSpace) (hu : ‖u‖^2 = 1)
    (c : CoefficientSpace) (n : ℕ) :
    projection n (terminalEmbedding u hu c) = c n • normalizedWick u n := by
  have hm (m : ℕ) : normalizedWick u m ∈ sector m :=
    (sector m).smul_mem _ (IBMCubicFirstChaos.wick_mem_sector u m)
  have hs := (projection n).hasSum (terminalEmbedding_hasSum u hu c)
  have ht : HasSum (fun m => projection n (c m • normalizedWick u m))
      (c n • normalizedWick u n) := by
    convert (hasSum_ite_eq n (c n • normalizedWick u n)) using 1
    funext m
    rw [map_smul, projection_of_sector (⟨_, hm m⟩ : sector m)]
    by_cases h : m = n
    · subst m; simp
    · simp [h, Ne.symm h]
  exact hs.unique ht

def roughTerminal (u : CoefficientSpace) (hu : ‖u‖^2 = 1) : GaussianL2 :=
  terminalEmbedding u hu harmonicSequence

theorem rough_single_observation (u : CoefficientSpace) (hu : ‖u‖^2 = 1) :
    roughTerminal u hu ∈ generated (fun _ : Unit => u) := by
  have hm : u ∈ sourceSpan (fun _ : Unit => u) :=
    (Submodule.span ℝ (Set.range (fun _ : Unit => u))).le_topologicalClosure
      (Submodule.subset_span ⟨(), rfl⟩)
  have he := conditional_fixes_terminalEmbedding (fun _ : Unit => u) u hu hm harmonicSequence
  exact (generated (fun _ : Unit => u)).starProjection_eq_self_iff.mp he
theorem rough_projection_energy (u : CoefficientSpace) (hu : ‖u‖^2 = 1) (n : ℕ) :
    ‖projection n (roughTerminal u hu)‖^2 = (harmonicSequence n)^2 := by
  rw [roughTerminal, projection_terminalEmbedding, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    (normalizedWick_orthonormal u hu).norm_eq_one, one_pow, mul_one]

theorem rough_not_in_derivative_domain (u : CoefficientSpace) (hu : ‖u‖^2 = 1) :
    roughTerminal u hu ∉ closedCylindricalDerivative.domain := by
  rw [derivative_domain_iff_weighted_chaos]
  simpa only [rough_projection_energy] using harmonic_weighted_not_summable

def terminalDirection : CoefficientSpace :=
  SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
    (GaussianTimeHilbert.timeVector 1)

theorem terminalDirection_unit : ‖terminalDirection‖^2 = 1 := by
  rw [terminalDirection, LinearIsometry.norm_map, GaussianTimeHilbert.timeVector_norm_sq]
  rfl

theorem brownian_wick_mem (n : ℕ) : (wick terminalDirection n : GaussianL2) ∈ brownianL2 := by
  have hm : Measurable[brownianSigma] (fun ω => value n (GaussianTimeProcess.process 1 ω) 1) := by
    letI : MeasurableSpace SampleSpace := brownianSigma
    exact (polynomial 1 n).continuous_eval.measurable.comp
      (Measurable.of_eval (fun _ : Unit => process_brownian_measurable 1))
  have he : (wick terminalDirection n : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => value n (GaussianTimeProcess.process 1 ω) 1 := brownianCore_coeFn 1 n
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr he.symm

theorem rough_brownian_mem : roughTerminal terminalDirection terminalDirection_unit ∈ brownianL2 := by
  apply brownianL2_isClosed.mem_of_tendsto
    (terminalEmbedding_hasSum terminalDirection terminalDirection_unit harmonicSequence)
  apply Eventually.of_forall
  intro s
  exact brownianL2.sum_mem (fun n _ => brownianL2.smul_mem _
    (brownianL2.smul_mem _ (brownian_wick_mem n)))

/-- The raw sigma-algebra of the actual Brownian observation at time one. -/
@[instance_reducible]
def terminalSigma : MeasurableSpace SampleSpace :=
  MeasurableSpace.comap (GaussianTimeProcess.process 1) inferInstance

theorem terminalSigma_le : terminalSigma ≤ (inferInstance : MeasurableSpace SampleSpace) :=
  (GaussianTimeProcess.process_stronglyMeasurable 1).measurable.comap_le

def terminalL2 : Submodule ℝ GaussianL2 := lpMeas ℝ ℝ terminalSigma 2 gaussianProduct

theorem terminalL2_isClosed : IsClosed (terminalL2 : Set GaussianL2) :=
  isClosed_aestronglyMeasurable terminalSigma_le

theorem brownian_wick_terminal_mem (n : ℕ) :
    (wick terminalDirection n : GaussianL2) ∈ terminalL2 := by
  have hp : Measurable[terminalSigma] (GaussianTimeProcess.process 1) :=
    Measurable.of_comap_le le_rfl
  have hm : Measurable[terminalSigma] (fun ω => value n (GaussianTimeProcess.process 1 ω) 1) := by
    letI : MeasurableSpace SampleSpace := terminalSigma
    exact (polynomial 1 n).continuous_eval.measurable.comp
      (Measurable.of_eval (fun _ : Unit => hp))
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr (brownianCore_coeFn 1 n).symm

theorem rough_terminal_mem : roughTerminal terminalDirection terminalDirection_unit ∈ terminalL2 := by
  apply terminalL2_isClosed.mem_of_tendsto
    (terminalEmbedding_hasSum terminalDirection terminalDirection_unit harmonicSequence)
  apply Eventually.of_forall
  intro s
  exact terminalL2.sum_mem (fun n _ => terminalL2.smul_mem _
    (terminalL2.smul_mem _ (brownian_wick_terminal_mem n)))
theorem actual_predictable_representation :
    itoIntegral (predictableAdjoint (roughTerminal terminalDirection terminalDirection_unit)) =
      roughTerminal terminalDirection terminalDirection_unit -
        (∫ ω, roughTerminal terminalDirection terminalDirection_unit ω ∂gaussianProduct) • gaussianOne :=
  brownian_representation _ rough_brownian_mem

theorem representation_without_full_derivative :
    ∃ F : GaussianL2, F ∈ brownianL2 ∧ F ∉ closedCylindricalDerivative.domain ∧
      itoIntegral (predictableAdjoint F) = F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne :=
  ⟨roughTerminal terminalDirection terminalDirection_unit, rough_brownian_mem,
    rough_not_in_derivative_domain _ _, actual_predictable_representation⟩

theorem rough_not_in_full_adjoint_domain (u : CoefficientSpace) (hu : ‖u‖^2 = 1) :
    roughTerminal u hu ∉ hilbertDivergence.adjoint.domain := by
  rw [hilbertDivergence_adjoint_eq_closedDerivative]
  exact rough_not_in_derivative_domain u hu

theorem no_full_adjoint_pair (u : CoefficientSpace) (hu : ‖u‖^2 = 1) :
    ¬ ∃ v : GaussianVectorL2, (roughTerminal u hu, v) ∈ hilbertDivergence.adjoint.graph := by
  rintro ⟨v, hv⟩
  exact rough_not_in_full_adjoint_domain u hu (LinearPMap.mem_domain_iff.mpr ⟨v,hv⟩)

theorem terminal_representation_without_full_adjoint :
    ∃ F : GaussianL2, AEStronglyMeasurable[terminalSigma] F gaussianProduct ∧
      F ∉ hilbertDivergence.adjoint.domain ∧
      itoIntegral (predictableAdjoint F) = F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne :=
  ⟨roughTerminal terminalDirection terminalDirection_unit, rough_terminal_mem,
    rough_not_in_full_adjoint_domain _ _, actual_predictable_representation⟩
theorem rough_gradient_truncation_energy (u : CoefficientSpace) (hu : ‖u‖^2 = 1) (N : ℕ) :
    ‖gradientTruncation N (roughTerminal u hu)‖^2 =
      ∑ n ∈ Finset.range (N+1), (n : ℝ) * (harmonicSequence n)^2 := by
  simp only [gradientTruncation, ContinuousLinearMap.sum_apply, projectedGradient_sum_energy,
    projectedGradient_energy, rough_projection_energy]

theorem rough_gradient_energy_diverges (u : CoefficientSpace) (hu : ‖u‖^2 = 1) :
    Tendsto (fun N : ℕ => ‖gradientTruncation N (roughTerminal u hu)‖^2) atTop atTop := by
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (harmonicSequence n)))).mp
      harmonic_weighted_not_summable
  simpa only [rough_gradient_truncation_energy, Function.comp_def] using
    ht.comp (tendsto_add_atTop_nat 1)

theorem rough_predictable_approximation (u : CoefficientSpace) (hu : ‖u‖^2 = 1) :
    Tendsto (fun N : ℕ => predictableAdjoint (truncation N (roughTerminal u hu)))
      atTop (𝓝 (predictableAdjoint (roughTerminal u hu))) :=
  predictableAdjoint.continuous.continuousAt.tendsto.comp (truncation_tendsto _)
theorem predictableProjection_gradientTruncation (F : GaussianL2) (N : ℕ) :
    predictableProjection (gradientTruncation N F) = predictableAdjoint (truncation N F) := by
  have hg := truncation_graph N F
  let x : closedCylindricalDerivative.domain :=
    ⟨truncation N F, LinearPMap.mem_domain_iff.mpr ⟨gradientTruncation N F, hg⟩⟩
  have he : closedCylindricalDerivative x = gradientTruncation N F :=
    closedCylindricalDerivative.mem_graph_snd_inj (closedCylindricalDerivative.mem_graph x) hg rfl
  have hp := predictableAdjoint_eq_projected_derivative x
  rw [he] at hp
  exact hp.symm

theorem all_L2_projected_graph_approximation (F : GaussianL2) :
    (∀ N : ℕ, (truncation N F, gradientTruncation N F) ∈ closedCylindricalDerivative.graph) ∧
      Tendsto (fun N : ℕ => (truncation N F, predictableProjection (gradientTruncation N F)))
        atTop (𝓝 (F, predictableAdjoint F)) := by
  refine ⟨fun N => truncation_graph N F, ?_⟩
  simp only [predictableProjection_gradientTruncation]
  exact (truncation_tendsto F).prodMk_nhds
    (predictableAdjoint.continuous.continuousAt.tendsto.comp (truncation_tendsto F))

theorem rough_projected_derivatives_converge (u : CoefficientSpace) (hu : ‖u‖^2 = 1) :
    Tendsto (fun N : ℕ => predictableProjection (gradientTruncation N (roughTerminal u hu)))
      atTop (𝓝 (predictableAdjoint (roughTerminal u hu))) := by
  simpa only [predictableProjection_gradientTruncation] using rough_predictable_approximation u hu
end OperatorDerivativeRewrite.Foundation.GaussianPredictableDomainGap
