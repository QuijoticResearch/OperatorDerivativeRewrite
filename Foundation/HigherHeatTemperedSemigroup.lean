import Foundation.QuarticDualDistributions
import Mathlib.Analysis.Distribution.FourierMultiplier

/-! Continuous linear heat operators on Schwartz tests and their actual tempered transposes. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatTemperedSemigroup
open HigherHeatL2 GaussianSchwartzKernel HigherHeatSchwartzSemigroup
open HigherHeatBackwardSchwartz HigherHeatSchwartzCalculus

def schwartzOperator (m : ℕ) (hm : 0 < m) (t : ℝ≥0) : 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℝ,ℂ) :=
  if ht : 0 < t then SchwartzMap.fourierMultiplierCLM ℂ (evenSymbol m hm t ht : ℝ → ℂ)
  else ContinuousLinearMap.id ℂ _

theorem schwartzOperator_apply (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    schwartzOperator m hm t f = evolve m hm t f := by
  by_cases ht : 0 < t
  · apply (fourierEquiv ℂ 𝓢(ℝ,ℂ)).injective
    ext ξ
    change 𝓕 (schwartzOperator m hm t f) ξ = 𝓕 (evolve m hm t f) ξ
    rw [schwartzOperator, dif_pos ht, SchwartzMap.fourierMultiplierCLM_apply,
      fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply (evenSymbol m hm t ht).hasTemperateGrowth,
      evolve_fourier]
    simp only [evenSymbol_apply, smul_eq_mul]
  · have ht0 : t=0 := le_antisymm (le_of_not_gt ht) (by positivity)
    subst t
    simp [schwartzOperator, evolve_zero]

theorem schwartzOperator_add (m : ℕ) (hm : 0 < m) (s t : ℝ≥0) :
    (schwartzOperator m hm s).comp (schwartzOperator m hm t) =
      schwartzOperator m hm (s+t) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, schwartzOperator_apply]
  exact evolve_add m hm s t f

def transpose (m : ℕ) (hm : 0 < m) (t : ℝ≥0) : 𝓢'(ℝ,ℂ) →L[ℂ] 𝓢'(ℝ,ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ (schwartzOperator m hm t)

theorem transpose_apply (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (F : 𝓢'(ℝ,ℂ)) (f : 𝓢(ℝ,ℂ)) :
    transpose m hm t F f = F (evolve m hm t f) := by
  change F (schwartzOperator m hm t f) = _
  rw [schwartzOperator_apply]

theorem transpose_zero (m : ℕ) (hm : 0 < m) :
    transpose m hm 0 = ContinuousLinearMap.id ℂ _ := by
  ext F f
  rw [transpose_apply, evolve_zero]
  rfl

theorem transpose_add (m : ℕ) (hm : 0 < m) (s t : ℝ≥0) :
    (transpose m hm s).comp (transpose m hm t) = transpose m hm (s+t) := by
  ext F f
  change transpose m hm s (transpose m hm t F) f = transpose m hm (s+t) F f
  rw [transpose_apply, transpose_apply, transpose_apply, evolve_add, add_comm t s]

theorem mean_evolve (m : ℕ) (hm : 0 < m) (T s : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    mean m T (evolve m hm s f) = mean m (s+T) f := by
  unfold mean
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    rw [evolve_fourier, symbol_add]
    simp only [HigherHeatSchwartzTransition.symbol_even]
    ring

theorem realized_propagation (n : ℕ) (s T : ℝ≥0) :
    transpose 2 (by norm_num) s (QuarticDualDistributions.realized n T) =
      QuarticDualDistributions.realized n (s+T) := by
  ext f
  rw [transpose_apply, QuarticDualDistributions.realized_apply,
    QuarticDualDistributions.realized_apply,
    ← QuarticDualSemigroup.evolve_jet 2 (by norm_num) s n f, mean_evolve]

theorem initial_orbit (n : ℕ) (s : ℝ≥0) :
    transpose 2 (by norm_num) s (QuarticDualDistributions.initial n) =
      QuarticDualDistributions.realized n s := by
  simpa only [QuarticDualDistributions.realized_initial, add_zero] using
    realized_propagation n s 0

theorem differential_jet_commute (m n : ℕ) (f : 𝓢(ℝ,ℂ)) :
    HigherHeatSpatialGenerator.differential m (HigherHeatSpatialGenerator.jet n f) =
      HigherHeatSpatialGenerator.jet n (HigherHeatSpatialGenerator.differential m f) := by
  apply (fourierEquiv ℂ 𝓢(ℝ,ℂ)).injective
  ext ξ
  change 𝓕 (HigherHeatSpatialGenerator.differential m
    (HigherHeatSpatialGenerator.jet n f)) ξ =
    𝓕 (HigherHeatSpatialGenerator.jet n (HigherHeatSpatialGenerator.differential m f)) ξ
  simp only [HigherHeatSpatialGenerator.differential_fourier,
    HigherHeatSchwartzJets.jet_fourier, HigherHeatSpatialGenerator.spectral_apply]
  ring

theorem realized_weak_heat_equation (n : ℕ) (f : 𝓢(ℝ,ℂ)) (T : ℝ) (hT : 0 ≤ T) :
    HasDerivWithinAt (fun t : ℝ => QuarticDualDistributions.realized n t.toNNReal f)
      (QuarticDualDistributions.realized n T.toNNReal
        (HigherHeatSpatialGenerator.differential 2 f)) (Set.Ici 0) T := by
  simpa only [QuarticDualDistributions.realized_apply, differential_jet_commute] using
    QuarticDualDistributions.realized_observable_generator n f T hT

theorem initial_zero : QuarticDualDistributions.initial 0 = TemperedDistribution.delta (0:ℝ) := by
  ext f
  rw [QuarticDualDistributions.initial_apply, TemperedDistribution.delta_apply]
  simp [HigherHeatSpatialGenerator.jet]

end OperatorDerivativeRewrite.Foundation.HigherHeatTemperedSemigroup
