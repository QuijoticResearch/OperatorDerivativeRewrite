import Foundation.QuarticAppellDualDensity
import Foundation.HigherHeatObservableGenerator

/-! Actual heat-semigroup propagation of the Appell coordinate densities. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.QuarticDualSemigroup
open HigherHeatSpatialGenerator HigherHeatSchwartzJets HigherHeatSchwartzSemigroup
open HigherHeatBackwardSchwartz QuarticAppellDualDensity

theorem evolve_jet (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (n : ℕ) (f : 𝓢(ℝ,ℂ)) :
    evolve m hm t (jet n f) = jet n (evolve m hm t f) := by
  apply (fourierEquiv ℂ 𝓢(ℝ,ℂ)).injective
  ext ξ
  change 𝓕 (evolve m hm t (jet n f)) ξ = 𝓕 (jet n (evolve m hm t f)) ξ
  rw [evolve_fourier, jet_fourier, jet_fourier, evolve_fourier]
  ring

theorem density_evolve (s T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    evolve 2 (by norm_num) s (density T hT n) = density (s+T) (by positivity) n := by
  rw [density, evolve_linear_smul, evolve_jet, HigherHeatObservableGenerator.evolve_kernel]
  rfl

theorem density_l2_evolve (s T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    HigherHeatL2.evolution 2 s ((density T hT n).toLp 2 volume) =
      (density (s+T) (by positivity) n).toLp 2 volume := by
  rw [← evolve_toLp 2 (by norm_num) s (density T hT n), density_evolve]

theorem density_l2_contraction (s T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ‖(density (s+T) (by positivity) n).toLp 2 volume‖ ≤
      ‖(density T hT n).toLp 2 volume‖ := by
  rw [← density_l2_evolve s T hT n]
  exact HigherHeatL2.evolution_contraction 2 s _

theorem density_l2_continuous (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    Continuous (fun s : ℝ≥0 => (density (s+T) (by positivity) n).toLp 2 volume) := by
  have he : (fun s : ℝ≥0 => (density (s+T) (by positivity) n).toLp 2 volume) =
      (fun s : ℝ≥0 => HigherHeatL2.evolution 2 s ((density T hT n).toLp 2 volume)) := by
    funext s
    exact (density_l2_evolve s T hT n).symm
  rw [he]
  exact HigherHeatL2.evolution_strong_continuous 2 _

theorem density_right_generator (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    HasDerivWithinAt (fun s : ℝ =>
      (density (s.toNNReal+T) (by positivity) n).toLp 2 volume)
      ((differential 2 (density T hT n)).toLp 2 volume) (Set.Ici 0) 0 := by
  have he : (fun s : ℝ => (density (s.toNNReal+T) (by positivity) n).toLp 2 volume) =
      (fun s : ℝ => HigherHeatL2.evolution 2 s.toNNReal
        ((density T hT n).toLp 2 volume)) := by
    funext s
    exact (density_l2_evolve s.toNNReal T hT n).symm
  rw [he]
  exact HigherHeatSpatialGenerator.evolution_hasDerivWithinAt 2 _

end OperatorDerivativeRewrite.Foundation.QuarticDualSemigroup
