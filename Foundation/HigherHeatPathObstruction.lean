import Foundation.HigherHeatKernelMoments
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Algebra.Order.Archimedean.Basic

/-! A finite signed path measure cannot realize the constructed higher-heat
increment laws on all successive equal-duration grids. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPathObstruction
open HigherHeatSignedLaws HigherHeatKernelMoments

theorem variation_mass_map_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : SignedMeasure Ω) (f : Ω → X) (hf : Measurable f) :
    ((μ.map f).variation Set.univ).toReal ≤ (μ.variation Set.univ).toReal := by
  apply ENNReal.toReal_mono
  · rw [← SignedMeasure.totalVariation_eq_variation]
    exact measure_ne_top _ _
  · calc
      (μ.map f).variation Set.univ ≤ (μ.variation.map f) Set.univ :=
        VectorMeasure.variation_map_le Set.univ
      _ = μ.variation Set.univ := by rw [Measure.map_apply hf MeasurableSet.univ]; rfl

theorem no_signed_increment_realization {Ω : Type*} [MeasurableSpace Ω]
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t)
    (μ : SignedMeasure Ω) (observation : (n : ℕ) → Ω → (Fin n → ℝ))
    (hobs : ∀ n, Measurable (observation n))
    (hlaw : ∀ n, μ.map (observation n) =
      incrementLaw m (by omega) (fun _ : Fin n => t) (fun _ => ht)) : False := by
  let C : ℝ := ∫ x : ℝ, ‖realKernel m (by omega : 0 < m) t ht x‖
  have hC : 1 < C := norm_integral_gt_one m hm t ht
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (μ.variation Set.univ).toReal hC
  have hb := variation_mass_map_le μ (observation n) (hobs n)
  rw [hlaw n,incrementLaw_variation_mass] at hb
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  exact (not_lt_of_ge hb) hn

def gridIncrement (t : ℝ≥0) (n : ℕ) (ω : ℝ≥0 → ℝ) (i : Fin n) : ℝ :=
  ω (((i.val+1 : ℕ) : ℝ≥0)*t) - ω ((i.val : ℝ≥0)*t)

theorem gridIncrement_measurable (t : ℝ≥0) (n : ℕ) : Measurable (gridIncrement t n) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

theorem no_signed_path_law (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t)
    (μ : SignedMeasure (ℝ≥0 → ℝ))
    (hlaw : ∀ n, μ.map (gridIncrement t n) =
      incrementLaw m (by omega) (fun _ : Fin n => t) (fun _ => ht)) : False :=
  no_signed_increment_realization m hm t ht μ (gridIncrement t)
    (gridIncrement_measurable t) hlaw

end OperatorDerivativeRewrite.Foundation.HigherHeatPathObstruction
