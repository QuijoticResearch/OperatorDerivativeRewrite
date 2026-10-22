import Foundation.ContinuousObservationFiltrationObstruction
import Mathlib.MeasureTheory.Measure.Continuity

/-! Countable additivity is a genuine extra obligation for raw martingale
energies. An actual continuous-observation counterexample has no Ioc energy measure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RawMartingaleEnergyMeasureObstruction
open FixedLawPathObstruction ContinuousObservationFiltrationObstruction InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

def shrinkingInterval (n : ℕ) : Set ℝ := Ioc 0 (smallTime n)

theorem shrinkingInterval_antitone : Antitone shrinkingInterval := by
  intro i j hij
  apply Ioc_subset_Ioc_right
  unfold smallTime
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 1

theorem shrinkingInterval_inter : (⋂ n, shrinkingInterval n) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ha := mem_iInter.mp hx
  have hp : 0 < x := (ha 0).1
  have he : ∀ᶠ n in atTop, smallTime n < x := smallTime_tendsto.eventually (eventually_lt_nhds hp)
  obtain ⟨n, hn⟩ := he.exists
  exact (not_le_of_gt hn) (ha n).2

/-- No measure can give mass one to every positive interval (0,t]. Finiteness
of one such interval is enough; the whole measure need not be finite. -/
theorem no_constant_origin_interval_measure (ρ : Measure ℝ)
    (hρ : ∀ t : ℝ, 0 < t → ρ (Ioc 0 t) = 1) : False := by
  have ht := tendsto_measure_iInter_atTop (μ := ρ)
    (fun n => (show MeasurableSet (shrinkingInterval n) from measurableSet_Ioc).nullMeasurableSet)
    shrinkingInterval_antitone
    (show ∃ n, ρ (shrinkingInterval n) ≠ ∞ from ⟨0, by
      rw [shrinkingInterval, hρ _ (smallTime_positive 0)]; norm_num⟩)
  rw [shrinkingInterval_inter, measure_empty] at ht
  have he : (ρ ∘ shrinkingInterval) = (fun _ : ℕ => (1 : ℝ≥0∞)) :=
    funext fun n => hρ _ (smallTime_positive n)
  rw [he] at ht
  have hh := tendsto_nhds_unique ht
    (show Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 1) from tendsto_const_nhds)
  norm_num at hh

/-- The squared-increment energies of this ACTUAL square-integrable martingale
cannot be the Ioc values of any countably additive time measure. -/
theorem no_actual_increment_energy_measure :
    ¬ ∃ ρ : Measure ℝ, ∀ t : ℝ, 0 < t →
      ρ (Ioc 0 t) = ENNReal.ofReal (∫ ω, (value t ω - value 0 ω) ^ 2 ∂gaussianProduct) := by
  rintro ⟨ρ, hρ⟩
  apply no_constant_origin_interval_measure ρ
  intro t ht
  rw [hρ t ht, increment_energy ht]
  norm_num

end OperatorDerivativeRewrite.Foundation.RawMartingaleEnergyMeasureObstruction
