import Foundation.PeriodicLocalGroundHarnack
import Foundation.PeriodicEvenWindingCriterion
/-! Actual stationary low-action mass from the verified joint-energy moment.
A region of uniformly positive native probability supports the local dressed-
ground comparison. No connectivity, mixing rate or spectral gap is asserted. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicLowActionStationaryMass
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabJoint
open PeriodicTemporalConcentration PeriodicGaugeSaturatedGround PeriodicCurvatureWeighted
attribute [local irreducible] spatialAction energy
variable {β : ℝ} (g : GroundData β)
private instance stationary_prob : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance triple_prob : IsProbabilityMeasure (tripleLaw g) := triple_probability g

private theorem scaled_square_integrable (β : ℝ) (g : GroundData β) :
    Integrable (fun U => (β*spatialAction U)^2) g.stationary := by
  apply Integrable.of_bound ((spatial_action_measurable.const_mul β).pow_const 2).aestronglyMeasurable
    (β^2*384^2)
  filter_upwards with U
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (spatial_action_bounds U).1 (spatial_action_bounds U).2 2) (sq_nonneg β)
  nlinarith

theorem stationary_scaled_square (β : ℝ) (hb : 16777216 ≤ β) (g : GroundData β) :
    (∫ U,(β*spatialAction U)^2 ∂g.stationary) ≤ 32*ratioConstant := by
  have hp : 0 < β := by linarith
  have hm := (spatial_action_measurable.const_mul β).pow_const 2
  have mp := PeriodicEvenWindingCriterion.left_triple_preserving g
  have hmap := integral_map (μ := tripleLaw g) (φ := fun q : Triple => q.1.1)
    mp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [mp.map_eq] at hmap
  have hpoint (q : Triple) : (β*spatialAction q.1.1)^2 ≤ (4*β^2)*energy q^2 := by
    have hs : spatialAction q.1.1 ≤ 2*energy q := by
      unfold energy halfAction
      linarith [(spatial_action_bounds q.1.2).1,(temporal_action_bounds q.1.1 q.1.2 q.2).1]
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (spatial_action_bounds q.1.1).1 hs 2) (sq_nonneg β)
    nlinarith
  have hi := integral_mono_of_nonneg (ae_of_all (tripleLaw g) (fun q => sq_nonneg (β*spatialAction q.1.1)))
    ((energy_square_integrable g).const_mul (4*β^2)) (ae_of_all _ hpoint)
  rw [integral_const_mul] at hi
  have hu := mul_le_mul_of_nonneg_left (energy_square_uniform β hb g) (show (0 : ℝ) ≤ 4*β^2 by positivity)
  have he : (4*β^2)*(8*ratioConstant/β^2)=32*ratioConstant := by field_simp <;> ring
  rw [he] at hu
  rw [hmap]
  exact hi.trans hu

theorem low_action_mass (β : ℝ) (hb : 16777216 ≤ β) (g : GroundData β) :
    (1/2 : ℝ) ≤ g.stationary.real {U | β*spatialAction U ≤ 8*(ratioConstant+1)} := by
  let K : ℝ := 8*(ratioConstant+1)
  let A : Set State := {U | K < β*spatialAction U}
  have hK : 0 < K := mul_pos (by norm_num) (by linarith [ratioConstant_pos])
  have hA : MeasurableSet A := measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)
  have hQ := (integrable_const (μ := g.stationary) (K^2)).indicator hA
  have hle := integral_mono hQ (scaled_square_integrable β g) (fun U => by
    by_cases hU : U∈A
    · rw [Set.indicator_of_mem hU]
      exact pow_le_pow_left₀ hK.le hU.le 2
    · rw [Set.indicator_of_notMem hU]
      exact sq_nonneg _)
  rw [integral_indicator hA,setIntegral_const,smul_eq_mul] at hle
  have htail : g.stationary.real A*K^2 ≤ 32*ratioConstant := hle.trans (stationary_scaled_square β hb g)
  have hpoly : 32*ratioConstant ≤ (1/2 : ℝ)*K^2 := by
    dsimp [K]
    nlinarith [sq_nonneg ratioConstant,ratioConstant_pos]
  have hbound : g.stationary.real A ≤ (1/2 : ℝ) :=
    (mul_le_mul_iff_left₀ (sq_pos_of_pos hK)).mp (htail.trans hpoly)
  have he : {U | β*spatialAction U ≤ 8*(ratioConstant+1)}=Aᶜ := by
    ext U
    simp only [A,Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt,K]
  rw [he,measureReal_compl hA,probReal_univ]
  linarith

open PeriodicLocalGroundHarnack PeriodicQuarticGaugeOverlap
/-- The local comparison has a set of anchors of actual stationary mass at least one half. -/
theorem half_mass_comparison (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (hb : 16777216 ≤ 1/t^2) (g : GroundData (1/t^2)) :
    ((1/2 : ℝ) ≤ g.stationary.real {U | (1/t^2)*spatialAction U ≤ 8*(ratioConstant+1)}) ∧
    (∀ U : State,(1/t^2)*spatialAction U ≤ 8*(ratioConstant+1) →
      ∀ W : State,W∈packet U (3*t) →
        (((1/(4*Real.pi^2))^192*Real.exp (-(3*(8*(ratioConstant+1))+59328))*dressed g U ≤
          PeriodicGroundHaarScale.upperConstant*dressed g W) ∧
         ((1/(4*Real.pi^2))^192*Real.exp (-(3*(8*(ratioConstant+1))+59328))*dressed g W ≤
          PeriodicGroundHaarScale.upperConstant*dressed g U))) := by
  refine ⟨low_action_mass (1/t^2) hb g,?_⟩
  intro U hU W hW
  exact uniform_local_comparison t ht h1 g U W _ hU hW
end OperatorDerivativeRewrite.Foundation.PeriodicLowActionStationaryMass
