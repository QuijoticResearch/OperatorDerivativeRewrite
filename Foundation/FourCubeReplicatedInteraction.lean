import Foundation.FourCubeGaugeCalibration
import Foundation.FourCubeProjectiveInteraction
import Mathlib.MeasureTheory.Integral.Pi
/-! Actual disjoint Wilson-cell partitions: a vanishing one-cell cubic can accumulate.
These are independent copies, not an unproved connected spatial transfer model. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeReplicatedInteraction
open FourCubeConditionalScore FourCubeHaarContinuousIntegral FourCubeHaarParity
open FourCubeProjectiveInteraction (ratio ratio_positive log_ratio)
open FourCubeThermalMixedDifference (cornerSum)

def cellPartition (β x y z : ℝ) : ℝ := FourCubeBoundarySmoothPartition.partition β ![x,y,z]

def productPartition (m : ℕ) (β x y z : ℝ) : ℝ :=
  ∫ s : Fin m → InteriorState,∏ i,FourCubeConditionalScore.weight β ![x,y,z] (s i)
    ∂Measure.pi (fun _ : Fin m => interiorHaar)

theorem product_weight_integrable (m : ℕ) (β x y z : ℝ) :
    Integrable (fun s : Fin m → InteriorState => ∏ i,
      FourCubeConditionalScore.weight β ![x,y,z] (s i))
      (Measure.pi (fun _ : Fin m => interiorHaar)) :=
  Integrable.fintype_prod (fun _ : Fin m => observable_integrable
    (FourCubeConditionalScore.weight β ![x,y,z]))

theorem productPartition_eq (m : ℕ) (β x y z : ℝ) :
    productPartition m β x y z=(cellPartition β x y z)^m := by
  rw [productPartition,integral_fintype_prod_eq_pow]
  simp only [Fintype.card_fin,cellPartition,FourCubeBoundarySmoothPartition.partition,
    ← haarIntegral_apply]
  rfl

theorem cellPartition_pos (β x y z : ℝ) : 0<cellPartition β x y z := partition_pos β _

theorem productPartition_pos (m : ℕ) (β x y z : ℝ) : 0<productPartition m β x y z := by
  rw [productPartition_eq]
  exact pow_pos (cellPartition_pos β x y z) m

private theorem log_cell (β x y z : ℝ) :
    Real.log (cellPartition β x y z)= -FourCubeThermalMixedDifference.freeEnergy β x y z+
      Real.log (FourCubePinnedConcentration.normalizer β) := by
  have h := potential_eq_actual β (![x,y,z]:Parameters)
  change -Real.log (cellPartition β x y z)=FourCubeThermalMixedDifference.freeEnergy β x y z-_ at h
  linarith

/-- Actual finite product Haar integral, including all32 interior links of each copy. -/
theorem product_log_ratio (m : ℕ) (β t : ℝ) :
    Real.log (ratio (productPartition m β) t)=
      -(m:ℝ)*cornerSum (FourCubeThermalMixedDifference.freeEnergy β) t := by
  rw [log_ratio _ (productPartition_pos m β)]
  simp_rw [productPartition_eq,Real.log_pow,log_cell]
  unfold cornerSum
  ring

def clock (n : ℕ) : ℝ := 1/((n:ℝ)+1)

theorem clock_pos (n : ℕ) : 0<clock n := by unfold clock; positivity

theorem clock_tendsto : Tendsto clock atTop (𝓝[≠] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,.of_forall (fun n => (clock_pos n).ne')⟩

def replicatedRatio (n : ℕ) : ℝ :=
  ratio (productPartition (n+1) (1/(clock n)^2)) (clock n)

theorem replicated_log_identity (n : ℕ) :
    Real.log (replicatedRatio n)= -8*FourCubeThermalMixedDifference.thermalResponse (clock n) := by
  rw [replicatedRatio,product_log_ratio,FourCubeThermalMixedDifference.thermalResponse]
  have hn : (n:ℝ)+1≠0 := by positivity
  simp only [Nat.cast_add,Nat.cast_one,clock]
  field_simp [hn]
  <;> ring

theorem replicated_log_limit : Tendsto (fun n => Real.log (replicatedRatio n)) atTop
    (𝓝 (-8*FourCubeThermalMixedDifference.c)) := by
  simpa only [replicated_log_identity,Function.comp_def] using
    (FourCubeThermalMixedDifference.actual_thermal_mixed_limit.comp clock_tendsto).const_mul (-8)

theorem replicated_ratio_limit : Tendsto replicatedRatio atTop
    (𝓝 (Real.exp (-8*FourCubeThermalMixedDifference.c))) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp replicated_log_limit
  apply h.congr'
  filter_upwards with n
  exact Real.exp_log (ratio_positive _ (productPartition_pos (n+1) _) _)

theorem replicated_limit_lt_one : Real.exp (-8*FourCubeThermalMixedDifference.c)<1 := by
  exact Real.exp_lt_one_iff.mpr (by linarith [FourCubeThermalMixedDifference.c_positive])

theorem replicated_not_tendsto_one : ¬ Tendsto replicatedRatio atTop (𝓝 (1:ℝ)) := by
  intro h
  exact (ne_of_lt replicated_limit_lt_one) (tendsto_nhds_unique replicated_ratio_limit h)

/-- The interaction vanishes for EVERY fixed finite number of cells. -/
theorem fixed_volume_ratio_limit (m : ℕ) :
    Tendsto (fun t : ℝ => ratio (productPartition m (1/t^2)) t) (𝓝[≠] 0) (𝓝 (1:ℝ)) := by
  have hi : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 (0:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ht := ((hi.mul FourCubeThermalMixedDifference.actual_thermal_mixed_limit).const_mul (-8*(m:ℝ)))
  have he : ∀ t : ℝ,Real.log (ratio (productPartition m (1/t^2)) t)=
      -8*(m:ℝ)*(t*FourCubeThermalMixedDifference.thermalResponse t) := by
    intro t
    rw [product_log_ratio,FourCubeThermalMixedDifference.thermalResponse]
    by_cases hz : t=0
    · subst t; simp [cornerSum]
    · field_simp [hz]
      <;> ring
  have hl : Tendsto (fun t : ℝ => Real.log (ratio (productPartition m (1/t^2)) t))
      (𝓝[≠] 0) (𝓝 (0:ℝ)) := by
    simpa only [he,zero_mul,mul_zero] using ht
  have hx := Real.continuous_exp.continuousAt.tendsto.comp hl
  simp only [Real.exp_zero] at hx
  apply hx.congr'
  filter_upwards with t
  exact Real.exp_log (ratio_positive _ (productPartition_pos m _) _)

/-- Every fixed volume converges, but convergence is NOT uniform in the block count. -/
theorem not_uniform_in_volume :
    ¬ TendstoUniformly (fun n (m : ℕ) =>
      ratio (productPartition m (1/(clock n)^2)) (clock n)) (fun _ => (1:ℝ)) atTop := by
  intro h
  apply replicated_not_tendsto_one
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp h ε hε] with n hn
  simpa only [replicatedRatio,dist_comm] using hn (n+1)

/-- Even n-dependent pairwise boundary counterterms cannot cancel this limit. -/
theorem pairwise_counterterm_limit (A B C : ℕ → ℝ → ℝ → ℝ) :
    Tendsto (fun n => ratio (fun x y z => Real.exp (A n x y+B n y z+C n z x)*
      productPartition (n+1) (1/(clock n)^2) x y z) (clock n)) atTop
      (𝓝 (Real.exp (-8*FourCubeThermalMixedDifference.c))) := by
  apply replicated_ratio_limit.congr'
  filter_upwards with n
  exact (FourCubeProjectiveInteraction.ratio_pairwise_invariant _
    (productPartition_pos (n+1) _) (A n) (B n) (C n) (clock n)).symm
end OperatorDerivativeRewrite.Foundation.FourCubeReplicatedInteraction
