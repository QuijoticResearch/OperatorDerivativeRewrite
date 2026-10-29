import Foundation.FourCubeOddIntegral

/-! Full-Haar cutoff removal at the actual first odd-correction scale. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeOddFullPartition
open QuaternionSU2Representation FourCubePinnedHaar FourCubePinnedCoercivity
open FourCubePinnedConcentration FourCubeHemisphereCoercivity FourCubeBoundaryCoercivity
open FourCubeScaledBoundaryControl FourCubeHaarPartitionAsymptotic FourCubeOddIntegral
open FourCubeMovingOddAction

def outsidePartition (t x y z : ℝ) : ℝ :=
  ∫ U in localStateDomainᶜ,Real.exp (-perturbedAction (movingBoundary t x y z) U/t^2) ∂pinnedHaar

theorem outside_action_gap (U : PinnedState) (hU : U∈localStateDomainᶜ) : 1/12 ≤ pinnedAction U := by
  have hh := outside_localStateDomain_subset hU
  obtain ⟨e,he⟩ := Set.mem_iUnion.mp hh
  change (1/4 : ℝ) ≤ defect (U e) at he
  linarith [pinned_coordinate_bound U e]

theorem outside_weight_bound (t x y z : ℝ) (ht : t ≠ 0) (U : PinnedState)
    (hU : U∈localStateDomainᶜ) :
    Real.exp (-perturbedAction (movingBoundary t x y z) U/t^2) ≤
      Real.exp (216*(x^2+y^2+z^2))*Real.exp (-1/(36*t^2)) := by
  have hβ : 0 ≤ 1/t^2 := by positivity
  have hc : (1/t^2)*t^2=1 := by field_simp
  have hb := mul_le_mul_of_nonneg_left (perturbedAction_lower (movingBoundary t x y z) U) hβ
  have hs := mul_le_mul_of_nonneg_left (outside_action_gap U hU) hβ
  have hcost := scaled_boundaryCost (1/t^2) t hβ hc x y z
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : -perturbedAction (movingBoundary t x y z) U/t^2=
      -(1/t^2)*perturbedAction (movingBoundary t x y z) U := by ring
  rw [he,show -1/(36*t^2)= -(1/t^2)/36 by field_simp [ht] <;> ring]
  nlinarith

theorem outsidePartition_nonneg (t x y z : ℝ) : 0 ≤ outsidePartition t x y z :=
  integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem outsidePartition_bound (t x y z : ℝ) (ht : t ≠ 0) : outsidePartition t x y z ≤
    Real.exp (216*(x^2+y^2+z^2))*Real.exp (-1/(36*t^2)) := by
  let C := Real.exp (216*(x^2+y^2+z^2))*Real.exp (-1/(36*t^2))
  have hi : Integrable (fun U : PinnedState => Real.exp (-perturbedAction (movingBoundary t x y z) U/t^2)) pinnedHaar := by
    convert! perturbed_boltzmann_integrable (1/t^2) (movingBoundary t x y z) using 1
    funext U
    congr 1
    ring
  unfold outsidePartition
  calc
    _ ≤ ∫ _ in localStateDomainᶜ,C ∂pinnedHaar := by
      apply integral_mono_ae hi.integrableOn (integrable_const C)
      filter_upwards [ae_restrict_mem localStateDomain_measurable.compl] with U hU
      exact outside_weight_bound t x y z ht U hU
    _ ≤ C := by
      rw [setIntegral_const,smul_eq_mul]
      exact mul_le_of_le_one_left (by dsimp [C]; positivity) measureReal_le_one

theorem gaussian_tail_power94 :
    Tendsto (fun t : ℝ => Real.exp (-1/(36*t^2))/|t|^94) (𝓝[≠] 0) (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => 1/(36*t^2)) (𝓝[≠] 0) atTop := by
    convert! inverse_square_tendsto.const_mul_atTop (by norm_num : 0 < (1/36 : ℝ)) using 1
    funext t
    ring
  have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 47).comp hu).const_mul ((36 : ℝ)^47)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have he : |t|^94=(t^2)^47 := by rw [← sq_abs]; ring
  simp only [Function.comp_def,neg_div]
  rw [he]
  field_simp [ht] <;> ring

theorem outside_pair_scaled_tendsto_zero (x y z : ℝ) :
    Tendsto (fun t : ℝ => (outsidePartition t x y z+outsidePartition (-t) x y z)/|t|^94)
      (𝓝[≠] 0) (𝓝 0) := by
  have hh := gaussian_tail_power94.const_mul (2*Real.exp (216*(x^2+y^2+z^2)))
  simp only [mul_zero] at hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => div_nonneg
    (add_nonneg (outsidePartition_nonneg t x y z) (outsidePartition_nonneg (-t) x y z)) (by positivity))) ?_ hh
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp := outsidePartition_bound t x y z ht
  have hm := outsidePartition_bound (-t) x y z (neg_ne_zero.mpr ht)
  simp only [neg_sq] at hm
  have hs := add_le_add hp hm
  have hd := div_le_div_of_nonneg_right hs (show 0 ≤ |t|^94 by positivity)
  convert! hd using 1 <;> ring

theorem outside_odd_scaled_tendsto_zero (x y z : ℝ) :
    Tendsto (fun t : ℝ => (outsidePartition t x y z-outsidePartition (-t) x y z)/(2*t*|t|^93))
      (𝓝[≠] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (outside_pair_scaled_tendsto_zero x y z)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp := outsidePartition_nonneg t x y z
  have hm := outsidePartition_nonneg (-t) x y z
  have hd : |2*t*|t|^93|=2*|t|^94 := by rw [abs_mul,abs_mul,abs_pow,abs_abs]; norm_num; ring
  rw [Real.norm_eq_abs,abs_div,hd]
  have ha : |outsidePartition t x y z-outsidePartition (-t) x y z| ≤
      outsidePartition t x y z+outsidePartition (-t) x y z := by
    simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hp,abs_of_nonneg hm] using abs_sub_le (outsidePartition t x y z) 0 (outsidePartition (-t) x y z)
  have ht' : t ≠ 0 := ht
  have hpos : 0 < |t|^94 := pow_pos (abs_pos.mpr ht') _
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hpos)).mpr
  have hc : (outsidePartition t x y z+outsidePartition (-t) x y z)/|t|^94*(2*|t|^94)=
      2*(outsidePartition t x y z+outsidePartition (-t) x y z) := by
    field_simp [hpos.ne'] <;> ring
  rw [hc]
  linarith

theorem full_partition_split (t x y z : ℝ) :
    pinnedPartition (1/t^2) (movingBoundary t x y z)=movingLocalPartition t x y z+outsidePartition t x y z := by
  have hi : Integrable (fun U : PinnedState => Real.exp (-perturbedAction (movingBoundary t x y z) U/t^2)) pinnedHaar := by
    convert! perturbed_boltzmann_integrable (1/t^2) (movingBoundary t x y z) using 1
    funext U
    congr 1
    ring
  have hh := integral_add_compl localStateDomain_measurable hi
  have he : pinnedPartition (1/t^2) (movingBoundary t x y z)=
      ∫ U : PinnedState,Real.exp (-perturbedAction (movingBoundary t x y z) U/t^2) ∂pinnedHaar := by
    unfold pinnedPartition weight
    apply integral_congr_ae
    filter_upwards with U
    unfold perturbedAction boundaryAction
    congr 1
    ring
  exact he.trans hh.symm

theorem actual_full_partition_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (pinnedPartition (1/t^2) (movingBoundary t x y z)-
      pinnedPartition (1/t^2) (movingBoundary (-t) x y z))/(2*t*|t|^93)) (𝓝[≠] 0)
      (𝓝 (∫ Y : Coordinates,firstDensity x y z Y)) := by
  have hh := (actual_cutoff_partition_odd_limit x y z).add (outside_odd_scaled_tendsto_zero x y z)
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards with t
  rw [full_partition_split,show 1/t^2=1/(-t)^2 by rw [neg_sq],full_partition_split]
  ring

theorem actual_normalized_partition_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (normalizedPartition (1/t^2) (movingBoundary t x y z)-
      normalizedPartition (1/t^2) (movingBoundary (-t) x y z))/(2*t)) (𝓝[≠] 0)
      (𝓝 ((∫ Y : Coordinates,firstDensity x y z Y)/
        (∫ Y : Coordinates,FourCubeHaarLaplaceDensity.gaussianDensity Y))) := by
  have hh := (actual_full_partition_odd_limit x y z).div actual_normalizer_asymptotic
    FourCubeHaarLaplaceDensity.gaussianDensity_integral_positive.ne'
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Pi.div_apply]
  unfold normalizedPartition
  field_simp [ht,abs_ne_zero.mpr ht,(normalizer_positive (1/t^2)).ne'] <;> ring
end OperatorDerivativeRewrite.Foundation.FourCubeOddFullPartition
