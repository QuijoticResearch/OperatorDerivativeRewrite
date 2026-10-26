import Foundation.IBMClockVacuumPast
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! Strong original-clock Bessel smoothing limits for ACTUAL B(abs(W_t)).
All sufficiently large REAL smoothing orders can fail completed right-past
adaptation, with a uniform positive distance from every adapted L2 variable,
despite genuine native Gaussian clock differentiability. Physical IBM calculus
and full all-time intrinsic observability are separate obligations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockSmoothingPast
open InfiniteGaussian GaussianClockValueOperators GaussianClockSpectralPowers
open IBMClockNativeSmoothing IBMClockFractionalCalculus IBMClockFractionalDomain
open IBMRandomTimeHilbert IBMTimeAveragedObservable IBMClockVacuumPast
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def smooth (β : ℝ≥0) (T : ℝ≥0) (hT : 0 < T) : Field :=
  regularizedEndpoint (β:ℝ) β.coe_nonneg T hT

theorem smooth_projection (β : ℝ≥0) (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    project n (smooth β T hT) = (((n:ℝ)+1)⁻¹)^(β:ℝ) • project n (randomSourceL2 T) := by
  unfold smooth regularizedEndpoint
  rw [bessel_projection]
  have he : (-2*(β:ℝ))/2 = -(β:ℝ) := by ring
  rw [he,Real.rpow_neg_eq_inv_rpow]

private theorem inverse_bounds (n : ℕ) : 0 ≤ ((n:ℝ)+1)⁻¹ ∧ ((n:ℝ)+1)⁻¹ ≤ 1 := by
  constructor
  · positivity
  · exact (inv_le_one₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem smooth_error_projection (β : ℝ≥0) (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    project n (smooth β T hT-project 0 (randomSourceL2 T)) =
      if n=0 then 0 else (((n:ℝ)+1)⁻¹)^(β:ℝ) • project n (randomSourceL2 T) := by
  rw [map_sub,smooth_projection,project_comp]
  by_cases hn : n=0
  · subst n; simp
  · simp only [if_neg hn,sub_zero]

theorem smooth_error_bound (β : ℝ≥0) (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    ‖project n (smooth β T hT-project 0 (randomSourceL2 T))‖^2 ≤
      ‖project n (randomSourceL2 T)‖^2 := by
  rw [smooth_error_projection]
  split_ifs
  · simp only [norm_zero,zero_pow (by norm_num : 2≠0)]; positivity
  · rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    have hp : ((((n:ℝ)+1)⁻¹)^(β:ℝ))^2 ≤ 1 := by
      have hb : 0 ≤ (((n:ℝ)+1)⁻¹)^(β:ℝ) := Real.rpow_nonneg (inverse_bounds n).1 _
      have hl := Real.rpow_le_one (inverse_bounds n).1 (inverse_bounds n).2 β.coe_nonneg
      exact pow_le_one₀ (n := 2) hb hl
    exact mul_le_of_le_one_left (sq_nonneg _) hp

theorem smooth_error_sector_tendsto (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun β => ‖project n (smooth β T hT-project 0 (randomSourceL2 T))‖^2)
      atTop (𝓝 0) := by
  by_cases hn : n=0
  · simp only [smooth_error_projection,if_pos hn,norm_zero,zero_pow (by norm_num : 2≠0)]
    exact tendsto_const_nhds
  · have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hi : ((n:ℝ)+1)⁻¹ < 1 :=
      (inv_lt_one₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).2 (by linarith)
    have hc : Tendsto (fun β : ℝ≥0 => (β:ℝ)) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b.toNNReal] with β hN
      exact (le_max_left b 0).trans hN
    have ht := (tendsto_rpow_atTop_of_base_lt_one ((n:ℝ)+1)⁻¹
      (by linarith [(inverse_bounds n).1]) hi).comp hc
    have h := (ht.pow 2).mul_const (‖project n (randomSourceL2 T)‖^2)
    simpa only [Function.comp_def,smooth_error_projection,if_neg hn,norm_smul,mul_pow,Real.norm_eq_abs,
      sq_abs,zero_pow (by norm_num : 2≠0),zero_mul] using h

theorem smooth_tendsto_vacuum (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun β => smooth β T hT) atTop (𝓝 (project 0 (randomSourceL2 T))) := by
  have ht := tendsto_tsum_of_dominated_convergence (project_hasSum_norm_sq (randomSourceL2 T)).summable
    (fun n => smooth_error_sector_tendsto n T hT)
    (Eventually.of_forall fun β n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact smooth_error_bound β n T hT)
  have he (β : ℝ≥0) : (∑' n, ‖project n (smooth β T hT-project 0 (randomSourceL2 T))‖^2) =
      ‖smooth β T hT-project 0 (randomSourceL2 T)‖^2 := (project_hasSum_norm_sq _).tsum_eq
  simp only [he,tsum_zero] at ht
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hr

theorem joint_smooth_tendsto_vacuum (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun β => jointRealization (smooth β T hT)) atTop
      (𝓝 (jointRealization (project 0 (randomSourceL2 T)))) :=
  jointRealization.continuous.tendsto _ |>.comp (smooth_tendsto_vacuum T hT)

theorem smooth_eventually_not_rightPast (T : ℝ≥0) (hT : 0 < T)
    (hp : jointRealization (project 0 (randomSourceL2 T)) ∉ IBMIntrinsicRightGerm.rightPast T) :
    ∀ᶠ β in atTop, jointRealization (smooth β T hT) ∉ IBMIntrinsicRightGerm.rightPast T := by
  have hc : IsClosed (IBMIntrinsicRightGerm.rightPast T : Set JointL2) := by
    exact Submodule.isClosed_orthogonal _
  exact (joint_smooth_tendsto_vacuum T hT).eventually (hc.isOpen_compl.mem_nhds hp)

theorem smooth_native_clock_domain (β : ℝ≥0) (hN : 1 ≤ β) (T : ℝ≥0) (hT : 0 < T) :
    jointRealization (smooth β T hT) ∈ IBMIntrinsicOperators.clockDerivative.domain := by
  apply (actual_native_smoothing_threshold (β:ℝ) β.coe_nonneg T hT).2
  have h : (1:ℝ) ≤ β := hN
  linarith

theorem exists_actual_eventual_smoothing_failure : ∃ (T : ℝ≥0) (hT : 0 < T) (β₀ : ℝ≥0),
    jointRealization (randomSourceL2 T) ∈ IBMIntrinsicRightGerm.rightPast T ∧
    ∀ β ≥ β₀, jointRealization (smooth β T hT) ∉ IBMIntrinsicRightGerm.rightPast T ∧
      jointRealization (smooth β T hT) ∈ IBMIntrinsicOperators.clockDerivative.domain := by
  obtain ⟨T,hT,ha,hp,_⟩ := exists_actual_adapted_clock_projection_failure
  obtain ⟨M,hM⟩ := eventually_atTop.1 (smooth_eventually_not_rightPast T hT hp)
  refine ⟨T,hT,max M 1,ha,?_⟩
  intro β hN
  exact ⟨hM β ((le_max_left M 1).trans hN),
    smooth_native_clock_domain β ((le_max_right M 1).trans hN) T hT⟩

theorem smooth_zero (T : ℝ≥0) (hT : 0 < T) : smooth 0 T hT = randomSourceL2 T := by
  apply eq_of_clock_projections
  intro n
  change project n (smooth 0 T hT) = project n (randomSourceL2 T)
  rw [smooth_projection]
  simp

theorem smooth_native_iff (β : ℝ≥0) (T : ℝ≥0) (hT : 0 < T) :
    jointRealization (smooth β T hT) ∈ IBMIntrinsicOperators.clockDerivative.domain ↔ 1/4 < (β:ℝ) :=
  actual_native_smoothing_threshold β β.coe_nonneg T hT

theorem causal_smooth_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun β => (IBMIntrinsicRightGerm.rightPast T).starProjection
      (jointRealization (smooth β T hT))) atTop
      (𝓝 ((IBMIntrinsicRightGerm.rightPast T).starProjection
        (jointRealization (project 0 (randomSourceL2 T))))) :=
  (IBMIntrinsicRightGerm.rightPast T).starProjection.continuous.tendsto _ |>.comp
    (joint_smooth_tendsto_vacuum T hT)

theorem positive_causal_error (T : ℝ≥0) (hT : 0 < T)
    (hp : jointRealization (project 0 (randomSourceL2 T)) ∉ IBMIntrinsicRightGerm.rightPast T) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in atTop,
      c ≤ ‖jointRealization (smooth β T hT)-(IBMIntrinsicRightGerm.rightPast T).starProjection
        (jointRealization (smooth β T hT))‖ := by
  let V := jointRealization (project 0 (randomSourceL2 T))
  let P := (IBMIntrinsicRightGerm.rightPast T).starProjection
  have hne : V-P V ≠ 0 := by
    intro hz
    apply hp
    have he := sub_eq_zero.mp hz
    change V ∈ IBMIntrinsicRightGerm.rightPast T
    rw [he]
    exact Submodule.starProjection_apply_mem _ _
  have hn : 0 < ‖V-P V‖ := norm_pos_iff.mpr hne
  have ht := ((joint_smooth_tendsto_vacuum T hT).sub (causal_smooth_tendsto T hT)).norm
  refine ⟨‖V-P V‖/2,half_pos hn,?_⟩
  exact (ht.eventually (eventually_gt_nhds (half_lt_self hn))).mono fun β hβ => hβ.le

private theorem projection_error_le (U : Submodule ℝ JointL2) [U.HasOrthogonalProjection]
    (Y G : JointL2) (hG : G ∈ U) : ‖Y-U.starProjection Y‖ ≤ ‖Y-G‖ := by
  have hg : U.starProjection G = G := U.starProjection_eq_self_iff.2 hG
  have he : Uᗮ.starProjection (Y-G) = Y-U.starProjection Y := by
    rw [Submodule.starProjection_orthogonal]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,map_sub,hg]
    abel
  rw [← he]
  exact Uᗮ.norm_starProjection_apply_le (Y-G)

theorem positive_distance_from_all_adapted (T : ℝ≥0) (hT : 0 < T)
    (hp : jointRealization (project 0 (randomSourceL2 T)) ∉ IBMIntrinsicRightGerm.rightPast T) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in atTop, ∀ G ∈ IBMIntrinsicRightGerm.rightPast T,
      c ≤ ‖jointRealization (smooth β T hT)-G‖ := by
  obtain ⟨c,hc,he⟩ := positive_causal_error T hT hp
  refine ⟨c,hc,he.mono ?_⟩
  intro β hβ G hG
  exact hβ.trans (projection_error_le (IBMIntrinsicRightGerm.rightPast T) (jointRealization (smooth β T hT)) G hG)

theorem exists_actual_uniform_smoothing_obstruction :
    ∃ (T : ℝ≥0) (hT : 0 < T) (B : ℝ≥0) (c : ℝ), 0 < c ∧
      jointRealization (randomSourceL2 T) ∈ IBMIntrinsicRightGerm.rightPast T ∧
      ∀ β ≥ B, jointRealization (smooth β T hT) ∈ IBMIntrinsicOperators.clockDerivative.domain ∧
        ∀ G ∈ IBMIntrinsicRightGerm.rightPast T, c ≤ ‖jointRealization (smooth β T hT)-G‖ := by
  obtain ⟨T,hT,ha,hp,_⟩ := exists_actual_adapted_clock_projection_failure
  obtain ⟨c,hc,he⟩ := positive_distance_from_all_adapted T hT hp
  obtain ⟨M,hM⟩ := eventually_atTop.1 he
  refine ⟨T,hT,max M 1,c,hc,ha,?_⟩
  intro β hβ
  exact ⟨smooth_native_clock_domain β ((le_max_right M 1).trans hβ) T hT,
    hM β ((le_max_left M 1).trans hβ)⟩

end OperatorDerivativeRewrite.Foundation.IBMClockSmoothingPast
