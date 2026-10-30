import Foundation.CubeFiniteGapComparison

/-! Coupling-uniform finite-cube contraction in the actual stationary L2 space. -/
noncomputable section
open MeasureTheory Filter Topology
namespace OperatorDerivativeRewrite.Foundation.CubeFiniteStationaryGap
open CubeFiniteGapComparison CubeRankOneComparison CubeBoundaryChartL2 CubeSlabGround
open CubeChordOperator CubeHaarOperator CubeGroundUnitary CubeSlabL2 CubeLimitComplementGap

def finiteConstant : ℝ := 24/25

theorem finiteConstant_bounds : 0 < finiteConstant ∧ finiteConstant < 1 := by norm_num [finiteConstant]

theorem chord_contraction :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ∀ f : ChordL2,
      inner ℝ f (chordGround (ground (1/t^2)))=0 ->
        ‖chordOperator (ground (1/t^2)) f‖ ≤ finiteConstant*‖f‖ := by
  have hp := rate_tendsto.eventually (eventually_gt_nhds gapConstant_bounds.1)
  have hu := rate_tendsto.eventually
    (eventually_lt_nhds (by norm_num [gapConstant,finiteConstant] : gapConstant < finiteConstant))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds,hp,hu]
    with t ht h1 hp hu
  intro f hf
  have hb := CubeRankOneComparison.complement_bound (chordOperator (ground (1/t^2)))
    (chordGround (ground (1/t^2))) (backward t ht CubeGaussianGroundEigenvector.stateClass)
    (rate t) vacuumCoefficient (chordOperator_selfadjoint _) (chordGround_norm _)
    (chordGround_fixed _) hp.le (hu.trans finiteConstant_bounds.2)
    (fun x => (finite_form t ht h1 x).2) (fun x => (finite_form t ht h1 x).1) f hf
  exact hb.trans (mul_le_mul_of_nonneg_right hu.le (norm_nonneg f))

theorem haar_contraction :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ∀ F : HaarL2,
      inner ℝ F (groundVector (ground (1/t^2)))=0 ->
        ‖haarOperator (ground (1/t^2)) F‖ ≤ finiteConstant*‖F‖ := by
  filter_upwards [chord_contraction] with t ht
  intro F hf
  have hp : inner ℝ (pull F) (chordGround (ground (1/t^2)))=0 := by
    change inner ℝ (lift.adjoint F) (chordGround (ground (1/t^2)))=0
    rw [ContinuousLinearMap.adjoint_inner_left,lift_chordGround]
    exact hf
  have hb := ht (pull F) hp
  have he : ‖haarOperator (ground (1/t^2)) F‖=
      ‖chordOperator (ground (1/t^2)) (pull F)‖ := by
    rw [factorization]
    change ‖lift (chordOperator (ground (1/t^2)) (pull F))‖=_
    exact lift_norm _
  rw [he]
  exact hb.trans (mul_le_mul_of_nonneg_left (pull_contraction F) finiteConstant_bounds.1.le)

theorem stationary_contraction :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ∀ f : StateL2 (ground (1/t^2)),
      (∫ U,f U ∂(ground (1/t^2)).stationary)=0 ->
        ‖operator (ground (1/t^2)) f‖ ≤ finiteConstant*‖f‖ := by
  filter_upwards [haar_contraction] with t ht
  intro f hf
  have hc := (centered_iff (ground (1/t^2)) f).mp hf
  have hb := ht (unitary (ground (1/t^2)) f) hc
  have he : haarOperator (ground (1/t^2)) (unitary (ground (1/t^2)) f)=
      unitary (ground (1/t^2)) (operator (ground (1/t^2)) f) := by
    rw [haarOperator_apply,(unitary _).symm_apply_apply]
  rw [he,(unitary _).norm_map,(unitary _).norm_map] at hb
  exact hb

theorem stationary_mean_zero_preserved (t : ℝ) (f : StateL2 (ground (1/t^2)))
    (hf : (∫ U,f U ∂(ground (1/t^2)).stationary)=0) :
    (∫ U,operator (ground (1/t^2)) f U ∂(ground (1/t^2)).stationary)=0 := by
  apply (centered_iff _ _).mpr
  have he : haarOperator (ground (1/t^2)) (unitary (ground (1/t^2)) f)=
      unitary (ground (1/t^2)) (operator (ground (1/t^2)) f) := by
    rw [haarOperator_apply,(unitary _).symm_apply_apply]
  rw [← he]
  have h := ContinuousLinearMap.adjoint_inner_right (haarOperator (ground (1/t^2)))
    (unitary (ground (1/t^2)) f) (groundVector (ground (1/t^2)))
  rw [haarOperator_selfadjoint,groundVector_fixed] at h
  exact h.symm.trans ((centered_iff _ _).mp hf)

theorem stationary_iterates :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ∀ n : ℕ, ∀ f : StateL2 (ground (1/t^2)),
      (∫ U,f U ∂(ground (1/t^2)).stationary)=0 ->
        ‖((operator (ground (1/t^2)))^n) f‖ ≤ finiteConstant^n*‖f‖ := by
  filter_upwards [stationary_contraction] with t ht
  intro n
  induction n with
  | zero =>
    intro f hf
    simp
  | succ n ih =>
    intro f hf
    rw [pow_succ (operator (ground (1/t^2))) n]
    change ‖((operator (ground (1/t^2)))^n) (operator (ground (1/t^2)) f)‖ ≤
      finiteConstant^(n+1)*‖f‖
    calc
      _ ≤ finiteConstant^n*‖operator (ground (1/t^2)) f‖ :=
        ih _ (stationary_mean_zero_preserved t f hf)
      _ ≤ finiteConstant^n*(finiteConstant*‖f‖) :=
        mul_le_mul_of_nonneg_left (ht f hf) (pow_nonneg finiteConstant_bounds.1.le n)
      _ = _ := by rw [pow_succ finiteConstant n]; ring

end OperatorDerivativeRewrite.Foundation.CubeFiniteStationaryGap
