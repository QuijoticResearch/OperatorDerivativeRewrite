import Foundation.IBMSpatialClockEnergy

/-! Deterministic compact-clock mesh control and the countable AE bridge to
the original Gaussian representatives. No random supremum law is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockGridPath
open InfiniteGaussian IBMUniformClockGridEnergy

theorem grid_mem (H : ℝ≥0) (N i : ℕ) (hi : i ≤ N+1) : grid (H/(N+1)) i ∈ Icc 0 H := by
  constructor
  · exact zero_le
  · apply NNReal.coe_le_coe.mp
    simp only [grid,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_natCast]
    have hp : 0 < (N+1:ℝ) := by positivity
    calc
      (H:ℝ)/(N+1)*i ≤ (H:ℝ)/(N+1)*(N+1) := by gcongr; exact_mod_cast hi
      _ = H := div_mul_cancel₀ _ hp.ne'

def pathMesh (f : C(ℝ≥0,ℝ)) (H : ℝ≥0) (N : ℕ) : ℝ :=
  (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
    (fun i => |f (grid (H/(N+1)) (i+1))-f (grid (H/(N+1)) i)|)

theorem pathMesh_nonneg (f : C(ℝ≥0,ℝ)) (H : ℝ≥0) (N : ℕ) : 0 ≤ pathMesh f H N :=
  (abs_nonneg _).trans (Finset.le_sup'
    (fun i => |f (grid (H/(N+1)) (i+1))-f (grid (H/(N+1)) i)|)
      (Finset.mem_range.mpr (Nat.zero_lt_succ N)))

theorem increment_le_pathMesh (f : C(ℝ≥0,ℝ)) (H : ℝ≥0) (N i : ℕ) (hi : i < N+1) :
    |f (grid (H/(N+1)) (i+1))-f (grid (H/(N+1)) i)| ≤ pathMesh f H N :=
  Finset.le_sup' (fun i => |f (grid (H/(N+1)) (i+1))-f (grid (H/(N+1)) i)|) (Finset.mem_range.mpr hi)

theorem pathMesh_tendsto (f : C(ℝ≥0,ℝ)) (H : ℝ≥0) : Tendsto (pathMesh f H) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun N => ha.trans_le (pathMesh_nonneg f H N)
  · intro ε hε
    obtain ⟨δ,hδ,hu⟩ := Metric.uniformContinuousOn_iff.mp
      ((isCompact_Icc : IsCompact (Icc (0:ℝ≥0) H)).uniformContinuousOn_of_continuous f.continuous.continuousOn) ε hε
    have ht : Tendsto (fun N : ℕ => (H:ℝ)/(N+1:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with N hN
    apply (Finset.sup'_lt_iff _).mpr
    intro i hi
    have hin := Finset.mem_range.mp hi
    have hp : 0 < (N+1:ℝ) := by positivity
    have hd : dist (grid (H/(N+1)) (i+1)) (grid (H/(N+1)) i) < δ := by
      rw [NNReal.dist_eq]
      simp only [grid,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_natCast,Nat.cast_add,Nat.cast_one,
        NNReal.coe_add,NNReal.coe_one]
      have he : (H:ℝ)/(N+1)*(i+1)-(H:ℝ)/(N+1)*i = (H:ℝ)/(N+1) := by ring
      rw [he]
      exact (abs_of_nonneg (by positivity)).trans_lt hN
    simpa only [Real.dist_eq] using hu _ (grid_mem H N (i+1) hin) _ (grid_mem H N i (by omega)) hd

theorem path_bound (f : C(ℝ≥0,ℝ)) (H : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Icc 0 H, |f t| ≤ M := by
  obtain ⟨M,hM⟩ := (isCompact_Icc.image (continuous_abs.comp f.continuous)).bddAbove
  refine ⟨max M 1,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _),?_⟩
  intro t ht
  exact (hM ⟨t,ht,rfl⟩).trans (le_max_left _ _)

theorem clock_grid_ae (H : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct, ∀ N i : ℕ,
    IBMConstructedSources.clockPath Y (grid (H/(N+1)) i) =
      GaussianTimeProcess.process (grid (H/(N+1)) i) Y :=
  ae_all_iff.mpr fun N => ae_all_iff.mpr fun i => IBMConstructedSources.clockPath_coordinate_ae _

end OperatorDerivativeRewrite.Foundation.IBMClockGridPath
