import Foundation.GaussianClockValueOperators
import Foundation.GaussianObservedSecondRegularization
import Foundation.GaussianPotentialIteration

/-! Actual joint SOURCE/CLOCK spectral truncations and their common-number
regularization, on the original source-valued Gaussian L2 space. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianClockSourceSpectral
open InfiniteGaussian GaussianNumberSectors GaussianClockValueOperators
open GaussianObservedSecondRegularization
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def sourceLift (B : GaussianL2 →L[ℝ] GaussianL2) : Field →L[ℝ] Field :=
  B.compLpL 2 gaussianProduct

theorem sourceLift_test (B : GaussianL2 →L[ℝ] GaussianL2) (L : GaussianL2 →L[ℝ] ℝ) (f : Field) :
    L.compLpL 2 gaussianProduct (sourceLift B f) =
      (L.comp B).compLpL 2 gaussianProduct f := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (sourceLift B f),B.coeFn_compLpL f,
    (L.comp B).coeFn_compLpL f] with ω hL hB hC
  change sourceLift B f ω = B (f ω) at hB
  rw [hL,hB,hC]
  rfl

/-- Source-value and clock-probability operators act on distinct actual factors. -/
theorem source_clock_commute (B A : GaussianL2 →L[ℝ] GaussianL2) (f : Field) :
    clockLift A (sourceLift B f) = sourceLift B (clockLift A f) := by
  apply eq_of_all_tests
  intro L
  rw [clockLift_test,sourceLift_test,sourceLift_test,clockLift_test]

theorem sourceLift_contraction (B : GaussianL2 →L[ℝ] GaussianL2)
    (hB : ∀ f, ‖B f‖ ≤ ‖f‖) (f : Field) : ‖sourceLift B f‖ ≤ ‖f‖ := by
  have h : ‖sourceLift B f‖ ≤ (1 : ℝ) * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [B.coeFn_compLpL f] with ω hω
    change sourceLift B f ω = B (f ω) at hω
    rw [hω,one_mul]
    exact hB _
  simpa only [one_mul] using h

def sourceTruncation (N : ℕ) : Field →L[ℝ] Field := sourceLift (truncation N)

theorem sourceTruncation_norm_le (N : ℕ) (f : Field) : ‖sourceTruncation N f‖ ≤ ‖f‖ :=
  sourceLift_contraction _ (GaussianPredictableChaosCore.scalar_truncation_norm_le N) f

theorem clockTruncation_norm_le (N : ℕ) (f : Field) :
    ‖clockLift (truncation N) f‖ ≤ ‖f‖ := by
  have hN : ‖truncation N‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa only [one_mul] using GaussianPredictableChaosCore.scalar_truncation_norm_le N x)
  exact (clockLift_norm_le _ f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hN (norm_nonneg f))

theorem sourceTruncation_tendsto (f : Field) :
    Tendsto (fun N => sourceTruncation N f) atTop (𝓝 f) := by
  apply BochnerL2Dominated.tendsto_of_ae_norm_bound
  · intro N
    filter_upwards [(truncation N).coeFn_compLpL f] with ω hω
    change sourceTruncation N f ω = truncation N (f ω) at hω
    rw [hω]
    exact GaussianPredictableChaosCore.scalar_truncation_norm_le N _
  · filter_upwards [ae_all_iff.mpr (fun N => (truncation N).coeFn_compLpL f)] with ω hω
    change ∀ N, sourceTruncation N f ω = truncation N (f ω) at hω
    simp only [hω]
    exact truncation_tendsto _

def jointTruncation (M N : ℕ) : Field →L[ℝ] Field :=
  (sourceTruncation M).comp (clockLift (truncation N))

def block (m n : ℕ) : Field →L[ℝ] Field :=
  (sourceLift (projection m)).comp (clockLift (projection n))

theorem jointTruncation_norm_le (M N : ℕ) (f : Field) : ‖jointTruncation M N f‖ ≤ ‖f‖ :=
  (sourceTruncation_norm_le M _).trans (clockTruncation_norm_le N f)

theorem sourceTruncation_eq_sum (M : ℕ) (f : Field) :
    sourceTruncation M f = ∑ m ∈ Finset.range (M + 1), sourceLift (projection m) f := by
  apply Lp.ext
  filter_upwards [(truncation M).coeFn_compLpL f,
    Lp.coeFn_fun_finsetSum (Finset.range (M + 1)) (fun m => sourceLift (projection m) f),
    ae_all_iff.mpr (fun m => (projection m).coeFn_compLpL f)] with ω ht hs hp
  change sourceTruncation M f ω = truncation M (f ω) at ht
  change ∀ m, sourceLift (projection m) f ω = projection m (f ω) at hp
  rw [ht,hs]
  simp only [truncation,ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun m _ => (hp m).symm)

/-- Actual rectangular partial sums of the source-resolved (m,n) blocks. -/
theorem jointTruncation_eq_sum (M N : ℕ) (f : Field) :
    jointTruncation M N f = ∑ m ∈ Finset.range (M + 1),
      ∑ n ∈ Finset.range (N + 1), block m n f := by
  change sourceTruncation M (clockLift (truncation N) f) = _
  rw [sourceTruncation_eq_sum,clock_truncation_eq]
  simp only [map_sum]
  rfl

theorem joint_tail_bound (M N : ℕ) (f : Field) :
    ‖f - jointTruncation M N f‖ ≤ ‖f - sourceTruncation M f‖ + ‖f - clockLift (truncation N) f‖ := by
  have h : ‖f - jointTruncation M N f‖ ≤
      ‖f - sourceTruncation M f‖ + ‖sourceTruncation M f - jointTruncation M N f‖ := by
    simpa only [dist_eq_norm] using dist_triangle f (sourceTruncation M f) (jointTruncation M N f)
  have hb : ‖sourceTruncation M f - jointTruncation M N f‖ ≤
      ‖f - clockLift (truncation N) f‖ := by
    change ‖sourceTruncation M f - sourceTruncation M (clockLift (truncation N) f)‖ ≤ _
    rw [← map_sub]
    exact sourceTruncation_norm_le M _
  exact h.trans (add_le_add le_rfl hb)

theorem joint_tail_compare (M N : ℕ) (f g : Field) :
    ‖f - jointTruncation M N f‖ ≤ 2 * ‖f - g‖ +
      ‖g - sourceTruncation M g‖ + ‖g - clockLift (truncation N) g‖ := by
  have h1 : ‖f - jointTruncation M N f‖ ≤ ‖f - g‖ + ‖g - jointTruncation M N f‖ := by
    simpa only [dist_eq_norm] using dist_triangle f g (jointTruncation M N f)
  have h2 : ‖g - jointTruncation M N f‖ ≤
      ‖g - jointTruncation M N g‖ + ‖jointTruncation M N g - jointTruncation M N f‖ := by
    simpa only [dist_eq_norm] using dist_triangle g (jointTruncation M N g) (jointTruncation M N f)
  have h3 : ‖jointTruncation M N g - jointTruncation M N f‖ ≤ ‖f - g‖ := by
    rw [← map_sub]
    simpa only [norm_sub_rev] using jointTruncation_norm_le M N (g-f)
  have h4 := joint_tail_bound M N g
  linarith

theorem commonSmoothing_projection (n : ℕ) (f : GaussianL2) :
    commonSmoothing (projection n f) = projection n (commonSmoothing f) := by
  rw [commonSmoothing_sector n ⟨_,projection_mem n f⟩]
  change _ = projection n (projection 0 f + GaussianInverseNumberPotential.potentialOperator f)
  rw [map_add,projection_of_sector ⟨_,projection_mem 0 f⟩,
    GaussianPotentialIteration.projection_potential]
  by_cases hn : n = 0
  · subst n; simp [GaussianRegularizedSecondDerivative.weight]
  · simp [GaussianRegularizedSecondDerivative.weight,hn]

theorem commonSmoothing_truncation (N : ℕ) (f : GaussianL2) :
    commonSmoothing (truncation N f) = truncation N (commonSmoothing f) := by
  simp only [truncation,ContinuousLinearMap.sum_apply,map_sum,commonSmoothing_projection]

theorem commonSmoothing_joint (M N : ℕ) (f : Field) :
    clockLift commonSmoothing (jointTruncation M N f) =
      jointTruncation M N (clockLift commonSmoothing f) := by
  change clockLift commonSmoothing (sourceLift (truncation M) (clockLift (truncation N) f)) = _
  rw [source_clock_commute]
  change sourceLift (truncation M) (clockLift commonSmoothing (clockLift (truncation N) f)) =
    sourceLift (truncation M) (clockLift (truncation N) (clockLift commonSmoothing f))
  apply congrArg (sourceLift (truncation M))
  apply eq_of_all_tests
  intro L
  rw [clockLift_test,clockLift_test,clockLift_test,clockLift_test]
  exact commonSmoothing_truncation N _

end OperatorDerivativeRewrite.Foundation.GaussianClockSourceSpectral
