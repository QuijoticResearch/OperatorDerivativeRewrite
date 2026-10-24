import Foundation.IBMPhysicalMeshVariation

/-! Genuine local-time square sums on arbitrary deterministic vanishing-mesh
partitions of a fixed compact time interval. Repeated points are allowed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianLocalTimeMesh
open InfiniteGaussian GaussianBrownianQuadraticVariation BrownianMassContinuousLimit

def pathSquares {n : ℕ} (f : ℝ≥0 → ℝ) (τ : Fin (n + 1) → ℝ≥0) : ℝ :=
  ∑ i : Fin n, (f (τ i.succ)-f (τ i.castSucc))^2

theorem grid_mem {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hend : τ (Fin.last n) = T) (i : Fin (n + 1)) : τ i ∈ Icc 0 T := by
  refine ⟨bot_le, ?_⟩
  simpa only [hend] using hτ (Fin.le_last i)

theorem pathSquares_bound {n : ℕ} (f : ℝ≥0 → ℝ) (hf : Monotone f) (h0 : f 0 = 0)
    (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hz : τ 0 = 0) (hend : τ (Fin.last n) = T) (K : ℝ)
    (hK : ∀ i : Fin n, f (τ i.succ)-f (τ i.castSucc) ≤ K) : pathSquares f τ ≤ K*f T := by
  calc
    _ ≤ ∑ i : Fin n, K*(f (τ i.succ)-f (τ i.castSucc)) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hn := sub_nonneg.mpr (hf (hτ (Fin.castSucc_le_succ i)))
      nlinarith [hK i]
    _ = K*(f (τ (Fin.last n))-f (τ 0)) := by
      rw [← Finset.mul_sum]
      exact congrArg (fun x : ℝ => K*x) (sum_fin_differences (fun i => f (τ i)))
    _ = _ := by rw [hz, hend, h0, sub_zero]

theorem pathSquares_terminal_bound {n : ℕ} (f : ℝ≥0 → ℝ) (hf : Monotone f) (h0 : f 0 = 0)
    (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hz : τ 0 = 0) (hend : τ (Fin.last n) = T) : pathSquares f τ ≤ (f T)^2 := by
  have h := pathSquares_bound f hf h0 T τ hτ hz hend (f T) (fun i => by
    have ha := hf (grid_mem T τ hτ hend i.castSucc).1
    have hb := hf (grid_mem T τ hτ hend i.succ).2
    rw [h0] at ha
    linarith)
  simpa only [pow_two] using h

theorem pathSquares_tendsto (f : ℝ≥0 → ℝ) (hc : Continuous f) (hf : Monotone f)
    (h0 : f 0 = 0) (T : ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hz : ∀ N, τ N 0 = 0)
    (hend : ∀ N, τ N (Fin.last (m N)) = T) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0))
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (τ N i.succ : ℝ) - τ N i.castSucc ≤ ε N) :
    Tendsto (fun N => pathSquares f (τ N)) atTop (nhds 0) := by
  have hn : 0 ≤ f T := by simpa only [h0] using hf (show (0 : ℝ≥0) ≤ T from bot_le)
  have huc : UniformContinuousOn f (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hpos : 0 < f T+1 := by linarith
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp huc (η/(f T+1)) (div_pos hη hpos)
  filter_upwards [(tendsto_order.mp hε).2 δ hδ] with N hsmall
  have hb := pathSquares_bound f hf h0 T (τ N) (hτ N) (hz N) (hend N) (η/(f T+1)) (fun i => by
    have hdist : dist (τ N i.succ) (τ N i.castSucc) < δ := by
      change dist (τ N i.succ : ℝ) (τ N i.castSucc : ℝ) < δ
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr
        (show (τ N i.castSucc : ℝ) ≤ τ N i.succ from hτ N (Fin.castSucc_le_succ i)))]
      exact (hmesh N i).trans_lt hsmall
    have he := hd _ (grid_mem T (τ N) (hτ N) (hend N) i.succ)
      _ (grid_mem T (τ N) (hτ N) (hend N) i.castSucc) hdist
    rw [Real.dist_eq] at he
    exact (le_abs_self _).trans he.le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun i _hi => sq_nonneg _)]
  have he := div_mul_cancel₀ η (ne_of_gt hpos)
  have hp := div_pos hη hpos
  nlinarith

def squares {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) : ℝ := pathSquares (limitPath Y) τ

theorem squares_nonnegative {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) : 0 ≤ squares τ Y := by
  unfold squares pathSquares
  exact Finset.sum_nonneg fun i _hi => sq_nonneg _

theorem squares_measurable {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : Measurable (squares τ) := by
  unfold squares pathSquares
  exact Finset.measurable_sum _ fun (i : Fin n) _hi =>
    (((ContinuousMap.measurable_eval (τ i.succ)).comp limitPath_measurable).sub
      ((ContinuousMap.measurable_eval (τ i.castSucc)).comp limitPath_measurable)).pow_const 2

theorem squares_bound {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hz : τ 0 = 0) (hend : τ (Fin.last n) = T) : ∀ᵐ Y ∂gaussianProduct,
    squares τ Y ≤ (limitPath Y T)^2 := by
  filter_upwards [limitPath_properties] with Y hp
  exact pathSquares_terminal_bound (limitPath Y) hp.2.1 hp.1 T τ hτ hz hend

theorem squares_integrable {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hz : τ 0 = 0) (hend : τ (Fin.last n) = T) : Integrable (squares τ) gaussianProduct := by
  apply (BrownianLocalTimeSquares.terminal_integrable T).mono' (squares_measurable τ).aestronglyMeasurable
  filter_upwards [squares_bound T τ hτ hz hend] with Y hY
  rwa [Real.norm_of_nonneg (squares_nonnegative τ Y)]

theorem squares_mean_tendsto (T : ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hz : ∀ N, τ N 0 = 0)
    (hend : ∀ N, τ N (Fin.last (m N)) = T) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0))
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (τ N i.succ : ℝ) - τ N i.castSucc ≤ ε N) :
    Tendsto (fun N => ∫ Y, squares (τ N) Y ∂gaussianProduct) atTop (nhds 0) := by
  have hpoint : ∀ᵐ Y ∂gaussianProduct,
      Tendsto (fun N => squares (τ N) Y) atTop (nhds 0) := by
    filter_upwards [limitPath_properties] with Y hp
    exact pathSquares_tendsto (limitPath Y) (limitPath Y).continuous hp.2.1 hp.1
      T m τ hτ hz hend ε hε hmesh
  have h := tendsto_integral_of_dominated_convergence (fun Y => (limitPath Y T)^2)
    (F := fun N Y => squares (τ N) Y) (f := fun _ => (0 : ℝ))
    (fun N => (squares_measurable (τ N)).aestronglyMeasurable)
    (BrownianLocalTimeSquares.terminal_integrable T)
    (fun N => (squares_bound T (τ N) (hτ N) (hz N) (hend N)).mono fun Y hY => by
      rwa [Real.norm_of_nonneg (squares_nonnegative (τ N) Y)]) hpoint
  simpa only [integral_zero] using h

end OperatorDerivativeRewrite.Foundation.BrownianLocalTimeMesh
