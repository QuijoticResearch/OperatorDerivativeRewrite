import Foundation.IBMSpatialRandomTestBounds

/-! Actual kernel convergence for EVERY square-integrable strongly measurable
completed spatial random test. Finite-range testing and uniform L2 bounds
justify the extension; deterministic-test convergence alone is not used as a
substitute for random-test convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialRandomTestConvergence
open InfiniteGaussian IBMSpatialCompletedTestLimit IBMSpatialRandomTestBounds

def deterministicError (T : ℝ≥0) (hT : 0 < T) (N : ℕ) (z : Completed) :
    Lp ℝ 1 gaussianProduct := IBMSpatialCompletedTestLimit.finiteOperator T N z-
      IBMSpatialCompletedTestLimit.limitOperator T hT z

theorem deterministicError_tendsto (T : ℝ≥0) (hT : 0 < T) (z : Completed) :
    Tendsto (fun N => ‖deterministicError T hT N z‖) atTop (𝓝 0) := by
  exact tendsto_iff_norm_sub_tendsto_zero.mp (completed_tendsto T hT z)

theorem simple_error_bound (T : ℝ≥0) (hT : 0 < T) (N : ℕ)
    (s : Lp.simpleFunc Completed 2 gaussianProduct) :
    ‖IBMSpatialRandomTestBounds.finiteOperator T N s-IBMSpatialRandomTestBounds.limitOperator T s‖ ≤
      ∑ z ∈ (Lp.simpleFunc.toSimpleFunc s).range, ‖deterministicError T hT N z‖ := by
  let d := IBMSpatialRandomTestBounds.finiteOperator T N s-IBMSpatialRandomTestBounds.limitOperator T s
  have hi (z : Completed) : Integrable (fun Y => ‖deterministicError T hT N z Y‖) gaussianProduct :=
    ((Lp.memLp (deterministicError T hT N z)).integrable (by norm_num)).norm
  have hd : ∀ᵐ Y ∂gaussianProduct, ‖d Y‖ ≤
      ∑ z ∈ (Lp.simpleFunc.toSimpleFunc s).range, ‖deterministicError T hT N z Y‖ := by
    have hall : ∀ᵐ Y ∂gaussianProduct, ∀ z : (Lp.simpleFunc.toSimpleFunc s).range,
        deterministicError T hT N z Y =
          IBMSpatialBoundedTestOperator.finiteValue (realize z) T N Y-
            IBMSpatialPathOccupation.pathValue (realize z) T Y := by
      apply ae_all_iff.mpr
      intro z
      filter_upwards [IBMSpatialCompletedTestLimit.finite_actual T N z,
        IBMSpatialPathReconstruction.completed_occupation_actual T hT z,
        Lp.coeFn_sub (IBMSpatialCompletedTestLimit.finiteOperator T N z)
          (IBMSpatialCompletedTestLimit.limitOperator T hT z)] with Y hf hl hs
      change deterministicError T hT N z Y = _ at hs
      rw [hs,Pi.sub_apply,hf,hl]
    filter_upwards [finite_actual T N (s:RandomTests),limit_actual T (s:RandomTests),
      Lp.simpleFunc.toSimpleFunc_eq_toFun s,Lp.coeFn_sub
        (IBMSpatialRandomTestBounds.finiteOperator T N s) (IBMSpatialRandomTestBounds.limitOperator T s),
      hall] with Y hf hl hs hsub hd
    have hz : deterministicError T hT N ((Lp.simpleFunc.toSimpleFunc s) Y) Y =
        IBMSpatialBoundedTestOperator.finiteValue (realize ((Lp.simpleFunc.toSimpleFunc s) Y)) T N Y-
          IBMSpatialPathOccupation.pathValue (realize ((Lp.simpleFunc.toSimpleFunc s) Y)) T Y :=
      hd ⟨(Lp.simpleFunc.toSimpleFunc s) Y,SimpleFunc.mem_range_self _ _⟩
    have he : d Y = deterministicError T hT N ((Lp.simpleFunc.toSimpleFunc s) Y) Y := by
      change (IBMSpatialRandomTestBounds.finiteOperator T N s-IBMSpatialRandomTestBounds.limitOperator T s) Y = _
      rw [hsub,Pi.sub_apply,hf,hl]
      rw [← hs]
      exact hz.symm
    rw [he]
    exact Finset.single_le_sum (s := (Lp.simpleFunc.toSimpleFunc s).range)
      (f := fun z : Completed => ‖deterministicError T hT N z Y‖)
      (fun z _ => norm_nonneg _) (SimpleFunc.mem_range_self _ _)
  rw [L1.norm_eq_integral_norm]
  calc
    _ ≤ ∫ Y, ∑ z ∈ (Lp.simpleFunc.toSimpleFunc s).range, ‖deterministicError T hT N z Y‖ ∂gaussianProduct :=
      integral_mono_ae ((Lp.memLp d).integrable (by norm_num)).norm
        (integrable_finsetSum _ (fun z _ => hi z)) hd
    _ = _ := by
      rw [integral_finsetSum _ (fun z _ => hi z)]
      exact Finset.sum_congr rfl fun z _ => (L1.norm_eq_integral_norm _).symm

theorem simple_tendsto (T : ℝ≥0) (hT : 0 < T) (s : Lp.simpleFunc Completed 2 gaussianProduct) :
    Tendsto (fun N => IBMSpatialRandomTestBounds.finiteOperator T N s) atTop
      (𝓝 (IBMSpatialRandomTestBounds.limitOperator T s)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := tendsto_finsetSum (Lp.simpleFunc.toSimpleFunc s).range (fun z _ => deterministicError_tendsto T hT z)
  simp only [Finset.sum_const_zero] at hs
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => simple_error_bound T hT N s) hs

theorem random_tendsto (T : ℝ≥0) (hT : 0 < T) (u : RandomTests) :
    Tendsto (fun N => IBMSpatialRandomTestBounds.finiteOperator T N u) atTop
      (𝓝 (IBMSpatialRandomTestBounds.limitOperator T u)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0 < ε/(3*(3*(T:ℝ)+1)) := by positivity
  obtain ⟨s,hs⟩ := (Lp.simpleFunc.denseRange (E := Completed) (μ := gaussianProduct)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞)).exists_dist_lt u hδ
  have hd : ‖u-(s:RandomTests)‖ < ε/(3*(3*(T:ℝ)+1)) := by simpa only [dist_eq_norm] using hs
  have hb : 3*(T:ℝ)*‖u-(s:RandomTests)‖ < ε/3 := by
    have hh := (lt_div_iff₀ (show 0 < 3*(3*(T:ℝ)+1) by positivity)).mp hd
    nlinarith [norm_nonneg (u-(s:RandomTests))]
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (simple_tendsto T hT s) (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hc : ‖IBMSpatialRandomTestBounds.finiteOperator T n s-IBMSpatialRandomTestBounds.limitOperator T s‖ < ε/3 :=
    by simpa only [dist_eq_norm] using hN n hn
  have ha := finite_norm_bound T n (u-(s:RandomTests))
  have hl := limit_norm_bound T ((s:RandomTests)-u)
  rw [norm_sub_rev (s:RandomTests) u] at hl
  have he : IBMSpatialRandomTestBounds.finiteOperator T n u-IBMSpatialRandomTestBounds.limitOperator T u =
      IBMSpatialRandomTestBounds.finiteOperator T n (u-(s:RandomTests))+
        (IBMSpatialRandomTestBounds.finiteOperator T n s-IBMSpatialRandomTestBounds.limitOperator T s)+
          IBMSpatialRandomTestBounds.limitOperator T ((s:RandomTests)-u) := by
    simp only [map_sub]
    abel
  rw [dist_eq_norm,he]
  have ht := norm_add_le (IBMSpatialRandomTestBounds.finiteOperator T n (u-(s:RandomTests))+
    (IBMSpatialRandomTestBounds.finiteOperator T n s-IBMSpatialRandomTestBounds.limitOperator T s))
      (IBMSpatialRandomTestBounds.limitOperator T ((s:RandomTests)-u))
  have ht' := norm_add_le (IBMSpatialRandomTestBounds.finiteOperator T n (u-(s:RandomTests)))
    (IBMSpatialRandomTestBounds.finiteOperator T n s-IBMSpatialRandomTestBounds.limitOperator T s)
  linarith

end OperatorDerivativeRewrite.Foundation.IBMSpatialRandomTestConvergence
