import Foundation.IBMPhysicalWickTestDomain

/-! Fixed physical quadratic-Wick probes of the compensated source grid.
Convergence below is strong in clock L2 for each even Schwartz probe, not
strong convergence of the source kernel or its observable projection. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawGridWickLimit
open InfiniteGaussian GaussianTimeProcess GaussianTimeSpaceHermite
open IBMRawGridSecondChaos IBMPhysicalWickTestDomain IBMUniformClockGridEnergy
open GaussianSmoothQuadraticVariation GaussianBrownianQuadraticVariation

theorem source_test_telescope (u : ℕ → CoefficientSpace) (n : ℕ) (k : CoefficientSpace) :
    inner ℝ (sourceSum u n) (wick k 2 : GaussianL2) =
      (inner ℝ (u n) k)^2-(inner ℝ (u 0) k)^2-
        ∑ i ∈ Finset.range n, (inner ℝ (u (i+1)) k-inner ℝ (u i) k)^2 := by
  rw [source_wick_test,Finset.mul_sum]
  calc
    _ = ∑ i ∈ Finset.range n,
        ((inner ℝ (u (i+1)) k)^2-(inner ℝ (u i) k)^2-
          (inner ℝ (u (i+1)) k-inner ℝ (u i) k)^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [increment,inner_sub_left]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib,
        Finset.sum_range_sub (fun i => (inner ℝ (u i) k)^2) n]

def action (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  (innerSL ℝ (wick (testDirection g) 2 : GaussianL2)).compLpL 2 gaussianProduct
    (sourceGrid (T/(N+1)) (N+1))

theorem action_actual (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    action g T N =ᵐ[gaussianProduct] fun Y =>
      inner ℝ (sourceSum (clockCurve (T/(N+1)) Y) (N+1))
        (wick (testDirection g) 2 : GaussianL2) := by
  filter_upwards [(innerSL ℝ (wick (testDirection g) 2 : GaussianL2)).coeFn_compLpL
    (sourceGrid (T/(N+1)) (N+1)),sourceGrid_ae (T/(N+1)) (N+1)] with Y h hY
  change action g T N Y = _ at h
  rw [h,hY]
  change inner ℝ (wick (testDirection g) 2 : GaussianL2) _ = _
  exact real_inner_comm _ _

theorem terminal_memLp (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) :
    MemLp (fun Y => (g (process T Y)-g 0)^2) 2 gaussianProduct := by
  have hm : Measurable (fun Y => (g (process T Y)-g 0)^2) := ((g.continuous.measurable.comp
    (process_stronglyMeasurable T).measurable).sub measurable_const).pow_const 2
  apply MemLp.of_bound hm.aestronglyMeasurable
    ((2*SchwartzMap.seminorm ℝ 0 0 g)^2)
  filter_upwards [] with Y
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (by
    have h1 := IBMBoundaryResidualLimit.schwartz_bound g (process T Y)
    have h0 := IBMBoundaryResidualLimit.schwartz_bound g 0
    linarith)

def terminal (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) : GaussianL2 :=
  (terminal_memLp g T).toLp _

def quadratic (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  quadraticSum g (g.smooth 2) (firstBound g) (secondBound g)
    (first_derivative_bound g) (second_derivative_bound g) T N

def drift (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) : GaussianL2 :=
  ∫ t in 0..(T:ℝ), GaussianLipschitzIntegrands.valueL2
    (square_derivative_lipschitz g (g.smooth 2) (firstBound g) (secondBound g)
      (first_derivative_bound g) (second_derivative_bound g)) t.toNNReal

theorem quadratic_tendsto (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) :
    Tendsto (quadratic g T) atTop (𝓝 (drift g T)) :=
  quadraticSum_tendsto _ _ _ _ _ _ _

private theorem time_grid (T : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    uniformTime T N i = grid (T/(N+1)) i.val := by
  unfold uniformTime grid
  push_cast
  ring

theorem action_identity (g : SchwartzMap ℝ ℝ) (hg : ∀ x, g (-x) = g x)
    (T : ℝ≥0) (N : ℕ) :
    action g T N = terminal g T-quadratic g T N := by
  have ht : grid (T/(N+1)) (N+1) = T := by
    unfold grid
    have hp : (N+1:ℝ≥0) ≠ 0 := by positivity
    simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ T hp
  have hzero : grid (T/(N+1)) 0 = 0 := by simp [grid]
  apply Lp.ext
  filter_upwards [action_actual g T N,(terminal_memLp g T).coeFn_toLp,
    quadraticSum_actual g (g.smooth 2) (firstBound g) (secondBound g)
      (first_derivative_bound g) (second_derivative_bound g) T N,
    Lp.coeFn_sub (terminal g T) (quadratic g T N),process_zero_ae] with Y ha he hq hs hz
  change terminal g T Y = _ at he
  change quadratic g T N Y = _ at hq
  rw [hs,Pi.sub_apply,he,hq,ha,source_test_telescope]
  simp only [clockCurve,even_clock_primitive g hg,ht,hzero,hz,sub_self,
    zero_pow (by norm_num : (2:ℕ) ≠ 0),
    sub_zero]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [time_grid,Fin.val_succ,Fin.val_castSucc]
  ring

theorem action_tendsto (g : SchwartzMap ℝ ℝ) (hg : ∀ x, g (-x) = g x) (T : ℝ≥0) :
    Tendsto (action g T) atTop (𝓝 (terminal g T-drift g T)) := by
  have h := (tendsto_const_nhds (x := terminal g T)).sub (quadratic_tendsto g T)
  exact h.congr' (Eventually.of_forall fun N => (action_identity g hg T N).symm)

end OperatorDerivativeRewrite.Foundation.IBMRawGridWickLimit
