import Foundation.IBMAllSchwartzWickLimit

/-! Original compensated source-grid tests converge for every real Schwartz
primitive in clock L1, with the actual folded derivative-square drift. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMAllSchwartzSourceReconstruction
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMPhysicalWickTestDomain IBMClippedClockStrongLimit IBMUniformClockGridEnergy
open IBMAllSchwartzWickLimit IBMRawGridSecondChaos

theorem terminal_memLp (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) :
    MemLp (fun Y => (g |process T Y|-g 0)^2) 2 gaussianProduct := by
  have hm : Measurable (fun Y => (g |process T Y|-g 0)^2) :=
    ((g.continuous.measurable.comp (continuous_abs.measurable.comp
      (process_stronglyMeasurable T).measurable)).sub measurable_const).pow_const 2
  apply MemLp.of_bound hm.aestronglyMeasurable ((2*SchwartzMap.seminorm ℝ 0 0 g)^2)
  filter_upwards [] with Y
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (by
    have h1 := IBMBoundaryResidualLimit.schwartz_bound g |process T Y|
    have h0 := IBMBoundaryResidualLimit.schwartz_bound g 0
    linarith)

def terminal (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) : GaussianL2 := (terminal_memLp g T).toLp _

private theorem time_grid (T : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    uniformTime T N i = grid (T/(N+1)) i.val := by
  unfold uniformTime grid
  push_cast
  ring

theorem original_action_identity (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    clockL1 (IBMRawGridWickLimit.action g T N) = clockL1 (terminal g T)-quadratic g T N := by
  have ht : grid (T/(N+1)) (N+1) = T := by
    unfold grid
    have hp : (N+1:ℝ≥0) ≠ 0 := by positivity
    simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ T hp
  have hz : grid (T/(N+1)) 0 = 0 := by simp [grid]
  apply Lp.ext
  filter_upwards [clockL1_actual (IBMRawGridWickLimit.action g T N),
    clockL1_actual (terminal g T),(terminal_memLp g T).coeFn_toLp,
    IBMRawGridWickLimit.action_actual g T N,quadratic_actual g T N,
    Lp.coeFn_sub (clockL1 (terminal g T)) (quadratic g T N),process_zero_ae] with Y hl hc hterm ha hq hs h0
  change terminal g T Y = _ at hterm
  rw [hl,hs,Pi.sub_apply,hc,hterm,ha,hq,IBMRawGridWickLimit.source_test_telescope]
  simp only [clockCurve,clock_primitive,ht,hz,h0,abs_zero,sub_self,
    zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [time_grid,Fin.val_succ,Fin.val_castSucc]
  ring

theorem original_action_tendsto (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => clockL1 (IBMRawGridWickLimit.action g T N)) atTop
      (𝓝 (clockL1 (terminal g T)-clockL1 (drift g T))) := by
  have h := (tendsto_const_nhds (x:=clockL1 (terminal g T))).sub (quadratic_tendsto g T hT)
  exact h.congr' (Eventually.of_forall fun N => (original_action_identity g T N).symm)

end OperatorDerivativeRewrite.Foundation.IBMAllSchwartzSourceReconstruction
