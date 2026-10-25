import Foundation.IBMClockVarianceBound

/-! The uniform clock variance bound is transferred to the ORIGINAL IBM
observable projection, giving actual native-grid norm escape. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeGridEscape
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMUniformClockGridEnergy IBMCenteredClockVariance IBMCenteredRawGrid
open IBMClockVarianceBound

theorem value_eq_min_sum {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (Y : SampleSpace) :
    value τ Y = ∑ i : Fin n,
      (min |process (τ i.castSucc) Y| |process (τ i.succ) Y|-|process (τ i.castSucc) Y|) := by
  have he := sum_fin_differences (fun i : Fin (n+1) => |process (τ i) Y|)
  have hmin (a b : ℝ) : 2*(min a b-a) = b-a-|b-a| := by
    rcases le_total a b with h | h
    · rw [min_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [min_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
  have hm := fun i : Fin n => hmin
    |process (τ i.castSucc) Y| |process (τ i.succ) Y|
  have hs : 2*(∑ i : Fin n,
      (min |process (τ i.castSucc) Y| |process (τ i.succ) Y|-|process (τ i.castSucc) Y|)) =
      (∑ i : Fin n, (|process (τ i.succ) Y|-|process (τ i.castSucc) Y|))-
        ∑ i : Fin n, |(|process (τ i.succ) Y|-|process (τ i.castSucc) Y|)| := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hm i
  rw [he] at hs
  unfold value
  linarith

private theorem time_grid (H : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    uniformTime H N i = grid (H/(N+1)) i.val := by
  unfold uniformTime grid
  push_cast
  ring

theorem actualClock_uniform_ae (H : ℝ≥0) (N : ℕ) :
    actualClock (H/(N+1)) (N+1) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => value (uniformTime H N) p.2 := by
  have hg := (measurePreserving_snd (μ:=gaussianProduct) (ν:=gaussianProduct)).quasiMeasurePreserving.ae
    (IBMClockGridPath.clock_grid_ae H)
  filter_upwards [hg] with p hp
  rw [value_eq_min_sum]
  simp only [time_grid,Fin.val_castSucc,Fin.val_succ]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    min |process (grid (H/(N+1)) i) p.2| |process (grid (H/(N+1)) (i+1)) p.2|-
      |process (grid (H/(N+1)) i) p.2|) (N+1)]
  unfold actualClock IBMRawStepCompensation.clockFunction
  apply Finset.sum_congr rfl
  intro i hi
  rw [hp N i,hp N (i+1)]

theorem centeredClock_uniform_bound (H : ℝ≥0) (N : ℕ) :
    ‖centeredClock (H/(N+1)) (N+1)‖^2 ≤ (9/2:ℝ)*(H:ℝ) := by
  have hv : ‖centeredClock (H/(N+1)) (N+1)‖^2 =
      Var[actualClock (H/(N+1)) (N+1); IBMSourceLaws.jointMeasure] := by
    rw [centered_clock_variance,variance_eq_integral (actualClock_memLp _ _).aemeasurable]
  rw [hv,variance_congr (actualClock_uniform_ae H N)]
  have hmap : Measure.map Prod.snd IBMSourceLaws.jointMeasure = gaussianProduct :=
    (measurePreserving_snd (μ:=gaussianProduct) (ν:=gaussianProduct)).map_eq
  have he := variance_map (X:=value (uniformTime H N)) (Y:=Prod.snd)
    (hmap.symm ▸ (value_memLp (uniformTime H N)).aemeasurable)
    (measurable_snd.aemeasurable (μ:=IBMSourceLaws.jointMeasure))
  rw [hmap] at he
  simp only [Function.comp_def] at he
  rw [← he]
  simpa only [(uniformTime_endpoints H N).2] using
    value_variance_bound (uniformTime H N) (uniformTime_monotone H N) (uniformTime_endpoints H N).1

theorem original_native_norm_escape (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N : ℕ => ‖IBMJointIntrinsicDerivative.jointDivergence
      (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))‖) atTop atTop := by
  apply IBMSourceEnergyGrowth.uniform_bounded_clock_escape H hH (C:=(9/2:ℝ)*H) (by positivity)
  exact Eventually.of_forall (centeredClock_uniform_bound H)

theorem no_original_native_L2_limit (H : ℝ≥0) (hH : 0 < H)
    (v : IBMTimeAveragedObservable.IntrinsicSpace) :
    ¬ Tendsto (fun N : ℕ => IBMJointIntrinsicDerivative.jointDivergence
      (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) atTop (𝓝 v) := by
  intro hv
  exact not_tendsto_nhds_of_tendsto_atTop (original_native_norm_escape H hH) _ hv.norm

end OperatorDerivativeRewrite.Foundation.IBMNativeGridEscape
