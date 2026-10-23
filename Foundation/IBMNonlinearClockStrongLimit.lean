import Foundation.IBMNonlinearClockLocalStrong

/-! Genuine global strong convergence of the original nonlinear native clock
averages. This is a vector-L2 limit; intrinsic graph identification is separate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockStrongLimit
open InfiniteGaussian IBMClockOverlapEnergy IBMFoldedTransitionBound IBMNonlinearClockCutoffError

theorem cutoff_window (j : ℕ) :
    ∀ r, r ∉ Ioc (-3*((j:ℝ)+1)) (3*((j:ℝ)+1)) → cutoff j r = 0 := by
  intro r hr
  apply (cutoff j).zero_of_le_dist
  change 2*((j:ℝ)+1) ≤ dist r 0
  rw [Real.dist_eq,sub_zero]
  have hh : r ≤ -3*((j:ℝ)+1) ∨ 3*((j:ℝ)+1) < r := by
    simpa only [mem_Ioc,not_and_or,not_lt,not_le] using hr
  have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
  rcases hh with hl | hr
  · linarith [neg_le_abs r]
  · linarith [le_abs_self r]

theorem native_cauchy (T : ℝ≥0) : CauchySeq (fun n => IBMNonlinearClockEnergy.average n T) := by
  let C := 8*peak 1*(T:ℝ)^2*Real.sqrt T+4*(T:ℝ)^3
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hb : Tendsto (fun j : ℕ => ((T:ℝ)/((j:ℝ)+1)^2)*C) atTop (𝓝 0) := by
    convert ((tendsto_const_nhds (x := (T:ℝ))).mul (ht.pow 2)).mul_const C using 1
    · funext j
      simp only [div_eq_mul_inv,one_mul,inv_pow]
    · simp
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := (hb.eventually (gt_mem_nhds
    (sq_pos_of_pos (by linarith : (0:ℝ)<ε/4)))).exists
  let v : ℕ → IBMClockAverageCandidate.Target := fun n =>
    IBMNonlinearClockTailEnergy.average (fun x => cutoff j |x|) n T
  have hclose (n : ℕ) : dist (IBMNonlinearClockEnergy.average n T) (v n) < ε/4 := by
    have he := average_cutoff_error (fun x => cutoff j |x|)
      ((cutoff_continuous j).measurable.comp continuous_abs.measurable)
      (fun x => (cutoff j).nonneg' |x|) (fun x => (cutoff j).le_one (x := |x|))
      (by positivity : (0:ℝ)<(j:ℝ)+1)
      (fun x hx => cutoff_one j |x| (by simpa only [abs_abs] using hx)) n T.property
    change ‖IBMNonlinearClockEnergy.average n T - v n‖^2 ≤
      ((T:ℝ)/((j:ℝ)+1)^2)*C at he
    rw [dist_eq_norm]
    nlinarith
  have hw := IBMNonlinearClockLocalStrong.localized_cauchy (cutoff j)
    (cutoff_continuous j) (cutoff_compactSupport j)
    (fun x => (cutoff j).nonneg' x) (fun x => (cutoff j).le_one (x := x))
    (show -3*((j:ℝ)+1) ≤ 3*((j:ℝ)+1) by
      have hh : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith) (cutoff_window j) T
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hw (ε/2) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmid : dist (v m) (v n) < ε/2 := hN m hm n hn
  have hl := hclose m
  have hr := hclose n
  have htri1 := dist_triangle (IBMNonlinearClockEnergy.average m T) (v m)
    (IBMNonlinearClockEnergy.average n T)
  have htri2 := dist_triangle (v m) (v n) (IBMNonlinearClockEnergy.average n T)
  rw [dist_comm (v n)] at htri2
  linarith

def nativeLimit (T : ℝ≥0) : IBMClockAverageCandidate.Target :=
  Classical.choose (cauchySeq_tendsto_of_complete (native_cauchy T))

theorem native_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMNonlinearClockEnergy.average n T) atTop (𝓝 (nativeLimit T)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (native_cauchy T))

theorem nativeLimit_unique (T : ℝ≥0) (v : IBMClockAverageCandidate.Target)
    (hv : Tendsto (fun n => IBMNonlinearClockEnergy.average n T) atTop (𝓝 v)) :
    nativeLimit T = v := tendsto_nhds_unique (native_tendsto T) hv

theorem nativeLimit_energy (T : ℝ≥0) :
    ‖nativeLimit T‖^2 ≤ 8*peak 1*(T:ℝ)^2*Real.sqrt T+4*(T:ℝ)^3 :=
  le_of_tendsto ((native_tendsto T).norm.pow 2)
    (Eventually.of_forall fun n => IBMNonlinearClockEnergy.average_uniform_energy n T.property)

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockStrongLimit
