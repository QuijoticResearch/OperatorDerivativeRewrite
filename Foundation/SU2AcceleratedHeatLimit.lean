import Foundation.AcceleratedDecayBoundary
import Foundation.SU2PolynomialHeatTrajectory

/-! A concrete singular time-scaling limit of the actual polynomial SU(2) heat
trajectories. No identification with a Yang--Mills lattice cutoff is assumed. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.SU2AcceleratedHeatLimit
open QuaternionSU2Representation SU2BoundedObservableGradient SU2RadialLaplacian
open SU2PolynomialHeatTrajectory AcceleratedDecayBoundary

def fast (n : ℕ) (t : ℝ) (A : SU2) : ℝ := accelerated observableTrajectory n t A

theorem fast_initial (n : ℕ) (A : SU2) : fast n 0 A = observable A := by
  simp [fast, accelerated, observable_initial]

theorem fast_continuous (n : ℕ) (A : SU2) : Continuous (fun t => fast n t A) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := (evolve_time_derivative (rate n*t) (1/2) (-1/2) A).comp t
    ((hasDerivAt_id' t).const_mul (rate n))
  exact h.continuousAt

theorem fast_heat_equation (n : ℕ) (t : ℝ) (A : SU2) :
    deriv (fun t => fast n t A) t = rate n*laplacian (fast n t) A := by
  have h := (evolve_time_derivative (rate n*t) (1/2) (-1/2) A).comp t
    ((hasDerivAt_id' t).const_mul (rate n))
  have hl := evolve_laplacian (rate n*t) (1/2) (-1/2) A
  simp only [Function.comp_def] at h
  change deriv (fun t => evolve (rate n*t) (1/2) (-1/2) A) t =
    rate n*laplacian (evolve (rate n*t) (1/2) (-1/2)) A
  rw [h.deriv, hl]
  ring

theorem fast_bound (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (A : SU2) :
    |fast n t A| ≤ 4*Real.exp (-2*(rate n*t)) :=
  observable_decay _ (mul_nonneg (rate_positive n).le ht) A

def limitAt (t : ℝ) (A : SU2) : ℝ := boundaryLimit observableTrajectory t A

theorem fast_positive_limit (t : ℝ) (ht : 0 < t) (A : SU2) :
    Tendsto (fun n => fast n t A) atTop (𝓝 0) := by
  exact positive_time_limit observableTrajectory 4 2 (by norm_num)
    (fun t ht A => by simpa only [Real.norm_eq_abs] using observable_decay t ht A) t ht A

theorem fast_nonnegative_limit (t : ℝ) (ht : 0 ≤ t) (A : SU2) :
    Tendsto (fun n => fast n t A) atTop (𝓝 (limitAt t A)) := by
  exact nonnegative_time_limit observableTrajectory 4 2 (by norm_num)
    (fun t ht A => by simpa only [Real.norm_eq_abs] using observable_decay t ht A) t ht A

theorem fast_uniform_away (δ : ℝ) (hδ : 0 < δ) :
    TendstoUniformlyOn (fun n (p : ℝ × SU2) => fast n p.1 p.2) (fun _ => 0)
      atTop {p | δ ≤ p.1} := by
  exact uniform_away_from_zero observableTrajectory 4 2 (by norm_num) (by norm_num)
    (fun t ht A => by simpa only [Real.norm_eq_abs] using observable_decay t ht A) δ hδ

theorem limit_initial (A : SU2) : limitAt 0 A = observable A := by
  simp [limitAt, boundaryLimit, observable_initial]

theorem limit_positive_time (t : ℝ) (ht : 0 < t) (A : SU2) : limitAt t A = 0 := by
  simp [limitAt, boundaryLimit, ne_of_gt ht]

theorem limit_not_right_continuous :
    ¬ ContinuousWithinAt (fun t => limitAt t (1 : SU2)) (Ici 0) 0 := by
  apply boundary_not_right_continuous observableTrajectory (1 : SU2)
  rw [observable_initial]
  norm_num [observable, ambient, polynomial, halfTrace, SU2TraceHessianModel.traceReal,
    Matrix.trace_one]

def layerTime (n : ℕ) : ℝ := Real.log 2 / rate n

theorem layerTime_positive (n : ℕ) : 0 < layerTime n := by
  exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (rate_positive n)

theorem layerTime_tendsto : Tendsto layerTime atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop rate_tendsto

theorem fast_layer_value (n : ℕ) : fast n (layerTime n) (1 : SU2) = -43/128 := by
  unfold fast accelerated layerTime
  have he : rate n*(Real.log 2/rate n) = Real.log 2 := by
    field_simp [(rate_positive n).ne']
  rw [he, observable_log_two_value]

theorem limit_layer_value (n : ℕ) : limitAt (layerTime n) (1 : SU2) = 0 :=
  limit_positive_time _ (layerTime_positive n) _

theorem nonuniform_on_initial_interval (δ : ℝ) (hδ : 0 < δ) :
    ¬ TendstoUniformlyOn (fun n t => fast n t (1 : SU2)) (fun t => limitAt t 1)
      atTop (Icc 0 δ) := by
  intro h
  have he := Metric.tendstoUniformlyOn_iff.mp h (43/256 : ℝ) (by norm_num)
  have ht := layerTime_tendsto.eventually (gt_mem_nhds hδ)
  obtain ⟨n, hn, htn⟩ := (he.and ht).exists
  have hv := hn (layerTime n) ⟨(layerTime_positive n).le, htn.le⟩
  rw [limit_layer_value, fast_layer_value] at hv
  norm_num at hv

end OperatorDerivativeRewrite.Foundation.SU2AcceleratedHeatLimit
