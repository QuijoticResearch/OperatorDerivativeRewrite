import Foundation.IBMTimeSpaceQuadrature
import Foundation.IBMActualSimpson

/-! A genuine nonseparable time-space chain formula for actual reflected-clock
IBM. Spatial Simpson sums converge in the ORIGINAL probability law. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMTimeSpaceSimpson
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMContinuousQuadrature IBMTimeSpaceQuadrature IBMActualSimpson
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def path (ω : JointSample) (t : ℝ) : ℝ := ibmValue (Real.toNNReal t) ω

theorem path_continuous (ω : JointSample) : Continuous (path ω) :=
  (ibmValue_continuous ω).comp continuous_real_toNNReal

theorem path_time (T : ℝ≥0) (N i : ℕ) (ω : JointSample) :
    path ω (time T N i) = ibmValue (grid (T / N) i) ω := by
  unfold path
  rw [IBMContinuousWeightedQuartic.real_time_eq_grid, Real.toNNReal_coe]

def sums (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), IBMSimpsonPeano.simpson (deriv (F (time T (n + 1) i)))
    (path ω (time T (n + 1) i)) (path ω (time T (n + 1) (i + 1)))

def spatialIncrements (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (F (time T (n + 1) i) (path ω (time T (n + 1) (i + 1))) -
    F (time T (n + 1) i) (path ω (time T (n + 1) i)))

def error (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  sums F T n ω - spatialIncrements F T n ω

def correction (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (ω : JointSample) : ℝ :=
  ∫ t in (0 : ℝ)..(T : ℝ), timeDerivative F t (path ω t)

def target (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (ω : JointSample) : ℝ :=
  F T (ibmValue T ω) - F 0 (ibmValue 0 ω) - correction F T ω

theorem path_measurable (t : ℝ) : Measurable (fun ω => path ω t) :=
  ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)

theorem sums_measurable (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 4 (F t))
    (T : ℝ≥0) (n : ℕ) : Measurable (sums F T n) := by
  apply Finset.measurable_sum
  intro i hi
  have hc : Continuous (fun p : ℝ × ℝ =>
      IBMSimpsonPeano.simpson (deriv (F (time T (n + 1) i))) p.1 p.2) := by
    have hg := (hF (time T (n + 1) i)).continuous_deriv (by norm_num)
    unfold IBMSimpsonPeano.simpson
    fun_prop
  exact hc.measurable.comp ((path_measurable _).prodMk (path_measurable _))

theorem spatialIncrements_measurable (F : ℝ → ℝ → ℝ)
    (hF : ∀ t, ContDiff ℝ 4 (F t)) (T : ℝ≥0) (n : ℕ) :
    Measurable (spatialIncrements F T n) := by
  apply Finset.measurable_sum
  intro i hi
  exact (((hF _).continuous.measurable.comp (path_measurable _)).sub
    ((hF _).continuous.measurable.comp (path_measurable _)))

theorem correction_integrable (F : ℝ → ℝ → ℝ)
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) (ω : JointSample) :
    IntervalIntegrable (fun t => timeDerivative F t (path ω t)) volume 0 T :=
  (hD.comp (continuous_id.prodMk (path_continuous ω))).intervalIntegrable _ _

theorem correction_measurable (F : ℝ → ℝ → ℝ)
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) : Measurable (correction F T) := by
  have hp : Measurable (fun p : ℝ × JointSample => path p.2 p.1) :=
    ibmValue_jointly_measurable.comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hm := (hD.measurable.comp (measurable_fst.prodMk hp)).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioc (0 : ℝ) T))
  have he : correction F T = fun ω => ∫ t, timeDerivative F t (path ω t)
      ∂volume.restrict (Ioc (0 : ℝ) T) := by
    funext ω
    exact intervalIntegral.integral_of_le T.coe_nonneg
  rw [he]
  exact hm.measurable

theorem target_measurable (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 4 (F t))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) : Measurable (target F T) :=
  (((hF T).continuous.measurable.comp
    (ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id))).sub
    ((hF 0).continuous.measurable.comp
      (ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)))).sub
        (correction_measurable F hD T)

theorem error_eventual_bound (F : ℝ → ℝ → ℝ)
    (hF : ∀ t, ContDiff ℝ 4 (F t))
    (hD : Continuous (fun p : ℝ × ℝ => iteratedDeriv 4 (F p.1) p.2))
    (T : ℝ≥0) (ω : JointSample) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |error F T n ω| ≤ ε * IBMUniformQuarticFamily.quartic T (n + 1) ω := by
  let R := IBMContinuousBlockWeights.pathBound id continuous_id T ω
  obtain ⟨δ, hδ, hu⟩ := IBMTimeSpacePeano.compact_error_bound F hF hD T R ε hε
  filter_upwards [(IBMUniformFifthRemainder.mesh_tendsto T ω).eventually (gt_mem_nhds hδ)] with n hn
  unfold error sums spatialIncrements
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [IBMUniformQuarticFamily.quartic, IBMUniformQuarticFamily.segment,
    Nat.cast_add, Nat.cast_one]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hb (j : ℕ) (hj : j ≤ n + 1) : |ibmValue (grid (T / (n + 1)) j) ω| ≤ R :=
    IBMContinuousBlockWeights.pathBound_bound id continuous_id T ω _
      (IBMActualPeanoRemainder.grid_le T n j hj)
  have hd : |ibmValue (grid (T / (n + 1)) (i + 1)) ω - ibmValue (grid (T / (n + 1)) i) ω| ≤
      IBMUniformFifthRemainder.mesh T n ω :=
    Finset.le_sup' (fun k => |ibmValue (grid (T / (n + 1)) (k + 1)) ω -
      ibmValue (grid (T / (n + 1)) k) ω|) hi
  have he := hu (time T (n + 1) i) (time_mem T.coe_nonneg (by omega) (by
    have := Finset.mem_range.mp hi; omega))
    (ibmValue (grid (T / (n + 1)) i) ω) (ibmValue (grid (T / (n + 1)) (i + 1)) ω)
    (hb i (by have := Finset.mem_range.mp hi; omega))
    (hb (i + 1) (by have := Finset.mem_range.mp hi; omega)) (hd.trans_lt hn)
  simpa only [path_time, Nat.cast_add, Nat.cast_one,
    show (4 : ℕ) = 2*2 from rfl, pow_mul, sq_abs] using he

theorem finite_chain (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    spatialIncrements F T n ω + increments F (path ω) T (n + 1) =
      F T (ibmValue T ω)-F 0 (ibmValue 0 ω) := by
  have he : spatialIncrements F T n ω + increments F (path ω) T (n + 1) =
      ∑ i ∈ Finset.range (n + 1),
        (F (time T (n + 1) (i + 1)) (path ω (time T (n + 1) (i + 1))) -
          F (time T (n + 1) i) (path ω (time T (n + 1) i))) := by
    rw [spatialIncrements, increments, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, Finset.sum_range_sub (fun i => F (time T (n + 1) i) (path ω (time T (n + 1) i)))]
  have ht : time T (n + 1) (n + 1) = T := by unfold time; exact div_mul_cancel₀ _ (by positivity)
  rw [ht]
  simp only [show time (T : ℝ) (n + 1) 0 = 0 by simp [time], path,
    Real.toNNReal_coe, Real.toNNReal_zero]

theorem spatialIncrements_tendsto (F : ℝ → ℝ → ℝ)
    (hF : ∀ x, ContDiff ℝ 1 (fun t => F t x))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) (ω : JointSample) :
    Tendsto (fun n => spatialIncrements F T n ω) atTop (𝓝 (target F T ω)) := by
  have h := (tendsto_const_nhds (x := F T (ibmValue T ω)-F 0 (ibmValue 0 ω))).sub
    (increments_tendsto F (path ω) hF hD (path_continuous ω) T.coe_nonneg)
  exact h.congr' (Eventually.of_forall fun n => by
    have he := finite_chain F T n ω
    dsimp [target, correction]
    linarith)

/-- Actual nonseparable C1-time/C4-space signed stochastic chain formula.
Joint continuity of the time partial and fourth spatial derivative is explicit.
No mixed time derivative, fifth spatial derivative or global bound is assumed. -/
theorem sums_tendstoInMeasure (F : ℝ → ℝ → ℝ)
    (hspace : ∀ t, ContDiff ℝ 4 (F t))
    (htime : ∀ x, ContDiff ℝ 1 (fun t => F t x))
    (hfour : Continuous (fun p : ℝ × ℝ => iteratedDeriv 4 (F p.1) p.2))
    (hdt : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (sums F T) atTop
      (fun ω => F T (ibmValue T ω) - F 0 (ibmValue 0 ω) -
        ∫ t in (0 : ℝ)..(T : ℝ), timeDerivative F t (path ω t)) := by
  change TendstoInMeasure jointMeasure (sums F T) atTop (target F T)
  have he := quartic_peano_tendstoInMeasure hT (error F T)
    (fun n => (sums_measurable F hspace T n).sub (spatialIncrements_measurable F hspace T n))
    (fun ω ε hε => error_eventual_bound F hspace hfour T ω hε)
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (sums_measurable F hspace T n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, he⟩ := (he.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [he] with ω hω
  have hp := (spatialIncrements_tendsto F htime hdt T ω).comp (hns.comp hms).tendsto_atTop
  simpa only [Function.comp_def, error, sub_add_cancel, zero_add] using hω.add hp

end OperatorDerivativeRewrite.Foundation.IBMTimeSpaceSimpson
