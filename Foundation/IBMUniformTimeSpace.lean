import Foundation.IBMTimeSpaceSimpson
import Foundation.IBMTimeSpacePrefixQuadrature

/-! Uniform-prefix error for the actual nonseparable IBM chain formula. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformTimeSpace
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMContinuousQuadrature IBMTimeSpaceQuadrature IBMTimeSpaceSimpson
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def snapshot (F : ℝ → ℝ → ℝ) (ω : JointSample) (t : ℝ) : ℝ :=
  F t (path ω t)-F 0 (path ω 0)-∫ s in (0 : ℝ)..t, timeDerivative F s (path ω s)

theorem target_snapshot (F : ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : JointSample) :
    target F t ω = snapshot F ω t := by
  simp only [target, correction, snapshot, path, Real.toNNReal_coe, Real.toNNReal_zero]

theorem node_snapshot (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (ω : JointSample) :
    snapshot F ω (time T (n + 1) m) = target F (grid (T / (n + 1)) m) ω := by
  rw [IBMContinuousWeightedQuartic.real_time_eq_grid]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (target_snapshot F (grid (T / (n + 1)) m) ω).symm

def prefixSums (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range m, IBMSimpsonPeano.simpson (deriv (F (time T (n + 1) i)))
    (path ω (time T (n + 1) i)) (path ω (time T (n + 1) (i + 1)))

def spatialPrefix (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range m, (F (time T (n + 1) i) (path ω (time T (n + 1) (i + 1))) -
    F (time T (n + 1) i) (path ω (time T (n + 1) i)))

def spatialError (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (ω : JointSample) : ℝ :=
  prefixSums F T n m ω-spatialPrefix F T n m ω

def spatialMaximum (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  (Finset.range (n + 2)).sup' Finset.nonempty_range_add_one (fun m => |spatialError F T n m ω|)

def error (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (ω : JointSample) : ℝ :=
  prefixSums F T n m ω-snapshot F ω (time T (n + 1) m)

def maximum (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  (Finset.range (n + 2)).sup' Finset.nonempty_range_add_one (fun m => |error F T n m ω|)

theorem prefixSums_measurable (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 4 (F t))
    (T : ℝ≥0) (n m : ℕ) : Measurable (prefixSums F T n m) := by
  apply Finset.measurable_sum
  intro i hi
  have hc : Continuous (fun p : ℝ × ℝ =>
      IBMSimpsonPeano.simpson (deriv (F (time T (n + 1) i))) p.1 p.2) := by
    have hg := (hF (time T (n + 1) i)).continuous_deriv (by norm_num)
    unfold IBMSimpsonPeano.simpson
    fun_prop
  exact hc.measurable.comp ((path_measurable _).prodMk (path_measurable _))

theorem spatialPrefix_measurable (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 4 (F t))
    (T : ℝ≥0) (n m : ℕ) : Measurable (spatialPrefix F T n m) := by
  apply Finset.measurable_sum
  intro i hi
  exact (((hF _).continuous.measurable.comp (path_measurable _)).sub
    ((hF _).continuous.measurable.comp (path_measurable _)))

theorem spatialMaximum_nonneg (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    0 ≤ spatialMaximum F T n ω :=
  (abs_nonneg _).trans (Finset.le_sup' (fun m => |spatialError F T n m ω|)
    (b := 0) (by simp))

theorem spatialMaximum_measurable (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 4 (F t))
    (T : ℝ≥0) (n : ℕ) : Measurable (spatialMaximum F T n) := by
  apply Finset.measurable_range_sup''
  intro m hm
  exact continuous_abs.measurable.comp ((prefixSums_measurable F hF T n m).sub
    (spatialPrefix_measurable F hF T n m))

theorem maximum_nonneg (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    0 ≤ maximum F T n ω :=
  (abs_nonneg _).trans (Finset.le_sup' (fun m => |error F T n m ω|)
    (b := 0) (by simp))

theorem maximum_measurable (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 4 (F t))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) (n : ℕ) : Measurable (maximum F T n) := by
  apply Finset.measurable_range_sup''
  intro m hm
  have he : error F T n m = fun ω => prefixSums F T n m ω-target F (grid (T / (n + 1)) m) ω := by
    funext ω
    rw [error,node_snapshot]
  rw [he]
  exact continuous_abs.measurable.comp ((prefixSums_measurable F hF T n m).sub
    (target_measurable F hF hD _))

theorem error_le_maximum (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (hm : m ≤ n + 1)
    (ω : JointSample) : |error F T n m ω| ≤ maximum F T n ω :=
  Finset.le_sup' (fun k => |error F T n k ω|) (Finset.mem_range.mpr (by omega))

theorem spatialMaximum_eventual_bound (F : ℝ → ℝ → ℝ)
    (hF : ∀ t, ContDiff ℝ 4 (F t))
    (hD : Continuous (fun p : ℝ × ℝ => iteratedDeriv 4 (F p.1) p.2))
    (T : ℝ≥0) (ω : JointSample) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, spatialMaximum F T n ω ≤ ε * IBMUniformQuarticFamily.quartic T (n + 1) ω := by
  let R := IBMContinuousBlockWeights.pathBound id continuous_id T ω
  obtain ⟨δ, hδ, hu⟩ := IBMTimeSpacePeano.compact_error_bound F hF hD T R ε hε
  filter_upwards [(IBMUniformFifthRemainder.mesh_tendsto T ω).eventually (gt_mem_nhds hδ)] with n hn
  apply Finset.sup'_le
  intro m hm
  have hmN : m ≤ n + 1 := by have := Finset.mem_range.mp hm; omega
  unfold spatialError prefixSums spatialPrefix
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans (b := ε * ∑ i ∈ Finset.range m,
    (ibmValue (grid (T / (n + 1)) (i + 1)) ω -
      ibmValue (grid (T / (n + 1)) i) ω)^4)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiN : i + 1 ≤ n + 1 := (Finset.mem_range.mp hi).trans_le hmN
    have hb (j : ℕ) (hj : j ≤ n + 1) : |ibmValue (grid (T / (n + 1)) j) ω| ≤ R :=
      IBMContinuousBlockWeights.pathBound_bound id continuous_id T ω _
        (IBMActualPeanoRemainder.grid_le T n j hj)
    have hd : |ibmValue (grid (T / (n + 1)) (i + 1)) ω -
        ibmValue (grid (T / (n + 1)) i) ω| ≤ IBMUniformFifthRemainder.mesh T n ω :=
      Finset.le_sup' (fun k => |ibmValue (grid (T / (n + 1)) (k + 1)) ω -
        ibmValue (grid (T / (n + 1)) k) ω|) (Finset.mem_range.mpr (by omega))
    have h := hu (time T (n + 1) i) (time_mem T.coe_nonneg (by omega) (by omega))
      (ibmValue (grid (T / (n + 1)) i) ω)
      (ibmValue (grid (T / (n + 1)) (i + 1)) ω)
      (hb i (by omega)) (hb (i + 1) hiN) (hd.trans_lt hn)
    simpa only [path_time, Nat.cast_add, Nat.cast_one, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using h
  · apply mul_le_mul_of_nonneg_left _ hε.le
    unfold IBMUniformQuarticFamily.quartic
    simp only [IBMUniformQuarticFamily.segment, Nat.cast_add, Nat.cast_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmN)
      (fun _ _ _ => by positivity)

theorem spatialMaximum_tendstoInMeasure (F : ℝ → ℝ → ℝ)
    (hF : ∀ t, ContDiff ℝ 4 (F t))
    (hD : Continuous (fun p : ℝ × ℝ => iteratedDeriv 4 (F p.1) p.2))
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (spatialMaximum F T) atTop (fun _ => (0 : ℝ)) := by
  apply IBMActualSimpson.quartic_peano_tendstoInMeasure hT _ (spatialMaximum_measurable F hF T)
  intro ω ε hε
  simpa only [abs_of_nonneg (spatialMaximum_nonneg F T _ ω)] using
    spatialMaximum_eventual_bound F hF hD T ω hε

theorem finite_chain (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (ω : JointSample) :
    spatialPrefix F T n m ω + IBMTimeSpacePrefixQuadrature.increments F (path ω) T (n + 1) m =
      F (time T (n + 1) m) (path ω (time T (n + 1) m))-F 0 (path ω 0) := by
  have he : spatialPrefix F T n m ω + IBMTimeSpacePrefixQuadrature.increments F (path ω) T (n + 1) m =
      ∑ i ∈ Finset.range m,
        (F (time T (n + 1) (i + 1)) (path ω (time T (n + 1) (i + 1))) -
          F (time T (n + 1) i) (path ω (time T (n + 1) i))) := by
    rw [spatialPrefix, IBMTimeSpacePrefixQuadrature.increments, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, Finset.sum_range_sub (fun i => F (time T (n + 1) i) (path ω (time T (n + 1) i)))]
  simp only [time, Nat.cast_zero, mul_zero]

theorem maximum_bound (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    maximum F T n ω ≤ spatialMaximum F T n ω +
      IBMTimeSpacePrefixQuadrature.errorMaximum F (path ω) T n := by
  apply Finset.sup'_le
  intro m hm
  have he : error F T n m ω = spatialError F T n m ω -
      (IBMTimeSpacePrefixQuadrature.increments F (path ω) T (n + 1) m -
        ∫ t in (0 : ℝ)..time T (n + 1) m, timeDerivative F t (path ω t)) := by
    have h := finite_chain F T n m ω
    unfold error spatialError snapshot
    linarith
  rw [he]
  exact (abs_sub _ _).trans (add_le_add
    (Finset.le_sup' (fun k => |spatialError F T n k ω|) hm)
    (IBMTimeSpacePrefixQuadrature.error_le_maximum F (path ω) T n m
      (by have := Finset.mem_range.mp hm; omega)))

/-- The actual nonseparable signed stochastic chain rule holds uniformly over
ALL grid prefixes, with the samplewise maximum tending to zero in probability. -/
theorem maximum_tendstoInMeasure (F : ℝ → ℝ → ℝ)
    (hspace : ∀ t, ContDiff ℝ 4 (F t))
    (htime : ∀ x, ContDiff ℝ 1 (fun t => F t x))
    (hfour : Continuous (fun p : ℝ × ℝ => iteratedDeriv 4 (F p.1) p.2))
    (hdt : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (maximum F T) atTop (fun _ => (0 : ℝ)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (maximum_measurable F hspace hdt T n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms,hms,he⟩ := ((spatialMaximum_tendstoInMeasure F hspace hfour hT).comp
    hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [he] with ω hω
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (maximum_nonneg F T _ ω)]
  have ht := (IBMTimeSpacePrefixQuadrature.errorMaximum_tendsto F (path ω) htime hdt
    (path_continuous ω) T.coe_nonneg).comp (hns.comp hms).tendsto_atTop
  apply squeeze_zero (fun _ => maximum_nonneg F T _ ω) (fun _ => maximum_bound F T _ ω)
  simpa only [Function.comp_def, add_zero] using hω.add ht

end OperatorDerivativeRewrite.Foundation.IBMUniformTimeSpace
