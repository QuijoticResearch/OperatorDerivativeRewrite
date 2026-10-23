import Foundation.IBMFourthPeano
import Foundation.IBMUniformFifthRemainder
import Foundation.IBMContinuousBlockWeights
import Foundation.IBMContinuousWeightedQuartic

/-! Total absolute fourth Taylor error for actual IBM on the full C4 domain.
Compact path geometry replaces a global fifth-derivative bound. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMActualPeanoRemainder
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformFifthRemainder IBMUniformQuarticFamily IBMUniformQuarticVariation
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

theorem term_measurable (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (s t : ℝ≥0) :
    Measurable (fun ω => IBMFourthTaylor.remainder f (ibmValue s ω) (ibmValue t ω)) := by
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  exact (IBMFourthPeano.remainder_continuous f hf).measurable.comp ((hm s).prodMk (hm t))

theorem absolute_measurable (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (T : ℝ≥0) (n : ℕ) :
    Measurable (absoluteRemainderSum f T n) := by
  apply Finset.measurable_sum
  intro i hi
  exact continuous_abs.measurable.comp (term_measurable f hf _ _)

theorem signed_measurable (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (T : ℝ≥0) (n : ℕ) :
    Measurable (remainderSum f T n) := by
  apply Finset.measurable_sum
  intro i hi
  exact term_measurable f hf _ _

theorem absolute_nonneg (f : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    0 ≤ absoluteRemainderSum f T n ω :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem grid_le (T : ℝ≥0) (n j : ℕ) (hj : j ≤ n + 1) :
    grid (T/(n + 1)) j ≤ T := by
  apply NNReal.coe_le_coe.mp
  have h := IBMContinuousQuadrature.time_mem T.coe_nonneg
    (by omega : 0 < n + 1) hj
  rw [IBMContinuousWeightedQuartic.real_time_eq_grid] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h.2

/-- For every sample and every epsilon, eventually the TOTAL absolute
Taylor error is at most epsilon times the actual quartic sum. -/
theorem absolute_eventual_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (T : ℝ≥0)
    (ω : JointSample) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, absoluteRemainderSum f T n ω ≤ ε*quartic T (n + 1) ω := by
  let R := IBMContinuousBlockWeights.pathBound id continuous_id T ω
  obtain ⟨δ, hδ, hu⟩ := IBMFourthPeano.compact_remainder_bound f hf R ε hε
  filter_upwards [(mesh_tendsto T ω).eventually (gt_mem_nhds hδ)] with n hn
  unfold absoluteRemainderSum
  simp only [quartic, IBMUniformQuarticFamily.segment, Nat.cast_add, Nat.cast_one]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hb (j : ℕ) (hj : j ≤ n + 1) : |ibmValue (grid (T/(n + 1)) j) ω| ≤ R := by
    exact IBMContinuousBlockWeights.pathBound_bound id continuous_id T ω _ (grid_le T n j hj)
  have hd : |ibmValue (grid (T/(n + 1)) (i + 1)) ω -
      ibmValue (grid (T/(n + 1)) i) ω| ≤ mesh T n ω :=
    Finset.le_sup' (fun k => |ibmValue (grid (T/(n + 1)) (k + 1)) ω -
      ibmValue (grid (T/(n + 1)) k) ω|) hi
  have h := hu (ibmValue (grid (T/(n + 1)) i) ω)
    (ibmValue (grid (T/(n + 1)) (i + 1)) ω)
    (hb i (by have := Finset.mem_range.mp hi; omega))
    (hb (i + 1) (by have := Finset.mem_range.mp hi; omega)) (hd.trans_lt hn)
  simpa only [show (4 : ℕ) = 2*2 from rfl, pow_mul, sq_abs] using h

/-- Genuine total absolute remainder decay, with only C4 regularity.
No global derivative bound, fifth derivative, or sample moment is assumed. -/
theorem absolute_tendstoInMeasure (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (absoluteRemainderSum f T) atTop (fun _ => (0 : ℝ)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (absolute_measurable f hf T n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hq⟩ :=
    ((quartic_tendstoInMeasure hT).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hq] with ω hω
  have hQ : Tendsto (fun i => quartic T (ns (ms i)+1) ω) atTop (𝓝 (3*(T : ℝ))) := by
    simpa only [Function.comp_def] using hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B : ℝ := 3*(T : ℝ)+1
  have hB : 0 < B := by dsimp [B]; positivity
  have he : 0 < ε/(2*B) := by positivity
  have hb := (hns.comp hms).tendsto_atTop.eventually
    (absolute_eventual_bound f hf T ω he)
  filter_upwards [hb, hQ.eventually (gt_mem_nhds (by dsimp [B]; linarith : 3*(T : ℝ) < B))]
    with i hi hqi
  simp only [Function.comp_def] at hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (absolute_nonneg f T (ns (ms i)) ω)]
  have hm := mul_le_mul_of_nonneg_left hqi.le he.le
  have hr : (ε/(2*B))*B = ε/2 := by field_simp
  linarith

theorem signed_tendstoInMeasure (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (remainderSum f T) atTop (fun _ => (0 : ℝ)) := by
  have ha := tendstoInMeasure_iff_measureReal_norm.mp (absolute_tendstoInMeasure f hf hT)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have hb (n : ℕ) :
      jointMeasure.real {ω | ε ≤ |remainderSum f T n ω|} ≤
      jointMeasure.real {ω | ε ≤ |absoluteRemainderSum f T n ω|} := by
    apply measureReal_mono (μ := jointMeasure) (h₂ := measure_ne_top _ _)
    intro ω hω
    have hs : |remainderSum f T n ω| ≤ absoluteRemainderSum f T n ω :=
      Finset.abs_sum_le_sum_abs _ _
    change ε ≤ |remainderSum f T n ω| at hω
    exact hω.trans (hs.trans (le_abs_self _))
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [sub_zero, Real.norm_eq_abs] using ha ε hε

end OperatorDerivativeRewrite.Foundation.IBMActualPeanoRemainder
