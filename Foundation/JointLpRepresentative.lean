import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.SpecificLimits.Normed

/-! Joint sample versions on the ORIGINAL measure space, with section agreement
for EVERY parameter. Finite measure, complete second-countable target and separable
L2 are explicit. No parameter measure, path continuity or universal null set is used. -/
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.JointLpRepresentative
variable {T Ω E : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure Ω} [IsFiniteMeasure μ]
  [SeparableSpace (Lp E 2 μ)]

private def eps (n : ℕ) : ℝ := (1/4) * (1/2)^n
private theorem eps_pos (n : ℕ) : 0 < eps n := by unfold eps; positivity

theorem exists_joint_representative (F : T → Lp E 2 μ) (hF : StronglyMeasurable F) :
    ∃ g : T × Ω → E, StronglyMeasurable g ∧ ∀ t, (F t) =ᵐ[μ] fun ω => g (t,ω) := by
  classical
  borelize ↥(Lp E 2 μ)
  let d := denseSeq (Lp E 2 μ)
  have hd : DenseRange d := denseRange_denseSeq _
  have ex (n : ℕ) (t : T) : ∃ j, dist (F t) (d j) < eps n :=
    Metric.denseRange_iff.mp hd (F t) (eps n) (eps_pos n)
  let ix (n : ℕ) (t : T) := Nat.find (ex n t)
  have hix (n : ℕ) : Measurable (ix n) :=
    measurable_find (ex n) (fun j =>
      measurableSet_lt (hF.measurable.dist measurable_const) measurable_const)
  let rep (j : ℕ) := (Lp.aestronglyMeasurable (d j)).mk (d j)
  have hrep (j : ℕ) : StronglyMeasurable (rep j) :=
    (Lp.aestronglyMeasurable (d j)).stronglyMeasurable_mk
  have arep (j : ℕ) : d j =ᵐ[μ] rep j := (Lp.aestronglyMeasurable (d j)).ae_eq_mk
  let a (n : ℕ) (z : T × Ω) := rep (ix n z.1) z.2
  have ha (n : ℕ) : StronglyMeasurable (a n) := by
    have hm : Measurable (fun z : ℕ × Ω => rep z.1 z.2) :=
      measurable_from_prod_countable_right (fun j => (hrep j).measurable)
    exact (hm.comp (((hix n).comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  have ae_a (n : ℕ) (t : T) : (d (ix n t)) =ᵐ[μ] (fun ω => a n (t,ω)) := arep _
  have bound (n : ℕ) (t : T) : dist (F t) (d (ix n t)) < eps n := Nat.find_spec (ex n t)
  have hnorm (N n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) (t : T) :
      ‖d (ix n t) - d (ix m t)‖ < (1/2:ℝ)^N := by
    have he (k : ℕ) (hk : N ≤ k) : eps k ≤ eps N := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) (by norm_num)
    have hc : dist (d (ix n t)) (d (ix m t)) < eps n + eps m := by
      calc
        _ ≤ dist (d (ix n t)) (F t) + dist (F t) (d (ix m t)) := dist_triangle _ _ _
        _ < eps n + eps m := add_lt_add (by simpa [dist_comm] using bound n t) (bound m t)
    rw [dist_eq_norm] at hc
    have hp : 0 < (1/2:ℝ)^N := by positivity
    have h1 := he n hn
    have h2 := he m hm
    unfold eps at h1 h2 hc
    linarith
  have heLp (N n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) (t : T) :
      eLpNorm ((fun ω => a n (t,ω)) - (fun ω => a m (t,ω))) 2 μ < (2⁻¹:ℝ≥0∞)^N := by
    have heq : ((d (ix n t) - d (ix m t)) : Lp E 2 μ) =ᵐ[μ]
        ((fun ω => a n (t,ω)) - (fun ω => a m (t,ω))) :=
      (Lp.coeFn_sub _ _).trans ((ae_a n t).sub (ae_a m t))
    rw [← eLpNorm_congr_ae heq, ← Lp.enorm_def, ← ofReal_norm]
    have hh := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < (1/2:ℝ)^N)).mpr
      (hnorm N n m hn hm t)
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2)] at hh
    have hhalf : ENNReal.ofReal (1/2:ℝ) = (2⁻¹:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
      norm_num
    rw [hhalf] at hh
    exact hh
  let g (z : T × Ω) := limUnder atTop (fun n => a n z)
  have hg : StronglyMeasurable g := StronglyMeasurable.limUnder ha
  refine ⟨g,hg,fun t => ?_⟩
  have hs (n : ℕ) : AEStronglyMeasurable (fun ω => a n (t,ω)) μ :=
    ((ha n).comp_measurable measurable_prodMk_left).aestronglyMeasurable
  have hb : ∑' n : ℕ, (2⁻¹:ℝ≥0∞)^n ≠ ∞ := by rw [ENNReal.tsum_geometric_two]; norm_num
  have hc := fun N n m hn hm => heLp N n m hn hm t
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => a n (t,ω)) atTop (𝓝 (g (t,ω))) := by
    filter_upwards [Lp.ae_tendsto_of_cauchy_eLpNorm hs (by norm_num : (1:ℝ≥0∞) ≤ 2) hb hc] with ω hω
    obtain ⟨l,hl⟩ := hω
    simpa only [g,hl.limUnder_eq] using hl
  have hlp : Tendsto (fun n => d (ix n t)) atTop (𝓝 (F t)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) (fun n => (by simpa [dist_comm] using (bound n t).le))
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)).const_mul (1/4:ℝ)
    change Tendsto (fun n => (1/4:ℝ)*(1/2:ℝ)^n) atTop (𝓝 0)
    simpa only [mul_zero] using hh
  have him : TendstoInMeasure μ (fun n => (fun ω => a n (t,ω))) atTop (F t) := by
    have he := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hlp
    apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2:ℝ≥0∞) ≠ 0)
    convert he using 1
    funext n
    exact eLpNorm_congr_ae ((ae_a n t).symm.sub EventuallyEq.rfl)
  exact tendstoInMeasure_ae_unique him (tendstoInMeasure_of_tendsto_ae hs hlim)
end OperatorDerivativeRewrite.Foundation.JointLpRepresentative
