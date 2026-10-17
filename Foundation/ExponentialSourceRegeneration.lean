import Foundation.IndependentCoordinateBlocks
import Foundation.ConstructedRenewalPoissonLaw

/-! A genuine independent future source and renewal counts after a deterministic arrival index. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ExponentialSourceRegeneration
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount

def tail (n : ℕ) (ω : Sample) : Sample := fun j => holding (n+j) ω

theorem tail_measurable (n : ℕ) : Measurable (tail n) :=
  measurable_pi_iff.mpr (fun j => holding_measurable (n+j))

theorem tail_preserving (n : ℕ) : MeasurePreserving (tail n) probability probability := by
  refine ⟨tail_measurable n, ?_⟩
  unfold probability tail holding
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Nat.add_left_cancel h)

theorem past_tail_independent (n : ℕ) :
    IndepFun (ConstructedRenewalPoissonLaw.initialSegment n) (tail n) probability := by
  exact IndependentCoordinateBlocks.disjoint_families holding_measurable holding_independent
    (fun i : Fin n => i.val) (fun j : ℕ => n+j) (fun i j h => by omega)

theorem split_preserving (n : ℕ) :
    MeasurePreserving (fun ω => (ConstructedRenewalPoissonLaw.initialSegment n ω,tail n ω))
      probability ((FiniteExponentialRenewal.probability n).prod probability) := by
  refine ⟨(ConstructedRenewalPoissonLaw.initialSegment_measurable n).prodMk (tail_measurable n), ?_⟩
  rw [(past_tail_independent n).map_prod_eq_prod_map_map
    (ConstructedRenewalPoissonLaw.initialSegment_measurable n).aemeasurable
    (tail_measurable n).aemeasurable,
    (ConstructedRenewalPoissonLaw.initialSegment_preserving n).map_eq, (tail_preserving n).map_eq]

theorem tail_good_ae (n : ℕ) : ∀ᵐ ω ∂probability, Good (tail n ω) :=
  (tail_preserving n).quasiMeasurePreserving.ae good_ae

theorem clock_add (n m : ℕ) (ω : Sample) :
    clock (n+m) ω = clock n ω + clock m (tail n ω) := by
  simp only [clock, Finset.sum_range_add, tail, holding]

theorem count_at_arrival_add {ω : Sample} (h : Good ω) (n : ℕ) (hf : Good (tail n ω))
    (t : ℝ) (ht : 0 ≤ t) : count (clock n ω+t) ω = n+count t (tail n ω) := by
  have hc : 0 ≤ clock n ω := by
    simpa only [clock_zero] using (good_strictMono h).monotone (Nat.zero_le n)
  apply (ConstructedRenewalPoissonLaw.count_eq_iff h _ (add_nonneg hc ht) _).mpr
  have hfint := count_interval hf t ht
  rw [clock_add, show n+count t (tail n ω)+1 = n+(count t (tail n ω)+1) by omega, clock_add]
  constructor <;> linarith [hfint.1,hfint.2]

def countAfter (n : ℕ) (t : ℝ) (ω : Sample) : ℕ := count (clock n ω+t) ω-n

theorem countAfter_measurable (n : ℕ) (t : ℝ) : Measurable (countAfter n t) := by
  have hc := count_joint_measurable.comp
    (((clock_measurable n).add_const t).prodMk measurable_id)
  have hs : Measurable (fun ω => count (clock n ω+t) ω) := by
    simpa only [Function.comp_def, id_eq] using hc
  exact (measurable_of_countable (fun k : ℕ => k-n)).comp hs

theorem countAfter_eq_tail (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    countAfter n t =ᵐ[probability] fun ω => count t (tail n ω) := by
  filter_upwards [good_ae,tail_good_ae n] with ω hω hf
  rw [countAfter, count_at_arrival_add hω n hf t ht]
  omega

theorem tail_count_law (n : ℕ) (t : ℝ≥0) :
    probability.map (fun ω => count t (tail n ω)) = poissonMeasure t := by
  rw [show (fun ω => count t (tail n ω)) = count t ∘ tail n from rfl,
    ← Measure.map_map (count_measurable t) (tail_measurable n), (tail_preserving n).map_eq]
  exact ConstructedRenewalPoissonLaw.countLaw_eq_poisson t

theorem countAfter_law (n : ℕ) (t : ℝ≥0) :
    probability.map (countAfter n t) = poissonMeasure t := by
  rw [Measure.map_congr (countAfter_eq_tail n t t.coe_nonneg)]
  exact tail_count_law n t

theorem countAfter_independent (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IndepFun (ConstructedRenewalPoissonLaw.initialSegment n) (countAfter n t) probability := by
  have hi := (past_tail_independent n).comp measurable_id (count_measurable t)
  exact hi.congr (Eventually.of_forall (fun _ => rfl)) (countAfter_eq_tail n t ht).symm

abbrev CountPath := ℝ≥0 → ℕ

def countPath (ω : Sample) : CountPath := fun t => count t ω

theorem countPath_measurable : Measurable countPath :=
  measurable_pi_iff.mpr (fun t => count_measurable t)

def afterPath (n : ℕ) (ω : Sample) : CountPath := fun t => countAfter n t ω

theorem afterPath_measurable (n : ℕ) : Measurable (afterPath n) :=
  measurable_pi_iff.mpr (fun t => countAfter_measurable n t)

theorem afterPath_eq_tail (n : ℕ) : afterPath n =ᵐ[probability] countPath ∘ tail n := by
  filter_upwards [good_ae,tail_good_ae n] with ω hω hf
  funext t
  change count (clock n ω+t) ω-n = count t (tail n ω)
  rw [count_at_arrival_add hω n hf t t.coe_nonneg]
  omega

theorem afterPath_preserving (n : ℕ) :
    MeasurePreserving (afterPath n) probability (probability.map countPath) := by
  refine ⟨afterPath_measurable n, ?_⟩
  rw [Measure.map_congr (afterPath_eq_tail n),
    ← Measure.map_map countPath_measurable (tail_measurable n), (tail_preserving n).map_eq]

theorem afterPath_independent (n : ℕ) :
    IndepFun (ConstructedRenewalPoissonLaw.initialSegment n) (afterPath n) probability := by
  have hi := (past_tail_independent n).comp measurable_id countPath_measurable
  exact hi.congr (Eventually.of_forall (fun _ => rfl)) (afterPath_eq_tail n).symm

theorem afterPath_split_preserving (n : ℕ) :
    MeasurePreserving (fun ω => (ConstructedRenewalPoissonLaw.initialSegment n ω,afterPath n ω))
      probability ((FiniteExponentialRenewal.probability n).prod (probability.map countPath)) := by
  refine ⟨(ConstructedRenewalPoissonLaw.initialSegment_measurable n).prodMk
    (afterPath_measurable n), ?_⟩
  rw [(afterPath_independent n).map_prod_eq_prod_map_map
    (ConstructedRenewalPoissonLaw.initialSegment_measurable n).aemeasurable
    (afterPath_measurable n).aemeasurable,
    (ConstructedRenewalPoissonLaw.initialSegment_preserving n).map_eq,
    (afterPath_preserving n).map_eq]

end OperatorDerivativeRewrite.Foundation.ExponentialSourceRegeneration
