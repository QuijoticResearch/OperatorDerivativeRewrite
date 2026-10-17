import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Characteristic-measure collision rates and their consistency recursion.
Indices k,l here correspond to the positive particle counts k+1,l+1. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.StickyCollisionRates
set_option backward.isDefEq.respectTransparency false

abbrev Interval := Set.Icc (0:ℝ) 1

def weight (k l : ℕ) (q : Interval) : ℝ := (q:ℝ)^k * (1-(q:ℝ))^l

theorem weight_nonnegative (k l : ℕ) (q : Interval) : 0 ≤ weight k l q := by
  exact mul_nonneg (pow_nonneg q.property.1 _) (pow_nonneg (sub_nonneg.mpr q.property.2) _)

theorem weight_le_one (k l : ℕ) (q : Interval) : weight k l q ≤ 1 := by
  have hq0 : 0 ≤ (q:ℝ) := q.property.1
  have hq1 : (q:ℝ) ≤ 1 := q.property.2
  have ha : (q:ℝ)^k ≤ 1 := pow_le_one₀ hq0 hq1
  have hb : (1-(q:ℝ))^l ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  exact le_trans (mul_le_mul_of_nonneg_right ha (pow_nonneg (by linarith) _))
    (by simpa only [one_mul] using hb)

theorem weight_continuous (k l : ℕ) : Continuous (weight k l) :=
  (continuous_subtype_val.pow k).mul ((continuous_const.sub continuous_subtype_val).pow l)

theorem weight_integrable (ν : Measure Interval) [IsFiniteMeasure ν] (k l : ℕ) :
    Integrable (weight k l) ν := by
  apply (integrable_const (1:ℝ)).mono' (weight_continuous k l).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun q => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (weight_nonnegative k l q)]
      using weight_le_one k l q)

def rate (ν : Measure Interval) (k l : ℕ) : ℝ := ∫ q, weight k l q ∂ν

theorem rate_nonnegative (ν : Measure Interval) (k l : ℕ) : 0 ≤ rate ν k l :=
  integral_nonneg (weight_nonnegative k l)

theorem weight_recursion (k l : ℕ) (q : Interval) :
    weight k l q = weight (k+1) l q + weight k (l+1) q := by
  simp only [weight, pow_succ]
  ring

theorem rate_recursion (ν : Measure Interval) [IsFiniteMeasure ν] (k l : ℕ) :
    rate ν k l = rate ν (k+1) l + rate ν k (l+1) := by
  unfold rate
  rw [← integral_add (weight_integrable ν (k+1) l) (weight_integrable ν k (l+1))]
  exact integral_congr_ae (Filter.Eventually.of_forall (weight_recursion k l))

theorem base_rate (ν : Measure Interval) : rate ν 0 0 = (ν Set.univ).toReal := by
  simp [rate, weight, Measure.real]

def zeroPoint : Interval := ⟨0,by norm_num⟩
def halfPoint : Interval := ⟨1/2,by norm_num⟩

theorem dirac_rate (q : Interval) (k l : ℕ) :
    rate (Measure.dirac q) k l = weight k l q := by
  exact integral_dirac _ _

theorem same_pair_rate : rate (Measure.dirac zeroPoint) 0 0 =
    rate (Measure.dirac halfPoint) 0 0 := by
  simp [dirac_rate, weight]

theorem different_triple_rate : rate (Measure.dirac zeroPoint) 1 0 ≠
    rate (Measure.dirac halfPoint) 1 0 := by
  norm_num [dirac_rate, weight, zeroPoint, halfPoint]

end OperatorDerivativeRewrite.Foundation.StickyCollisionRates
