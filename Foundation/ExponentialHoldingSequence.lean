import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib

/-! An actual iid exponential holding-time sequence on a countable product probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ExponentialHoldingSequence

def base : Measure ℝ := expMeasure 1

instance base_probability : IsProbabilityMeasure base :=
  isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)

abbrev Sample := ℕ → ℝ

def probability : Measure Sample := Measure.infinitePi (fun _ : ℕ => base)

instance probability_isProbability : IsProbabilityMeasure probability := by
  unfold probability
  infer_instance

def holding (n : ℕ) (ω : Sample) : ℝ := ω n

theorem holding_measurable (n : ℕ) : Measurable (holding n) := measurable_pi_apply n

theorem holding_preserving (n : ℕ) : MeasurePreserving (holding n) probability base :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => base) n

theorem holding_law (n : ℕ) : probability.map (holding n) = base :=
  (holding_preserving n).map_eq

theorem holding_independent : iIndepFun holding probability :=
  iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (by fun_prop)

theorem holding_identDistrib (n m : ℕ) : IdentDistrib (holding n) (holding m) probability probability :=
  ⟨(holding_measurable n).aemeasurable, (holding_measurable m).aemeasurable,
    (holding_law n).trans (holding_law m).symm⟩

theorem base_cdf (x : ℝ) : base.real (Iic x) = if 0 ≤ x then 1-Real.exp (-x) else 0 := by
  rw [← cdf_eq_real]
  simpa only [base, one_mul] using cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1) x

theorem base_tail : base.real (Ioi 1) = Real.exp (-1) := by
  have he := measureReal_compl (μ := base) (s := Iic (1 : ℝ)) measurableSet_Iic
  rw [compl_Iic, probReal_univ, base_cdf] at he
  norm_num at he
  linarith

theorem base_positive : ∀ᵐ x : ℝ ∂base, 0 < x := by
  have hz : base (Iic 0) = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (by
    rw [base_cdf]
    norm_num)
  rw [ae_iff]
  have hs : {x : ℝ | ¬ 0 < x} = Iic 0 := by ext x; simp only [mem_setOf_eq, mem_Iic, not_lt]
  rw [hs]
  exact hz

theorem holding_positive : ∀ᵐ ω ∂probability, ∀ n, 0 < holding n ω :=
  ae_all_iff.mpr (fun n => (holding_preserving n).quasiMeasurePreserving.ae base_positive)

def successMap : ℝ → ℝ := (Ioi (1 : ℝ)).indicator 1

theorem successMap_measurable : Measurable successMap := measurable_const.indicator measurableSet_Ioi

theorem successMap_bounds (x : ℝ) : 0 ≤ successMap x ∧ successMap x ≤ 1 := by
  simp only [successMap, indicator_apply]
  split_ifs <;> norm_num

def success (n : ℕ) (ω : Sample) : ℝ := successMap (holding n ω)

theorem success_integrable (n : ℕ) : Integrable (success n) probability := by
  apply Integrable.of_bound (successMap_measurable.comp (holding_measurable n)).aestronglyMeasurable 1
  exact Eventually.of_forall (fun ω => by
    change ‖successMap (holding n ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (successMap_bounds _).1]
    exact (successMap_bounds _).2)

theorem success_integral (n : ℕ) : (∫ ω, success n ω ∂probability) = Real.exp (-1) := by
  have he := integral_map (μ := probability) (holding_measurable n).aemeasurable
    successMap_measurable.aestronglyMeasurable
  rw [holding_law n] at he
  calc
    _ = ∫ x, successMap x ∂base := he.symm
    _ = _ := by rw [successMap, integral_indicator_one measurableSet_Ioi, base_tail]

theorem success_independent : iIndepFun success probability :=
  holding_independent.comp (fun _ => successMap) (fun _ => successMap_measurable)

theorem success_identDistrib (n m : ℕ) : IdentDistrib (success n) (success m) probability probability :=
  (holding_identDistrib n m).comp successMap_measurable

end OperatorDerivativeRewrite.Foundation.ExponentialHoldingSequence
