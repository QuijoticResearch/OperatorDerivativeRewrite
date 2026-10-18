import Foundation.MarkedPrefixFiltration
import Foundation.CyclicCenteredKernel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Independence.Integration

/-! Genuine predictable stochastic integrals for every nonzero cyclic character. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.CyclicPredictableIntegral
open MarkedRenewalRealization FiniteMarkedRenewalMarginals
variable (N : ℕ) [NeZero N]

abbrev Source := MarkSample (ZMod N)
abbrev Coefficients := (n : ℕ) → Prefix (ZMod N) n → ℂ

def probability : Measure (Source N) := marks (CyclicRootProbabilityNoise.probability N)

instance probability_isProbability : IsProbabilityMeasure (probability N) := by
  unfold probability
  infer_instance

abbrev history := MarkedPrefixFiltration.history (ZMod N)

theorem prefix_past (n : ℕ) : Measurable[history N n] (initialSegment n) :=
  MarkedPrefixFiltration.prefix_past (ZMod N) n

theorem coefficient_past (H : Coefficients N) (n : ℕ) :
    StronglyMeasurable[history N n] (fun η => H n (initialSegment n η)) :=
  MarkedPrefixFiltration.coefficient_past (ZMod N) n (H n) (measurable_of_countable _)

theorem coefficient_integrable (H : Coefficients N) (n : ℕ) :
    Integrable (fun η => H n (initialSegment n η)) (probability N) :=
  MarkedPrefixFiltration.prefix_integrable (ZMod N) (CyclicRootProbabilityNoise.probability N)
    n (H n) Integrable.of_finite

theorem fresh_independent (n : ℕ) :
    Indep (MeasurableSpace.comap (fun η : Source N => η n) inferInstance)
      (history N n) (probability N) :=
  MarkedPrefixFiltration.fresh_independent (ZMod N) (CyclicRootProbabilityNoise.probability N) n

def freshCharacter (j : ZMod N) (n : ℕ) (η : Source N) : ℂ := ZMod.stdAddChar (j*η n)

theorem freshCharacter_measurable (j : ZMod N) (n : ℕ) : Measurable (freshCharacter N j n) :=
  (measurable_of_countable (fun k : ZMod N => ZMod.stdAddChar (j*k))).comp (measurable_pi_apply n)

theorem freshCharacter_integrable (j : ZMod N) (n : ℕ) :
    Integrable (freshCharacter N j n) (probability N) :=
  (mark_preserving (CyclicRootProbabilityNoise.probability N) n).integrable_comp_of_integrable
    (show Integrable (fun k : ZMod N => (ZMod.stdAddChar (j*k) : ℂ))
      (CyclicRootProbabilityNoise.probability N) from Integrable.of_finite)

theorem freshCharacter_mean (j : ZMod N) (hj : j ≠ 0) (n : ℕ) :
    (∫ η, freshCharacter N j n η ∂probability N) = 0 := by
  have he := integral_map (μ := marks (CyclicRootProbabilityNoise.probability N))
    (measurable_pi_apply n).aemeasurable
    (measurable_of_countable (fun k : ZMod N => (ZMod.stdAddChar (j*k) : ℂ))).aestronglyMeasurable
  rw [(mark_preserving (CyclicRootProbabilityNoise.probability N) n).map_eq] at he
  change (∫ η, (ZMod.stdAddChar (j*η n) : ℂ) ∂marks (CyclicRootProbabilityNoise.probability N)) = 0
  rw [← he]
  simpa [hj] using CyclicMarkRepresentation.character_gram N j 0

theorem freshCharacter_independent (j : ZMod N) (n : ℕ) :
    Indep (MeasurableSpace.comap (freshCharacter N j n) inferInstance) (history N n) (probability N) := by
  have hm : Measurable[MeasurableSpace.comap (fun η : Source N => η n) inferInstance]
      (freshCharacter N j n) :=
    (measurable_of_countable (fun k : ZMod N => (ZMod.stdAddChar (j*k) : ℂ))).comp
      (comap_measurable (fun η : Source N => η n))
  exact indep_of_indep_of_le (fresh_independent N n) hm.comap_le le_rfl

theorem freshCharacter_condExp (j : ZMod N) (hj : j ≠ 0) (n : ℕ) :
    (probability N)[freshCharacter N j n | history N n] =ᵐ[probability N] fun _ => (0 : ℂ) := by
  have he := condExp_indep_eq (freshCharacter_measurable N j n).comap_le ((history N).le n)
    (comap_measurable (freshCharacter N j n)).stronglyMeasurable (freshCharacter_independent N j n)
  simpa only [freshCharacter_mean N j hj n] using he

def increment (j : ZMod N) (H : Coefficients N) (n : ℕ) (η : Source N) : ℂ :=
  H n (initialSegment n η)*freshCharacter N j n η

theorem coefficient_fresh_independent (j : ZMod N) (H : Coefficients N) (n : ℕ) :
    IndepFun (fun η => H n (initialSegment n η)) (freshCharacter N j n) (probability N) :=
  indep_of_indep_of_le (freshCharacter_independent N j n).symm
    (coefficient_past N H n).measurable.comap_le le_rfl

theorem increment_integrable (j : ZMod N) (H : Coefficients N) (n : ℕ) :
    Integrable (increment N j H n) (probability N) :=
  (coefficient_fresh_independent N j H n).integrable_mul
    (coefficient_integrable N H n) (freshCharacter_integrable N j n)

theorem increment_condExp (j : ZMod N) (hj : j ≠ 0) (H : Coefficients N) (n : ℕ) :
    (probability N)[increment N j H n | history N n] =ᵐ[probability N] fun _ => (0 : ℂ) := by
  have he := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    (coefficient_past N H n) (increment_integrable N j H n) (freshCharacter_integrable N j n)
  have hz := freshCharacter_condExp N j hj n
  filter_upwards [he,hz] with η he hz
  change (probability N)[increment N j H n | history N n] η =
    H n (initialSegment n η)*(probability N)[freshCharacter N j n | history N n] η at he
  rw [he,hz,mul_zero]

def stochasticIntegral (j : ZMod N) (H : Coefficients N) (n : ℕ) (η : Source N) : ℂ :=
  ∑ i ∈ Finset.range n, increment N j H i η

theorem stochasticIntegral_adapted (j : ZMod N) (H : Coefficients N) :
    StronglyAdapted (history N) (stochasticIntegral N j H) := by
  intro n
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hH := (coefficient_past N H i).mono ((history N).mono hin.le)
  have hm : Measurable[history N n] (fun η : Source N => η i) :=
    (measurable_pi_apply (⟨i,hin⟩ : Fin n)).comp (prefix_past N n)
  exact hH.measurable.mul
    ((measurable_of_countable (fun k : ZMod N => (ZMod.stdAddChar (j*k) : ℂ))).comp hm)

theorem stochasticIntegral_integrable (j : ZMod N) (H : Coefficients N) (n : ℕ) :
    Integrable (stochasticIntegral N j H n) (probability N) :=
  integrable_finsetSum (Finset.range n) (fun i _ => increment_integrable N j H i)

theorem stochasticIntegral_successor (j : ZMod N) (H : Coefficients N) (n : ℕ) :
    stochasticIntegral N j H (n+1)-stochasticIntegral N j H n = increment N j H n := by
  funext η
  simp only [stochasticIntegral,Pi.sub_apply,Finset.sum_range_succ,add_sub_cancel_left]

theorem stochasticIntegral_martingale (j : ZMod N) (hj : j ≠ 0) (H : Coefficients N) :
    Martingale (stochasticIntegral N j H) (history N) (probability N) := by
  apply martingale_of_condExp_sub_eq_zero_nat (stochasticIntegral_adapted N j H)
    (stochasticIntegral_integrable N j H)
  intro n
  rw [stochasticIntegral_successor]
  exact increment_condExp N j hj H n

def totalIntegral (H : ZMod N → Coefficients N) : ℕ → Source N → ℂ :=
  ∑ j ∈ Finset.univ.erase (0 : ZMod N), stochasticIntegral N j (H j)

theorem totalIntegral_martingale (H : ZMod N → Coefficients N) :
    Martingale (totalIntegral N H) (history N) (probability N) := by
  classical
  have hs : ∀ s : Finset (ZMod N), (0 : ZMod N) ∉ s →
      Martingale (∑ j ∈ s, stochasticIntegral N j (H j)) (history N) (probability N) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using martingale_zero ℂ (history N) (probability N)
    | @insert j s hj ih =>
      intro h0
      have hj0 : j ≠ 0 := by intro he; subst j; exact h0 (Finset.mem_insert_self _ _)
      have h0s : (0 : ZMod N) ∉ s := fun h => h0 (Finset.mem_insert_of_mem h)
      simpa only [Finset.sum_insert hj] using
        (stochasticIntegral_martingale N j hj0 (H j)).add (ih h0s)
  exact hs _ (by simp)

theorem totalIntegral_zero (H : ZMod N → Coefficients N) : totalIntegral N H 0 = 0 := by
  funext η
  simp [totalIntegral,stochasticIntegral]

end OperatorDerivativeRewrite.Foundation.CyclicPredictableIntegral
