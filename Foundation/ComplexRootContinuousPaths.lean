import Foundation.ComplexRootOneStepCalculus
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! Actual continuous complex sample paths carrying the finite independent root walks. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.ComplexRootContinuousPaths
open ComplexFourthRootWalk

abbrev Path := {ω : C(ℝ, ℂ) // ω 0 = 0}

def ramp (n : ℕ) (i : Fin n) (t : ℝ) : ℝ := min 1 (max 0 ((n : ℝ)*t-i.val))

theorem ramp_continuous (n : ℕ) (i : Fin n) : Continuous (ramp n i) := by
  unfold ramp
  fun_prop

theorem ramp_zero (n : ℕ) (i : Fin n) : ramp n i 0 = 0 := by
  unfold ramp
  rw [mul_zero, zero_sub, max_eq_left (neg_nonpos.mpr (Nat.cast_nonneg i.val))]
  norm_num

theorem ramp_one (n : ℕ) (i : Fin n) : ramp n i 1 = 1 := by
  have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
  unfold ramp
  rw [mul_one, max_eq_right (by linarith), min_eq_left (by linarith)]

theorem ramp_grid (n : ℕ) (hn : 0 < n) (i : Fin n) (k : ℕ) :
    ramp n i ((k : ℝ)/n) = if i.val < k then 1 else 0 := by
  have hne : (n : ℝ) ≠ 0 := by positivity
  have he : (n : ℝ)*((k : ℝ)/n) = k := by field_simp
  rw [ramp, he]
  by_cases hi : i.val < k
  · have hh : (i.val : ℝ)+1 ≤ k := by exact_mod_cast hi
    rw [if_pos hi, max_eq_right (by linarith), min_eq_left (by linarith)]
  · have hh : (k : ℝ) ≤ i.val := by exact_mod_cast (Nat.le_of_not_gt hi)
    rw [if_neg hi, max_eq_left (by linarith)]
    norm_num

def path (n : ℕ) (a : ℝ) (ω : Sample n) : Path :=
  ⟨⟨fun t => ∑ i : Fin n, (ramp n i t : ℂ) * increment n a i ω, by
      apply continuous_finset_sum
      intro i _
      exact (Complex.continuous_ofReal.comp (ramp_continuous n i)).mul continuous_const⟩,
    by
      change (∑ i : Fin n, (ramp n i 0 : ℂ) * increment n a i ω) = 0
      simp only [ramp_zero, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]⟩

theorem path_measurable (n : ℕ) (a : ℝ) : Measurable (path n a) := measurable_of_countable _

theorem path_terminal (n : ℕ) (a : ℝ) (ω : Sample n) : (path n a ω).val 1 = terminal n a ω := by
  change (∑ i : Fin n, (ramp n i 1 : ℂ) * increment n a i ω) = _
  simp only [ramp_one, Complex.ofReal_one, one_mul, terminal]

theorem path_grid (n : ℕ) (hn : 0 < n) (a : ℝ) (k : ℕ) (ω : Sample n) :
    (path n a ω).val ((k : ℝ)/n) = position n a k ω := by
  change (∑ i : Fin n, (ramp n i ((k : ℝ)/n) : ℂ) * increment n a i ω) = _
  simp only [ramp_grid n hn, position, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero, ite_mul, one_mul, zero_mul]

theorem path_mean (n : ℕ) (a t : ℝ) :
    (∫ ω, (path n a ω).val t ∂probability n) = 0 := by
  change (∫ ω, (∑ i : Fin n, (ramp n i t : ℂ) * increment n a i ω) ∂probability n) = 0
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_const_mul, increment_mean, mul_zero]
  exact Finset.sum_const_zero

def law (n : ℕ) (a : ℝ) : Measure Path := (probability n).map (path n a)

instance law_isProbability (n : ℕ) (a : ℝ) : IsProbabilityMeasure (law n a) := by
  unfold law
  infer_instance

theorem terminal_law (n : ℕ) (a : ℝ) :
    (law n a).map (fun ω => ω.val 1) = ComplexFourthRootWalk.law n a := by
  have hm : Measurable (fun ω : Path => ω.val 1) :=
    ((continuous_eval_const 1).comp continuous_subtype_val).measurable
  rw [law, Measure.map_map hm (path_measurable n a)]
  unfold ComplexFourthRootWalk.law
  congr 1
  funext ω
  exact path_terminal n a ω

end OperatorDerivativeRewrite.Foundation.ComplexRootContinuousPaths
