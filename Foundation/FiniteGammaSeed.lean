import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-! A bounded three-state Gamma seed with all matrix positivity axioms. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteGammaSeed
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

inductive State | o | x | y deriving DecidableEq, Fintype, Inhabited
instance : MeasurableSpace State := ⊤
instance : DiscreteMeasurableSpace State := ⟨fun _ => trivial⟩
abbrev Algebra := State → ℝ
abbrev Form := EuclideanSpace ℝ (State × Fin 2)

theorem state_card : Fintype.card State = 3 := by decide

def μ : Measure State := (1/3 : ℝ≥0∞) • Measure.count

instance μ_probability : IsProbabilityMeasure μ where
  measure_univ := by
    norm_num [μ, Measure.smul_apply, Measure.count_apply_finite, state_card]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance μ_complete : μ.IsComplete := ⟨fun _ _ => trivial⟩

def expect (f : Algebra) : ℝ := (1/3 : ℝ) * ∑ s : State, f s

theorem integral_expect (f : Algebra) : (∫ s, f s ∂μ) = expect f := by
  rw [μ, integral_smul_measure, integral_count]
  norm_num [expect]

theorem all_memLp (f : Algebra) (p : ℝ≥0∞) : MemLp f p μ := MemLp.of_discrete

theorem expect_const (c : ℝ) : expect (fun _ => c) = c := by
  simp [expect, state_card]

theorem expect_nonneg (f : Algebra) (hf : ∀ s, 0 ≤ f s) : 0 ≤ expect f := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun s _ => hf s))

theorem expect_sum {ι : Type*} [Fintype ι] (f : ι → Algebra) :
    expect (fun s => ∑ i, f i s) = ∑ i, expect (f i) := by
  unfold expect
  rw [Finset.sum_comm, Finset.mul_sum]

def beta : Algebra →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun f i := if i = 0 then f State.x-f State.o else f State.y-f State.o
  map_add' f g := by funext i; by_cases h : i = 0 <;> simp [h] <;> ring
  map_smul' r f := by funext i; by_cases h : i = 0 <;> simp [h, smul_eq_mul] <;> ring

def gamma (f g : Algebra) : Algebra := fun _ => dotProduct (beta f) (beta g)

theorem beta_const (c : ℝ) : beta (fun _ => c) = 0 := by
  funext i
  simp [beta]

theorem gamma_symmetric (f g : Algebra) : gamma f g = gamma g f := by
  funext s
  exact dotProduct_comm _ _

theorem gamma_const (c : ℝ) (g : Algebra) : gamma (fun _ => c) g = 0 := by
  funext s
  change dotProduct (beta (fun _ => c)) (beta g) = 0
  rw [beta_const, zero_dotProduct]

theorem gamma_add_left (f g h : Algebra) : gamma (f+g) h = gamma f h + gamma g h := by
  funext s
  simp [gamma, map_add, add_dotProduct]

theorem gamma_smul_left (c : ℝ) (f g : Algebra) : gamma (c • f) g = c • gamma f g := by
  funext s
  simp [gamma, map_smul, smul_dotProduct]

theorem matrix_square_identity {ι : Type*} [Fintype ι] (f u : ι → Algebra) (s : State) :
    (∑ i, ∑ j, u i s * u j s * gamma (f i) (f j) s) =
      dotProduct (∑ i, u i s • beta (f i)) (∑ i, u i s • beta (f i)) := by
  rw [sum_dotProduct]
  simp_rw [dotProduct_sum, smul_dotProduct, dotProduct_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [gamma, smul_eq_mul]
  ring

theorem matrix_pointwise_nonneg {ι : Type*} [Fintype ι] (f u : ι → Algebra) (s : State) :
    0 ≤ ∑ i, ∑ j, u i s * u j s * gamma (f i) (f j) s := by
  rw [matrix_square_identity]
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

theorem weighted_matrix_positive {ι : Type*} [Fintype ι] (f u : ι → Algebra)
    (q : Algebra) (hq : ∀ s, 0 ≤ q s) :
    0 ≤ ∑ i, ∑ j, expect (fun s => q s * u i s * u j s * gamma (f i) (f j) s) := by
  have he : (fun s => q s * ∑ i, ∑ j, u i s * u j s * gamma (f i) (f j) s) =
      fun s => ∑ i, ∑ j, q s * u i s * u j s * gamma (f i) (f j) s := by
    funext s
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := expect_nonneg (fun s => q s * ∑ i, ∑ j, u i s * u j s * gamma (f i) (f j) s)
    (fun s => mul_nonneg (hq s) (matrix_pointwise_nonneg f u s))
  rw [he, expect_sum] at h
  simpa only [expect_sum] using h

theorem matrix_positive {ι : Type*} [Fintype ι] (f u : ι → Algebra) :
    0 ≤ ∑ i, ∑ j, expect (fun s => u i s * u j s * gamma (f i) (f j) s) := by
  simpa using weighted_matrix_positive f u (fun _ => 1) (fun _ => by norm_num)

theorem energy_formula (f : Algebra) : expect (gamma f f) = dotProduct (beta f) (beta f) :=
  expect_const _

theorem energy_tendsto_zero (f : ℕ → Algebra) (hf : Filter.Tendsto f Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => expect (gamma (f n) (f n))) Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (fun n => beta (f n)) Filter.atTop (nhds 0) := by
    have hc : Continuous (beta : Algebra → Fin 2 → ℝ) := beta.continuous_of_finiteDimensional
    simpa only [map_zero, Function.comp_def] using hc.tendsto 0 |>.comp hf
  have hc : Continuous (fun v : Fin 2 → ℝ => dotProduct v v) :=
    continuous_id.dotProduct continuous_id
  have he := hc.tendsto 0 |>.comp hb
  simpa only [Function.comp_def, energy_formula, zero_dotProduct] using he

end OperatorDerivativeRewrite.Foundation.FiniteGammaSeed
