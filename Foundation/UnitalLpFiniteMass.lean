import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! Unital test algebras inside finite-p Lp necessarily have finite ambient mass. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.UnitalLpFiniteMass
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem nonzero_constant_iff {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {c : ℝ} (hc : c ≠ 0) : MemLp (fun _ : α => c) p μ ↔ μ Set.univ < ∞ := by
  rw [memLp_const_iff hp0 hpt]
  simp only [hc, false_or]

theorem infinite_mass_excludes_constant {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hμ : μ Set.univ = ∞) {c : ℝ} (hc : c ≠ 0) :
    ¬ MemLp (fun _ : α => c) p μ := by
  rw [nonzero_constant_iff μ hp0 hpt hc, hμ]
  exact lt_irrefl _

theorem unital_algebra_forces_finite_mass (A : Subalgebra ℝ (α → ℝ))
    (hA : ∀ f ∈ A, MemLp f 2 μ) : μ Set.univ < ∞ := by
  have h : MemLp (fun _ : α => (1 : ℝ)) 2 μ := hA 1 A.one_mem
  exact (nonzero_constant_iff μ (by norm_num) (by norm_num) (by norm_num)).mp h

theorem no_unital_algebra_on_infinite_mass (hμ : μ Set.univ = ∞) :
    ¬ ∃ A : Subalgebra ℝ (α → ℝ), ∀ f ∈ A, MemLp f 2 μ := by
  rintro ⟨A,hA⟩
  have h := unital_algebra_forces_finite_mass μ A hA
  rw [hμ] at h
  exact (lt_irrefl _ h)

theorem real_volume_one_not_L2 :
    ¬ MemLp (fun _ : ℝ => (1 : ℝ)) 2 volume :=
  infinite_mass_excludes_constant volume (by norm_num) (by norm_num)
    Real.volume_univ (by norm_num)

theorem real_volume_one_in_Linfinity :
    MemLp (fun _ : ℝ => (1 : ℝ)) ∞ volume := memLp_top_const _

end OperatorDerivativeRewrite.Foundation.UnitalLpFiniteMass
