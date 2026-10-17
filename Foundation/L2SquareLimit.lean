import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Passing a uniform L2 bound on squares through an actual L2 limit. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.L2SquareLimit
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem exists_square_of_bounded_approximation
    (f q : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ) (C : ℝ) (hC : 0 ≤ C)
    (ht : Tendsto f atTop (𝓝 g))
    (hq : ∀ n, q n =ᵐ[μ] fun x => (f n x)^2)
    (hb : ∀ n, ‖q n‖ ≤ C) :
    ∃ z : Lp ℝ 2 μ, z =ᵐ[μ] (fun x => (g x)^2) ∧ ‖z‖ ≤ C := by
  obtain ⟨ns, _, hae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have ht2 : ∀ᵐ x ∂μ, Tendsto (fun n => (f (ns n) x)^2) atTop (𝓝 ((g x)^2)) := by
    filter_upwards [hae] with x hx
    exact hx.pow 2
  have hbound (n : ℕ) : eLpNorm (fun x => (f (ns n) x)^2) 2 μ ≤ ENNReal.ofReal C := by
    rw [← eLpNorm_congr_ae (hq (ns n)), ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb (ns n))
  have hm : AEStronglyMeasurable (fun x => (g x)^2) μ := (Lp.aestronglyMeasurable g).pow 2
  have hl := Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound)
    (fun n => (Lp.aestronglyMeasurable (f (ns n))).pow 2) hm ht2
  have hmem : MemLp (fun x => (g x)^2) 2 μ :=
    hl.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hmem.toLp _, MemLp.coeFn_toLp _, ?_⟩
  have he : ENNReal.ofReal ‖hmem.toLp (fun x => (g x)^2)‖ ≤ ENNReal.ofReal C := by
    rw [ofReal_norm, Lp.enorm_toLp]
    exact hl
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp he

theorem memLp_four_of_square (g z : Lp ℝ 2 μ) (hz : z =ᵐ[μ] fun x => (g x)^2) : MemLp g 4 μ := by
  have hm : MemLp (fun x => (g x)^2) 2 μ := (memLp_congr_ae hz).mp (Lp.memLp z)
  have h42 : (4 : ℝ≥0∞)/2 = 2 := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_div_cancel_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by simp : (2 : ℝ≥0∞) ≠ ∞)]
  have hr : MemLp (fun x => ‖g x‖^(2 : ℝ)) ((4 : ℝ≥0∞)/2) μ := by
    rw [h42]
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hm
  exact (memLp_norm_rpow_iff (p := 4) (q := 2) (Lp.aestronglyMeasurable g)
    (by norm_num) (by norm_num)).mp hr

end OperatorDerivativeRewrite.Foundation.L2SquareLimit
