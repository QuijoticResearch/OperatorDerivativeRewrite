import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A contraction tangent has the genuine Banach dissipativity estimate. -/
noncomputable section
open Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ContractionTangentDissipativity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_resolvent_bound (F : ℝ → E) (x v : E)
    (hF : ∀ t, 0 < t → ‖F t‖ ≤ ‖x‖)
    (hlim : Tendsto (fun t : ℝ => t⁻¹ • (F t-x)) (𝓝[Set.Ioi 0] 0) (𝓝 v))
    (q : ℝ) (hq : 0 < q) : q*‖x‖ ≤ ‖q • x-v‖ := by
  obtain ⟨φ,hφn,hφx⟩ := exists_dual_vector'' ℝ x
  change φ x = ‖x‖ at hφx
  have hφ (y : E) : φ y ≤ ‖y‖ := by
    calc
      φ y ≤ |φ y| := le_abs_self _
      _ = ‖φ y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖φ‖*‖y‖ := φ.le_opNorm y
      _ ≤ 1*‖y‖ := mul_le_mul_of_nonneg_right hφn (norm_nonneg _)
      _ = ‖y‖ := one_mul _
  have ht := φ.continuous.tendsto v |>.comp hlim
  have hv : φ v ≤ 0 := by
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hf : φ (F t)-φ x ≤ 0 := sub_nonpos.mpr (by
      rw [hφx]
      exact (hφ _).trans (hF t ht))
    change φ (t⁻¹ • (F t-x)) ≤ 0
    rw [map_smul, map_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) hf
  calc
    q*‖x‖ ≤ q*φ x-φ v := by rw [hφx]; linarith
    _ = φ (q • x-v) := by rw [map_sub, map_smul]; rfl
    _ ≤ ‖q • x-v‖ := hφ _

end OperatorDerivativeRewrite.Foundation.ContractionTangentDissipativity
