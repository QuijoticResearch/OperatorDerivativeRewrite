import Foundation.HigherHeatFourierPathGenerator
import Foundation.ContractionTangentDissipativity

/-! Actual dissipativity and a closed densely defined path-space heat operator. -/
noncomputable section
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathClosure
open HigherHeatDyadicLaws HigherHeatFourierBanach HigherHeatFourierPathSemigroup
open HigherHeatFourierPathGenerator

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem graph_bound (m : ℕ) (hm : 0 < m) (q : ℝ) (hq : 0 < q)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ m) :
    q*‖z.1‖ ≤ ‖q • z.1-z.2‖ :=
  ContractionTangentDissipativity.norm_resolvent_bound
    (fun t => evolution levels ξ m hm t.toNNReal z.1) z.1 z.2
    (fun t _ => evolution_bound levels ξ m hm t.toNNReal z.1)
    (graph_limit levels ξ m hm z hz) q hq

theorem closure_bound (m : ℕ) (hm : 0 < m) (q : ℝ) (hq : 0 < q)
    (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ (graph levels ξ m).topologicalClosure) : q*‖z.1‖ ≤ ‖q • z.1-z.2‖ := by
  exact (closure_minimal (s := (graph levels ξ m : Set (TestSpace levels ξ × TestSpace levels ξ)))
    (fun w hw => graph_bound levels ξ m hm q hq w hw)
    (isClosed_le (continuous_const.mul continuous_fst.norm)
      ((continuous_fst.const_smul q).sub continuous_snd).norm)) hz

theorem closure_vertical_zero (m : ℕ) (hm : 0 < m) (y : TestSpace levels ξ)
    (hy : (0,y) ∈ (graph levels ξ m).topologicalClosure) : y=0 := by
  have hb (f : TestSpace levels ξ) (hf : ∃ g, (f,g) ∈ graph levels ξ m) : ‖f‖ ≤ ‖f-y‖ := by
    obtain ⟨g,hg⟩ := hf
    have hg' := (graph levels ξ m).le_topologicalClosure hg
    have hq (q : ℝ) (hq : 0 < q) : q*(‖f‖-‖f-y‖) ≤ ‖g‖ := by
      have hz := (graph levels ξ m).topologicalClosure.add_mem hg'
        ((graph levels ξ m).topologicalClosure.smul_mem (q:ℂ) hy)
      have hh := closure_bound levels ξ m hm q hq _ hz
      change q*‖f+(q:ℂ) • (0 : TestSpace levels ξ)‖ ≤
        ‖q • (f+(q:ℂ) • 0)-(g+(q:ℂ) • y)‖ at hh
      simp only [smul_zero,add_zero] at hh
      have hc : (q:ℂ) • y=q • y := by
        change (algebraMap ℝ ℂ q) • y=q • y
        exact IsScalarTower.algebraMap_smul ℂ q y
      rw [hc] at hh
      have he : q • f-(g+q • y)=q • (f-y)-g := by rw [smul_sub]; abel
      rw [he] at hh
      have ht := norm_sub_le (q • (f-y)) g
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hq] at ht
      nlinarith
    by_contra hn
    have hd : 0 < ‖f‖-‖f-y‖ := sub_pos.mpr (lt_of_not_ge hn)
    have hh := hq ((‖g‖+1)/(‖f‖-‖f-y‖)) (div_pos (by positivity) hd)
    rw [div_mul_cancel₀ _ hd.ne'] at hh
    linarith
  have hd : Dense {f : TestSpace levels ξ | ∃ g, (f,g) ∈ graph levels ξ m} := by
    have hd := domain_dense levels ξ m hm
    have he : ((operator levels ξ m).domain : Set _)={f | ∃ g, (f,g) ∈ graph levels ξ m} := by
      ext f
      change f ∈ (operator levels ξ m).domain ↔ ∃ g, (f,g) ∈ graph levels ξ m
      rw [LinearPMap.mem_domain_iff, operator_graph levels ξ m hm]
    rwa [he] at hd
  have hy' : ‖y‖ ≤ ‖y-y‖ :=
    (closure_minimal hb (isClosed_le continuous_norm (continuous_id.sub continuous_const).norm)) (hd y)
  simpa only [sub_self,norm_zero,norm_le_zero_iff] using hy'

theorem closable (m : ℕ) (hm : 0 < m) : (operator levels ξ m).IsClosable := by
  refine ⟨(graph levels ξ m).topologicalClosure.toLinearPMap, ?_⟩
  rw [operator_graph levels ξ m hm]
  symm
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨f,g⟩ hg h0
  change f=0 at h0
  subst f
  exact closure_vertical_zero levels ξ m hm g hg

theorem closed_closure (m : ℕ) (hm : 0 < m) : (operator levels ξ m).closure.IsClosed :=
  (closable levels ξ m hm).closure_isClosed

theorem closure_domain_dense (m : ℕ) (hm : 0 < m) :
    Dense ((operator levels ξ m).closure.domain : Set (TestSpace levels ξ)) :=
  (domain_dense levels ξ m hm).mono (operator levels ξ m).le_closure.1

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathClosure
