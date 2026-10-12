import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Minimization from a quantitative quartic midpoint inequality

A continuous bounded-below real functional on a complete real normed space
attains its infimum if its midpoint deficit controls the fourth power of
the distance. The proof constructs an infimizing sequence and proves it
Cauchy. It uses neither finite-dimensional compactness nor reflexivity.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.QuarticUniformMinimization

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- A positive quartic midpoint deficit makes every infimizing sequence Cauchy,
so continuity and completeness produce a genuine global minimizer. -/
theorem exists_minimizer_of_quartic_midpoint
    (E : H → ℝ) (hE : Continuous E) (hbelow : BddBelow (Set.range E))
    (k : ℝ) (hk : 0 < k)
    (hmid : ∀ u v : H,
      E ((1 / 2 : ℝ) • (u + v)) + k * ‖u - v‖ ^ 4 ≤ (E u + E v) / 2) :
    ∃ u : H, ∀ v : H, E u ≤ E v := by
  obtain ⟨r, _, hrt, hrmem⟩ :=
    exists_seq_tendsto_sInf (show (Set.range E).Nonempty from ⟨E 0, ⟨0, rfl⟩⟩) hbelow
  choose u hu using hrmem
  have ht : Tendsto (fun n => E (u n)) atTop (𝓝 (sInf (Set.range E))) := by
    simpa only [hu] using hrt
  have hCauchy : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hgap : 0 < k * ε ^ 4 := mul_pos hk (pow_pos hε 4)
    have hev := ht.eventually (gt_mem_nhds (show
      sInf (Set.range E) < sInf (Set.range E) + k * ε ^ 4 by linarith))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hlow : sInf (Set.range E) ≤ E ((1 / 2 : ℝ) • (u m + u n)) :=
      csInf_le hbelow ⟨_, rfl⟩
    have hm' := hN m hm
    have hn' := hN n hn
    have hmid' := hmid (u m) (u n)
    have hnorm : ‖u m - u n‖ < ε := by
      by_contra hnot
      have hpow := pow_le_pow_left₀ hε.le (le_of_not_gt hnot) 4
      have hmul := mul_le_mul_of_nonneg_left hpow hk.le
      nlinarith
    simpa only [dist_eq_norm] using hnorm
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hval : E v = sInf (Set.range E) :=
    tendsto_nhds_unique (hE.continuousAt.tendsto.comp hv) ht
  refine ⟨v, fun w => ?_⟩
  rw [hval]
  exact csInf_le hbelow ⟨w, rfl⟩

end OperatorDerivativeRewrite.Foundation.QuarticUniformMinimization
