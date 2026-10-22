import Foundation.IBMPredictableCompactApproximation

/-! Continuity at the empty set and genuine countable additivity of IBM ring energy. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableContentContinuity
open IBMPredictableRectangles IBMPredictableRingContent IBMCompactPredictableFibers
open IBMPredictableCompactApproximation IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false

def budget (ε : ℝ) (i : ℕ) : ℝ := (ε/2) * (1/2 : ℝ) ^ (i+1)

theorem budget_pos {ε : ℝ} (hε : 0 < ε) (i : ℕ) : 0 < budget ε i :=
  mul_pos (half_pos hε) (pow_pos (by norm_num) _)

theorem budget_sum (ε : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, budget ε i) = (ε/2) * (1-(1/2 : ℝ)^n) := by
  induction n with
  | zero => simp only [Finset.sum_range_zero, pow_zero, sub_self, mul_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [budget, pow_succ]
    ring

theorem budget_sum_le {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    (∑ i ∈ Finset.range n, budget ε i) ≤ ε/2 := by
  rw [budget_sum]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n]

theorem energy_continuity (F : JointL2) (E : ℕ → Set Space)
    (hE : ∀ n, E n ∈ elementaryRing) (hm : Antitone E) (he : (⋂ n, E n) = ∅) :
    Tendsto (fun n => ‖ringIntegral F (E n)‖ ^ 2) atTop (𝓝 0) := by
  classical
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (sq_nonneg _)
  · intro ε hε
    have ha n := ring_approximable F (hE n) (budget ε n) (budget_pos hε n)
    choose K D hK hKE hD hloss hbudget using ha
    have hKe : (⋂ n, K n) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hpE : p ∈ ⋂ n, E n := mem_iInter.mpr fun n => hKE n (mem_iInter.mp hp n)
      simp only [he, mem_empty_iff_false] at hpE
    let U (n : ℕ) : Set Space := ⋃ i ∈ Finset.range (n+1), D i
    have hU n : U n ∈ elementaryRing :=
      elementary_isSetRing.biUnion_mem (Finset.range (n+1)) (fun i _ => hD i)
    let R (n : ℕ) := E n \ U n
    have hR n : R n ∈ elementaryRing := elementary_isSetRing.sdiff_mem (hE n) (hU n)
    let A (n : ℕ) := projection (closedPrefix K n)
    have hA n : MeasurableSet (A n) := projection_measurable (closedPrefix_mem K hK n)
    have hs n : R n ⊆ univ ×ˢ A n := by
      intro p hp
      refine ⟨mem_univ _, ⟨p.1, ?_⟩⟩
      apply (mem_closedPrefix K n p).mpr
      intro i hi
      by_contra hnK
      have hDi := hloss i ⟨hm hi hp.1, hnK⟩
      exact hp.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi), hDi⟩⟩)
    have hvanish : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ∀ᶠ n in atTop, ω ∉ A n :=
      ae_of_all _ fun ω => closedPrefix_projection_exit K hK hKe ω
    have hl := ring_integrals_tendsto_zero F R hR A hA hs hvanish
    have hz : Tendsto (fun n => ‖ringIntegral F (R n)‖ ^ 2) atTop (𝓝 0) := by
      simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using hl.norm.pow 2
    have hUb n : content F (U n) ≤ ENNReal.ofReal (ε/2) := by
      calc
        content F (U n) ≤ ∑ i ∈ Finset.range (n+1), content F (D i) :=
          addContent_biUnion_le elementary_isSetRing (fun i _ => hD i)
        _ ≤ ∑ i ∈ Finset.range (n+1), ENNReal.ofReal (budget ε i) :=
          Finset.sum_le_sum fun i _ => (hbudget i).le
        _ = ENNReal.ofReal (∑ i ∈ Finset.range (n+1), budget ε i) :=
          (ENNReal.ofReal_sum_of_nonneg (fun i _ => (budget_pos hε i).le)).symm
        _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal (budget_sum_le hε.le (n+1))
    have hEb n : content F (E n) ≤ content F (R n) + content F (U n) := by
      have hsub : E n ⊆ R n ∪ U n := by
        intro p hp
        by_cases hu : p ∈ U n
        · exact Or.inr hu
        · exact Or.inl ⟨hp, hu⟩
      exact (addContent_mono elementary_isSetRing.isSetSemiring (hE n)
        (elementary_isSetRing.union_mem (hR n) (hU n)) hsub).trans
          (addContent_union_le elementary_isSetRing (hR n) (hU n))
    filter_upwards [hz.eventually (eventually_lt_nhds (half_pos hε))] with n hn
    have hνR : content F (R n) < ENNReal.ofReal (ε/2) := by
      rw [content_energy F (hR n)]
      exact (ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).mpr hn
    have hνE : content F (E n) < ENNReal.ofReal ε := by
      calc
        content F (E n) ≤ content F (R n) + content F (U n) := hEb n
        _ ≤ content F (R n) + ENNReal.ofReal (ε/2) := add_le_add le_rfl (hUb n)
        _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hνR
        _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
          congr 1
          ring
    rw [content_energy F (hE n)] at hνE
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hνE

theorem content_continuity (F : JointL2) (E : ℕ → Set Space)
    (hE : ∀ n, E n ∈ elementaryRing) (hm : Antitone E) (he : (⋂ n, E n) = ∅) :
    Tendsto (fun n => content F (E n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ENNReal.ofReal (‖ringIntegral F (E n)‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp (energy_continuity F E hE hm he)
  exact hh.congr' (Eventually.of_forall fun n => (content_energy F (hE n)).symm)

theorem content_countable_additivity (F : JointL2) (E : ℕ → Set Space)
    (hE : ∀ n, E n ∈ elementaryRing) (hU : (⋃ n, E n) ∈ elementaryRing)
    (hd : Pairwise (fun i j => Disjoint (E i) (E j))) :
    content F (⋃ n, E n) = ∑' n, content F (E n) :=
  addContent_iUnion_eq_sum_of_tendsto_zero elementary_isSetRing (content F)
    (fun _S hS => (lt_of_le_of_lt (content_bound F hS) ENNReal.ofReal_lt_top).ne)
    (fun {S} hS hm he => content_continuity F S hS hm he) hE hU hd

theorem content_sigma_subadditive (F : JointL2) : (content F).IsSigmaSubadditive :=
  isSigmaSubadditive_of_addContent_iUnion_eq_tsum elementary_isSetRing
    (fun E hE hU hd => content_countable_additivity F E hE hU hd)

end OperatorDerivativeRewrite.Foundation.IBMPredictableContentContinuity
