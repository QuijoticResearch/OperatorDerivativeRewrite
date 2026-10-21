import Foundation.RiemannQuadraticArithmeticHeat

/-! Closedness of actual all-real times from inherited polynomial modulus bounds. -/
noncomputable section
open Complex Polynomial Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenRealityClosed
open RiemannEvenFlow

theorem upper_vertical_bound (m : ℕ) (t : ℝ)
    (hreal : ∀ z : ℂ, flow m t z = 0 → z.im = 0)
    (x a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖flow m t ((x:ℂ)+I*a)‖ ≤ ‖flow m t ((x:ℂ)+I*b)‖ := by
  have h0 : flow m t 0 ≠ 0 :=
    ne_of_apply_ne Complex.re (ne_of_gt (RiemannEvenNormalizedCompact.actual_flow_zero_pos m t))
  obtain ⟨r,P,hr,hrb,hzeros,hP0,heven,hlim⟩ :=
    EvenEntirePolynomialApproximation.exists_real_polynomial_approximation
      (flow m t) ((flow_differentiable m t).differentiableOn.analyticOnNhd isOpen_univ)
      h0 (RiemannEvenEvolution.flow_even m t)
      (RiemannEvenEntireGrowth.exists_subquadratic_growth m t) (RiemannEvenWindowZeros.flow_conj m t)
  exact PolynomialStripLimit.limit_upper_bound
    (fun n => (P n).map (algebraMap ℝ ℂ)) (flow m t) 0 x a b
    (fun n z hz => le_of_eq (hreal z ((hzeros n z).mp hz).2))
    (fun z => (tendstoLocallyUniformlyOn_univ.mpr hlim).tendsto_at (mem_univ z)) ha hab

theorem reality_of_time_sequence (m : ℕ) (s : ℕ → ℝ) (t : ℝ)
    (hs : Tendsto s atTop (𝓝 t))
    (hreal : ∀ n, ∀ z : ℂ, flow m (s n) z = 0 → z.im = 0)
    (z : ℂ) (hz : flow m t z = 0) : z.im = 0 := by
  have hpoint (w : ℂ) : Tendsto (fun n => flow m (s n) w) atTop (𝓝 (flow m t w)) :=
    (RiemannEvenEvolution.even_order_heat_equation m t w).continuousAt.tendsto.comp hs
  have hvert (x a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      ‖flow m t ((x:ℂ)+I*a)‖ ≤ ‖flow m t ((x:ℂ)+I*b)‖ := by
    apply le_of_tendsto_of_tendsto ((hpoint _).norm) ((hpoint _).norm)
    exact Eventually.of_forall fun n => upper_vertical_bound m (s n) (hreal n) x a b ha hab
  have h0 : flow m t 0 ≠ 0 :=
    ne_of_apply_ne Complex.re (ne_of_gt (RiemannEvenNormalizedCompact.actual_flow_zero_pos m t))
  have hupper := PolynomialStripLimit.zero_im_le_of_vertical_bound
    (flow m t) 0 (flow_differentiable m t) ⟨0,h0⟩ hvert
  have hu := hupper z hz
  have hl := hupper (-z) (by rw [RiemannEvenEvolution.flow_even m t]; exact hz)
  simp only [Complex.neg_im] at hl
  linarith

def realTimes (m : ℕ) : Set ℝ := {t | ∀ z : ℂ, flow m t z = 0 → z.im = 0}

theorem isClosed_realTimes (m : ℕ) : IsClosed (realTimes m) := by
  apply SequentialSpace.isClosed_of_seq
  intro s t hs hst
  exact reality_of_time_sequence m s t hst hs

theorem quadratic_upper (t u : ℝ) (htu : t ≤ u) (ht : t ∈ realTimes 1) :
    u ∈ realTimes 1 := RiemannQuadraticStripEvolution.once_real_always_real t u htu ht

theorem quadratic_nonempty : (realTimes 1).Nonempty :=
  ⟨1/2, RiemannQuadraticGlobalStrip.classical_half_all_real⟩

theorem quadratic_infimum_mem (hb : BddBelow (realTimes 1)) :
    sInf (realTimes 1) ∈ realTimes 1 :=
  (isClosed_realTimes 1).csInf_mem quadratic_nonempty hb

theorem quadratic_eq_Ici (hb : BddBelow (realTimes 1)) :
    realTimes 1 = Ici (sInf (realTimes 1)) := by
  ext t
  constructor
  · exact fun ht => csInf_le hb ht
  · exact fun ht => quadratic_upper _ _ ht (quadratic_infimum_mem hb)

theorem quadratic_nonreal_before (hb : BddBelow (realTimes 1))
    (t : ℝ) (ht : t < sInf (realTimes 1)) :
    ∃ z : ℂ, flow 1 t z = 0 ∧ z.im ≠ 0 := by
  have hn : t ∉ realTimes 1 := by
    intro hm
    exact (not_le_of_gt ht) (csInf_le hb hm)
  simpa only [realTimes, mem_ofPred_eq, not_forall, not_imp, exists_prop] using hn

theorem quadratic_dichotomy : realTimes 1 = univ ∨
    ∃ A : ℝ, A ≤ 1/2 ∧ realTimes 1 = Ici A := by
  by_cases hb : BddBelow (realTimes 1)
  · exact Or.inr ⟨sInf (realTimes 1),
      csInf_le hb RiemannQuadraticGlobalStrip.classical_half_all_real, quadratic_eq_Ici hb⟩
  · left
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨u,hu,hut⟩ := not_bddBelow_iff.mp hb t
    exact quadratic_upper u t hut.le hu

theorem quadratic_bddBelow_iff_nonreal_exists : BddBelow (realTimes 1) ↔
    ∃ (t : ℝ) (z : ℂ), flow 1 t z = 0 ∧ z.im ≠ 0 := by
  constructor
  · intro hb
    obtain ⟨z,hz,hi⟩ := quadratic_nonreal_before hb (sInf (realTimes 1)-1) (by linarith)
    exact ⟨_,z,hz,hi⟩
  · rintro ⟨t,z,hz,hi⟩
    refine ⟨t,?_⟩
    intro u hu
    by_contra hn
    exact hi (quadratic_upper u t (le_of_not_ge hn) hu z hz)

end OperatorDerivativeRewrite.Foundation.RiemannEvenRealityClosed
