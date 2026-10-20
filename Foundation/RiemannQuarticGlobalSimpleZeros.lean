import Foundation.RiemannQuarticEntireGrowth

/-! Global simplicity for the actual quartic flow, using the same stationary
center for its bounded transition disk and its complementary far region. -/
noncomputable section
open Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticGlobalSimpleZeros
open RiemannQuarticFlow RiemannQuarticTransitionSaddle
open RiemannQuarticUniformFarScale

theorem deriv_flow_neg (t : ℝ) (z : ℂ) :
    deriv (flow t) (-z) = -deriv (flow t) z := by
  have h := ((flow_differentiable t (-z)).hasDerivAt.comp z (hasDerivAt_neg z)).deriv
  have he : (fun q : ℂ => flow t (-q)) = flow t := by
    funext q
    exact RiemannQuarticEvolution.flow_even t q
  change deriv (fun q : ℂ => flow t (-q)) z = deriv (flow t) (-z) * -1 at h
  rw [he] at h
  linear_combination h

theorem uniform_far_real_zeros_simple :
    ∃ N : ℝ, ∀ (t u x : ℝ), 1 ≤ t → 120021 ≤ u →
      RiemannQuarticSaddleTimes.phaseSlope t u = 0 → N ≤ u →
      Real.exp 64 * realScale u ≤ x → flow t (x : ℂ) = 0 →
      deriv (flow t) (x : ℂ) ≠ 0 := by
  obtain ⟨Y,hY⟩ := eventually_atTop.1
    RiemannQuarticFarSimpleZeros.eventually_uniform_real_simple_zeros
  refine ⟨max Y 10000,?_⟩
  intro t u x ht hu hs hN hx hzero
  have hF : u ≤ Real.exp 64 * realScale u := by
    have he := Real.add_one_le_exp (4*u)
    have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos (4*u)).le
    have hB : u ≤ realScale u := by unfold realScale; nlinarith
    have h64 : 1 ≤ Real.exp (64 : ℝ) := by linarith [Real.add_one_le_exp (64 : ℝ)]
    exact hB.trans (by nlinarith [realScale_pos u])
  have hYx : Y ≤ x := ((le_max_left _ _).trans hN).trans (hF.trans hx)
  have h10000 : 10000 ≤ x := ((le_max_right _ _).trans hN).trans (hF.trans hx)
  have hnorm : ‖(x : ℂ)‖ = x := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < x by linarith)]
  obtain ⟨w,v,hr,hi,hp,hmodel,hv,hroot⟩ :=
    uniform_actual_far_saddles t u ht hu hs (x : ℂ) (by simp) (by simpa only [hnorm] using hx)
  rw [hnorm] at hp
  exact (hY x hYx t ht h10000 w hr hi hp hmodel (x : ℂ) (by simp) hzero).2

theorem eventually_all_zeros_real_simple :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℂ, flow t z = 0 →
      z.im = 0 ∧ deriv (flow t) z ≠ 0 := by
  obtain ⟨N,hfar⟩ := uniform_far_real_zeros_simple
  let M := 2 * Real.exp (64 : ℝ)
  let R := max N 120021
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  filter_upwards [RiemannQuarticTransitionSimpleZeros.bounded_ratio_real_simple_zeros M hM R hR,
    eventually_all_zeros_real,eventually_ge_atTop (1 : ℝ)] with t hb hreal ht
  obtain ⟨u,huR,huM,hs,hzeros⟩ := hb
  have huN : N ≤ u := (le_max_left _ _).trans huR
  have hu : 120021 ≤ u := (le_max_right _ _).trans huR
  intro z hz
  have him := hreal z hz
  refine ⟨him,?_⟩
  by_cases hnorm : ‖z‖ ≤ M * realScale u
  · exact (hzeros z hnorm hz).2
  · have hzcast : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
    have habs : ‖z‖ = |z.re| := by
      calc
        ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hzcast.symm
        _ = |z.re| := by rw [Complex.norm_real,Real.norm_eq_abs]
    have hcut : Real.exp 64 * realScale u ≤ |z.re| := by
      rw [habs] at hnorm
      dsimp [M] at hnorm
      nlinarith [mul_pos (Real.exp_pos (64 : ℝ)) (realScale_pos u)]
    rcases le_total 0 z.re with hpos | hneg
    · rw [abs_of_nonneg hpos] at hcut
      simpa only [hzcast] using hfar t u z.re ht hu hs huN hcut (by simpa only [hzcast] using hz)
    · rw [abs_of_nonpos hneg] at hcut
      have hn : flow t ((-z.re : ℝ) : ℂ) = 0 := by
        simp only [Complex.ofReal_neg,hzcast,RiemannQuarticEvolution.flow_even,hz]
      have hd := hfar t u (-z.re) ht hu hs huN hcut hn
      simpa only [Complex.ofReal_neg,hzcast,deriv_flow_neg,neg_ne_zero] using hd

end OperatorDerivativeRewrite.Foundation.RiemannQuarticGlobalSimpleZeros
