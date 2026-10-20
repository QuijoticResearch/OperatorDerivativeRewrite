import Foundation.RiemannEvenFarModelSaddle
import Foundation.RiemannEvenSaddleGrowth
import Foundation.RiemannQuarticTransitionSaddle

/-! Uniform-in-time comparison of actual integer-even stationary scales
with the degree-correct far-saddle hypotheses. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenUniformFarScale
open RiemannEvenRealSaddle RiemannQuarticTransitionSaddle

theorem polynomial_gap_eventually (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ d : ℝ in atTop, C*(1+d)^k ≤ Real.exp (4*d) := by
  have h := ((isLittleO_pow_exp_pos_mul_atTop k (b := 4) (by norm_num)).const_mul_left (C*2^k)).bound zero_lt_one
  filter_upwards [h,eventually_ge_atTop (1 : ℝ)] with d hb hd
  simp only [Real.norm_eq_abs,one_mul,abs_of_pos (Real.exp_pos _)] at hb
  have hp : (1+d)^k ≤ 2^k*d^k := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by linarith : 0 ≤ 1+d) (by linarith : 1+d ≤ 2*d) k
  have hm := mul_le_mul_of_nonneg_left hp hC
  have hc : (C*2^k)*d^k ≤ Real.exp (4*d) := (le_abs_self _).trans hb
  exact hm.trans (by simpa only [mul_assoc] using hc)

theorem exists_uniform_stationary_far_scale (m : ℕ) (hm : 0 < m) :
    ∃ D : ℝ, 16 ≤ D ∧ ∀ t u a : ℝ, 1 ≤ t → ((2*m : ℕ) : ℝ)+4 ≤ u →
      phaseSlope m t u = 0 → u+D ≤ a →
      10000*((((2*m : ℕ) : ℝ)+1)^2)*(t+1)*(a+4)^(2*m-1) ≤ realScale a := by
  let n : ℕ := 2*m
  let A : ℝ := 10000*(((n : ℝ)+1)^2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨D,hD⟩ := eventually_atTop.1 (polynomial_gap_eventually (n-1) (2*A) (by positivity))
  refine ⟨max D 16,le_max_right _ _,?_⟩
  intro t u a ht hu hs ha
  let d : ℝ := a-u
  have hd : 16 ≤ d := by dsimp [d]; linarith [le_max_right D 16]
  have hdD : D ≤ d := by dsimp [d]; linarith [le_max_left D 16]
  have hn : (2 : ℝ) ≤ (n : ℝ) := by dsimp [n]; exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu4 : 4 ≤ u := by change (n : ℝ)+4 ≤ u at hu; linarith
  have hu0 : 0 ≤ u := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hlinear : a+4 ≤ u*(1+d) := by
    have hh := mul_le_mul_of_nonneg_right hu4 (show 0 ≤ d by linarith)
    dsimp [d] at *
    nlinarith
  have hpoly : (a+4)^(n-1) ≤ u^(n-1)*(1+d)^(n-1) := by
    have hh := pow_le_pow_left₀ (by dsimp [d] at hd; linarith : 0 ≤ a+4) hlinear (n-1)
    simpa only [mul_pow] using hh
  have hbase : t*u^(n-1) ≤ realScale u := by
    have hb := (stationary_scale_bounds m t u (by linarith) hs).2
    have hnonneg : 0 ≤ t*u^(n-1) := by positivity
    have hh := mul_le_mul_of_nonneg_right hn hnonneg
    change ((n : ℝ)*t*u^(n-1)) ≤ 4*Real.pi*Real.exp (4*u)-8 at hb
    dsimp [realScale]
    nlinarith
  have htime : A*(t+1) ≤ 2*A*t := by nlinarith
  have hgap := hD d hdD
  change A*(t+1)*(a+4)^(n-1) ≤ _
  calc
    _ ≤ (2*A*t)*(u^(n-1)*(1+d)^(n-1)) :=
      mul_le_mul htime hpoly (pow_nonneg (by dsimp [d] at hd; linarith : 0 ≤ a+4) _) (by positivity)
    _ ≤ realScale u*(2*A*(1+d)^(n-1)) := by
      have hh := mul_le_mul_of_nonneg_right hbase (show 0 ≤ 2*A*(1+d)^(n-1) by positivity)
      nlinarith
    _ ≤ realScale u*Real.exp (4*d) := mul_le_mul_of_nonneg_left hgap (realScale_pos u).le
    _ = realScale a := by
      unfold realScale
      rw [mul_assoc,← Real.exp_add]
      congr 2
      dsimp [d]
      ring

theorem far_parameter (u D x : ℝ) (hx : Real.exp (4*D)*realScale u ≤ x) :
    ∃ a : ℝ, u+D ≤ a ∧ x = realScale a := by
  have hx0 : 0 < x := lt_of_lt_of_le (mul_pos (Real.exp_pos _) (realScale_pos u)) hx
  let a : ℝ := Real.log (x/(4*Real.pi))/4
  have hid : x = realScale a := by
    dsimp [realScale,a]
    rw [show 4*(Real.log (x/(4*Real.pi))/4) = Real.log (x/(4*Real.pi)) by ring,
      Real.exp_log (by positivity : 0 < x/(4*Real.pi))]
    field_simp
  have he : Real.exp (4*(u+D))*(4*Real.pi) = Real.exp (4*D)*realScale u := by
    unfold realScale
    rw [show 4*(u+D) = 4*u+4*D by ring,Real.exp_add]
    ring
  have hstart : Real.exp (4*(u+D)) ≤ x/(4*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    rw [he]
    exact hx
  have hlog := Real.log_le_log (Real.exp_pos _) hstart
  rw [Real.log_exp] at hlog
  exact ⟨a,by dsimp [a]; linarith,hid⟩

end OperatorDerivativeRewrite.Foundation.RiemannEvenUniformFarScale
