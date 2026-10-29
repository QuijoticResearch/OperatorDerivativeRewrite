import Foundation.FourCubeHessianMeanValue

/-! Full-Haar thermal mixed-Hessian obstructions, including reference subtraction. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeThermalHessianBudget
open FourCubeHessianMeanValue FourCubeThermalMixedDifference

theorem actual_large_deviation (B : ℝ → ℝ → ℝ → ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∃ x y : ℝ,|x|<t ∧ |y|<t ∧
      (c/(2*t)< |mixedHessian (1/t^2) x y t-B (1/t^2) x y| ∨
       c/(2*t)< |mixedHessian (1/t^2) x y (-t)-B (1/t^2) x y|) := by
  filter_upwards [actual_thermal_hessian_difference] with t ht
  obtain ⟨x,y,hx,hy,hd⟩ := ht
  refine ⟨x,y,hx,hy,?_⟩
  by_cases hp : c/(2*t)< |mixedHessian (1/t^2) x y t-B (1/t^2) x y|
  · exact Or.inl hp
  · right
    by_contra hn
    have ha := le_abs_self (mixedHessian (1/t^2) x y t-B (1/t^2) x y)
    have hb := neg_le_abs (mixedHessian (1/t^2) x y (-t)-B (1/t^2) x y)
    have he : c/(2*t)+c/(2*t)=c/t := by ring
    have hp' := le_of_not_gt hp
    have hn' := le_of_not_gt hn
    linarith

theorem actual_deviation_eventually_gt (B : ℝ → ℝ → ℝ → ℝ) (K : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∃ x y : ℝ,|x|<t ∧ |y|<t ∧
      (K< |mixedHessian (1/t^2) x y t-B (1/t^2) x y| ∨
       K< |mixedHessian (1/t^2) x y (-t)-B (1/t^2) x y|) := by
  have hi : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun t : ℝ => (2*t)*K) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hi.const_mul 2).mul_const K
  have hb := hz.eventually (eventually_lt_nhds c_positive)
  filter_upwards [actual_large_deviation B,hb,self_mem_nhdsWithin] with t ht hb htpos
  have hk : K<c/(2*t) := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) htpos)).mpr (by nlinarith)
  obtain ⟨x,y,hx,hy,he⟩ := ht
  exact ⟨x,y,hx,hy,he.imp (lt_trans hk) (lt_trans hk)⟩

private theorem budget_bound (C C0 t x y : ℝ) (hC : 0≤C) (ht : 0<t) (hx : |x|<t) (hy : |y|<t) :
    C*(1/t^2)*(x^2+y^2+t^2)+C0≤3*C+C0 := by
  have hxx : x^2≤t^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) ht.le).mpr hx.le
  have hyy : y^2≤t^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) ht.le).mpr hy.le
  have hs : (1/t^2)*(x^2+y^2+t^2)≤3 := by
    calc
      _ ≤ (1/t^2)*(3*t^2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 3 := by field_simp [ht.ne'] <;> ring
  calc
    _ = C*((1/t^2)*(x^2+y^2+t^2))+C0 := by ring
    _ ≤ C*3+C0 := by
      have hh := mul_le_mul_of_nonneg_left hs hC
      linarith
    _ = _ := by ring

theorem actual_quadratic_budget_violations (B : ℝ → ℝ → ℝ → ℝ) (C C0 : ℝ) (hC : 0≤C) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∃ x y : ℝ,|x|<t ∧ |y|<t ∧
      (C*(1/t^2)*(x^2+y^2+t^2)+C0< |mixedHessian (1/t^2) x y t-B (1/t^2) x y| ∨
       C*(1/t^2)*(x^2+y^2+t^2)+C0< |mixedHessian (1/t^2) x y (-t)-B (1/t^2) x y|) := by
  filter_upwards [actual_deviation_eventually_gt B (3*C+C0),self_mem_nhdsWithin] with t ht htpos
  obtain ⟨x,y,hx,hy,he⟩ := ht
  have hb := budget_bound C C0 t x y hC htpos hx hy
  exact ⟨x,y,hx,hy,he.imp (lt_of_le_of_lt hb) (lt_of_le_of_lt hb)⟩

theorem no_eventual_quadratic_budget (B : ℝ → ℝ → ℝ → ℝ) (C C0 : ℝ) (hC : 0≤C) :
    ¬ (∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x y : ℝ, |x|<t → |y|<t →
      |mixedHessian (1/t^2) x y t-B (1/t^2) x y|≤C*(1/t^2)*(x^2+y^2+t^2)+C0 ∧
      |mixedHessian (1/t^2) x y (-t)-B (1/t^2) x y|≤C*(1/t^2)*(x^2+y^2+t^2)+C0) := by
  intro hb
  obtain ⟨t,ht,hb⟩ := ((actual_quadratic_budget_violations B C C0 hC).and hb).exists
  obtain ⟨x,y,hx,hy,he⟩ := ht
  have hh := hb x y hx hy
  exact he.elim (not_lt_of_ge hh.1) (not_lt_of_ge hh.2)

end OperatorDerivativeRewrite.Foundation.FourCubeThermalHessianBudget
