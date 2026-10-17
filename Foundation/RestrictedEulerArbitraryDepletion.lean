import Foundation.RestrictedEulerSpectralDistinction

/-! Arbitrarily small normalized stretching coexists with unbounded raw
stretching in exact RE trajectories. No full Navier--Stokes solution is asserted. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RestrictedEulerArbitraryDepletion
open RestrictedEulerRatioCounterexample RestrictedEulerAlignedGrowth
  RestrictedEulerSpectralDistinction
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

def strainFactor (p : ℝ) : ℝ := p^2+1+(p-1)^2

theorem strainFactor_pos (p : ℝ) : 0 < strainFactor p := by
  unfold strainFactor
  nlinarith [sq_nonneg p,sq_nonneg (p-1)]

theorem normalized_scaled (p a c : ℝ) (ha : a ≠ 0) (hc : 0 < c) :
    normalizedStretching (c • matrix p a)=1/Real.sqrt (strainFactor p) := by
  rw [normalizedStretching,stretching_scaled p a c ha,strainSquared_scaled]
  change c/Real.sqrt (c^2*strainFactor p)=1/Real.sqrt (strainFactor p)
  rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq_eq_abs,abs_of_pos hc]
  have hs : Real.sqrt (strainFactor p) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (strainFactor_pos p))
  field_simp [ne_of_gt hc,hs]

theorem parameter_lt_sqrt (p : ℝ) (hp : 0 < p) : p < Real.sqrt (strainFactor p) := by
  have hs := Real.sq_sqrt (le_of_lt (strainFactor_pos p))
  have hn := Real.sqrt_nonneg (strainFactor p)
  unfold strainFactor at hs hn ⊢
  nlinarith [sq_nonneg (p-1)]

theorem exists_profile (ε : ℝ) (hε : 0 < ε) :
    ∃ p a : ℝ, 2 < p ∧ 0 < a ∧ a^2=(p-2)*(p+1) ∧
      (∀ c : ℝ, 0 < c → 0 < normalizedStretching (c • matrix p a) ∧
        normalizedStretching (c • matrix p a) < ε) ∧
      (∀ t : ℝ, t ≠ 1 → ∀ i j : Fin 3,
        HasDerivAt (fun s => family p a s i j) (flow (family p a t) i j) t) ∧
      (∀ M : ℝ, 0 ≤ M → ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ M < stretching (family p a t)) ∧
      (∀ r : ℝ, (r • (1 : Matrix (Fin 3) (Fin 3) ℝ)-matrix p a).det=(r-1)^2*(r+2)) := by
  let p : ℝ := 2+ε⁻¹
  have hp : 2 < p := by dsimp [p]; exact lt_add_of_pos_right 2 (inv_pos.mpr hε)
  have hp₀ : 0 < p := by linarith
  let a : ℝ := Real.sqrt ((p-2)*(p+1))
  have hb : 0 < (p-2)*(p+1) := mul_pos (by linarith) (by linarith)
  have ha : 0 < a := Real.sqrt_pos.mpr hb
  have haq : a^2=(p-2)*(p+1) := Real.sq_sqrt (le_of_lt hb)
  refine ⟨p,a,hp,ha,haq,?_,?_,?_,?_⟩
  · intro c hc
    rw [normalized_scaled p a c (ne_of_gt ha) hc]
    have hs : 0 < Real.sqrt (strainFactor p) := Real.sqrt_pos.mpr (strainFactor_pos p)
    refine ⟨by positivity,(div_lt_iff₀ hs).mpr ?_⟩
    have hlt := mul_lt_mul_of_pos_left (parameter_lt_sqrt p hp₀) hε
    have he : ε*p=2*ε+1 := by dsimp [p]; field_simp <;> ring
    nlinarith
  · intro t ht i j
    exact family_component_ode p a t haq ht i j
  · intro M hM
    exact family_stretching_unbounded p a (ne_of_gt ha) M hM
  · intro r
    exact shifted_determinant p a r haq

theorem no_positive_normalized_threshold :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ p a : ℝ,
      2 < p → 0 < a → a^2=(p-2)*(p+1) → ε ≤ normalizedStretching (matrix p a) := by
  rintro ⟨ε,hε,hbound⟩
  obtain ⟨p,a,hp,ha,haq,hsmall,_,_,_⟩ := exists_profile ε hε
  have hs := (hsmall 1 (by norm_num)).2
  simp only [one_smul] at hs
  exact (not_lt_of_ge (hbound p a hp ha haq)) hs

end OperatorDerivativeRewrite.Foundation.RestrictedEulerArbitraryDepletion
