import Foundation.YMPositivePower

/-! Quantitative bounded-probe mixing by the existing reset-range estimate.
The invariant probability may differ from the row-normalization reference. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.YMPositiveMixing
variable {Ω : Type*} [MeasurableSpace Ω] [Nonempty Ω]
variable (μ π : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
variable (k : Ω → Ω → ℝ) (m M : ℝ)
variable (hk : Measurable (Function.uncurry k)) (hm : 0 < m)
variable (hb : ∀ x y, m ≤ k x y ∧ k x y ≤ M)

include hk hm hb in
/-- No stationarity for μ is assumed. Centering is under the actual π. -/
theorem centered_iterate_bound (F : ℕ → Ω → ℝ)
    (hF : ∀ n, Measurable (F n))
    (hrec : ∀ n x, F (n+1) x=YMPositiveKernel.average μ k (F n) x)
    (hzero : ∀ n, (∫ x,F n x ∂π)=0)
    (B : ℝ) (hB : ∀ x, |F 0 x| ≤ B) (n : ℕ) (x : Ω) :
    |F n x| ≤ 2*B*(1-m/M)^n := by
  let θ := 1-m/M
  have hrange (n : ℕ) : ∃ L U : ℝ,
      (∀ y,L ≤ F n y ∧ F n y ≤ U) ∧ U-L=2*B*θ^n := by
    induction n with
    | zero => exact ⟨-B,B,(fun y => abs_le.mp (hB y)),by simp; ring⟩
    | succ n ih =>
      obtain ⟨L,U,hLU,hw⟩ := ih
      let c := (m/M)*(∫ y,F n y ∂μ)
      refine ⟨θ*L+c,θ*U+c,?_,?_⟩
      · intro y
        have he := YMPositivePower.average_reset_range μ k m M hk hm hb (F n) (hF n) L U hLU y
        rw [hrec]
        change θ*L ≤ _-c ∧ _-c ≤ θ*U at he
        constructor <;> linarith [he.1,he.2]
      · calc
          θ*U+c-(θ*L+c)=θ*(U-L) := by ring
          _=2*B*θ^(n+1) := by rw [hw,pow_succ]; ring
  obtain ⟨L,U,hLU,hw⟩ := hrange n
  have hi : Integrable (F n) π := Integrable.of_bound (hF n).aestronglyMeasurable
    (|L|+|U|) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> linarith [(hLU y).1,(hLU y).2,le_abs_self U,neg_abs_le L,abs_nonneg L,abs_nonneg U])
  have hL := integral_mono (integrable_const L) hi (fun y => (hLU y).1)
  have hU := integral_mono hi (integrable_const U) (fun y => (hLU y).2)
  simp only [integral_const,probReal_univ,one_smul,hzero] at hL hU
  change |F n x| ≤ 2*B*θ^n
  rw [← hw]
  exact abs_le.mpr ⟨by linarith [(hLU x).1],by linarith [(hLU x).2]⟩

end OperatorDerivativeRewrite.Foundation.YMPositiveMixing
