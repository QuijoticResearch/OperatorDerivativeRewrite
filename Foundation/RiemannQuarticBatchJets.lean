import Foundation.RiemannQuarticStoredJets

/-! One stored prefix supplies every lower exponential coefficient, with
exactly the same rounded intervals as the original evaluator. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticBatchJets
open RiemannQuarticDyadic RiemannQuarticIntervalJets RiemannQuarticStoredJets

theorem expPrefix_stable (F : ℕ → Box) (base : Box) (p q : ℕ) :
    ∀ n ≤ q, expPrefix F base p q n=expJet F base p n := by
  induction q with
  | zero =>
    intro n hn
    have : n=0 := by omega
    subst n
    rfl
  | succ q ih =>
    intro n hn
    by_cases h : n ≤ q
    · simpa only [expPrefix, if_pos h] using ih n h
    · have : n=q+1 := by omega
      subst n
      rfl

theorem stored_lower_eq (F : ℕ → Box) (base : Box) (p q n : ℕ) (hn : n ≤ q) :
    (stored F base p q).getD n base=expJet F base p n := by
  rw [stored_agrees F base p q n hn, expPrefix_stable F base p q n hn]

theorem stored_lower_default_eq (F : ℕ → Box) (base d : Box) (p q n : ℕ)
    (hn : n ≤ q) :
    (stored F base p q).getD n d=expJet F base p n := by
  have hlt : n < (stored F base p q).length := by rw [stored_length]; omega
  have he : (stored F base p q).getD n d=(stored F base p q).getD n base := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]
  rw [he, stored_lower_eq F base p q n hn]

end OperatorDerivativeRewrite.Foundation.RiemannQuarticBatchJets
