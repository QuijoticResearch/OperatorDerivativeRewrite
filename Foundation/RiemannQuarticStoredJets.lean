import Foundation.RiemannQuarticIntervalJets

/-! Store each exponential coefficient once. The resulting intervals agree
exactly with the previously verified structurally recursive evaluator. -/
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticStoredJets
open RiemannQuarticDyadic RiemannQuarticIntervalJets RiemannQuarticTaylorJets

private theorem sum_congr (F G : ℕ → Box) (p n : ℕ) (h : ∀ i < n, F i=G i) :
    sum F p n=sum G p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

private theorem step_congr (F E E' : ℕ → Box) (p n : ℕ) (h : ∀ i ≤ n, E i=E' i) :
    expStep F E p n=expStep F E' p n := by
  unfold expStep
  apply congrArg (fun V => divNat V (n+1) p)
  apply sum_congr
  intro i hi
  rw [h (n-i) (Nat.sub_le _ _)]

def stored (F : ℕ → Box) (base : Box) (p : ℕ) : ℕ → List Box
  | 0 => [base]
  | n+1 =>
      let previous := stored F base p n
      previous ++ [expStep F (fun i => previous.getD i base) p n]

theorem stored_length (F : ℕ → Box) (base : Box) (p n : ℕ) :
    (stored F base p n).length=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stored, List.length_append, List.length_cons, List.length_nil, ih]

private theorem getD_append_left (L R : List Box) (d : Box) (i : ℕ) (hi : i < L.length) :
    (L++R).getD i d=L.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_last (L : List Box) (v d : Box) :
    (L++[v]).getD L.length d=v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

theorem stored_agrees (F : ℕ → Box) (base : Box) (p n : ℕ) :
    ∀ k ≤ n, (stored F base p n).getD k base=expPrefix F base p n k := by
  induction n with
  | zero =>
    intro k hk
    have hk0 : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    intro k hk
    by_cases hkn : k ≤ n
    · have hlt : k < (stored F base p n).length := by rw [stored_length]; omega
      simp only [stored, getD_append_left _ _ _ _ hlt, expPrefix, if_pos hkn]
      exact ih k hkn
    · have hk' : k=n+1 := by omega
      subst k
      have hl := stored_length F base p n
      have hget := getD_append_last (stored F base p n)
        (expStep F (fun i => (stored F base p n).getD i base) p n) base
      rw [hl] at hget
      simp only [stored, hget, expPrefix, if_neg (by omega : ¬ n+1 ≤ n)]
      exact step_congr F _ _ p n ih

def expJetStored (F : ℕ → Box) (base : Box) (p n : ℕ) : Box :=
  (stored F base p n).getD n base

theorem expJetStored_eq (F : ℕ → Box) (base : Box) (p n : ℕ) :
    expJetStored F base p n=expJet F base p n :=
  stored_agrees F base p n n le_rfl

theorem expJetStored_mem (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℝ)
    (F : ℕ → Box) (base : Box) (p n : ℕ) (hb : Real.exp (f x) ∈ base)
    (hF : ∀ i ≤ n, coefficient f i x ∈ F i) :
    coefficient (fun u => Real.exp (f u)) n x ∈ expJetStored F base p n := by
  rw [expJetStored_eq]
  exact expJet_mem f hf x F base p n hb hF

end OperatorDerivativeRewrite.Foundation.RiemannQuarticStoredJets
