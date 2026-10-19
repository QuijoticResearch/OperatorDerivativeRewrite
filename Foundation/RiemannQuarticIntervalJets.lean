import Foundation.RiemannQuarticIntervalTrig

/-! Sound interval propagation for actual normalized product/exponential jets. -/
open Inclusion
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticIntervalJets
open RiemannQuarticDyadic RiemannQuarticTaylorJets

def convolution (F G : ℕ → Box) (p n : ℕ) : Box :=
  sum (fun i => mul (F i) (G (n-i)) p) p (n+1)

theorem convolution_mem (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : ℝ) (F G : ℕ → Box) (p n : ℕ)
    (hF : ∀ i ≤ n, coefficient f i x ∈ F i)
    (hG : ∀ i ≤ n, coefficient g i x ∈ G i) :
    coefficient (fun u => f u*g u) n x ∈ convolution F G p n := by
  rw [coefficient_mul f g hf hg n x]
  apply RiemannQuarticDyadic.sum_mem
  intro i hi
  have hin : i ≤ n := by omega
  exact mul_mem (hF i hin) (hG (n-i) (Nat.sub_le _ _)) p

def expStep (F E : ℕ → Box) (p n : ℕ) : Box :=
  divNat (sum (fun i => mul (mul (rational (i+1 : ℚ) p) (F (i+1)) p)
    (E (n-i)) p) p (n+1)) (n+1) p

def expPrefix (F : ℕ → Box) (base : Box) (p : ℕ) : ℕ → (ℕ → Box)
  | 0 => fun _ => base
  | n+1 => fun k =>
      if k ≤ n then expPrefix F base p n k else expStep F (expPrefix F base p n) p n

theorem expPrefix_mem (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℝ)
    (F : ℕ → Box) (base : Box) (p : ℕ) (hbase : Real.exp (f x) ∈ base) (n : ℕ) :
    (∀ i ≤ n, coefficient f i x ∈ F i) →
      ∀ k ≤ n, coefficient (fun u => Real.exp (f u)) k x ∈ expPrefix F base p n k := by
  induction n with
  | zero =>
    intro hF k hk
    have hk0 : k=0 := by omega
    subst k
    simpa only [expPrefix, coefficient_zero] using hbase
  | succ n ih =>
    intro hF k hk
    have hold := ih (fun i hi => hF i (by omega))
    by_cases hkn : k ≤ n
    · simpa only [expPrefix, if_pos hkn] using hold k hkn
    · have hkeq : k=n+1 := by omega
      subst k
      simp only [expPrefix, if_neg (by omega : ¬ n+1 ≤ n)]
      rw [coefficient_exp_succ f hf n x]
      have hsum : (∑ i ∈ Finset.range (n+1), (i+1 : ℝ)*coefficient f (i+1) x*
          coefficient (fun u => Real.exp (f u)) (n-i) x) ∈
          sum (fun i => mul (mul (rational (i+1 : ℚ) p) (F (i+1)) p)
            (expPrefix F base p n (n-i)) p) p (n+1) := by
        apply RiemannQuarticDyadic.sum_mem
        intro i hi
        have hin : i ≤ n := by omega
        have hc : (i+1 : ℝ) ∈ rational (i+1 : ℚ) p := by
          simpa only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using rational_mem (i+1 : ℚ) p
        exact mul_mem (mul_mem hc (hF (i+1) (by omega)) p)
          (hold (n-i) (Nat.sub_le _ _)) p
      simpa only [Nat.cast_add, Nat.cast_one, expStep] using divNat_mem hsum (n+1) p

def expJet (F : ℕ → Box) (base : Box) (p n : ℕ) : Box := expPrefix F base p n n

theorem expJet_mem (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℝ)
    (F : ℕ → Box) (base : Box) (p n : ℕ) (hbase : Real.exp (f x) ∈ base)
    (hF : ∀ i ≤ n, coefficient f i x ∈ F i) :
    coefficient (fun u => Real.exp (f u)) n x ∈ expJet F base p n :=
  expPrefix_mem f hf x F base p hbase n hF n le_rfl

end OperatorDerivativeRewrite.Foundation.RiemannQuarticIntervalJets
