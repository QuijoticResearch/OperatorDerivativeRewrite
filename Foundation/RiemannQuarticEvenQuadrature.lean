import Foundation.RiemannQuarticGridAssembly

/-! Odd powers integrate to zero on the centered cell. Compute only the
eight contributing coefficients of the actual degree15 Taylor integral. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticEvenQuadrature
open RiemannQuarticDyadic RiemannQuarticNodeQuadrature RiemannQuarticNodeJets
open RiemannQuarticTaylorJets RiemannQuarticRealCertificate RiemannQuarticChannelJets
open RiemannQuarticGridAssembly
open RiemannQuarticIntervalChecks

theorem sum_pairs (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (2*n), f i)=
      ∑ i ∈ Finset.range n, (f (2*i)+f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem odd_factor (i : ℕ) : taylorFactor (2*i+1)=0 := by
  simp only [taylorFactor, pow_add, pow_mul]
  norm_num

theorem polynomialIntegral_even (j k : ℕ) :
    polynomialIntegral j k=
      ∑ i ∈ Finset.range 8,
        coefficient (realIntegrand 4 k (632083/10000)) (2*i) (center j)*
          (taylorFactor (2*i) : ℝ) := by
  rw [polynomialIntegral, localPolynomial_integral]
  have hf (n : ℕ) :
      (((1/200 : ℝ)^(n+1)-(-(1/200 : ℝ))^(n+1))/(n+1 : ℝ))=
        (taylorFactor n : ℝ) := by
    push_cast
    simp only [taylorFactor]
    push_cast
    ring
  simp_rw [mul_div_assoc, hf]
  rw [show 15+1=2*8 by rfl, sum_pairs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [odd_factor]
  simp

def evenPolynomialBox (j k : ℕ) : Box :=
  let U := point j
  let J := pointTrig j
  let W := weightTable U 14
  RiemannQuarticDyadic.sum (fun i =>
    mul (integrandJet U X J (weights W) k 192 (2*i))
      (rational (taylorFactor (2*i)) 192) 192) 192 8

theorem evenPolynomialBox_mem (j k : ℕ) (hj : j < 160) (hk : k ≤ 2) :
    polynomialIntegral j k ∈ evenPolynomialBox j k := by
  rw [polynomialIntegral_even]
  have ht := pointTrig_mem j hj
  apply RiemannQuarticDyadic.sum_mem
  intro i hi
  have hn : 2*i ≤ 14 := by omega
  have hc := nodeJet_mem (rational_mem (center j) 192) (center_domain j hj)
    ht.1 ht.2 14 k (2*i) hk hn
  exact mul_mem hc (rational_mem (taylorFactor (2*i)) 192) 192

def evenTotalBox (k : ℕ) : Box :=
  RiemannQuarticDyadic.sum (fun j => evenPolynomialBox j k) 192 160

theorem evenTotalBox_mem (k : ℕ) (hk : k ≤ 2) :
    totalPolynomial k ∈ evenTotalBox k := by
  apply RiemannQuarticDyadic.sum_mem
  intro j hj
  exact evenPolynomialBox_mem j k hj hk

theorem negative_Laguerre_of_checks
    (hchecks : ∀ j < 160, cellCheck j=true)
    (h0 : inside (evenTotalBox 0) (-1) (-164/10^12)=true)
    (h1 : inside (evenTotalBox 1) (-38/10^14) (38/10^14)=true)
    (h2 : inside (evenTotalBox 2) (-1) (-1455/10^13)=true) :
    realLaguerre (632083/10000) < -(2/10^20 : ℝ) := by
  have hp0 := inside_spec h0 (evenTotalBox_mem 0 (by norm_num))
  have hp1 := inside_spec h1 (evenTotalBox_mem 1 (by norm_num))
  have hp2 := inside_spec h2 (evenTotalBox_mem 2 (by norm_num))
  norm_num at hp0 hp1 hp2
  apply negative_Laguerre_of_polynomial_bounds hchecks
  · convert hp0.2 using 1 <;> norm_num
  · exact abs_le.mpr ⟨by linarith [hp1.1], by linarith [hp1.2]⟩
  · convert hp2.2 using 1 <;> norm_num

end OperatorDerivativeRewrite.Foundation.RiemannQuarticEvenQuadrature
