import Foundation.RiemannQuarticNodeQuadrature

/-! Assembly of actual cell integrals. Neither arithmetic checks nor the
three final integral enclosures are hypotheses disguised as conclusions. -/
noncomputable section
open Set MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticGridAssembly
open RiemannQuarticDyadic RiemannQuarticNodeQuadrature RiemannQuarticTaylorJets
open RiemannQuarticRealCertificate

def polynomialIntegral (j k : ℕ) : ℝ :=
  ∫ u in (center j : ℝ)-(1/200 : ℝ)..(center j : ℝ)+(1/200 : ℝ),
    localPolynomial (realIntegrand 4 k (632083/10000)) 15 (center j) u
def totalPolynomial (k : ℕ) : ℝ := ∑ j ∈ Finset.range 160, polynomialIntegral j k
def totalBox (k : ℕ) : Box :=
  RiemannQuarticDyadic.sum (fun j => polynomialBox j k) 192 160

theorem center_left (j : ℕ) : (center j : ℝ)-(1/200 : ℝ)=(j : ℝ)/100 := by
  simp only [RiemannQuarticNodeQuadrature.center]
  push_cast
  ring
theorem center_right (j : ℕ) : (center j : ℝ)+(1/200 : ℝ)=(j+1 : ℝ)/100 := by
  simp only [RiemannQuarticNodeQuadrature.center]
  push_cast
  ring

theorem quadrature_partition (k : ℕ) :
    realQuadrature 4 k (632083/10000)=
      ∑ j ∈ Finset.range 160,
        ∫ u in (center j : ℝ)-(1/200 : ℝ)..(center j : ℝ)+(1/200 : ℝ),
          realIntegrand 4 k (632083/10000) u := by
  simp_rw [center_left, center_right]
  have hf := (realIntegrand_contDiff 4 k (632083/10000)).continuous
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ)/100) (n := 160)
    (fun j _ => hf.intervalIntegrable (μ := volume) (a := (j : ℝ)/100)
      (b := ((j+1 : ℕ) : ℝ)/100))
  simpa only [realQuadrature, Nat.cast_zero, zero_div, Nat.cast_ofNat,
    Nat.cast_add, Nat.cast_one, show (160 : ℝ)/100=8/5 by norm_num] using h.symm

theorem totalBox_mem (k : ℕ) (hk : k ≤ 2) : totalPolynomial k ∈ totalBox k := by
  apply RiemannQuarticDyadic.sum_mem
  intro j hj
  exact polynomialBox_mem j k hj hk

theorem quadrature_polynomial_error (k : ℕ) (hk : k ≤ 2)
    (hchecks : ∀ j < 160, cellCheck j=true) :
    |realQuadrature 4 k (632083/10000)-totalPolynomial k| ≤ (16/10^15 : ℝ) := by
  rw [quadrature_partition, totalPolynomial, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range 160,
        |(∫ u in (center j : ℝ)-(1/200 : ℝ)..(center j : ℝ)+(1/200 : ℝ),
          realIntegrand 4 k (632083/10000) u)-polynomialIntegral j k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range 160, (1/10^16 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact cell_taylor_error j k (Finset.mem_range.mp hj) hk
        (hchecks j (Finset.mem_range.mp hj))
    _ = _ := by norm_num

theorem negative_Laguerre_of_polynomial_bounds
    (hchecks : ∀ j < 160, cellCheck j=true)
    (h0 : totalPolynomial 0 ≤ -(164/10^12 : ℝ))
    (h1 : |totalPolynomial 1| ≤ (38/10^14 : ℝ))
    (h2 : totalPolynomial 2 ≤ -(1455/10^13 : ℝ)) :
    realLaguerre (632083/10000) < -(2/10^20 : ℝ) := by
  have he0 := abs_le.mp (quadrature_polynomial_error 0 (by norm_num) hchecks)
  have he1 := abs_le.mp (quadrature_polynomial_error 1 (by norm_num) hchecks)
  have he2 := abs_le.mp (quadrature_polynomial_error 2 (by norm_num) hchecks)
  have hp1 := abs_le.mp h1
  apply negative_Laguerre_of_enclosures
  · linarith [he0.2]
  · exact abs_le.mpr ⟨by linarith [hp1.1, he1.1], by linarith [hp1.2, he1.2]⟩
  · linarith [he2.2]

end OperatorDerivativeRewrite.Foundation.RiemannQuarticGridAssembly
