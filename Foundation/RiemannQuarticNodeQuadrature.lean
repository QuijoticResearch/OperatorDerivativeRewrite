import Foundation.RiemannQuarticNodeJets

/-! Actual centered Taylor integrals and whole-cell error checks on the
160-cell partition of [0, 8/5]. Numerical checks are separate obligations. -/
noncomputable section
open Set MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticNodeQuadrature
open RiemannQuarticDyadic RiemannQuarticIntervalChecks RiemannQuarticIntervalTrig
open RiemannQuarticNodeJets RiemannQuarticChannelJets RiemannQuarticTaylorJets
open RiemannQuarticRealCertificate RiemannQuarticCellDomain

def center (j : ℕ) : ℚ := (2*j+1)/200
def cell (j : ℕ) : Box := range (j/100) ((j+1)/100) 192
def point (j : ℕ) : Box := rational (center j) 192
def pointTrig (j : ℕ) : Box × Box :=
  scaledTrig (mul X (point j) 192) 192 48 8
def taylorFactor (n : ℕ) : ℚ :=
  ((1/200 : ℚ)^(n+1)-(-1/200 : ℚ)^(n+1))/(n+1)
def polynomialBox (j k : ℕ) : Box :=
  let U := point j
  let J := pointTrig j
  let W := weightTable U 15
  RiemannQuarticDyadic.sum (fun n =>
    mul (integrandJet U X J (weights W) k 192 n) (rational (taylorFactor n) 192) 192) 192 16
def cellCheck (j : ℕ) : Bool :=
  let U := cell j
  let W := weightTable U 16
  let J := (range (-1) 1 192, range (-1) 1 192)
  (List.range 3).all (fun k =>
    inside (integrandJet U X J (weights W) k 192 16) (-(10^22)) (10^22))

theorem center_domain (j : ℕ) (hj : j < 160) :
    (center j : ℝ) ∈ Icc (0 : ℝ) (8/5) := by
  have hj' : (j : ℝ) ≤ 159 := by exact_mod_cast (show j ≤ 159 by omega)
  simp only [center, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat, Nat.cast_one]
  constructor <;> linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]

theorem pointTrig_mem (j : ℕ) (hj : j < 160) :
    Real.cos ((632083/10000 : ℝ)*(center j : ℝ)) ∈ (pointTrig j).1 ∧
      Real.sin ((632083/10000 : ℝ)*(center j : ℝ)) ∈ (pointTrig j).2 := by
  have hx : (632083/10000 : ℝ) ∈ X := by
    simpa [X] using rational_mem (632083/10000) 192
  exact scaledTrig_mem (mul_mem hx (rational_mem (center j) 192) 192) 192 48 8
    (by norm_num) (frequency_scaled_small _ (center_domain j hj))

theorem polynomialBox_mem (j k : ℕ) (hj : j < 160) (hk : k ≤ 2) :
    (∫ u in (center j : ℝ)-(1/200 : ℝ)..(center j : ℝ)+(1/200 : ℝ),
      localPolynomial (realIntegrand 4 k (632083/10000)) 15 (center j) u) ∈
      polynomialBox j k := by
  rw [localPolynomial_integral]
  have ht := pointTrig_mem j hj
  apply RiemannQuarticDyadic.sum_mem
  intro n hn
  have hn' : n ≤ 15 := by omega
  have hc := nodeJet_mem (rational_mem (center j) 192) (center_domain j hj)
    ht.1 ht.2 15 k n hk hn'
  have hf : (((1/200 : ℝ)^(n+1)-(-1/200 : ℝ)^(n+1))/(n+1 : ℝ)) ∈
      rational (taylorFactor n) 192 := by
    simpa only [taylorFactor, Rat.cast_div, Rat.cast_sub, Rat.cast_pow, Rat.cast_neg,
      Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using
      rational_mem (taylorFactor n) 192
  have hm := mul_mem hc hf 192
  simpa only [nodeJet, point, neg_div, div_eq_mul_inv, neg_mul, mul_assoc] using hm

theorem cell_domain (j : ℕ) (hj : j < 160) (u : ℝ)
    (hu : u ∈ Icc (center j-(1/200 : ℝ)) (center j+(1/200 : ℝ))) :
    u ∈ cell j ∧ u ∈ Icc (0 : ℝ) (8/5) := by
  have hj' : (j : ℝ) ≤ 159 := by exact_mod_cast (show j ≤ 159 by omega)
  simp only [center, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat, Nat.cast_one] at hu
  have hl : (↑(j/100 : ℚ) : ℝ) ≤ u := by push_cast; linarith [hu.1]
  have hr : u ≤ (↑((j+1)/100 : ℚ) : ℝ) := by push_cast; linarith [hu.2]
  have hz : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  exact ⟨range_mem hl hr 192, by constructor <;> linarith [hu.1, hu.2]⟩

theorem cell_sixteenth (j : ℕ) (hj : j < 160) (hcheck : cellCheck j=true)
    (u : ℝ) (hu : u ∈ Icc (center j-(1/200 : ℝ)) (center j+(1/200 : ℝ)))
    (k : ℕ) (hk : k ≤ 2) :
    |coefficient (realIntegrand 4 k (632083/10000)) 16 u| ≤ (10^22 : ℝ) := by
  have hd := cell_domain j hj u hu
  have hc : Real.cos ((632083/10000 : ℝ)*u) ∈ range (-1) 1 192 :=
    range_mem (by simpa using Real.neg_one_le_cos _) (by simpa using Real.cos_le_one _) 192
  have hs : Real.sin ((632083/10000 : ℝ)*u) ∈ range (-1) 1 192 :=
    range_mem (by simpa using Real.neg_one_le_sin _) (by simpa using Real.sin_le_one _) 192
  have hb := nodeJet_mem (J := (range (-1) 1 192, range (-1) 1 192))
    hd.1 hd.2 hc hs 16 k 16 hk le_rfl
  have he := (List.all_eq_true.mp hcheck) k (by simp; omega)
  have h := inside_spec he hb
  apply abs_le.mpr
  norm_num at h ⊢
  exact h

theorem cell_taylor_error (j k : ℕ) (hj : j < 160) (hk : k ≤ 2)
    (hcheck : cellCheck j=true) :
    |(∫ u in (center j : ℝ)-(1/200 : ℝ)..(center j : ℝ)+(1/200 : ℝ),
        realIntegrand 4 k (632083/10000) u)-
      (∫ u in (center j : ℝ)-(1/200 : ℝ)..(center j : ℝ)+(1/200 : ℝ),
        localPolynomial (realIntegrand 4 k (632083/10000)) 15 (center j) u)| ≤
      (1/10^16 : ℝ) := by
  have he := local_integral_error (realIntegrand 4 k (632083/10000))
    (realIntegrand_contDiff 4 k (632083/10000)) 15 (center j) (1/200) (10^22)
    (by norm_num) (by positivity)
    (fun u hu => cell_sixteenth j hj hcheck u hu k hk)
  norm_num at he
  exact he.trans (by norm_num)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticNodeQuadrature
