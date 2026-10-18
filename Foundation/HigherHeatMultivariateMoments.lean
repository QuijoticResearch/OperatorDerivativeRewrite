import Foundation.HigherHeatChronologicalProbes
import Foundation.HigherHeatStepIntegralRealization
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Actual multivariate signed polynomial moments and the strict-simplex quartic
reconstruction obstruction, with arbitrary-grid nonconvergence. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMultivariateMoments
open HigherHeatSignedLaws HigherHeatPolynomialRealization HigherHeatChronologicalProbes
  HigherHeatStepIntegralLaws HigherHeatStepIntegralRealization
variable {ι : Type*} [Fintype ι]

def value (P : MvPolynomial ι ℝ) (x : ι → ℝ) : ℂ := (MvPolynomial.eval x P : ℂ)

theorem value_monomial (d : ι →₀ ℕ) (c : ℝ) (x : ι → ℝ) :
    value (MvPolynomial.monomial d c) x = c • powers d x := by
  simp [value, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype d (fun i n => x i ^ n) (fun _ => pow_zero _),
    powers, Complex.real_smul]

omit [Fintype ι] in
theorem value_add (P Q : MvPolynomial ι ℝ) (x : ι → ℝ) :
    value (P + Q) x = value P x + value Q x := by simp [value]

theorem polynomial_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (P : MvPolynomial ι ℝ) :
    (incrementLaw m hm t ht).Integrable (value P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    have he : value (MvPolynomial.monomial d c) = (fun x => c • powers d x) :=
      funext (value_monomial d c)
    rw [he]
    exact VectorMeasure.Integrable.fun_smul c (powers_integrable m hm t ht d)
  | add P Q hP hQ =>
    have he : value (P+Q) = (fun x => value P x + value Q x) := funext (value_add P Q)
    rw [he]
    exact hP.add hQ


omit [Fintype ι] in
theorem value_smul (c : ℝ) (P : MvPolynomial ι ℝ) (x : ι → ℝ) :
    value (c • P) x = c • value P x := by simp [value, Complex.real_smul]

def mean (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) :
    MvPolynomial ι ℝ →ₗ[ℝ] ℂ where
  toFun P := ∫ᵛ x, value P x ∂<•incrementLaw m hm t ht
  map_add' P Q := by
    simp_rw [value_add]
    exact VectorMeasure.integral_add (polynomial_integrable m hm t ht P)
      (polynomial_integrable m hm t ht Q)
  map_smul' c P := by
    change (∫ᵛ x, value (c • P) x ∂<•incrementLaw m hm t ht) =
      c • (∫ᵛ x, value P x ∂<•incrementLaw m hm t ht)
    simp_rw [value_smul]
    rw [VectorMeasure.integral_fun_smul]

theorem mean_monomial (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (d : ι →₀ ℕ) (c : ℝ) :
    mean m hm t ht (MvPolynomial.monomial d c) =
      c • (∏ i, (kernelExpectation m hm (t i) (ht i) (Polynomial.X ^ d i) : ℂ)) := by
  change (∫ᵛ x, value (MvPolynomial.monomial d c) x ∂<•incrementLaw m hm t ht) = _
  simp_rw [value_monomial]
  rw [VectorMeasure.integral_fun_smul, powers_integral]

theorem mean_monomial_off_order (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (d : ι →₀ ℕ) (c : ℝ) (i : ι) (hi : ¬ 2*m ∣ d i) :
    mean m hm t ht (MvPolynomial.monomial d c) = 0 := by
  rw [mean_monomial]
  have hz : (∏ j, (kernelExpectation m hm (t j) (ht j)
      (Polynomial.X ^ d j) : ℂ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [kernelExpectation_eq_moments, PseudoPolynomialStein.expectation_X_pow,
      PseudoPolynomialStein.moment_off_order (2*m) (by omega) _ _ hi]
    rfl
  rw [hz, smul_zero]

open Classical in
def indicator (I : Finset ι) : ι →₀ ℕ := ∑ i ∈ I, Finsupp.single i 1

omit [Fintype ι] in
theorem indicator_apply (I : Finset ι) (i : ι) :
    indicator I i = exponent I 1 i := by
  classical
  simp [indicator, exponent, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem indicator_degree (I : Finset ι) : (indicator I).sum (fun _ n => n) = I.card := by
  classical
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp_rw [indicator_apply]
  simp [exponent]

theorem off_order_of_degree (p : ℕ) (I : Finset ι) (d : ι →₀ ℕ)
    (hpos : ∀ i ∈ I, 0 < d i) (hd : d.sum (fun _ n => n) < p * I.card) :
    ∃ i ∈ I, ¬ p ∣ d i := by
  classical
  by_contra hn
  have hall : ∀ i ∈ I, p ≤ d i := by
    intro i hi
    have hh : p ∣ d i := by
      by_contra h
      exact hn ⟨i, hi, h⟩
    exact Nat.le_of_dvd (hpos i hi) hh
  have hb : p * I.card ≤ ∑ i ∈ I, d i := by
    calc
      p * I.card = ∑ _i ∈ I, p := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ I, d i := Finset.sum_le_sum hall
  have hs : (∑ i ∈ I, d i) ≤ d.sum (fun _ n => n) := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ I)
  omega



omit [Fintype ι] in
theorem exponent_degree_add (d e : ι →₀ ℕ) :
    (d+e).sum (fun _ n => n) = d.sum (fun _ n => n) + e.sum (fun _ n => n) := by
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem chronological_monomial_annihilates (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (I : Finset ι) (c : ℝ) (Q : MvPolynomial ι ℝ)
    (hdeg : I.card + Q.totalDegree < (2*m)*I.card) :
    mean m hm t ht (MvPolynomial.monomial (indicator I) c * Q) = 0 := by
  classical
  calc
    _ = mean m hm t ht (MvPolynomial.monomial (indicator I) c *
        (∑ d ∈ Q.support, MvPolynomial.monomial d (Q.coeff d))) :=
      congrArg (fun R => mean m hm t ht (MvPolynomial.monomial (indicator I) c * R))
        (MvPolynomial.as_sum Q)
    _ = 0 := by
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_eq_zero
      intro d hd
      rw [MvPolynomial.monomial_mul_monomial]
      have hpos : ∀ i ∈ I, 0 < (indicator I + d) i := by
        intro i hi
        simp [Finsupp.add_apply, indicator_apply, exponent, hi]
      have hb : (indicator I+d).sum (fun _ n => n) < (2*m)*I.card := by
        rw [exponent_degree_add, indicator_degree]
        have hh := MvPolynomial.le_totalDegree hd
        omega
      obtain ⟨i, _, hi⟩ := off_order_of_degree (2*m) I (indicator I+d) hpos hb
      exact mean_monomial_off_order m hm t ht _ _ i hi

omit [Fintype ι] in
theorem value_mul (P Q : MvPolynomial ι ℝ) (x : ι → ℝ) :
    value (P*Q) x = value P x * value Q x := by simp [value]

theorem value_indicator (I : Finset ι) (x : ι → ℝ) :
    value (MvPolynomial.monomial (indicator I) 1) x = monomial I x := by
  rw [value_monomial, one_smul]
  congr 1
  exact funext (indicator_apply I)

theorem chronological_polynomial_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (I : Finset ι) (Q : MvPolynomial ι ℝ) :
    (incrementLaw m hm t ht).Integrable (fun x => monomial I x * value Q x) := by
  have he : (fun x => monomial I x * value Q x) =
      value (MvPolynomial.monomial (indicator I) 1 * Q) := by
    funext x
    rw [value_mul, value_indicator]
  rw [he]
  exact polynomial_integrable m hm t ht _

theorem chronological_polynomial_zero (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (I : Finset ι) (Q : MvPolynomial ι ℝ)
    (hdeg : I.card + Q.totalDegree < (2*m)*I.card) :
    (∫ᵛ x, monomial I x * value Q x ∂<•incrementLaw m hm t ht) = 0 := by
  have he := chronological_monomial_annihilates m hm t ht I 1 Q hdeg
  change (∫ᵛ x, value (MvPolynomial.monomial (indicator I) 1 * Q) x
    ∂<•incrementLaw m hm t ht) = 0 at he
  simpa only [value_mul, value_indicator] using he



def terminal : MvPolynomial ι ℝ := ∑ i, MvPolynomial.X i

theorem terminal_degree : (terminal (ι := ι)).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_X i).le

theorem terminal_power_degree (n : ℕ) : ((terminal (ι := ι))^n).totalDegree ≤ n := by
  calc
    _ ≤ n * (terminal (ι := ι)).totalDegree := MvPolynomial.totalDegree_pow _ _
    _ ≤ n * 1 := Nat.mul_le_mul_left _ terminal_degree
    _ = n := Nat.mul_one _

theorem value_terminal_power (n : ℕ) (x : ι → ℝ) :
    value ((terminal (ι := ι))^n) x = (∑ i, (x i : ℂ))^n := by
  simp [value, terminal]

theorem terminal_power_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (n : ℕ) :
    (incrementLaw m hm t ht).Integrable (fun x => (∑ i, (x i : ℂ))^n) := by
  have he : value ((terminal (ι := ι))^n) = (fun x => (∑ i, (x i : ℂ))^n) :=
    funext (value_terminal_power n)
  rw [← he]
  exact polynomial_integrable m hm t ht _

theorem strict_terminal_cross_zero (m : ℕ) (hm : 2 ≤ m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (I : Finset ι) (hI : I.card = 2*m) :
    (∫ᵛ x, monomial I x * (∑ i, (x i : ℂ))^(2*m)
      ∂<•incrementLaw m (by omega) t ht) = 0 := by
  have he := chronological_polynomial_zero m (by omega) t ht I
    ((terminal (ι := ι))^(2*m)) (by
      rw [hI]
      have hh := terminal_power_degree (ι := ι) (2*m)
      nlinarith)
  simpa only [value_terminal_power] using he



def chronologicalPolynomial (A : Finset (Finset ι)) (c : Finset ι → ℝ) :
    MvPolynomial ι ℝ := ∑ I ∈ A, MvPolynomial.monomial (indicator I) (c I)

theorem value_chronological (A : Finset (Finset ι)) (c : Finset ι → ℝ) (x : ι → ℝ) :
    value (chronologicalPolynomial A c) x = chronological A c x := by
  simp only [chronologicalPolynomial, value, map_sum, Complex.ofReal_sum,
    chronological]
  apply Finset.sum_congr rfl
  intro I _
  change value (MvPolynomial.monomial (indicator I) (c I)) x = _
  rw [value_monomial]
  congr 1
  exact congrArg (fun d => powers d x) (funext (indicator_apply I))

theorem mean_chronological_product_zero (m : ℕ) (hm : 2 ≤ m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (A B : Finset (Finset ι)) (c d : Finset ι → ℝ)
    (hA : ∀ I ∈ A, I.Nonempty) :
    mean m (by omega) t ht (chronologicalPolynomial A c * chronologicalPolynomial B d) = 0 := by
  change (∫ᵛ x, value (chronologicalPolynomial A c * chronologicalPolynomial B d) x
    ∂<•incrementLaw m (by omega) t ht) = 0
  simp_rw [value_mul, value_chronological]
  exact chronological_gram_zero m hm t ht A B c d hA

theorem mean_chronological_annihilates (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (A : Finset (Finset ι)) (c : Finset ι → ℝ)
    (Q : MvPolynomial ι ℝ) (hdeg : ∀ I ∈ A, I.card + Q.totalDegree < (2*m)*I.card) :
    mean m hm t ht (chronologicalPolynomial A c * Q) = 0 := by
  rw [chronologicalPolynomial, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro I hI
  exact chronological_monomial_annihilates m hm t ht I (c I) Q (hdeg I hI)

theorem mean_C (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (c : ℝ) : mean m hm t ht (MvPolynomial.C c) = (c : ℂ) := by
  have he := mean_monomial m hm t ht (0 : ι →₀ ℕ) c
  simpa [kernelExpectation_one, Complex.real_smul] using he

theorem terminal_moment (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (hT : 0 < ∑ i, t i) (n : ℕ) :
    mean m hm t ht ((terminal (ι := ι))^n) =
      (PseudoPolynomialStein.moment (2*m)
        ((-1:ℝ)^(m+1)*((∑ i, t i : ℝ≥0):ℝ)) n : ℂ) := by
  have hi : (incrementLaw m hm t ht).Integrable
      ((fun y : ℝ => (y : ℂ)^n) ∘ integralMap (fun _ : ι => (1 : ℝ))) := by
    simpa [Function.comp_def, integralMap, Complex.ofReal_sum] using
      terminal_power_integrable m hm t ht n
  have hfm : Continuous (fun y : ℝ => (y : ℂ)^n) := by fun_prop
  have he : (∫ᵛ y : ℝ, (y : ℂ)^n ∂<•(incrementLaw m hm t ht).map
      (integralMap (fun _ : ι => (1 : ℝ)))) =
      (∫ᵛ x, ((integralMap (fun _ : ι => (1 : ℝ)) x : ℝ) : ℂ)^n
        ∂<•incrementLaw m hm t ht) :=
    VectorMeasure.integral_map (integralMap_measurable (fun _ : ι => (1 : ℝ)))
      hfm.aestronglyMeasurable hi
  change (∫ᵛ x, value ((terminal (ι := ι))^n) x ∂<•incrementLaw m hm t ht) = _
  simp_rw [value_terminal_power]
  have he' : (∫ᵛ y : ℝ, (y : ℂ)^n ∂<•integralLaw m hm t ht (fun _ => 1)) =
      (∫ᵛ x, (∑ i, (x i : ℂ))^n ∂<•incrementLaw m hm t ht) := by
    simpa [integralLaw, integralMap, Complex.ofReal_sum] using he
  rw [← he', integralLaw_eq_heatLaw]
  simp only [effectiveTime, nnnorm_one, one_pow, mul_one]
  rw [heatLaw, dite_eq_left hT, HigherHeatSignedPolynomialCalculus.signed_moment]



def quarticTarget (T : ℝ≥0) : MvPolynomial ι ℝ :=
  (terminal (ι := ι))^4 + MvPolynomial.C (24*(T:ℝ))

theorem quarticTarget_degree (T : ℝ≥0) : (quarticTarget (ι := ι) T).totalDegree ≤ 4 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact terminal_power_degree 4
  · change (MvPolynomial.C (24*(T:ℝ)) : MvPolynomial ι ℝ).totalDegree ≤ 4
    rw [MvPolynomial.totalDegree_C]
    omega

theorem quarticTarget_square_mean (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (T : ℝ≥0) (hT : 0 < T) (hsum : ∑ i, t i = T) :
    mean 2 (by norm_num) t ht ((quarticTarget (ι := ι) T)^2) =
      19584*((T:ℝ):ℂ)^2 := by
  have htpos : 0 < ∑ i, t i := by rw [hsum]; exact hT
  have h4 : mean 2 (by norm_num) t ht ((terminal (ι := ι))^4) =
      -24*((T:ℝ):ℂ) := by
    rw [terminal_moment 2 (by norm_num) t ht htpos 4, hsum]
    norm_num [PseudoPolynomialStein.moment]
    ring
  have h8 : mean 2 (by norm_num) t ht ((terminal (ι := ι))^8) =
      20160*((T:ℝ):ℂ)^2 := by
    rw [terminal_moment 2 (by norm_num) t ht htpos 8, hsum]
    norm_num [PseudoPolynomialStein.moment]
    ring
  have halg : (quarticTarget (ι := ι) T)^2 = (terminal (ι := ι))^8 +
      (48*(T:ℝ)) • (terminal (ι := ι))^4 + MvPolynomial.C (576*(T:ℝ)^2) := by
    simp only [quarticTarget, Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, map_pow]
    have h24 : MvPolynomial.C (24:ℝ) = (24:MvPolynomial ι ℝ) :=
      map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ) 24
    have h48 : MvPolynomial.C (48:ℝ) = (48:MvPolynomial ι ℝ) :=
      map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ) 48
    have h576 : MvPolynomial.C (576:ℝ) = (576:MvPolynomial ι ℝ) :=
      map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ) 576
    rw [h24, h48, h576]
    ring
  rw [halg, map_add, map_add, map_smul, h4, h8, mean_C]
  simp only [Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_pow]
  norm_num <;> ring

theorem quartic_chronological_residual_mean (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (T : ℝ≥0) (hT : 0 < T) (hsum : ∑ i, t i = T)
    (A : Finset (Finset ι)) (c : Finset ι → ℝ) (hA : ∀ I ∈ A, I.card = 4) :
    mean 2 (by norm_num) t ht
      ((chronologicalPolynomial A c - quarticTarget (ι := ι) T)^2) =
      19584*((T:ℝ):ℂ)^2 := by
  have hgram := mean_chronological_product_zero 2 (by norm_num) t ht A A c c (by
    intro I hi
    exact Finset.card_pos.mp (by rw [hA I hi]; norm_num))
  have hcross := mean_chronological_annihilates 2 (by norm_num) t ht A c
    (quarticTarget (ι := ι) T) (by
      intro I hi
      rw [hA I hi]
      have hh := quarticTarget_degree (ι := ι) T
      omega)
  have halg : (chronologicalPolynomial A c - quarticTarget (ι := ι) T)^2 =
      chronologicalPolynomial A c * chronologicalPolynomial A c -
      (2:ℝ) • (chronologicalPolynomial A c * quarticTarget (ι := ι) T) +
      (quarticTarget (ι := ι) T)^2 := by
    simp only [Algebra.smul_def, map_ofNat]
    ring
  rw [halg, map_add, map_sub, map_smul, hgram, hcross,
    quarticTarget_square_mean t ht T hT hsum]
  simp



theorem value_quarticTarget (T : ℝ≥0) (x : ι → ℝ) :
    value (quarticTarget (ι := ι) T) x = (∑ i, (x i : ℂ))^4 + 24*((T:ℝ):ℂ) := by
  simp [quarticTarget, value, terminal]

def quarticResidual (A : Finset (Finset ι)) (c : Finset ι → ℝ) (T : ℝ≥0)
    (x : ι → ℝ) : ℂ := chronological A c x - ((∑ i, (x i : ℂ))^4 + 24*((T:ℝ):ℂ))

omit [Fintype ι] in
theorem value_pow (P : MvPolynomial ι ℝ) (n : ℕ) (x : ι → ℝ) :
    value (P^n) x = value P x ^ n := by simp [value]

omit [Fintype ι] in
theorem value_sub (P Q : MvPolynomial ι ℝ) (x : ι → ℝ) :
    value (P-Q) x = value P x - value Q x := by simp [value]

theorem value_residual_square (A : Finset (Finset ι)) (c : Finset ι → ℝ)
    (T : ℝ≥0) (x : ι → ℝ) :
    value ((chronologicalPolynomial A c - quarticTarget (ι := ι) T)^2) x =
      quarticResidual A c T x ^ 2 := by
  simp only [value_pow, value_sub, value_chronological, value_quarticTarget, quarticResidual]

theorem quartic_residual_square_integrable (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (A : Finset (Finset ι)) (c : Finset ι → ℝ) (T : ℝ≥0) :
    (incrementLaw 2 (by norm_num) t ht).Integrable (fun x => quarticResidual A c T x ^ 2) := by
  have he : value ((chronologicalPolynomial A c - quarticTarget (ι := ι) T)^2) =
      (fun x => quarticResidual A c T x ^ 2) := funext (value_residual_square A c T)
  rw [← he]
  exact polynomial_integrable 2 (by norm_num) t ht _

theorem quartic_residual_second_moment (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (T : ℝ≥0) (hT : 0 < T) (hsum : ∑ i, t i = T)
    (A : Finset (Finset ι)) (c : Finset ι → ℝ) (hA : ∀ I ∈ A, I.card = 4) :
    (∫ᵛ x, quarticResidual A c T x ^ 2 ∂<•incrementLaw 2 (by norm_num) t ht) =
      19584*((T:ℝ):ℂ)^2 := by
  have he := quartic_chronological_residual_mean t ht T hT hsum A c hA
  change (∫ᵛ x, value ((chronologicalPolynomial A c - quarticTarget (ι := ι) T)^2) x
    ∂<•incrementLaw 2 (by norm_num) t ht) = _ at he
  simpa only [value_residual_square] using he

open Filter in
theorem no_refining_signed_square_convergence (N : ℕ → ℕ)
    (t : ∀ n, Fin (N n) → ℝ≥0) (ht : ∀ n i, 0 < t n i)
    (T : ℝ≥0) (hT : 0 < T) (hsum : ∀ n, ∑ i, t n i = T)
    (A : ∀ n, Finset (Finset (Fin (N n)))) (c : ∀ n, Finset (Fin (N n)) → ℝ)
    (hA : ∀ n I, I ∈ A n → I.card = 4) :
    ¬ Tendsto (fun n => ∫ᵛ x, quarticResidual (A n) (c n) T x ^ 2
      ∂<•incrementLaw 2 (by norm_num) (t n) (ht n)) atTop (nhds 0) := by
  simp_rw [quartic_residual_second_moment _ _ T hT (hsum _) _ _ (hA _)]
  intro h
  have he := tendsto_nhds_unique h tendsto_const_nhds
  have hn : (19584:ℂ)*((T:ℝ):ℂ)^2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hT)))
  exact hn he.symm


end OperatorDerivativeRewrite.Foundation.HigherHeatMultivariateMoments
