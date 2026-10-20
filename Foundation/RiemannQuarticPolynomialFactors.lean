import Foundation.RiemannQuarticCanonicalPairs
import Mathlib.Algebra.Polynomial.Splits

/-! Actual finite divisor support and normalized real split-polynomial
factors. The real-zero hypothesis is required to identify these with the
canonical factors; it is not assumed at arbitrary times. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn Polynomial
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticPolynomialFactors
open RiemannQuarticFlow RiemannQuarticZeroCounting RiemannQuarticCanonicalDerivative

def zeroSupport (t R : ℝ) : Finset ℂ :=
  (MeromorphicOn.divisor_ball_support_finite
    (((flow_analytic t).mono (subset_univ (closedBall (0 : ℂ) R))).meromorphicOn)).toFinset

theorem mem_zeroSupport (t R : ℝ) (a : ℂ) :
    a ∈ zeroSupport t R ↔ divisor (flow t) (ball 0 R) a ≠ 0 := by
  simp only [zeroSupport,Set.Finite.mem_toFinset,Function.mem_support]

theorem zeroSupport_mem_ball (t R : ℝ) (a : ℂ) (ha : a ∈ zeroSupport t R) :
    a ∈ ball (0 : ℂ) R :=
  (divisor (flow t) (ball 0 R)).supportWithinDomain ((mem_zeroSupport t R a).mp ha)

theorem zeroSupport_ne_zero (t R : ℝ) (a : ℂ) (ha : a ∈ zeroSupport t R) : a ≠ 0 := by
  intro he
  subst a
  exact (mem_zeroSupport t R 0).mp ha (ball_divisor_zero_at_origin t R)

theorem zeroSupport_neg (t R : ℝ) (a : ℂ) :
    -a ∈ zeroSupport t R ↔ a ∈ zeroSupport t R := by
  rw [mem_zeroSupport,mem_zeroSupport,ball_divisor_neg]

theorem zeroSupport_is_zero (t R : ℝ) (a : ℂ) (ha : a ∈ zeroSupport t R) : flow t a = 0 := by
  have he := ((flow_analytic t).mono (subset_univ (ball (0 : ℂ) R))).meromorphicNFOn
    |>.zero_set_eq_divisor_support (fun z => flow_zero_order_finite t z)
  have hm : a ∈ Function.support (divisor (flow t) (ball 0 R)) := (mem_zeroSupport t R a).mp ha
  rw [← he] at hm
  exact hm.2

def positiveZeroSupport (t R : ℝ) : Finset ℂ := (zeroSupport t R).filter fun a => 0 < a.re

def pairPolynomial (a : ℝ) : ℝ[X] := C (-1/a^2) * ((X-C a)*(X+C a))

theorem pairPolynomial_splits (a : ℝ) : (pairPolynomial a).Splits := by
  exact ((Splits.X_sub_C a).mul (Splits.X_add_C a)).C_mul (-1/a^2)

theorem pairPolynomial_eval_zero (a : ℝ) (ha : a ≠ 0) : (pairPolynomial a).eval 0 = 1 := by
  simp only [pairPolynomial,eval_mul,eval_C,eval_sub,eval_X,eval_add,zero_sub,zero_add]
  field_simp

theorem pairPolynomial_complex_eval (a : ℝ) (ha : a ≠ 0) (z : ℂ) :
    ((pairPolynomial a).map (algebraMap ℝ ℂ)).eval z = 1-z^2/(a : ℂ)^2 := by
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  simp only [pairPolynomial,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_sub,
    Polynomial.map_X,Polynomial.map_add,eval_mul,eval_C,eval_sub,eval_X,eval_add]
  push_cast
  field_simp [hac]
  ring_nf <;> rfl

def numeratorPoly (t R : ℝ) (_hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) : ℝ[X] :=
  ∏ a ∈ positiveZeroSupport t R,
    pairPolynomial a.re ^ (divisor (flow t) (ball 0 R) a).toNat

theorem numeratorPoly_splits (t R : ℝ) (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) :
    (numeratorPoly t R hreal).Splits := by
  exact Splits.prod fun a ha => (pairPolynomial_splits a.re).pow _

theorem numeratorPoly_eval_zero (t R : ℝ) (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) :
    (numeratorPoly t R hreal).eval 0 = 1 := by
  simp only [numeratorPoly,eval_prod,eval_pow]
  apply Finset.prod_eq_one
  intro a ha
  have hp : 0 < a.re := (Finset.mem_filter.mp ha).2
  rw [pairPolynomial_eval_zero a.re hp.ne',one_pow]

def denominatorProduct (t R : ℝ) (_hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) (z : ℂ) : ℂ :=
  ∏ a ∈ positiveZeroSupport t R,
    (1-conj a^2*z^2/(R : ℂ)^4) ^ (divisor (flow t) (ball 0 R) a).toNat

theorem numeratorPoly_complex_eval (t R : ℝ)
    (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) (z : ℂ) :
    ((numeratorPoly t R hreal).map (algebraMap ℝ ℂ)).eval z =
      ∏ a ∈ positiveZeroSupport t R,
        (1-z^2/a^2) ^ (divisor (flow t) (ball 0 R) a).toNat := by
  simp only [numeratorPoly,Polynomial.map_prod,Polynomial.map_pow,eval_prod,eval_pow]
  apply Finset.prod_congr rfl
  intro a ha
  have haS : a ∈ zeroSupport t R := (Finset.mem_filter.mp ha).1
  have hp : 0 < a.re := (Finset.mem_filter.mp ha).2
  have him : a.im = 0 := hreal a (zeroSupport_is_zero t R a haS)
  have hac : (a.re : ℂ) = a := by apply Complex.ext <;> simp [him]
  rw [pairPolynomial_complex_eval a.re hp.ne' z,hac]

theorem inverseZeroProduct_finset (t R : ℝ) (z : ℂ) :
    RiemannQuarticCanonicalReconstruction.inverseZeroProduct t R z =
      ∏ a ∈ zeroSupport t R,
        (canonicalFactor R a z)⁻¹ ^ (divisor (flow t) (ball 0 R) a).toNat := by
  rw [RiemannQuarticCanonicalReconstruction.inverseZeroProduct_apply]
  have he : (∏ᶠ a : ℂ, canonicalFactor R a z ^ (-divisor (flow t) (ball 0 R) a)) =
      ∏ a ∈ zeroSupport t R, canonicalFactor R a z ^ (-divisor (flow t) (ball 0 R) a) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro a ha
    apply (mem_zeroSupport t R a).mpr
    intro hd
    simp only [Function.mem_mulSupport,hd,neg_zero,zpow_zero,ne_eq,not_true_eq_false] at ha
  rw [he]
  apply Finset.prod_congr rfl
  intro a ha
  have hn : 0 ≤ divisor (flow t) (ball 0 R) a :=
    ((flow_analytic t).mono (subset_univ (ball (0 : ℂ) R))).divisor_nonneg a
  calc
    _ = canonicalFactor R a z ^ (-((divisor (flow t) (ball 0 R) a).toNat : ℤ)) := by
      rw [Int.toNat_of_nonneg hn]
    _ = _ := by simp only [zpow_neg,zpow_natCast,inv_pow]

theorem inverseZeroProduct_pairs (t R : ℝ)
    (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) (z : ℂ) :
    RiemannQuarticCanonicalReconstruction.inverseZeroProduct t R z =
      ∏ a ∈ positiveZeroSupport t R,
        ((canonicalFactor R a z)⁻¹*(canonicalFactor R (-a) z)⁻¹) ^
          (divisor (flow t) (ball 0 R) a).toNat := by
  rw [inverseZeroProduct_finset]
  rw [RiemannQuarticCanonicalPairs.opposite_finite_product (zeroSupport t R)
    (fun a => (canonicalFactor R a z)⁻¹ ^ (divisor (flow t) (ball 0 R) a).toNat)
    (fun a ha => (zeroSupport_neg t R a).mpr ha)
    (zeroSupport_ne_zero t R)
    (fun a ha => hreal a (zeroSupport_is_zero t R a ha))]
  apply Finset.prod_congr rfl
  intro a ha
  rw [ball_divisor_neg,← mul_pow]

theorem denominatorProduct_ne_zero (t R : ℝ) (hR : 0 < R)
    (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) R) : denominatorProduct t R hreal z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  have haS := (Finset.mem_filter.mp ha).1
  exact pow_ne_zero _ (RiemannQuarticCanonicalPairs.paired_denominator_ne_zero R hR a z
    (zeroSupport_mem_ball t R a haS) hz)

theorem normalized_inverse_product_eq (t R : ℝ) (hR : 0 < R)
    (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) R) :
    RiemannQuarticCanonicalReconstruction.inverseZeroProduct t R z /
      RiemannQuarticCanonicalReconstruction.inverseZeroProduct t R 0 =
      ((numeratorPoly t R hreal).map (algebraMap ℝ ℂ)).eval z / denominatorProduct t R hreal z := by
  let n := fun a : ℂ => (divisor (flow t) (ball 0 R) a).toNat
  calc
    _ = (∏ a ∈ positiveZeroSupport t R,
        (((canonicalFactor R a z)⁻¹*(canonicalFactor R (-a) z)⁻¹)^n a) /
          (((canonicalFactor R a 0)⁻¹*(canonicalFactor R (-a) 0)⁻¹)^n a)) := by
      rw [inverseZeroProduct_pairs t R hreal z,inverseZeroProduct_pairs t R hreal 0]
      rw [Finset.prod_div_distrib]
    _ = ∏ a ∈ positiveZeroSupport t R, (1-z^2/a^2)^n a / (1-conj a^2*z^2/(R : ℂ)^4)^n a := by
      apply Finset.prod_congr rfl
      intro a ha
      have haS := (Finset.mem_filter.mp ha).1
      rw [← div_pow,RiemannQuarticCanonicalPairs.normalized_reciprocal_pair R hR a z
        (zeroSupport_ne_zero t R a haS) (zeroSupport_mem_ball t R a haS) hz,div_pow]
    _ = _ := by
      rw [Finset.prod_div_distrib,numeratorPoly_complex_eval]
      rfl

theorem numerator_reconstruction (t R : ℝ) (hR : 0 < R)
    (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) R) :
    ((numeratorPoly t R hreal).map (algebraMap ℝ ℂ)).eval z = denominatorProduct t R hreal z *
      (RiemannQuarticCanonicalReconstruction.inverseZeroProduct t R z /
        RiemannQuarticCanonicalReconstruction.inverseZeroProduct t R 0) := by
  have he := (eq_div_iff (denominatorProduct_ne_zero t R hR hreal z hz)).mp
    (normalized_inverse_product_eq t R hR hreal z hz)
  simpa only [mul_comm] using he.symm

theorem eventually_actual_split_factorization :
    ∀ᶠ t : ℝ in atTop, ∀ R : ℝ, 0 < R → ∃ P : ℝ[X], ∃ D : ℂ → ℂ,
      P.Splits ∧ P.eval 0 = 1 ∧ D 0 = 1 ∧
      (∀ z ∈ closedBall (0 : ℂ) R, D z ≠ 0) ∧
      ∀ z ∈ closedBall (0 : ℂ) R, (P.map (algebraMap ℝ ℂ)).eval z = D z *
        (RiemannQuarticCanonicalReconstruction.inverseZeroProduct t R z /
          RiemannQuarticCanonicalReconstruction.inverseZeroProduct t R 0) := by
  filter_upwards [RiemannQuarticUniformFarScale.eventually_all_zeros_real] with t hreal
  intro R hR
  exact ⟨numeratorPoly t R hreal,denominatorProduct t R hreal,numeratorPoly_splits t R hreal,
    numeratorPoly_eval_zero t R hreal,by simp [denominatorProduct],
    fun z hz => denominatorProduct_ne_zero t R hR hreal z hz,
    fun z hz => numerator_reconstruction t R hR hreal z hz⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticPolynomialFactors
