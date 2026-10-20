import Foundation.RiemannQuarticCanonicalProductLimit

/-! Opposite canonical factors and finite pairing of nonzero real roots.
The complex algebra is checked before a real-root hypothesis is used. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalPairs
open RiemannQuarticCanonicalReconstruction

theorem paired_denominator_ne_zero (R : ℝ) (hR : 0 < R) (a z : ℂ)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ closedBall (0 : ℂ) R) :
    1-conj a^2*z^2/(R : ℂ)^4 ≠ 0 := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hN := canonical_numerator_ne_zero R a z ha hz
  have hneg : -a ∈ ball (0 : ℂ) R := by simpa using ha
  have hM := canonical_numerator_ne_zero R (-a) z hneg hz
  simp only [map_neg,neg_mul,sub_neg_eq_add] at hM
  have he : 1-conj a^2*z^2/(R : ℂ)^4 =
      (((R : ℂ)^2-conj a*z)*((R : ℂ)^2+conj a*z))/(R : ℂ)^4 := by
    field_simp
    ring
  rw [he]
  exact div_ne_zero (mul_ne_zero hN hM) (pow_ne_zero 4 hRc)

theorem normalized_reciprocal_pair (R : ℝ) (hR : 0 < R) (a z : ℂ)
    (ha0 : a ≠ 0) (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ closedBall (0 : ℂ) R) :
    ((canonicalFactor R a z)⁻¹*(canonicalFactor R (-a) z)⁻¹) /
      ((canonicalFactor R a 0)⁻¹*(canonicalFactor R (-a) 0)⁻¹) =
      (1-z^2/a^2)/(1-conj a^2*z^2/(R : ℂ)^4) := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hneg : -a ∈ ball (0 : ℂ) R := by simpa using ha
  have hN := canonical_numerator_ne_zero R a z ha hz
  have hM := canonical_numerator_ne_zero R (-a) z hneg hz
  have hD := paired_denominator_ne_zero R hR a z ha hz
  simp only [map_neg,neg_mul,sub_neg_eq_add] at hM
  have hK : (R : ℂ)^4-conj a^2*z^2 ≠ 0 := by
    convert mul_ne_zero hN hM using 1 <;> ring
  have hKn : -(z^2*conj a^2)+(R : ℂ)^4 ≠ 0 := by
    convert hK using 1 <;> ring
  apply (eq_div_iff hD).mpr
  simp only [canonical_reciprocal_eq,map_neg,neg_mul,sub_neg_eq_add,mul_zero,sub_zero,zero_sub]
  field_simp [hRc,ha0,hN,hM,hK,hKn] <;> ring_nf <;> field_simp [hKn] <;> ring

theorem opposite_finite_product (S : Finset ℂ) (f : ℂ → ℂ)
    (hneg : ∀ a ∈ S, -a ∈ S) (hzero : ∀ a ∈ S, a ≠ 0)
    (hreal : ∀ a ∈ S, a.im = 0) :
    (∏ a ∈ S, f a) = ∏ a ∈ S with 0 < a.re, f a*f (-a) := by
  classical
  have hre (a : ℂ) (ha : a ∈ S) : a.re ≠ 0 := by
    intro hr
    apply hzero a ha
    apply Complex.ext <;> simp [hr,hreal a ha]
  have he : (∏ a ∈ S with ¬0 < a.re, f a) = ∏ a ∈ S with 0 < a.re, f (-a) := by
    symm
    apply Finset.prod_bij (fun a _ => -a)
    · intro a ha
      obtain ⟨haS,haP⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      exact ⟨hneg a haS,by simp only [neg_re]; linarith⟩
    · intro a ha b hb hab
      exact neg_injective hab
    · intro b hb
      obtain ⟨hbS,hbP⟩ := Finset.mem_filter.mp hb
      have hbr : b.re < 0 := lt_of_le_of_ne (le_of_not_gt hbP) (hre b hbS)
      refine ⟨-b,Finset.mem_filter.mpr ⟨hneg b hbS,?_⟩,by simp⟩
      simpa only [neg_re] using neg_pos.mpr hbr
    · intro a ha
      rfl
  calc
    _ = (∏ a ∈ S with 0 < a.re, f a)*(∏ a ∈ S with ¬0 < a.re, f a) :=
      (Finset.prod_filter_mul_prod_filter_not S (fun a : ℂ => 0 < a.re) f).symm
    _ = _ := by rw [he,← Finset.prod_mul_distrib]

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalPairs
