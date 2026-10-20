import Foundation.RiemannQuarticPolynomialFactors
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! The actual multiplicity-weighted denominator product tends locally
uniformly to one. Its error is controlled by the actual closed-disk zero
mass, rather than an assumed summable list of zeros. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticDenominatorLimit
open RiemannQuarticFlow RiemannQuarticPolynomialFactors RiemannQuarticZeroCounting

theorem finite_power_product_bound (S : Finset ℂ) (n : ℂ → ℕ) (f : ℂ → ℂ) :
    ‖(∏ a ∈ S, (1+f a)^n a)-1‖ ≤ Real.exp (∑ a ∈ S, (n a : ℝ)*‖f a‖)-1 := by
  classical
  have hb := Finset.norm_prod_one_add_sub_one_le
    (S.sigma fun a => Finset.range (n a)) (fun q : Σ _ : ℂ, ℕ => f q.1)
  simpa only [Finset.prod_sigma,Finset.sum_sigma,Finset.prod_const,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul] using hb

theorem open_closed_divisor_eq (t R : ℝ) (a : ℂ) (ha : a ∈ ball (0 : ℂ) R) :
    divisor (flow t) (ball 0 R) a = divisor (flow t) (closedBall 0 R) a := by
  rw [(((flow_analytic t).mono (subset_univ (ball (0 : ℂ) R))).meromorphicOn).divisor_apply ha,
    (((flow_analytic t).mono (subset_univ (closedBall (0 : ℂ) R))).meromorphicOn).divisor_apply
      (ball_subset_closedBall ha)]

theorem positive_weighted_mass_le (t R : ℝ) (hR : 0 < R) :
    (∑ a ∈ positiveZeroSupport t R,
      ((divisor (flow t) (ball 0 R) a).toNat : ℝ)*‖a‖^2/R^4) ≤
      ∑ᶠ a : ℂ, (divisor (flow t) (closedBall 0 R) a : ℝ)*‖a‖^2/R^4 := by
  classical
  let d := divisor (flow t) (closedBall (0 : ℂ) R)
  let T := (d.finiteSupport (isCompact_closedBall ..)).toFinset
  have hn (a : ℂ) : 0 ≤ (d a : ℝ) := by
    exact_mod_cast ((flow_analytic t).mono (subset_univ _)).divisor_nonneg a
  have he (a : ℂ) (ha : a ∈ positiveZeroSupport t R) :
      ((divisor (flow t) (ball 0 R) a).toNat : ℝ) = (d a : ℝ) := by
    have hb := zeroSupport_mem_ball t R a (Finset.mem_filter.mp ha).1
    rw [show divisor (flow t) (ball 0 R) a = d a from open_closed_divisor_eq t R a hb]
    have hpos : 0 ≤ d a := ((flow_analytic t).mono (subset_univ _)).divisor_nonneg a
    exact_mod_cast (Int.toNat_of_nonneg hpos)
  have hsub : positiveZeroSupport t R ⊆ T := by
    intro a ha
    have hS := (Finset.mem_filter.mp ha).1
    have hb := zeroSupport_mem_ball t R a hS
    have hd := (mem_zeroSupport t R a).mp hS
    rw [open_closed_divisor_eq t R a hb] at hd
    simpa only [T,Set.Finite.mem_toFinset,Function.mem_support] using hd
  have hsum : (∑ᶠ a : ℂ, (d a : ℝ)*‖a‖^2/R^4) =
      ∑ a ∈ T, (d a : ℝ)*‖a‖^2/R^4 := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    change a ∈ (d.finiteSupport (isCompact_closedBall ..)).toFinset
    rw [Set.Finite.mem_toFinset]
    change d a ≠ 0
    intro hd
    simp only [Function.mem_support,hd,Int.cast_zero,zero_mul,zero_div,ne_eq,
      not_true_eq_false] at ha
  change _ ≤ ∑ᶠ a : ℂ, (d a : ℝ)*‖a‖^2/R^4
  rw [hsum]
  calc
    _ = ∑ a ∈ positiveZeroSupport t R, (d a : ℝ)*‖a‖^2/R^4 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [he a ha]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro a ha hnot
      exact div_nonneg (mul_nonneg (hn a) (sq_nonneg _)) (by positivity))

theorem denominator_error_bound (t R : ℝ) (hR : 0 < R)
    (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) (z : ℂ) :
    ‖denominatorProduct t R hreal z-1‖ ≤
      Real.exp (‖z‖^2*(∑ᶠ a : ℂ,
        (divisor (flow t) (closedBall 0 R) a : ℝ)*‖a‖^2/R^4))-1 := by
  have hb := finite_power_product_bound (positiveZeroSupport t R)
    (fun a => (divisor (flow t) (ball 0 R) a).toNat)
    (fun a => -(conj a^2*z^2/(R : ℂ)^4))
  simp only [← sub_eq_add_neg] at hb
  change ‖denominatorProduct t R hreal z-1‖ ≤ _ at hb
  refine hb.trans (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1)
  have hnorm (a : ℂ) : ‖-(conj a^2*z^2/(R : ℂ)^4)‖ = ‖a‖^2*‖z‖^2/R^4 := by
    simp only [norm_neg,norm_div,norm_mul,norm_pow,Complex.norm_conj,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hR]
  simp_rw [hnorm]
  calc
    _ = ‖z‖^2*(∑ a ∈ positiveZeroSupport t R,
        ((divisor (flow t) (ball 0 R) a).toNat : ℝ)*‖a‖^2/R^4) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (positive_weighted_mass_le t R hR) (sq_nonneg _)

theorem denominator_uniform_on_closedBall (t : ℝ)
    (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    TendstoUniformlyOn (fun R z => denominatorProduct t R hreal z) (fun _ => 1)
      atTop (closedBall (0 : ℂ) ρ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hm := weighted_zero_mass_tendsto_zero t
  have hlim : Tendsto (fun R : ℝ => Real.exp (ρ^2*(∑ᶠ a : ℂ,
      (divisor (flow t) (closedBall 0 R) a : ℝ)*‖a‖^2/R^4))-1) atTop (𝓝 0) := by
    have hc : Tendsto (fun R : ℝ => ρ^2*(∑ᶠ a : ℂ,
        (divisor (flow t) (closedBall 0 R) a : ℝ)*‖a‖^2/R^4)) atTop (𝓝 0) := by
      simpa using hm.const_mul (ρ^2)
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp hc).sub_const 1
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hlim.eventually (Iio_mem_nhds hε)] with R hR hsmall
  intro z hz
  have hRp : 0 < R := by linarith
  have hmass := (weighted_zero_mass_bound t R hRp).1
  have hnorm := mem_closedBall_zero_iff.mp hz
  have hb := denominator_error_bound t R hRp hreal z
  have hs : ‖z‖^2 ≤ ρ^2 := by nlinarith [norm_nonneg z]
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs hmass)
  have hfinal : ‖denominatorProduct t R hreal z-1‖ < ε := by linarith
  simpa only [dist_eq_norm,norm_sub_rev] using hfinal

theorem denominator_locally_uniform (t : ℝ)
    (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0) :
    TendstoLocallyUniformly (fun R z => denominatorProduct t R hreal z) (fun _ => 1) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  exact (denominator_uniform_on_closedBall t hreal ρ hρ.le).mono hsub

theorem denominator_locally_uniform_along {ι : Type*} {p : Filter ι}
    (t : ℝ) (hreal : ∀ z : ℂ, flow t z = 0 → z.im = 0)
    (r : ι → ℝ) (hr : Tendsto r p atTop) :
    TendstoLocallyUniformly (fun i z => denominatorProduct t (r i) hreal z) (fun _ => 1) p := by
  intro u hu x
  obtain ⟨s,hs,h⟩ := denominator_locally_uniform t hreal u hu x
  exact ⟨s,hs,hr.eventually h⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticDenominatorLimit
