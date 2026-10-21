import Foundation.EvenEntireCanonicalApproximation
import Foundation.RiemannQuarticDenominatorLimit
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Canonical real-polynomial approximation for even entire functions of
subquadratic growth. Finite polynomials retain all actual disk zeros, including
nonreal and imaginary-axis zeros; no all-real or simple-zero hypothesis is used.
Convergence is compact-uniform, not yet Gaussian heat-domain convergence. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn Polynomial
open scoped Topology ComplexConjugate
attribute [local instance] Classical.propDecidable
namespace OperatorDerivativeRewrite.Foundation.EvenEntirePolynomialApproximation
open EvenEntireCanonicalDerivative EvenEntireCanonicalApproximation

def positiveHalf (a : ℂ) : Prop := 0<a.re ∨ a.re=0 ∧ 0<a.im

theorem positiveHalf_neg (a : ℂ) (ha : a≠0) : positiveHalf (-a) ↔ ¬positiveHalf a := by
  have hne : a.re≠0 ∨ a.im≠0 := by
    by_contra h
    push Not at h
    exact ha (Complex.ext h.1 h.2)
  simp only [positiveHalf,neg_re,neg_im]
  constructor
  · rintro (h | ⟨hr,hi⟩) (h' | ⟨hr',hi'⟩) <;> linarith
  · intro h
    by_cases hr : a.re=0
    · right
      have hi : a.im≠0 := hne.resolve_left (not_not.mpr hr)
      refine ⟨by linarith,?_⟩
      have hn : ¬0<a.im := fun hp => h (Or.inr ⟨hr,hp⟩)
      have hh := lt_of_le_of_ne (le_of_not_gt hn) hi
      linarith
    · left
      have hn : ¬0<a.re := fun hp => h (Or.inl hp)
      have hh := lt_of_le_of_ne (le_of_not_gt hn) hr
      linarith

theorem opposite_finite_product {M : Type*} [CommMonoid M] (S : Finset ℂ) (F : ℂ → M)
    (hneg : ∀ a∈S, -a∈S) (hzero : ∀ a∈S, a≠0) :
    (∏ a∈S, F a)=∏ a∈S with positiveHalf a, F a*F (-a) := by
  classical
  have he : (∏ a∈S with ¬positiveHalf a, F a)=
      ∏ a∈S with positiveHalf a, F (-a) := by
    symm
    apply Finset.prod_bij (fun a _ => -a)
    · intro a ha
      obtain ⟨haS,haP⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hneg a haS,by
        rw [positiveHalf_neg a (hzero a haS)]
        exact not_not.mpr haP⟩
    · intro a ha b hb hab
      exact neg_injective hab
    · intro b hb
      obtain ⟨hbS,hbP⟩ := Finset.mem_filter.mp hb
      exact ⟨-b,Finset.mem_filter.mpr ⟨hneg b hbS,
        (positiveHalf_neg b (hzero b hbS)).mpr hbP⟩,by simp⟩
    · intro a ha
      rfl
  calc
    _=(∏ a∈S with positiveHalf a,F a)*(∏ a∈S with ¬positiveHalf a,F a) :=
      (Finset.prod_filter_mul_prod_filter_not S positiveHalf F).symm
    _=_ := by rw [he,← Finset.prod_mul_distrib]

variable (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
  (h0 : f 0≠0) (heven : ∀ z : ℂ,f (-z)=f z)

def zeroSupport (R : ℝ) : Finset ℂ :=
  (MeromorphicOn.divisor_ball_support_finite
    ((hf.mono (subset_univ (closedBall (0:ℂ) R))).meromorphicOn)).toFinset

theorem mem_zeroSupport (R : ℝ) (a : ℂ) :
    a∈zeroSupport f hf R ↔ divisor f (ball 0 R) a≠0 := by
  simp only [zeroSupport,Set.Finite.mem_toFinset,Function.mem_support]

theorem zeroSupport_mem_ball (R : ℝ) (a : ℂ) (haS : a∈zeroSupport f hf R) :
    a∈ball (0:ℂ) R :=
  (divisor f (ball 0 R)).supportWithinDomain ((mem_zeroSupport f hf R a).mp haS)

include h0 in
theorem zeroSupport_ne_zero (R : ℝ) (a : ℂ) (haS : a∈zeroSupport f hf R) : a≠0 := by
  intro he
  subst a
  exact (mem_zeroSupport f hf R 0).mp haS (ball_divisor_zero_at_origin f hf h0 R)

include heven in
theorem zeroSupport_neg (R : ℝ) (a : ℂ) :
    -a∈zeroSupport f hf R ↔ a∈zeroSupport f hf R := by
  rw [mem_zeroSupport,mem_zeroSupport,ball_divisor_neg f hf heven]

def halfZeroSupport (R : ℝ) : Finset ℂ := (zeroSupport f hf R).filter positiveHalf

def numeratorPoly (R : ℝ) : ℂ[X] :=
  ∏ a∈halfZeroSupport f hf R,
    (1-C (1/a^2)*X^2)^(divisor f (ball 0 R) a).toNat

def denominatorProduct (R : ℝ) (z : ℂ) : ℂ :=
  ∏ a∈halfZeroSupport f hf R,
    (1-conj a^2*z^2/(R:ℂ)^4)^(divisor f (ball 0 R) a).toNat

theorem numeratorPoly_eval (R : ℝ) (z : ℂ) :
    (numeratorPoly f hf R).eval z=
      ∏ a∈halfZeroSupport f hf R, (1-z^2/a^2)^(divisor f (ball 0 R) a).toNat := by
  simp only [numeratorPoly,eval_prod,eval_pow,eval_sub,eval_one,eval_mul,eval_C,eval_X]
  congr 1
  ext a
  ring

theorem numeratorPoly_origin (R : ℝ) : (numeratorPoly f hf R).eval 0=1 := by
  simp [numeratorPoly_eval]

theorem numeratorPoly_even (R : ℝ) (z : ℂ) :
    (numeratorPoly f hf R).eval (-z)=(numeratorPoly f hf R).eval z := by
  simp only [numeratorPoly_eval,neg_sq]

theorem inverseZeroProduct_finset (R : ℝ) (z : ℂ) :
    inverseZeroProduct f R z=∏ a∈zeroSupport f hf R,
      (canonicalFactor R a z)⁻¹^(divisor f (ball 0 R) a).toNat := by
  rw [inverseZeroProduct_apply f hf]
  have he : (∏ᶠ a : ℂ,canonicalFactor R a z^(-divisor f (ball 0 R) a))=
      ∏ a∈zeroSupport f hf R,canonicalFactor R a z^(-divisor f (ball 0 R) a) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro a haM
    apply (mem_zeroSupport f hf R a).mpr
    intro hd
    simp only [Function.mem_mulSupport,hd,neg_zero,zpow_zero,ne_eq,not_true_eq_false] at haM
  rw [he]
  apply Finset.prod_congr rfl
  intro a haS
  have hn : 0≤divisor f (ball 0 R) a := (hf.mono (subset_univ _)).divisor_nonneg a
  calc
    _=canonicalFactor R a z^(-((divisor f (ball 0 R) a).toNat:ℤ)) := by
      rw [Int.toNat_of_nonneg hn]
    _=_ := by simp only [zpow_neg,zpow_natCast,inv_pow]

include h0 heven in
theorem inverseZeroProduct_pairs (R : ℝ) (z : ℂ) :
    inverseZeroProduct f R z=∏ a∈halfZeroSupport f hf R,
      ((canonicalFactor R a z)⁻¹*(canonicalFactor R (-a) z)⁻¹)^
        (divisor f (ball 0 R) a).toNat := by
  rw [inverseZeroProduct_finset f hf]
  rw [opposite_finite_product (zeroSupport f hf R)
    (fun a => (canonicalFactor R a z)⁻¹^(divisor f (ball 0 R) a).toNat)
    (fun a haS => (zeroSupport_neg f hf heven R a).mpr haS)
    (zeroSupport_ne_zero f hf h0 R)]
  apply Finset.prod_congr rfl
  intro a haS
  rw [ball_divisor_neg f hf heven,← mul_pow]

theorem denominatorProduct_ne_zero (R : ℝ) (hR : 0<R) (z : ℂ)
    (hz : z∈closedBall (0:ℂ) R) : denominatorProduct f hf R z≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a haS
  exact pow_ne_zero _ (RiemannQuarticCanonicalPairs.paired_denominator_ne_zero R hR a z
    (zeroSupport_mem_ball f hf R a (Finset.mem_filter.mp haS).1) hz)

include h0 heven in
theorem numerator_reconstruction (R : ℝ) (hR : 0<R) (z : ℂ)
    (hz : z∈closedBall (0:ℂ) R) :
    (numeratorPoly f hf R).eval z=denominatorProduct f hf R z*
      (inverseZeroProduct f R z/inverseZeroProduct f R 0) := by
  have he : inverseZeroProduct f R z/inverseZeroProduct f R 0=
      (numeratorPoly f hf R).eval z/denominatorProduct f hf R z := by
    rw [inverseZeroProduct_pairs f hf h0 heven R z,
      inverseZeroProduct_pairs f hf h0 heven R 0,← Finset.prod_div_distrib]
    rw [numeratorPoly_eval,denominatorProduct,← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro a haS
    have haS' := (Finset.mem_filter.mp haS).1
    rw [← div_pow,RiemannQuarticCanonicalPairs.normalized_reciprocal_pair R hR a z
      (zeroSupport_ne_zero f hf h0 R a haS') (zeroSupport_mem_ball f hf R a haS') hz,
      div_pow]
  have hh := (eq_div_iff (denominatorProduct_ne_zero f hf R hR z hz)).mp he
  simpa only [mul_comm] using hh.symm

include hf in
theorem open_closed_divisor_eq (R : ℝ) (a : ℂ) (ha : a ∈ ball (0 : ℂ) R) :
    divisor f (ball 0 R) a = divisor f (closedBall 0 R) a := by
  rw [((hf.mono (subset_univ (ball (0 : ℂ) R))).meromorphicOn).divisor_apply ha,
    ((hf.mono (subset_univ (closedBall (0 : ℂ) R))).meromorphicOn).divisor_apply
      (ball_subset_closedBall ha)]

theorem half_weighted_mass_le (R : ℝ) (hR : 0 < R) :
    (∑ a ∈ halfZeroSupport f hf R,
      ((divisor f (ball 0 R) a).toNat : ℝ)*‖a‖^2/R^4) ≤
      ∑ᶠ a : ℂ, (divisor f (closedBall 0 R) a : ℝ)*‖a‖^2/R^4 := by
  classical
  let d := divisor f (closedBall (0 : ℂ) R)
  let T := (d.finiteSupport (isCompact_closedBall ..)).toFinset
  have hn (a : ℂ) : 0 ≤ (d a : ℝ) := by
    exact_mod_cast (hf.mono (subset_univ _)).divisor_nonneg a
  have he (a : ℂ) (ha : a ∈ halfZeroSupport f hf R) :
      ((divisor f (ball 0 R) a).toNat : ℝ) = (d a : ℝ) := by
    have hb := zeroSupport_mem_ball f hf R a (Finset.mem_filter.mp ha).1
    rw [show divisor f (ball 0 R) a = d a from open_closed_divisor_eq f hf R a hb]
    have hpos : 0 ≤ d a := (hf.mono (subset_univ _)).divisor_nonneg a
    exact_mod_cast (Int.toNat_of_nonneg hpos)
  have hsub : halfZeroSupport f hf R ⊆ T := by
    intro a ha
    have hS := (Finset.mem_filter.mp ha).1
    have hb := zeroSupport_mem_ball f hf R a hS
    have hd := (mem_zeroSupport f hf R a).mp hS
    rw [open_closed_divisor_eq f hf R a hb] at hd
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
    _ = ∑ a ∈ halfZeroSupport f hf R, (d a : ℝ)*‖a‖^2/R^4 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [he a ha]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro a ha hnot
      exact div_nonneg (mul_nonneg (hn a) (sq_nonneg _)) (by positivity))

theorem denominator_error_bound (R : ℝ) (hR : 0 < R)
    (z : ℂ) :
    ‖denominatorProduct f hf R z-1‖ ≤
      Real.exp (‖z‖^2*(∑ᶠ a : ℂ,
        (divisor f (closedBall 0 R) a : ℝ)*‖a‖^2/R^4))-1 := by
  have hb := RiemannQuarticDenominatorLimit.finite_power_product_bound (halfZeroSupport f hf R)
    (fun a => (divisor f (ball 0 R) a).toNat)
    (fun a => -(conj a^2*z^2/(R : ℂ)^4))
  simp only [← sub_eq_add_neg] at hb
  change ‖denominatorProduct f hf R z-1‖ ≤ _ at hb
  refine hb.trans (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1)
  have hnorm (a : ℂ) : ‖-(conj a^2*z^2/(R : ℂ)^4)‖ = ‖a‖^2*‖z‖^2/R^4 := by
    simp only [norm_neg,norm_div,norm_mul,norm_pow,Complex.norm_conj,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hR]
  simp_rw [hnorm]
  calc
    _ = ‖z‖^2*(∑ a ∈ halfZeroSupport f hf R,
        ((divisor f (ball 0 R) a).toNat : ℝ)*‖a‖^2/R^4) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (half_weighted_mass_le f hf R hR) (sq_nonneg _)

variable (hgrowth : ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, ‖f z‖≤C*Real.exp (‖z‖*Real.sqrt ‖z‖))

include h0 hgrowth in
theorem denominator_uniform_on_closedBall 
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    TendstoUniformlyOn (fun R z => denominatorProduct f hf R z) (fun _ => 1)
      atTop (closedBall (0 : ℂ) ρ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hm := EntireSubquadraticZeroCounting.weighted_zero_mass_tendsto_zero f hf h0 hgrowth
  have hlim : Tendsto (fun R : ℝ => Real.exp (ρ^2*(∑ᶠ a : ℂ,
      (divisor f (closedBall 0 R) a : ℝ)*‖a‖^2/R^4))-1) atTop (𝓝 0) := by
    have hc : Tendsto (fun R : ℝ => ρ^2*(∑ᶠ a : ℂ,
        (divisor f (closedBall 0 R) a : ℝ)*‖a‖^2/R^4)) atTop (𝓝 0) := by
      simpa using hm.const_mul (ρ^2)
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp hc).sub_const 1
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hlim.eventually (Iio_mem_nhds hε)] with R hR hsmall
  intro z hz
  have hRp : 0 < R := by linarith
  have hmass := (EntireSubquadraticZeroCounting.weighted_zero_mass_bound f hf R hRp).1
  have hnorm := mem_closedBall_zero_iff.mp hz
  have hb := denominator_error_bound f hf R hRp z
  have hs : ‖z‖^2 ≤ ρ^2 := by nlinarith [norm_nonneg z]
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs hmass)
  have hfinal : ‖denominatorProduct f hf R z-1‖ < ε := by linarith
  simpa only [dist_eq_norm,norm_sub_rev] using hfinal

include h0 hgrowth in
theorem denominator_locally_uniform 
    :
    TendstoLocallyUniformly (fun R z => denominatorProduct f hf R z) (fun _ => 1) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  exact (denominator_uniform_on_closedBall f hf h0 hgrowth ρ hρ.le).mono hsub

include h0 hgrowth in
theorem denominator_locally_uniform_along {ι : Type*} {p : Filter ι}
    (r : ι → ℝ) (hr : Tendsto r p atTop) :
    TendstoLocallyUniformly (fun i z => denominatorProduct f hf (r i) z) (fun _ => 1) p := by
  intro u hu x
  obtain ⟨s,hs,h⟩ := denominator_locally_uniform f hf h0 hgrowth u hu x
  exact ⟨s,hs,hr.eventually h⟩


include h0 heven hgrowth in
theorem exists_polynomial_approximation :
    ∃ r : ℝ → ℝ, Tendsto r atTop atTop ∧
      (∀ R : ℝ, 1≤R → 2*R<r R ∧ r R<2*R+1) ∧
      TendstoLocallyUniformly
        (fun R z => f 0*(numeratorPoly f hf (r R)).eval z) f atTop := by
  obtain ⟨r,h,hdata,hB,hscale⟩ :=
    EvenEntireCanonicalApproximation.exists_product_approximation f hf h0 heven hgrowth
  have hr : Tendsto r atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨max 1 b,?_⟩
    intro R hR
    have hR1 : 1≤R := (le_max_left _ _).trans hR
    linarith [(hdata R hR1).1,(le_max_right 1 b).trans hR]
  have hD := denominator_locally_uniform_along f hf h0 hgrowth r hr
  have hmul : TendstoLocallyUniformly (fun R z => denominatorProduct f hf (r R) z*
      (f 0*(inverseZeroProduct f (r R) z/inverseZeroProduct f (r R) 0))) f atTop := by
    have hd : Differentiable ℂ f := fun z => (hf z (mem_univ _)).differentiableAt
    have hh := hD.mul₀ hscale continuous_const hd.continuous
    have he : (fun _ : ℂ => (1:ℂ))*f=f := by funext z; simp
    rw [he] at hh
    exact hh
  refine ⟨r,hr,fun R hR => ⟨(hdata R hR).1,(hdata R hR).2.1⟩,?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0:ℂ)
  apply (tendstoLocallyUniformly_iff_forall_isCompact.mp hmul K hK).congr
  filter_upwards [eventually_ge_atTop (max 1 (ρ+1))] with R hR
  have hR1 : 1≤R := (le_max_left _ _).trans hR
  intro z hz
  have hzr : z∈closedBall (0:ℂ) (r R) := mem_closedBall_zero_iff.mpr (by
    have hn := mem_closedBall_zero_iff.mp (hsub hz)
    linarith [(hdata R hR1).1,(le_max_right 1 (ρ+1)).trans hR])
  have hrp : 0<r R := by linarith [(hdata R hR1).1]
  dsimp only
  rw [numerator_reconstruction f hf h0 heven (r R) hrp z hzr]
  ring


variable (hconj : ∀ z : ℂ,f (conj z)=conj (f z))

theorem deriv_conj_of_real (F : ℂ → ℂ) (hF : ∀ z : ℂ,F (conj z)=conj (F z))
    (z : ℂ) : deriv F (conj z)=conj (deriv F z) := by
  have he : conj ∘ F ∘ conj=F := by
    funext w
    simp only [Function.comp_apply,hF,Complex.conj_conj]
  have hd := congrArg (fun G : ℂ → ℂ => deriv G (conj z)) he
  rw [deriv_conj_conj] at hd
  simpa only [Function.comp_apply,Complex.conj_conj] using hd.symm

include hconj in
theorem iteratedDeriv_conj (n : ℕ) (z : ℂ) :
    iteratedDeriv n f (conj z)=conj (iteratedDeriv n f z) := by
  induction n generalizing z with
  | zero => simpa only [iteratedDeriv_zero] using hconj z
  | succ n ih =>
    simpa only [iteratedDeriv_succ] using deriv_conj_of_real (iteratedDeriv n f) ih z

include hf hconj in
theorem order_conj (z : ℂ) : meromorphicOrderAt f (conj z)=meromorphicOrderAt f z := by
  rw [(hf (conj z) (mem_univ _)).meromorphicOrderAt_eq,
    (hf z (mem_univ _)).meromorphicOrderAt_eq]
  congr 1
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf (conj z) (mem_univ _)),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf z (mem_univ _))]
  simp only [iteratedDeriv_conj f hconj,map_eq_zero]

include hf hconj in
theorem ball_divisor_conj (R : ℝ) (z : ℂ) :
    divisor f (ball 0 R) (conj z)=divisor f (ball 0 R) z := by
  have ha := hf.mono (subset_univ (ball (0:ℂ) R))
  by_cases hz : z∈ball (0:ℂ) R
  · have hc : conj z∈ball (0:ℂ) R := by
      simpa only [mem_ball_zero_iff,Complex.norm_conj] using hz
    rw [ha.meromorphicOn.divisor_apply hc,ha.meromorphicOn.divisor_apply hz,
      order_conj f hf hconj]
  · have hc : conj z∉ball (0:ℂ) R := by
      simpa only [mem_ball_zero_iff,Complex.norm_conj] using hz
    rw [(divisor f (ball 0 R)).apply_eq_zero_of_notMem hz,
      (divisor f (ball 0 R)).apply_eq_zero_of_notMem hc]

include hconj in
theorem zeroSupport_conj (R : ℝ) (z : ℂ) :
    conj z∈zeroSupport f hf R ↔ z∈zeroSupport f hf R := by
  rw [mem_zeroSupport,mem_zeroSupport,ball_divisor_conj f hf hconj]

include h0 heven in
theorem numeratorPoly_unpaired (R : ℝ) :
    (∏ a∈zeroSupport f hf R,(1-C (1/a)*X)^(divisor f (ball 0 R) a).toNat)=
      numeratorPoly f hf R := by
  rw [opposite_finite_product (zeroSupport f hf R)
    (fun a => (1-C (1/a)*X)^(divisor f (ball 0 R) a).toNat)
    (fun a haS => (zeroSupport_neg f hf heven R a).mpr haS)
    (zeroSupport_ne_zero f hf h0 R)]
  unfold numeratorPoly
  apply Finset.prod_congr rfl
  intro a haS
  rw [ball_divisor_neg f hf heven,← mul_pow]
  congr 1
  simp only [one_div,inv_neg,map_neg,neg_mul,sub_neg_eq_add]
  ring_nf
  rw [Polynomial.C_pow]
  ring

include h0 heven hconj in
theorem numeratorPoly_conj (R : ℝ) :
    (numeratorPoly f hf R).map (starRingEnd ℂ)=numeratorPoly f hf R := by
  rw [← numeratorPoly_unpaired f hf h0 heven,Polynomial.map_prod]
  apply Finset.prod_bij (fun a _ => conj a)
  · intro a haS
    exact (zeroSupport_conj f hf hconj R a).mpr haS
  · intro a haS b hbS hab
    simpa only [Complex.conj_conj] using congrArg conj hab
  · intro b hbS
    exact ⟨conj b,(zeroSupport_conj f hf hconj R b).mpr hbS,Complex.conj_conj b⟩
  · intro a haS
    rw [Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_X,ball_divisor_conj f hf hconj]
    simp only [map_div₀,map_one]

def realPolynomial (P : ℂ[X]) : ℝ[X] :=
  ∑ n∈P.support,monomial n (P.coeff n).re

theorem realPolynomial_coeff (P : ℂ[X]) (n : ℕ) :
    (realPolynomial P).coeff n=(P.coeff n).re := by
  classical
  simp only [realPolynomial,finsetSum_coeff,coeff_monomial]
  by_cases hn : n∈P.support
  · simp [hn]
  · have hc : P.coeff n=0 := by simpa only [Polynomial.mem_support_iff,not_not] using hn
    simp [hn,hc]

theorem realPolynomial_map (P : ℂ[X]) (hP : P.map (starRingEnd ℂ)=P) :
    (realPolynomial P).map (algebraMap ℝ ℂ)=P := by
  ext n
  have he : conj (P.coeff n)=P.coeff n := by
    simpa only [coeff_map] using congrArg (fun Q : ℂ[X] => Q.coeff n) hP
  have him := Complex.conj_eq_iff_im.mp he
  simp only [coeff_map,realPolynomial_coeff,Complex.coe_algebraMap]
  exact Complex.ext (by simp) (by simpa using him.symm)

include h0 heven hconj in
theorem numeratorPoly_real (R : ℝ) :
    (realPolynomial (numeratorPoly f hf R)).map (algebraMap ℝ ℂ)=numeratorPoly f hf R :=
  realPolynomial_map _ (numeratorPoly_conj f hf h0 heven hconj R)


include h0 in
theorem mem_zeroSupport_iff (R : ℝ) (z : ℂ) :
    z∈zeroSupport f hf R ↔ z∈ball (0:ℂ) R ∧ f z=0 := by
  have he := (hf.mono (subset_univ (ball (0:ℂ) R))).meromorphicNFOn
    |>.zero_set_eq_divisor_support
      (fun z => EntireSubquadraticZeroCounting.zero_order_finite f hf h0 z)
  rw [mem_zeroSupport]
  change z∈Function.support (divisor f (ball 0 R)) ↔ _
  rw [← he]
  rfl

include h0 heven in
theorem numeratorPoly_zero_iff (R : ℝ) (z : ℂ) :
    (numeratorPoly f hf R).eval z=0 ↔ z∈ball (0:ℂ) R ∧ f z=0 := by
  rw [numeratorPoly_eval]
  constructor
  · intro hz
    obtain ⟨a,haS,hpow⟩ := Finset.prod_eq_zero_iff.mp hz
    have haS' := (Finset.mem_filter.mp haS).1
    have ha0 := zeroSupport_ne_zero f hf h0 R a haS'
    have hfactor : 1-z^2/a^2=0 := (pow_eq_zero_iff'.mp hpow).1
    have he : (z-a)*(z+a)=0 := by
      field_simp [ha0] at hfactor
      linear_combination -hfactor
    have hroots : z=a ∨ z=-a := by
      rcases mul_eq_zero.mp he with hh | hh
      · exact Or.inl (sub_eq_zero.mp hh)
      · exact Or.inr (eq_neg_of_add_eq_zero_left hh)
    apply (mem_zeroSupport_iff f hf h0 R z).mp
    rcases hroots with rfl | rfl
    · exact haS'
    · exact (zeroSupport_neg f hf heven R a).mpr haS'
  · intro hz
    have hzS := (mem_zeroSupport_iff f hf h0 R z).mpr hz
    have hz0 := zeroSupport_ne_zero f hf h0 R z hzS
    have hfactor (a : ℂ) (haS : a∈zeroSupport f hf R)
        (hval : 1-z^2/a^2=0) :
        (1-z^2/a^2)^(divisor f (ball 0 R) a).toNat=0 := by
      have hn : 0≤divisor f (ball 0 R) a := (hf.mono (subset_univ _)).divisor_nonneg a
      have hne := (mem_zeroSupport f hf R a).mp haS
      have hn0 : (divisor f (ball 0 R) a).toNat≠0 := by
        intro he
        have hh := Int.toNat_of_nonneg hn
        rw [he] at hh
        exact hne hh.symm
      rw [hval,zero_pow hn0]
    apply Finset.prod_eq_zero_iff.mpr
    by_cases hp : positiveHalf z
    · exact ⟨z,Finset.mem_filter.mpr ⟨hzS,hp⟩,hfactor z hzS (by simp [hz0])⟩
    · have hnS := (zeroSupport_neg f hf heven R z).mpr hzS
      exact ⟨-z,Finset.mem_filter.mpr ⟨hnS,(positiveHalf_neg z hz0).mpr hp⟩,
        hfactor (-z) hnS (by simp [hz0])⟩


include hf h0 heven hconj hgrowth in
theorem exists_real_polynomial_approximation :
    ∃ r : ℝ → ℝ, ∃ P : ℕ → ℝ[X],
      Tendsto r atTop atTop ∧
      (∀ R : ℝ, 1≤R → 2*R<r R ∧ r R<2*R+1) ∧
      (∀ n : ℕ, ∀ z : ℂ, ((P n).map (algebraMap ℝ ℂ)).eval z=0 ↔
        z∈ball (0:ℂ) (r ((n:ℝ)+1)) ∧ f z=0) ∧
      (∀ n : ℕ, ((P n).map (algebraMap ℝ ℂ)).eval 0=f 0) ∧
      (∀ n : ℕ, ∀ z : ℂ, ((P n).map (algebraMap ℝ ℂ)).eval (-z)=
        ((P n).map (algebraMap ℝ ℂ)).eval z) ∧
      TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) f atTop := by
  obtain ⟨r,hr,hrbounds,hlim⟩ := exists_polynomial_approximation f hf h0 heven hgrowth
  have hreal0 : ((f 0).re:ℂ)=f 0 := by
    have hc : conj (f 0)=f 0 := by simpa only [map_zero] using (hconj 0).symm
    have him := Complex.conj_eq_iff_im.mp hc
    exact Complex.ext (by simp) (by simpa using him.symm)
  let Q : ℝ → ℝ[X] := fun R => C (f 0).re*realPolynomial (numeratorPoly f hf (r R))
  have hQeq (R : ℝ) (z : ℂ) : ((Q R).map (algebraMap ℝ ℂ)).eval z=
      f 0*(numeratorPoly f hf (r R)).eval z := by
    dsimp [Q]
    rw [Polynomial.map_mul,Polynomial.map_C,eval_mul,eval_C,
      numeratorPoly_real f hf h0 heven hconj,Complex.coe_algebraMap,hreal0]
  have hQ : TendstoLocallyUniformly
      (fun R z => ((Q R).map (algebraMap ℝ ℂ)).eval z) f atTop := by
    have he : (fun R z => ((Q R).map (algebraMap ℝ ℂ)).eval z)=
        (fun R z => f 0*(numeratorPoly f hf (r R)).eval z) := funext fun R => funext (hQeq R)
    rw [he]
    exact hlim
  have hnat : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  refine ⟨r,fun n => Q ((n:ℝ)+1),hr,hrbounds,?_,?_,?_,?_⟩
  · intro n z
    rw [hQeq,mul_eq_zero]
    simp only [h0,false_or]
    exact numeratorPoly_zero_iff f hf h0 heven _ z
  · intro n
    rw [hQeq,numeratorPoly_origin,mul_one]
  · intro n z
    rw [hQeq,hQeq,numeratorPoly_even]
  · intro u hu x
    obtain ⟨s,hs,hsmall⟩ := hQ u hu x
    exact ⟨s,hs,hnat.eventually hsmall⟩


end OperatorDerivativeRewrite.Foundation.EvenEntirePolynomialApproximation



