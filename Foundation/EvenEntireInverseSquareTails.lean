import Foundation.EvenEntirePolynomialApproximation
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Actual divisor-product quadratic moments and absolute annular tails.
Compact holomorphic convergence controls the inverse-square sum. Under an explicit
fixed zero strip, absolute annular sums vanish and tail products have arbitrarily
small Gaussian growth on the whole plane. No full heat-limit interchange here. -/
noncomputable section
open Set Metric Filter Complex Polynomial MeromorphicOn
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace OperatorDerivativeRewrite.Foundation.EvenEntireInverseSquareTails
open EvenEntirePolynomialApproximation

theorem second_product (P Q : ℂ[X]) :
    (P*Q).derivative.derivative.eval 0=
      P.derivative.derivative.eval 0*Q.eval 0+
      2*P.derivative.eval 0*Q.derivative.eval 0+
      P.eval 0*Q.derivative.derivative.eval 0 := by
  simp only [derivative_mul,derivative_add,eval_add,eval_mul]
  ring

theorem power_origin_jets (P : ℂ[X]) (h0 : P.eval 0=1)
    (h1 : P.derivative.eval 0=0) (n : ℕ) :
    (P^n).eval 0=1 ∧ (P^n).derivative.eval 0=0 ∧
      (P^n).derivative.derivative.eval 0=(n:ℂ)*P.derivative.derivative.eval 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    constructor
    · simp only [eval_pow,h0,one_pow]
    constructor
    · rw [pow_succ,derivative_mul,eval_add,eval_mul,eval_mul,ih.2.1,h1]
      ring
    · rw [pow_succ,second_product,ih.1,ih.2.1,ih.2.2,h0,h1]
      push_cast
      ring

theorem product_origin_jets {ι : Type*} (S : Finset ι) (P : ι → ℂ[X])
    (h0 : ∀ a∈S,(P a).eval 0=1) (h1 : ∀ a∈S,(P a).derivative.eval 0=0) :
    (∏ a∈S,P a).eval 0=1 ∧ (∏ a∈S,P a).derivative.eval 0=0 ∧
      (∏ a∈S,P a).derivative.derivative.eval 0=
        ∑ a∈S,(P a).derivative.derivative.eval 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have h0a := h0 a (Finset.mem_insert_self ..)
    have h1a := h1 a (Finset.mem_insert_self ..)
    have hi := ih (fun b hb => h0 b (Finset.mem_insert_of_mem hb))
      (fun b hb => h1 b (Finset.mem_insert_of_mem hb))
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    constructor
    · rw [eval_mul,h0a,hi.1]; ring
    constructor
    · rw [derivative_mul,eval_add,eval_mul,eval_mul,h1a,hi.2.1]; ring
    · rw [second_product,h0a,h1a,hi.1,hi.2.1,hi.2.2]; ring

theorem paired_factor_jets (c : ℂ) (n : ℕ) :
    ((1-C c*X^2)^n).eval 0=1 ∧
      ((1-C c*X^2)^n).derivative.eval 0=0 ∧
      ((1-C c*X^2)^n).derivative.derivative.eval 0= -2*(n:ℂ)*c := by
  have h0 : (1-C c*X^2).eval (0:ℂ)=1 := by simp
  have h1 : (1-C c*X^2).derivative.eval (0:ℂ)=0 := by simp
  have h2 : (1-C c*X^2).derivative.derivative.eval (0:ℂ)= -2*c := by
    simp
    ring
  obtain ⟨h0n,h1n,h2n⟩ := power_origin_jets (1-C c*X^2) h0 h1 n
  exact ⟨h0n,h1n,by rw [h2n,h2]; ring⟩

variable (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)

def inverseSquareSum (R : ℝ) : ℂ :=
  ∑ a∈halfZeroSupport f hf R, ((divisor f (ball 0 R) a).toNat:ℂ)/a^2

theorem numerator_second_origin (R : ℝ) :
    (numeratorPoly f hf R).derivative.derivative.eval 0= -2*inverseSquareSum f hf R := by
  have hj := product_origin_jets (halfZeroSupport f hf R)
    (fun a => (1-C (1/a^2)*X^2)^(divisor f (ball 0 R) a).toNat)
    (fun a ha => (paired_factor_jets (1/a^2) _).1)
    (fun a ha => (paired_factor_jets (1/a^2) _).2.1)
  rw [numeratorPoly,hj.2.2]
  simp only [(paired_factor_jets _ _).2.2]
  unfold inverseSquareSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

variable (h0 : f 0≠0) (heven : ∀ z : ℂ,f (-z)=f z)
  (hgrowth : ∃ C : ℝ,0<C ∧ ∀ z : ℂ,‖f z‖≤C*Real.exp (‖z‖*Real.sqrt ‖z‖))

include h0 heven hgrowth in
theorem exists_inverseSquareSum_limit :
    ∃ r : ℝ → ℝ, Tendsto r atTop atTop ∧
      (∀ R : ℝ,1≤R → 2*R<r R ∧ r R<2*R+1) ∧
      TendstoLocallyUniformly (fun R z => f 0*(numeratorPoly f hf (r R)).eval z) f atTop ∧
      Tendsto (fun R => inverseSquareSum f hf (r R)) atTop
        (𝓝 (-deriv (deriv f) 0/(2*f 0))) := by
  obtain ⟨r,hr,hrbounds,hlim⟩ := exists_polynomial_approximation f hf h0 heven hgrowth
  let Q : ℝ → ℂ[X] := fun R => C (f 0)*numeratorPoly f hf (r R)
  have hQ : TendstoLocallyUniformlyOn (fun R z => (Q R).eval z) f atTop univ := by
    apply tendstoLocallyUniformlyOn_univ.mpr
    simpa only [Q,eval_mul,eval_C] using hlim
  have hd := hQ.deriv (Filter.Eventually.of_forall (fun R => (Q R).differentiableOn)) isOpen_univ
  have hd' : TendstoLocallyUniformlyOn (fun R z => (Q R).derivative.eval z)
      (deriv f) atTop univ := by
    have he (R : ℝ) : deriv (fun z => (Q R).eval z)=(fun z => (Q R).derivative.eval z) :=
      _root_.funext (fun z => (Q R).deriv (x:=z))
    simpa only [Function.comp_def,he] using hd
  have hdd := hd'.deriv
    (Filter.Eventually.of_forall (fun R => (Q R).derivative.differentiableOn)) isOpen_univ
  have hdd' : TendstoLocallyUniformlyOn (fun R z => (Q R).derivative.derivative.eval z)
      (deriv (deriv f)) atTop univ := by
    have he (R : ℝ) : deriv (fun z => (Q R).derivative.eval z)=
        (fun z => (Q R).derivative.derivative.eval z) :=
      _root_.funext (fun z => (Q R).derivative.deriv (x:=z))
    simpa only [Function.comp_def,he] using hdd
  have ht := hdd'.tendsto_at (mem_univ (0:ℂ))
  have he (R : ℝ) : (Q R).derivative.derivative.eval 0=
      -2*f 0*inverseSquareSum f hf (r R) := by
    dsimp [Q]
    rw [derivative_C_mul,derivative_C_mul,eval_mul,eval_C,numerator_second_origin]
    ring
  simp_rw [he] at ht
  have ht' := ht.const_mul (-(2*f 0)⁻¹)
  have heq : (fun R => -(2*f 0)⁻¹*(-2*f 0*inverseSquareSum f hf (r R)))=
      (fun R => inverseSquareSum f hf (r R)) := by
    funext R
    field_simp [h0]
  rw [heq] at ht'
  have hl : -(2*f 0)⁻¹*deriv (deriv f) 0= -deriv (deriv f) 0/(2*f 0) := by ring
  rw [hl] at ht'
  exact ⟨r,hr,hrbounds,hlim,ht'⟩


theorem inverse_square_real_lower (a : ℂ) (ha : a≠0)
    (hcone : 2*|a.im|≤‖a‖) : ‖(1/a^2:ℂ)‖≤2*(1/a^2:ℂ).re := by
  have hr : 0<‖a‖ := norm_pos_iff.mpr ha
  have he : (1/a^2:ℂ).re=(a.re^2-a.im^2)/‖a‖^4 := by
    simp only [one_div,Complex.inv_re,Complex.normSq_eq_norm_sq,norm_pow]
    rw [pow_two,Complex.mul_re]
    ring
  rw [norm_div,norm_one,norm_pow,he]
  have hs := pow_le_pow_left₀ (by positivity : 0≤2*|a.im|) hcone 2
  have hn := Complex.sq_norm a
  rw [Complex.normSq_apply] at hn
  have hnum : ‖a‖^2≤2*(a.re^2-a.im^2) := by nlinarith [sq_abs a.im]
  rw [← mul_div_assoc,div_le_div_iff₀ (sq_pos_of_pos hr) (pow_pos hr 4)]
  have hm := mul_le_mul_of_nonneg_right hnum (sq_nonneg ‖a‖)
  nlinarith

theorem weighted_inverse_square_cone (a : ℂ) (ha : a≠0)
    (hcone : 2*|a.im|≤‖a‖) (n : ℕ) :
    ‖(n:ℂ)/a^2‖≤2*((n:ℂ)/a^2).re := by
  have he : (n:ℂ)/a^2=(n:ℂ)*(1/a^2) := by ring
  rw [he,norm_mul]
  have hn : ‖(n:ℂ)‖=(n:ℝ) := by simp
  rw [hn]
  have hr : ((n:ℂ)*(1/a^2)).re=(n:ℝ)*(1/a^2:ℂ).re := by simp
  rw [hr]
  have hh := mul_le_mul_of_nonneg_left (inverse_square_real_lower a ha hcone)
    (Nat.cast_nonneg n : (0:ℝ)≤n)
  nlinarith

theorem finite_inverse_square_tail_bound (S : Finset ℂ) (n : ℂ → ℕ)
    (hzero : ∀ a∈S,a≠0) (hcone : ∀ a∈S,2*|a.im|≤‖a‖) :
    (∑ a∈S,‖(n a:ℂ)/a^2‖)≤2*(∑ a∈S,(n a:ℂ)/a^2).re := by
  have hb := Finset.sum_le_sum (fun a ha =>
    weighted_inverse_square_cone a (hzero a ha) (hcone a ha) (n a))
  simpa only [Complex.re_sum,Finset.mul_sum] using hb


include hf in
theorem ball_divisor_eq_of_mem (R S : ℝ) (a : ℂ)
    (haR : a∈ball (0:ℂ) R) (haS : a∈ball (0:ℂ) S) :
    divisor f (ball 0 R) a=divisor f (ball 0 S) a := by
  rw [(hf.mono (subset_univ _)).meromorphicOn.divisor_apply haR,
    (hf.mono (subset_univ _)).meromorphicOn.divisor_apply haS]

theorem halfZeroSupport_mono (R S : ℝ) (hRS : R≤S) :
    halfZeroSupport f hf R ⊆ halfZeroSupport f hf S := by
  intro a ha
  obtain ⟨haR,hp⟩ := Finset.mem_filter.mp ha
  have hbR := zeroSupport_mem_ball f hf R a haR
  have hbS : a∈ball (0:ℂ) S := ball_subset_ball hRS hbR
  refine Finset.mem_filter.mpr ⟨?_,hp⟩
  rw [mem_zeroSupport,← ball_divisor_eq_of_mem f hf R S a hbR hbS]
  exact (mem_zeroSupport f hf R a).mp haR

theorem inverseSquareSum_difference (R S : ℝ) (hRS : R≤S) :
    inverseSquareSum f hf S-inverseSquareSum f hf R=
      ∑ a∈halfZeroSupport f hf S\halfZeroSupport f hf R,
        ((divisor f (ball 0 S) a).toNat:ℂ)/a^2 := by
  have hsub := halfZeroSupport_mono f hf R S hRS
  have he : (∑ a∈halfZeroSupport f hf R,((divisor f (ball 0 S) a).toNat:ℂ)/a^2)=
      inverseSquareSum f hf R := by
    unfold inverseSquareSum
    apply Finset.sum_congr rfl
    intro a ha
    have hbR := zeroSupport_mem_ball f hf R a (Finset.mem_filter.mp ha).1
    rw [ball_divisor_eq_of_mem f hf R S a hbR (ball_subset_ball hRS hbR)]
  apply (sub_eq_iff_eq_add).mpr
  have hs := Finset.sum_sdiff (f:=fun a : ℂ => ((divisor f (ball 0 S) a).toNat:ℂ)/a^2) hsub
  rw [he] at hs
  exact hs.symm

include h0 in
theorem actual_inverse_square_tail_bound (R S b : ℝ) (hRS : R≤S) (hRb : 2*b≤R)
    (hstrip : ∀ z : ℂ,f z=0 → |z.im|≤b) :
    (∑ a∈halfZeroSupport f hf S\halfZeroSupport f hf R,
      ‖((divisor f (ball 0 S) a).toNat:ℂ)/a^2‖)≤
      2*(inverseSquareSum f hf S-inverseSquareSum f hf R).re := by
  rw [inverseSquareSum_difference f hf R S hRS]
  apply finite_inverse_square_tail_bound
  · intro a ha
    exact zeroSupport_ne_zero f hf h0 S a (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).1
  · intro a ha
    obtain ⟨haS,haR⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨haS',hp⟩ := Finset.mem_filter.mp haS
    have hazero := ((mem_zeroSupport_iff f hf h0 S a).mp haS').2
    have hb : R≤‖a‖ := by
      by_contra h
      have hbR : a∈ball (0:ℂ) R := mem_ball_zero_iff.mpr (lt_of_not_ge h)
      have haR' := (mem_zeroSupport_iff f hf h0 R a).mpr ⟨hbR,hazero⟩
      exact haR (Finset.mem_filter.mpr ⟨haR',hp⟩)
    linarith [hstrip a hazero]


include h0 heven hgrowth in
theorem exists_absolute_inverse_square_tails (b : ℝ)
    (hstrip : ∀ z : ℂ,f z=0 → |z.im|≤b) :
    ∃ r : ℝ → ℝ, Tendsto r atTop atTop ∧
      (∀ R : ℝ,1≤R → 2*R<r R ∧ r R<2*R+1) ∧
      TendstoLocallyUniformly (fun R z => f 0*(numeratorPoly f hf (r R)).eval z) f atTop ∧
      Tendsto (fun R => inverseSquareSum f hf (r R)) atTop
        (𝓝 (-deriv (deriv f) 0/(2*f 0))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℝ, ∀ i j : ℝ, N ≤ i → N ≤ j → r i ≤ r j →
        (∑ a∈halfZeroSupport f hf (r j)\halfZeroSupport f hf (r i),
          ‖((divisor f (ball 0 (r j)) a).toNat:ℂ)/a^2‖)<ε := by
  obtain ⟨r,hr,hrbounds,hpoly,hlim⟩ := exists_inverseSquareSum_limit f hf h0 heven hgrowth
  refine ⟨r,hr,hrbounds,hpoly,hlim,?_⟩
  intro ε hε
  let L : ℂ := -deriv (deriv f) 0/(2*f 0)
  have hsmall := (Metric.tendsto_nhds.mp hlim) (ε/8) (by positivity)
  have hlarge := hr.eventually (eventually_ge_atTop (2*b))
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (hsmall.and hlarge)
  refine ⟨N,?_⟩
  intro i j hi hj hij
  have hbi := hN i hi
  have hbj := hN j hj
  have hbound := actual_inverse_square_tail_bound f hf h0 (r i) (r j) b hij hbi.2 hstrip
  have hdiff : ‖inverseSquareSum f hf (r j)-inverseSquareSum f hf (r i)‖<ε/2 := by
    have hh := norm_sub_le (inverseSquareSum f hf (r j)-L)
      (inverseSquareSum f hf (r i)-L)
    have he : (inverseSquareSum f hf (r j)-L)-(inverseSquareSum f hf (r i)-L)=
        inverseSquareSum f hf (r j)-inverseSquareSum f hf (r i) := by ring
    rw [he] at hh
    have hsi : ‖inverseSquareSum f hf (r i)-L‖<ε/8 := by simpa only [dist_eq_norm] using hbi.1
    have hsj : ‖inverseSquareSum f hf (r j)-L‖<ε/8 := by simpa only [dist_eq_norm] using hbj.1
    linarith
  have hre := Complex.re_le_norm (inverseSquareSum f hf (r j)-inverseSquareSum f hf (r i))
  linarith


theorem paired_product_norm_bound (S : Finset ℂ) (n : ℂ → ℕ) (z : ℂ) :
    ‖∏ a∈S,(1-z^2/a^2)^(n a)‖≤
      Real.exp (‖z‖^2*(∑ a∈S,‖(n a:ℂ)/a^2‖)) := by
  have hb := RiemannQuarticDenominatorLimit.finite_power_product_bound S n
    (fun a => -(z^2/a^2))
  simp only [← sub_eq_add_neg] at hb
  have hs : (∑ a∈S,(n a:ℝ)*‖-(z^2/a^2)‖)=
      ‖z‖^2*(∑ a∈S,‖(n a:ℂ)/a^2‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [norm_neg,norm_div,norm_pow]
    have hn : ‖(n a:ℂ)‖=(n a:ℝ) := by simp
    rw [hn]
    ring
  rw [hs] at hb
  have hh := norm_le_norm_sub_add (∏ a∈S,(1-z^2/a^2)^(n a)) (1:ℂ)
  norm_num only [norm_one] at hh
  linarith

include h0 heven hgrowth in
theorem exists_gaussian_product_tails (b : ℝ)
    (hstrip : ∀ z : ℂ,f z=0 → |z.im|≤b) :
    ∃ r : ℝ → ℝ, Tendsto r atTop atTop ∧
      (∀ R : ℝ,1≤R → 2*R<r R ∧ r R<2*R+1) ∧
      TendstoLocallyUniformly (fun R z => f 0*(numeratorPoly f hf (r R)).eval z) f atTop ∧
      Tendsto (fun R => inverseSquareSum f hf (r R)) atTop
        (𝓝 (-deriv (deriv f) 0/(2*f 0))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℝ, ∀ i j : ℝ, N ≤ i → N ≤ j → r i ≤ r j →
        ∀ z : ℂ, ‖∏ a∈halfZeroSupport f hf (r j)\halfZeroSupport f hf (r i),
          (1-z^2/a^2)^(divisor f (ball 0 (r j)) a).toNat‖≤Real.exp (ε*‖z‖^2) := by
  obtain ⟨r,hr,hrbounds,hpoly,hlim,htails⟩ :=
    exists_absolute_inverse_square_tails f hf h0 heven hgrowth b hstrip
  refine ⟨r,hr,hrbounds,hpoly,hlim,?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := htails ε hε
  refine ⟨N,?_⟩
  intro i j hi hj hij z
  have hs := hN i j hi hj hij
  have hp := paired_product_norm_bound
    (halfZeroSupport f hf (r j)\halfZeroSupport f hf (r i))
    (fun a => (divisor f (ball 0 (r j)) a).toNat) z
  apply hp.trans
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hs.le (sq_nonneg ‖z‖)
  nlinarith


end OperatorDerivativeRewrite.Foundation.EvenEntireInverseSquareTails





