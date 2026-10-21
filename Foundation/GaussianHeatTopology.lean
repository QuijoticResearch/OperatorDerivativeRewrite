import Foundation.RiemannQuadraticGaussian
import Foundation.PseudoMomentGaussianBoundary
import Mathlib.Data.Nat.Choose.Basic

/-! Compact-uniform polynomial limits do not suffice for Gaussian backward heat.
The actual even real polynomials have value one at the origin and converge locally
uniformly to one, while every genuine time-one imaginary Gaussian integral is two.
Integrability, transport to the existing heat law, exact L1 distance, failure of
common domination, and the pure-order polynomial expectation identity are proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Set Metric Filter Complex
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianHeatTopology

def coefficient (n : ℕ) : ℝ := (-1)^n*(n.factorial : ℝ)/((2*n).factorial : ℝ)
def q (n : ℕ) (z : ℂ) : ℂ := (coefficient n : ℂ)*z^(2*n)
def heatAtZero (f : ℂ → ℂ) : ℂ :=
  ∫ x : ℝ, f (Complex.I*((Real.sqrt 2*x : ℝ):ℂ)) ∂GaussianCore.γ

theorem factorial_square_le (n : ℕ) : n.factorial*n.factorial ≤ (2*n).factorial := by
  have hh := Nat.le_of_dvd (Nat.factorial_pos (n+n))
    (Nat.factorial_mul_factorial_dvd_factorial_add n n)
  simpa only [two_mul] using hh

theorem coefficient_norm (n : ℕ) : ‖(coefficient n : ℂ)‖=
    (n.factorial : ℝ)/((2*n).factorial : ℝ) := by
  simp [coefficient,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_mul,abs_pow]

theorem coefficient_bound (n : ℕ) : ‖(coefficient n : ℂ)‖ ≤ 1/(n.factorial : ℝ) := by
  rw [coefficient_norm]
  have hn : 0<(n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hd : 0<((2*n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (2*n)
  apply (div_le_div_iff₀ hd hn).mpr
  norm_num only [one_mul]
  exact_mod_cast factorial_square_le n

theorem q_bound (n : ℕ) (z : ℂ) (R : ℝ) (hR : 0≤R) (hz : ‖z‖≤R) :
    ‖q n z‖ ≤ (R^2)^n/(n.factorial : ℝ) := by
  rw [q,norm_mul,norm_pow]
  have hp : ‖z‖^(2*n) ≤ R^(2*n) := pow_le_pow_left₀ (norm_nonneg z) hz _
  calc
    _ ≤ (1/(n.factorial : ℝ))*R^(2*n) :=
      mul_le_mul (coefficient_bound n) hp (pow_nonneg (norm_nonneg z) _)
        (by positivity)
    _ = _ := by rw [pow_mul]; ring

theorem q_uniform_disk (R : ℝ) (hR : 0≤R) :
    TendstoUniformlyOn q (fun _ => 0) atTop (closedBall (0:ℂ) R) := by
  have hs : Summable (fun n : ℕ => (R^2)^n/(n.factorial : ℝ)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp (R^2)).summable
  have ht := hs.tendsto_atTop_zero
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn
  intro z hz
  have hb := q_bound n z R hR (mem_closedBall_zero_iff.mp hz)
  simpa only [dist_zero_left] using hb.trans_lt hn

theorem q_locally_uniform_zero : TendstoLocallyUniformly q (fun _ => 0) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R,hR,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0:ℂ)
  exact (q_uniform_disk R hR.le).mono hsub

theorem q_imaginary (n : ℕ) (y : ℝ) :
    q n (I*(y:ℂ))=((n.factorial : ℝ)/((2*n).factorial : ℝ)*y^(2*n) : ℝ) := by
  have hs : (-1:ℂ)^n*(-1:ℂ)^n=1 := by rw [← mul_pow]; norm_num
  simp only [q,coefficient,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one,mul_pow,pow_mul,Complex.I_sq]
  calc
    _ = ((-1:ℂ)^n*(-1:ℂ)^n)*((n.factorial : ℝ):ℂ)/(((2*n).factorial : ℝ):ℂ)*
      ((y:ℂ)^2)^n := by ring
    _ = _ := by rw [hs]; ring

theorem q_imaginary_integrable (n : ℕ) :
    Integrable (fun x : ℝ => q n (I*((Real.sqrt 2*x : ℝ):ℂ))) GaussianCore.γ := by
  have hi := PseudoMomentGaussianBoundary.scaled_polynomial_integrable (Real.sqrt 2)
    (X^(2*n) : ℝ[X])
  simp only [Polynomial.eval_pow,Polynomial.eval_X] at hi
  have hc : Integrable (fun x : ℝ =>
      (((n.factorial : ℝ)/((2*n).factorial : ℝ)*(Real.sqrt 2*x)^(2*n) : ℝ):ℂ))
      GaussianCore.γ := (hi.const_mul ((n.factorial : ℝ)/((2*n).factorial : ℝ))).ofReal
  simpa only [q_imaginary] using hc

theorem heat_q (n : ℕ) : heatAtZero (q n)=1 := by
  have hm := PseudoMomentGaussianBoundary.expectation_nonnegative_gaussian 1
    (by norm_num) (X^(2*n) : ℝ[X])
  rw [PseudoPolynomialStein.expectation_X_pow,
    PseudoPolynomialStein.moment_multiple 2 (by norm_num)] at hm
  simp only [one_pow,mul_one,Polynomial.eval_pow,Polynomial.eval_X,mul_one] at hm
  unfold heatAtZero
  simp_rw [q_imaginary]
  rw [integral_complex_ofReal,integral_const_mul,← hm]
  have hn : (n.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hd : ((2*n).factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*n)
  have he : (n.factorial : ℝ)/((2*n).factorial : ℝ)*
      (((2*n).factorial : ℝ)/(n.factorial : ℝ))=1 := by field_simp
  simpa only [Complex.ofReal_one] using congrArg (fun x : ℝ => (x:ℂ)) he

theorem variance_two_law : GaussianCore.γ.map (fun x : ℝ => Real.sqrt 2*x)=
    RiemannQuadraticGaussian.law 1 := by
  have hv : (NNReal.mk ((Real.sqrt 2)^2) (sq_nonneg _) : ℝ≥0)=2 := by
    apply Subtype.ext
    change (Real.sqrt (2:ℝ))^2=(2:ℝ)
    exact Real.sq_sqrt (by norm_num)
  change (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt 2*x)=gaussianReal 0 (2*1)
  rw [gaussianReal_map_const_mul,hv]
  simp only [mul_zero,mul_one]

theorem heat_eq_law (f : ℂ → ℂ) (hf : Continuous f) :
    heatAtZero f=∫ y : ℝ, f (I*(y:ℂ)) ∂RiemannQuadraticGaussian.law 1 := by
  have hl : HasLaw (fun x : ℝ => Real.sqrt 2*x) (RiemannQuadraticGaussian.law 1)
      GaussianCore.γ := ⟨by fun_prop,variance_two_law⟩
  have hc : Continuous (fun y : ℝ => f (I*(y:ℂ))) :=
    hf.comp (continuous_const.mul Complex.continuous_ofReal)
  exact hl.integral_comp (f:=fun y : ℝ => f (I*(y:ℂ))) hc.aestronglyMeasurable

def normalized (n : ℕ) (z : ℂ) : ℂ := 1+q (n+1) z

def polynomial (n : ℕ) : ℝ[X] := 1+C (coefficient (n+1))*X^(2*(n+1))

theorem polynomial_eval (n : ℕ) (z : ℂ) :
    ((polynomial n).map (algebraMap ℝ ℂ)).eval z=normalized n z := by
  simp [polynomial,normalized,q]

theorem normalized_origin (n : ℕ) : normalized n 0=1 := by
  simp [normalized,q]

theorem normalized_even (n : ℕ) (z : ℂ) : normalized n (-z)=normalized n z := by
  simp only [normalized,q,pow_mul,neg_sq]

theorem normalized_uniform_disk (R : ℝ) (hR : 0≤R) :
    TendstoUniformlyOn normalized (fun _ => 1) atTop (closedBall (0:ℂ) R) := by
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hh := hshift.eventually ((Metric.tendstoUniformlyOn_iff.mp (q_uniform_disk R hR)) ε hε)
  filter_upwards [hh] with n hn
  intro z hz
  simpa [dist_eq_norm,normalized,sub_add_eq_sub_sub] using hn z hz

theorem normalized_locally_uniform_one :
    TendstoLocallyUniformly normalized (fun _ => 1) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R,hR,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0:ℂ)
  exact (normalized_uniform_disk R hR.le).mono hsub

theorem normalized_imaginary_integrable (n : ℕ) :
    Integrable (fun x : ℝ => normalized n (I*((Real.sqrt 2*x : ℝ):ℂ))) GaussianCore.γ :=
  (integrable_const (1:ℂ)).add (q_imaginary_integrable (n+1))

theorem heat_normalized (n : ℕ) : heatAtZero (normalized n)=2 := by
  unfold heatAtZero normalized
  rw [integral_add (integrable_const (1:ℂ)) (q_imaginary_integrable (n+1))]
  change (∫ x : ℝ, (1:ℂ) ∂GaussianCore.γ)+heatAtZero (q (n+1))=2
  rw [heat_q]
  norm_num

theorem normalized_law_integrable (n : ℕ) :
    Integrable (fun y : ℝ => normalized n (I*(y:ℂ))) (RiemannQuadraticGaussian.law 1) := by
  rw [← variance_two_law]
  apply (integrable_map_measure (by unfold normalized q; fun_prop) (by fun_prop)).mpr
  exact normalized_imaginary_integrable n

theorem heat_normalized_law (n : ℕ) :
    (∫ y : ℝ, normalized n (I*(y:ℂ)) ∂RiemannQuadraticGaussian.law 1)=2 := by
  rw [← heat_eq_law (normalized n) (by unfold normalized q; fun_prop),heat_normalized]

theorem heat_one : heatAtZero (fun _ => 1)=1 := by simp [heatAtZero]

theorem heat_not_tendsto : ¬ Tendsto (fun n => heatAtZero (normalized n)) atTop
    (𝓝 (heatAtZero (fun _ => 1))) := by
  simp only [heat_normalized,heat_one]
  intro h
  have he : (2:ℂ)=1 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at he

theorem no_integrable_domination : ¬ ∃ g : ℝ → ℝ,
    Integrable g (RiemannQuadraticGaussian.law 1) ∧
      ∀ n : ℕ, ∀ᵐ y : ℝ ∂RiemannQuadraticGaussian.law 1,
        ‖normalized n (I*(y:ℂ))‖ ≤ g y := by
  rintro ⟨g,hg,hbound⟩
  have hpoint : ∀ᵐ y : ℝ ∂RiemannQuadraticGaussian.law 1,
      Tendsto (fun n => normalized n (I*(y:ℂ))) atTop (𝓝 1) :=
    Filter.Eventually.of_forall (fun y =>
      (normalized_locally_uniform_one.tendstoLocallyUniformlyOn (s:=univ)).tendsto_at
        (mem_univ (I*(y:ℂ))))
  have ht := tendsto_integral_of_dominated_convergence g
    (fun n => by unfold normalized q; fun_prop) hg hbound hpoint
  simp only [heat_normalized_law] at ht
  have ht' : Tendsto (fun _ : ℕ => (2:ℂ)) atTop (𝓝 1) := by simpa using ht
  have he : (2:ℂ)=1 := tendsto_nhds_unique
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2:ℂ)) atTop (𝓝 2)) ht'
  norm_num at he

theorem q_law_integrable (n : ℕ) :
    Integrable (fun y : ℝ => q n (I*(y:ℂ))) (RiemannQuadraticGaussian.law 1) := by
  rw [← variance_two_law]
  apply (integrable_map_measure (by unfold q; fun_prop) (by fun_prop)).mpr
  exact q_imaginary_integrable n

theorem heat_q_law (n : ℕ) :
    (∫ y : ℝ, q n (I*(y:ℂ)) ∂RiemannQuadraticGaussian.law 1)=1 := by
  rw [← heat_eq_law (q n) (by unfold q; fun_prop),heat_q]

theorem q_imaginary_norm (n : ℕ) (y : ℝ) :
    ‖q n (I*(y:ℂ))‖=(n.factorial : ℝ)/((2*n).factorial : ℝ)*y^(2*n) := by
  have hp : 0≤y^(2*n) := by rw [pow_mul]; positivity
  have hv : 0≤(n.factorial : ℝ)/((2*n).factorial : ℝ)*y^(2*n) :=
    mul_nonneg (by positivity) hp
  rw [q_imaginary]
  simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_of_nonneg hv

theorem integral_distance_one (n : ℕ) :
    (∫ y : ℝ, ‖normalized n (I*(y:ℂ))-1‖ ∂RiemannQuadraticGaussian.law 1)=1 := by
  have he (y : ℝ) : ‖normalized n (I*(y:ℂ))-1‖=(q (n+1) (I*(y:ℂ))).re := by
    simp only [normalized,add_sub_cancel_left]
    rw [q_imaginary_norm,q_imaginary,Complex.ofReal_re]
  calc
    _ = ∫ y : ℝ, (q (n+1) (I*(y:ℂ))).re ∂RiemannQuadraticGaussian.law 1 :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = (∫ y : ℝ, q (n+1) (I*(y:ℂ)) ∂RiemannQuadraticGaussian.law 1).re := by
      simpa only [RCLike.re_eq_complex_re] using integral_re (q_law_integrable (n+1))
    _ = 1 := by rw [heat_q_law,Complex.one_re]

theorem q_exp_bound (n : ℕ) (z : ℂ) : ‖q n z‖ ≤ Real.exp (‖z‖^2) :=
  (q_bound n z ‖z‖ (norm_nonneg z) le_rfl).trans
    (Real.pow_div_factorial_le_exp (‖z‖^2) (sq_nonneg _) n)

theorem polynomial_signed_expectation (n : ℕ) :
    PseudoPolynomialStein.expectation 2 (-1) (polynomial n)=2 := by
  have hone : PseudoPolynomialStein.expectation 2 (-1) 1=1 := by
    simpa only [pow_zero,PseudoPolynomialStein.moment_zero] using
      PseudoPolynomialStein.expectation_X_pow 2 0 (-1)
  have hs : (-1:ℝ)^(n+1)*(-1:ℝ)^(n+1)=1 := by rw [← mul_pow]; norm_num
  have he : coefficient (n+1)*(((2*(n+1)).factorial : ℝ)*(-1:ℝ)^(n+1)/
      ((n+1).factorial : ℝ))=1 := by
    unfold coefficient
    calc
      _ = ((-1:ℝ)^(n+1)*(-1:ℝ)^(n+1))*
          (((n+1).factorial : ℝ)/((2*(n+1)).factorial : ℝ))*
          (((2*(n+1)).factorial : ℝ)/((n+1).factorial : ℝ)) := by ring
      _ = 1 := by
        rw [hs]
        have hn : ((n+1).factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
        have hd : ((2*(n+1)).factorial : ℝ)≠0 := by
          exact_mod_cast Nat.factorial_ne_zero (2*(n+1))
        field_simp
  rw [polynomial,map_add,C_mul_X_pow_eq_monomial,
    PseudoPolynomialStein.expectation_monomial,hone,
    PseudoPolynomialStein.moment_multiple 2 (by norm_num),he]
  norm_num

theorem polynomial_expectation_eq_heat (n : ℕ) :
    (PseudoPolynomialStein.expectation 2 (-1) (polynomial n) : ℂ)=
      heatAtZero (normalized n) := by
  rw [polynomial_signed_expectation,heat_normalized]
  norm_num

end OperatorDerivativeRewrite.Foundation.GaussianHeatTopology
