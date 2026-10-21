import Foundation.EvenEntireInverseSquareTails
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! Uniform Gaussian budgets for complete actual divisor polynomials.
Finite inner products and annular bounds yield arbitrarily small quadratic growth
uniformly over all approximants. Fernique domination proves genuine Gaussian L1
and integral convergence for every fixed complex affine shift. -/
noncomputable section
open Set Metric Filter Complex Polynomial MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable
namespace OperatorDerivativeRewrite.Foundation.EvenEntireGaussianBudget
open EvenEntirePolynomialApproximation EvenEntireInverseSquareTails

theorem quadratic_factor_gaussian_bound (c z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ‖1-c*z^2‖ ≤ (1+‖c‖/δ)*Real.exp (δ*‖z‖^2) := by
  have h0 : 0 ≤ 1+‖c‖/δ := by positivity
  calc
    _ ≤ ‖(1:ℂ)‖+‖c*z^2‖ := norm_sub_le (1:ℂ) (c*z^2)
    _=1+‖c‖*‖z‖^2 := by rw [norm_one,Complex.norm_mul,_root_.norm_pow]
    _ ≤ (1+‖c‖/δ)+(δ+‖c‖)*‖z‖^2 := by
      nlinarith [div_nonneg (norm_nonneg c) hδ.le,mul_nonneg hδ.le (sq_nonneg ‖z‖)]
    _=(1+‖c‖/δ)*(1+δ*‖z‖^2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (δ*‖z‖^2)]) h0

theorem finite_product_subset_gaussian_budget (S : Finset ℂ) (n : ℂ → ℕ)
    (c : ℂ → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : Finset ℂ,T⊆S → ∀ z : ℂ,
      ‖∏ a∈T,(1-c a*z^2)^(n a)‖ ≤ C*Real.exp (ε*‖z‖^2) := by
  let D : ℝ := ∑ a∈S,(n a:ℝ)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun a ha => Nat.cast_nonneg _)
  let δ : ℝ := ε/(1+D)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hbudget : δ*D ≤ ε := by
    have he : δ*(1+D)=ε := by dsimp [δ]; field_simp
    nlinarith
  let A : ℂ → ℝ := fun a => 1+‖c a‖/δ
  have hA (a : ℂ) : 1 ≤ A a := by dsimp [A]; linarith [div_nonneg (norm_nonneg (c a)) hδ.le]
  let C : ℝ := ∏ a∈S,(A a)^(n a)
  have hC : 0 < C := Finset.prod_pos (fun a ha => pow_pos (by linarith [hA a]) _)
  refine ⟨C,hC,?_⟩
  intro T hT z
  have hsum : (∑ a∈T,(n a:ℝ)) ≤ D :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (by intro a ha hnot; positivity)
  have hprod : (∏ a∈T,(A a)^(n a)) ≤ C := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hT (by intro a ha; exact pow_nonneg (by linarith [hA a]) _)
    intro a ha hnot
    exact one_le_pow₀ (hA a)
  calc
    _=∏ a∈T,‖1-c a*z^2‖^(n a) := by rw [norm_prod]; simp only [norm_pow]
    _ ≤ ∏ a∈T,(A a*Real.exp (δ*‖z‖^2))^(n a) := by
      apply Finset.prod_le_prod₀
      · intro a ha; positivity
      · intro a ha
        exact pow_le_pow_left₀ (norm_nonneg _) (quadratic_factor_gaussian_bound (c a) z δ hδ) _
    _=(∏ a∈T,(A a)^(n a))*Real.exp ((∑ a∈T,(n a:ℝ))*(δ*‖z‖^2)) := by
      simp_rw [mul_pow,← Real.exp_nat_mul]
      rw [Finset.prod_mul_distrib,← Real.exp_sum]
      congr 2
      rw [Finset.sum_mul]
    _ ≤ C*Real.exp (ε*‖z‖^2) := by
      apply mul_le_mul hprod ?_ (by positivity) hC.le
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsum hδ.le
      have hf := mul_le_mul_of_nonneg_right (hh.trans hbudget) (sq_nonneg ‖z‖)
      nlinarith

variable (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)

theorem common_weight_product (R S : ℝ) (hRS : R ≤ S) (z : ℂ) :
    (∏ a∈halfZeroSupport f hf R,
      (1-z^2/a^2)^(divisor f (ball 0 S) a).toNat)=(numeratorPoly f hf R).eval z := by
  rw [numeratorPoly_eval]
  apply Finset.prod_congr rfl
  intro a ha
  have hbR := zeroSupport_mem_ball f hf R a (Finset.mem_filter.mp ha).1
  rw [ball_divisor_eq_of_mem f hf R S a hbR (ball_subset_ball hRS hbR)]

theorem numerator_eval_factorization (R S : ℝ) (hRS : R ≤ S) (z : ℂ) :
    (numeratorPoly f hf S).eval z=(numeratorPoly f hf R).eval z*
      (∏ a∈halfZeroSupport f hf S\halfZeroSupport f hf R,
        (1-z^2/a^2)^(divisor f (ball 0 S) a).toNat) := by
  have hsub := halfZeroSupport_mono f hf R S hRS
  have he := Finset.prod_sdiff
    (f:=fun a : ℂ => (1-z^2/a^2)^(divisor f (ball 0 S) a).toNat) hsub
  rw [common_weight_product f hf R S hRS z] at he
  rw [numeratorPoly_eval]
  simpa only [mul_comm] using he.symm

theorem bounded_radius_gaussian_budget (B ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ R : ℝ,R ≤ B → ∀ z : ℂ,
      ‖(numeratorPoly f hf R).eval z‖ ≤ C*Real.exp (ε*‖z‖^2) := by
  obtain ⟨C,hC,hbound⟩ := finite_product_subset_gaussian_budget (halfZeroSupport f hf B)
    (fun a => (divisor f (ball 0 B) a).toNat) (fun a => 1/a^2) ε hε
  refine ⟨C,hC,?_⟩
  intro R hRB z
  have hb := hbound (halfZeroSupport f hf R) (halfZeroSupport_mono f hf R B hRB) z
  have he : (∏ a∈halfZeroSupport f hf R,
      (1-(1/a^2)*z^2)^(divisor f (ball 0 B) a).toNat)=
      (numeratorPoly f hf R).eval z := by
    rw [← common_weight_product f hf R B hRB z]
    apply Finset.prod_congr rfl
    intro a ha
    congr 1
    ring
  rw [he] at hb
  exact hb

variable (h0 : f 0≠0) (heven : ∀ z : ℂ,f (-z)=f z)
  (hgrowth : ∃ C : ℝ,0 < C ∧ ∀ z : ℂ,‖f z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖))

include h0 heven hgrowth in
theorem exists_uniform_gaussian_budget (b : ℝ)
    (hstrip : ∀ z : ℂ,f z=0 → |z.im| ≤ b) :
    ∃ r : ℝ → ℝ,Tendsto r atTop atTop ∧
      (∀ R : ℝ,1 ≤ R → 2*R < r R ∧ r R < 2*R+1) ∧
      TendstoLocallyUniformly (fun R z => f 0*(numeratorPoly f hf (r R)).eval z) f atTop ∧
      ∀ ε : ℝ,0 < ε → ∃ C : ℝ,0 < C ∧ ∀ R : ℝ,1 ≤ R → ∀ z : ℂ,
        ‖f 0*(numeratorPoly f hf (r R)).eval z‖ ≤ C*Real.exp (ε*‖z‖^2) := by
  obtain ⟨r,hr,hrbounds,hpoly,hlim,htails⟩ :=
    exists_gaussian_product_tails f hf h0 heven hgrowth b hstrip
  refine ⟨r,hr,hrbounds,hpoly,?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := htails (ε/2) (by positivity)
  let i : ℝ := max N 1
  have hiN : N ≤ i := le_max_left _ _
  have hi1 : 1 ≤ i := le_max_right _ _
  let B : ℝ := 2*i+1
  have hiB : r i ≤ B := (hrbounds i hi1).2.le
  obtain ⟨C,hC,hinner⟩ := bounded_radius_gaussian_budget f hf B (ε/2) (by positivity)
  have hnum (j : ℝ) (hj : 1 ≤ j) (z : ℂ) :
      ‖(numeratorPoly f hf (r j)).eval z‖ ≤ C*Real.exp (ε*‖z‖^2) := by
    by_cases hbig : i ≤ j ∧ r i ≤ r j
    · have ht := hN i j hiN (hiN.trans hbig.1) hbig.2 z
      have hin := hinner (r i) hiB z
      rw [numerator_eval_factorization f hf (r i) (r j) hbig.2 z,Complex.norm_mul]
      calc
        _ ≤ (C*Real.exp ((ε/2)*‖z‖^2))*Real.exp ((ε/2)*‖z‖^2) :=
          mul_le_mul hin ht (norm_nonneg _) (by positivity)
        _=C*Real.exp (ε*‖z‖^2) := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
    · have hjB : r j ≤ B := by
        by_cases hij : i ≤ j
        · have hri : r j < r i := lt_of_not_ge (fun h => hbig ⟨hij,h⟩)
          exact hri.le.trans hiB
        · have hji : j < i := lt_of_not_ge hij
          have hb := (hrbounds j hj).2
          dsimp [B]
          linarith
      have hh := hinner (r j) hjB z
      apply hh.trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
      nlinarith [sq_nonneg ‖z‖]
  refine ⟨‖f 0‖*C,mul_pos (norm_pos_iff.mpr h0) hC,?_⟩
  intro R hR z
  rw [Complex.norm_mul]
  have hh := mul_le_mul_of_nonneg_left (hnum R hR z) (norm_nonneg (f 0))
  simpa only [mul_assoc] using hh


theorem shifted_norm_square (z c : ℂ) (y : ℝ) :
    ‖z+c*(y:ℂ)‖^2 ≤ 2*‖z‖^2+2*‖c‖^2*‖y‖^2 := by
  have hh := norm_add_le z (c*(y:ℂ))
  rw [Complex.norm_mul,Complex.norm_real] at hh
  have hs := pow_le_pow_left₀ (norm_nonneg (z+c*(y:ℂ))) hh 2
  nlinarith [sq_nonneg (‖z‖-‖c‖*‖y‖)]

theorem exists_gaussian_majorant (μ : Measure ℝ) [IsGaussian μ] (F : ℕ → ℂ → ℂ)
    (hbudget : ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ w : ℂ,
      ‖F n w‖ ≤ C*Real.exp (ε*‖w‖^2)) (z c : ℂ) :
    ∃ g : ℝ → ℝ,Integrable g μ ∧ ∀ n : ℕ,∀ y : ℝ,‖F n (z+c*(y:ℂ))‖ ≤ g y := by
  obtain ⟨a,ha,hgauss⟩ := IsGaussian.exists_integrable_exp_sq μ
  let ε : ℝ := a/(4*(‖c‖^2+1))
  have hε : 0<ε := div_pos ha (by positivity)
  obtain ⟨C,hC,hbound⟩ := hbudget ε hε
  let g : ℝ → ℝ := fun y => C*Real.exp (2*ε*‖z‖^2)*Real.exp (a*‖y‖^2)
  have hg : Integrable g μ := hgauss.const_mul (C*Real.exp (2*ε*‖z‖^2))
  have hcoef : 2*ε*‖c‖^2 ≤ a := by
    have he : ε*(4*(‖c‖^2+1))=a := by dsimp [ε]; field_simp
    nlinarith [mul_nonneg hε.le (sq_nonneg ‖c‖)]
  refine ⟨g,hg,?_⟩
  intro n y
  have hs := mul_le_mul_of_nonneg_left (shifted_norm_square z c y) hε.le
  have hc := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)
  calc
    _ ≤ C*Real.exp (ε*‖z+c*(y:ℂ)‖^2) := hbound n _
    _ ≤ C*Real.exp (2*ε*‖z‖^2+a*‖y‖^2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC.le
    _ = g y := by dsimp [g]; rw [Real.exp_add]; ring

theorem gaussian_integral_limit (μ : Measure ℝ) [IsGaussian μ]
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (hF : ∀ n,Continuous (F n)) (hcont : Continuous f)
    (hlim : TendstoLocallyUniformly F f atTop)
    (hbudget : ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ w : ℂ,
      ‖F n w‖ ≤ C*Real.exp (ε*‖w‖^2)) (z c : ℂ) :
    (∀ n : ℕ,Integrable (fun y : ℝ => F n (z+c*(y:ℂ))) μ) ∧
      Integrable (fun y : ℝ => f (z+c*(y:ℂ))) μ ∧
      Tendsto (fun n => ∫ y : ℝ,F n (z+c*(y:ℂ)) ∂μ) atTop
        (𝓝 (∫ y : ℝ,f (z+c*(y:ℂ)) ∂μ)) := by
  obtain ⟨g,hg,hbound⟩ := exists_gaussian_majorant μ F hbudget z c
  have hs : Continuous (fun y : ℝ => z+c*(y:ℂ)) := by fun_prop
  have hpoint (y : ℝ) : Tendsto (fun n => F n (z+c*(y:ℂ))) atTop
      (𝓝 (f (z+c*(y:ℂ)))) :=
    (hlim.tendstoLocallyUniformlyOn (s:=univ)).tendsto_at (mem_univ _)
  have hn (n : ℕ) : Integrable (fun y : ℝ => F n (z+c*(y:ℂ))) μ :=
    hg.mono' ((hF n).comp hs).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbound n))
  have hboundf (y : ℝ) : ‖f (z+c*(y:ℂ))‖ ≤ g y :=
    le_of_tendsto ((continuous_norm.continuousAt.tendsto).comp (hpoint y))
      (Filter.Eventually.of_forall (fun n => hbound n y))
  have hf : Integrable (fun y : ℝ => f (z+c*(y:ℂ))) μ :=
    hg.mono' (hcont.comp hs).aestronglyMeasurable (Filter.Eventually.of_forall hboundf)
  refine ⟨hn,hf,?_⟩
  exact tendsto_integral_of_dominated_convergence g
    (fun n => ((hF n).comp hs).aestronglyMeasurable) hg
    (fun n => Filter.Eventually.of_forall (hbound n))
    (Filter.Eventually.of_forall hpoint)


variable (hconj : ∀ z : ℂ,f (conj z)=conj (f z))

include hf h0 heven hgrowth hconj in
theorem exists_real_polynomials_with_gaussian_budget (b : ℝ)
    (hstrip : ∀ z : ℂ,f z=0 → |z.im| ≤ b) :
    ∃ r : ℝ → ℝ, ∃ P : ℕ → ℝ[X], Tendsto r atTop atTop ∧
      (∀ R : ℝ,1 ≤ R → 2*R<r R ∧ r R<2*R+1) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval z=0 ↔
        z∈ball (0:ℂ) (r ((n:ℝ)+1)) ∧ f z=0) ∧
      (∀ n : ℕ,((P n).map (algebraMap ℝ ℂ)).eval 0=f 0) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval (-z)=
        ((P n).map (algebraMap ℝ ℂ)).eval z) ∧
      TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) f atTop ∧
      ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ z : ℂ,
        ‖((P n).map (algebraMap ℝ ℂ)).eval z‖ ≤ C*Real.exp (ε*‖z‖^2) := by
  obtain ⟨r,hr,hrbounds,hlim,hbudget⟩ := exists_uniform_gaussian_budget f hf h0 heven hgrowth b hstrip
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
        (fun R z => f 0*(numeratorPoly f hf (r R)).eval z) :=
      _root_.funext fun R => _root_.funext (hQeq R)
    rw [he]
    exact hlim
  have hnat : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  refine ⟨r,fun n => Q ((n:ℝ)+1),hr,hrbounds,?_,?_,?_,?_,?_⟩
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
  · intro ε hε
    obtain ⟨C,hC,hbound⟩ := hbudget ε hε
    refine ⟨C,hC,?_⟩
    intro n z
    rw [hQeq]
    exact hbound ((n:ℝ)+1) (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) z


theorem gaussian_L1_limit (μ : Measure ℝ) [IsGaussian μ]
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (hF : ∀ n,Continuous (F n)) (hcont : Continuous f)
    (hlim : TendstoLocallyUniformly F f atTop)
    (hbudget : ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ w : ℂ,
      ‖F n w‖ ≤ C*Real.exp (ε*‖w‖^2)) (z c : ℂ) :
    Tendsto (fun n => ∫ y : ℝ,‖F n (z+c*(y:ℂ))-f (z+c*(y:ℂ))‖ ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨g,hg,hbound⟩ := exists_gaussian_majorant μ F hbudget z c
  have hs : Continuous (fun y : ℝ => z+c*(y:ℂ)) := by fun_prop
  have hpoint (y : ℝ) : Tendsto (fun n => F n (z+c*(y:ℂ))) atTop
      (𝓝 (f (z+c*(y:ℂ)))) :=
    (hlim.tendstoLocallyUniformlyOn (s:=univ)).tendsto_at (mem_univ _)
  have hboundf (y : ℝ) : ‖f (z+c*(y:ℂ))‖ ≤ g y :=
    le_of_tendsto ((continuous_norm.continuousAt.tendsto).comp (hpoint y))
      (Filter.Eventually.of_forall (fun n => hbound n y))
  have hdiff (n : ℕ) (y : ℝ) :
      ‖‖F n (z+c*(y:ℂ))-f (z+c*(y:ℂ))‖‖ ≤ 2*g y := by
    rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    have hh := norm_sub_le (F n (z+c*(y:ℂ))) (f (z+c*(y:ℂ)))
    linarith [hbound n y,hboundf y]
  have hpt (y : ℝ) : Tendsto (fun n => ‖F n (z+c*(y:ℂ))-f (z+c*(y:ℂ))‖)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => f (z+c*(y:ℂ))) atTop
        (𝓝 (f (z+c*(y:ℂ)))) := tendsto_const_nhds
    have hsub : Tendsto (fun n => F n (z+c*(y:ℂ))-f (z+c*(y:ℂ))) atTop
        (𝓝 (0:ℂ)) := by simpa only [sub_self] using (hpoint y).sub hconst
    have hh := (continuous_norm.continuousAt.tendsto).comp hsub
    simpa only [Function.comp_def,norm_zero] using hh
  have hm (n : ℕ) : Continuous (fun y : ℝ => ‖F n (z+c*(y:ℂ))-f (z+c*(y:ℂ))‖) :=
    (((hF n).comp hs).sub (hcont.comp hs)).norm
  have ht := tendsto_integral_of_dominated_convergence (fun y => 2*g y)
    (fun n => (hm n).aestronglyMeasurable) (hg.const_mul 2)
    (fun n => Filter.Eventually.of_forall (hdiff n)) (Filter.Eventually.of_forall hpt)
  simpa only [integral_zero] using ht


end OperatorDerivativeRewrite.Foundation.EvenEntireGaussianBudget






