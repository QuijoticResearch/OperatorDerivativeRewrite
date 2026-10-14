import Foundation.GaussianL2QuarticEmbeddingObstruction
import Foundation.GaussianAdjoints
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Physical exponential targets lie in the actual closed Gaussian derivative graph,
but their graph norm cannot bound L4. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianExponentialSobolevObstruction
open GaussianCore GaussianL2QuarticEmbeddingObstruction

def taylorPolynomial (θ : ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range N, Polynomial.C (θ^i/(i.factorial : ℝ))*Polynomial.X^i

theorem taylor_eval (θ x : ℝ) (N : ℕ) : (taylorPolynomial θ N).eval x=
    ∑ i ∈ Finset.range N, (θ*x)^i/(i.factorial : ℝ) := by
  simp only [taylorPolynomial,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  ring

private theorem exp_series (x : ℝ) : HasSum (fun i : ℕ => x^i/(i.factorial : ℝ)) (Real.exp x) := by
  simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

theorem taylor_eval_bound (θ x : ℝ) (N : ℕ) : |(taylorPolynomial θ N).eval x|≤Real.exp |θ*x| := by
  rw [taylor_eval]
  have hs := exp_series |θ*x|
  calc
    _≤∑ i ∈ Finset.range N, |(θ*x)^i/(i.factorial : ℝ)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.range N) (fun i => (θ*x)^i/(i.factorial : ℝ))
    _=∑ i ∈ Finset.range N, |θ*x|^i/(i.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [abs_div,abs_pow,abs_of_nonneg (Nat.cast_nonneg i.factorial : (0 : ℝ)≤_)]
    _≤∑' i : ℕ, |θ*x|^i/(i.factorial : ℝ) := hs.summable.sum_le_tsum _ (fun i hi => by positivity)
    _=Real.exp |θ*x| := hs.tsum_eq

theorem absolute_exp_memLp_two (θ : ℝ) : MemLp (fun x : ℝ => Real.exp |θ*x|) 2 γ := by
  apply ((gaussian_exp_memLp_two θ).add (gaussian_exp_memLp_two (-θ))).mono' (by fun_prop)
  apply Eventually.of_forall
  intro x
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  by_cases hx : 0≤θ*x
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos (le_of_not_ge hx)]
    simpa only [neg_mul,Pi.add_apply] using le_add_of_nonneg_left (Real.exp_pos (θ*x)).le

theorem taylorClass_tendsto (θ : ℝ) : Tendsto (fun N => polynomialL2 (taylorPolynomial θ N))
    atTop (𝓝 (classTwo θ)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun (N : ℕ) (x : ℝ) => (taylorPolynomial θ N).eval x)
    (fun N => polynomial_memLp (taylorPolynomial θ N) 2 (by simp))
    (fun x => Real.exp (θ*x)) (gaussian_exp_memLp_two θ)).2
  have hc : UnifIntegrable (fun _ : ℕ => fun x : ℝ => Real.exp |θ*x|) 2 γ :=
    unifIntegrable_const (by norm_num) (by simp) (absolute_exp_memLp_two θ)
  have hui : UnifIntegrable (fun (N : ℕ) (x : ℝ) => (taylorPolynomial θ N).eval x) 2 γ := by
    apply hc.ae_mono (fun _ => by fun_prop)
    intro N
    apply Eventually.of_forall
    intro x
    rw [enorm_le_iff_norm_le]
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using taylor_eval_bound θ x N
  have ht (x : ℝ) : Tendsto (fun N => (taylorPolynomial θ N).eval x) atTop (𝓝 (Real.exp (θ*x))) := by
    simpa only [taylor_eval] using (exp_series (θ*x)).tendsto_sum_nat
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by simp)
    (fun _ => by fun_prop) (gaussian_exp_memLp_two θ) hui (Eventually.of_forall ht)

theorem taylor_derivative (θ : ℝ) (N : ℕ) :
    (taylorPolynomial θ (N+1)).derivative=θ • taylorPolynomial θ N := by
  rw [taylorPolynomial,Polynomial.derivative_sum,Finset.sum_range_succ']
  simp only [Polynomial.derivative_C_mul_X_pow,Nat.add_sub_cancel,Nat.cast_zero,mul_zero,
    Polynomial.C_0,zero_mul,add_zero]
  rw [taylorPolynomial,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.smul_eq_C_mul,← mul_assoc,← Polynomial.C_mul]
  congr 1
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp

theorem exponential_derivative_graph (θ : ℝ) : (classTwo θ,θ • classTwo θ)∈closedDerivative.graph := by
  have ht := (taylorClass_tendsto θ).comp (tendsto_add_atTop_nat 1)
  have hd := (taylorClass_tendsto θ).const_smul θ
  apply closedDerivative_isClosed.mem_of_tendsto (ht.prodMk_nhds hd)
  apply Eventually.of_forall
  intro N
  have hg := closedDerivative_polynomial_graph (taylorPolynomial θ (N+1))
  rw [taylor_derivative] at hg
  change (polynomialL2 (taylorPolynomial θ (N+1)),polynomialEmbedding (θ • taylorPolynomial θ N))∈_ at hg
  rw [map_smul] at hg
  exact hg

theorem exponential_hasDerivAt (θ x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (θ*y)) (θ*Real.exp (θ*x)) x := by
  simpa only [id_eq,mul_comm,mul_one] using ((hasDerivAt_id x).const_mul θ).exp

theorem no_graph_norm_L4_bound (K : ℝ) :
    ∃ θ : ℝ, K*(‖classTwo θ‖+‖θ • classTwo θ‖)<‖classFour θ‖ := by
  let θ := |K|+1
  have hθ : 0<θ := by dsimp [θ]; positivity
  refine ⟨θ, ?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hθ,classTwo_norm,classFour_norm]
  have hle : K*(1+θ)<Real.exp (θ^2) := by
    have hh := Real.add_one_le_exp (θ^2)
    have ha := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity : 0≤1+θ)
    dsimp [θ] at *
    nlinarith
  have hm := mul_lt_mul_of_pos_right hle (Real.exp_pos (θ^2))
  have he : Real.exp (θ^2)*Real.exp (θ^2)=Real.exp (2*θ^2) := by rw [← Real.exp_add]; congr 1; ring
  rw [he] at hm
  nlinarith

theorem admitted_graph_L4_counterexample (K : ℝ) :
    ∃ θ : ℝ, (classTwo θ,θ • classTwo θ)∈closedDerivative.graph ∧
      K*(‖classTwo θ‖+‖θ • classTwo θ‖)<‖classFour θ‖ := by
  obtain ⟨θ,hθ⟩ := no_graph_norm_L4_bound K
  exact ⟨θ,exponential_derivative_graph θ,hθ⟩

end OperatorDerivativeRewrite.Foundation.GaussianExponentialSobolevObstruction
