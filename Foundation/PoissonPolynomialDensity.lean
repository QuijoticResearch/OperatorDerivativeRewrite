import Foundation.PoissonExponentialTotal
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Actual scalar-L2 polynomial density for a positive-rate Poisson law.
Taylor approximations are dominated by a proved L2 exponential majorant. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.PoissonPolynomialDensity
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMoments
open PoissonCoherentVectors PoissonExponentialTotal

def polynomialClass (rate : ℝ≥0) (hr : 0 < rate) (p : Polynomial ℝ) : ScalarL2 rate :=
  (polynomial_memLp_two rate hr p).toLp (fun k : ℕ => p.eval (k : ℝ))

def polynomialSpan (rate : ℝ≥0) (hr : 0 < rate) : Submodule ℝ (ScalarL2 rate) :=
  Submodule.span ℝ (Set.range (polynomialClass rate hr))

def taylorPolynomial (θ : ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range N, Polynomial.C (θ^i/(i.factorial : ℝ))*Polynomial.X^i

theorem taylor_eval (θ : ℝ) (N k : ℕ) :
    (taylorPolynomial θ N).eval (k : ℝ) =
      ∑ i ∈ Finset.range N, (θ*(k : ℝ))^i/(i.factorial : ℝ) := by
  simp only [taylorPolynomial,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow]
  ring

private theorem exp_series (x : ℝ) :
    HasSum (fun i : ℕ => x^i/(i.factorial : ℝ)) (Real.exp x) := by
  simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

theorem taylor_eval_bound (θ : ℝ) (N k : ℕ) :
    |(taylorPolynomial θ N).eval (k : ℝ)| ≤ exponential |θ| k := by
  rw [taylor_eval]
  have hs := exp_series |θ*(k : ℝ)|
  calc
    _ ≤ ∑ i ∈ Finset.range N, |(θ*(k : ℝ))^i/(i.factorial : ℝ)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.range N)
        (fun i => (θ*(k : ℝ))^i/(i.factorial : ℝ))
    _ = ∑ i ∈ Finset.range N, |θ*(k : ℝ)|^i/(i.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [abs_div,abs_pow,abs_of_nonneg (Nat.cast_nonneg i.factorial : (0 : ℝ) ≤ _)]
    _ ≤ ∑' i : ℕ, |θ*(k : ℝ)|^i/(i.factorial : ℝ) :=
      hs.summable.sum_le_tsum _ (fun i _ => by positivity)
    _ = Real.exp |θ*(k : ℝ)| := hs.tsum_eq
    _ = exponential |θ| k := by
      unfold exponential
      simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ _)]

theorem taylorClass_tendsto (rate : ℝ≥0) (hr : 0 < rate) (θ : ℝ) :
    Tendsto (fun N => polynomialClass rate hr (taylorPolynomial θ N)) atTop
      (𝓝 (scalar rate θ)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun N k : ℕ => (taylorPolynomial θ N).eval (k : ℝ))
    (fun N => polynomial_memLp_two rate hr (taylorPolynomial θ N))
    (exponential θ) (exponential_memLp rate θ)).2
  have hc : UnifIntegrable (fun _ : ℕ => exponential |θ|) 2 (poissonLaw rate) :=
    unifIntegrable_const (by norm_num) (by simp) (exponential_memLp rate |θ|)
  have hui : UnifIntegrable (fun N k : ℕ => (taylorPolynomial θ N).eval (k : ℝ))
      2 (poissonLaw rate) := by
    apply hc.ae_mono (fun _ => by fun_prop)
    intro N
    apply Filter.Eventually.of_forall
    intro k
    have hp : 0 < exponential |θ| k := Real.exp_pos _
    rw [enorm_le_iff_norm_le]
    simpa only [Real.norm_eq_abs,abs_of_pos hp] using taylor_eval_bound θ N k
  have ht (k : ℕ) : Tendsto (fun N => (taylorPolynomial θ N).eval (k : ℝ)) atTop
      (𝓝 (exponential θ k)) := by
    simpa only [taylor_eval,exponential] using (exp_series (θ*(k : ℝ))).tendsto_sum_nat
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by simp)
    (fun _ => by fun_prop) (exponential_memLp rate θ) hui (Filter.Eventually.of_forall ht)

/-- Density is now proved for the actual Poisson scalar space, rather than
postulated from the existence of a classical orthogonal polynomial family. -/
theorem polynomialSpan_closure (rate : ℝ≥0) (hr : 0 < rate) :
    (polynomialSpan rate hr).topologicalClosure=⊤ := by
  have he (θ : ℝ) : scalar rate θ ∈ (polynomialSpan rate hr).topologicalClosure := by
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (taylorClass_tendsto rate hr θ)
    exact Filter.Eventually.of_forall fun N => (polynomialSpan rate hr).le_topologicalClosure
      (Submodule.subset_span ⟨taylorPolynomial θ N,rfl⟩)
  have hs : exponentialSpan rate ≤ (polynomialSpan rate hr).topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro _ ⟨θ,rfl⟩
    exact he θ
  have hc := (exponentialSpan rate).topologicalClosure_minimal hs
    (Submodule.isClosed_topologicalClosure _)
  rw [exponentialSpan_closure rate hr] at hc
  exact le_antisymm le_top hc

end OperatorDerivativeRewrite.Foundation.PoissonPolynomialDensity
