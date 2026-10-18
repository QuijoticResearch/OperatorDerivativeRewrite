import Foundation.MultivariateFactorialHeat
import Foundation.MultivariateFactorialSubstitution
import Foundation.FactorialAnalyticHeat
import Mathlib.Algebra.MvPolynomial.Funext

/-! Actual complete directional heat operators and their finite signed-kernel realization. -/
noncomputable section

open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MultivariateDirectionalKernel
open MultivariateFactorialDomain MultivariatePolynomialNilpotence MultivariateFactorialHeat
open MultivariateFactorialSubstitution
variable {ι : Type*}

def line (v x : ι → ℝ) : MvPolynomial ι ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X)

theorem line_C (v x : ι → ℝ) (c : ℝ) : line v x (MvPolynomial.C c) = Polynomial.C c := by
  simp [line]

theorem line_X (v x : ι → ℝ) (i : ι) :
    line v x (MvPolynomial.X i) = Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X := by
  rw [line, MvPolynomial.aeval_X]

theorem eval_line (v x : ι → ℝ) (P : MvPolynomial ι ℝ) (z : ℝ) :
    (line v x P).eval z = MvPolynomial.eval (fun i => x i + z * v i) P := by
  have he : (Polynomial.aeval z).comp (line v x) =
      MvPolynomial.aeval (fun i => x i + z * v i) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, line_X, MvPolynomial.aeval_X, map_add, map_mul]
    simp only [Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  exact AlgHom.congr_fun he P

theorem derivative_line (v x : ι → ℝ) (P : MvPolynomial ι ℝ) :
    Polynomial.derivative (line v x P) = line v x (polynomialDerivative v P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [line_C, Polynomial.derivative_C, polynomialDerivative_C]
    exact (map_zero (line v x)).symm
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, Polynomial.derivative_mul, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    rw [hP, polynomialDerivative_X, line_C, line_X]
    simp
    ring

theorem iterate_derivative_line (v x : ι → ℝ) (P : MvPolynomial ι ℝ) (r : ℕ) :
    Polynomial.derivative^[r] (line v x P) =
      line v x ((polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r] P) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', ih, derivative_line,
      Function.iterate_succ_apply']

theorem line_coordinate (v x : ι → ℝ) (P : MvPolynomial ι ℝ) (r : ℕ) :
    FactorialAnalyticDomain.polynomial (line v x P) r =
      MvPolynomial.eval x ((polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r] P) := by
  rw [FactorialAnalyticHeat.polynomial_coordinate_derivative,
    iterate_derivative_line, eval_line]
  simp only [zero_mul, add_zero]

theorem expectation_series (p : ℕ) (hp : 0 < p) (a : ℝ) (v x : ι → ℝ) (P : MvPolynomial ι ℝ) :
    HasSum (fun k : ℕ => (a^k/(k.factorial:ℝ)) *
      MvPolynomial.eval x ((polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[p*k] P))
      (PseudoPolynomialStein.expectation p a (line v x P)) := by
  have hs := FactorialAnalyticHeat.series_coordinate p a
    (FactorialAnalyticDomain.polynomial (line v x P)) 0
  convert hs using 1
  · funext k
    rw [zero_add, line_coordinate]
  · change _ = FactorialAnalyticHeat.mean p a (FactorialAnalyticDomain.polynomial (line v x P))
    rw [FactorialAnalyticHeat.mean_polynomial p hp]

open Classical in
theorem expectation_polynomialEvolution (p : ℕ) (hp : 0 < p) (a : ℝ)
    (v x : ι → ℝ) (P : MvPolynomial ι ℝ) :
    PseudoPolynomialStein.expectation p a (line v x P) =
      MvPolynomial.eval x (polynomialEvolution p a v P) := by
  have hs := expectation_series p hp a v x P
  have hf := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range (P.totalDegree+1))
    (f := fun k : ℕ => (a^k/(k.factorial:ℝ)) *
      MvPolynomial.eval x ((polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[p*k] P))
    (fun k hk => by
      have hk' : P.totalDegree < p*k := by
        have he : P.totalDegree+1 ≤ k := Nat.le_of_not_gt (by simpa using hk)
        have hpk : k ≤ p*k := by nlinarith
        omega
      rw [iterate_zero v P (p*k) hk', map_zero, mul_zero])
  rw [hs.unique hf]
  simp only [polynomialEvolution, map_sum, MvPolynomial.smul_eval]

open MeasureTheory in
theorem actual_kernel_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (v x : ι → ℝ) (P : MvPolynomial ι ℝ) :
    Integrable (fun z : ℝ => MvPolynomial.eval (fun i => x i + z * v i) P *
      HigherHeatSignedLaws.realKernel m hm t ht z) := by
  simpa only [eval_line] using
    HigherHeatPolynomialRealization.polynomial_integrable m hm t ht (line v x P)

open MeasureTheory in
open Classical in
theorem actual_kernel_evolution (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (v x : ι → ℝ) (P : MvPolynomial ι ℝ) :
    (∫ z : ℝ, MvPolynomial.eval (fun i => x i + z * v i) P *
      HigherHeatSignedLaws.realKernel m hm t ht z) =
      MvPolynomial.eval x (polynomialEvolution (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) v P) := by
  have he := LinearMap.congr_fun
    (HigherHeatPolynomialRealization.kernelExpectation_eq_moments m hm t ht)
    (line v x P)
  change (∫ z : ℝ, (line v x P).eval z * HigherHeatSignedLaws.realKernel m hm t ht z) = _ at he
  simpa only [eval_line, expectation_polynomialEvolution (2*m) (by omega)] using he

open Classical in
def transport (p : ℕ) (hp : 0 < p) (a : ℝ) (v : ι → ℝ) :
    MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ where
  toFun := polynomialEvolution p a v
  map_add' P Q := by
    apply MvPolynomial.funext
    intro x
    rw [map_add, ← expectation_polynomialEvolution p hp, ← expectation_polynomialEvolution p hp,
      ← expectation_polynomialEvolution p hp]
    simp only [map_add]
  map_smul' c P := by
    apply MvPolynomial.funext
    intro x
    rw [← expectation_polynomialEvolution p hp]
    simp only [map_smul, RingHom.id_apply, MvPolynomial.smul_eval, smul_eq_mul]
    rw [← expectation_polynomialEvolution p hp]

theorem completed_transport [DecidableEq ι] (p : ℕ) (hp : 0 < p) (a : ℝ)
    (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (P : MvPolynomial ι ℝ) :
    evolution p a v hv (polynomial P) = polynomial (transport p hp a v P) :=
  evolution_polynomial p hp a v hv P

open MeasureTheory in
theorem actual_kernel_transport (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (v x : ι → ℝ) (P : MvPolynomial ι ℝ) :
    (∫ z : ℝ, MvPolynomial.eval (fun i => x i + z * v i) P *
      HigherHeatSignedLaws.realKernel m hm t ht z) =
      MvPolynomial.eval x (transport (2*m) (by omega) ((-1:ℝ)^(m+1)*(t:ℝ)) v P) :=
  actual_kernel_evolution m hm t ht v x P

theorem actual_transport_bound (m : ℕ) (hm : 0 < m) (t : ℝ≥0)
    (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (P : MvPolynomial ι ℝ) :
    ‖polynomial (transport (2*m) (by omega) ((-1:ℝ)^(m+1)*(t:ℝ)) v P)‖ ≤
      Real.exp (t:ℝ) * ‖polynomial P‖ := by
  classical
  change ‖polynomial (polynomialEvolution (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) v P)‖ ≤ _
  have h := polynomialEvolution_bound (2*m) (by omega) ((-1:ℝ)^(m+1)*(t:ℝ)) v hv P
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg t.coe_nonneg] using h

end OperatorDerivativeRewrite.Foundation.MultivariateDirectionalKernel
