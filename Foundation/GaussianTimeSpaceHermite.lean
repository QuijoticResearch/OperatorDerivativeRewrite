import Foundation.GaussianChaosCylinders
import Foundation.GaussianQuadraticIncrement

/-! Canonical probabilists' time-space Hermite polynomials and actual Gaussian
cylinders. Raising and lowering use genuine polynomial differentiation. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTimeSpaceHermite
open InfiniteGaussian GaussianNumberSectors GaussianQuadraticIncrement
open GaussianTimePolynomialPairing GaussianTimeFieldNorm

def raise (t : ℝ) (p : MvPolynomial Unit ℝ) : MvPolynomial Unit ℝ :=
  X () * p - t • pderiv () p

theorem raise_smul (t c : ℝ) (p : MvPolynomial Unit ℝ) :
    raise t (c • p) = c • raise t p := by
  simp only [raise, Derivation.map_smul, smul_sub, mul_smul_comm]
  rw [smul_comm t c]

theorem pderiv_raise (t : ℝ) (p : MvPolynomial Unit ℝ) :
    pderiv () (raise t p) = p + raise t (pderiv () p) := by
  simp [raise, pderiv_mul]
  ring

def polynomial (t : ℝ) : ℕ → MvPolynomial Unit ℝ
  | 0 => 1
  | n + 1 => raise t (polynomial t n)

@[simp] theorem polynomial_zero (t : ℝ) : polynomial t 0 = 1 := rfl

theorem polynomial_succ (t : ℝ) (n : ℕ) :
    polynomial t (n + 1) = raise t (polynomial t n) := rfl

@[simp] theorem polynomial_one (t : ℝ) : polynomial t 1 = X () := by
  simp [polynomial_succ, raise]

theorem polynomial_derivative (t : ℝ) (n : ℕ) :
    pderiv () (polynomial t (n + 1)) = (n + 1 : ℝ) • polynomial t n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [polynomial_succ, pderiv_raise, ih, raise_smul, ← polynomial_succ]
    push_cast
    module

theorem polynomial_recursion (t : ℝ) (n : ℕ) :
    polynomial t (n + 2) = X () * polynomial t (n + 1) -
      ((n + 1 : ℝ) * t) • polynomial t n := by
  rw [polynomial_succ, raise, polynomial_derivative, smul_smul, mul_comm t]

@[simp] theorem polynomial_two (t : ℝ) : polynomial t 2 = X () ^ 2 - C t := by
  rw [polynomial_recursion]
  simp [pow_two, Algebra.smul_def]

theorem polynomial_at_zero (n : ℕ) : polynomial 0 n = X () ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [polynomial_succ, raise, ih, pow_succ, mul_comm]

def value (n : ℕ) (x t : ℝ) : ℝ := eval (fun _ : Unit => x) (polynomial t n)

@[simp] theorem value_zero (x t : ℝ) : value 0 x t = 1 := by simp [value]
@[simp] theorem value_one (x t : ℝ) : value 1 x t = x := by simp [value]
@[simp] theorem value_two (x t : ℝ) : value 2 x t = x ^ 2 - t := by simp [value]

theorem value_recursion (n : ℕ) (x t : ℝ) :
    value (n + 2) x t = x * value (n + 1) x t - (n + 1 : ℝ) * t * value n x t := by
  simp [value, polynomial_recursion, smul_eq_mul, mul_assoc]

def core (h : CoefficientSpace) (t : ℝ) (n : ℕ) : polynomialCylindricalDomain :=
  cylinderCore (fun _ : Unit => h) (polynomial t n)

theorem core_coeFn (h : CoefficientSpace) (t : ℝ) (n : ℕ) :
    (core h t n : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => value n (firstChaosEmbedding h ω) t :=
  isonormalCylinderL2_coeFn _ _

theorem core_memLp (h : CoefficientSpace) (t : ℝ) (n : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => value n (firstChaosEmbedding h ω) t) p gaussianProduct :=
  (polynomialDomain_memLp (core h t n) p hp).ae_eq (core_coeFn h t n)

theorem core_derivative (h : CoefficientSpace) (t : ℝ) (n : ℕ) :
    polynomialDerivative (core h t (n + 1)) = (n + 1 : ℝ) • scalarTensor h (core h t n) := by
  rw [core, cylinder_gradient_expansion]
  change (∑ i : Unit, scalarTensor h
    (cylinderCore (fun _ : Unit => h) (pderiv i (polynomial t (n + 1))))) = _
  simp only [Fintype.sum_unique, show (default : Unit) = () from rfl, polynomial_derivative]
  have he : (cylinderCore (fun _ : Unit => h) ((n + 1 : ℝ) • polynomial t n) : GaussianL2) =
      (n + 1 : ℝ) • (core h t n : GaussianL2) := by
    change familyPolynomialEmbedding (fun _ : Unit => h) ((n + 1 : ℝ) • polynomial t n) =
      (n + 1 : ℝ) • familyPolynomialEmbedding (fun _ : Unit => h) (polynomial t n)
    exact map_smul _ _ _
  rw [he, map_smul]

theorem core_zero (h : CoefficientSpace) (t : ℝ) : (core h t 0 : GaussianL2) = gaussianOne := by
  apply Lp.ext
  filter_upwards [core_coeFn h t 0, gaussianOne_coeFn] with ω hc h1
  simp [hc, h1]

theorem core_zero_derivative (h : CoefficientSpace) (t : ℝ) :
    polynomialDerivative (core h t 0) = 0 := by
  have hg := closedCylindricalDerivative_core_graph (core h t 0)
  rw [core_zero] at hg
  exact closedCylindricalDerivative.mem_graph_snd_inj hg
    (by simpa using closedDerivative_constant_graph 1) rfl

theorem core_one (h : CoefficientSpace) (t : ℝ) : core h t 1 = firstChaosPolynomial h := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [core_coeFn h t 1, firstChaosPolynomial_coeFn h] with ω hc hf
  simp [hc, hf]

def wick (h : CoefficientSpace) (n : ℕ) : polynomialCylindricalDomain := core h (‖h‖ ^ 2) n

theorem wick_raising (h : CoefficientSpace) (n : ℕ) :
    (wick h (n + 1) : GaussianL2) = rankDivergence (wick h n) h := by
  apply Lp.ext
  cases n with
  | zero =>
    filter_upwards [core_coeFn h (‖h‖ ^ 2) 1, rankDivergence_coeFn (wick h 0) h,
      core_coeFn h (‖h‖ ^ 2) 0,
      (show polynomialDerivative (wick h 0) = 0 from core_zero_derivative h _)
        ▸ Lp.coeFn_zero CoefficientSpace 2 gaussianProduct] with ω hc hr h0 hd
    simp only [wick] at hr hd ⊢
    rw [hc, hr, h0, hd]
    simp [value]
  | succ n =>
    have hd := core_derivative h (‖h‖ ^ 2) n
    filter_upwards [core_coeFn h (‖h‖ ^ 2) (n + 2),
      rankDivergence_coeFn (wick h (n + 1)) h, core_coeFn h (‖h‖ ^ 2) (n + 1),
      core_coeFn h (‖h‖ ^ 2) n,
      Lp.coeFn_smul (n + 1 : ℝ) (scalarTensor h (core h (‖h‖ ^ 2) n)),
      scalarTensor_coeFn h (core h (‖h‖ ^ 2) n)] with ω hc hr hn hp hs ht
    change (core h (‖h‖ ^ 2) (n + 2) : GaussianL2) ω = _
    rw [hc, hr]
    change value (n + 2) _ _ = (core h (‖h‖ ^ 2) (n + 1) : GaussianL2) ω * _ -
      inner ℝ (polynomialDerivative (core h (‖h‖ ^ 2) (n + 1)) ω) h
    rw [hn, hd, hs]
    simp only [Pi.smul_apply]
    rw [ht, hp, value_recursion]
    simp only [Pi.smul_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring

theorem wick_centered (h : CoefficientSpace) (n : ℕ) :
    inner ℝ gaussianOne (wick h (n + 1) : GaussianL2) = 0 := by
  have hi := polynomialDerivative_rank_pairing oneCore (wick h n) h
  rw [oneCore_derivative, oneCore_eq, ← wick_raising] at hi
  simpa using hi.symm

theorem wick_inner_succ (h k : CoefficientSpace) (n m : ℕ) :
    inner ℝ (wick h (n + 1) : GaussianL2) (wick k (m + 1) : GaussianL2) =
      (n + 1 : ℝ) * inner ℝ h k * inner ℝ (wick h n : GaussianL2) (wick k m : GaussianL2) := by
  have hi := polynomialDerivative_rank_pairing (wick h (n + 1)) (wick k m) k
  rw [← wick_raising] at hi
  change inner ℝ (polynomialDerivative (core h (‖h‖ ^ 2) (n + 1))) _ = _ at hi
  rw [core_derivative, real_inner_smul_left, scalarTensor_pair_inner] at hi
  exact hi.symm.trans (by unfold wick; ring)

/-- All-order covariance, derived from actual Gaussian IBP. Directions may
be arbitrary, correlated, zero, or linearly dependent. -/
theorem wick_inner (h k : CoefficientSpace) (n m : ℕ) :
    inner ℝ (wick h n : GaussianL2) (wick k m : GaussianL2) =
      if n = m then (n.factorial : ℝ) * (inner ℝ h k) ^ n else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero =>
      simp only [wick, core_zero]
      rw [GaussianDeterministicGraphCore.gaussianOne_inner_self]
      norm_num
    | succ m =>
      rw [show (wick h 0 : GaussianL2) = gaussianOne from core_zero h _, wick_centered]
      simp
  | succ n ih =>
    cases m with
    | zero =>
      rw [show (wick k 0 : GaussianL2) = gaussianOne from core_zero k _, real_inner_comm,
        wick_centered]
      simp
    | succ m =>
      rw [wick_inner_succ, ih]
      by_cases hn : n = m
      · subst m
        simp only [ite_true, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      · simp [hn]

theorem wick_norm_sq (h : CoefficientSpace) (n : ℕ) :
    ‖(wick h n : GaussianL2)‖ ^ 2 = (n.factorial : ℝ) * (‖h‖ ^ 2) ^ n := by
  rw [← real_inner_self_eq_norm_sq, wick_inner, if_pos rfl, real_inner_self_eq_norm_sq]

attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

def brownianCore (T : ℝ≥0) (n : ℕ) : polynomialCylindricalDomain :=
  wick (SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
    (GaussianTimeHilbert.timeVector T)) n

theorem brownianCore_coeFn (T : ℝ≥0) (n : ℕ) :
    (brownianCore T n : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => value n (GaussianTimeProcess.process T ω) T := by
  have h := core_coeFn (SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
    (GaussianTimeHilbert.timeVector T))
    (‖SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector T)‖ ^ 2) n
  rw [(SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert).norm_map,
    GaussianTimeHilbert.timeVector_norm_sq] at h
  simp only [brownianCore, wick,
    (SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert).norm_map,
    GaussianTimeHilbert.timeVector_norm_sq]
  exact h

theorem brownianCore_memLp (T : ℝ≥0) (n : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => value n (GaussianTimeProcess.process T ω) T) p gaussianProduct :=
  (polynomialDomain_memLp (brownianCore T n) p hp).ae_eq (brownianCore_coeFn T n)

theorem brownianCore_inner (S T : ℝ≥0) (n m : ℕ) :
    inner ℝ (brownianCore S n : GaussianL2) (brownianCore T m : GaussianL2) =
      if n = m then (n.factorial : ℝ) * (min (S : ℝ) T) ^ n else 0 := by
  rw [brownianCore, brownianCore, wick_inner,
    (SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert).inner_map_map,
    GaussianTimeHilbert.timeVector_inner]

theorem brownianCore_norm_sq (T : ℝ≥0) (n : ℕ) :
    ‖(brownianCore T n : GaussianL2)‖ ^ 2 = (n.factorial : ℝ) * (T : ℝ) ^ n := by
  rw [← real_inner_self_eq_norm_sq, brownianCore_inner, if_pos rfl, min_self]

end OperatorDerivativeRewrite.Foundation.GaussianTimeSpaceHermite
