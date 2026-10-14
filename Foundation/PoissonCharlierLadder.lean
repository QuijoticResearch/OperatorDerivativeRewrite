import Foundation.PoissonPolynomialExamples
import Foundation.PoissonAdjoints

/-! Charlier polynomials reconstructed through the ACTUAL maximal Poisson
adjoint pair. The weighted field measure retains the Poisson rate. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.PoissonCharlierLadder
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonCoordinateEvaluation PoissonWeightedDomains PoissonMoments PoissonAdjoints

def polynomial (rate : ℝ≥0) : ℕ → Polynomial ℝ
  | 0 => 1
  | n+1 => Polynomial.X * (polynomial rate n).comp (Polynomial.X - 1) -
      Polynomial.C (rate : ℝ) * polynomial rate n

def value (rate : ℝ≥0) (n : ℕ) (x : ℝ) : ℝ := (polynomial rate n).eval x

theorem value_zero (rate : ℝ≥0) (x : ℝ) : value rate 0 x = 1 := by
  simp [value, polynomial]

theorem value_succ (rate : ℝ≥0) (n : ℕ) (x : ℝ) :
    value rate (n+1) x = x*value rate n (x-1) - rate*value rate n x := by
  simp [value, polynomial, Polynomial.eval_comp]

theorem value_lowering (rate : ℝ≥0) (n : ℕ) (x : ℝ) :
    value rate (n+1) (x+1) - value rate (n+1) x = (n+1 : ℝ)*value rate n x := by
  induction n generalizing x with
  | zero => simp [value_succ, value_zero]
  | succ n ih =>
    have hx := ih x
    have hm := ih (x-1)
    rw [show x-1+1=x by ring] at hm
    have he := value_succ rate n x
    rw [value_succ rate (n+1) (x+1), value_succ rate (n+1) x]
    rw [show x+1-1=x by ring]
    rw [show value rate (n+1) (x+1) = value rate (n+1) x +
      (n+1 : ℝ)*value rate n x by linarith]
    rw [show value rate (n+1) (x-1) = value rate (n+1) x -
      (n+1 : ℝ)*value rate n (x-1) by linarith]
    push_cast
    linear_combination -((n+1 : ℝ))*he

theorem value_memLp (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    MemLp (fun k : ℕ => value rate n k) 2 (poissonLaw rate) :=
  polynomial_memLp_two rate hr (polynomial rate n)

theorem value_field_memLp (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    MemLp (fun k : ℕ => value rate n k) 2 ((rate : ℝ≥0∞) • poissonLaw rate) :=
  (value_memLp rate hr n).smul_measure (by finiteness)

def scalar (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) : ScalarL2 rate :=
  (value_memLp rate hr n).toLp (fun k : ℕ => value rate n k)

def field (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) : FieldL2 rate :=
  (value_field_memLp rate hr n).toLp (fun k : ℕ => value rate n k)

theorem scalar_apply (rate : ℝ≥0) (hr : 0 < rate) (n k : ℕ) :
    scalar rate hr n k = value rate n k :=
  ae_eq_implies_pointwise rate hr (MemLp.coeFn_toLp (value_memLp rate hr n)) k

theorem field_apply (rate : ℝ≥0) (hr : 0 < rate) (n k : ℕ) :
    field rate hr n k = value rate n k :=
  weighted_ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (value_field_memLp rate hr n)) k

theorem lowering_graph (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    (scalar rate hr (n+1), (n+1 : ℝ) • field rate hr n) ∈
      (maximalDifference rate hr).graph := by
  rw [maximalDifference_graph]
  intro k
  rw [field_smul_apply rate hr, field_apply, scalar_apply, scalar_apply]
  simpa only [Nat.cast_add, Nat.cast_one] using (value_lowering rate n (k : ℝ)).symm

theorem raising_graph (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    (field rate hr n, scalar rate hr (n+1)) ∈ (maximalDivergence rate hr).graph := by
  rw [maximalDivergence_graph]
  intro k
  rw [scalar_apply]
  cases k with
  | zero => simp [maximalDivergenceExpr, field_apply, value_succ]
  | succ k =>
    simp only [maximalDivergenceExpr, field_apply, value_succ, Nat.cast_add, Nat.cast_one]
    rw [show (k : ℝ)+1-1=k by ring]

theorem number_eigen_graph (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    ∃ g : FieldL2 rate,
      (scalar rate hr (n+1), g) ∈ (maximalDifference rate hr).graph ∧
      (g, (n+1 : ℝ) • scalar rate hr (n+1)) ∈ (maximalDivergence rate hr).graph :=
  ⟨_, lowering_graph rate hr n, (maximalDivergence rate hr).graph.smul_mem _
    (raising_graph rate hr n)⟩

theorem graph_duality (rate : ℝ≥0) (hr : 0 < rate)
    {f v : ScalarL2 rate} {g u : FieldL2 rate}
    (hf : (f,g) ∈ (maximalDifference rate hr).graph)
    (hu : (u,v) ∈ (maximalDivergence rate hr).graph) :
    inner ℝ g u = inner ℝ f v := by
  rw [← maximalDifference_adjoint_eq_maximalDivergence,
    LinearPMap.adjoint_graph_eq_graph_adjoint
      ((coreDifference_dense_domain rate hr).mono (coreDifference_le_maximal rate hr).1)] at hu
  exact sub_eq_zero.mp ((Submodule.mem_adjoint_iff _ _).mp hu f g hf)

theorem eigen_graph (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    ∃ g : FieldL2 rate,
      (scalar rate hr n,g) ∈ (maximalDifference rate hr).graph ∧
      (g,(n : ℝ) • scalar rate hr n) ∈ (maximalDivergence rate hr).graph := by
  cases n with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · rw [maximalDifference_graph]
      intro k
      change (0 : FieldL2 rate) k = _
      rw [field_zero_apply rate hr, scalar_apply, scalar_apply, value_zero, value_zero]
      ring
    · simpa using (maximalDivergence rate hr).graph.zero_mem
  | succ n => simpa only [Nat.cast_add, Nat.cast_one] using number_eigen_graph rate hr n

/-- Orthogonality is derived from the closed adjoint pair, not imported as
a special-function assertion. -/
theorem scalar_orthogonal (rate : ℝ≥0) (hr : 0 < rate) (n m : ℕ) (hnm : n ≠ m) :
    inner ℝ (scalar rate hr n) (scalar rate hr m) = 0 := by
  obtain ⟨g,hg,hgn⟩ := eigen_graph rate hr n
  obtain ⟨u,hu,hum⟩ := eigen_graph rate hr m
  have h := graph_duality rate hr hg hum
  have k := graph_duality rate hr hu hgn
  rw [inner_smul_right] at h k
  rw [real_inner_comm g u, real_inner_comm (scalar rate hr n) (scalar rate hr m)] at k
  have hnm' : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
  exact (mul_eq_zero.mp (show ((n : ℝ)-m)*inner ℝ (scalar rate hr n)
    (scalar rate hr m) = 0 by nlinarith)).resolve_left (sub_ne_zero.mpr hnm')

theorem field_inner (rate : ℝ≥0) (hr : 0 < rate) (n m : ℕ) :
    inner ℝ (field rate hr n) (field rate hr m) =
      (rate : ℝ)*inner ℝ (scalar rate hr n) (scalar rate hr m) := by
  rw [L2_inner_eq_integral, integral_smul_measure, L2_inner_eq_integral]
  simp only [ENNReal.coe_toReal, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun k => by
    change inner ℝ (field rate hr n k) (field rate hr m k) =
      inner ℝ (scalar rate hr n k) (scalar rate hr m k)
    rw [field_apply, field_apply, scalar_apply, scalar_apply]

theorem scalar_norm_sq_succ (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    ‖scalar rate hr (n+1)‖^2 = (n+1 : ℝ)*(rate : ℝ)*‖scalar rate hr n‖^2 := by
  have h := graph_duality rate hr (lowering_graph rate hr n) (raising_graph rate hr n)
  rw [real_inner_smul_left, field_inner, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at h
  nlinarith [h]

theorem scalar_norm_sq (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    ‖scalar rate hr n‖^2 = (n.factorial : ℝ)*(rate : ℝ)^n := by
  induction n with
  | zero =>
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
    have he : (fun k => inner ℝ (scalar rate hr 0 k) (scalar rate hr 0 k)) =
        fun _ : ℕ => (1 : ℝ) := by
      funext k
      simp [scalar_apply, value_zero]
    rw [he]
    simp
  | succ n ih =>
    rw [scalar_norm_sq_succ, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, pow_succ]
    ring

theorem scalar_inner (rate : ℝ≥0) (hr : 0 < rate) (n m : ℕ) :
    inner ℝ (scalar rate hr n) (scalar rate hr m) =
      if n=m then (n.factorial : ℝ)*(rate : ℝ)^n else 0 := by
  split_ifs with h
  · subst m
    rw [real_inner_self_eq_norm_sq, scalar_norm_sq]
  · exact scalar_orthogonal rate hr n m h

end OperatorDerivativeRewrite.Foundation.PoissonCharlierLadder
