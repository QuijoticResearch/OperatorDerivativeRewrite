import Foundation.PoissonPolynomialDensity
import Foundation.PoissonCharlierLadder

/-! Algebraic ladder spanning and completeness in the actual Poisson L2 space. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonCharlierCompleteness
open PoissonDifferenceCore PoissonDifferenceOperators PoissonCoordinateEvaluation
open PoissonCharlierLadder PoissonPolynomialDensity

theorem X_mul_zero (rate : ℝ≥0) :
    Polynomial.X * polynomial rate 0 = polynomial rate 1 + (rate : ℝ) • polynomial rate 0 := by
  simp [polynomial,Polynomial.smul_eq_C_mul]

theorem X_mul_succ (rate : ℝ≥0) (n : ℕ) :
    Polynomial.X * polynomial rate (n+1) = polynomial rate (n+2) +
      ((rate : ℝ)+(n+1 : ℝ)) • polynomial rate (n+1) +
      ((rate : ℝ)*(n+1 : ℝ)) • polynomial rate n := by
  apply Polynomial.funext
  intro x
  have hl := value_lowering rate n (x-1)
  rw [show x-1+1=x by ring] at hl
  have hn := value_succ rate n x
  have hs := value_succ rate (n+1) x
  simp only [Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_add,Polynomial.eval_smul,
    smul_eq_mul]
  change x*value rate (n+1) x = value rate (n+2) x +
    (rate+(n+1 : ℝ))*value rate (n+1) x + (rate*(n+1 : ℝ))*value rate n x
  linear_combination -hs - (n+1 : ℝ)*hn + x*hl

def algebraicSpan (rate : ℝ≥0) : Submodule ℝ (Polynomial ℝ) :=
  Submodule.span ℝ (Set.range (polynomial rate))

theorem X_mul_mem (rate : ℝ≥0) (p : Polynomial ℝ) (hp : p ∈ algebraicSpan rate) :
    Polynomial.X*p ∈ algebraicSpan rate := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n,rfl⟩ := hp
    have hm (i : ℕ) : polynomial rate i ∈ algebraicSpan rate := Submodule.subset_span ⟨i,rfl⟩
    cases n with
    | zero =>
      rw [X_mul_zero]
      exact (algebraicSpan rate).add_mem (hm 1)
        ((algebraicSpan rate).smul_mem _ (hm 0))
    | succ n =>
      rw [X_mul_succ]
      exact (algebraicSpan rate).add_mem
        ((algebraicSpan rate).add_mem (hm (n+2)) ((algebraicSpan rate).smul_mem _ (hm (n+1))))
        ((algebraicSpan rate).smul_mem _ (hm n))
  | zero => simp
  | add p q hp hq ihp ihq => rw [mul_add]; exact (algebraicSpan rate).add_mem ihp ihq
  | smul c p hp ih => rw [mul_smul_comm]; exact (algebraicSpan rate).smul_mem c ih

theorem algebraicSpan_eq_top (rate : ℝ≥0) : algebraicSpan rate=⊤ := by
  have hAll (p : Polynomial ℝ) : p ∈ algebraicSpan rate := by
    induction p using Polynomial.induction_on with
    | C c =>
      have h : polynomial rate 0 ∈ algebraicSpan rate := Submodule.subset_span ⟨0,rfl⟩
      simpa only [polynomial,Polynomial.smul_eq_C_mul,mul_one] using
        (algebraicSpan rate).smul_mem c h
    | add p q hp hq => exact (algebraicSpan rate).add_mem hp hq
    | monomial n c ih =>
      convert X_mul_mem rate _ ih using 1 <;> ring
  exact top_unique (fun p _ => hAll p)

def polynomialEmbedding (rate : ℝ≥0) (hr : 0 < rate) : Polynomial ℝ →ₗ[ℝ] ScalarL2 rate where
  toFun := polynomialClass rate hr
  map_add' p q := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (PoissonMoments.polynomial_memLp_two rate hr (p+q)),
      MemLp.coeFn_toLp (PoissonMoments.polynomial_memLp_two rate hr p),
      MemLp.coeFn_toLp (PoissonMoments.polynomial_memLp_two rate hr q),
      Lp.coeFn_add (polynomialClass rate hr p) (polynomialClass rate hr q)] with k ha hp hq hs
    change polynomialClass rate hr (p+q) k = _ at ha
    change polynomialClass rate hr p k = _ at hp
    change polynomialClass rate hr q k = _ at hq
    rw [ha,hs]
    simp only [Pi.add_apply,Polynomial.eval_add]
    rw [hp,hq]
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (PoissonMoments.polynomial_memLp_two rate hr (c • p)),
      MemLp.coeFn_toLp (PoissonMoments.polynomial_memLp_two rate hr p),
      Lp.coeFn_smul c (polynomialClass rate hr p)] with k ha hp hs
    change polynomialClass rate hr (c • p) k = _ at ha
    change polynomialClass rate hr p k = _ at hp
    change polynomialClass rate hr (c • p) k = (c • polynomialClass rate hr p) k
    rw [ha,hs]
    simp only [Pi.smul_apply,Polynomial.eval_smul,smul_eq_mul]
    rw [hp]

theorem polynomialEmbedding_ladder (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    polynomialEmbedding rate hr (polynomial rate n)=PoissonCharlierLadder.scalar rate hr n := rfl

def scalarSpan (rate : ℝ≥0) (hr : 0 < rate) : Submodule ℝ (ScalarL2 rate) :=
  Submodule.span ℝ (Set.range (PoissonCharlierLadder.scalar rate hr))

theorem scalarSpan_closure (rate : ℝ≥0) (hr : 0 < rate) :
    (scalarSpan rate hr).topologicalClosure=⊤ := by
  have hs : polynomialSpan rate hr ≤ scalarSpan rate hr := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    have hp : p ∈ algebraicSpan rate := by rw [algebraicSpan_eq_top]; trivial
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨n,rfl⟩ := hp
      exact Submodule.subset_span ⟨n,rfl⟩
    | zero => change polynomialEmbedding rate hr 0 ∈ _; simp
    | add p q hp hq ihp ihq =>
      change polynomialEmbedding rate hr (p+q) ∈ _
      rw [map_add]; exact (scalarSpan rate hr).add_mem ihp ihq
    | smul c p hp ih =>
      change polynomialEmbedding rate hr (c • p) ∈ _
      rw [map_smul]; exact (scalarSpan rate hr).smul_mem c ih
  have hc := Submodule.topologicalClosure_mono hs
  rw [polynomialSpan_closure rate hr] at hc
  exact le_antisymm le_top hc

end OperatorDerivativeRewrite.Foundation.PoissonCharlierCompleteness
