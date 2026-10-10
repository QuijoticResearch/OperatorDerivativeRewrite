import Foundation.GaussianCore
import Foundation.MultiplierCore
import Mathlib.Algebra.Polynomial.Roots

/-! The genuine polynomial derivative as an operator in Gaussian L². -/
noncomputable section
open MeasureTheory Polynomial
namespace OperatorDerivativeRewrite.Foundation.GaussianCore
set_option backward.isDefEq.respectTransparency false

abbrev GaussianL2 := Lp ℝ 2 γ

/-- Polynomial evaluation as an actual Gaussian L² equivalence class. -/
def polynomialL2 (p : ℝ[X]) : GaussianL2 :=
  (polynomial_memLp p 2 (by simp)).toLp (fun x => p.eval x)

theorem polynomialL2_coeFn (p : ℝ[X]) :
    polynomialL2 p =ᵐ[γ] fun x => p.eval x := MemLp.coeFn_toLp _

/-- Evaluation into Gaussian L² is linear. -/
def polynomialEmbedding : ℝ[X] →ₗ[ℝ] GaussianL2 where
  toFun := polynomialL2
  map_add' p q := by
    apply Lp.ext
    filter_upwards [polynomialL2_coeFn (p + q), polynomialL2_coeFn p,
      polynomialL2_coeFn q, Lp.coeFn_add (polynomialL2 p) (polynomialL2 q)] with x h1 h2 h3 h4
    rw [h1, h4]; simp only [Pi.add_apply, h2, h3, eval_add]
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [polynomialL2_coeFn (c • p), polynomialL2_coeFn p,
      Lp.coeFn_smul c (polynomialL2 p)] with x h1 h2 h3
    change (polynomialL2 (c • p)) x = (c • polynomialL2 p) x
    rw [h1, h3]; simp only [Pi.smul_apply, h2, eval_smul]

/-- Nondegeneracy of Gaussian measure makes polynomial representations unique. -/
theorem polynomialEmbedding_injective : Function.Injective polynomialEmbedding := by
  intro p q h
  change polynomialL2 p = polynomialL2 q at h
  have ha : (fun x => p.eval x) =ᵐ[γ] (fun x => q.eval x) :=
    (polynomialL2_coeFn p).symm.trans (h ▸ polynomialL2_coeFn q)
  exact Polynomial.funext (congrFun (continuous_representation_unique p.continuous q.continuous ha))

/-- Hilbert pairing of polynomial classes equals the actual Gaussian integral. -/
theorem polynomialL2_inner (p q : ℝ[X]) :
    inner ℝ (polynomialL2 p) (polynomialL2 q) = ∫ x, p.eval x * q.eval x ∂γ := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [polynomialL2_coeFn p, polynomialL2_coeFn q] with x hp hq
  rw [hp, hq]; simp only [Real.inner_apply]

/-- IBP expressed in the genuine Gaussian L² Hilbert space. -/
theorem polynomialL2_integration_by_parts (p q : ℝ[X]) :
    inner ℝ (polynomialL2 p.derivative) (polynomialL2 q) =
      inner ℝ (polynomialL2 p) (polynomialL2 (divergencePolynomial q)) := by
  rw [polynomialL2_inner, polynomialL2_inner, polynomial_integration_by_parts]

/-- Graph consists precisely of actual polynomial functions and actual derivatives. -/
def derivativeGraph : Submodule ℝ (GaussianL2 × GaussianL2) :=
  LinearMap.range (polynomialEmbedding.prod (polynomialEmbedding.comp derivative))

theorem derivativeGraph_vertical_zero (z : GaussianL2 × GaussianL2)
    (hz : z ∈ derivativeGraph) (hzero : z.1 = 0) : z.2 = 0 := by
  obtain ⟨p, hp⟩ := hz
  subst z
  have hp0 : p = 0 := polynomialEmbedding_injective (by simpa using hzero)
  change polynomialEmbedding (derivative p) = 0
  rw [hp0, map_zero, map_zero]

/-- The derivative has the algebraic polynomial domain, separate from graph closure. -/
def polynomialDerivative : GaussianL2 →ₗ.[ℝ] GaussianL2 := derivativeGraph.toLinearPMap

theorem polynomialDerivative_graph : polynomialDerivative.graph = derivativeGraph :=
  derivativeGraph.toLinearPMap_graph_eq derivativeGraph_vertical_zero

/-- Membership includes the true derivative, with no independently chosen coefficient. -/
theorem polynomialDerivative_polynomial (p : ℝ[X]) :
    (polynomialL2 p, polynomialL2 p.derivative) ∈ polynomialDerivative.graph := by
  rw [polynomialDerivative_graph]
  exact ⟨p, rfl⟩

/-- IBP continues to every element of the closure of the graph by continuity. -/
theorem closed_graph_ibp (z : GaussianL2 × GaussianL2)
    (hz : z ∈ derivativeGraph.topologicalClosure) (q : ℝ[X]) :
    inner ℝ z.2 (polynomialL2 q) = inner ℝ z.1 (polynomialL2 (divergencePolynomial q)) := by
  apply (closure_minimal (s := (derivativeGraph : Set (GaussianL2 × GaussianL2)))
    (t := {z | inner ℝ z.2 (polynomialL2 q) =
      inner ℝ z.1 (polynomialL2 (divergencePolynomial q))}) ?_ ?_) hz
  · rintro z ⟨p, rfl⟩
    exact polynomialL2_integration_by_parts p q
  · exact isClosed_eq (continuous_snd.inner continuous_const)
      (continuous_fst.inner continuous_const)

/-- The closure of the graph still has no nonzero vertical elements. -/
theorem closed_derivativeGraph_vertical_zero (z : GaussianL2 × GaussianL2)
    (hz : z ∈ derivativeGraph.topologicalClosure) (hzero : z.1 = 0) : z.2 = 0 := by
  have hortho (p : ℝ[X]) : inner ℝ z.2 (polynomialL2 p) = 0 := by
    rw [closed_graph_ibp z hz p, hzero, inner_zero_left]
  have hsecond : z.2 ∈ polynomialEmbedding.range.topologicalClosure := by
    apply (closure_minimal
      (s := (derivativeGraph : Set (GaussianL2 × GaussianL2)))
      (t := {w | w.2 ∈ polynomialEmbedding.range.topologicalClosure}) ?_ ?_) hz
    · rintro w ⟨p, rfl⟩
      exact polynomialEmbedding.range.le_topologicalClosure ⟨p.derivative, rfl⟩
    · exact polynomialEmbedding.range.isClosed_topologicalClosure.preimage continuous_snd
  have hself : inner ℝ z.2 z.2 = 0 := by
    apply (closure_minimal (s := (polynomialEmbedding.range : Set GaussianL2))
      (t := {v | inner ℝ z.2 v = 0}) ?_ ?_) hsecond
    · rintro v ⟨p, rfl⟩; exact hortho p
    · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  exact inner_self_eq_zero.mp hself

/-- Genuine closability in all of Gaussian L², proved using IBP and graph limits. -/
theorem polynomialDerivative_isClosable : polynomialDerivative.IsClosable := by
  refine ⟨derivativeGraph.topologicalClosure.toLinearPMap, ?_⟩
  rw [polynomialDerivative_graph,
    Submodule.toLinearPMap_graph_eq _ closed_derivativeGraph_vertical_zero]

/-- The graph closure is an actual closed extension of the genuine derivative. -/
theorem polynomialDerivative_closure_isClosed : polynomialDerivative.closure.IsClosed :=
  polynomialDerivative_isClosable.closure_isClosed

/-- The polynomial divergence is a linear map, not prescribed independent data. -/
def divergenceLinear : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := divergencePolynomial
  map_add' p q := by simp [divergencePolynomial, mul_add]; ring
  map_smul' c p := by simp [divergencePolynomial, smul_sub]

/-- Graph of the genuine Gaussian polynomial divergence. -/
def divergenceGraph : Submodule ℝ (GaussianL2 × GaussianL2) :=
  LinearMap.range (polynomialEmbedding.prod (polynomialEmbedding.comp divergenceLinear))

theorem divergenceGraph_vertical_zero (z : GaussianL2 × GaussianL2)
    (hz : z ∈ divergenceGraph) (hzero : z.1 = 0) : z.2 = 0 := by
  obtain ⟨p, hp⟩ := hz
  subst z
  have hp0 : p = 0 := polynomialEmbedding_injective (by simpa using hzero)
  change polynomialEmbedding (divergenceLinear p) = 0
  rw [hp0, map_zero, map_zero]

/-- Divergence is xq-q' on the algebraic polynomial domain. -/
def polynomialDivergence : GaussianL2 →ₗ.[ℝ] GaussianL2 := divergenceGraph.toLinearPMap

theorem polynomialDivergence_graph : polynomialDivergence.graph = divergenceGraph :=
  divergenceGraph.toLinearPMap_graph_eq divergenceGraph_vertical_zero

/-- The genuine derivative and divergence satisfy the formal-adjoint identity. -/
theorem polynomialDerivative_formalAdjoint :
    polynomialDerivative.IsFormalAdjoint polynomialDivergence := by
  intro f u
  have hf := polynomialDerivative.mem_graph f
  have hu := polynomialDivergence.mem_graph u
  rw [polynomialDerivative_graph] at hf
  rw [polynomialDivergence_graph] at hu
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hu
  have hp1 := congrArg Prod.fst hp
  have hp2 := congrArg Prod.snd hp
  have hq1 := congrArg Prod.fst hq
  have hq2 := congrArg Prod.snd hq
  change polynomialL2 p = (f : GaussianL2) at hp1
  change polynomialL2 p.derivative = polynomialDerivative f at hp2
  change polynomialL2 q = (u : GaussianL2) at hq1
  change polynomialL2 (divergencePolynomial q) = polynomialDivergence u at hq2
  rw [← hp1, ← hp2, ← hq1, ← hq2]
  exact polynomialL2_integration_by_parts p q

/-- Polynomial functions genuinely belong to the divergence's adjoint domain.
No claim about its value is made without establishing density of the divergence domain. -/
theorem polynomial_mem_divergence_adjoint_domain (p : ℝ[X]) :
    polynomialL2 p ∈ polynomialDivergence.adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists
  refine ⟨polynomialL2 p.derivative, ?_⟩
  intro u
  have hu := polynomialDivergence.mem_graph u
  rw [polynomialDivergence_graph] at hu
  obtain ⟨q, hq⟩ := hu
  have hq1 := congrArg Prod.fst hq
  have hq2 := congrArg Prod.snd hq
  change polynomialL2 q = (u : GaussianL2) at hq1
  change polynomialL2 (divergencePolynomial q) = polynomialDivergence u at hq2
  rw [← hq1, ← hq2]
  exact polynomialL2_integration_by_parts p q

/-- Actual L² product closure on the polynomial core, with its genuine derivative. -/
theorem polynomial_product_graph (p q : ℝ[X]) :
    (polynomialL2 (p * q),
      polynomialL2 (p.derivative * q) + polynomialL2 (p * q.derivative)) ∈
      polynomialDerivative.graph := by
  have h := polynomialDerivative_polynomial (p * q)
  rw [derivative_mul] at h
  change (polynomialL2 (p * q), polynomialEmbedding (p.derivative * q + p * q.derivative)) ∈ _ at h
  rw [polynomialEmbedding.map_add] at h
  exact h

/-- Genuine one-coordinate cylinder F=p(W(h)), as a Gaussian L² class. -/
def cylindricalL2 (h : ℝ) (p : ℝ[X]) : GaussianL2 :=
  polynomialL2 (coordinatePolynomial h p)

theorem cylindricalL2_coeFn (h : ℝ) (p : ℝ[X]) :
    cylindricalL2 h p =ᵐ[γ] fun x => p.eval (W h x) := by
  exact (polynomialL2_coeFn (coordinatePolynomial h p)).trans
    (Filter.Eventually.of_forall (coordinatePolynomial_eval h p))

/-- Its derivative class is determined by differentiating its actual pullback polynomial. -/
def cylindricalDerivativeL2 (h : ℝ) (p : ℝ[X]) : GaussianL2 :=
  polynomialL2 (coordinatePolynomial h p).derivative

/-- The actual operator evaluates this cylinder to its genuine derivative. -/
theorem cylindrical_operator_graph (h : ℝ) (p : ℝ[X]) :
    (cylindricalL2 h p, cylindricalDerivativeL2 h p) ∈ polynomialDerivative.graph :=
  polynomialDerivative_polynomial (coordinatePolynomial h p)

/-- The derivative has the Malliavin formula p'(W(h))h almost everywhere. -/
theorem cylindricalDerivativeL2_coeFn (h : ℝ) (p : ℝ[X]) :
    cylindricalDerivativeL2 h p =ᵐ[γ] fun x => p.derivative.eval (W h x) * h := by
  apply (polynomialL2_coeFn (coordinatePolynomial h p).derivative).trans
  apply Filter.Eventually.of_forall
  intro x
  have hd := (coordinatePolynomial h p).hasDerivAt x
  have he : (fun y => (coordinatePolynomial h p).eval y) = (fun y => p.eval (W h y)) :=
    funext (coordinatePolynomial_eval h p)
  rw [he] at hd
  exact hd.unique (cylindrical_hasDerivAt h p x)

/-- Changing both the polynomial and coordinate representation leaves the derivative unchanged. -/
theorem cylindrical_representation_independent (h k : ℝ) (p q : ℝ[X])
    (he : cylindricalL2 h p = cylindricalL2 k q) :
    cylindricalDerivativeL2 h p = cylindricalDerivativeL2 k q := by
  have hp : coordinatePolynomial h p = coordinatePolynomial k q :=
    polynomialEmbedding_injective he
  simp only [cylindricalDerivativeL2, hp]

/-- The basic Gaussian cylinder fails the bounded-multiplier criterion already at L∞. -/
theorem coordinate_not_admissible :
    ¬ IsDivergenceMultiplier polynomialDivergence (fun x : ℝ => x) := by
  rintro ⟨hf, _⟩
  exact coordinate_not_memLp_top hf

/-- Constants do satisfy the verified commutator and domain-preservation criterion. -/
theorem constant_admissible (c : ℝ) :
    IsDivergenceMultiplier polynomialDivergence (fun _ : ℝ => c) :=
  isDivergenceMultiplier_const polynomialDivergence c

/-- Exact algebraic derivative domain: the range of polynomial evaluation in L². -/
theorem polynomialDerivative_domain : polynomialDerivative.domain = polynomialEmbedding.range := by
  ext f
  constructor
  · intro hf
    have hg := polynomialDerivative.mem_graph ⟨f, hf⟩
    rw [polynomialDerivative_graph] at hg
    obtain ⟨p, hp⟩ := hg
    exact ⟨p, congrArg Prod.fst hp⟩
  · rintro ⟨p, rfl⟩
    have hg := polynomialDerivative_polynomial p
    rw [LinearPMap.mem_graph_iff] at hg
    obtain ⟨y, hy, _⟩ := hg
    change (y : GaussianL2) = polynomialEmbedding p at hy
    rw [← hy]; exact y.property

/-- Exact divergence domain: the same algebraic polynomial core. -/
theorem polynomialDivergence_domain : polynomialDivergence.domain = polynomialEmbedding.range := by
  ext f
  constructor
  · intro hf
    have hg := polynomialDivergence.mem_graph ⟨f, hf⟩
    rw [polynomialDivergence_graph] at hg
    obtain ⟨p, hp⟩ := hg
    exact ⟨p, congrArg Prod.fst hp⟩
  · rintro ⟨p, rfl⟩
    have hg : (polynomialL2 p, polynomialL2 (divergencePolynomial p)) ∈
        polynomialDivergence.graph := by
      rw [polynomialDivergence_graph]; exact ⟨p, rfl⟩
    rw [LinearPMap.mem_graph_iff] at hg
    obtain ⟨y, hy, _⟩ := hg
    change (y : GaussianL2) = polynomialEmbedding p at hy
    rw [← hy]; exact y.property

end OperatorDerivativeRewrite.Foundation.GaussianCore
