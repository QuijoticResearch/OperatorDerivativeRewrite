import Foundation.GaussianHermite

/-! Spectral graph approximations prove the full adjoint identifications. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianCore
set_option backward.isDefEq.respectTransparency false

/-- Genuine Hermite coefficient of a Gaussian L² vector. -/
def hermiteCoefficient (f : GaussianL2) (n : ℕ) : ℝ :=
  inner ℝ (normalizedHermite n) f

/-- Finite Hermite expansion, determined entirely by the input vector. -/
def hermiteTruncation (f : GaussianL2) (N : ℕ) : GaussianL2 :=
  ∑ n ∈ Finset.range N, hermiteCoefficient f n • normalizedHermite n

@[simp] theorem hermiteTruncation_zero (f : GaussianL2) : hermiteTruncation f 0 = 0 := by
  simp [hermiteTruncation]

theorem hermiteTruncation_succ (f : GaussianL2) (N : ℕ) :
    hermiteTruncation f (N + 1) = hermiteTruncation f N +
      hermiteCoefficient f N • normalizedHermite N := by
  exact Finset.sum_range_succ _ _

/-- Completeness supplies convergence in L², with no operator-domain assumption. -/
theorem hermiteTruncation_tendsto (f : GaussianL2) :
    Tendsto (hermiteTruncation f) atTop (𝓝 f) :=
  (hermiteBasis_hasSum f).tendsto_sum_nat

/-- Testing δ₀* against the verified Hermite core determines every derivative coefficient. -/
theorem divergence_adjoint_coefficients {f g : GaussianL2}
    (h : (f, g) ∈ polynomialDivergence.adjoint.graph) (n : ℕ) :
    hermiteCoefficient g n = Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f (n + 1) := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint polynomialDivergence_dense_domain] at h
  have hh := (Submodule.mem_adjoint_iff _ _).mp h _ _
    (normalizedHermite_divergence_graph n)
  simp only [real_inner_smul_left, sub_eq_zero] at hh
  exact hh.symm

/-- Testing D₀* against the constant vector determines its zeroth coefficient. -/
theorem derivative_adjoint_coefficient_zero {f g : GaussianL2}
    (h : (f, g) ∈ polynomialDerivative.adjoint.graph) : hermiteCoefficient g 0 = 0 := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint polynomialDerivative_dense_domain] at h
  have hh := (Submodule.mem_adjoint_iff _ _).mp h _ _
    normalizedHermite_derivative_zero_graph
  simpa [hermiteCoefficient] using hh

/-- All remaining divergence coefficients are likewise determined by the true adjoint equation. -/
theorem derivative_adjoint_coefficients {f g : GaussianL2}
    (h : (f, g) ∈ polynomialDerivative.adjoint.graph) (n : ℕ) :
    hermiteCoefficient g (n + 1) = Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f n := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint polynomialDerivative_dense_domain] at h
  have hh := (Submodule.mem_adjoint_iff _ _).mp h _ _
    (normalizedHermite_derivative_graph n)
  simp only [real_inner_smul_left, sub_eq_zero] at hh
  exact hh.symm

/-- Finite derivative graphs are constructed from the actual lowering action. -/
theorem hermiteTruncation_derivative_graph (f g : GaussianL2)
    (h : ∀ n, hermiteCoefficient g n =
      Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f (n + 1)) (N : ℕ) :
    (hermiteTruncation f (N + 1), hermiteTruncation g N) ∈ polynomialDerivative.graph := by
  induction N with
  | zero =>
    simpa only [hermiteTruncation_succ, hermiteTruncation_zero, zero_add,
      Prod.smul_mk, smul_zero] using
      polynomialDerivative.graph.smul_mem (hermiteCoefficient f 0)
        normalizedHermite_derivative_zero_graph
  | succ N ih =>
    have hn := polynomialDerivative.graph.smul_mem (hermiteCoefficient f (N + 1))
      (normalizedHermite_derivative_graph N)
    have hh := polynomialDerivative.graph.add_mem ih hn
    rw [hermiteTruncation_succ f (N + 1), hermiteTruncation_succ g N, h N]
    convert hh using 1
    simp only [Prod.mk_add_mk, Prod.smul_mk, smul_smul, mul_comm]

/-- Finite divergence graphs are constructed from the actual raising action. -/
theorem hermiteTruncation_divergence_graph (f g : GaussianL2)
    (h0 : hermiteCoefficient g 0 = 0)
    (h : ∀ n, hermiteCoefficient g (n + 1) =
      Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f n) (N : ℕ) :
    (hermiteTruncation f N, hermiteTruncation g (N + 1)) ∈ polynomialDivergence.graph := by
  induction N with
  | zero =>
    simp only [hermiteTruncation_succ, hermiteTruncation_zero, h0, zero_smul, zero_add]
    exact polynomialDivergence.graph.zero_mem
  | succ N ih =>
    have hn := polynomialDivergence.graph.smul_mem (hermiteCoefficient f N)
      (normalizedHermite_divergence_graph N)
    have hh := polynomialDivergence.graph.add_mem ih hn
    rw [hermiteTruncation_succ f N, hermiteTruncation_succ g (N + 1), h N]
    convert hh using 1
    simp only [Prod.mk_add_mk, Prod.smul_mk, smul_smul, mul_comm]

/-- Every vector pair with lowering coefficients lies in the genuine graph closure. -/
theorem closedDerivative_graph_of_coefficients (f g : GaussianL2)
    (h : ∀ n, hermiteCoefficient g n =
      Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f (n + 1)) :
    (f, g) ∈ closedDerivative.graph := by
  rw [← polynomialDerivative_isClosable.graph_closure_eq_closure_graph]
  apply mem_closure_of_tendsto
    (((hermiteTruncation_tendsto f).comp (tendsto_add_atTop_nat 1)).prodMk_nhds
      (hermiteTruncation_tendsto g))
  exact Eventually.of_forall (hermiteTruncation_derivative_graph f g h)

/-- Every vector pair with raising coefficients lies in the genuine divergence graph closure. -/
theorem closedDivergence_graph_of_coefficients (f g : GaussianL2)
    (h0 : hermiteCoefficient g 0 = 0)
    (h : ∀ n, hermiteCoefficient g (n + 1) =
      Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f n) :
    (f, g) ∈ closedDivergence.graph := by
  rw [← polynomialDivergence_isClosable.graph_closure_eq_closure_graph]
  apply mem_closure_of_tendsto
    ((hermiteTruncation_tendsto f).prodMk_nhds
      ((hermiteTruncation_tendsto g).comp (tendsto_add_atTop_nat 1)))
  exact Eventually.of_forall (hermiteTruncation_divergence_graph f g h0 h)

/-- Essential adjointness is proved by explicit finite Hermite graph approximation. -/
theorem closedDerivative_eq_divergence_adjoint :
    closedDerivative = polynomialDivergence.adjoint := by
  apply le_antisymm closedDerivative_le_divergence_adjoint
  apply LinearPMap.le_of_le_graph
  rintro ⟨f, g⟩ h
  exact closedDerivative_graph_of_coefficients f g (divergence_adjoint_coefficients h)

/-- The opposite full identification follows from its own raising approximation argument. -/
theorem closedDivergence_eq_derivative_adjoint :
    closedDivergence = polynomialDerivative.adjoint := by
  apply le_antisymm closedDivergence_le_derivative_adjoint
  apply LinearPMap.le_of_le_graph
  rintro ⟨f, g⟩ h
  exact closedDivergence_graph_of_coefficients f g
    (derivative_adjoint_coefficient_zero h) (derivative_adjoint_coefficients h)

theorem closedDerivative_eq_closedDivergence_adjoint :
    closedDerivative = closedDivergence.adjoint := by
  rw [closedDivergence_adjoint_eq, closedDerivative_eq_divergence_adjoint]

theorem closedDivergence_eq_closedDerivative_adjoint :
    closedDivergence = closedDerivative.adjoint := by
  rw [closedDerivative_adjoint_eq, closedDivergence_eq_derivative_adjoint]

/-- Exact spectral characterization of the closed derivative graph. -/
theorem closedDerivative_graph_iff (f g : GaussianL2) :
    (f, g) ∈ closedDerivative.graph ↔ ∀ n, hermiteCoefficient g n =
      Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f (n + 1) := by
  constructor
  · intro h; rw [closedDerivative_eq_divergence_adjoint] at h
    exact divergence_adjoint_coefficients h
  · exact closedDerivative_graph_of_coefficients f g

/-- Exact spectral characterization of the closed divergence graph, including its zero mode. -/
theorem closedDivergence_graph_iff (f g : GaussianL2) :
    (f, g) ∈ closedDivergence.graph ↔ hermiteCoefficient g 0 = 0 ∧
      ∀ n, hermiteCoefficient g (n + 1) =
        Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f n := by
  constructor
  · intro h; rw [closedDivergence_eq_derivative_adjoint] at h
    exact ⟨derivative_adjoint_coefficient_zero h, derivative_adjoint_coefficients h⟩
  · rintro ⟨h0, h⟩; exact closedDivergence_graph_of_coefficients f g h0 h

end OperatorDerivativeRewrite.Foundation.GaussianCore
