import Foundation.PoissonCoordinateEvaluation

/-! Maximal pointwise Poisson difference and divergence as closed Hilbert operators.
The weighted-moment characterization of their domains is a separate theorem. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonMaximalOperators
open PoissonDifferenceCore PoissonDifferenceOperators PoissonCoordinateEvaluation

variable (rate : ℝ≥0) (hr : 0 < rate)

/-- The maximal difference graph uses the actual representative at every positive-mass atom. -/
def maximalDifferenceGraph : Submodule ℝ (ScalarL2 rate × FieldL2 rate) where
  carrier := {z | ∀ n, z.2 n = z.1 (n + 1) - z.1 n}
  zero_mem' := by
    intro n
    change (0 : FieldL2 rate) n = (0 : ScalarL2 rate) (n + 1) - (0 : ScalarL2 rate) n
    rw [field_zero_apply rate hr, scalar_zero_apply rate hr, scalar_zero_apply rate hr]
    ring
  add_mem' := by
    intro x y hx hy n
    change (x.2 + y.2 : FieldL2 rate) n =
      (x.1 + y.1 : ScalarL2 rate) (n + 1) - (x.1 + y.1 : ScalarL2 rate) n
    rw [field_add_apply rate hr, scalar_add_apply rate hr, scalar_add_apply rate hr]
    linear_combination hx n + hy n
  smul_mem' := by
    intro c x hx n
    change (c • x.2 : FieldL2 rate) n =
      (c • x.1 : ScalarL2 rate) (n + 1) - (c • x.1 : ScalarL2 rate) n
    rw [field_smul_apply rate hr, scalar_smul_apply rate hr,
      scalar_smul_apply rate hr]
    linear_combination c * hx n

/-- The maximal divergence coefficient, with the count-zero boundary explicit. -/
def maximalDivergenceExpr (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => -(rate : ℝ) * u 0
  | n + 1 => (n + 1 : ℝ) * u n - (rate : ℝ) * u (n + 1)

/-- The maximal divergence graph uses the actual field and scalar representatives. -/
def maximalDivergenceGraph : Submodule ℝ (FieldL2 rate × ScalarL2 rate) where
  carrier := {z | ∀ n, z.2 n = maximalDivergenceExpr rate z.1 n}
  zero_mem' := by
    intro n
    cases n with
    | zero =>
        change (0 : ScalarL2 rate) 0 = -(rate : ℝ) * (0 : FieldL2 rate) 0
        rw [scalar_zero_apply rate hr, field_zero_apply rate hr]
        ring
    | succ n =>
        change (0 : ScalarL2 rate) (n + 1) =
          (n + 1 : ℝ) * (0 : FieldL2 rate) n -
            (rate : ℝ) * (0 : FieldL2 rate) (n + 1)
        rw [scalar_zero_apply rate hr, field_zero_apply rate hr,
          field_zero_apply rate hr]
        ring
  add_mem' := by
    intro x y hx hy n
    cases n with
    | zero =>
        change (x.2 + y.2 : ScalarL2 rate) 0 =
          -(rate : ℝ) * (x.1 + y.1 : FieldL2 rate) 0
        rw [scalar_add_apply rate hr, field_add_apply rate hr]
        have hxn := hx 0
        have hyn := hy 0
        simp only [maximalDivergenceExpr] at hxn hyn
        linear_combination hxn + hyn
    | succ n =>
        change (x.2 + y.2 : ScalarL2 rate) (n + 1) =
          (n + 1 : ℝ) * (x.1 + y.1 : FieldL2 rate) n -
            (rate : ℝ) * (x.1 + y.1 : FieldL2 rate) (n + 1)
        rw [scalar_add_apply rate hr, field_add_apply rate hr,
          field_add_apply rate hr]
        have hxn := hx (n + 1)
        have hyn := hy (n + 1)
        simp only [maximalDivergenceExpr] at hxn hyn
        linear_combination hxn + hyn
  smul_mem' := by
    intro c x hx n
    cases n with
    | zero =>
        change (c • x.2 : ScalarL2 rate) 0 =
          -(rate : ℝ) * (c • x.1 : FieldL2 rate) 0
        rw [scalar_smul_apply rate hr, field_smul_apply rate hr]
        have hxn := hx 0
        simp only [maximalDivergenceExpr] at hxn
        linear_combination c * hxn
    | succ n =>
        change (c • x.2 : ScalarL2 rate) (n + 1) =
          (n + 1 : ℝ) * (c • x.1 : FieldL2 rate) n -
            (rate : ℝ) * (c • x.1 : FieldL2 rate) (n + 1)
        rw [scalar_smul_apply rate hr, field_smul_apply rate hr,
          field_smul_apply rate hr]
        have hxn := hx (n + 1)
        simp only [maximalDivergenceExpr] at hxn
        linear_combination c * hxn

/-- The maximal difference graph is closed: each coefficient equation is a closed condition. -/
theorem maximalDifferenceGraph_isClosed :
    IsClosed (maximalDifferenceGraph rate hr : Set (ScalarL2 rate × FieldL2 rate)) := by
  have hset : (maximalDifferenceGraph rate hr : Set (ScalarL2 rate × FieldL2 rate)) =
      ⋂ n : ℕ, {z : ScalarL2 rate × FieldL2 rate |
        z.2 n = z.1 (n + 1) - z.1 n} := by
    ext z
    simp [maximalDifferenceGraph]
  rw [hset]
  apply isClosed_iInter
  intro n
  apply isClosed_eq
  · exact (continuous_field_apply rate hr n).comp continuous_snd
  · exact ((continuous_scalar_apply rate hr (n + 1)).comp continuous_fst).sub
      ((continuous_scalar_apply rate hr n).comp continuous_fst)

/-- The maximal divergence graph is closed, including the zero boundary equation. -/
theorem maximalDivergenceGraph_isClosed :
    IsClosed (maximalDivergenceGraph rate hr : Set (FieldL2 rate × ScalarL2 rate)) := by
  have hset : (maximalDivergenceGraph rate hr : Set (FieldL2 rate × ScalarL2 rate)) =
      ⋂ n : ℕ, {z : FieldL2 rate × ScalarL2 rate |
        z.2 n = maximalDivergenceExpr rate z.1 n} := by
    ext z
    simp [maximalDivergenceGraph]
  rw [hset]
  apply isClosed_iInter
  intro n
  apply isClosed_eq
  · exact (continuous_scalar_apply rate hr n).comp continuous_snd
  · cases n with
    | zero =>
        change Continuous (fun z : FieldL2 rate × ScalarL2 rate =>
          -(rate : ℝ) * z.1 0)
        exact continuous_const.mul
          ((continuous_field_apply rate hr 0).comp continuous_fst)
    | succ n =>
        change Continuous (fun z : FieldL2 rate × ScalarL2 rate =>
          (n + 1 : ℝ) * z.1 n - (rate : ℝ) * z.1 (n + 1))
        exact (continuous_const.mul
          ((continuous_field_apply rate hr n).comp continuous_fst)).sub
          (continuous_const.mul
            ((continuous_field_apply rate hr (n + 1)).comp continuous_fst))

/-- The maximal difference graph has no nonzero vertical vector. -/
theorem maximalDifferenceGraph_vertical_zero
    (z : ScalarL2 rate × FieldL2 rate) (hz : z ∈ maximalDifferenceGraph rate hr)
    (hz0 : z.1 = 0) : z.2 = 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2)
    (μ := (rate : ℝ≥0∞) • poissonLaw rate)] with n hn
  have he := hz n
  rw [hz0, scalar_zero_apply rate hr, scalar_zero_apply rate hr] at he
  simp only [sub_self] at he
  exact he.trans hn.symm

/-- The maximal divergence graph has no nonzero vertical vector. -/
theorem maximalDivergenceGraph_vertical_zero
    (z : FieldL2 rate × ScalarL2 rate) (hz : z ∈ maximalDivergenceGraph rate hr)
    (hz0 : z.1 = 0) : z.2 = 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2)
    (μ := poissonLaw rate)] with n hn
  have he := hz n
  rw [hz0] at he
  cases n with
  | zero =>
      change z.2 0 = -(rate : ℝ) * (0 : FieldL2 rate) 0 at he
      rw [field_zero_apply rate hr] at he
      simp only [mul_zero] at he
      exact he.trans hn.symm
  | succ n =>
      change z.2 (n + 1) = (n + 1 : ℝ) * (0 : FieldL2 rate) n -
        (rate : ℝ) * (0 : FieldL2 rate) (n + 1) at he
      rw [field_zero_apply rate hr, field_zero_apply rate hr] at he
      simp only [mul_zero, sub_self] at he
      exact he.trans hn.symm

/-- The maximal Poisson difference, defined by an actual L²-valued pointwise graph. -/
def maximalDifference : ScalarL2 rate →ₗ.[ℝ] FieldL2 rate :=
  (maximalDifferenceGraph rate hr).toLinearPMap

/-- The maximal Poisson divergence, defined by an actual L²-valued pointwise graph. -/
def maximalDivergence : FieldL2 rate →ₗ.[ℝ] ScalarL2 rate :=
  (maximalDivergenceGraph rate hr).toLinearPMap

theorem maximalDifference_graph : (maximalDifference rate hr).graph =
    maximalDifferenceGraph rate hr :=
  (maximalDifferenceGraph rate hr).toLinearPMap_graph_eq
    (maximalDifferenceGraph_vertical_zero rate hr)

theorem maximalDivergence_graph : (maximalDivergence rate hr).graph =
    maximalDivergenceGraph rate hr :=
  (maximalDivergenceGraph rate hr).toLinearPMap_graph_eq
    (maximalDivergenceGraph_vertical_zero rate hr)

/-- The maximal pointwise Poisson difference is a closed operator. -/
theorem maximalDifference_isClosed : (maximalDifference rate hr).IsClosed := by
  rw [LinearPMap.IsClosed, maximalDifference_graph]
  exact maximalDifferenceGraph_isClosed rate hr

/-- The maximal pointwise Poisson divergence is a closed operator. -/
theorem maximalDivergence_isClosed : (maximalDivergence rate hr).IsClosed := by
  rw [LinearPMap.IsClosed, maximalDivergence_graph]
  exact maximalDivergenceGraph_isClosed rate hr

/-- The genuine finite-support difference graph is contained in the maximal pointwise graph. -/
theorem coreDifference_le_maximal :
    coreDifference rate hr ≤ maximalDifference rate hr := by
  apply LinearPMap.le_of_le_graph
  intro z hz
  rw [coreDifference_graph] at hz
  obtain ⟨f, rfl⟩ := hz
  rw [maximalDifference_graph]
  intro n
  change (fieldFinsupp rate (finsuppDifference f)) n =
    (scalarFinsupp rate f) (n + 1) - (scalarFinsupp rate f) n
  rw [fieldFinsupp_apply rate hr, scalarFinsupp_apply rate hr,
    scalarFinsupp_apply rate hr, finsuppDifference_apply]

/-- The genuine finite-support divergence graph is contained in the maximal pointwise graph. -/
theorem coreDivergence_le_maximal :
    coreDivergence rate hr ≤ maximalDivergence rate hr := by
  apply LinearPMap.le_of_le_graph
  intro z hz
  rw [coreDivergence_graph] at hz
  obtain ⟨u, rfl⟩ := hz
  rw [maximalDivergence_graph]
  intro n
  change (scalarFinsupp rate (finsuppDivergence rate u)) n =
    maximalDivergenceExpr rate (fieldFinsupp rate u) n
  rw [scalarFinsupp_apply rate hr, finsuppDivergence_apply]
  cases n with
  | zero =>
      simp only [maximalDivergenceExpr, divergence_at_zero,
        fieldFinsupp_apply rate hr]
  | succ n =>
      simp only [maximalDivergenceExpr, divergence_at_succ,
        fieldFinsupp_apply rate hr]

end OperatorDerivativeRewrite.Foundation.PoissonMaximalOperators
