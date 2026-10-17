import Foundation.HigherHeatContinuousCylinders

/-! A concrete cylinder algebra on continuous paths and its nonpositive higher-heat expectation. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPathCylinderAlgebra
open HigherHeatDyadicLaws HigherHeatCylindricalExpectation HigherHeatNegativeProbe
open HigherHeatContinuousCylinders

theorem product_mem {F G : Path →ᵇ ℝ} (hF : F ∈ realizedSpace) (hG : G ∈ realizedSpace) :
    F*G ∈ realizedSpace := by
  obtain ⟨c,rfl⟩ := hF
  obtain ⟨d,rfl⟩ := hG
  obtain ⟨n,f,g,hc,hd⟩ := DirectLimit.exists_eq_mk₂ transition c d
  change c=cylinderOf n f at hc
  change d=cylinderOf n g at hd
  refine ⟨cylinderOf n (f*g),?_⟩
  rw [hc,hd]
  ext ω
  rfl

theorem constant_mem (r : ℝ) : algebraMap ℝ (Path →ᵇ ℝ) r ∈ realizedSpace := by
  refine ⟨cylinderOf 0 (BoundedContinuousFunction.const (Grid 0) r),?_⟩
  ext ω
  rfl

def cylinderAlgebra : Subalgebra ℝ (Path →ᵇ ℝ) where
  carrier := realizedSpace
  zero_mem' := realizedSpace.zero_mem
  one_mem' := by simpa using constant_mem 1
  add_mem' := realizedSpace.add_mem
  mul_mem' := product_mem
  algebraMap_mem' := constant_mem

instance cylinderAlgebra_algebra : Algebra ℝ cylinderAlgebra := Subalgebra.algebra cylinderAlgebra

instance cylinderAlgebra_module : Module ℝ cylinderAlgebra := Algebra.toModule

def inclusion : cylinderAlgebra →ₗ[ℝ] realizedSpace where
  toFun F := ⟨F.val,F.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def algebraExpectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : cylinderAlgebra →ₗ[ℝ] ℝ :=
  (pathExpectation m hm T hT).comp inclusion

def representCylinder (c : Cylinder) : cylinderAlgebra := ⟨realize c,⟨c,rfl⟩⟩

theorem representCylinder_apply (c : Cylinder) (ω : Path) : (representCylinder c).val ω=realize c ω := rfl

theorem algebraExpectation_represent (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (c : Cylinder) :
    algebraExpectation m hm T hT (representCylinder c)=cylindricalExpectation m hm T hT c := by
  change pathExpectation m hm T hT (realizationEquiv c)=cylindricalExpectation m hm T hT c
  exact pathExpectation_apply m hm T hT c

theorem algebraExpectation_one (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    algebraExpectation m hm T hT (1 : cylinderAlgebra)=1 := by
  have he : (1 : cylinderAlgebra)=representCylinder unitCylinder := by
    ext ω
    rfl
  rw [he,algebraExpectation_represent,cylindricalExpectation_normalized]

theorem negative_nonnegative_witness (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) :
    ∃ F : cylinderAlgebra, (∀ ω : Path, 0 ≤ F.val ω) ∧ algebraExpectation m (by omega) T hT F < 0 := by
  refine ⟨representCylinder (negativeCylinder m (by omega) T hT),?_,?_⟩
  · intro ω
    change 0 ≤ terminalTest (probe m (by omega) T hT) (sample 0 ω)
    exact terminal_probe_nonnegative m (by omega) T hT _
  · rw [algebraExpectation_represent]
    exact negative_cylinder_expectation m hm T hT

theorem cylinder_integrable (μ : Measure Path) [IsFiniteMeasure μ] (F : cylinderAlgebra) :
    Integrable (fun ω : Path => F.val ω) μ :=
  Integrable.of_bound F.val.continuous.aestronglyMeasurable ‖F.val‖
    (Eventually.of_forall F.val.norm_coe_le_norm)

theorem no_positive_measure_realization (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T)
    (μ : Measure Path) [IsFiniteMeasure μ] :
    ¬ ∀ F : cylinderAlgebra, algebraExpectation m (by omega) T hT F=∫ ω : Path, F.val ω ∂μ := by
  intro h
  obtain ⟨F,hF,hneg⟩ := negative_nonnegative_witness m hm T hT
  rw [h F] at hneg
  have hn : (0 : ℝ) ≤ ∫ ω : Path, F.val ω ∂μ := integral_nonneg (fun ω => hF ω)
  linarith

end OperatorDerivativeRewrite.Foundation.HigherHeatPathCylinderAlgebra
