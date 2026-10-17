import Foundation.ContinuousDensityDuality

/-! Higher even heat expectations are unbounded on the unit ball of actual path cylinder functions. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatUnboundedExpectation
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatPositionVariation
open HigherHeatDyadicLaws HigherHeatCylindricalExpectation HigherHeatContinuousCylinders
open HigherHeatPathCylinderAlgebra HigherHeatSignedRepresentation ContinuousDensityDuality

theorem incrementDensity_continuous (m : ℕ) (hm : 0 < m) (n : ℕ)
    (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) : Continuous (incrementDensity m hm t ht) := by
  unfold incrementDensity
  fun_prop

set_option backward.isDefEq.respectTransparency false in
theorem increment_norm_integral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ x : Grid n, ‖incrementDensity m hm (fun _ => duration T n)
      (fun _ => duration_pos T hT n) x‖ ∂Measure.pi (fun _ => volume)) =
      (∫ x : ℝ, ‖realKernel m hm T hT x‖)^(gridSize n) := by
  simp only [incrementDensity,norm_prod]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin (gridSize n)) (x : ℝ) =>
    ‖realKernel m hm (duration T n) (duration_pos T hT n) x‖)]
  simp_rw [norm_integral_time_independent m hm (duration T n) T (duration_pos T hT n) hT]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

def positionTest (n : ℕ) (g : Grid n →ᵇ ℝ) : Test n :=
  g.compContinuous ⟨(cumulativeEquiv (gridSize n)).symm,
    (cumulativeEquiv (gridSize n)).symm.toContinuousLinearEquiv.continuous⟩

theorem positionTest_cumulative (n : ℕ) (g : Grid n →ᵇ ℝ) (x : Grid n) :
    positionTest n g (linearImage (cumulativeMatrix (gridSize n)) x)=g x := by
  change g ((cumulativeEquiv (gridSize n)).symm (linearImage _ x))=g x
  rw [← cumulativeEquiv_apply,LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
theorem positionTest_expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (g : Grid n →ᵇ ℝ) :
    expectation m hm T hT n (positionTest n g)=
      ∫ x : Grid n, incrementDensity m hm (fun _ => duration T n)
        (fun _ => duration_pos T hT n) x*g x ∂Measure.pi (fun _ => volume) := by
  change (∫ᵛ x : Grid n, positionTest n g x ∂•
    (incrementLaw m hm (fun _ => duration T n) (fun _ => duration_pos T hT n)).map
      (linearImage (cumulativeMatrix (gridSize n)))) = _
  rw [VectorMeasure.integral_map (linearImage_measurable _)
    (positionTest n g).continuous.aestronglyMeasurable]
  · simp_rw [positionTest_cumulative]
    exact HigherHeatNegativeProbe.real_integral_density _ _ (incrementDensity_integrable _ _ _ _)
      (incrementDensity_continuous _ _ _ _ _).measurable g g.continuous.measurable ‖g‖ g.norm_coe_le_norm
  · have he : (fun x : Grid n => positionTest n g (linearImage (cumulativeMatrix (gridSize n)) x))=g := by
      funext x
      exact positionTest_cumulative n g x
    change (incrementLaw m hm (fun _ => duration T n) (fun _ => duration_pos T hT n)).Integrable
      (fun x => positionTest n g (linearImage (cumulativeMatrix (gridSize n)) x))
    rw [he]
    exact bounded_real_integrable _ g

theorem unbounded_unit_cylinders (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) (R : ℝ) :
    ∃ F : cylinderAlgebra, ‖F.val‖ ≤ 1 ∧ R < algebraExpectation m (by omega) T hT F := by
  let C : ℝ := ∫ x : ℝ, ‖realKernel m (by omega : 0 < m) T hT x‖
  have hC : 1 < C := HigherHeatKernelMoments.norm_integral_gt_one m hm T hT
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt R hC
  have hp : C^n ≤ C^(gridSize n) := pow_le_pow_right₀ hC.le (level_le_size n)
  have hd : R < ∫ x : Grid n, ‖incrementDensity m (by omega : 0 < m)
      (fun _ => duration T n) (fun _ => duration_pos T hT n) x‖ ∂Measure.pi (fun _ => volume) := by
    rw [increment_norm_integral m (by omega) T hT n]
    exact hn.trans_le hp
  obtain ⟨g,hg,hR⟩ := exists_norm_one_test _ _
    (incrementDensity_continuous m (by omega) _ _ _) (incrementDensity_integrable _ _ _ _) R hd
  refine ⟨representCylinder (cylinderOf n (positionTest n g)),?_,?_⟩
  · apply (BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 1)).2
    intro ω
    exact hg _
  · rw [algebraExpectation_represent,cylindricalExpectation_apply,positionTest_expectation]
    exact hR

theorem no_uniform_bound (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) :
    ¬ ∃ C : ℝ, ∀ F : cylinderAlgebra,
      |algebraExpectation m (by omega) T hT F| ≤ C*‖F.val‖ := by
  rintro ⟨C,h⟩
  obtain ⟨F,hF,hR⟩ := unbounded_unit_cylinders m hm T hT (max C 0)
  have hb := h F
  have he : algebraExpectation m (by omega) T hT F ≤ |algebraExpectation m (by omega) T hT F| := le_abs_self _
  have hmC : C*‖F.val‖ ≤ max C 0 := calc
    C*‖F.val‖ ≤ max C 0*‖F.val‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max C 0 := mul_le_of_le_one_right (le_max_right _ _) hF
  exact (not_lt_of_ge (he.trans (hb.trans hmC))) hR

end OperatorDerivativeRewrite.Foundation.HigherHeatUnboundedExpectation
