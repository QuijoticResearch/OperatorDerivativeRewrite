import Foundation.CubeOperatorTail

/-! Uniform native L2 localization on the action tail of the actual Wilson slab. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.CubeOperatorLocalization
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround CubeSlabL2 CubeOperatorTail
attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar
variable {beta : ℝ} (d : GroundData beta)

/-- Actual measurable action-tail component of a native L2 class. -/
def tailPart (eps : ℝ) (f : StateL2 d) : StateL2 d :=
  ((Lp.memLp f).indicator (measurableSet_le measurable_const spatial_action_measurable)).toLp
    ({U | eps ≤ spatialAction U}.indicator f)

theorem tailPart_coe (eps : ℝ) (f : StateL2 d) :
    tailPart d eps f =ᵐ[d.stationary] {U | eps ≤ spatialAction U}.indicator f :=
  MemLp.coeFn_toLp _

theorem tailPart_norm (eps : ℝ) (f : StateL2 d) : ‖tailPart d eps f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [tailPart_coe d eps f] with U hU
  rw [hU]
  by_cases h : eps ≤ spatialAction U <;> simp [Set.indicator,h]

/-- Uniform over every native L2 input, including unbounded representatives. -/
theorem operator_tailPart_bound (hb : 0 ≤ beta) (eps : ℝ) (f : StateL2 d) :
    ‖operator d (tailPart d eps f)‖ ≤ (Real.exp (-beta*eps/2)/d.value)*‖f‖ := by
  have hs : ∀ᵐ U ∂d.stationary, spatialAction U < eps → tailPart d eps f U=0 := by
    filter_upwards [tailPart_coe d eps f] with U hU h
    rw [hU]
    simp only [Set.indicator_of_notMem (show U ∉ {V | eps ≤ spatialAction V} from not_le.mpr h)]
  exact (norm_tail_bound d hb eps (tailPart d eps f) hs).trans
    (mul_le_mul_of_nonneg_left (tailPart_norm d eps f)
      (div_nonneg (Real.exp_pos _).le d.value_pos.le))

/-- A fixed action-tail threshold gives exponential native operator localization.
Constants depend on the threshold and the finite cell, not on the input or coupling. -/
theorem operator_tailPart_exponential (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ beta : ℝ, 0 ≤ beta → ∀ g : GroundData beta,
      ∀ f : StateL2 g, ‖operator g (tailPart g eps f)‖ ≤
        C*Real.exp (-beta*eps/4)*‖f‖ := by
  obtain ⟨c,hc,hl⟩ := CubeGroundMass.eigenvalue_small_rate (eps/4) (by positivity)
  refine ⟨1/c,div_pos zero_lt_one hc,?_⟩
  intro beta hb g f
  have hv := hl beta hb g
  have hdiv := div_le_div_of_nonneg_left (Real.exp_pos (-beta*eps/2)).le
    (mul_pos hc (Real.exp_pos _)) hv
  have he : Real.exp (-beta*eps/2)=Real.exp (-beta*(eps/4))*Real.exp (-beta*(eps/4)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq : Real.exp (-beta*eps/2)/(c*Real.exp (-beta*(eps/4)))=
      (1/c)*Real.exp (-beta*eps/4) := by
    rw [he]
    have ha : -beta*(eps/4)=-beta*eps/4 := by ring
    rw [ha]
    field_simp [hc.ne',(Real.exp_pos (-beta*eps/4)).ne']
  exact (operator_tailPart_bound g hb eps f).trans
    (mul_le_mul_of_nonneg_right (hdiv.trans_eq heq) (norm_nonneg f))

end OperatorDerivativeRewrite.Foundation.CubeOperatorLocalization
