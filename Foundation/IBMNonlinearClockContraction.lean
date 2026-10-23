import Foundation.IBMNonlinearClockCutoffError
import Foundation.IBMNonlinearClockLocalization
import Foundation.BochnerCoefficientParseval
import Foundation.BochnerL2MajorantRealization

/-! Exact coefficient contractions of the actual localized nonlinear clock
average, in clock/source order. The mask is explicitly composed with abs. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockContraction
open InfiniteGaussian IBMClockPhysicalOccupation IBMClockOverlapEnergy
open IBMNonlinearClockTailEnergy IBMNonlinearClockLocalization
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem tensor_contraction (h d : CoefficientSpace) (f : GaussianL2) :
    (innerSL ℝ h).compLpL 2 gaussianProduct (scalarTensor d f) = inner ℝ h d • f := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ h).coeFn_compLpL (scalarTensor d f),
    scalarTensor_coeFn d f,Lp.coeFn_smul (inner ℝ h d) f] with X hc ht hs
  rw [hc,ht,hs,Pi.smul_apply,innerSL_apply_apply,inner_smul_right]
  simp only [smul_eq_mul,mul_comm]

theorem field_contraction_ae (h : CoefficientSpace) (χ : ℝ → ℝ) (hχ : Measurable χ)
    (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (n : ℕ) (t : ℝ) :
    contraction h (field (fun x => χ |x|) n t) =ᵐ[gaussianProduct]
      fun Y => IBMSourceValuedOccupation.fieldValue h
        (fun r => χ r • IBMNonlinearClockColumn.column n r) (t,Y) := by
  have hm : Measurable (fun x : ℝ => χ |x|) := hχ.comp continuous_abs.measurable
  have he := ((innerSL ℝ h).compLpL 2 gaussianProduct).coeFn_compLpL
    (field (fun x => χ |x|) n t)
  filter_upwards [he,field_ae (fun x => χ |x|) hm (fun x => h0 _) (fun x => h1 _) n t]
    with Y hc hf
  change contraction h (field (fun x => χ |x|) n t) Y = _ at hc
  rw [hc,hf,maskedSection,map_smul,IBMNonlinearClockField.sectionField,
    map_smul,tensor_contraction]
  simp only [IBMSourceValuedOccupation.fieldValue,smul_smul]
  congr 1
  ring

/-- Contraction of the original FULL native vector equals the same actual
localized occupation integral already known to converge strongly. -/
theorem average_contraction (h : CoefficientSpace) (χ : ℝ → ℝ) (hc : Continuous χ)
    (hs : HasCompactSupport χ) (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1)
    (n : ℕ) (T : ℝ≥0) :
    contraction h (IBMNonlinearClockTailEnergy.average (fun x => χ |x|) n T) =
      nativeField h n χ hc hs T := by
  let G : ℝ → GaussianL2 := fun r => χ r • IBMNonlinearClockColumn.column n r
  have hG : Continuous G := hc.smul (IBMNonlinearColumnContinuity.column_continuous n)
  have hGs : HasCompactSupport G := hs.smul_right
  obtain ⟨M,hb⟩ := hG.norm.bddAbove_range_of_hasCompactSupport hGs.norm
  have hM : 0 ≤ M := (norm_nonneg (G 0)).trans (hb ⟨0,rfl⟩)
  let B : SampleSpace → ℝ := fun _ => ‖h‖*Real.sqrt T*M
  have hB : MemLp B 2 gaussianProduct := memLp_const _
  have hmajor : ∀ᵐ p : ℝ × SampleSpace ∂(window T).prod gaussianProduct,
      ‖IBMSourceValuedOccupation.fieldValue h G p‖ ≤ B p.2 := by
    have ht : ∀ᵐ p : ℝ × SampleSpace ∂(window T).prod gaussianProduct,
        p.1 ∈ Ioc 0 (T:ℝ) :=
      (Measure.quasiMeasurePreserving_fst (μ := window T) (ν := gaussianProduct)).ae
        (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [ht] with p hp
    exact IBMSourceValuedOccupation.fieldValue_bound h G hM (fun r => hb ⟨r,rfl⟩) T p hp
  have hi := field_integrable (fun x => χ |x|) (hc.measurable.comp continuous_abs.measurable)
    (fun x => h0 _) (fun x => h1 _) n T.property
  unfold IBMNonlinearClockTailEnergy.average
  apply ((contraction h).integral_comp_comm hi).symm.trans
  have he := BochnerL2MajorantRealization.integral_coeFn_ae
    (fun t => contraction h (field (fun x => χ |x|) n t))
    ((contraction h).integrable_comp hi) (IBMSourceValuedOccupation.fieldValue h G)
    (IBMSourceValuedOccupation.fieldValue_stronglyMeasurable h G hG)
    (ae_of_all _ (field_contraction_ae h χ hc.measurable h0 h1 n)) B hB hmajor
  apply Lp.ext
  exact he.trans (MemLp.coeFn_toLp _).symm

theorem contraction_tendsto (h : CoefficientSpace) (χ : ℝ → ℝ) (hc : Continuous χ)
    (hs : HasCompactSupport χ) (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1)
    {a b : ℝ} (hab : a ≤ b) (hwin : ∀ r, r ∉ Ioc a b → χ r = 0) (T : ℝ≥0) :
    Tendsto (fun n => contraction h
      (IBMNonlinearClockTailEnergy.average (fun x => χ |x|) n T)) atTop
        (𝓝 (limitField h χ hc hs hab T)) := by
  simpa only [average_contraction h χ hc hs h0 h1] using
    nativeField_tendsto h χ hc hs hab hwin T

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockContraction
