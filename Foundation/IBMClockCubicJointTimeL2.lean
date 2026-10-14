import Foundation.IBMClockSixthMoment
import Foundation.FiniteMeasureL2Integration

/-! Actual finite-horizon cubic time integral in the full joint IBM law.
All constants are fixed-mollifier bounds; no singular limit is claimed. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.IBMClockCubicJointTimeL2
open InfiniteGaussian IBMClockCubicCorrection IBMClockCubicJointL2 IBMClockSixthMoment
open IBMClockCubicRepresentative IBMSceneryCubicProjection
attribute [local irreducible] IBMConstructedSources.mollifiedValue IBMDyadicExtension.field

theorem joint_energy_growth (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0,
      (∫ ω, (value n t ω)^2 ∂IBMSourceLaws.jointMeasure) ≤ C*(1+15*(t : ℝ)^3) := by
  obtain ⟨A,hA,hgrowth⟩ := spatialCorrection_global_growth n
  refine ⟨64*A^2,by positivity, ?_⟩
  intro t
  have hG := (value_memLp_joint n t).integrable_sq
  have hi : Integrable (fun ωY => ‖sectionClass n t ωY‖^2) gaussianProduct := by
    exact hG.integral_prod_right.congr (Eventually.of_forall fun ωY => (section_energy n t ωY).symm)
  have hj : Integrable (fun ωY => A^2*(1+|IBMConstructedSources.clockPath ωY t|)^6)
      gaussianProduct := by
    simpa only [← pow_mul] using (clock_cubic_growth_memLp t).integrable_sq.const_mul (A^2)
  change (∫ ω : SampleSpace × SampleSpace, (value n t ω)^2
    ∂gaussianProduct.prod gaussianProduct) ≤ _
  rw [integral_prod_symm (fun ω => (value n t ω)^2) hG]
  simp only [← section_energy]
  calc
    _ ≤ ∫ ωY, A^2*(1+|IBMConstructedSources.clockPath ωY t|)^6 ∂gaussianProduct := by
      apply integral_mono hi hj
      intro ωY
      have hb : ‖sectionClass n t ωY‖ ≤ A*(1+|IBMConstructedSources.clockPath ωY t|)^3 := by
        simpa only [sectionClass,abs_abs] using hgrowth |IBMConstructedSources.clockPath ωY t|
      calc
        _ ≤ (A*(1+|IBMConstructedSources.clockPath ωY t|)^3)^2 := by
          change ‖sectionClass n t ωY‖^2 ≤ _
          exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
        _ = _ := by ring
    _ = A^2*(∫ ωY, (1+|IBMConstructedSources.clockPath ωY t|)^6 ∂gaussianProduct) :=
      integral_const_mul _ _
    _ ≤ A^2*(64*(1+15*(t : ℝ)^3)) :=
      mul_le_mul_of_nonneg_left (clock_growth_sixth_integral_le t) (sq_nonneg A)
    _ = _ := by ring

def timeValue (n : ℕ) (p : ℝ × IBMSourceLaws.JointSample) : ℝ :=
  value n (Real.toNNReal p.1) p.2

theorem timeValue_measurable (n : ℕ) : Measurable (timeValue n) := by
  have hm : Measurable (fun p : ℝ × IBMSourceLaws.JointSample => (Real.toNNReal p.1,p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  exact (value_jointly_measurable n).comp hm

theorem timeValue_memLp (n : ℕ) (T : ℝ) :
    MemLp (timeValue n) 2 ((volume.restrict (Set.Icc 0 T)).prod IBMSourceLaws.jointMeasure) := by
  have hm := timeValue_measurable n
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun s => (value_memLp_joint n (Real.toNNReal s)).integrable_sq
  · obtain ⟨C,hC,hgrowth⟩ := joint_energy_growth n
    have hc : Continuous (fun s : ℝ => C*(1+15*(Real.toNNReal s : ℝ)^3)) := by fun_prop
    apply hc.integrableOn_Icc.mono'
      (hm.pow_const 2).stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have he : (∫ ω, ‖(timeValue n (s,ω))^2‖ ∂IBMSourceLaws.jointMeasure)=
          ∫ ω, (value n (Real.toNNReal s) ω)^2 ∂IBMSourceLaws.jointMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun _ => Real.norm_of_nonneg (sq_nonneg _)
      rw [he]
      exact hgrowth (Real.toNNReal s)

theorem integratedValue_memLp_joint (n : ℕ) (T : ℝ) :
    MemLp (fun ω : IBMSourceLaws.JointSample => integratedValue n ω.2 T ω.1)
      2 IBMSourceLaws.jointMeasure :=
  FiniteMeasureL2Integration.column_integral_memLp (timeValue n) (timeValue_memLp n T)

theorem integratedValue_joint_energy_le (n : ℕ) (T : ℝ) :
    (∫ ω : IBMSourceLaws.JointSample, (integratedValue n ω.2 T ω.1)^2
      ∂IBMSourceLaws.jointMeasure) ≤ (volume.restrict (Set.Icc 0 T)).real Set.univ *
        ∫ p, (timeValue n p)^2
          ∂(volume.restrict (Set.Icc 0 T)).prod IBMSourceLaws.jointMeasure :=
  FiniteMeasureL2Integration.column_integral_energy_le (timeValue n) (timeValue_memLp n T)

end OperatorDerivativeRewrite.Foundation.IBMClockCubicJointTimeL2
