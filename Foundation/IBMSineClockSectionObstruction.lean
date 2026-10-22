import Foundation.IBMNonlinearFirstSource
import Foundation.IBMClockBochnerConverse

/-! The actual bounded sine scenery section retains a Brownian first-source
energy obstruction. Smooth bounded scalar functions need not be clock-Sobolev. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineClockSectionObstruction
open InfiniteGaussian IBMNonlinearFirstSource IBMContinuousScenery
open IBMClockSectionEnergyObstruction GaussianWeakVectorPrimitive IBMClockBochnerConverse
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def sineSection (c x : ℝ) : GaussianL2 := scenerySine |c*x|

theorem section_continuous (c : ℝ) : Continuous (sineSection c) :=
  scenerySine_continuous.comp ((continuous_const.mul continuous_id).abs)

theorem section_memLp (c : ℝ) : MemLp (sineSection c) 2 GaussianCore.γ :=
  MemLp.of_bound (section_continuous c).aestronglyMeasurable 1
    (ae_of_all _ fun x => sineClass_norm_le _)

def sectionClass (c : ℝ) : Lp GaussianL2 2 GaussianCore.γ := (section_memLp c).toLp _

theorem sectionClass_ae (c : ℝ) : sectionClass c =ᵐ[GaussianCore.γ] sineSection c :=
  (section_memLp c).coeFn_toLp

def projected (c x : ℝ) : GaussianL2 := projection (sineSection c x)

theorem projected_formula (c x : ℝ) :
    projected c x = Real.exp (-|c*x|/2) • sourceScenery |c*x| := by
  simpa only [projected, sineSection, abs_abs] using scenerySine_projection |c*x|

theorem projected_zero (c : ℝ) : projected c 0 = 0 := by
  have hz : sourceScenery 0 = 0 := by
    apply norm_eq_zero.mp
    have hn := IBMRandomTimeHilbert.sourceScenery_norm_sq 0
    simp only [abs_zero] at hn
    nlinarith [norm_nonneg (sourceScenery 0)]
  simp only [projected_formula, mul_zero, abs_zero, hz, smul_zero]

theorem projected_lower (c : ℝ) (hc : 0 < c) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (Real.exp (-c/2)^2*c) * (x-0) ≤ ‖projected c x - projected c 0‖^2 := by
  have hcx : 0 ≤ c*x := mul_nonneg hc.le hx.1
  have he : Real.exp (-c/2) ≤ Real.exp (-(c*x)/2) :=
    Real.exp_le_exp.mpr (by nlinarith [hx.2])
  have hs : Real.exp (-c/2)^2 ≤ Real.exp (-(c*x)/2)^2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le he 2
  have hm := mul_le_mul_of_nonneg_right hs hcx
  rw [projected_zero, sub_zero, sub_zero, projected_formula, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, IBMRandomTimeHilbert.sourceScenery_norm_sq]
  simp only [abs_abs, abs_of_nonneg hcx]
  nlinarith

theorem project_integral (g : Lp GaussianL2 2 GaussianCore.γ) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    projection (∫ y in Icc 0 x, g y) = ∫ y in Icc 0 x, (projection.compLp g) y := by
  obtain ⟨C, _, hC, hcmp⟩ := GaussianLocalSobolev.exists_local_measure_comparison 0 1
  have hg := ((Lp.memLp g).of_measure_le_smul hC hcmp).mono_measure
    (Measure.restrict_mono (Icc_subset_Icc_right hx.2) le_rfl)
  have hvol : (volume : Measure ℝ) ≪ GaussianCore.γ :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
  have ha : projection.compLp g =ᵐ[volume.restrict (Icc 0 x)] fun y => projection (g y) :=
    ae_restrict_of_ae (hvol.ae_eq (projection.coeFn_compLp g))
  exact (projection.integral_comp_comm (hg.integrable (by norm_num))).symm.trans
    (integral_congr_ae ha).symm

theorem no_section_ae_primitive (c : ℝ) (hc : 0 < c)
    (g : Lp GaussianL2 2 GaussianCore.γ) (v : GaussianL2) :
    ¬ (sineSection c =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun x => v + ∫ y in Icc 0 x, g y) := by
  intro hp
  have hproj : projected c =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun x => projection v + ∫ y in Icc 0 x, (projection.compLp g) y := by
    filter_upwards [hp, ae_restrict_mem measurableSet_Icc] with x hx hxi
    change projection (sineSection c x) = _
    rw [hx, map_add, project_integral g x hxi]
  obtain ⟨C, _, hC, hcmp⟩ := GaussianLocalSobolev.exists_local_measure_comparison 0 1
  have hg := (Lp.memLp (projection.compLp g)).of_measure_le_smul hC hcmp
  exact no_finite_energy_primitive_ae (by norm_num)
    (show 0 < Real.exp (-c/2)^2*c by positivity)
    (projection.continuous.comp (section_continuous c)).continuousOn
    (projected_lower c hc) hg (projection v) hproj

theorem no_common_closed_derivative (c : ℝ) (hc : 0 < c) :
    ¬ ∃ g : Lp GaussianL2 2 GaussianCore.γ,
      ∀ e : GaussianL2, ((innerSL ℝ e).compLp (sectionClass c),
        (innerSL ℝ e).compLp g) ∈ GaussianCore.closedDerivative.graph := by
  rintro ⟨g, hg⟩
  obtain ⟨v, hv⟩ := weak_graph_primitive (sectionClass c) g hg
    (a := 0) (b := 1) (by norm_num)
  have hvol : (volume : Measure ℝ) ≪ GaussianCore.γ :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
  have hr : sectionClass c =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] sineSection c :=
    ae_restrict_of_ae (hvol.ae_eq (sectionClass_ae c))
  exact no_section_ae_primitive c hc g v (hr.symm.trans hv)

theorem section_not_native_clock_domain (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (c : ℝ) (hc : 0 < c) :
    ProductL2Curry.flip gaussianProduct gaussianProduct
      (fieldPullback h hh (sectionClass c)) ∉
        (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).domain := by
  intro hu
  obtain ⟨V, hV⟩ := LinearPMap.mem_domain_iff.mp hu
  exact no_common_closed_derivative c hc
    ⟨recoveredField h hh V, original_field_graph_recovery h hh _ V hV⟩

end OperatorDerivativeRewrite.Foundation.IBMSineClockSectionObstruction
