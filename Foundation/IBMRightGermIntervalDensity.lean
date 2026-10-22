import Foundation.IBMRightGermIntegralCompletion
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.PiSystem

/-! Full time-L2 interval density for the actual IBM energy measure, by
finite-horizon vector-measure uniqueness and its zero origin mass. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRightGermIntervalDensity
open IBMRightGermEnergyMeasure IBMRightGermDeterministicIntegral
open IBMRightGermIntegralCompletion
set_option backward.isDefEq.respectTransparency false

theorem Iic_ae_Ioc (t : ℝ≥0) : Iic t =ᵐ[energyMeasure] Ioc 0 t := by
  have hz := measure_eq_zero_iff_ae_notMem.mp energyMeasure_origin
  filter_upwards [hz] with x hx
  have hp : 0 < x := pos_iff_ne_zero.mpr (by simpa only [mem_singleton_iff] using hx)
  simp only [mem_Iic, mem_Ioc, hp, true_and]

theorem Iic_finite (t : ℝ≥0) : energyMeasure (Iic t) ≠ ⊤ := by
  rw [measure_congr (Iic_ae_Ioc t)]
  exact (energyMeasure_Ioc_finite 0 t).ne

theorem timePrefix_mem (t : ℝ≥0) : timePrefix t ∈ domain := by
  apply timeDictionary.range.le_topologicalClosure
  refine ⟨Finsupp.single t 1, ?_⟩
  simp only [timeDictionary, Finsupp.linearCombination_single, one_smul]

theorem orthogonal_prefix_integral (f : TimeL2) (hf : f ∈ domainᗮ) (t : ℝ≥0) :
    (∫ x in Iic t, f x ∂energyMeasure) = 0 := by
  have hi := Submodule.inner_right_of_mem_orthogonal (timePrefix_mem t) hf
  have he := L2.inner_indicatorConstLp_one (𝕜 := ℝ)
    measurableSet_Ioc (energyMeasure_Ioc_finite 0 t).ne f
  exact (setIntegral_congr_set (Iic_ae_Ioc t)).trans (he.symm.trans hi)

theorem orthogonal_zero_on_horizon (f : TimeL2) (hf : f ∈ domainᗮ) (T : ℝ≥0) :
    f =ᵐ[energyMeasure.restrict (Iic T)] (fun _ => (0 : ℝ)) := by
  have hi : Integrable f (energyMeasure.restrict (Iic T)) :=
    integrableOn_Lp_of_measure_ne_top f (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Iic_finite T)
  have hv : (energyMeasure.restrict (Iic T)).withDensityᵥ f = 0 := by
    apply VectorMeasure.ext_of_generateFrom (range Iic)
    · rintro s ⟨t, rfl⟩
      rw [withDensityᵥ_apply hi measurableSet_Iic, VectorMeasure.zero_apply,
        Measure.restrict_restrict measurableSet_Iic, Iic_inter_Iic]
      exact orthogonal_prefix_integral f hf (min t T)
    · exact (BorelSpace.measurable_eq (α := ℝ≥0)).trans
        (borel_eq_generateFrom_Iic (α := ℝ≥0))
    · exact isPiSystem_Iic
    · rw [withDensityᵥ_apply hi MeasurableSet.univ, VectorMeasure.zero_apply,
        Measure.restrict_univ]
      exact orthogonal_prefix_integral f hf T
  apply hi.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
  simpa only [withDensityᵥ_zero] using hv

theorem orthogonal_zero (f : TimeL2) (hf : f ∈ domainᗮ) : f = 0 := by
  have hc : (⋃ n : ℕ, Iic (n : ℝ≥0)) = univ := by
    ext x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact exists_nat_ge x
  have hz : f =ᵐ[energyMeasure.restrict (⋃ n : ℕ, Iic (n : ℝ≥0))]
      (fun _ => (0 : ℝ)) :=
    (ae_eq_restrict_iUnion_iff _ _ _).mpr (fun n => orthogonal_zero_on_horizon f hf n)
  rw [hc, Measure.restrict_univ] at hz
  exact Lp.ext (hz.trans (Lp.coeFn_zero ℝ 2 energyMeasure).symm)

theorem domain_eq_top : domain = ⊤ := by
  letI : domain.HasOrthogonalProjection := by unfold domain; infer_instance
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  exact orthogonal_zero f hf

theorem timeDictionary_dense : DenseRange timeDictionary :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr domain_eq_top

end OperatorDerivativeRewrite.Foundation.IBMRightGermIntervalDensity
