import Foundation.BrownianMassStieltjesSupport
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Defs

/-! The samplewise Stieltjes measures form a genuine measurable kernel of
temporal mass. This is not a Markov transition or a stochastic flow kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianMassMeasurableKernel
open InfiniteGaussian BrownianMassContinuousLimit BrownianMassStieltjesSupport

theorem monotone_samples_measurable : MeasurableSet {ω | Monotone (limitPath ω)} := by
  have hc : Continuous (fun f : C(ℝ≥0, ℝ) => fun t => f t) :=
    continuous_pi (fun _ => by fun_prop)
  have hs : IsClosed {f : C(ℝ≥0, ℝ) | Monotone f} := isClosed_monotone.preimage hc
  exact hs.measurableSet.preimage limitPath_measurable

theorem cumulative_coordinate_measurable (t : ℝ≥0) : Measurable (fun ω => cumulative ω t) := by
  classical
  have he : (fun ω => cumulative ω t) =
      fun ω => if Monotone (limitPath ω) then limitPath ω t else 0 := by
    funext ω
    by_cases h : Monotone (limitPath ω) <;> simp [cumulative, h]
  rw [he]
  exact Measurable.ite monotone_samples_measurable
    ((ContinuousMap.measurable_eval t).comp limitPath_measurable) measurable_const

def restrictedMass (T : ℝ≥0) (ω : SampleSpace) : Measure ℝ≥0 :=
  (massMeasure ω).restrict (Icc 0 T)

instance restrictedMass_finite (T : ℝ≥0) (ω : SampleSpace) :
    IsFiniteMeasure (restrictedMass T ω) := by
  constructor
  rw [restrictedMass, Measure.restrict_apply_univ, massMeasure_Icc]
  exact ENNReal.ofReal_lt_top

theorem restrictedMass_Iic (T t : ℝ≥0) (ω : SampleSpace) :
    restrictedMass T ω (Iic t) = ENNReal.ofReal (cumulative ω (min t T) - cumulative ω 0) := by
  have he : Iic t ∩ Icc (0 : ℝ≥0) T = Icc 0 (min t T) := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [restrictedMass, Measure.restrict_apply measurableSet_Iic, he, massMeasure_Icc]

theorem restrictedMass_measurable (T : ℝ≥0) : Measurable (restrictedMass T) := by
  have hgen : (inferInstance : MeasurableSpace ℝ≥0) =
      MeasurableSpace.generateFrom (range (Iic : ℝ≥0 → Set ℝ≥0)) := by
    rw [(inferInstance : BorelSpace ℝ≥0).measurable_eq, borel_eq_generateFrom_Iic]
  apply Measurable.measure_of_isPiSystem (μ := restrictedMass T) hgen isPiSystem_Iic
  · rintro _ ⟨t, rfl⟩
    have he : (fun ω => restrictedMass T ω (Iic t)) =
        fun ω => ENNReal.ofReal (cumulative ω (min t T) - cumulative ω 0) :=
      funext (restrictedMass_Iic T t)
    rw [he]
    exact ((cumulative_coordinate_measurable (min t T)).sub
      (cumulative_coordinate_measurable 0)).ennreal_ofReal
  · have he : (fun ω => restrictedMass T ω univ) =
        fun ω => ENNReal.ofReal (cumulative ω T - cumulative ω 0) := by
      funext ω
      rw [restrictedMass, Measure.restrict_apply_univ, massMeasure_Icc]
    rw [he]
    exact ((cumulative_coordinate_measurable T).sub
      (cumulative_coordinate_measurable 0)).ennreal_ofReal

theorem massMeasure_measurable : Measurable massMeasure := by
  apply Measure.measurable_measure.mpr
  intro s hs
  have he : (fun ω => massMeasure ω s) =
      fun ω => ⨆ N : ℕ, restrictedMass (N : ℝ≥0) ω s := by
    funext ω
    have hmono : Monotone (fun N : ℕ => s ∩ Icc (0 : ℝ≥0) (N : ℝ≥0)) := by
      intro N M hNM u hu
      exact ⟨hu.1, hu.2.1, hu.2.2.trans (by exact_mod_cast hNM)⟩
    have hU : (⋃ N : ℕ, s ∩ Icc (0 : ℝ≥0) (N : ℝ≥0)) = s := by
      ext t
      constructor
      · intro h
        obtain ⟨_, ht⟩ := mem_iUnion.mp h
        exact ht.1
      · intro ht
        obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
        exact mem_iUnion.mpr ⟨N, ht, t.property, by exact_mod_cast hN.le⟩
    calc
      massMeasure ω s = massMeasure ω (⋃ N : ℕ, s ∩ Icc 0 (N : ℝ≥0)) :=
        congrArg (massMeasure ω) hU.symm
      _ = ⨆ N : ℕ, massMeasure ω (s ∩ Icc 0 (N : ℝ≥0)) := hmono.measure_iUnion
      _ = ⨆ N : ℕ, restrictedMass (N : ℝ≥0) ω s := by
        congr 1
        funext N
        rw [restrictedMass, Measure.restrict_apply hs]
  rw [he]
  exact Measurable.iSup (fun N : ℕ =>
    (Measure.measurable_coe hs).comp (restrictedMass_measurable N))

def massKernel : Kernel SampleSpace ℝ≥0 := ⟨massMeasure, massMeasure_measurable⟩

theorem massKernel_apply (ω : SampleSpace) (s : Set ℝ≥0) : massKernel ω s = massMeasure ω s := rfl

end OperatorDerivativeRewrite.Foundation.BrownianMassMeasurableKernel
