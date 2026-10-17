import Foundation.BrownianMassRandomTimeChange
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Physical time is the forward image of ordinary time plus clock mass.
Ordinary time on NNReal is explicitly the image of positive real Lebesgue time. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianClockMeasureTransport
open InfiniteGaussian BrownianMassStieltjesSupport BrownianRandomMassClock
open BrownianMassRandomTimeChange

def ordinaryTime : Measure ℝ≥0 :=
  Measure.map Real.toNNReal ((volume : Measure ℝ).restrict (Ioi 0))

theorem positive_preimage_Iic (t : ℝ≥0) :
    Real.toNNReal ⁻¹' Iic t ∩ Ioi 0 = Ioc 0 (t : ℝ) := by
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_Ioc]
  constructor
  · rintro ⟨hx, hp⟩
    exact ⟨hp, (Real.toNNReal_le_iff_le_coe).mp hx⟩
  · rintro ⟨hp, hx⟩
    exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hx, hp⟩

theorem ordinaryTime_Iic (t : ℝ≥0) : ordinaryTime (Iic t) = (t : ℝ≥0∞) := by
  rw [ordinaryTime, Measure.map_apply continuous_real_toNNReal.measurable measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage continuous_real_toNNReal.measurable),
    positive_preimage_Iic, Real.volume_Ioc, sub_zero, ENNReal.ofReal_coe_nnreal]

theorem measure_ext_initial {μ ν : Measure ℝ≥0}
    (hfinite : ∀ t : ℝ≥0, μ (Iic t) ≠ ∞)
    (heq : ∀ t : ℝ≥0, μ (Iic t) = ν (Iic t)) : μ = ν := by
  have hgen : (inferInstance : MeasurableSpace ℝ≥0) =
      MeasurableSpace.generateFrom (range (Iic : ℝ≥0 → Set ℝ≥0)) := by
    rw [(inferInstance : BorelSpace ℝ≥0).measurable_eq, borel_eq_generateFrom_Iic]
  apply Measure.ext_of_generateFrom_of_iUnion (range (Iic : ℝ≥0 → Set ℝ≥0))
    (fun n : ℕ => Iic (n : ℝ≥0)) hgen isPiSystem_Iic
  · ext t
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
    exact ⟨n, by exact_mod_cast hn.le⟩
  · exact fun n => ⟨(n : ℝ≥0), rfl⟩
  · exact fun n => hfinite n
  · rintro _ ⟨t, rfl⟩
    exact heq t

theorem massMeasure_Iic (ω : SampleSpace) (t : ℝ≥0) :
    massMeasure ω (Iic t) = (mass ω t : ℝ≥0∞) := by
  have he : Iic t = Icc (0 : ℝ≥0) t := by ext u; simp
  rw [he, massMeasure_Icc, ← mass_coe, ENNReal.ofReal_coe_nnreal]

def clockMeasure (κ : ℝ≥0) (ω : SampleSpace) : Measure ℝ≥0 :=
  ordinaryTime + (κ : ℝ≥0∞) • massMeasure ω

theorem clockMeasure_Iic (κ : ℝ≥0) (ω : SampleSpace) (t : ℝ≥0) :
    clockMeasure κ ω (Iic t) = (forward κ ω t : ℝ≥0∞) := by
  simp only [clockMeasure, Measure.add_apply, Measure.smul_apply, ordinaryTime_Iic,
    massMeasure_Iic, smul_eq_mul, forward, StickyTimeChangeClock.clock,
    ENNReal.coe_add, ENNReal.coe_mul]

theorem forward_preimage_Iic (κ : ℝ≥0) (ω : SampleSpace) (t : ℝ≥0) :
    forward κ ω ⁻¹' Iic t = Iic (inverse κ ω t) := by
  ext s
  change forward κ ω s ≤ t ↔ s ≤ inverse κ ω t
  constructor
  · intro h
    have := inverse_monotone κ ω h
    simpa only [inverse_forward] using this
  · intro h
    have := (forward_strictMono κ ω).monotone h
    simpa only [forward_inverse] using this

theorem forward_map_clockMeasure (κ : ℝ≥0) (ω : SampleSpace) :
    Measure.map (forward κ ω) (clockMeasure κ ω) = ordinaryTime := by
  have he (t : ℝ≥0) :
      (Measure.map (forward κ ω) (clockMeasure κ ω)) (Iic t) = (t : ℝ≥0∞) := by
    rw [Measure.map_apply (forward_continuous κ ω).measurable measurableSet_Iic,
      forward_preimage_Iic, clockMeasure_Iic, forward_inverse]
  exact measure_ext_initial (fun t => by rw [he]; exact ENNReal.coe_ne_top)
    (fun t => (he t).trans (ordinaryTime_Iic t).symm)

end OperatorDerivativeRewrite.Foundation.BrownianClockMeasureTransport
