import Foundation.IBMTerminalEnergyMeasure
import Foundation.IBMGridDifferenceControl

/-! Actual coefficient-localized countably additive future-time energy.
The full joint predictable measure is not defined here. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMWeightedTerminalEnergy
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMObservedTerminalMartingale
open IBMRightGermFiltration IBMTerminalEnergyMeasure
open IBMIntrinsicMartingaleStep (Coefficient)
set_option backward.isDefEq.respectTransparency false

theorem weighted_memLp (F : JointL2) (s : ℝ≥0) (a : Coefficient s) :
    MemLp (a.function * (F : IBMSourceLaws.JointSample → ℝ)) 2 IBMSourceLaws.jointMeasure := by
  apply (Lp.memLp F).of_le_mul (c := a.bound)
    ((a.adapted.mono (naturalFiltration.le s)).aestronglyMeasurable.mul
      (Lp.memLp F).aestronglyMeasurable)
  filter_upwards [a.bounded] with ω hω
  exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))

def weightedTerminal (F : JointL2) (s : ℝ≥0) (a : Coefficient s) : JointL2 :=
  (weighted_memLp F s a).toLp _

theorem weightedTerminal_ae (F : JointL2) (s : ℝ≥0) (a : Coefficient s) :
    weightedTerminal F s a =ᵐ[IBMSourceLaws.jointMeasure] a.function * F :=
  (weighted_memLp F s a).coeFn_toLp

theorem weighted_channel (F : JointL2) (s : ℝ≥0) (a : Coefficient s)
    {t : ℝ≥0} (hst : s ≤ t) :
    channel (weightedTerminal F s a) t =ᵐ[IBMSourceLaws.jointMeasure] a.function * channel F t := by
  have hm := a.adapted.mono ((naturalFiltration.mono hst).trans (raw_le_germ t))
  have he := condExp_mul_of_stronglyMeasurable_left hm
    ((weighted_memLp F s a).integrable (by norm_num))
    ((Lp.memLp F).integrable (by norm_num))
  have hp := projection_ae t (weightedTerminal F s a)
  change channel (weightedTerminal F s a) t =ᵐ[IBMSourceLaws.jointMeasure]
    IBMSourceLaws.jointMeasure[weightedTerminal F s a | germFiltration t] at hp
  exact hp.trans ((condExp_congr_ae (weightedTerminal_ae F s a)).trans
    (he.trans (EventuallyEq.rfl.mul (projection_ae t F).symm)))

theorem weighted_increment_norm (F : JointL2) (s : ℝ≥0) (a : Coefficient s)
    {u t : ℝ≥0} (hsu : s ≤ u) (hut : u ≤ t) :
    ‖channelClass (weightedTerminal F s a) t - channelClass (weightedTerminal F s a) u‖ ^ 2 =
      ∫ ω, a.function ω ^ 2 * (channel F t ω - channel F u ω) ^ 2 ∂IBMSourceLaws.jointMeasure := by
  rw [actual_increment_energy]
  apply integral_congr_ae
  filter_upwards [weighted_channel F s a hsu, weighted_channel F s a (hsu.trans hut)] with ω hu ht
  rw [hu, ht]
  simp only [Pi.mul_apply]
  ring

def localizedMeasure (F : JointL2) (s : ℝ≥0) (a : Coefficient s) : Measure ℝ≥0 :=
  (energyMeasure (weightedTerminal F s a)).restrict (Ioi s)

theorem localized_finite (F : JointL2) (s : ℝ≥0) (a : Coefficient s) :
    IsFiniteMeasure (localizedMeasure F s a) := by
  let _ := finite_measure (weightedTerminal F s a)
  unfold localizedMeasure
  infer_instance

theorem localized_increment (F : JointL2) (s : ℝ≥0) (a : Coefficient s)
    {u t : ℝ≥0} (hsu : s ≤ u) (hut : u ≤ t) :
    localizedMeasure F s a (Ioc u t) = ENNReal.ofReal
      (∫ ω, a.function ω ^ 2 * (channel F t ω - channel F u ω) ^ 2
        ∂IBMSourceLaws.jointMeasure) := by
  have hsub : Ioc u t ⊆ Ioi s := fun _ h => hsu.trans_lt h.1
  rw [localizedMeasure, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsub, energyMeasure_increment _ hut,
    weighted_increment_norm F s a hsu hut]

theorem weighted_time_additivity (F : JointL2) (s : ℝ≥0) (a : Coefficient s)
    {u v t : ℝ≥0} (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    (∫ ω, a.function ω ^ 2 * (channel F t ω - channel F u ω) ^ 2
      ∂IBMSourceLaws.jointMeasure) =
      (∫ ω, a.function ω ^ 2 * (channel F v ω - channel F u ω) ^ 2
        ∂IBMSourceLaws.jointMeasure) +
      (∫ ω, a.function ω ^ 2 * (channel F t ω - channel F v ω) ^ 2
        ∂IBMSourceLaws.jointMeasure) := by
  rw [← weighted_increment_norm F s a hsu (huv.trans hvt),
    ← weighted_increment_norm F s a hsu huv,
    ← weighted_increment_norm F s a (hsu.trans huv) hvt,
    ← increment_energy _ (huv.trans hvt), ← increment_energy _ huv, ← increment_energy _ hvt]
  ring

theorem later_consistency (F : JointL2) {s u r t : ℝ≥0} (a : Coefficient s)
    (hsu : s ≤ u) (hur : u ≤ r) (hrt : r ≤ t) :
    localizedMeasure F s a (Ioc r t) =
      localizedMeasure F u (IBMIntrinsicMartingaleRefinement.later hsu a) (Ioc r t) := by
  rw [localized_increment F s a (hsu.trans hur) hrt, localized_increment F u _ hur hrt]
  rfl

def eventCoefficient (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[naturalFiltration s] A) : Coefficient s where
  function := A.indicator (fun _ => (1 : ℝ))
  adapted := stronglyMeasurable_const.indicator hA
  bound := 1
  bounded := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]

def eventEnergy (F : JointL2) (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[naturalFiltration s] A) : Measure ℝ≥0 :=
  localizedMeasure F s (eventCoefficient s A hA)

theorem eventEnergy_increment (F : JointL2) (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[naturalFiltration s] A) {u t : ℝ≥0} (hsu : s ≤ u) (hut : u ≤ t) :
    eventEnergy F s A hA (Ioc u t) = ENNReal.ofReal
      (∫ ω in A, (channel F t ω - channel F u ω) ^ 2 ∂IBMSourceLaws.jointMeasure) := by
  rw [eventEnergy, localized_increment F s _ hsu hut]
  congr 1
  rw [← integral_indicator (naturalFiltration.le s A hA)]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hω : ω ∈ A <;> simp [eventCoefficient, Set.indicator, hω]

theorem increment_square_integrable (F : JointL2) (u t : ℝ≥0) :
    Integrable (fun ω => (channel F t ω - channel F u ω) ^ 2) IBMSourceLaws.jointMeasure := by
  have hm := (channel_memLp F t).sub (channel_memLp F u)
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm

def incrementMeasure (F : JointL2) (u t : ℝ≥0) : Measure IBMSourceLaws.JointSample :=
  IBMSourceLaws.jointMeasure.withDensity
    (fun ω => ENNReal.ofReal ((channel F t ω - channel F u ω) ^ 2))

theorem incrementMeasure_apply (F : JointL2) (u t : ℝ≥0)
    {A : Set IBMSourceLaws.JointSample} (hA : MeasurableSet A) :
    incrementMeasure F u t A = ENNReal.ofReal
      (∫ ω in A, (channel F t ω - channel F u ω) ^ 2 ∂IBMSourceLaws.jointMeasure) := by
  rw [incrementMeasure, withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal (increment_square_integrable F u t).integrableOn
    (ae_of_all _ (fun ω => sq_nonneg (channel F t ω - channel F u ω)))).symm

theorem incrementMeasure_finite (F : JointL2) (u t : ℝ≥0) :
    IsFiniteMeasure (incrementMeasure F u t) := by
  constructor
  rw [incrementMeasure_apply F u t MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top

theorem event_time_agreement (F : JointL2) (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[naturalFiltration s] A) {u t : ℝ≥0} (hsu : s ≤ u) (hut : u ≤ t) :
    eventEnergy F s A hA (Ioc u t) = incrementMeasure F u t A := by
  rw [eventEnergy_increment F s A hA hsu hut,
    incrementMeasure_apply F u t (naturalFiltration.le s A hA)]

theorem event_countable_additivity (F : JointL2) (s : ℝ≥0)
    (A : ℕ → Set IBMSourceLaws.JointSample)
    (hA : ∀ i, MeasurableSet[naturalFiltration s] (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    {u t : ℝ≥0} (hsu : s ≤ u) (hut : u ≤ t) :
    eventEnergy F s (⋃ i, A i) (MeasurableSet.iUnion hA) (Ioc u t) =
      ∑' i, eventEnergy F s (A i) (hA i) (Ioc u t) := by
  rw [event_time_agreement F s _ (MeasurableSet.iUnion hA) hsu hut]
  rw [measure_iUnion hdis (fun i => naturalFiltration.le s (A i) (hA i))]
  exact tsum_congr fun i => (event_time_agreement F s (A i) (hA i) hsu hut).symm

end OperatorDerivativeRewrite.Foundation.IBMWeightedTerminalEnergy
