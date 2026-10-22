import Foundation.IBMGermPredictableStep

/-! Actual support domination for elementary predictable indicator energies. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMGermIndicatorSupport
open IBMTimeAveragedObservable IBMObservedTerminalMartingale
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMGermPredictableStep
set_option backward.isDefEq.respectTransparency false

def sumClass {ι : Type*} (F : JointL2) (I : Finset ι) (s t : ι → ℝ≥0)
    (a : ∀ i, Coefficient (s i)) : JointL2 :=
  ∑ i ∈ I, stepClass F (s i) (t i) (a i)

theorem sumClass_ae {ι : Type*} (F : JointL2) (I : Finset ι) (s t : ι → ℝ≥0)
    (a : ∀ i, Coefficient (s i)) (hst : ∀ i ∈ I, s i ≤ t i) :
    sumClass F I s t a =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => ∑ i ∈ I, (a i).function ω * (channel F (t i) ω - channel F (s i) ω) := by
  have hc := (Finset.eventually_all I).mpr (fun i hi => stepClass_ae F (hst i hi) (a i))
  filter_upwards [Lp.coeFn_finsetSum I (fun i => stepClass F (s i) (t i) (a i)), hc]
    with ω hs ha
  rw [show sumClass F I s t a ω = _ from hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => ha i hi

theorem finite_energy {ι : Type*} (F : JointL2) (I : Finset ι) (s t : ι → ℝ≥0)
    (a : ∀ i, Coefficient (s i)) (hst : ∀ i ∈ I, s i ≤ t i)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → t i ≤ s j ∨ t j ≤ s i) :
    ‖sumClass F I s t a‖ ^ 2 = ∑ i ∈ I, ‖stepClass F (s i) (t i) (a i)‖ ^ 2 := by
  classical
  unfold sumClass
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have ho : inner ℝ (stepClass F (s i) (t i) (a i))
        (∑ j ∈ I, stepClass F (s j) (t j) (a j)) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      rcases hd i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hij with h | h
      · exact disjoint_steps_orthogonal F (hst i (Finset.mem_insert_self _ _)) h
          (hst j (Finset.mem_insert_of_mem hj)) (a i) (a j)
      · rw [real_inner_comm]
        exact disjoint_steps_orthogonal F (hst j (Finset.mem_insert_of_mem hj)) h
          (hst i (Finset.mem_insert_self _ _)) (a j) (a i)
    rw [Finset.sum_insert hi, norm_add_sq_real, ho,
      ih (fun j hj => hst j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk => hd j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)),
      Finset.sum_insert hi]
    ring

theorem idempotent_sum_pairing {ι : Type*} (F : JointL2) (I : Finset ι)
    (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i)) (hst : ∀ i ∈ I, s i ≤ t i)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (ha : ∀ i ∈ I, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, (a i).function ω ^ 2 = (a i).function ω) :
    inner ℝ F (sumClass F I s t a) = ‖sumClass F I s t a‖ ^ 2 := by
  rw [finite_energy F I s t a hst hd]
  unfold sumClass
  rw [inner_sum]
  exact Finset.sum_congr rfl fun i hi => idempotent_pairing F (hst i hi) (a i) (ha i hi)

theorem zero_off_support {ι : Type*} (F : JointL2) (I : Finset ι)
    (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i)) (hst : ∀ i ∈ I, s i ≤ t i)
    (A : Set IBMSourceLaws.JointSample)
    (hH : ∀ r, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ω ∉ A →
      (∑ i ∈ I, IBMIntrinsicPredictableProcess.timeStep (s i) (t i) (a i) r ω) = 0) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ω ∉ A → sumClass F I s t a ω = 0 := by
  classical
  have hh := (Finset.eventually_all (I.image s ∪ I.image t)).mpr (fun r _ => hH r)
  filter_upwards [sumClass_ae F I s t a hst, hh] with ω hs hω hn
  rw [hs]
  exact IBMFiniteIntervalIdentification.interval_relation I s t (fun i => (a i).function ω)
    hst (fun r => channel F r ω) (fun r hr => hω r hr hn)

def supportedTerminal (F : JointL2) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet A) : JointL2 := ((Lp.memLp F).indicator hA).toLp _

theorem supportedTerminal_ae (F : JointL2) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet A) : supportedTerminal F A hA =ᵐ[IBMSourceLaws.jointMeasure]
      A.indicator (F : IBMSourceLaws.JointSample → ℝ) :=
  ((Lp.memLp F).indicator hA).coeFn_toLp

theorem supportedTerminal_energy (F : JointL2) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet A) : ‖supportedTerminal F A hA‖ ^ 2 =
      ∫ ω in A, F ω ^ 2 ∂IBMSourceLaws.jointMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [supportedTerminal_ae F A hA] with ω hω
  rw [hω, Real.inner_apply]
  by_cases ha : ω ∈ A <;> simp [Set.indicator, ha, pow_two]

theorem energy_support_bound {ι : Type*} (F : JointL2) (I : Finset ι)
    (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i)) (hst : ∀ i ∈ I, s i ≤ t i)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (ha : ∀ i ∈ I, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, (a i).function ω ^ 2 = (a i).function ω)
    (A : Set IBMSourceLaws.JointSample) (hA : MeasurableSet A)
    (hH : ∀ r, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ω ∉ A →
      (∑ i ∈ I, IBMIntrinsicPredictableProcess.timeStep (s i) (t i) (a i) r ω) = 0) :
    ‖sumClass F I s t a‖ ^ 2 ≤ ∫ ω in A, F ω ^ 2 ∂IBMSourceLaws.jointMeasure := by
  have he : inner ℝ (supportedTerminal F A hA) (sumClass F I s t a) =
      inner ℝ F (sumClass F I s t a) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [supportedTerminal_ae F A hA, zero_off_support F I s t a hst A hH]
      with ω hf hz
    rw [hf, Real.inner_apply, Real.inner_apply]
    by_cases hn : ω ∈ A
    · simp only [Set.indicator_of_mem hn]
    · rw [Set.indicator_of_notMem hn, hz hn, mul_zero, mul_zero]
  have hp := idempotent_sum_pairing F I s t a hst hd ha
  have hn := sq_nonneg ‖supportedTerminal F A hA - sumClass F I s t a‖
  rw [norm_sub_sq_real, he, hp] at hn
  rw [← supportedTerminal_energy F A hA]
  linarith

theorem integral_identification {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : JointL2) (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i))
    (u v : κ → ℝ≥0) (b : ∀ j, Coefficient (u j))
    (hst : ∀ i, s i ≤ t i) (huv : ∀ j, u j ≤ v j)
    (he : ∀ r, (fun ω => ∑ i, IBMIntrinsicPredictableProcess.timeStep (s i) (t i) (a i) r ω)
      =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => ∑ j, IBMIntrinsicPredictableProcess.timeStep (u j) (v j) (b j) r ω)) :
    sumClass F Finset.univ s t a = sumClass F Finset.univ u v b := by
  apply Lp.ext
  have hh := IBMFiniteIntervalIdentification.interval_equal_ae IBMSourceLaws.jointMeasure
    s t (fun i => (a i).function) u v (fun j => (b j).function) hst huv (channel F) he
  exact (sumClass_ae F Finset.univ s t a (fun i _ => hst i)).trans
    (hh.trans (sumClass_ae F Finset.univ u v b (fun j _ => huv j)).symm)

end OperatorDerivativeRewrite.Foundation.IBMGermIndicatorSupport
