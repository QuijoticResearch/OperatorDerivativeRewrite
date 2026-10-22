import Foundation.IBMRawObservedMartingale
import Foundation.IBMIntrinsicPredictableProcess

/-! Actual random predictable integration for IBM terminal-observable
martingales, reusing the full raw-past coefficient type and predictability. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTerminalPredictableStep
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMRawObservedMartingale
open IBMIntrinsicMartingaleStep (Coefficient)
set_option backward.isDefEq.respectTransparency false

def increment (F : JointL2) (s t : ℝ≥0) : IBMSourceLaws.JointSample → ℝ :=
  rawValue F t - rawValue F s

theorem increment_memLp (F : JointL2) (s t : ℝ≥0) :
    MemLp (increment F s t) 2 IBMSourceLaws.jointMeasure :=
  (rawValue_memLp F t).sub (rawValue_memLp F s)

theorem increment_condExp (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) :
    IBMSourceLaws.jointMeasure[increment F s t | naturalFiltration s]
      =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
  have he := condExp_sub ((raw_martingale F).integrable t) ((raw_martingale F).integrable s)
    (naturalFiltration s)
  have hs := condExp_of_stronglyMeasurable (naturalFiltration.le s)
    ((raw_martingale F).stronglyAdapted s) ((raw_martingale F).integrable s)
  exact he.trans ((((raw_martingale F).condExp_ae_eq hst).sub (EventuallyEq.of_eq hs)).trans
    (by filter_upwards [] with ω; simp))

def step (F : JointL2) (s t : ℝ≥0) (a : Coefficient s) : IBMSourceLaws.JointSample → ℝ :=
  a.function * increment F s t

theorem step_memLp (F : JointL2) (s t : ℝ≥0) (a : Coefficient s) :
    MemLp (step F s t a) 2 IBMSourceLaws.jointMeasure := by
  refine (increment_memLp F s t).of_le_mul (c := a.bound)
    ((a.adapted.mono (naturalFiltration.le s)).aestronglyMeasurable.mul
      (increment_memLp F s t).aestronglyMeasurable) ?_
  filter_upwards [a.bounded] with ω hω
  exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))

def stepClass (F : JointL2) (s t : ℝ≥0) (a : Coefficient s) : JointL2 :=
  (step_memLp F s t a).toLp _

theorem stepClass_ae (F : JointL2) (s t : ℝ≥0) (a : Coefficient s) :
    stepClass F s t a =ᵐ[IBMSourceLaws.jointMeasure] step F s t a :=
  (step_memLp F s t a).coeFn_toLp

theorem step_condExp (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    IBMSourceLaws.jointMeasure[step F s t a | naturalFiltration s]
      =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
  have he := condExp_mul_of_stronglyMeasurable_left a.adapted
    ((step_memLp F s t a).integrable (by norm_num))
    ((increment_memLp F s t).integrable (by norm_num))
  exact he.trans (by
    filter_upwards [increment_condExp F hst] with ω hω
    simp only [Pi.mul_apply, hω, mul_zero])

theorem stepClass_mem_past (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    stepClass F s t a ∈ past t := by
  have hm := (a.adapted.mono (naturalFiltration.mono hst)).mul
    (((raw_martingale F).stronglyAdapted t).sub
      (((raw_martingale F).stronglyAdapted s).mono (naturalFiltration.mono hst)))
  exact hm.aestronglyMeasurable.congr (stepClass_ae F s t a).symm

theorem stepClass_projection_zero (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    (past s).starProjection (stepClass F s t a) = 0 := by
  apply Lp.ext
  exact (IBMCofinalPast.projection_ae s (stepClass F s t a)).trans
    ((condExp_congr_ae (stepClass_ae F s t a)).trans
      ((step_condExp F hst a).trans (Lp.coeFn_zero _ _ _).symm))

theorem past_inner_step_zero (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s)
    (g : JointL2) (hg : g ∈ past s) : inner ℝ g (stepClass F s t a) = 0 := by
  have he := (past s).inner_starProjection_left_eq_right g (stepClass F s t a)
  rw [Submodule.starProjection_eq_self_iff.mpr hg, stepClass_projection_zero F hst a,
    inner_zero_right] at he
  exact he

theorem disjoint_steps_orthogonal (F : JointL2) {r u s t : ℝ≥0}
    (hru : r ≤ u) (hus : u ≤ s) (hst : s ≤ t) (a : Coefficient r) (b : Coefficient s) :
    inner ℝ (stepClass F r u a) (stepClass F s t b) = 0 :=
  past_inner_step_zero F hst b _
    ((stepClass_mem_past F hru a).mono (naturalFiltration.mono hus))

theorem step_energy (F : JointL2) (s t : ℝ≥0) (a : Coefficient s) :
    ‖stepClass F s t a‖ ^ 2 =
      ∫ ω, a.function ω ^ 2 * increment F s t ω ^ 2 ∂IBMSourceLaws.jointMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [stepClass_ae F s t a] with ω hω
  rw [hω, Real.inner_apply]
  change (a.function ω * increment F s t ω) * (a.function ω * increment F s t ω) = _
  ring

theorem coefficient_process_predictable (s t : ℝ≥0) (a : Coefficient s) :
    IsStronglyPredictable naturalFiltration (IBMIntrinsicPredictableProcess.timeStep s t a) :=
  IBMIntrinsicPredictableProcess.timeStep_predictable s t a

theorem quadratic_agreement {s t H : ℝ≥0} (hs : s ≤ H) (ht : t ≤ H) (a : Coefficient s) :
    stepClass (IBMIntrinsicQuadraticMartingale.valueClass H : JointL2) s t a =
      IBMIntrinsicMartingaleStep.stepClass s t a := by
  have he (u : ℝ≥0) (hu : u ≤ H) :
      rawValue (IBMIntrinsicQuadraticMartingale.valueClass H : JointL2) u
        =ᵐ[IBMSourceLaws.jointMeasure] IBMIntrinsicQuadraticMartingale.value u := by
    have hp := rawClass_ae (IBMIntrinsicQuadraticMartingale.valueClass H : JointL2) u
    change (past u).starProjection (IBMIntrinsicQuadraticMartingale.valueClass H : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] _ at hp
    rw [IBMIntrinsicMartingaleEndpoint.projection_value hu] at hp
    exact hp.symm.trans (IBMIntrinsicQuadraticMartingale.valueClass_ae u)
  apply Lp.ext
  filter_upwards [stepClass_ae _ s t a, IBMIntrinsicMartingaleStep.stepClass_ae s t a,
    he s hs, he t ht] with ω hn ho hsω htω
  rw [hn, ho]
  simp only [step, increment, IBMIntrinsicMartingaleStep.step,
    IBMIntrinsicMartingaleStep.increment, Pi.mul_apply, Pi.sub_apply, hsω, htω]

end OperatorDerivativeRewrite.Foundation.IBMTerminalPredictableStep
