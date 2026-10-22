import Foundation.IBMIntrinsicQuadraticMartingale
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! Actual bounded predictable-step integration against the intrinsic IBM
quadratic martingale. Orthogonality uses conditioning, not Gaussian increments. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleStep
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable
open IBMIntrinsicQuadraticMartingale
set_option backward.isDefEq.respectTransparency false

def increment (s t : ℝ≥0) : IBMSourceLaws.JointSample → ℝ := value t - value s

theorem increment_memLp (s t : ℝ≥0) : MemLp (increment s t) 2 IBMSourceLaws.jointMeasure :=
  (value_memLp t).sub (value_memLp s)

theorem increment_condExp {s t : ℝ≥0} (hst : s ≤ t) :
    IBMSourceLaws.jointMeasure[increment s t | naturalFiltration s]
      =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
  have he := condExp_sub (actual_martingale.integrable t) (actual_martingale.integrable s)
    (naturalFiltration s)
  have hs := condExp_of_stronglyMeasurable (naturalFiltration.le s)
    (actual_martingale.stronglyAdapted s) (actual_martingale.integrable s)
  exact he.trans (((actual_martingale.condExp_ae_eq hst).sub (Filter.EventuallyEq.of_eq hs)).trans
    (by filter_upwards [] with ω; simp))

/-- A genuine bounded coefficient measurable in the full actual IBM past. -/
structure Coefficient (s : ℝ≥0) where
  function : IBMSourceLaws.JointSample → ℝ
  adapted : StronglyMeasurable[naturalFiltration s] function
  bound : ℝ
  bounded : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖function ω‖ ≤ bound

def step (s t : ℝ≥0) (a : Coefficient s) : IBMSourceLaws.JointSample → ℝ :=
  a.function * increment s t

theorem step_memLp (s t : ℝ≥0) (a : Coefficient s) :
    MemLp (step s t a) 2 IBMSourceLaws.jointMeasure := by
  refine (increment_memLp s t).of_le_mul (c := a.bound)
    ((a.adapted.mono (naturalFiltration.le s)).aestronglyMeasurable.mul
      (increment_memLp s t).aestronglyMeasurable) ?_
  filter_upwards [a.bounded] with ω hω
  exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))

def stepClass (s t : ℝ≥0) (a : Coefficient s) : JointL2 := (step_memLp s t a).toLp _

theorem stepClass_ae (s t : ℝ≥0) (a : Coefficient s) :
    stepClass s t a =ᵐ[IBMSourceLaws.jointMeasure] step s t a :=
  (step_memLp s t a).coeFn_toLp

theorem step_condExp {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    IBMSourceLaws.jointMeasure[step s t a | naturalFiltration s]
      =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
  have he := condExp_mul_of_stronglyMeasurable_left a.adapted
    ((step_memLp s t a).integrable (by norm_num))
    ((increment_memLp s t).integrable (by norm_num))
  exact he.trans (by
    filter_upwards [increment_condExp hst] with ω hω
    simp only [Pi.mul_apply, hω, mul_zero])

theorem stepClass_mem_past {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    stepClass s t a ∈ past t := by
  have hm := (a.adapted.mono (naturalFiltration.mono hst)).mul
    ((actual_martingale.stronglyAdapted t).sub
      ((actual_martingale.stronglyAdapted s).mono (naturalFiltration.mono hst)))
  exact hm.aestronglyMeasurable.congr (stepClass_ae s t a).symm

theorem step_integral_zero {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    (∫ ω, step s t a ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  have he := integral_condExp (μ := IBMSourceLaws.jointMeasure)
    (f := step s t a) (naturalFiltration.le s)
  rw [integral_congr_ae (step_condExp hst a), integral_zero] at he
  exact he.symm

theorem stepClass_condExp_zero {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    (condExpL2 ℝ ℝ (naturalFiltration.le s) (stepClass s t a) : JointL2) = 0 := by
  have he : (condExpL2 ℝ ℝ (naturalFiltration.le s) (stepClass s t a) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure]
        IBMSourceLaws.jointMeasure[stepClass s t a | naturalFiltration s] := by
    simpa only [Lp.toLp_coeFn] using (Lp.memLp (stepClass s t a)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (naturalFiltration.le s)
  apply Lp.ext
  exact he.trans ((condExp_congr_ae (stepClass_ae s t a)).trans
    ((step_condExp hst a).trans (Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure).symm))

theorem past_inner_step_zero {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s)
    (f : JointL2) (hf : f ∈ past s) : inner ℝ f (stepClass s t a) = 0 := by
  have he := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (naturalFiltration.le s)
    (stepClass s t a) f hf
  rw [stepClass_condExp_zero hst a, inner_zero_left] at he
  rw [real_inner_comm]
  exact he.symm

/-- Ordered disjoint actual stochastic steps are orthogonal, even with random
past-dependent coefficients. No increment independence is assumed. -/
theorem disjoint_steps_orthogonal {r u s t : ℝ≥0} (hru : r ≤ u) (hus : u ≤ s)
    (hst : s ≤ t) (a : Coefficient r) (b : Coefficient s) :
    inner ℝ (stepClass r u a) (stepClass s t b) = 0 :=
  past_inner_step_zero hst b _
    ((stepClass_mem_past hru a).mono (naturalFiltration.mono hus))

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleStep
