import Foundation.BackwardHeatLpRealization
import Foundation.HigherHeatSchwartzContinuity

/-! Actual backward Schwartz kernel observables as continuous Bochner-valued processes. -/
noncomputable section
open MeasureTheory FourierTransform Filter
open scoped NNReal ENNReal Topology SchwartzMap BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.BackwardSchwartzLpRealization
open HigherHeatContinuousCylinders HigherHeatLpControls BoundedMovingLpProcess
open HigherHeatBackwardSchwartz HigherHeatSchwartzContinuity

def observable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ)) (t : ℝ) : Path →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ω => backward m hm T t.toNNReal f (ω.val t))
    ((backward_joint_continuous m hm T f).comp
      (continuous_const.prodMk (coordinate_continuous t)))
    (∫ ξ, ‖𝓕 f ξ‖) (fun ω => backward_bound m hm T t.toNNReal f (ω.val t))

theorem observable_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ))
    (t : ℝ) (ω : Path) : observable m hm T f t ω = backward m hm T t.toNNReal f (ω.val t) := rfl

theorem joint_continuous (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ)) :
    Continuous (fun z : ℝ × Path => observable m hm T f z.1 z.2) := by
  have he : Continuous (fun z : ℝ × Path => z.2.val z.1) := by fun_prop
  exact (backward_joint_continuous m hm T f).comp
    ((show Continuous (fun z : ℝ × Path => z.1.toNNReal) by fun_prop).prodMk he)

theorem observable_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ))
    (t : ℝ) (ω : Path) : ‖observable m hm T f t ω‖ ≤ ∫ ξ, ‖𝓕 f ξ‖ :=
  backward_bound m hm T t.toNNReal f (ω.val t)

theorem actual_kernel (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ))
    (t : ℝ) (ht : t.toNNReal < T) (ω : Path) :
    observable m hm T f t ω = ∫ᵛ y, f (ω.val t + y)
      ∂<•HigherHeatSignedLaws.law m hm (T-t.toNNReal) (tsub_pos_iff_lt.mpr ht) := by
  rw [HigherHeatSignedLaws.law, SignedDensityIntegral.integral_density volume _
    (HigherHeatSignedLaws.realKernel m hm _ _).integrable
    (HigherHeatSignedLaws.realKernel m hm _ _).continuous.measurable
    (fun y => f (ω.val t + y)) (f.continuous.comp (continuous_const.add continuous_id)).measurable
    (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f _)]
  change HigherHeatSchwartzSemigroup.evolve m hm (T-t.toNNReal) f (ω.val t) = _
  rw [← HigherHeatSchwartzTransition.transition_evolve m hm _ (tsub_pos_iff_lt.mpr ht)]
  unfold HigherHeatBackwardFourier.transition
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by simp only [Complex.real_smul]; ring)

variable (μ : Measure Path) [IsFiniteMeasure μ] (k : ℕ) [Fact (0 < k)]

def realization (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ)) :
    ℝ → Lp ℂ (power k) μ := process μ k (observable m hm T f)

theorem realization_ae (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    realization μ k m hm T f t =ᵐ[μ] observable m hm T f t := process_ae μ k _ t

theorem realization_continuous (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ)) :
    Continuous (realization μ k m hm T f) :=
  continuous_process μ k _ (joint_continuous m hm T f) _ (observable_bound m hm T f)

theorem realization_memLp (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ))
    (q : ℝ≥0∞) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    MemLp (realization μ k m hm T f) q ν :=
  process_memLp μ k _ (joint_continuous m hm T f) _
    (integral_nonneg (fun _ => norm_nonneg _)) (observable_bound m hm T f) q ν

theorem terminal_ae (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ)) :
    realization μ k m hm T f T =ᵐ[μ] (fun ω => f (ω.val T)) := by
  filter_upwards [realization_ae μ k m hm T f T] with ω he
  rw [he, observable_apply, Real.toNNReal_coe, backward_terminal]

theorem initial_ae (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ, ℂ)) :
    realization μ k m hm T f 0 =ᵐ[μ] (fun _ => HigherHeatSchwartzCalculus.mean m T f) := by
  filter_upwards [realization_ae μ k m hm T f 0] with ω he
  rw [he, observable_apply, Real.toNNReal_zero, ω.property]
  exact backward_initial m hm T hT f

end OperatorDerivativeRewrite.Foundation.BackwardSchwartzLpRealization
