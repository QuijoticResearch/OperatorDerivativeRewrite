import Foundation.IBMFirstChaosMixedStein
import Foundation.IBMBoundaryResidualLimit
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! Actual correction expectations for shifted Schwartz tests. All derivative
tests and mixed moments are on verified integrable Gaussian source domains. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMCorrectionStein
open InfiniteGaussian IBMFirstChaosDiagonalStein IBMFirstChaosMixedStein

def jet (g : SchwartzMap ℝ ℝ) : ℕ → SchwartzMap ℝ ℝ
  | 0 => g
  | k+1 => SchwartzMap.derivCLM ℝ ℝ (jet g k)

def shiftedJet (g : SchwartzMap ℝ ℝ) (a : ℝ) (k : ℕ) (x : ℝ) : ℝ := jet g k (a+x)

theorem shiftedJet_smooth (g : SchwartzMap ℝ ℝ) (a : ℝ) (k : ℕ) :
    ContDiff ℝ 2 (shiftedJet g a k) :=
  ((jet g k).smooth 2).comp (contDiff_const.add contDiff_id)

theorem shiftedJet_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) (k : ℕ) :
    deriv (shiftedJet g a k) = shiftedJet g a (k+1) := by
  funext x
  have he := ((jet g k).hasDerivAt (a+x)).comp x ((hasDerivAt_id x).const_add a)
  have he' : HasDerivAt (shiftedJet g a k) (shiftedJet g a (k+1) x) x := by
    convert he using 1 <;> first | rfl | simp [shiftedJet, jet]
  exact he'.deriv

theorem shiftedJet_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (k : ℕ) (x : ℝ) :
    ‖shiftedJet g a k x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g k) :=
  IBMBoundaryResidualLimit.schwartz_bound _ _

theorem shiftedJet_lipschitz (g : SchwartzMap ℝ ℝ) (a : ℝ) (k : ℕ) :
    LipschitzWith (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 (jet g k)))
      (shiftedJet g a k) := by
  have ht : LipschitzWith 1 (fun x : ℝ => a+x) := by
    intro x y
    simp only [edist_dist, Real.dist_eq, add_sub_add_left_eq_sub, NNReal.coe_one,
      ENNReal.coe_one, one_mul]
    exact le_rfl
  change LipschitzWith _ ((jet g k) ∘ (fun x : ℝ => a+x))
  simpa only [mul_one] using
    (IBMBoundaryWeightedClock.schwartz_lipschitz (jet g k)).comp ht

theorem shifted_first (g : SchwartzMap ℝ ℝ) (a : ℝ) (k : ℕ)
    (u v : CoefficientSpace) :
    (∫ ω, firstChaosEmbedding v ω * shiftedJet g a k (firstChaosEmbedding u ω)
      ∂gaussianProduct) =
      inner ℝ u v * ∫ ω, shiftedJet g a (k+1) (firstChaosEmbedding u ω)
        ∂gaussianProduct := by
  have hb : ∀ x, ‖deriv (shiftedJet g a k) x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (jet g (k+1)) := by
    rw [shiftedJet_deriv]; exact shiftedJet_bound g a (k+1)
  simpa only [shiftedJet_deriv] using
    first_mixed (shiftedJet_smooth g a k) (shiftedJet_bound g a k) hb u v

theorem shifted_second (g : SchwartzMap ℝ ℝ) (a : ℝ) (k : ℕ)
    (u v : CoefficientSpace) :
    (∫ ω, (firstChaosEmbedding v ω)^2 * shiftedJet g a k (firstChaosEmbedding u ω)
      ∂gaussianProduct) =
      ‖v‖^2 * (∫ ω, shiftedJet g a k (firstChaosEmbedding u ω) ∂gaussianProduct) +
      (inner ℝ u v)^2 * ∫ ω, shiftedJet g a (k+2) (firstChaosEmbedding u ω)
        ∂gaussianProduct := by
  have hb : ∀ x, ‖deriv (shiftedJet g a k) x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (jet g (k+1)) := by
    rw [shiftedJet_deriv]; exact shiftedJet_bound g a (k+1)
  have hc : ∀ x, ‖deriv (deriv (shiftedJet g a k)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (jet g (k+2)) := by
    rw [shiftedJet_deriv, shiftedJet_deriv]; exact shiftedJet_bound g a (k+2)
  simpa only [shiftedJet_deriv] using
    second_mixed (shiftedJet_smooth g a k) (shiftedJet_bound g a k) hb hc u v

def correction (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v w : CoefficientSpace) : ℝ :=
  ∫ ω, shiftedJet g a 2 (firstChaosEmbedding u ω) * (firstChaosEmbedding v ω)^2 +
    shiftedJet g a 1 (firstChaosEmbedding u ω) * firstChaosEmbedding w ω ∂gaussianProduct

theorem correction_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v w : CoefficientSpace) :
    Integrable (fun ω =>
      shiftedJet g a 2 (firstChaosEmbedding u ω) * (firstChaosEmbedding v ω)^2 +
      shiftedJet g a 1 (firstChaosEmbedding u ω) * firstChaosEmbedding w ω)
      gaussianProduct := by
  have h₁ := second_mixed_integrable u v (shiftedJet_smooth g a 2).continuous
    (shiftedJet_bound g a 2)
  have h₂ := first_mixed_integrable u w (shiftedJet_smooth g a 1).continuous
    (shiftedJet_bound g a 1)
  have hf : (fun ω =>
      shiftedJet g a 2 (firstChaosEmbedding u ω) * (firstChaosEmbedding v ω)^2 +
      shiftedJet g a 1 (firstChaosEmbedding u ω) * firstChaosEmbedding w ω) =
      (fun ω => (firstChaosEmbedding v ω)^2 * shiftedJet g a 2 (firstChaosEmbedding u ω)) +
      (fun ω => firstChaosEmbedding w ω * shiftedJet g a 1 (firstChaosEmbedding u ω)) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  rw [hf]
  exact h₁.add h₂

theorem correction_identity (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v w : CoefficientSpace) :
    correction g a u v w =
      (‖v‖^2 + inner ℝ u w) *
        (∫ ω, shiftedJet g a 2 (firstChaosEmbedding u ω) ∂gaussianProduct) +
      (inner ℝ u v)^2 *
        (∫ ω, shiftedJet g a 4 (firstChaosEmbedding u ω) ∂gaussianProduct) := by
  have h₁ := second_mixed_integrable u v (shiftedJet_smooth g a 2).continuous
    (shiftedJet_bound g a 2)
  have h₂ := first_mixed_integrable u w (shiftedJet_smooth g a 1).continuous
    (shiftedJet_bound g a 1)
  unfold correction
  simp_rw [mul_comm (shiftedJet g a 2 _) ((firstChaosEmbedding v _)^2),
    mul_comm (shiftedJet g a 1 _) (firstChaosEmbedding w _)]
  rw [integral_add h₁ h₂, shifted_second, shifted_first]
  ring

end OperatorDerivativeRewrite.Foundation.IBMCorrectionStein
