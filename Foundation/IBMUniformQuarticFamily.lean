import Foundation.IBMUniformClockOccupation
import Foundation.IBMJointQuartic

/-! Actual IBM uniform-grid quartic sums and their scenery-conditional mean
and fluctuation bounds. The clock is the existing constructed Brownian path. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformQuarticFamily
open InfiniteGaussian IBMSourceLaws IBMConstructedSources
open IBMUniformClockGridEnergy IBMUniformClockMaximum IBMUniformClockOccupation
open IBMQuarticOccupationEnergy IBMClockTraversalEnvelope
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.sceneryPath

def segment (T : ℝ≥0) (n k : ℕ) : ℝ≥0 × ℝ≥0 :=
  (grid (T / n) k, grid (T / n) (k + 1))

def intervals (T : ℝ≥0) (n : ℕ) : Finset (ℝ≥0 × ℝ≥0) :=
  (Finset.range n).image (segment T n)

theorem sum_intervals {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (f : (ℝ≥0 × ℝ≥0) → ℝ) :
    (∑ p ∈ intervals T n, f p) = ∑ k ∈ Finset.range n, f (segment T n k) := by
  unfold intervals
  rw [Finset.sum_image]
  intro i hi j hj hij
  exact grid_injective (div_pos hT (by exact_mod_cast hn)) (congrArg Prod.fst hij)

def quartic (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ k ∈ Finset.range n, (ibmValue (segment T n k).2 ω - ibmValue (segment T n k).1 ω) ^ 4

def clockMean (T : ℝ≥0) (n : ℕ) (ω : SampleSpace) : ℝ :=
  ∑ k ∈ Finset.range n, 3 * (|clockPath ω (segment T n k).2| -
    |clockPath ω (segment T n k).1|) ^ 2

def residual (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  quartic T n ω - clockMean T n ω.2

theorem quartic_measurable (T : ℝ≥0) (n : ℕ) : Measurable (quartic T n) := by
  apply Finset.measurable_sum
  intro k hk
  exact ((ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)).sub
    (ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id))).pow_const 4

theorem clockMean_measurable (T : ℝ≥0) (n : ℕ) : Measurable (clockMean T n) := by
  apply Finset.measurable_sum
  intro k hk
  have ht := continuous_abs.measurable.comp
    ((ContinuousMap.measurable_eval (segment T n k).2).comp clockPath_measurable)
  have hs := continuous_abs.measurable.comp
    ((ContinuousMap.measurable_eval (segment T n k).1).comp clockPath_measurable)
  exact ((ht.sub hs).pow_const 2).const_mul 3

theorem residual_measurable (T : ℝ≥0) (n : ℕ) : Measurable (residual T n) :=
  (quartic_measurable T n).sub ((clockMean_measurable T n).comp measurable_snd)

private abbrev oldQuartic (I : Finset (ℝ≥0 × ℝ≥0)) (x y : SampleSpace) : ℝ :=
  IBMFiniteQuartic.quarticSum (fun r ω => sceneryPath ω r) (fun t ω => clockPath ω t)
    (fun ω => (sceneryPath ω).continuous) (fun ω => (clockPath ω).continuous) I x y

private theorem oldQuartic_eq {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (x y : SampleSpace) : oldQuartic (intervals T n) x y = quartic T n (x,y) := by
  unfold oldQuartic IBMFiniteQuartic.quarticSum
  rw [sum_intervals hT n hn]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [IBMContinuousComposition.value_eq, IBMModificationBridge.sceneryPath_apply,
    IBMModificationBridge.clockPath_apply, ibmValue_eq]

/-- Exact actual scenery-conditional mean, with no supplied source laws. -/
theorem conditional_mean {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n) (y : SampleSpace) :
    (∫ x, quartic T n (x,y) ∂gaussianProduct) = clockMean T n y := by
  have h := IBMFiniteQuartic.conditional_quarticSum_expectation
    (fun r ω => sceneryPath ω r) (fun t ω => clockPath ω t)
    (fun ω => (sceneryPath ω).continuous) (fun ω => (clockPath ω).continuous)
    sceneryPath_coordinate_ae (intervals T n) y
  change (∫ x, oldQuartic (intervals T n) x y ∂gaussianProduct) = _ at h
  simp_rw [oldQuartic_eq hT n hn] at h
  rw [sum_intervals hT n hn] at h
  exact h

theorem conditional_quartic_memLp {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (y : SampleSpace) : MemLp (fun x => quartic T n (x,y)) 2 gaussianProduct := by
  have h := conditional_quartic_memLp_two
    (fun r ω => sceneryPath ω r) (fun t ω => clockPath ω t)
    (fun ω => (sceneryPath ω).continuous) (fun ω => (clockPath ω).continuous)
    sceneryPath_coordinate_ae (intervals T n) y
  change MemLp (fun x => oldQuartic (intervals T n) x y) 2 gaussianProduct at h
  simpa only [oldQuartic_eq hT n hn] using h

theorem conditional_residual_square_integrable {T : ℝ≥0} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (y : SampleSpace) :
    Integrable (fun x => residual T n (x,y) ^ 2) gaussianProduct := by
  have hc : MemLp (fun _ : SampleSpace => clockMean T n y) 2 gaussianProduct := memLp_const _
  have hm : MemLp (fun x => residual T n (x,y)) 2 gaussianProduct := by
    change MemLp (fun x => quartic T n (x,y) - clockMean T n y) 2 gaussianProduct
    exact (conditional_quartic_memLp hT n hn y).sub hc
  simpa only [Real.norm_eq_abs, sq_abs] using hm.integrable_norm_pow'

private theorem occupation_intervals {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (y : SampleSpace) :
    (∫ x, count (intervals T n) (fun p => |clockPath y p.1|)
      (fun p => |clockPath y p.2|) x ^ 2) = occupation T n y := by
  have he (x : ℝ) : count (intervals T n) (fun p => |clockPath y p.1|)
      (fun p => |clockPath y p.2|) x =
      count (Finset.range n) (fun k => |clockPath y (grid (T / n) k)|)
        (fun k => |clockPath y (grid (T / n) (k + 1))|) x :=
    sum_intervals hT n hn _
  simp_rw [he]
  rfl

/-- Actual conditional squared fluctuation is controlled on the good-clock
event by the integrable endpoint energy. -/
theorem conditional_residual_square_le {T : ℝ≥0} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 ≤ δ) {y : SampleSpace}
    (hy : y ∉ bad T n δ) :
    (∫ x, residual T n (x,y) ^ 2 ∂gaussianProduct) ≤
      96 * δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ y := by
  have hmesh : ∀ p ∈ intervals T n, abs (|clockPath y p.2| - |clockPath y p.1|) ≤ δ := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    exact reflected_mesh_of_not_bad T n δ hy ⟨k, Finset.mem_range.mp hk⟩
  have h := actual_conditional_centered_square_le (intervals T n) y δ hδ hmesh
  change (∫ x, (oldQuartic (intervals T n) x y -
    ∫ z, oldQuartic (intervals T n) z y ∂gaussianProduct) ^ 2 ∂gaussianProduct) ≤ _ at h
  simp_rw [oldQuartic_eq hT n hn, conditional_mean hT n hn y] at h
  rw [occupation_intervals hT n hn y] at h
  exact h.trans (mul_le_mul_of_nonneg_left (occupation_le_envelope T n hδ hy) (by positivity))

end OperatorDerivativeRewrite.Foundation.IBMUniformQuarticFamily
