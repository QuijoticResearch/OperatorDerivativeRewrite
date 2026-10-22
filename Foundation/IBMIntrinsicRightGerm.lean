import Foundation.IBMDecreasingPastProjection

/-! Canonical strong-L2 right germs for the ACTUAL intrinsic IBM martingale.
The germ is not asserted to equal the present value or to be a modification. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicRightGerm
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable IBMIntrinsicQuadraticMartingale
open IBMIntrinsicMartingaleEndpoint IBMDecreasingPastProjection
set_option backward.isDefEq.respectTransparency false

def rightPast (t : ℝ≥0) : Submodule ℝ JointL2 :=
  (⨆ u : Ioi t, (past u.val)ᗮ).topologicalClosureᗮ

private instance rightPastProjection (t : ℝ≥0) : (rightPast t).HasOrthogonalProjection := by
  unfold rightPast
  infer_instance

theorem rightPast_eq_iInf (t : ℝ≥0) : rightPast t = ⨅ u : Ioi t, past u.val := by
  unfold rightPast
  rw [Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal]
  simp only [Submodule.orthogonal_orthogonal]

theorem past_le_rightPast (t : ℝ≥0) : past t ≤ rightPast t := by
  rw [rightPast_eq_iInf]
  exact le_iInf fun u f hf => hf.mono (naturalFiltration.mono u.property.le)

theorem rightPast_le_past {t T : ℝ≥0} (hT : t < T) : rightPast t ≤ past T := by
  rw [rightPast_eq_iInf]
  exact iInf_le (fun u : Ioi t => past u.val) ⟨T, hT⟩

theorem intersection_eq_rightPast (τ : ℕ → ℝ≥0) (t : ℝ≥0)
    (ht : ∀ n, t < τ n) (hlim : Tendsto τ atTop (𝓝 t)) :
    intersectionSpace τ = rightPast t := by
  rw [intersectionSpace_eq_iInf, rightPast_eq_iInf]
  apply le_antisymm
  · apply le_iInf
    intro u f hf
    have he : ∀ᶠ n in atTop, τ n < u.val := hlim.eventually (eventually_lt_nhds u.property)
    obtain ⟨n, hn⟩ := he.exists
    exact ((iInf_le (fun k => past (τ k)) n) hf).mono (naturalFiltration.mono hn.le)
  · apply le_iInf
    intro n
    exact iInf_le (fun u : Ioi t => past u.val) ⟨τ n, ht n⟩

theorem project_horizon {t T H : ℝ≥0} (hT : t < T) (hH : T ≤ H) :
    (rightPast t).starProjection (valueClass T : JointL2) =
      (rightPast t).starProjection (valueClass H : JointL2) := by
  rw [← projection_value hH]
  exact DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le
    (rightPast_le_past hT)) (valueClass H : JointL2)

def rightLimitClass (t : ℝ≥0) : JointL2 :=
  (rightPast t).starProjection (valueClass (t + 1) : JointL2)

theorem rightLimitClass_horizon {t T : ℝ≥0} (hT : t < T) :
    rightLimitClass t = (rightPast t).starProjection (valueClass T : JointL2) := by
  have hp : t < t + 1 := lt_add_of_pos_right _ (by norm_num)
  unfold rightLimitClass
  calc
    _ = (rightPast t).starProjection (valueClass (max (t + 1) T) : JointL2) :=
      project_horizon hp (le_max_left _ _)
    _ = _ := (project_horizon hT (le_max_right _ _)).symm

theorem valueClass_tendsto_right (τ : ℕ → ℝ≥0) (hτ : Antitone τ) (t T : ℝ≥0)
    (ht : ∀ n, t < τ n) (hT : ∀ n, τ n ≤ T) (hlim : Tendsto τ atTop (𝓝 t)) :
    Tendsto (fun n => (valueClass (τ n) : JointL2)) atTop (𝓝 (rightLimitClass t)) := by
  have hs := IBMDecreasingPastProjection.valueClass_tendsto τ hτ T hT
  simpa only [intersection_eq_rightPast τ t ht hlim,
    ← rightLimitClass_horizon ((ht 0).trans_le (hT 0))] using hs

theorem rightLimitClass_mem (t : ℝ≥0) : rightLimitClass t ∈ rightPast t :=
  Submodule.starProjection_apply_mem _ _

theorem project_to_present (t : ℝ≥0) :
    (past t).starProjection (rightLimitClass t) = (valueClass t : JointL2) := by
  unfold rightLimitClass
  have he := DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le
    (past_le_rightPast t)) (valueClass (t + 1) : JointL2)
  exact he.trans (projection_value (by simp))

def jumpClass (t : ℝ≥0) : JointL2 := rightLimitClass t - (valueClass t : JointL2)

theorem jumpClass_mem_orthogonal (t : ℝ≥0) : jumpClass t ∈ (past t)ᗮ := by
  have h := (past t).sub_starProjection_mem_orthogonal (rightLimitClass t)
  rwa [project_to_present] at h

theorem energy_decomposition (t : ℝ≥0) :
    ‖rightLimitClass t‖ ^ 2 = ‖(valueClass t : JointL2)‖ ^ 2 + ‖jumpClass t‖ ^ 2 := by
  have he : rightLimitClass t = (valueClass t : JointL2) + jumpClass t := by
    unfold jumpClass
    abel
  have ho := Submodule.inner_right_of_mem_orthogonal (valueClass t).property
    (jumpClass_mem_orthogonal t)
  rw [he, norm_add_sq_real, ho]
  ring

theorem equals_present_iff_energy (t : ℝ≥0) :
    rightLimitClass t = (valueClass t : JointL2) ↔
      ‖rightLimitClass t‖ ^ 2 = ‖(valueClass t : JointL2)‖ ^ 2 := by
  constructor
  · intro h; rw [h]
  · intro h
    have he := energy_decomposition t
    have hj : ‖jumpClass t‖ ^ 2 = 0 := by linarith
    have hz : jumpClass t = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
    exact sub_eq_zero.mp hz

theorem rightLimitClass_ne_zero {t : ℝ≥0} (ht : 0 < t) : rightLimitClass t ≠ 0 := by
  intro hz
  have he := project_to_present t
  rw [hz, map_zero] at he
  exact IBMEvenClockProjection.conditional_quadratic_ne_zero t t ht le_rfl he.symm

def rightValue (t : ℝ≥0) : IBMSourceLaws.JointSample → ℝ := rightLimitClass t

theorem rightValue_memLp (t : ℝ≥0) : MemLp (rightValue t) 2 IBMSourceLaws.jointMeasure :=
  Lp.memLp (rightLimitClass t)

theorem rightValue_future_ae {t u : ℝ≥0} (hu : t < u) :
    AEStronglyMeasurable[naturalFiltration u] (rightValue t) IBMSourceLaws.jointMeasure :=
  (rightPast_le_past hu) (rightLimitClass_mem t)

theorem rightValue_present_condExp (t : ℝ≥0) :
    IBMSourceLaws.jointMeasure[rightValue t | naturalFiltration t]
      =ᵐ[IBMSourceLaws.jointMeasure] value t := by
  have he := IBMCofinalPast.projection_ae t (rightLimitClass t)
  rw [project_to_present] at he
  exact he.symm.trans (valueClass_ae t)

theorem rightValue_eq_original_iff (t : ℝ≥0) :
    rightValue t =ᵐ[IBMSourceLaws.jointMeasure] value t ↔ jumpClass t = 0 := by
  constructor
  · intro he
    have hz : rightLimitClass t = (valueClass t : JointL2) :=
      Lp.ext (he.trans (valueClass_ae t).symm)
    exact sub_eq_zero.mpr hz
  · intro hz
    have he : rightLimitClass t = (valueClass t : JointL2) := sub_eq_zero.mp hz
    change rightLimitClass t =ᵐ[IBMSourceLaws.jointMeasure] value t
    rw [he]
    exact valueClass_ae t

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicRightGerm
