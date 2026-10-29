import Foundation.FourCubeDirichletBox

/-! Actual32-link Haar consequences of the standard Dirichlet-box coercivity.
Bounds are unnormalized. No coupling-uniform normalized concentration or
physical transfer-operator gap follows without further estimates. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.FourCubeDirichletHaar
open QuaternionSU2Representation OneSidedBlockRank FourCubeHaarParity
open FourCubePinnedCoercivity FourCubeDirichletBox
attribute [local irreducible] faces OneSidedBlockIncidence.edges

theorem link_measurable (b : Fin 3 → SU2) (e : BoxEdge) :
    Measurable (fun s : InteriorState => link b s e) := by
  unfold link
  cases label e with
  | none => exact measurable_const
  | some v =>
    cases v with
    | inl i => exact measurable_pi_apply i
    | inr j => exact measurable_const

theorem action_measurable (b : Fin 3 → SU2) : Measurable (action b) := by
  unfold action word defect
  apply Finset.measurable_sum
  intro p hp
  exact measurable_const.sub (halfTrace_measurable.comp
    ((((link_measurable b _).mul (link_measurable b _)).mul
      (link_measurable b _).inv).mul (link_measurable b _).inv))

theorem action_upper (b : Fin 3 → SU2) (s : InteriorState) : action b s ≤ 1728 := by
  calc
    action b s ≤ ∑ _p∈faces,(2 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := (abs_le.mp (halfTrace_bound (word b s p))).1
      dsimp [defect]
      linarith
    _ = 1728 := by rw [Finset.sum_const,face_count]; norm_num

theorem vacuum_one : action (fun _ => 1) (fun _ => 1)=0 := by
  have hl (e : BoxEdge) : link (fun _ => 1) (fun _ => 1) e=1 := by
    unfold link
    cases label e with
    | none => rfl
    | some v => cases v <;> rfl
  simp [action,word,hl,defect_one]

/-- All32 integrated links, including the former gauge pole, are forced to identity. -/
theorem zero_forces_identity (b : Fin 3 → SU2) (s : InteriorState)
    (h : action b s=0) : s=1 := by
  funext e
  have he := coordinate_bound b s e
  rw [h] at he
  exact (defect_zero_iff _).mp (le_antisymm he (defect_nonneg _))

theorem vacuum_zero_iff (s : InteriorState) : action (fun _ => 1) s=0 ↔ s=1 := by
  constructor
  · exact zero_forces_identity _ s
  · intro h
    subst s
    exact vacuum_one

theorem boltzmann_integrable (b : Fin 3 → SU2) (β : ℝ) :
    Integrable (fun s => Real.exp (-β*action b s)) interiorHaar := by
  apply Integrable.of_bound
    ((measurable_const.mul (action_measurable b)).exp.aestronglyMeasurable)
    (Real.exp (1728*|β|))
  filter_upwards with s
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  change -β*action b s ≤ 1728*|β|
  calc
    -β*action b s ≤ |β| *action b s :=
      mul_le_mul_of_nonneg_right (neg_le_abs β) (action_nonneg b s)
    _ ≤ |β| *1728 := mul_le_mul_of_nonneg_left (action_upper b s) (abs_nonneg β)
    _ = 1728*|β| := mul_comm _ _

theorem boltzmann_barrier (b : Fin 3 → SU2) (β ε : ℝ) (hβ : 0 ≤ β)
    (s : InteriorState) (e : Interior) (he : ε ≤ defect (s e)) :
    Real.exp (-β*action b s) ≤ Real.exp (-β*ε) := by
  apply Real.exp_le_exp.mpr
  have hh := coordinate_bound b s e
  nlinarith

/-- Actual Haar integral over a coordinate tail, uniformly in arbitrary source values. -/
theorem boltzmann_tail (b : Fin 3 → SU2) (β ε : ℝ) (hβ : 0 ≤ β) (e : Interior) :
    (∫ s in {s : InteriorState | ε ≤ defect (s e)},
      Real.exp (-β*action b s) ∂interiorHaar) ≤ Real.exp (-β*ε) := by
  have hh := norm_setIntegral_le_of_norm_le_const
    (μ := interiorHaar) (s := {s : InteriorState | ε ≤ defect (s e)})
    (f := fun s => Real.exp (-β*action b s)) (measure_lt_top _ _)
    (fun s hs => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact boltzmann_barrier b β ε hβ s e hs)
  have hm : interiorHaar.real {s : InteriorState | ε ≤ defect (s e)} ≤ 1 :=
    measureReal_le_one
  have ht := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-β*ε)).le
  simp only [mul_one] at ht
  exact (le_abs_self _).trans (hh.trans ht)

end OperatorDerivativeRewrite.Foundation.FourCubeDirichletHaar
