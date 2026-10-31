import Foundation.PeriodicHighExcursion
import Mathlib.LinearAlgebra.Matrix.Notation
/-! Stationary low-action mass at the ACTUAL resolvent cutoff, with a sharp
finite reversible comparison model. No nonnegative spectrum is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicHighMassAnchor
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicHighActionL2 PeriodicHighExcursion
attribute [local irreducible] spatialAction represented completed operator compression
private instance prob {β : ℝ} (g : GroundData β) : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance markov {β : ℝ} (g : GroundData β) : IsMarkovKernel g.transition := g.transition_markov
private instance edge_prob {β : ℝ} (g : GroundData β) : IsProbabilityMeasure (edgeLaw g) := by
  unfold edgeLaw
  infer_instance

theorem one_step_event {β : ℝ} (g : GroundData β) (K : ℝ) :
    (survivingLaw g K 1).real Set.univ=
      (edgeLaw g).real ((region β K).prod (region β K)) := by
  let F : StateL2 g := (highVector g K 0 : completed g K)
  have hF : (fun U => F U)=ᵐ[g.stationary] survival g K 0 := by
    dsimp only [F,highVector]
    exact MemLp.coeFn_toLp _
  rw [survival_zero] at hF
  have hl := (left_preserving g).quasiMeasurePreserving.ae_eq_comp hF
  have hr := (right_preserving g).quasiMeasurePreserving.ae_eq_comp hF
  have hA : MeasurableSet (region β K) :=
    measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)
  calc
    _ = inner ℝ (highVector g K 1) (highVector g K 0) := mass_pairing g K 1
    _ = inner ℝ (compression g K (highVector g K 0)) (highVector g K 0) := by rw [compression_step g K 0]
    _ = inner ℝ (operator g F) F := compression_pairing g K _ _
    _ = ∫ p,F p.1*F p.2 ∂edgeLaw g := operator_pairing g F F
    _ = ∫ p,((region β K).prod (region β K)).indicator (fun _ => (1:ℝ)) p ∂edgeLaw g := by
      apply integral_congr_ae
      filter_upwards [hl,hr] with p hp hq
      change F p.1=PeriodicHighActionKernel.cut β K (fun _ => (1:ℝ)) p.1 at hp
      change F p.2=PeriodicHighActionKernel.cut β K (fun _ => (1:ℝ)) p.2 at hq
      rw [hp,hq]
      by_cases h : p∈(region β K).prod (region β K)
      · have h1 : K<β*spatialAction p.1 := h.1
        have h2 : K<β*spatialAction p.2 := h.2
        calc
          _ = 1 := by simp [PeriodicHighActionKernel.cut,h1,h2]
          _ = _ := (Set.indicator_of_mem h (fun _ : State × State => (1:ℝ))).symm
      · have hzero : (PeriodicHighActionKernel.cut β K (fun _ => (1:ℝ)) p.1)*
            (PeriodicHighActionKernel.cut β K (fun _ => (1:ℝ)) p.2)=0 := by
          by_cases h1 : K<β*spatialAction p.1
          · have h2 : ¬K<β*spatialAction p.2 := fun h2 => h ⟨h1,h2⟩
            simp [PeriodicHighActionKernel.cut,h1,h2]
          · simp [PeriodicHighActionKernel.cut,h1]
        exact hzero.trans (Set.indicator_of_notMem h (fun _ : State × State => (1:ℝ))).symm

    _ = _ := integral_indicator_one (hA.prod hA)

/-- The two genuine stationary marginals bound the actual simultaneous event. -/
theorem edge_lower {β : ℝ} (g : GroundData β) (A : Set State) (hA : MeasurableSet A) :
    2*g.stationary.real A-1 ≤ (edgeLaw g).real (A.prod A) := by
  let E : Set (State × State) := Prod.fst ⁻¹' A
  let F : Set (State × State) := Prod.snd ⁻¹' A
  have hE : (edgeLaw g).real E=g.stationary.real A := by
    have h := congrArg (fun ν : Measure State => ν A) (left_preserving g).map_eq
    rw [Measure.map_apply measurable_fst hA] at h
    exact congrArg ENNReal.toReal h
  have hF : (edgeLaw g).real F=g.stationary.real A := by
    have h := congrArg (fun ν : Measure State => ν A) (right_preserving g).map_eq
    rw [Measure.map_apply measurable_snd hA] at h
    exact congrArg ENNReal.toReal h
  have hInt : E∩F=A.prod A := by ext p; rfl
  have hUnion : (edgeLaw g).real (E∪F) ≤ 1 := by
    have h := measureReal_mono (μ := edgeLaw g) (Set.subset_univ (E∪F)) (measure_ne_top _ _)
    simpa only [probReal_univ] using h
  have h := measureReal_union_add_inter₀ (μ := edgeLaw g) (s := E) (t := F)
    (hA.preimage measurable_snd).nullMeasurableSet
  rw [hInt,hE,hF] at h
  linarith

/-- At the proved high resolvent cutoff, at most two thirds of the ACTUAL
stationary law lies in the high region, uniformly in the specified coupling range. -/
theorem high_mass {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    g.stationary.real (region β PeriodicHighActionSchur.threshold) ≤ (2/3 : ℝ) := by
  let K := PeriodicHighActionSchur.threshold
  have hA : MeasurableSet (region β K) :=
    measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)
  have hl := edge_lower g (region β K) hA
  rw [← one_step_event] at hl
  have hu := geometric_mass g hb 1
  simp only [pow_one] at hu
  change g.stationary.real (region β K) ≤ _
  linarith

theorem low_mass {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    (1/3 : ℝ) ≤ g.stationary.real {U | β*spatialAction U ≤ PeriodicHighActionSchur.threshold} := by
  let A := region β PeriodicHighActionSchur.threshold
  have hA : MeasurableSet A := measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)
  have hc : Aᶜ={U | β*spatialAction U ≤ PeriodicHighActionSchur.threshold} := by
    ext U
    simp only [A,region,Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt]
  have h := measureReal_add_measureReal_compl (μ := g.stationary) hA
  rw [hc,probReal_univ] at h
  have hu := high_mass hb g
  linarith

namespace TwoState
open scoped Matrix

def weights : Fin 2 → ℝ := ![2/3,1/3]
def transition : Matrix (Fin 2) (Fin 2) ℝ := !![1/2,1/2;1,0]
def joint (i j : Fin 2) : ℝ := weights i*transition i j
def normSq (f : Fin 2 → ℝ) : ℝ := ∑ i,weights i*f i^2
def form (f : Fin 2 → ℝ) : ℝ := ∑ i,weights i*(transition.mulVec f) i*f i

/-- Explicit positive stationary weights and a stochastic transition matrix. -/
theorem stochastic : (∀ i,0<weights i) ∧ (∑ i,weights i)=1 ∧
    ∀ i,(∀ j,0≤transition i j) ∧ (∑ j,transition i j)=1 := by
  refine ⟨?_,?_,?_⟩
  · intro i; fin_cases i <;> norm_num [weights]
  · norm_num [weights,Fin.sum_univ_two]
  · intro i
    fin_cases i <;> constructor
    all_goals first | (intro j; fin_cases j <;> norm_num [transition]) | norm_num [transition,Fin.sum_univ_two]

/-- The finite joint probability table is symmetric and has both weights as marginals. -/
theorem stationary : (∀ i j,0≤joint i j ∧ joint i j=joint j i) ∧
    (∀ i,∑ j,joint i j=weights i) ∧ (∀ j,∑ i,joint i j=weights j) := by
  refine ⟨?_,?_,?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [joint,weights,transition]
  · intro i; fin_cases i <;> norm_num [joint,weights,transition,Fin.sum_univ_two]
  · intro j; fin_cases j <;> norm_num [joint,weights,transition,Fin.sum_univ_two]

theorem contraction_identity (f : Fin 2 → ℝ) :
    normSq f-normSq (transition.mulVec f)=(1/6 : ℝ)*(f 0-f 1)^2 := by
  simp [normSq,weights,transition,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem contractive (f : Fin 2 → ℝ) : normSq (transition.mulVec f)≤normSq f := by
  have h := contraction_identity f
  nlinarith [sq_nonneg (f 0-f 1)]

/-- High={0} attains mass2/3 and has the exact scalar high compression1/2.
The squared norm identity certifies its norm ratio without a spectral positivity premise. -/
theorem high_exact (x : ℝ) : weights 0=(2/3 : ℝ) ∧ joint 0 0=(1/2 : ℝ)*weights 0 ∧
    (transition.mulVec ![x,0]) 0=x/2 ∧
    normSq ![x/2,0]=(1/2 : ℝ)^2*normSq ![x,0] ∧
    form ![x,0]=(1/2 : ℝ)*normSq ![x,0] := by
  simp [weights,joint,transition,normSq,form,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  constructor <;> ring_nf <;> trivial

/-- This reversible contraction has a negative quadratic direction: positivity
of the ACTUAL Wilson transfer would be an additional theorem, not generic Markov data. -/
theorem negative_mode : normSq ![1,-2]=2 ∧ form ![1,-2]=(-1:ℝ) := by
  norm_num [normSq,form,weights,transition,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

end TwoState
end OperatorDerivativeRewrite.Foundation.PeriodicHighMassAnchor
