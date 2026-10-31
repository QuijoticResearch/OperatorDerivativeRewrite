import Foundation.FourCubeConditionalScore
import Foundation.FiniteCovarianceHessian
import Mathlib.Analysis.Calculus.Deriv.Shift
/-! Actual all32 Wilson score symmetry. Global conjugation-invariant tests
are used explicitly; no identification with a complete local-gauge sector or
uniform multiblock contraction is assumed. -/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.FourCubeInvariantScore
open FourCubeConditionalScore FourCubeHaarContinuousIntegral FourCubeBoundarySmoothAction
open FourCubeHaarParity FourCubeIntegratedCubic QuaternionSU2Representation
attribute [local irreducible] action haarIntegral

def flip (i : Fin 3) (a : Parameters) : Parameters := fun j => if i=j then a j else -a j

private theorem conjugate_inv (g A : SU2) : g*A⁻¹*g⁻¹=(g*A*g⁻¹)⁻¹ := by group

theorem boundary_turn (i : Fin 3) (a : Parameters) (c : OneSidedCapComplex.Boundary) :
    turn i*boundaryData (a 0) (a 1) (a 2) c*(turn i)⁻¹=
      boundaryData (flip i a 0) (flip i a 1) (flip i a 2) c := by
  cases c with
  | inl c =>
    simp only [boundaryData]
    split_ifs
    · exact turn_axis i 0 (a 0)
    · rw [conjugate_inv,turn_axis]
      rfl
    · simp
  | inr p =>
    simp only [boundaryData]
    split_ifs
    · rw [conjugate_inv,turn_axis]
      rfl
    · simp

theorem fill_turn (i : Fin 3) (a : Parameters) (s : InteriorState) :
    conjugate (turn i) (fill (boundaryData (a 0) (a 1) (a 2)) s)=
      fill (boundaryData (flip i a 0) (flip i a 1) (flip i a 2)) (interiorConjugate (turn i) s) := by
  funext e
  cases e with
  | inl e => rfl
  | inr c => exact boundary_turn i a c

theorem action_turn (i : Fin 3) (a : Parameters) (s : InteriorState) :
    action (flip i a) (interiorConjugate (turn i) s)=action a s := by
  simp only [action_apply,cellAction]
  rw [← fill_turn,fullAction_conjugate]

theorem weight_turn (β : ℝ) (i : Fin 3) (a : Parameters) (s : InteriorState) :
    weight β (flip i a) (interiorConjugate (turn i) s)=weight β a s := by
  unfold weight
  simp only [exp_apply,ContinuousMap.smul_apply,smul_eq_mul,action_turn]

private theorem haar_turn (i : Fin 3) (f : Observables) :
    (∫ s,f (interiorConjugate (turn i) s) ∂interiorHaar)=∫ s,f s ∂interiorHaar := by
  have h := integral_map (μ := interiorHaar) (interiorConjugate_preserving (turn i)).measurable.aemeasurable
    f.continuous.measurable.aestronglyMeasurable
  rw [(interiorConjugate_preserving (turn i)).map_eq] at h
  exact h.symm

theorem weighted_turn (β : ℝ) (i : Fin 3) (a : Parameters) (f : Observables)
    (hf : ∀ s,f (interiorConjugate (turn i) s)=f s) :
    haarIntegral (f*weight β (flip i a))=haarIntegral (f*weight β a) := by
  rw [haarIntegral_apply,haarIntegral_apply,← haar_turn i (f*weight β (flip i a))]
  apply integral_congr_ae
  filter_upwards with s
  simp only [ContinuousMap.mul_apply,hf,weight_turn]

theorem expectation_turn (β : ℝ) (i : Fin 3) (a : Parameters) (f : Observables)
    (hf : ∀ s,f (interiorConjugate (turn i) s)=f s) :
    expectation β (flip i a) f=expectation β a f := by
  unfold expectation FourCubeBoundarySmoothPartition.partition
  rw [weighted_turn β i a f hf]
  have h := weighted_turn β i a 1 (fun _ => rfl)
  simpa only [one_mul,weight] using congrArg (fun z : ℝ => haarIntegral (f*weight β a)/z) h

theorem flip_smul (i : Fin 3) (t : ℝ) (u : Parameters) : flip i (t • u)=t • flip i u := by
  funext j
  simp only [flip,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

/-- At identity boundary the odd source channel cancels against invariant tests. -/
theorem odd_response_zero (β : ℝ) (i : Fin 3) (u : Parameters) (hu : flip i u=-u)
    (f : Observables) (hf : ∀ s,f (interiorConjugate (turn i) s)=f s) :
    response β 0 u f=0 := by
  have he : (fun t : ℝ => expectation β (0+t • u) f)=
      (fun t => expectation β (0+(-t) • u) f) := by
    funext t
    have h := expectation_turn β i (t • u) f hf
    rw [flip_smul,hu,smul_neg,← neg_smul] at h
    simpa only [zero_add] using h.symm
  have hd := congrArg (fun F : ℝ → ℝ => deriv F 0) he
  have hn := deriv_comp_neg (fun t : ℝ => expectation β (0+t • u) f) (0:ℝ)
  simp only [neg_zero] at hn
  rw [hn] at hd
  rw [(expectation_hasDerivAt β 0 u f).deriv] at hd
  linarith

theorem expectation_contDiff (β : ℝ) (f : Observables) :
    ContDiff ℝ ∞ (fun a => expectation β a f) := by
  have hw := exponential_contDiff.comp (action_contDiff.const_smul (-β))
  have hconst : ContDiff ℝ ∞ (fun _ : Parameters => f) := contDiff_const
  have hn := haarIntegral.contDiff.comp (hconst.mul hw)
  exact hn.div (FourCubeBoundarySmoothPartition.partition_contDiff β) (fun a => (partition_pos β a).ne')

theorem coordinate_response_zero (β : ℝ) (j : Fin 3) (f : Observables)
    (hf : ∀ g s,f (interiorConjugate g s)=f s) :
    response β 0 (FiniteCovarianceHessian.direction j) f=0 := by
  have hi : (j+1 : Fin 3)≠j := by fin_cases j <;> decide
  apply odd_response_zero β (j+1) _ _ f (hf _)
  funext k
  by_cases hk : k=j
  · subst k
    simp [flip,FiniteCovarianceHessian.direction,hi]
  · simp [flip,FiniteCovarianceHessian.direction,Pi.single_apply,hk,Ne.symm hk]

/-- All first-order channels vanish at identity against globally conjugation-invariant tests. -/
theorem invariant_response_zero (β : ℝ) (u : Parameters) (f : Observables)
    (hf : ∀ g s,f (interiorConjugate g s)=f s) : response β 0 u f=0 := by
  let F := fun a => expectation β a f
  have hF : Differentiable ℝ F := (expectation_contDiff β f).differentiable (by simp)
  have hv (v : Parameters) : fderiv ℝ F 0 v=response β 0 v f := by
    have hl : HasDerivAt (fun t : ℝ => (0:Parameters)+t • v) v 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const v |>.const_add (0:Parameters)
    have h := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hl
    have h0 : HasDerivAt (fun t : ℝ => expectation β (0+t • v) f) (fderiv ℝ F 0 v) 0 := by
      simpa only [Function.comp_def,zero_smul,add_zero] using h
    exact h0.unique (expectation_hasDerivAt β 0 v f)
  rw [← hv u,FiniteCovarianceHessian.coordinate_expansion u]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j _
  rw [hv,coordinate_response_zero β j f hf,mul_zero]

/-- Only global conjugation invariance is required; no local-gauge-sector equality is asserted. -/
def invariantCore : Submodule ℝ Observables where
  carrier := {f | ∀ g s,f (interiorConjugate g s)=f s}
  zero_mem' := by intro g s; rfl
  add_mem' := by
    intro f h hf hh g s
    change f (interiorConjugate g s)+h (interiorConjugate g s)=f s+h s
    rw [hf g s,hh g s]
  smul_mem' := by
    intro r f hf g s
    change r • f (interiorConjugate g s)=r • f s
    rw [hf g s]

/-- The explicit closed native span, not an assumed full measurable invariant space. -/
def invariantSpace (β : ℝ) : Submodule ℝ (Native β 0) :=
  (invariantCore.map (ContinuousMap.toLp 2 (law β 0) ℝ).toLinearMap).topologicalClosure

instance invariantSpace_complete (β : ℝ) : CompleteSpace (invariantSpace β) :=
  (invariantCore.map (ContinuousMap.toLp 2 (law β 0) ℝ).toLinearMap).isClosed_topologicalClosure.completeSpace_coe

theorem invariantSpace_le_kernel (β : ℝ) (u : Parameters) :
    invariantSpace β≤(nativeResponse β 0 u).ker := by
  apply Submodule.topologicalClosure_minimal _ _ (nativeResponse β 0 u).isClosed_ker
  rintro x ⟨f,hf,rfl⟩
  change nativeResponse β 0 u (ContinuousMap.toLp 2 (law β 0) ℝ f)=0
  rw [nativeResponse_core]
  exact invariant_response_zero β u f hf

/-- Native orthogonality follows on the actual closure by continuity, without a density fiction. -/
theorem score_orthogonal (β : ℝ) (u : Parameters) :
    nativeScore β 0 u∈(invariantSpace β)ᗮ := by
  apply (invariantSpace β).mem_orthogonal _ |>.mpr
  intro v hv
  have h := invariantSpace_le_kernel β u hv
  change inner ℝ (nativeScore β 0 u) v=0 at h
  simpa only [real_inner_comm] using h

theorem projected_score_zero (β : ℝ) (u : Parameters) :
    (invariantSpace β).starProjection (nativeScore β 0 u)=0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).mpr (score_orthogonal β u)

/-- The actual conditional expectation has zero first variation on every stated invariant core test. -/
theorem invariant_native_derivative (β : ℝ) (u : Parameters) (f : invariantCore) :
    HasDerivAt (fun t : ℝ => ∫ s,(f : Observables) s ∂law β (t • u)) 0 0 := by
  have h := native_derivative β 0 u (f : Observables)
  rw [nativeResponse_core,invariant_response_zero β u f f.property] at h
  simpa only [zero_add] using h
end OperatorDerivativeRewrite.Foundation.FourCubeInvariantScore
