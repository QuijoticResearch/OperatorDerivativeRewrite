import Foundation.HigherHeatPolynomialCylinders
import Foundation.HigherHeatPositionVariation

/-! Faithful realization of unbounded polynomial cylinders as continuous path functions. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialPathDomain
open HigherHeatPolynomialCylinders HigherHeatPolynomialRefinement HigherHeatPositionVariation
  HigherHeatGridDoubling HigherHeatCylinderFourier HigherHeatBlockCoarsening
  HigherHeatObservationRefinement

abbrev Path := HigherHeatContinuousCylinders.Path

def increments (n : ℕ) (ω : Path) : Fin (size n) → ℝ :=
  (cumulativeEquiv (size n)).symm (HigherHeatContinuousCylinders.sample n ω)

theorem increments_continuous (n : ℕ) : Continuous (increments n) :=
  (cumulativeEquiv (size n)).symm.toContinuousLinearEquiv.continuous.comp
    (HigherHeatContinuousCylinders.sample_continuous n)

theorem increments_surjective (n : ℕ) : Function.Surjective (increments n) := by
  intro x
  obtain ⟨ω, hω⟩ := HigherHeatContinuousCylinders.sample_surjective n (cumulativeEquiv (size n) x)
  refine ⟨ω, ?_⟩
  simp [increments, hω]

theorem cumulative_coarsen (N : ℕ) (x : Fin (2*N) → ℝ) :
    cumulativeEquiv N (coarsen pairBlock x) = oldPositions (cumulativeEquiv (2*N) x) := by
  have he : coarsen pairBlock x = linearImage (blockMatrix pairBlock) x := by
    funext i
    exact (block_apply pairBlock x i).symm
  rw [cumulativeEquiv_apply, he, block_observation, ← blockPositions_eq,
    cumulativeEquiv_apply, oldPositions_apply]

theorem increments_step (n : ℕ) (ω : Path) :
    coarsen (@pairBlock (size n)) (increments (n+1) ω) = increments n ω := by
  apply (cumulativeEquiv (size n)).injective
  calc
    _ = oldPositions (cumulativeEquiv (size (n+1)) (increments (n+1) ω)) :=
      cumulative_coarsen (size n) (increments (n+1) ω)
    _ = oldPositions (HigherHeatContinuousCylinders.sample (n+1) ω) := by
      rw [increments, LinearEquiv.apply_symm_apply]
    _ = HigherHeatContinuousCylinders.sample n ω :=
      HigherHeatContinuousCylinders.sample_restriction n ω
    _ = cumulativeEquiv (size n) (increments n ω) := by
      rw [increments, LinearEquiv.apply_symm_apply]

def sampleLift (n : ℕ) : Test n →ₐ[ℝ] C(Path, ℝ) where
  toFun P := ⟨fun ω => MvPolynomial.eval (increments n ω) P,
    (MvPolynomial.continuous_eval P).comp (increments_continuous n)⟩
  map_one' := by ext ω; simp
  map_mul' P Q := by ext ω; simp
  map_zero' := by ext ω; simp
  map_add' P Q := by ext ω; simp
  commutes' c := by ext ω; simp

theorem sampleLift_apply (n : ℕ) (P : Test n) (ω : Path) :
    sampleLift n P ω = MvPolynomial.eval (increments n ω) P := rfl

theorem sampleLift_injective (n : ℕ) : Function.Injective (sampleLift n) := by
  intro P Q hPQ
  apply MvPolynomial.funext
  intro x
  obtain ⟨ω, hω⟩ := increments_surjective n x
  have he := congrArg (fun F : C(Path,ℝ) => F ω) hPQ
  change MvPolynomial.eval (increments n ω) P = MvPolynomial.eval (increments n ω) Q at he
  rwa [hω] at he

theorem sampleLift_step (n : ℕ) (P : Test n) : sampleLift (n+1) (step n P) = sampleLift n P := by
  ext ω
  change MvPolynomial.eval (increments (n+1) ω) (pullback pairBlock P) =
    MvPolynomial.eval (increments n ω) P
  have he := eval_pullback (@pairBlock (size n)) P (increments (n+1) ω)
  exact he.trans (congrArg (fun x => MvPolynomial.eval x P) (increments_step n ω))

theorem sampleLift_transfer (i j : ℕ) (h : i ≤ j) (P : Test i) :
    sampleLift j (transfer i j h P) = sampleLift i P := by
  induction j, h using Nat.le_induction with
  | base => rw [transfer_self]
  | succ j hj ih => rw [transfer_succ i j hj P, sampleLift_step, ih]

def realize : Cylinder →ₐ[ℝ] C(Path, ℝ) :=
  DirectLimit.Algebra.lift Test transition C(Path,ℝ) sampleLift
    (fun i j h P => sampleLift_transfer i j h P)

theorem realize_apply (n : ℕ) (P : Test n) (ω : Path) :
    realize (cylinderOf n P) ω = MvPolynomial.eval (increments n ω) P := rfl

theorem realize_injective : Function.Injective realize :=
  DirectLimit.lift_injective transition (fun n P => sampleLift n P)
    (fun i j h P => (sampleLift_transfer i j h P).symm) sampleLift_injective

def realizedAlgebra : Subalgebra ℝ C(Path, ℝ) := realize.range


def realizationEquiv : Cylinder ≃ₐ[ℝ] realizedAlgebra :=
  AlgEquiv.ofInjective realize realize_injective

def pathExpectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    realizedAlgebra →ₗ[ℝ] ℂ :=
  (cylindricalExpectation m hm T hT).comp realizationEquiv.symm.toLinearMap

theorem pathExpectation_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F : Cylinder) :
    pathExpectation m hm T hT (realizationEquiv F) = cylindricalExpectation m hm T hT F := by
  simp [pathExpectation]

def quarticObservable : realizedAlgebra := realizationEquiv (terminalCylinder^4)

theorem quarticObservable_nonnegative (ω : Path) : 0 ≤ quarticObservable.val ω := by
  have he : quarticObservable.val = realize (terminalCylinder^4) :=
    AlgEquiv.ofInjective_apply realize realize_injective _
  rw [he, map_pow]
  change 0 ≤ (realize terminalCylinder ω)^4
  positivity

theorem quarticExpectation_negative (T : ℝ≥0) (hT : 0 < T) :
    (pathExpectation 2 (by norm_num) T hT quarticObservable).re < 0 := by
  rw [quarticObservable, pathExpectation_apply, biharmonic_fourth]
  have ht : 0 < (T:ℝ) := hT
  have he : -24*(T:ℝ) < 0 := by nlinarith
  simpa using he



theorem terminal_unbounded (M : ℝ) : ∃ ω : Path, M < realize terminalCylinder ω := by
  obtain ⟨ω, hω⟩ := increments_surjective 0 (fun _ => M+1)
  refine ⟨ω, ?_⟩
  change M < MvPolynomial.eval (increments 0 ω) (HigherHeatMultivariateMoments.terminal : Test 0)
  rw [hω]
  simp only [HigherHeatMultivariateMoments.terminal, map_sum, MvPolynomial.eval_X,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  change M < (1:ℕ) • (M+1)
  simp

theorem no_positive_integral_representation (T : ℝ≥0) (hT : 0 < T) (μ : Measure Path) :
    ¬ ∀ F : realizedAlgebra, (pathExpectation 2 (by norm_num) T hT F).re =
      ∫ ω, F.val ω ∂μ := by
  intro h
  have hn := quarticExpectation_negative T hT
  rw [h quarticObservable] at hn
  have hp : 0 ≤ ∫ ω : Path, quarticObservable.val ω ∂μ :=
    MeasureTheory.integral_nonneg (fun ω => quarticObservable_nonnegative ω)
  linarith



open Classical in
def positionPolynomial (n : ℕ) (i : Fin (size n)) : Test n :=
  ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MvPolynomial.X j

def positionCylinder (n : ℕ) (i : Fin (size n)) : Cylinder := cylinderOf n (positionPolynomial n i)

theorem realize_position (n : ℕ) (i : Fin (size n)) (ω : Path) :
    realize (positionCylinder n i) ω =
      HigherHeatContinuousCylinders.coordinate (HigherHeatContinuousCylinders.sampleTime n i) ω := by
  classical
  have he : cumulativeEquiv (size n) (increments n ω) = HigherHeatContinuousCylinders.sample n ω := by
    simp [increments]
  have hi := congrFun he i
  rw [cumulativeEquiv_apply, cumulative_apply] at hi
  change MvPolynomial.eval (increments n ω) (positionPolynomial n i) = _
  simpa only [positionPolynomial, map_sum, MvPolynomial.eval_X,
    HigherHeatContinuousCylinders.sample] using hi

theorem position_refinement (n : ℕ) (i : Fin (size n)) :
    positionCylinder (n+1) (oddIndex i) = positionCylinder n i := by
  apply realize_injective
  ext ω
  have hleft := realize_position (n+1) (oddIndex i) ω
  have hright := realize_position n i ω
  have ht := congrFun (HigherHeatContinuousCylinders.sample_restriction n ω) i
  exact hleft.trans (ht.trans hright.symm)


end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialPathDomain
