import Foundation.ComplexRootPoissonLaw
import Foundation.PoissonContractionAlgebra

/-! A genuine compound-root transition semigroup with an actual bounded generator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonSemigroup
open ComplexFourthRootNoise ComplexFourthRootWalk ComplexRootTransitionOperator

local instance : NormedAlgebra ℝ (Test →L[ℂ] Test) :=
  NormedAlgebra.restrictScalars ℝ ℂ (Test →L[ℂ] Test)

local instance : Nontrivial Test := ⟨⟨BoundedContinuousFunction.const ℂ 0,
    BoundedContinuousFunction.const ℂ 1, by
      intro h
      have he := congrArg (fun f : Test => f 0) h
      norm_num at he⟩⟩

local instance : NormOneClass (Test →L[ℂ] Test) := ⟨ContinuousLinearMap.norm_id⟩

set_option backward.isDefEq.respectTransparency false in
theorem walk_successor_integral (n : ℕ) (a : ℝ) (F : ℂ → ℂ) (z : ℂ) :
    (∫ ω, F (z + terminal (n+1) a ω) ∂ComplexFourthRootWalk.probability (n+1)) =
      ∫ k : Fin 4, (∫ ω, F (z + noise a k + terminal n a ω)
        ∂ComplexFourthRootWalk.probability n) ∂ComplexFourthRootNoise.probability := by
  calc
    _ = ∫ p : Fin 4 × Sample n, F (z + noise a p.1 + terminal n a p.2)
        ∂ComplexFourthRootNoise.probability.prod (ComplexFourthRootWalk.probability n) := by
      unfold ComplexFourthRootWalk.probability
      rw [← ((measurePreserving_piFinSuccAbove
        (fun _ : Fin (n+1) => ComplexFourthRootNoise.probability) 0).symm).integral_comp']
      congr 1
      funext p
      simp only [Function.comp_def, terminal, increment,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.sum_univ_succ,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove,
        cast_eq, Fin.cons_zero]
      congr 1
      ring
    _ = _ := integral_prod _ Integrable.of_finite

theorem step_pow_apply (a : ℝ) (n : ℕ) (f : Test) (z : ℂ) :
    ((step a)^n) f z = ∫ ω, f (z + terminal n a ω) ∂ComplexFourthRootWalk.probability n := by
  induction n generalizing z with
  | zero => simp [terminal]
  | succ n ih =>
    rw [pow_succ']
    change step a (((step a)^n) f) z = _
    rw [step_integral, walk_successor_integral]
    apply integral_congr_ae
    exact Eventually.of_forall (fun k => ih (z+noise a k))

def transition (a t : ℝ) : Test →L[ℂ] Test := PoissonContractionAlgebra.evolution (step a) t

theorem transition_zero (a : ℝ) : transition a 0 = ContinuousLinearMap.id ℂ Test :=
  PoissonContractionAlgebra.evolution_zero (step a)

theorem transition_add (a s t : ℝ) :
    transition a (s+t) = (transition a s).comp (transition a t) :=
  PoissonContractionAlgebra.evolution_add (step a) s t

theorem transition_continuous (a : ℝ) : Continuous (transition a) :=
  PoissonContractionAlgebra.evolution_continuous (step a)

theorem transition_hasDerivAt (a t : ℝ) :
    HasDerivAt (transition a)
      ((transition a t).comp (step a - ContinuousLinearMap.id ℂ Test)) t :=
  PoissonContractionAlgebra.evolution_hasDerivAt (step a) t

theorem transition_norm (a : ℝ) (r : ℝ≥0) : ‖transition a r‖ ≤ 1 :=
  PoissonContractionAlgebra.evolution_norm (step a) (step_norm a) r

theorem transition_average (a : ℝ) (r : ℝ≥0) :
    transition a r = ∫ n : ℕ, (step a)^n ∂poissonMeasure r :=
  (PoissonContractionAlgebra.average_eq_evolution (step a) (step_norm a) r).symm

theorem transition_average_apply (a : ℝ) (r : ℝ≥0) (f : Test) (z : ℂ) :
    transition a r f z = ∫ n : ℕ, ((step a)^n) f z ∂poissonMeasure r := by
  let ev : (Test →L[ℂ] Test) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ z).comp (ContinuousLinearMap.apply ℂ Test f)
  rw [transition_average]
  change ev (∫ n : ℕ, (step a)^n ∂poissonMeasure r) =
    ∫ n : ℕ, ev ((step a)^n) ∂poissonMeasure r
  exact (ev.integral_comp_comm (PoissonContractionAlgebra.powers_integrable (step a) (step_norm a) r)).symm

theorem transition_law (a : ℝ) (r : ℝ≥0) (f : Test) (z : ℂ) :
    transition a r f z = ∫ y, f (z+y) ∂ComplexRootPoissonLaw.law r a := by
  let fz : Test := BoundedContinuousFunction.compContinuousCLM ℂ ℂ
    ⟨fun y => z+y, continuous_const.add continuous_id⟩ f
  have he := ComplexRootPoissonLaw.integral_bounded r a fz
  rw [transition_average_apply]
  simp_rw [step_pow_apply]
  exact he.symm

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonSemigroup
