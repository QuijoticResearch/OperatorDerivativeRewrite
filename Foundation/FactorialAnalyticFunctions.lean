import Foundation.FactorialAnalyticHeat
import Mathlib.Topology.CompactOpen

/-! Faithful smooth function realization and classical higher-heat solutions. -/
noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.FactorialAnalyticFunctions
open FactorialAnalyticDomain FactorialAnalyticHeat PseudoPolynomialStein

def realize (u : H) : C(ℝ, ℝ) where
  toFun x := mean 1 x u
  continuous_toFun := continuous_iff_continuousAt.mpr (fun x =>
    (mean_hasDerivAt 1 x u).differentiableAt.continuousAt)

theorem realize_apply (u : H) (x : ℝ) : realize u x = mean 1 x u := rfl

theorem realize_zero (u : H) : realize u 0 = u 0 := by
  change evolution 1 0 u 0 = u 0
  rw [evolution_zero]
  rfl

theorem realize_deriv (u : H) :
    deriv (realize u : ℝ → ℝ) = (realize (shift u) : ℝ → ℝ) := by
  funext x
  have hd := (mean_hasDerivAt 1 x u).deriv
  change deriv (fun t : ℝ => mean 1 t u) x = mean 1 x (shift u)
  simpa only [pow_one] using hd

theorem realize_iterated (n : ℕ) (u : H) :
    iteratedDeriv n (realize u : ℝ → ℝ) = (realize ((shift^n) u) : ℝ → ℝ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, realize_deriv, pow_succ']
    rfl

theorem coordinate_recovery (u : H) (n : ℕ) :
    iteratedDeriv n (realize u : ℝ → ℝ) 0 = u n := by
  rw [realize_iterated, realize_zero, shift_pow_apply, zero_add]

theorem realize_injective : Function.Injective realize := by
  intro u v he
  ext n
  have hh := congrArg (fun f : C(ℝ, ℝ) => iteratedDeriv n (f : ℝ → ℝ) 0) he
  simpa only [coordinate_recovery] using hh

theorem expectation_one_order (a : ℝ) (P : Polynomial ℝ) : expectation 1 a P = P.eval a := by
  have he : Polynomial.leval a = expectation 1 a := by
    apply expectation_unique 1 a
    · simp
    · intro Q
      simp [Polynomial.leval_apply, eval_mul, eval_X]
  exact (LinearMap.congr_fun he P).symm

theorem realize_polynomial (P : Polynomial ℝ) (x : ℝ) : realize (polynomial P) x = P.eval x := by
  rw [realize_apply, mean_polynomial 1 (by norm_num), expectation_one_order]

theorem realize_bound (u : H) (x : ℝ) : |realize u x| ≤ Real.exp |x| * ‖u‖ :=
  (mean 1 x).le_of_opNorm_le (mean_norm 1 x) u

theorem heat_equation (p : ℕ) (u : H) (a x : ℝ) :
    HasDerivAt (fun t : ℝ => realize (evolution p t u) x)
      (iteratedDeriv p (realize (evolution p a u) : ℝ → ℝ) x) a := by
  have hd := (mean 1 x).hasFDerivAt.comp_hasDerivAt a (evolution_hasDerivAt p a u)
  convert hd using 1
  · rfl
  · rw [realize_iterated]
    exact congrArg (fun v : H => realize v x) (shift_evolution p p a u)

theorem actual_polynomial_solution (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (P : Polynomial ℝ) (x : ℝ) :
    realize (evolution (2 * m) ((-1 : ℝ)^(m + 1)*(t : ℝ)) (polynomial P)) x =
      ∫ y : ℝ, P.eval (x + y) * HigherHeatSignedLaws.realKernel m hm t ht y := by
  rw [evolution_polynomial (2 * m) (by omega), realize_polynomial]
  exact (PureOrderPolynomialTransport.actual_kernel_transport m hm t ht P x).symm

theorem realize_continuous : Continuous realize := by
  let : NormedAlgebra ℚ (H →L[ℝ] H) := NormedAlgebra.restrictScalars ℚ ℝ _
  have he : Continuous (fun z : H × ℝ => evolution 1 z.2 z.1) := by
    have hc : Continuous (fun z : H × ℝ => NormedSpace.exp (z.2 • shift^1)) :=
      NormedSpace.exp_continuous.comp (continuous_snd.smul continuous_const)
    exact hc.clm_apply continuous_fst
  let f : C(H × ℝ, ℝ) := ⟨fun z => mean 1 z.2 z.1,
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 0).continuous.comp he⟩
  exact f.curry.continuous

def realization : H →L[ℝ] C(ℝ, ℝ) where
  toFun := realize
  map_add' u v := by ext x; exact (mean 1 x).map_add u v
  map_smul' c u := by ext x; exact (mean 1 x).map_smul c u
  cont := realize_continuous

theorem realize_smooth (u : H) (n : ℕ) : ContDiff ℝ n (realize u : ℝ → ℝ) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := (n : ℕ∞))
  intro k hk
  rw [realize_iterated]
  exact fun x => (mean_hasDerivAt 1 x ((shift^k) u)).differentiableAt

theorem physical_heat_equation (m : ℕ) (u : H) (t x : ℝ) :
    HasDerivAt (fun s : ℝ => realize (evolution (2 * m) ((-1 : ℝ)^(m + 1)*s) u) x)
      ((-1 : ℝ)^(m + 1) * iteratedDeriv (2 * m)
        (realize (evolution (2 * m) ((-1 : ℝ)^(m + 1)*t) u) : ℝ → ℝ) x) t := by
  have hd := (heat_equation (2 * m) u ((-1 : ℝ)^(m + 1)*t) x).comp t
    ((hasDerivAt_id t).const_mul ((-1 : ℝ)^(m + 1)))
  simpa only [Function.comp_def, one_mul, mul_comm] using hd

end OperatorDerivativeRewrite.Foundation.FactorialAnalyticFunctions
