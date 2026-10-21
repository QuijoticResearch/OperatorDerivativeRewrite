import Foundation.PolynomialStripLimit
import Foundation.RiemannQuadraticOperatorApproximation

/-! The classical coarse de Bruijn strip bound for the ACTUAL quadratic Xi flow.
Existing exact Xi polynomial approximants, actual Gaussian/operator convergence,
finite-polynomial heat strip contraction and nonzero entire strip closure discharge
all transfer hypotheses. The resulting all-real statement for t >= 1/2 is the
classical upper bound, not a zero-time/RH theorem or an exact threshold value. -/
noncomputable section
open Polynomial Complex Set Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticGlobalStrip
open RiemannEvenFlow PureOrderPolynomialTransport

theorem flow_zero_strip (t : ℝ) (ht : 0≤t) (z : ℂ) (hz : flow 1 t z=0) :
    z.im^2≤max (1-2*t) 0 := by
  let s : ℝ≥0 := ⟨t,ht⟩
  let B : ℝ := max (1-2*t) 0
  have hB : 0≤B := le_max_right _ _
  obtain ⟨P,h0,hstrip,heven,hlim,hbudget,hheat⟩ :=
    RiemannQuadraticOperatorApproximation.exists_actual_uniform_operator_approximation
  have hPn (n : ℕ) : P n≠0 := by
    intro hzero
    have he := h0 n
    rw [hzero,Polynomial.map_zero,eval_zero] at he
    exact (RiemannQuadraticDivisor.flow_origin_ne_zero 0) he.symm
  have hinit (n : ℕ) (a : ℂ) (ha : ((P n).map (algebraMap ℝ ℂ)).eval a=0) : a.im^2≤(1:ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a.im) (by norm_num : (0:ℝ)≤1)).mpr
      (hstrip n a ha)
  let Q : ℕ → ℂ[X] := fun n => (transport 2 (-t) (P n)).map (algebraMap ℝ ℂ)
  have hQ (n : ℕ) (a : ℂ) (ha : (Q n).eval a=0) : a.im^2≤B := by
    simpa only [one_pow] using
      PolynomialStripLimit.quadratic_heat_strip (P n) (hPn n) t 1 ht (hinit n) a ha
  have he := PolynomialStripLimit.strip_zero_limit Q (flow 1 t) (Real.sqrt B)
    (flow_differentiable 1 t) ⟨0,RiemannQuadraticDivisor.flow_origin_ne_zero t⟩
    (fun n a ha => Real.abs_le_sqrt (hQ n a ha))
    (fun w => (tendstoLocallyUniformlyOn_univ.mpr (hheat s)).tendsto_at (mem_univ w)) z hz
  have hsq := (sq_le_sq₀ (abs_nonneg z.im) (Real.sqrt_nonneg B)).mpr he
  simpa only [sq_abs,Real.sq_sqrt hB] using hsq

theorem real_zeros_after_half (t : ℝ) (ht : 1/2≤t) (z : ℂ) (hz : flow 1 t z=0) : z.im=0 := by
  have he := flow_zero_strip t (by linarith) z hz
  rw [max_eq_right (by linarith : 1-2*t≤0)] at he
  nlinarith [sq_nonneg z.im]

theorem classical_half_all_real : ∀ z : ℂ,flow 1 (1/2) z=0 → z.im=0 :=
  fun z hz => real_zeros_after_half (1/2) (by norm_num) z hz

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticGlobalStrip
