import Foundation.RiemannQuadraticStripEvolution

/-! Exact arithmetic half-plane transfer and two limitations of strip/real-axis data.
All arithmetic nonvanishing assumptions remain explicit. -/
noncomputable section
open Complex Polynomial
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticArithmeticHeat
open RiemannEvenFlow

theorem zero_time_strip (theta : ℝ)
    (hfree : ∀ w : ℂ, theta < w.re → riemannZeta w ≠ 0)
    (z : ℂ) (hz : flow 1 0 z = 0) : |z.im| ≤ 2*theta-1 := by
  have hn (w : ℂ) (hw : w.im < 1-2*theta) : flow 1 0 w ≠ 0 := by
    have he : RiemannRealOrderFlow.flow 1 0 w = flow 1 0 w := by
      simpa only [Nat.cast_one] using RiemannRealOrderFlow.flow_nat 1 0 w
    rw [← he]
    exact RiemannQuadraticXiTransfer.nonzero_of_zeta_half_plane theta hfree 1 w hw
  rw [abs_le]
  constructor
  · by_contra h
    exact hn z (by linarith [lt_of_not_ge h]) hz
  · by_contra h
    have hc : flow 1 0 (conj z) = 0 := by
      rw [RiemannEvenWindowZeros.flow_conj 1 0, hz]
      simp
    exact hn (conj z) (by simp only [Complex.conj_im]; linarith [lt_of_not_ge h]) hc

theorem heat_strip (theta : ℝ)
    (hfree : ∀ w : ℂ, theta < w.re → riemannZeta w ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (hz : flow 1 t z = 0) :
    z.im^2 ≤ max ((2*theta-1)^2-2*t) 0 := by
  have he := RiemannQuadraticStripEvolution.strip_between_times
    0 t (2*theta-1) ht (zero_time_strip theta hfree) z hz
  simpa only [sub_zero] using he

theorem real_after_wait (theta : ℝ)
    (hfree : ∀ w : ℂ, theta < w.re → riemannZeta w ≠ 0)
    (t : ℝ) (ht : (2*theta-1)^2/2 ≤ t)
    (z : ℂ) (hz : flow 1 t z = 0) : z.im = 0 := by
  apply RiemannQuadraticStripEvolution.real_after_strip_wait
    0 t (2*theta-1) (zero_time_strip theta hfree) (by simpa using ht) z hz

-- The endpoint premise is a strong arithmetic hypothesis, not supplied by 7/8.
theorem critical_half_plane_real_forward
    (hfree : ∀ w : ℂ, (1/2 : ℝ) < w.re → riemannZeta w ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (hz : flow 1 t z = 0) : z.im = 0 := by
  exact real_after_wait (1/2) hfree t (by norm_num; exact ht) z hz

-- Bounds with boundaries tending to 1/2 do require independent arithmetic input.
theorem asymptotic_half_planes_real_forward
    (hfree : ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ w : ℂ, (1/2 : ℝ)+epsilon < w.re → riemannZeta w ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (hz : flow 1 t z = 0) : z.im = 0 := by
  apply critical_half_plane_real_forward _ t ht z hz
  intro w hw
  let epsilon : ℝ := (w.re-1/2)/2
  exact hfree epsilon (by dsimp [epsilon]; linarith) w (by dsimp [epsilon]; linarith)

-- Sharpness of strip data for GENERAL polynomial heat, not an actual Xi zero.
theorem polynomial_strip_sharpness :
    (∀ a : ℂ,
      ((Polynomial.X^2 + Polynomial.C (9/16) : ℝ[X]).map (algebraMap ℝ ℂ)).eval a = 0 →
      |a.im| ≤ (3/4 : ℝ)) ∧
    ((PureOrderPolynomialTransport.transport 2 (-1/4)
      (Polynomial.X^2 + Polynomial.C (9/16) : ℝ[X])).map (algebraMap ℝ ℂ)).eval (I/4) = 0 ∧
    (I/4 : ℂ).im ≠ 0 := by
  constructor
  · intro a ha
    have he : a^2+(9/16 : ℂ) = 0 := by simpa using ha
    have hf : (a-3*I/4)*(a+3*I/4) = 0 := by
      linear_combination he - (9/16 : ℂ)*Complex.I_sq
    rcases mul_eq_zero.mp hf with h | h
    · rw [sub_eq_zero.mp h]
      norm_num
    · rw [eq_neg_iff_add_eq_zero.mpr h]
      norm_num
  · have hx : PureOrderPolynomialTransport.transport 2 (-1/4) Polynomial.X =
        (Polynomial.X : ℝ[X]) := by
      simpa [ComplexGaussianPolynomialTransport.transport_one] using
        ComplexGaussianPolynomialTransport.transport_mul_X (-1/4) 1
    have hs : PureOrderPolynomialTransport.transport 2 (-1/4) (Polynomial.X^2) =
        (Polynomial.X^2 + Polynomial.C (-1/2) : ℝ[X]) := by
      rw [show (Polynomial.X : ℝ[X])^2 = Polynomial.X*Polynomial.X by ring,
        ComplexGaussianPolynomialTransport.transport_mul_X, hx]
      norm_num
    constructor
    · have hc : PureOrderPolynomialTransport.transport 2 (-1/4) (Polynomial.C (9/16)) =
          (Polynomial.C (9/16) : ℝ[X]) := by
        have he : (Polynomial.C (9/16) : ℝ[X]) = (9/16 : ℝ) • (1 : ℝ[X]) := by
          simp [Polynomial.smul_eq_C_mul]
        calc
          _ = PureOrderPolynomialTransport.transport 2 (-1/4) ((9/16 : ℝ) • (1 : ℝ[X])) :=
            congrArg _ he
          _ = (9/16 : ℝ) • (1 : ℝ[X]) := by
            rw [map_smul, ComplexGaussianPolynomialTransport.transport_one]
          _ = _ := he.symm
      rw [map_add, hs, hc]
      norm_num [div_pow, Complex.I_sq]
    · norm_num

-- Real-axis exclusion alone supplies no complex zero-free half-plane for
-- general conjugation-symmetric polynomials. This is not a Dirichlet L-function.
theorem real_axis_exclusion_not_half_plane :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (∀ z : ℂ, f (conj z) = conj (f z)) ∧ (∀ x : ℝ, f (x : ℂ) ≠ 0) ∧
      ∃ z : ℂ, f z = 0 ∧ (7/8 : ℝ) < z.re := by
  refine ⟨fun z => (z-1)^2+1, by fun_prop, ?_, ?_, 1+I, ?_, ?_⟩
  · intro z
    simp
  · intro x hx
    have he := congrArg Complex.re hx
    have hr : (x-1)^2+1 = (0 : ℝ) := by
      simpa [pow_two, Complex.mul_re] using he
    nlinarith [sq_nonneg (x-1)]
  · simp [Complex.I_sq]
  · norm_num

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticArithmeticHeat
