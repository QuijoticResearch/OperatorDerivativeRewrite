import Foundation.LpProducts
import Foundation.Adjoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Genuine one-coordinate Gaussian polynomial functions and their actual derivatives. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Polynomial
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianCore

/-- The nondegenerate, standard real Gaussian probability measure. -/
abbrev γ : Measure ℝ := gaussianReal 0 1

/-- Gaussian polynomial functions have every finite positive moment. -/
theorem polynomial_memLp (p : ℝ[X]) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun x : ℝ => p.eval x) r γ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert MeasureTheory.MemLp.add hp hq using 1
      funext x; simp
  | monomial n a =>
    cases n with
    | zero => simpa using (memLp_const a : MemLp (fun _ : ℝ => a) r γ)
    | succ n =>
      have h := (memLp_id_gaussianReal' (μ := 0) (v := 1)
        (r * (n + 1 : ℕ)) (ENNReal.mul_ne_top hr (by simp))).norm_rpow_div (n + 1 : ℕ)
      have hd : r * (n + 1 : ℕ) / (n + 1 : ℕ) = r := by
        rw [ENNReal.mul_div_cancel_right (by positivity) (by simp)]
      rw [hd] at h
      simp only [ENNReal.toReal_natCast, Real.rpow_natCast, id_eq] at h
      have hp : MemLp (fun x : ℝ => x ^ (n + 1)) r γ :=
        (memLp_norm_iff (by fun_prop)).mp (by simpa [norm_pow] using h)
      simpa [eval_monomial, mul_comm] using hp.const_mul a

/-- Smoothness is inherited from actual polynomial evaluation. -/
theorem polynomial_smooth (p : ℝ[X]) : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : ℝ => p.eval x) := by
  convert p.contDiff_aeval (𝕜 := ℝ) (⊤ : WithTop ℕ∞) using 1
  funext x; simp

/-- Differentiation of an actual function, rather than prescribed coefficient data. -/
theorem polynomial_hasDerivAt (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => p.eval y) (p.derivative.eval x) x := p.hasDerivAt x

/-- Continuous Gaussian representatives that agree almost everywhere agree everywhere. -/
theorem continuous_representation_unique {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[γ] g) : f = g :=
  MeasureTheory.Measure.eq_of_ae_eq
    ((gaussianReal_absolutelyContinuous' 0 (by norm_num)).ae_le h) hf hg

/-- Different polynomial representations of the same random variable have the same derivative. -/
theorem derivative_representation_independent (p q : ℝ[X])
    (h : (fun x => p.eval x) =ᵐ[γ] (fun x => q.eval x)) :
    (fun x => p.derivative.eval x) = (fun x => q.derivative.eval x) := by
  have he := continuous_representation_unique p.continuous q.continuous h
  funext x
  rw [← p.deriv (x := x), ← q.deriv (x := x), he]

/-- A substantive product rule for the derivatives of actual polynomial functions. -/
theorem derivative_product (p q : ℝ[X]) (x : ℝ) :
    deriv (fun y => p.eval y * q.eval y) x =
      p.derivative.eval x * q.eval x + p.eval x * q.derivative.eval x :=
  ((p.hasDerivAt x).mul (q.hasDerivAt x)).deriv

/-- A substantive chain rule for polynomial cylindrical functions. -/
theorem derivative_chain (p q : ℝ[X]) (x : ℝ) :
    deriv (fun y => p.eval (q.eval y)) x =
      p.derivative.eval (q.eval x) * q.derivative.eval x :=
  by
  simpa only [Function.comp_def] using
    ((p.hasDerivAt (q.eval x)).comp x (q.hasDerivAt x)).deriv

/-- Derivative of the standard Gaussian density, proved from its exponential formula. -/
theorem density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hg : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    convert ((hasDerivAt_pow 2 x).neg.div_const (2 : ℝ)) using 1; ring
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have he : gaussianPDFReal 0 1 = (fun y : ℝ => c * Real.exp (-(y ^ 2) / 2)) := by
    funext y; simp [gaussianPDFReal, c]
  rw [he]
  convert hg.exp.const_mul c using 1; ring

/-- Gaussian integrability transfers to ordinary integration against the density. -/
theorem integrable_density_mul {f : ℝ → ℝ} (hf : Integrable f γ) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [γ, gaussianReal_of_var_ne_zero 0 (by norm_num)] at hf
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using hf

/-- Stein's identity for genuine polynomials; all three integrability requirements are proved. -/
theorem polynomial_stein (p : ℝ[X]) :
    (∫ x, p.eval x * x ∂γ) = ∫ x, p.derivative.eval x ∂γ := by
  have hi (q : ℝ[X]) : Integrable (fun x : ℝ => q.eval x) γ :=
    (polynomial_memLp q 1 (by simp)).integrable (by simp)
  have hx : Integrable (fun x : ℝ => p.eval x * x) γ := by
    convert hi (p * X) using 1
    funext x; simp
  have h1 := integrable_density_mul hx
  have h2 := integrable_density_mul (hi p.derivative)
  have h3 := integrable_density_mul (hi p)
  have hneg : Integrable (fun x => p.eval x * (-x * gaussianPDFReal 0 1 x)) := by
    convert h1.neg using 1; funext x; simp only [Pi.neg_apply]; ring
  have hp : Integrable (fun x => p.derivative.eval x * gaussianPDFReal 0 1 x) := by
    convert h2 using 1; funext x; ring
  have hv : Integrable (fun x => p.eval x * gaussianPDFReal 0 1 x) := by
    convert h3 using 1; funext x; ring
  have hb := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => p.hasDerivAt x) (fun x _ => density_hasDerivAt x) hneg hp hv
  rw [integral_gaussianReal_eq_integral_smul (by norm_num),
    integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]
  have he : (fun x => gaussianPDFReal 0 1 x * (p.eval x * x)) =
      -(fun x => p.eval x * (-x * gaussianPDFReal 0 1 x)) := by
    funext x; simp only [Pi.neg_apply]; ring
  rw [he]
  change (∫ x, -(p.eval x * (-x * gaussianPDFReal 0 1 x))) = _
  rw [integral_neg, hb, neg_neg]
  congr 1; funext x; ring

/-- The polynomial Gaussian divergence, determined by the actual derivative. -/
def divergencePolynomial (q : ℝ[X]) : ℝ[X] := X * q - q.derivative

/-- Genuine Gaussian integration by parts, without an assumed Stein identity. -/
theorem polynomial_integration_by_parts (p q : ℝ[X]) :
    (∫ x, p.derivative.eval x * q.eval x ∂γ) =
      ∫ x, p.eval x * (divergencePolynomial q).eval x ∂γ := by
  have hi (a b : ℝ[X]) : Integrable (fun x : ℝ => a.eval x * b.eval x) γ := by
    simpa using (polynomial_memLp (a * b) 1 (by simp)).integrable (by simp)
  have h := polynomial_stein (p * q)
  simp only [derivative_mul, eval_add, eval_mul] at h
  rw [integral_add (hi p.derivative q) (hi p q.derivative)] at h
  simp only [divergencePolynomial, eval_sub, eval_mul, eval_X, mul_sub]
  rw [integral_sub (by
    convert hi p (X * q) using 1
    funext x; simp)
    (hi p q.derivative)]
  have he : (∫ x, p.eval x * (x * q.eval x) ∂γ) =
      ∫ x, p.eval x * q.eval x * x ∂γ := by
    congr 1; funext x; ring
  rw [he, h]; ring

/-- A genuine rank-one isonormal coordinate on the standard Gaussian space. -/
def W (h x : ℝ) : ℝ := h * x

/-- The coordinate has Gaussian law with mean zero and variance h². -/
theorem W_gaussian_law (h : ℝ) :
    γ.map (W h) = gaussianReal 0 (⟨h ^ 2, sq_nonneg h⟩ : NNReal) := by
  convert gaussianReal_map_const_mul (μ := 0) (v := 1) h using 1
  · rfl
  · congr 1
    · simp
    · apply NNReal.eq; change h ^ 2 = h ^ 2 * 1; ring

/-- Pull a one-coordinate polynomial cylinder back to the canonical Gaussian coordinate. -/
def coordinatePolynomial (h : ℝ) (p : ℝ[X]) : ℝ[X] := p.comp (C h * X)

theorem coordinatePolynomial_eval (h : ℝ) (p : ℝ[X]) (x : ℝ) :
    (coordinatePolynomial h p).eval x = p.eval (W h x) := by
  simp [coordinatePolynomial, W]

/-- The rank-one Malliavin derivative is the actual chain derivative p'(W h) h. -/
theorem cylindrical_hasDerivAt (h : ℝ) (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => p.eval (W h y)) (p.derivative.eval (W h x) * h) x := by
  simpa [W, Function.comp_def] using
    (p.hasDerivAt (h * x)).comp x ((hasDerivAt_id x).const_mul h)

/-- The Gaussian coordinate is not an essentially bounded multiplier. -/
theorem coordinate_not_memLp_top : ¬ MemLp (fun x : ℝ => x) ∞ γ := by
  intro hf
  have he : eLpNormEssSup (fun x : ℝ => x) γ < ⊤ := by
    simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp he
  change ∀ᵐ x ∂γ, ‖x‖₊ ≤ C at hC
  have hb : ∀ᵐ x ∂γ, ‖x‖ ≤ (C : ℝ) := hC.mono fun x hx => by exact_mod_cast hx
  have hmin : (fun x : ℝ => min ‖x‖ (C : ℝ)) = (fun x : ℝ => ‖x‖) :=
    continuous_representation_unique (continuous_norm.min continuous_const) continuous_norm
      (hb.mono fun _ hx => min_eq_left hx)
  have ht := congrFun hmin ((C : ℝ) + 1)
  have hc : 0 ≤ (C : ℝ) := C.property
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith), min_eq_right (by linarith)] at ht
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianCore
