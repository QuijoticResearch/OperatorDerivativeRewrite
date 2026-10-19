import Foundation.RiemannThetaComplexKernel
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
/-! Holomorphy and exact derivatives of the actual arithmetic theta kernel.
The moment series is holomorphic on Re(v)>0. Composition gives an analytic
kernel on Re(exp(4u))>0. At each nonzero value the normalized principal log
defines a genuine local phase and reconstructs the Fourier amplitude nearby.
No global logarithm, actual saddle existence or contour estimate is asserted. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaComplexKernel
open RiemannQuarticSaddleTheta RiemannQuarticKernel

theorem term_hasDerivAt (k n : ℕ) (v : ℂ) :
    HasDerivAt (fun w => complexThetaTerm k w n)
      (-(Real.pi : ℂ)*complexThetaTerm (k+2) v n) v := by
  have h := (((hasDerivAt_id v).const_mul
    ((-Real.pi*((n+1 : ℕ) : ℝ)^2 : ℝ) : ℂ)).cexp).const_mul
    ((((n+1 : ℕ) : ℝ)^k : ℂ))
  convert h using 1
  · funext w
    rfl
  · simp only [complexThetaTerm, pow_add, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow, id_eq]
    ring

theorem term_norm_le (k n : ℕ) (c : ℝ) (v : ℂ) (hv : c ≤ v.re) :
    ‖complexThetaTerm k v n‖ ≤ thetaTerm k c n := by
  rw [norm_complexThetaTerm]
  exact thetaTerm_antitone k n hv

theorem moment_differentiableOn_lower (k : ℕ) (c : ℝ) (hc : 0 < c) :
    DifferentiableOn ℂ (moment k) {v : ℂ | c < v.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (thetaTerm_summable k c hc)
  · intro n v hv
    exact (term_hasDerivAt k n v).differentiableAt.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro n v hv
    exact term_norm_le k n c v hv.le

theorem moment_differentiableAt (k : ℕ) (v : ℂ) (hv : 0 < v.re) :
    DifferentiableAt ℂ (moment k) v := by
  exact (moment_differentiableOn_lower k (v.re/2) (by linarith)).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      change v.re/2 < v.re
      linarith))
theorem moment_hasDerivAt (k : ℕ) (v : ℂ) (hv : 0 < v.re) :
    HasDerivAt (moment k) (-(Real.pi : ℂ)*moment (k+2) v) v := by
  have hs := Complex.hasSum_deriv_of_summable_norm
    (thetaTerm_summable k (v.re/2) (by linarith))
    (fun n w _ => (term_hasDerivAt k n w).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun n w hw => term_norm_le k n (v.re/2) w hw.le)
    (show v ∈ {w : ℂ | v.re/2 < w.re} from by change v.re/2 < v.re; linarith)
  simp_rw [(term_hasDerivAt k _ v).deriv] at hs
  have hs' : HasSum (fun n => -(Real.pi : ℂ)*complexThetaTerm (k+2) v n)
      (-(Real.pi : ℂ)*moment (k+2) v) := by
    apply HasSum.mul_left
    simpa only [Nat.zero_add, moment] using (complexThetaTail_summable (k+2) 0 v hv).hasSum
  have heq : deriv (moment k) v=-(Real.pi : ℂ)*moment (k+2) v := hs.unique hs'
  rw [← heq]
  exact (moment_differentiableAt k v hv).hasDerivAt

theorem moment_analyticAt (k : ℕ) (v : ℂ) (hv : 0 < v.re) :
    AnalyticAt ℂ (moment k) v :=
  (moment_differentiableOn_lower k (v.re/2) (by linarith)).analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      change v.re/2 < v.re
      linarith))

theorem kernelComplex_differentiableAt (u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) :
    DifferentiableAt ℂ kernelComplex u := by
  have he (a : ℂ) : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (a*w)) u :=
    (((hasDerivAt_id u).const_mul a).cexp).differentiableAt
  exact (((he 9).const_mul (2*(Real.pi : ℂ)^2)).mul
    ((moment_differentiableAt 4 _ hu).comp u (he 4))).sub
    (((he 5).const_mul (3*(Real.pi : ℂ))).mul
      ((moment_differentiableAt 2 _ hu).comp u (he 4)))

theorem kernelComplex_analyticAt (u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) :
    AnalyticAt ℂ kernelComplex u := by
  have hopen : IsOpen {w : ℂ | 0 < (Complex.exp (4*w)).re} :=
    isOpen_lt continuous_const
      (Complex.continuous_re.comp (Complex.continuous_exp.comp (continuous_const.mul continuous_id)))
  apply DifferentiableOn.analyticAt (s := {w : ℂ | 0 < (Complex.exp (4*w)).re})
  · intro w hw
    exact (kernelComplex_differentiableAt w hw).differentiableWithinAt
  · exact hopen.mem_nhds hu

def kernelDerivative (u : ℂ) : ℂ :=
  30*(Real.pi : ℂ)^2*Complex.exp (9*u)*moment 4 (Complex.exp (4*u))-
    8*(Real.pi : ℂ)^3*Complex.exp (13*u)*moment 6 (Complex.exp (4*u))-
    15*(Real.pi : ℂ)*Complex.exp (5*u)*moment 2 (Complex.exp (4*u))

theorem kernelComplex_hasDerivAt (u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) :
    HasDerivAt kernelComplex (kernelDerivative u) u := by
  have he (a : ℂ) := ((hasDerivAt_id u).const_mul a).cexp
  have hm (k : ℕ) := (moment_hasDerivAt k _ hu).comp u (he 4)
  have hd := (((he 9).const_mul (2*(Real.pi : ℂ)^2)).mul (hm 4)).sub
    (((he 5).const_mul (3*(Real.pi : ℂ))).mul (hm 2))
  convert hd using 1
  · funext w
    rfl
  · have h13 : Complex.exp (13*u)=Complex.exp (9*u)*Complex.exp (4*u) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h9 : Complex.exp (9*u)=Complex.exp (5*u)*Complex.exp (4*u) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    dsimp [kernelDerivative]
    rw [h13,h9]
    norm_num
    ring

theorem kernel_normalized_log_analyticAt (u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) (hne : kernelComplex u ≠ 0) :
    AnalyticAt ℂ (fun w => Complex.log (kernelComplex w/kernelComplex u)) u := by
  apply ((kernelComplex_analyticAt u hu).div analyticAt_const hne).clog
  change kernelComplex u/kernelComplex u ∈ Complex.slitPlane
  rw [div_self hne]
  simp

theorem kernel_normalized_log_hasDerivAt (u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) (hne : kernelComplex u ≠ 0) :
    HasDerivAt (fun w => Complex.log (kernelComplex w/kernelComplex u))
      (kernelDerivative u/kernelComplex u) u := by
  have h := ((kernelComplex_hasDerivAt u hu).div_const (kernelComplex u)).clog
    (show kernelComplex u/kernelComplex u ∈ Complex.slitPlane from by
      rw [div_self hne]; simp)
  simpa only [div_self hne, div_one] using h

theorem kernel_normalized_log_reconstruct (u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) (hne : kernelComplex u ≠ 0) :
    ∀ᶠ w in nhds u,
      kernelComplex u*Complex.exp (Complex.log (kernelComplex w/kernelComplex u))=
        kernelComplex w := by
  have hc := ((kernelComplex_differentiableAt u hu).continuousAt.div_const
    (kernelComplex u))
  have hz : kernelComplex u/kernelComplex u ≠ 0 := by rw [div_self hne]; exact one_ne_zero
  have he : ∀ᶠ w in nhds u, kernelComplex w/kernelComplex u ≠ 0 :=
    hc.eventually_ne hz
  filter_upwards [he] with w hw
  rw [Complex.exp_log hw]
  field_simp

/-- A genuine local phase, normalized at a nonzero kernel value. -/
def localPhase (t x : ℝ) (base w : ℂ) : ℂ :=
  (t : ℂ)*w^4+Complex.I*(x : ℂ)*w+
    Complex.log (kernelComplex w/kernelComplex base)

theorem localPhase_hasDerivAt (t x : ℝ) (u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) (hne : kernelComplex u ≠ 0) :
    HasDerivAt (localPhase t x u)
      (4*(t : ℂ)*u^3+Complex.I*(x : ℂ)+kernelDerivative u/kernelComplex u) u := by
  have h := ((((hasDerivAt_id u).pow 4).const_mul (t : ℂ)).add
    ((hasDerivAt_id u).const_mul (Complex.I*(x : ℂ)))).add
    (kernel_normalized_log_hasDerivAt u hu hne)
  convert h using 1
  · funext w
    rfl
  · simp only [id_eq]
    norm_num
    ring

theorem localPhase_reconstruct (t x : ℝ) (u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) (hne : kernelComplex u ≠ 0) :
    ∀ᶠ w in nhds u,
      kernelComplex u*Complex.exp (localPhase t x u w)=
        Complex.exp ((t : ℂ)*w^4+Complex.I*(x : ℂ)*w)*kernelComplex w := by
  filter_upwards [kernel_normalized_log_reconstruct u hu hne] with w hw
  rw [localPhase, Complex.exp_add]
  calc
    _ = Complex.exp ((t : ℂ)*w^4+Complex.I*(x : ℂ)*w)*
        (kernelComplex u*Complex.exp (Complex.log (kernelComplex w/kernelComplex u))) := by ring
    _ = _ := by rw [hw]

end OperatorDerivativeRewrite.Foundation.RiemannThetaComplexKernel
