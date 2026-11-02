import Foundation.ComplexGaussianPolynomialTransport
import Foundation.GaussianBoundedBanachStein
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Polynomial
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.RiemannStochasticBridge
open RiemannEvenFlow RiemannEvenEvolution RiemannEvenDomain
open RiemannQuarticFlow (halfLine)

/-- All complex derivatives of the ACTUAL quadratic Xi flow, observed by real translation. -/
def observable (k : ℕ) (t : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  symmetricJet 1 k t (z+(y:ℂ))

def horizontalBound (k : ℕ) (t : ℝ) (z : ℂ) : ℝ :=
  ((∫ u : ℝ, weighted 1 k t (-z.im) u ∂halfLine)+
    (∫ u : ℝ, weighted 1 k t z.im u ∂halfLine))/2

private theorem weighted_integral_nonneg (k : ℕ) (t B : ℝ) :
    0≤∫ u : ℝ, weighted 1 k t B u ∂halfLine := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact weighted_nonneg 1 k t B u hu

theorem horizontalBound_nonneg (k : ℕ) (t : ℝ) (z : ℂ) :
    0≤horizontalBound k t z := by
  exact div_nonneg (add_nonneg (weighted_integral_nonneg k t _) (weighted_integral_nonneg k t _)) (by norm_num)

private theorem jet_norm_le (k : ℕ) (t : ℝ) (w : ℂ) :
    ‖jet 1 k t w‖≤∫ u : ℝ, weighted 1 k t (-w.im) u ∂halfLine := by
  calc
    _ ≤ ∫ u : ℝ, ‖integrand 1 k t w u‖ ∂halfLine := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      exact RiemannQuadraticGaussian.integrand_norm t k w u hu

/-- The bound depends on Im(z), NEVER on the real Gaussian coordinate. -/
theorem observable_bound (k : ℕ) (t : ℝ) (z : ℂ) (y : ℝ) :
    ‖observable k t z y‖≤horizontalBound k t z := by
  have h1 := jet_norm_le k t (z+(y:ℂ))
  have h2 := jet_norm_le k t (-(z+(y:ℂ)))
  simp only [Complex.add_im,Complex.ofReal_im,add_zero,Complex.neg_im,neg_neg] at h1 h2
  have htri := norm_add_le (jet 1 k t (z+(y:ℂ)))
    ((-1:ℂ)^k*jet 1 k t (-(z+(y:ℂ))))
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] at htri
  unfold observable symmetricJet horizontalBound
  rw [norm_div,Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right (htri.trans (add_le_add h1 h2)) (by norm_num)

theorem observable_hasDerivAt (k : ℕ) (t : ℝ) (z : ℂ) (y : ℝ) :
    HasDerivAt (observable k t z) (observable (k+1) t z y) y := by
  have h := (symmetricJet_hasDerivAt 1 k t (z+(y:ℂ))).comp (y:ℂ)
    ((hasDerivAt_id (y:ℂ)).const_add z)
  simpa only [mul_one,observable,Function.comp_def] using! h.comp_ofReal

theorem observable_continuous (k : ℕ) (t : ℝ) (z : ℂ) :
    Continuous (observable k t z) :=
  continuous_iff_continuousAt.mpr fun y => (observable_hasDerivAt k t z y).continuousAt

/-- Genuine Gaussian Lp domains, including L-infinity; no factorial sequence domain. -/
theorem observable_memLp (s : ℝ≥0) (k : ℕ) (t : ℝ) (z : ℂ) (p : ℝ≥0∞) :
    MemLp (observable k t z) p (RiemannQuadraticGaussian.law s) := by
  exact MemLp.of_bound (observable_continuous k t z).aestronglyMeasurable
    (horizontalBound k t z) (Eventually.of_forall (observable_bound k t z))

theorem polynomial_pairing_integrable (s : ℝ≥0) (k : ℕ) (t : ℝ) (z : ℂ) (Q : ℂ[X]) :
    Integrable (fun y : ℝ => Q.eval (y:ℂ)*observable k t z y) (RiemannQuadraticGaussian.law s) := by
  exact (ComplexGaussianPolynomialTransport.complex_polynomial_integrable s Q).mul_bdd
    (observable_continuous k t z).aestronglyMeasurable
    (Eventually.of_forall (observable_bound k t z))

/-- Exact mean in the original flow convention: REAL Gaussian shifts DECREASE time. -/
theorem observable_average (s : ℝ≥0) (k : ℕ) (t : ℝ) (z : ℂ) :
    (∫ y : ℝ, observable k t z y ∂RiemannQuadraticGaussian.law s)=
      symmetricJet 1 k (t-(s:ℝ)) z := by
  have he (y : ℝ) : observable k t z y=
    (jet 1 k t (z+(y:ℂ))+(-1:ℂ)^k*jet 1 k t (-z+(-1:ℂ)*(y:ℂ)))/2 := by
    unfold observable symmetricJet
    congr 2
    congr 1
    ring
  have hp := RiemannQuadraticGaussian.shifted_jet_average s t 1 k z 1 (by norm_num)
  simp only [one_mul,mul_one] at hp
  have hn := RiemannQuadraticGaussian.shifted_jet_average s t 1 k (-z) (-1) (by norm_num)
  simp only [mul_one] at hn
  simp_rw [he]
  rw [integral_div,integral_add
    (by simpa using RiemannQuadraticGaussian.shifted_jet_integrable s t k z 1)
    ((RiemannQuadraticGaussian.shifted_jet_integrable s t k (-z) (-1)).const_mul _),integral_const_mul,
    hp,hn]
  simp only [symmetricJet]

/-- Actual all-derivative FIRST-chaos Stein bridge. This is not full reconstruction. -/
theorem actual_xi_stein (s : ℝ≥0) (k : ℕ) (t : ℝ) (z : ℂ) :
    (∫ y : ℝ, (y:ℂ)*observable k t z y ∂RiemannQuadraticGaussian.law s)=
      (2*(s:ℝ):ℂ)*symmetricJet 1 (k+1) (t-(s:ℝ)) z := by
  have h := GaussianBoundedBanachStein.scaled_stein
    (observable k t z) (observable (k+1) t z) (observable_hasDerivAt k t z)
    (observable_continuous (k+1) t z).stronglyMeasurable
    (horizontalBound k t z) (horizontalBound (k+1) t z)
    (horizontalBound_nonneg k t z) (horizontalBound_nonneg (k+1) t z)
    (observable_bound k t z) (observable_bound (k+1) t z) 0 (2*s)
  simp only [zero_add,Complex.real_smul] at h
  change (∫ y : ℝ, (y:ℂ)*observable k t z y ∂RiemannQuadraticGaussian.law s)=
    ((2*s:ℝ≥0):ℂ)*(∫ y : ℝ, observable (k+1) t z y ∂RiemannQuadraticGaussian.law s) at h
  rw [observable_average] at h
  simpa using h

/-- Bilinear covariance, without complex conjugation; at real x the observables are real. -/
def covariance (s : ℝ≥0) (t : ℝ) (z : ℂ) (j k : ℕ) : ℂ :=
  (∫ y : ℝ, observable j t z y*observable k t z y ∂RiemannQuadraticGaussian.law s)-
    (∫ y : ℝ, observable j t z y ∂RiemannQuadraticGaussian.law s)*
    (∫ y : ℝ, observable k t z y ∂RiemannQuadraticGaussian.law s)

theorem pair_integrable (s : ℝ≥0) (t : ℝ) (z : ℂ) (j k : ℕ) :
    Integrable (fun y => observable j t z y*observable k t z y) (RiemannQuadraticGaussian.law s) := by
  exact ((observable_memLp s j t z 1).integrable (by norm_num)).mul_bdd
    (observable_continuous k t z).aestronglyMeasurable
    (Eventually.of_forall (observable_bound k t z))

def laguerreValue (t : ℝ) (z : ℂ) : ℂ :=
  (symmetricJet 1 1 t z)^2-symmetricJet 1 0 t z*symmetricJet 1 2 t z

/-- The exact missing SIGN term when Gaussian/conditional projection transports curvature. -/
theorem actual_laguerre_covariance (s : ℝ≥0) (t : ℝ) (z : ℂ) :
    laguerreValue (t-(s:ℝ)) z=
      (∫ y : ℝ, (observable 1 t z y)^2-observable 0 t z y*observable 2 t z y
        ∂RiemannQuadraticGaussian.law s)-covariance s t z 1 1+covariance s t z 0 2 := by
  simp only [pow_two]
  rw [integral_sub (pair_integrable s t z 1 1) (pair_integrable s t z 0 2)]
  unfold covariance laguerreValue
  simp_rw [observable_average]
  ring

/-- A nondegenerate positive variance mixture has the OPPOSITE degree-two Turan sign. -/
theorem two_variance_turan (q r v : ℝ) :
    (q*r+(1-q)*v)^2-(q*r^2+(1-q)*v^2)= -q*(1-q)*(r-v)^2 := by
  ring

/-- Positive contraction eigenvalues from a genuine two-variance Gaussian mixture. -/
def mixtureEigenvalue (n : ℕ) : ℝ := (1+(1/2:ℝ)^n)/2

theorem mixtureEigenvalue_bounds (n : ℕ) :
    0<mixtureEigenvalue n ∧ mixtureEigenvalue n≤1 := by
  have hp : 0<(1/2:ℝ)^n := pow_pos (by norm_num) _
  have hu : (1/2:ℝ)^n≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold mixtureEigenvalue
  constructor <;> linarith

theorem mixture_finite_contraction {N : ℕ} (c : Fin N → ℝ) :
    (∑ j, (mixtureEigenvalue j.val*c j)^2)≤∑ j, (c j)^2 := by
  apply Finset.sum_le_sum
  intro j hj
  have h := mixtureEigenvalue_bounds j.val
  have hs : (mixtureEigenvalue j.val)^2≤1 := by nlinarith
  simpa only [mul_pow,one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (c j))

theorem mixture_turan_negative :
    (mixtureEigenvalue 1)^2-mixtureEigenvalue 0*mixtureEigenvalue 2= -1/16 := by
  norm_num [mixtureEigenvalue]

def mixtureJensenTwo (z : ℂ) : ℂ :=
  (mixtureEigenvalue 0:ℂ)+2*(mixtureEigenvalue 1:ℂ)*z+(mixtureEigenvalue 2:ℂ)*z^2

theorem mixture_jensen_nonreal_zero :
    mixtureJensenTwo (-6/5+(2/5:ℂ)*Complex.I)=0 ∧
      (-6/5+(2/5:ℂ)*Complex.I).im≠0 := by
  constructor <;> norm_num [mixtureJensenTwo,mixtureEigenvalue,Complex.ext_iff,
    pow_two,Complex.mul_re,Complex.mul_im]

def mixtureTransform (z : ℂ) : ℂ := (Complex.exp (-z^2)+Complex.exp (-(z^2)/2))/2

theorem mixture_gaussian_representation (z : ℂ) :
    mixtureTransform z=
      ((∫ y : ℝ, Complex.exp (Complex.I*z*(y:ℂ)) ∂RiemannQuadraticGaussian.law 1)+
        (∫ y : ℝ, Complex.exp (Complex.I*z*(y:ℂ)) ∂RiemannQuadraticGaussian.law (1/2)))/2 := by
  rw [RiemannQuadraticGaussian.gaussian_phase_integral,RiemannQuadraticGaussian.gaussian_phase_integral]
  have he : (Complex.I*z)^2= -z^2 := by rw [mul_pow,Complex.I_sq];ring
  simp only [he,mixtureTransform]
  norm_num
  ring

theorem mixture_transform_nonreal_zero :
    mixtureTransform ((Real.sqrt Real.pi:ℂ)*(1+Complex.I))=0 ∧
      0<((Real.sqrt Real.pi:ℂ)*(1+Complex.I)).im := by
  have hr : 0<Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hs : ((Real.sqrt Real.pi:ℂ)*(1+Complex.I))^2=2*(Real.pi:ℂ)*Complex.I := by
    have h : (Real.sqrt Real.pi:ℂ)^2=(Real.pi:ℂ) := by
      exact_mod_cast Real.sq_sqrt Real.pi_pos.le
    calc
      _ = (Real.sqrt Real.pi:ℂ)^2*(2*Complex.I) := by ring_nf;simp [Complex.I_sq]
      _ = _ := by rw [h];ring
  have he : Complex.exp (-(Real.pi:ℂ)*Complex.I)= -1 := by
    rw [show -(Real.pi:ℂ)*Complex.I= -((Real.pi:ℂ)*Complex.I) from by ring,
      Complex.exp_neg,Complex.exp_pi_mul_I]
    norm_num
  have he2 : Complex.exp (-(2*(Real.pi:ℂ)*Complex.I))=1 := by
    rw [show -(2*(Real.pi:ℂ)*Complex.I)=-(Real.pi:ℂ)*Complex.I+(-(Real.pi:ℂ)*Complex.I) from by ring,
      Complex.exp_add,he]
    norm_num
  constructor
  · unfold mixtureTransform
    rw [hs,he2,show -(2*(Real.pi:ℂ)*Complex.I)/2=-(Real.pi:ℂ)*Complex.I from by ring,he]
    norm_num
  · simpa using hr

/-- The SAME genuine Gaussian averaging operation can destroy even the first Laguerre inequality. -/
theorem quadratic_gaussian_average (z : ℂ) :
    (∫ y : ℝ, (z+(y:ℂ))^2-1 ∂RiemannQuadraticGaussian.law 1)=z^2+1 := by
  have hi : Integrable (fun y : ℝ => (y:ℂ)) (RiemannQuadraticGaussian.law 1) := by
    simpa only [pow_one] using ComplexGaussianPolynomialTransport.complex_power_integrable 1 1
  have hi2 := ComplexGaussianPolynomialTransport.complex_power_integrable 1 2
  have h1 := ComplexGaussianPolynomialTransport.complex_power_average 1 1
  have h2 := ComplexGaussianPolynomialTransport.complex_power_average 1 2
  norm_num [PseudoPolynomialStein.moment] at h1 h2
  have he (y : ℝ) : (z+(y:ℂ))^2-1=((z^2-1)+(2*z)*(y:ℂ))+(y:ℂ)^2 := by ring
  have hc : Integrable (fun _y : ℝ => z^2-1) (RiemannQuadraticGaussian.law 1) := integrable_const _
  have hl : Integrable (fun y : ℝ => (2*z)*(y:ℂ)) (RiemannQuadraticGaussian.law 1) := hi.const_mul _
  have hsum := hc.add hl
  simp_rw [he]
  have ha : (∫ y : ℝ, z^2-1+(2*z)*(y:ℂ)+(y:ℂ)^2 ∂RiemannQuadraticGaussian.law 1)=
      (∫ y : ℝ, z^2-1+(2*z)*(y:ℂ) ∂RiemannQuadraticGaussian.law 1)+
        (∫ y : ℝ, (y:ℂ)^2 ∂RiemannQuadraticGaussian.law 1) := by
    simpa only [Pi.add_apply] using integral_add hsum hi2
  have hb : (∫ y : ℝ, z^2-1+(2*z)*(y:ℂ) ∂RiemannQuadraticGaussian.law 1)=
      (∫ _y : ℝ, z^2-1 ∂RiemannQuadraticGaussian.law 1)+
        (∫ y : ℝ, (2*z)*(y:ℂ) ∂RiemannQuadraticGaussian.law 1) := by
    simpa only [Pi.add_apply] using integral_add hc hl
  rw [ha,hb,integral_const_mul,h1,h2]
  simp
  ring

theorem quadratic_original_real_roots (z : ℂ) (hz : z^2-1=0) : z.im=0 := by
  have h : (z-1)*(z+1)=0 := by linear_combination hz
  rcases mul_eq_zero.mp h with h|h
  · have he : z=1 := sub_eq_zero.mp h
    simp [he]
  · have he : z= -1 := eq_neg_of_add_eq_zero_left h
    simp [he]

theorem quadratic_original_laguerre_positive (x : ℝ) : 0<(2*x)^2-(x^2-1)*2 := by
  nlinarith [sq_nonneg x]

theorem quadratic_mean_nonreal_zero : Complex.I^2+1=0 ∧ Complex.I.im≠0 := by
  simp

theorem quadratic_mean_laguerre_negative :
    (0:ℂ)^2-(∫ y : ℝ, ((0:ℂ)+(y:ℂ))^2-1 ∂RiemannQuadraticGaussian.law 1)*2= -2 := by
  rw [quadratic_gaussian_average]
  norm_num

end OperatorDerivativeRewrite.Foundation.RiemannStochasticBridge
