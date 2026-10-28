import Foundation.SU2QuadraticWilsonChannel
import Mathlib.Analysis.Complex.Exponential

/-! A bounded, actual exponential-weight vacuum certificate.
Only the first two kinetic moments are used; no analytic eigenbranch or
stationary vacuum existence is assumed. The four-edge Wilson application
is a temporal loop marginal, not a four-dimensional spatial gap theorem. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

/-- Quadratic positive-vacuum candidate before a smallness condition. -/
def trial (A B t x : ℝ) : ℝ := 1+A*t*x+B*t^2*(x^2-1/4)

def lowPart (A B t x : ℝ) : ℝ :=
  1+(1+A)*t*x+t^2*((B+A+1/2)*x^2-B/4)

def errorConstant (A B : ℝ) : ℝ :=
  (2+Real.exp 1)*(1+|A|+|B|)

private theorem square_center_bound (x : ℝ) (hx : |x| ≤ 1) : |x^2-1/4| ≤ 1 := by
  have h := (abs_le.mp hx)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg (x-1), sq_nonneg (x+1),
    mul_nonneg (sub_nonneg.mpr h.2) (by linarith : 0 ≤ x+1)]

theorem trial_bound (A B t x : ℝ) (ht : |t| ≤ 1) (hx : |x| ≤ 1) :
    |trial A B t x| ≤ 1+|A|+|B| := by
  have ht2 : |t|^2 ≤ 1 := by nlinarith [abs_nonneg t]
  have h1 : |A*t*x| ≤ |A| := by
    rw [abs_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_left hx (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
      (by simpa using mul_le_mul_of_nonneg_left ht (abs_nonneg A))
  have h2 : |B*t^2*(x^2-1/4)| ≤ |B| := by
    rw [abs_mul,abs_mul,abs_pow]
    exact (mul_le_mul_of_nonneg_left (square_center_bound x hx)
      (mul_nonneg (abs_nonneg _) (sq_nonneg _))).trans
      (by simpa using mul_le_mul_of_nonneg_left ht2 (abs_nonneg B))
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (by simpa using add_le_add_left h1 1)) h2)

theorem trial_positive (A B t x : ℝ) (hx : |x| ≤ 1)
    (hsmall : |A| * |t|+|B| * |t|^2 ≤ 1/2) : 1/2 ≤ trial A B t x := by
  have h1 : |A*t*x| ≤ |A| * |t| := by
    rw [abs_mul,abs_mul]
    simpa using mul_le_mul_of_nonneg_left hx (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have h2 : |B*t^2*(x^2-1/4)| ≤ |B| * |t|^2 := by
    rw [abs_mul,abs_mul,abs_pow]
    simpa using mul_le_mul_of_nonneg_left (square_center_bound x hx)
      (mul_nonneg (abs_nonneg _) (sq_nonneg _))
  dsimp [trial]
  linarith [neg_abs_le (A*t*x),neg_abs_le (B*t^2*(x^2-1/4))]

theorem exponential_remainder (t x : ℝ) (ht : |t| ≤ 1) (hx : |x| ≤ 1) :
    |Real.exp (t*x)-(1+t*x+(t*x)^2/2)| ≤ |t|^3*Real.exp 1 := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((t*x : ℝ) : ℂ) 3
  norm_num [Finset.sum_range_succ] at h
  have he : ((Real.exp (t*x)-(1+t*x+(t*x)^2/2) : ℝ) : ℂ) =
      Complex.exp ((t*x : ℝ) : ℂ)-(1+((t*x : ℝ) : ℂ)+((t*x : ℝ) : ℂ)^2/2) := by
    push_cast
    rfl
  simp only [Complex.ofReal_mul] at he
  rw [← he,Complex.norm_real,Real.norm_eq_abs] at h
  have h' : |Real.exp (t*x)-(1+t*x+(t*x)^2/2)| ≤
      |t*x|^3*Real.exp |t*x| := by simpa only [abs_mul] using h
  have htx : |t*x| ≤ |t| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  exact h'.trans (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) htx 3)
    (Real.exp_le_exp.mpr (htx.trans ht)) (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _))

theorem weighted_remainder (A B t x : ℝ) (ht : |t| ≤ 1) (hx : |x| ≤ 1) :
    |Real.exp (t*x)*trial A B t x-lowPart A B t x| ≤
      |t|^3*errorConstant A B := by
  let R := Real.exp (t*x)-(1+t*x+(t*x)^2/2)
  have he : Real.exp (t*x)*trial A B t x-lowPart A B t x =
      R*trial A B t x+t^3*(B*x*(x^2-1/4)+A*x^3/2)+
      t^4*(B*x^2*(x^2-1/4)/2) := by dsimp [R,trial,lowPart]; ring
  have htx : |t|^4 ≤ |t|^3 := by
    simpa only [pow_succ, mul_one] using mul_le_mul_of_nonneg_left ht (pow_nonneg (abs_nonneg t) 3)
  have hx2 : |x|^2 ≤ 1 := by nlinarith [abs_nonneg x]
  have hx3 : |x|^3 ≤ 1 := (pow_le_pow_left₀ (abs_nonneg x) hx 3).trans (by norm_num)
  have hb : |B*x*(x^2-1/4)| ≤ |B| := by
    rw [abs_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_left (square_center_bound x hx)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans (by simpa using mul_le_mul_of_nonneg_left hx (abs_nonneg B))
  have ha : |A*x^3/2| ≤ |A|/2 := by
    rw [abs_div,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hx3 (abs_nonneg A)) (by norm_num)
  have hc : |B*x^2*(x^2-1/4)/2| ≤ |B|/2 := by
    rw [abs_div,abs_mul,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (mul_le_mul_of_nonneg_left (square_center_bound x hx) (mul_nonneg (abs_nonneg _) (sq_nonneg _))).trans
      (by simpa using mul_le_mul_of_nonneg_left hx2 (abs_nonneg B))
  have hR : |R*trial A B t x| ≤ |t|^3*Real.exp 1*(1+|A|+|B|) := by
    rw [abs_mul]
    exact mul_le_mul (exponential_remainder t x ht hx) (trial_bound A B t x ht hx)
      (abs_nonneg _) (mul_nonneg (pow_nonneg (abs_nonneg t) 3) (Real.exp_pos _).le)
  have h3 : |t^3*(B*x*(x^2-1/4)+A*x^3/2)| ≤ |t|^3*(|B|+|A|/2) := by
    rw [abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hb ha)) (pow_nonneg (abs_nonneg t) 3)
  have h4 : |t^4*(B*x^2*(x^2-1/4)/2)| ≤ |t|^3*(|B|/2) := by
    rw [abs_mul,abs_pow]
    exact mul_le_mul htx hc (abs_nonneg _) (pow_nonneg (abs_nonneg t) 3)
  rw [he]
  apply (abs_add_le (R*trial A B t x+t^3*(B*x*(x^2-1/4)+A*x^3/2))
    (t^4*(B*x^2*(x^2-1/4)/2))).trans
  have hsum := (abs_add_le (R*trial A B t x) (t^3*(B*x*(x^2-1/4)+A*x^3/2))).trans
    (add_le_add hR h3)
  have hp := pow_nonneg (abs_nonneg t) 3
  have hA := abs_nonneg A
  have hB := abs_nonneg B
  dsimp [errorConstant]
  nlinarith [mul_nonneg hp hA,mul_nonneg hp hB]

end OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

namespace OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

def linearCoefficient (a : ℝ) : ℝ := a/(1-a)
def quadraticTrialCoefficient (a r : ℝ) : ℝ := r*(1+a)/(2*(1-a)*(1-r))
def vacuumSecond (a : ℝ) : ℝ := (1+a)/(8*(1-a))

theorem lowPart_moment_identity (a r t x : ℝ) (ha : a ≠ 1) (hr : r ≠ 1) :
    1+(1+linearCoefficient a)*t*(a*x)+
      t^2*((quadraticTrialCoefficient a r+linearCoefficient a+1/2)*
        (1/4+r*(x^2-1/4))-quadraticTrialCoefficient a r/4) =
      trial (linearCoefficient a) (quadraticTrialCoefficient a r) t x+vacuumSecond a*t^2 := by
  dsimp [linearCoefficient,quadraticTrialCoefficient,vacuumSecond,trial]
  field_simp [sub_ne_zero.mpr (Ne.symm ha),sub_ne_zero.mpr (Ne.symm hr)]
  <;> ring

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

private theorem trial_measurable (A B t : ℝ) (Y : Ω → ℝ) (hY : Measurable Y) :
    Measurable (fun ω => trial A B t (Y ω)) := by
  unfold trial
  fun_prop

private theorem lowPart_integrable (A B t : ℝ) (Y : Ω → ℝ)
    (hY : Measurable Y) (hb : ∀ ω, |Y ω| ≤ 1) :
    Integrable (fun ω => lowPart A B t (Y ω)) μ := by
  have h1 := BoundedExponentialTiltResponse.bounded_power_integrable μ Y hY hb 1
  have h2 := BoundedExponentialTiltResponse.bounded_power_integrable μ Y hY hb 2
  simp only [pow_one] at h1
  convert ((integrable_const (1:ℝ)).add (h1.const_mul ((1+A)*t))).add
    (((h2.const_mul (B+A+1/2)).sub (integrable_const (B/4))).const_mul (t^2)) using 1
  funext ω
  rfl

private theorem exponential_trial_integrable (A B t : ℝ) (ht : |t| ≤ 1)
    (Y : Ω → ℝ) (hY : Measurable Y) (hb : ∀ ω, |Y ω| ≤ 1) :
    Integrable (fun ω => Real.exp (t*Y ω)*trial A B t (Y ω)) μ := by
  apply Integrable.of_bound
    (((measurable_const.mul hY).exp.mul (trial_measurable A B t Y hY)).aestronglyMeasurable)
    (Real.exp 1*(1+|A|+|B|))
  filter_upwards with ω
  change ‖Real.exp (t*Y ω)*trial A B t (Y ω)‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  have he : t*Y ω ≤ 1 := calc
    _ ≤ |t*Y ω| := le_abs_self _
    _ = |t| * |Y ω| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg t)
    _ ≤ 1 := by simpa using ht
  exact mul_le_mul (Real.exp_le_exp.mpr he) (trial_bound A B t (Y ω) ht (hb ω))
    (abs_nonneg _) (Real.exp_pos _).le

theorem lowPart_integral (A B t : ℝ) (Y : Ω → ℝ)
    (hY : Measurable Y) (hb : ∀ ω, |Y ω| ≤ 1) :
    (∫ ω, lowPart A B t (Y ω) ∂μ) =
      1+(1+A)*t*(∫ ω, Y ω ∂μ)+t^2*((B+A+1/2)*(∫ ω, Y ω^2 ∂μ)-B/4) := by
  have h1 := BoundedExponentialTiltResponse.bounded_power_integrable μ Y hY hb 1
  have h2 := BoundedExponentialTiltResponse.bounded_power_integrable μ Y hY hb 2
  simp only [pow_one] at h1
  have hu := (h1.const_mul ((1+A)*t))
  have hv := ((h2.const_mul (B+A+1/2)).sub (integrable_const (B/4))).const_mul (t^2)
  have houter := integral_add ((integrable_const (1:ℝ)).add hu) hv
  have hinner := integral_add (integrable_const (1:ℝ)) hu
  have hsub := integral_sub (h2.const_mul (B+A+1/2)) (integrable_const (B/4))
  simp only [Pi.add_apply,Pi.sub_apply] at houter hinner hsub
  dsimp [lowPart]
  rw [houter,hinner,integral_const_mul,integral_const_mul,hsub,integral_const_mul]
  simp

theorem exponential_trial_moment_error (a r t x : ℝ) (ha : a ≠ 1) (hr : r ≠ 1)
    (ht : |t| ≤ 1) (Y : Ω → ℝ) (hY : Measurable Y) (hb : ∀ ω, |Y ω| ≤ 1)
    (hfirst : (∫ ω, Y ω ∂μ)=a*x)
    (hsecond : (∫ ω, Y ω^2 ∂μ)=1/4+r*(x^2-1/4)) :
    |(∫ ω, Real.exp (t*Y ω)*trial (linearCoefficient a)
        (quadraticTrialCoefficient a r) t (Y ω) ∂μ)-
      (trial (linearCoefficient a) (quadraticTrialCoefficient a r) t x+vacuumSecond a*t^2)| ≤
      |t|^3*errorConstant (linearCoefficient a) (quadraticTrialCoefficient a r) := by
  let A := linearCoefficient a
  let B := quadraticTrialCoefficient a r
  have hi := (exponential_trial_integrable μ A B t ht Y hY hb).sub
    (lowPart_integrable μ A B t Y hY hb)
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => Real.exp (t*Y ω)*trial A B t (Y ω)-lowPart A B t (Y ω))
    (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using weighted_remainder A B t (Y ω) ht (hb ω)))
  have hsub := integral_sub (exponential_trial_integrable μ A B t ht Y hY hb)
    (lowPart_integrable μ A B t Y hY hb)
  rw [hsub,Real.norm_eq_abs] at h
  simp only [probReal_univ,mul_one] at h
  rw [lowPart_integral μ A B t Y hY hb,hfirst,hsecond] at h
  dsimp [A,B] at h
  rw [lowPart_moment_identity a r t x ha hr] at h
  exact h

end OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

namespace OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

def eigenErrorConstant (a r : ℝ) : ℝ :=
  errorConstant (linearCoefficient a) (quadraticTrialCoefficient a r)+
    |vacuumSecond a| * (|linearCoefficient a|+|quadraticTrialCoefficient a r|)

theorem eigenErrorConstant_nonneg (a r : ℝ) : 0 ≤ eigenErrorConstant a r := by
  unfold eigenErrorConstant errorConstant
  positivity

private theorem trial_deviation (A B t x : ℝ) (ht : |t| ≤ 1) (hx : |x| ≤ 1) :
    |trial A B t x-1| ≤ |t| * (|A|+|B|) := by
  have ht2 : |t|^2 ≤ |t| := by nlinarith [abs_nonneg t]
  have h1 : |A*t*x| ≤ |t| * |A| := by
    rw [abs_mul,abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx (mul_nonneg (abs_nonneg A) (abs_nonneg t))]
  have h2 : |B*t^2*(x^2-1/4)| ≤ |t| * |B| := by
    rw [abs_mul,abs_mul,abs_pow]
    calc
      _ ≤ |B| * |t|^2*1 := mul_le_mul_of_nonneg_left (square_center_bound x hx)
        (mul_nonneg (abs_nonneg B) (sq_nonneg _))
      _ ≤ |t| * |B| := by nlinarith [mul_le_mul_of_nonneg_left ht2 (abs_nonneg B)]
  have he : trial A B t x-1=A*t*x+B*t^2*(x^2-1/4) := by unfold trial; ring
  rw [he]
  exact (abs_add_le _ _).trans (by nlinarith)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem exponential_trial_eigen_error (a r t x : ℝ) (ha : a ≠ 1) (hr : r ≠ 1)
    (ht : |t| ≤ 1) (hx : |x| ≤ 1) (Y : Ω → ℝ)
    (hY : Measurable Y) (hb : ∀ ω, |Y ω| ≤ 1)
    (hfirst : (∫ ω, Y ω ∂μ)=a*x)
    (hsecond : (∫ ω, Y ω^2 ∂μ)=1/4+r*(x^2-1/4)) :
    |(∫ ω, Real.exp (t*Y ω)*trial (linearCoefficient a)
        (quadraticTrialCoefficient a r) t (Y ω) ∂μ)-
      (1+vacuumSecond a*t^2)*trial (linearCoefficient a) (quadraticTrialCoefficient a r) t x| ≤
      |t|^3*eigenErrorConstant a r := by
  let w := trial (linearCoefficient a) (quadraticTrialCoefficient a r) t x
  let E := ∫ ω, Real.exp (t*Y ω)*trial (linearCoefficient a)
    (quadraticTrialCoefficient a r) t (Y ω) ∂μ
  have h := exponential_trial_moment_error μ a r t x ha hr ht Y hY hb hfirst hsecond
  have hw := trial_deviation (linearCoefficient a) (quadraticTrialCoefficient a r) t x ht hx
  have hc : |vacuumSecond a*t^2*(w-1)| ≤
      |t|^3*(|vacuumSecond a| * (|linearCoefficient a|+|quadraticTrialCoefficient a r|)) := by
    rw [abs_mul,abs_mul,abs_pow]
    calc
      _ ≤ |vacuumSecond a| * |t|^2*(|t| * (|linearCoefficient a|+|quadraticTrialCoefficient a r|)) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg (abs_nonneg _) (sq_nonneg _))
      _ = _ := by ring
  have he : E-(1+vacuumSecond a*t^2)*w=(E-(w+vacuumSecond a*t^2))-vacuumSecond a*t^2*(w-1) := by ring
  change |E-(1+vacuumSecond a*t^2)*w| ≤ _
  rw [he]
  have htri : |(E-(w+vacuumSecond a*t^2))-vacuumSecond a*t^2*(w-1)| ≤
      |E-(w+vacuumSecond a*t^2)|+|vacuumSecond a*t^2*(w-1)| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (E-(w+vacuumSecond a*t^2))
      (vacuumSecond a*t^2*(w-1))
  exact htri.trans ((add_le_add h hc).trans (le_of_eq (by dsimp [eigenErrorConstant]; ring)))

/-- Explicit positive supersolution bound for the actual exponential integral.
The displayed moment assumptions must be verified for the chosen kinetic law. -/
theorem exponential_trial_supersolution (a r t x : ℝ) (ha : a ≠ 1) (hr : r ≠ 1)
    (ht : |t| ≤ 1) (hx : |x| ≤ 1)
    (hsmall : |linearCoefficient a| * |t|+|quadraticTrialCoefficient a r| * |t|^2 ≤ 1/2)
    (Y : Ω → ℝ) (hY : Measurable Y) (hb : ∀ ω, |Y ω| ≤ 1)
    (hfirst : (∫ ω, Y ω ∂μ)=a*x)
    (hsecond : (∫ ω, Y ω^2 ∂μ)=1/4+r*(x^2-1/4)) :
    (∫ ω, Real.exp (t*Y ω)*trial (linearCoefficient a)
        (quadraticTrialCoefficient a r) t (Y ω) ∂μ) ≤
      (1+vacuumSecond a*t^2+2*eigenErrorConstant a r*|t|^3)*
        trial (linearCoefficient a) (quadraticTrialCoefficient a r) t x := by
  have he := exponential_trial_eigen_error μ a r t x ha hr ht hx Y hY hb hfirst hsecond
  have hp := trial_positive (linearCoefficient a) (quadraticTrialCoefficient a r) t x hx hsmall
  have hC := eigenErrorConstant_nonneg a r
  have hab := le_abs_self ((∫ ω, Real.exp (t*Y ω)*trial (linearCoefficient a)
    (quadraticTrialCoefficient a r) t (Y ω) ∂μ)-
    (1+vacuumSecond a*t^2)*trial (linearCoefficient a) (quadraticTrialCoefficient a r) t x)
  nlinarith [mul_nonneg (mul_nonneg hC (pow_nonneg (abs_nonneg t) 3)) (by linarith :
    0 ≤ 2*trial (linearCoefficient a) (quadraticTrialCoefficient a r) t x-1)]

end OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

namespace OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel

private theorem mul_measurable : Measurable (fun p : SU2 × SU2 => p.1*p.2) := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology SU2 := homeomorph.symm.secondCountableTopology
  exact continuous_mul.measurable

/-- Distribution of a product of n independent genuine Wilson increments. -/
def walkLaw (β : ℝ) : ℕ → Measure SU2
  | 0 => Measure.dirac 1
  | n+1 => ((increment β).prod (walkLaw β n)).map (fun p => p.1*p.2)

theorem walkLaw_probability (β : ℝ) (n : ℕ) : IsProbabilityMeasure (walkLaw β n) := by
  induction n with
  | zero => dsimp [walkLaw]; infer_instance
  | succ n ih =>
    letI := increment_probability β
    letI := ih
    exact (Measure.isProbabilityMeasure_map_iff mul_measurable.aemeasurable).mpr inferInstance

private theorem walk_integral (β : ℝ) (n : ℕ) (f : SU2 → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ V, |f V| ≤ B) :
    (∫ V, f V ∂walkLaw β (n+1)) = ∫ V, ∫ W, f (V*W) ∂walkLaw β n ∂increment β := by
  letI := increment_probability β
  letI := walkLaw_probability β n
  have hi : Integrable (fun p : SU2 × SU2 => f (p.1*p.2)) ((increment β).prod (walkLaw β n)) := by
    apply Integrable.of_bound (hf.comp mul_measurable).aestronglyMeasurable B
    filter_upwards with p
    simpa only [Real.norm_eq_abs,Function.comp_apply] using hb (p.1*p.2)
  rw [walkLaw,integral_map mul_measurable.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi]

theorem walk_first_moment (β : ℝ) (n : ℕ) (C : SU2) :
    (∫ V, halfTrace (C*V) ∂walkLaw β n)=coefficient β^n*halfTrace C := by
  induction n generalizing C with
  | zero => simp [walkLaw]
  | succ n ih =>
    rw [walk_integral β n (fun V => halfTrace (C*V)) (halfTrace_measurable.comp (measurable_const_mul C)) 1 (fun V => halfTrace_bound (C*V))]
    have he (V : SU2) : (∫ W, halfTrace (C*(V*W)) ∂walkLaw β n)=coefficient β^n*halfTrace (C*V) := by
      simpa only [mul_assoc] using ih (C*V)
    simp_rw [he]
    rw [integral_const_mul]
    change coefficient β^n*step β halfTrace C=_
    rw [halfTrace_eigen,pow_succ]
    ring

private theorem centeredSquare_sandwich (β : ℝ) (L R : SU2) :
    (∫ V, centeredSquare (L*V*R) ∂increment β)=quadraticCoefficient β*centeredSquare (L*R) := by
  have he (V : SU2) : centeredSquare (L*V*R)=centeredSquare ((R*L)*V) := by
    unfold centeredSquare
    rw [halfTrace_mul_comm (L*V) R]
    simp only [mul_assoc]
  simp_rw [he]
  change step β centeredSquare (R*L)=_
  rw [centeredSquare_step]
  unfold centeredSquare
  rw [halfTrace_mul_comm R L]

theorem walk_centered_second (β : ℝ) (n : ℕ) (C : SU2) :
    (∫ V, centeredSquare (C*V) ∂walkLaw β n)=quadraticCoefficient β^n*centeredSquare C := by
  induction n generalizing C with
  | zero => simp [walkLaw]
  | succ n ih =>
    rw [walk_integral β n (fun V => centeredSquare (C*V)) (((halfTrace_measurable.comp (measurable_const_mul C)).pow_const 2).sub measurable_const)
      1 (fun V => square_center_bound (halfTrace (C*V)) (halfTrace_bound (C*V)))]
    simp_rw [← mul_assoc,ih,integral_const_mul]
    change quadraticCoefficient β^n*step β centeredSquare C=_
    rw [centeredSquare_step,pow_succ]
    ring

theorem walk_second_moment (β : ℝ) (n : ℕ) (C : SU2) :
    (∫ V, halfTrace (C*V)^2 ∂walkLaw β n)=
      1/4+quadraticCoefficient β^n*(halfTrace C^2-1/4) := by
  letI := walkLaw_probability β n
  have hi := BoundedExponentialTiltResponse.bounded_power_integrable (walkLaw β n)
    (fun V => halfTrace (C*V)) (halfTrace_measurable.comp (measurable_const_mul C)) (fun V => halfTrace_bound (C*V)) 2
  have h := walk_centered_second β n C
  unfold centeredSquare at h
  rw [integral_sub hi (integrable_const _)] at h
  norm_num at h
  linarith

end OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

namespace OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel

/-- Genuine exponential spatial weight applied to the n-increment loop marginal. -/
def weightedWalk (β : ℝ) (n : ℕ) (t : ℝ) (f : SU2 → ℝ) (C : SU2) : ℝ :=
  ∫ V, Real.exp (t*halfTrace (C*V))*f (C*V) ∂walkLaw β n

theorem weightedWalk_trial_error (β : ℝ) (n : ℕ) (t : ℝ)
    (ha : coefficient β^n ≠ 1) (hr : quadraticCoefficient β^n ≠ 1)
    (ht : |t| ≤ 1) (C : SU2) :
    |weightedWalk β n t (fun D => trial (linearCoefficient (coefficient β^n))
      (quadraticTrialCoefficient (coefficient β^n) (quadraticCoefficient β^n)) t (halfTrace D)) C-
      (1+vacuumSecond (coefficient β^n)*t^2)*
      trial (linearCoefficient (coefficient β^n))
        (quadraticTrialCoefficient (coefficient β^n) (quadraticCoefficient β^n)) t (halfTrace C)| ≤
      |t|^3*eigenErrorConstant (coefficient β^n) (quadraticCoefficient β^n) := by
  letI := walkLaw_probability β n
  exact exponential_trial_eigen_error (walkLaw β n) _ _ _ _ ha hr ht (halfTrace_bound C)
    (fun V => halfTrace (C*V)) (halfTrace_measurable.comp (measurable_const_mul C))
    (fun V => halfTrace_bound (C*V)) (walk_first_moment β n C) (walk_second_moment β n C)

theorem weightedWalk_trial_supersolution (β : ℝ) (n : ℕ) (t : ℝ)
    (ha : coefficient β^n ≠ 1) (hr : quadraticCoefficient β^n ≠ 1)
    (ht : |t| ≤ 1)
    (hsmall : |linearCoefficient (coefficient β^n)| * |t|+
      |quadraticTrialCoefficient (coefficient β^n) (quadraticCoefficient β^n)| * |t|^2 ≤ 1/2)
    (C : SU2) :
    weightedWalk β n t (fun D => trial (linearCoefficient (coefficient β^n))
      (quadraticTrialCoefficient (coefficient β^n) (quadraticCoefficient β^n)) t (halfTrace D)) C ≤
      (1+vacuumSecond (coefficient β^n)*t^2+
        2*eigenErrorConstant (coefficient β^n) (quadraticCoefficient β^n)*|t|^3)*
      trial (linearCoefficient (coefficient β^n))
        (quadraticTrialCoefficient (coefficient β^n) (quadraticCoefficient β^n)) t (halfTrace C) := by
  letI := walkLaw_probability β n
  exact exponential_trial_supersolution (walkLaw β n) _ _ _ _ ha hr ht (halfTrace_bound C)
    hsmall (fun V => halfTrace (C*V)) (halfTrace_measurable.comp (measurable_const_mul C))
    (fun V => halfTrace_bound (C*V)) (walk_first_moment β n C) (walk_second_moment β n C)

/-- This certificate's sufficient positivity window collapses as a tends to one.
It is a limitation of this trial and bound, not of all possible spectral methods. -/
theorem necessary_trial_window (a B t : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hsmall : |linearCoefficient a| * |t|+|B| * |t|^2 ≤ 1/2) :
    |t| ≤ (1-a)/(2*a) := by
  have hA : 0 < linearCoefficient a := div_pos ha (sub_pos.mpr ha1)
  rw [abs_of_pos hA] at hsmall
  have hb : 0 ≤ |B| * |t|^2 := mul_nonneg (abs_nonneg B) (sq_nonneg _)
  have hs : a/(1-a)*|t| ≤ 1/2 := by dsimp [linearCoefficient] at hsmall; linarith
  have hs' : (a*|t|)/(1-a) ≤ 1/2 := by simpa only [div_mul_eq_mul_div] using hs
  have hm := (div_le_iff₀ (sub_pos.mpr ha1)).mp hs'
  apply (le_div_iff₀ (mul_pos (by norm_num) ha)).mpr
  nlinarith

end OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

namespace OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open BoundedExponentialTiltResponse

theorem haar_absolutelyContinuous_increment (β : ℝ) : law ≪ increment β := by
  apply withDensity_absolutelyContinuous'
    (((measurable_const.mul halfTrace_measurable).exp.div_const _).ennreal_ofReal.aemeasurable)
  filter_upwards with V
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (Real.exp_pos _) (partition_pos law halfTrace halfTrace_measurable halfTrace_bound β)

private theorem square_le_one (V : SU2) : halfTrace V^2 ≤ 1 := by
  have hb := abs_le.mp (halfTrace_bound V)
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1-halfTrace V) (by linarith : 0 ≤ 1+halfTrace V)]

theorem secondMoment_lt_one (β : ℝ) : secondMoment β < 1 := by
  letI := increment_probability β
  have hi := bounded_power_integrable (increment β) halfTrace halfTrace_measurable halfTrace_bound 2
  have hm : secondMoment β ≤ 1 := by
    simpa only [secondMoment,integral_const,probReal_univ,one_smul] using
      integral_mono hi (integrable_const (1:ℝ)) square_le_one
  apply lt_of_le_of_ne hm
  intro he
  have hz : (∫ V, 1-halfTrace V^2 ∂increment β)=0 := by
    rw [integral_sub (integrable_const _) hi]
    change (∫ _, (1:ℝ) ∂increment β)-secondMoment β=0
    simp [he]
  have hae := (integral_eq_zero_iff_of_nonneg (fun V => sub_nonneg.mpr (square_le_one V))
    ((integrable_const (1:ℝ)).sub hi)).mp hz
  have hhaar := (haar_absolutelyContinuous_increment β).ae_eq hae
  have heq : (fun V : SU2 => halfTrace V^2)=ᵐ[law] fun _ => (1:ℝ) := by
    filter_upwards [hhaar] with V hV
    change 1-halfTrace V^2=0 at hV
    linarith
  have h := integral_congr_ae heq
  rw [(SU2TiltEnergyResponse.moment_values law).2.1] at h
  norm_num at h

theorem coefficient_square_le_secondMoment (β : ℝ) : coefficient β^2 ≤ secondMoment β := by
  letI := increment_probability β
  have h1 := bounded_power_integrable (increment β) halfTrace halfTrace_measurable halfTrace_bound 1
  have h2 := bounded_power_integrable (increment β) halfTrace halfTrace_measurable halfTrace_bound 2
  simp only [pow_one] at h1
  have he : (fun V : SU2 => (halfTrace V-coefficient β)^2)=
      fun V => (halfTrace V^2-(2*coefficient β)*halfTrace V)+coefficient β^2 := by funext V; ring
  have hnon := integral_nonneg (μ := increment β)
    (f := fun V : SU2 => (halfTrace V-coefficient β)^2) (fun V => sq_nonneg (halfTrace V-coefficient β))
  rw [he] at hnon
  have hadd := integral_add (h2.sub (h1.const_mul (2*coefficient β))) (integrable_const (coefficient β^2))
  have hsub := integral_sub h2 (h1.const_mul (2*coefficient β))
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd,hsub,integral_const_mul] at hnon
  change 0 ≤ secondMoment β-2*coefficient β*coefficient β+(∫ _, coefficient β^2 ∂increment β) at hnon
  simp only [integral_const,probReal_univ,one_smul] at hnon
  nlinarith

theorem coefficient_abs_lt_one (β : ℝ) : |coefficient β| < 1 := by
  have h := coefficient_square_le_secondMoment β
  have hm := secondMoment_lt_one β
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (coefficient β-1),sq_nonneg (coefficient β+1)]

theorem quadraticCoefficient_abs_lt_one (β : ℝ) : |quadraticCoefficient β| < 1 := by
  have hm := secondMoment_lt_one β
  have h0 : 0 ≤ secondMoment β := integral_nonneg (fun V => sq_nonneg (halfTrace V))
  unfold quadraticCoefficient
  rw [abs_lt]
  constructor <;> linarith

theorem kinetic_power_ne_one (β : ℝ) (n : ℕ) (hn : n ≠ 0) :
    coefficient β^n ≠ 1 ∧ quadraticCoefficient β^n ≠ 1 := by
  have hp (z : ℝ) (hz : |z| < 1) : z^n ≠ 1 := by
    have h : |z|^n < 1 := pow_lt_one₀ (abs_nonneg z) hz hn
    rw [← abs_pow] at h
    exact ne_of_lt ((le_abs_self _).trans_lt h)
  exact ⟨hp _ (coefficient_abs_lt_one β),hp _ (quadraticCoefficient_abs_lt_one β)⟩

end OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

namespace OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel

/-- Half weights on both sides of the genuine temporal loop convolution. -/
def symmetricWalk (β : ℝ) (n : ℕ) (t : ℝ) (f : SU2 → ℝ) (C : SU2) : ℝ :=
  Real.exp (t*halfTrace C/2)*
    ∫ V, Real.exp (t*halfTrace (C*V)/2)*f (C*V) ∂walkLaw β n

def vacuumCandidate (a r t : ℝ) (C : SU2) : ℝ :=
  Real.exp (t*halfTrace C/2)*trial (linearCoefficient a) (quadraticTrialCoefficient a r) t (halfTrace C)

theorem vacuumCandidate_positive (a r t : ℝ)
    (hsmall : |linearCoefficient a| * |t|+|quadraticTrialCoefficient a r| * |t|^2 ≤ 1/2)
    (C : SU2) : 0 < vacuumCandidate a r t C := by
  exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le (by norm_num)
    (trial_positive _ _ _ _ (halfTrace_bound C) hsmall))

/-- The finite-coupling four-increment vacuum upper certificate has no spectral
isolation or existence premise. Smallness is explicit and is not a physical
homogeneous four-dimensional coupling regime. -/
theorem symmetricWalk_four_supersolution (β t : ℝ) (ht : |t| ≤ 1)
    (hsmall : |linearCoefficient (coefficient β^4)| * |t|+
      |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2)
    (C : SU2) :
    symmetricWalk β 4 t (vacuumCandidate (coefficient β^4) (quadraticCoefficient β^4) t) C ≤
      (1+vacuumSecond (coefficient β^4)*t^2+
        2*eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4)*|t|^3)*
      vacuumCandidate (coefficient β^4) (quadraticCoefficient β^4) t C := by
  have he (D : SU2) : Real.exp (t*halfTrace D/2)*
      vacuumCandidate (coefficient β^4) (quadraticCoefficient β^4) t D =
      Real.exp (t*halfTrace D)*trial (linearCoefficient (coefficient β^4))
        (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (halfTrace D) := by
    unfold vacuumCandidate
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  unfold symmetricWalk
  simp_rw [he]
  have h := weightedWalk_trial_supersolution β 4 t (kinetic_power_ne_one β 4 (by decide)).1
    (kinetic_power_ne_one β 4 (by decide)).2 ht hsmall C
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (t*halfTrace C/2)).le
  simpa only [weightedWalk,vacuumCandidate,mul_left_comm] using hm

end OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

namespace OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem exponential_trial_domination (A B t M : ℝ) (ht : |t| ≤ 1)
    (Y f : Ω → ℝ) (hY : Measurable Y) (hf : Measurable f)
    (hb : ∀ ω, |Y ω| ≤ 1) (hdom : ∀ ω, |f ω| ≤ M*trial A B t (Y ω)) :
    Integrable (fun ω => Real.exp (t*Y ω)*f ω) μ ∧
      |∫ ω, Real.exp (t*Y ω)*f ω ∂μ| ≤
        M*(∫ ω, Real.exp (t*Y ω)*trial A B t (Y ω) ∂μ) := by
  have hi := (exponential_trial_integrable μ A B t ht Y hY hb).const_mul M
  have hn : ∀ᵐ ω ∂μ, ‖Real.exp (t*Y ω)*f ω‖ ≤
      M*(Real.exp (t*Y ω)*trial A B t (Y ω)) := by
    filter_upwards with ω
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    nlinarith [mul_le_mul_of_nonneg_left (hdom ω) (Real.exp_pos (t*Y ω)).le]
  refine ⟨Integrable.mono' hi (((measurable_const.mul hY).exp.mul hf).aestronglyMeasurable) hn,?_⟩
  have h := norm_integral_le_of_norm_le hi hn
  simpa only [Real.norm_eq_abs,integral_const_mul] using h

/-- An actual weighted-supremum domination estimate with its L1 domain proved.
It is not a stationary-gap estimate or a claim of full-lattice realization. -/
theorem weightedWalk_four_domination (β t M : ℝ) (ht : |t| ≤ 1) (hM : 0 ≤ M)
    (hsmall : |linearCoefficient (coefficient β^4)| * |t|+
      |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2)
    (f : SU2 → ℝ) (hf : Measurable f)
    (hdom : ∀ D, |f D| ≤ M*trial (linearCoefficient (coefficient β^4))
      (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (halfTrace D))
    (C : SU2) :
    Integrable (fun V => Real.exp (t*halfTrace (C*V))*f (C*V)) (walkLaw β 4) ∧
    |weightedWalk β 4 t f C| ≤
      M*(1+vacuumSecond (coefficient β^4)*t^2+
        2*eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4)*|t|^3)*
        trial (linearCoefficient (coefficient β^4))
          (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (halfTrace C) := by
  letI := walkLaw_probability β 4
  have h := exponential_trial_domination (walkLaw β 4) _ _ t M ht
    (fun V => halfTrace (C*V)) (fun V => f (C*V))
    (halfTrace_measurable.comp (measurable_const_mul C)) (hf.comp (measurable_const_mul C))
    (fun V => halfTrace_bound (C*V)) (fun V => hdom (C*V))
  refine ⟨h.1,?_⟩
  have hs := weightedWalk_trial_supersolution β 4 t (kinetic_power_ne_one β 4 (by decide)).1
    (kinetic_power_ne_one β 4 (by decide)).2 ht hsmall C
  have hm := mul_le_mul_of_nonneg_left hs hM
  exact h.2.trans (by simpa only [weightedWalk,mul_assoc] using hm)

end OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate

namespace OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open Filter
open scoped Topology

/-- This sufficient trial window cannot certify any fixed nonzero spatial
amplitude uniformly at large Wilson parameter. This is not a no-gap theorem. -/
theorem no_uniform_fixed_trial_window (t : ℝ) (ht : t ≠ 0) :
    ¬ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      |linearCoefficient (coefficient β^4)| * |t|+
        |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2 := by
  rintro ⟨β₀,hsmall⟩
  have hlim := fixed_word_factor_tendsto_one 4
  have hpos : ∀ᶠ β : ℝ in atTop, (1/2:ℝ) < coefficient β^4 :=
    (tendsto_order.mp hlim).1 _ (by norm_num)
  have he : ∀ᶠ β : ℝ in atTop, (2*|t|+1)*coefficient β^4 ≤ 1 := by
    filter_upwards [hpos,eventually_ge_atTop β₀] with β hp hb
    have ha0 : 0 < coefficient β^4 := lt_trans (by norm_num) hp
    have ha1 : coefficient β^4 < 1 := by
      have h := pow_lt_one₀ (abs_nonneg (coefficient β)) (coefficient_abs_lt_one β) (by decide : (4:ℕ) ≠ 0)
      rw [← abs_pow] at h
      exact (le_abs_self _).trans_lt h
    have hw := necessary_trial_window (coefficient β^4)
      (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t ha0 ha1 (hsmall β hb)
    have hm := (le_div_iff₀ (mul_pos (by norm_num) ha0)).mp hw
    nlinarith
  have hl : Tendsto (fun β : ℝ => (2*|t|+1)*coefficient β^4) atTop (𝓝 (2*|t|+1)) := by
    simpa only [mul_one] using hlim.const_mul (2*|t|+1)
  have hh := le_of_tendsto hl he
  have htpos := abs_pos.mpr ht
  linarith

end OperatorDerivativeRewrite.Foundation.SU2WilsonGroundCertificate
