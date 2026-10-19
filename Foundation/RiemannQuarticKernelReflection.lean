import Foundation.RiemannQuarticPairedSaddle
import Foundation.RiemannThetaModularity
import Foundation.RiemannQuarticSaddleNeighborhood
import Mathlib.Analysis.Analytic.IsolatedZeros
/-! Arithmetic kernel reflection and exact paired vertical-endpoint cancellation.
Complex evenness is proved only in the natural strip |Imw|<pi/8.
The paired horizontal flow formula uses the verified contour range |h|<=1/16. -/
noncomputable section
open Set Metric Complex Filter
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticKernelReflection
open RiemannThetaDifferentiation RiemannThetaModularity RiemannQuarticKernel RiemannThetaComplexKernel

theorem psiPrime_reflection (u : ℝ) : psiPrime u+psiPrime (-u)=(-Real.exp (-u)-Real.exp u)/2 := by
  have hl := (psi_hasDerivAt u).sub ((psi_hasDerivAt (-u)).comp u (hasDerivAt_neg u))
  have hr := ((((hasDerivAt_neg u).exp).sub (Real.hasDerivAt_exp u))).div_const 2
  have he : (fun x : ℝ => psi x-psi (-x))=(fun x => (Real.exp (-x)-Real.exp x)/2) := funext psi_reflection
  change HasDerivAt (fun x : ℝ => psi x-psi (-x)) _ u at hl
  rw [he] at hl
  have h := hl.unique hr
  linarith

theorem psiSecond_reflection (u : ℝ) : psiSecond u-psiSecond (-u)=(Real.exp (-u)-Real.exp u)/2 := by
  have hl := (psiPrime_hasDerivAt u).add ((psiPrime_hasDerivAt (-u)).comp u (hasDerivAt_neg u))
  have hr := (((((hasDerivAt_neg u).exp).neg).sub (Real.hasDerivAt_exp u))).div_const 2
  have he : (fun x : ℝ => psiPrime x+psiPrime (-x))=(fun x => (-Real.exp (-x)-Real.exp x)/2) := funext psiPrime_reflection
  change HasDerivAt (fun x : ℝ => psiPrime x+psiPrime (-x)) _ u at hl
  rw [he] at hl
  have h := hl.unique hr
  linarith

theorem kernel_even (u : ℝ) : kernel (-u)=kernel u := by
  rw [kernel_differential_identity,kernel_differential_identity]
  have h := psi_reflection u
  have h2 := psiSecond_reflection u
  linarith

theorem moment_conj (k : ℕ) (v : ℂ) : moment k (conj v)=conj (moment k v) := by
  rw [moment,moment,Complex.conj_tsum]
  apply tsum_congr
  intro n
  simp only [RiemannQuarticSaddleTheta.complexThetaTerm,map_mul,← Complex.exp_conj,Complex.conj_ofReal,map_pow,map_natCast]

theorem kernel_conj (w : ℂ) : kernelComplex (conj w)=conj (kernelComplex w) := by
  simp only [kernelComplex,map_sub,map_mul,map_pow,map_ofNat,Complex.conj_ofReal,← Complex.exp_conj,← moment_conj]

def strip : Set ℂ := {w | w.im ∈ Ioo (-Real.pi/8) (Real.pi/8)}

theorem strip_domain (w : ℂ) (hw : w ∈ strip) : 0 < (Complex.exp (4*w)).re := by
  have hh : (4*w).im ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    norm_num [Complex.mul_im]
    change -Real.pi/8 < w.im ∧ w.im < Real.pi/8 at hw
    constructor <;> linarith [hw.1,hw.2]
  rw [Complex.exp_re]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo hh)

theorem strip_neg (w : ℂ) (hw : w ∈ strip) : -w ∈ strip := by
  change -Real.pi/8 < w.im ∧ w.im < Real.pi/8 at hw
  change -Real.pi/8 < (-w).im ∧ (-w).im < Real.pi/8
  simp only [Complex.neg_im]
  constructor <;> linarith [hw.1,hw.2]

theorem kernelComplex_even (w : ℂ) (hw : w ∈ strip) : kernelComplex (-w)=kernelComplex w := by
  have hf : AnalyticOnNhd ℂ (fun z => kernelComplex (-z)) strip := by
    intro z hz
    exact (RiemannThetaComplexKernel.kernelComplex_analyticAt (-z) (strip_domain (-z) (strip_neg z hz))).comp analyticAt_id.neg
  have hg : AnalyticOnNhd ℂ kernelComplex strip := by
    intro z hz
    exact RiemannThetaComplexKernel.kernelComplex_analyticAt z (strip_domain z hz)
  have hconv : Convex ℝ strip := (convex_Ioo (-Real.pi/8) (Real.pi/8)).linear_preimage Complex.imCLM.toLinearMap
  have h0 : (0 : ℂ) ∈ strip := by change -Real.pi/8 < (0 : ℂ).im ∧ (0 : ℂ).im < Real.pi/8; simp only [Complex.zero_im]; constructor <;> linarith [Real.pi_pos]
  have hseq : Tendsto (fun n : ℕ => ((1/((n : ℝ)+1) : ℝ) : ℂ)) atTop (nhds 0) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (nhds 0))
    simpa only [Function.comp_def,Complex.ofReal_zero] using h
  have hcl : (0 : ℂ) ∈ closure ({z | kernelComplex (-z)=kernelComplex z} \ {0}) := by
    apply mem_closure_of_tendsto hseq
    filter_upwards with n
    refine ⟨?_,?_⟩
    · change kernelComplex (-((1/((n : ℝ)+1) : ℝ) : ℂ))=kernelComplex (((1/((n : ℝ)+1) : ℝ) : ℂ))
      rw [← Complex.ofReal_neg,kernelComplex_real,kernelComplex_real,kernel_even]
    · change (((1/((n : ℝ)+1) : ℝ) : ℂ)) ≠ 0
      exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ)<1/((n : ℝ)+1)))
  exact hf.eqOn_of_preconnected_of_mem_closure hg hconv.isPreconnected h0 hcl hw

open RiemannQuarticFrequencyBranch RiemannQuarticSignedContour

theorem weight_neg_neg (t : ℝ) (z w : ℂ) (hw : w ∈ strip) :
    saddleWeight t (-z) (-w)=saddleWeight t z w := by
  unfold saddleWeight
  rw [kernelComplex_even w hw]
  congr 2 <;> ring

theorem vertical_pair_cancel (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| ≤ 1/16) :
    (∫ y : ℝ in 0..(-h), saddleWeight t (-z) ((y : ℂ)*Complex.I))=
      -(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)) := by
  rw [intervalIntegral.integral_symm]
  have hc := intervalIntegral.integral_comp_neg (a := 0) (b := h)
    (fun y : ℝ => saddleWeight t (-z) ((y : ℂ)*Complex.I))
  simp only [neg_zero] at hc
  rw [← hc]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  have hyabs := (vertical_abs_le h y hy).trans hh
  have hw : (y : ℂ)*Complex.I ∈ strip := by
    change -Real.pi/8 < ((y : ℂ)*Complex.I).im ∧ ((y : ℂ)*Complex.I).im < Real.pi/8
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,Complex.ofReal_im,Complex.I_re,mul_zero,add_zero]
    constructor <;> linarith [(abs_le.mp hyabs).1,(abs_le.mp hyabs).2,Real.pi_gt_three]
  have he : ((-y : ℝ) : ℂ)*Complex.I= -((y : ℂ)*Complex.I) := by push_cast; ring
  change saddleWeight t (-z) (((-y : ℝ) : ℂ)*Complex.I)=saddleWeight t z ((y : ℂ)*Complex.I)
  rw [he]
  exact weight_neg_neg t z _ hw

theorem flow_eq_paired_horizontal (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| ≤ 1/16) :
    RiemannQuarticFlow.flow t z=
      ((∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
        (∫ x : ℝ in Ioi 0, saddleWeight t (-z) ((x : ℂ)-(h : ℂ)*Complex.I)))/2 := by
  rw [RiemannQuarticFlow.flow,RiemannQuarticPairedSaddle.jet_zero_eq_halfline,
    RiemannQuarticPairedSaddle.jet_zero_eq_halfline,
    halfline_contour_shift_signed t z h hh,halfline_contour_shift_signed t (-z) (-h) (by simpa using hh),
    vertical_pair_cancel t z h hh]
  simp only [Complex.ofReal_neg,neg_mul,add_neg_cancel_right,← sub_eq_add_neg]
  ring


end OperatorDerivativeRewrite.Foundation.RiemannQuarticKernelReflection
