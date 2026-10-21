import Foundation.RiemannRealOrderFractionalDensity
import Foundation.RiemannRealOrderCubicEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Actual fractional power/exponential derivatives through order four.
Power identities are used on the principal slit plane, with all derivative
claims for the arithmetic density retaining the kernel's analytic domain. -/
noncomputable section
open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalJets
open RiemannThetaComplexKernel

def falling (s : ℝ) (n : ℕ) : ℝ := (Finset.range n).prod (fun j => s-(j : ℝ))
def powerJet (s : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (falling s n : ℂ)*z^((s-(n : ℝ) : ℝ) : ℂ)
def phaseJet (a t : ℝ) (n : ℕ) (z : ℂ) : ℂ := (t : ℂ)*powerJet (2*a) n z
def exponential (a t : ℝ) (z : ℂ) : ℂ := Complex.exp ((t : ℂ)*z^((2*a : ℝ) : ℂ))

def bell (a t : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  match n with
  | 0 => 1
  | 1 => phaseJet a t 1 z
  | 2 => phaseJet a t 2 z+(phaseJet a t 1 z)^2
  | 3 => phaseJet a t 3 z+3*phaseJet a t 1 z*phaseJet a t 2 z+(phaseJet a t 1 z)^3
  | 4 => phaseJet a t 4 z+4*phaseJet a t 1 z*phaseJet a t 3 z+
      3*(phaseJet a t 2 z)^2+6*(phaseJet a t 1 z)^2*phaseJet a t 2 z+(phaseJet a t 1 z)^4
  | _ => 0

def exponentialJet (a t : ℝ) (n : ℕ) (z : ℂ) : ℂ := bell a t n z*exponential a t z

theorem falling_succ (s : ℝ) (n : ℕ) : falling s (n+1)=falling s n*(s-(n : ℝ)) :=
  Finset.prod_range_succ _ _

theorem powerJet_zero (s : ℝ) (z : ℂ) : powerJet s 0 z=z^(s : ℂ) := by
  simp [powerJet,falling]

theorem powerJet_hasDerivAt (s : ℝ) (n : ℕ) (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (powerJet s n) (powerJet s (n+1) z) z := by
  have h := ((hasDerivAt_id z).cpow_const (c := ((s-(n : ℝ) : ℝ) : ℂ)) hz).const_mul
    (falling s n : ℂ)
  have he : (((s-((n+1 : ℕ) : ℝ) : ℝ) : ℂ)) = ((s-(n : ℝ) : ℝ) : ℂ)-1 := by
    push_cast
    ring
  convert h using 1
  · funext w
    simp [powerJet,id_eq]
  · rw [powerJet,falling_succ,Complex.ofReal_mul,he]
    simp only [id_eq,mul_one]
    ring

theorem phaseJet_hasDerivAt (a t : ℝ) (n : ℕ) (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (phaseJet a t n) (phaseJet a t (n+1) z) z :=
  (powerJet_hasDerivAt (2*a) n z hz).const_mul (t : ℂ)

theorem phaseJet_real (a t u : ℝ) (n : ℕ) (hu : 0 ≤ u) :
    phaseJet a t n (u : ℂ) = (t*falling (2*a) n*u^(2*a-(n : ℝ)) : ℝ) := by
  simp only [phaseJet,powerJet,Complex.ofReal_mul]
  rw [Complex.ofReal_cpow hu]
  ring

theorem exponential_analyticAt (a t : ℝ) (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (exponential a t) z :=
  (analyticAt_const.mul (analyticAt_id.cpow analyticAt_const hz)).cexp

theorem exponential_hasDerivAt (a t : ℝ) (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (exponential a t) (phaseJet a t 1 z*exponential a t z) z := by
  have h := (phaseJet_hasDerivAt a t 0 z hz).cexp
  convert h using 1
  · funext w
    simp [phaseJet,powerJet_zero,exponential]
  · simp only [phaseJet,powerJet_zero,exponential]
    ring

theorem exponentialJet_hasDerivAt (a t : ℝ) (n : ℕ) (hn : n ≤ 3)
    (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (exponentialJet a t n) (exponentialJet a t (n+1) z) z := by
  have hp (j : ℕ) := phaseJet_hasDerivAt a t j z hz
  have he := exponential_hasDerivAt a t z hz
  change HasDerivAt (fun w => bell a t n w*exponential a t w)
    (bell a t (n+1) z*exponential a t z) z
  interval_cases n
  · simpa [exponentialJet,bell] using he
  · convert (hp 1).mul he using 1
    · funext w
      simp only [exponentialJet,bell,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,mul_add,add_mul] <;> ring
    · simp only [exponentialJet,bell,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,mul_add,add_mul] <;> ring
  · convert ((hp 2).add ((hp 1).pow 2)).mul he using 1
    · funext w
      simp only [exponentialJet,bell,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,mul_add,add_mul] <;> ring
    · simp only [exponentialJet,bell,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,mul_add,add_mul] <;> ring
  · convert (((hp 3).add (((hp 1).const_mul 3).mul (hp 2))).add ((hp 1).pow 3)).mul he using 1
    · funext w
      simp only [exponentialJet,bell,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,mul_add,add_mul] <;> ring
    · simp only [exponentialJet,bell,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,mul_add,add_mul] <;> ring

theorem exponential_iteratedDeriv : ∀ n : ℕ, n ≤ 4 → ∀ z : ℂ, z ∈ Complex.slitPlane →
    iteratedDeriv n (exponential a t) z=exponentialJet a t n z := by
  intro n
  induction n with
  | zero => intro _ z _; simp [exponentialJet,bell]
  | succ n ih =>
    intro hn z hz
    have hlocal : iteratedDeriv n (exponential a t) =ᶠ[𝓝 z] exponentialJet a t n := by
      filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih (by omega) w hw
    rw [iteratedDeriv_succ,hlocal.deriv_eq]
    exact (exponentialJet_hasDerivAt a t n (by omega) z hz).deriv

theorem density_third_derivative (a t : ℝ) (z : ℂ) (hz : z ∈ Complex.slitPlane)
    (hK : 0 < (Complex.exp (4*z)).re) :
    iteratedDeriv 3 (RiemannRealOrderFractionalDensity.density a t) z =
      exponential a t z*(iteratedDeriv 3 kernelComplex z+
        3*phaseJet a t 1 z*iteratedDeriv 2 kernelComplex z+
        3*(phaseJet a t 2 z+(phaseJet a t 1 z)^2)*iteratedDeriv 1 kernelComplex z+
        (phaseJet a t 3 z+3*phaseJet a t 1 z*phaseJet a t 2 z+
          (phaseJet a t 1 z)^3)*kernelComplex z) := by
  have h := iteratedDeriv_fun_mul
    (n := 3) (x := z) (exponential_analyticAt a t z hz).contDiffAt
    (kernelComplex_analyticAt z hK).contDiffAt
  change iteratedDeriv 3 (fun w => exponential a t w*kernelComplex w) z=_
  rw [h]
  norm_num [Finset.sum_range_succ,exponential_iteratedDeriv, hz,exponentialJet,bell,Nat.choose] <;> ring

theorem density_fourth_derivative (a t : ℝ) (z : ℂ) (hz : z ∈ Complex.slitPlane)
    (hK : 0 < (Complex.exp (4*z)).re) :
    iteratedDeriv 4 (RiemannRealOrderFractionalDensity.density a t) z =
      exponential a t z*(iteratedDeriv 4 kernelComplex z+
        4*phaseJet a t 1 z*iteratedDeriv 3 kernelComplex z+
        6*(phaseJet a t 2 z+(phaseJet a t 1 z)^2)*iteratedDeriv 2 kernelComplex z+
        4*(phaseJet a t 3 z+3*phaseJet a t 1 z*phaseJet a t 2 z+
          (phaseJet a t 1 z)^3)*iteratedDeriv 1 kernelComplex z+
        (phaseJet a t 4 z+4*phaseJet a t 1 z*phaseJet a t 3 z+
          3*(phaseJet a t 2 z)^2+6*(phaseJet a t 1 z)^2*phaseJet a t 2 z+
          (phaseJet a t 1 z)^4)*kernelComplex z) := by
  have h := iteratedDeriv_fun_mul
    (n := 4) (x := z) (exponential_analyticAt a t z hz).contDiffAt
    (kernelComplex_analyticAt z hK).contDiffAt
  change iteratedDeriv 4 (fun w => exponential a t w*kernelComplex w) z=_
  rw [h]
  norm_num [Finset.sum_range_succ,exponential_iteratedDeriv, hz,exponentialJet,bell,Nat.choose] <;> ring

def endpointDifference (a t u : ℝ) : ℂ :=
  (Real.exp (t*u^(2*a)) : ℂ)*kernelComplex (u : ℂ)-kernelComplex 0*(Real.exp (-u) : ℂ)

theorem endpointDifference_actual (a t u : ℝ) (hu : 0 ≤ u) :
    endpointDifference a t u = RiemannRealOrderFractionalDensity.density a t (u : ℂ)-
      kernelComplex 0*(Real.exp (-u) : ℂ) := by
  simp only [endpointDifference,RiemannRealOrderFractionalDensity.density]
  rw [← Complex.ofReal_cpow hu,← Complex.ofReal_mul,← Complex.ofReal_exp]

theorem endpointDifference_zero (a t : ℝ) (ha : 0 < 2*a) : endpointDifference a t 0=0 := by
  simp [endpointDifference,Real.zero_rpow ha.ne']

theorem endpointDifference_hasDerivAt (a t : ℝ) (ha : 1 < 2*a) :
    HasDerivAt (endpointDifference a t) (kernelComplex 0) (0 : ℝ) := by
  have hpow : HasDerivAt (fun u : ℝ => u^(2*a)) 0 (0 : ℝ) := by
    have h := Real.hasDerivAt_rpow_const (x := 0) (p := 2*a) (Or.inr ha.le)
    simpa [Real.zero_rpow (by linarith : 2*a-1 ≠ 0)] using h
  have hE : HasDerivAt (fun u : ℝ => Real.exp (t*u^(2*a))) 0 (0 : ℝ) := by
    simpa using (hpow.const_mul t).exp
  have hodd : deriv kernelComplex 0=0 := by
    simpa using RiemannRealOrderCubicEndpoint.odd_kernel_derivative_zero 1 (by decide)
  have hK : HasDerivAt (fun u : ℝ => kernelComplex (u : ℂ)) 0 (0 : ℝ) := by
    have h := (kernelComplex_analyticAt 0 (by simp)).differentiableAt.hasDerivAt
    simpa only [hodd] using (h.comp_ofReal (z := (0 : ℝ)))
  have h := ((hE.ofReal_comp).mul hK).sub
    ((((hasDerivAt_id (0 : ℝ)).neg).exp).ofReal_comp.const_mul (kernelComplex 0))
  convert h using 1
  · rfl
  · simp [Real.zero_rpow (by linarith : 2*a ≠ 0)]

theorem endpointDifference_isBigO (a t : ℝ) (ha : 1 < 2*a) :
    endpointDifference a t =O[𝓝 (0 : ℝ)] (fun u : ℝ => u) := by
  have h := (endpointDifference_hasDerivAt a t ha).isBigO_sub
  simpa only [endpointDifference_zero a t (by linarith),sub_zero] using h

theorem endpointDifference_continuousOn (a t : ℝ) :
    ContinuousOn (endpointDifference a t) (Ioi 0) := by
  have hd : ContinuousOn (fun u : ℝ => RiemannRealOrderFractionalDensity.density a t (u : ℂ))
      (Ioi 0) := by
    simpa only [iteratedDeriv_zero] using
      RiemannRealOrderFractionalDensity.density_iteratedDeriv_continuousOn 0 a t
  have hc : ContinuousOn (fun u : ℝ => RiemannRealOrderFractionalDensity.density a t (u : ℂ)-
      kernelComplex 0*(Real.exp (-u) : ℂ)) (Ioi 0) :=
    hd.sub (continuousOn_const.mul (by fun_prop))
  apply hc.congr
  intro u hu
  exact endpointDifference_actual a t u hu.le

theorem critical_endpoint_term_integrable (a t : ℝ) (ha : 1 < a) :
    ∃ δ : ℝ, 0 < δ ∧ IntegrableOn
      (fun u : ℝ => (u^(2*a-4) : ℝ)*endpointDifference a t u) (Ioo 0 δ) := by
  obtain ⟨C,hC,hB⟩ := isBigO_iff'.mp (endpointDifference_isBigO a t (by linarith))
  obtain ⟨δ,hδ,hδB⟩ := Metric.mem_nhds_iff.mp hB
  refine ⟨δ,hδ,?_⟩
  have hm : IntegrableOn (fun u : ℝ => C*u^(2*a-3)) (Ioo 0 δ) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mpr (by linarith)).const_mul C
  have hp : ContinuousOn (fun u : ℝ => ((u^(2*a-4) : ℝ) : ℂ)) (Ioo 0 δ) := by
    intro u hu
    exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_id.rpow_const (Or.inl hu.1.ne'))).continuousWithinAt
  have hw := (endpointDifference_continuousOn a t).mono
    (show Ioo (0 : ℝ) δ ⊆ Ioi 0 from fun _ hu => hu.1)
  apply hm.mono' ((hp.mul hw).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hb : ‖endpointDifference a t u‖ ≤ C*u := by
    have hball : u ∈ Metric.ball (0 : ℝ) δ := by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hu.1] using hu.2
    have h := hδB hball
    change ‖endpointDifference a t u‖ ≤ C*‖u‖ at h
    simpa only [Real.norm_eq_abs,abs_of_pos hu.1] using h
  change ‖((u^(2*a-4) : ℝ) : ℂ)*endpointDifference a t u‖ ≤ C*u^(2*a-3)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hu.1 _)]
  calc
    _ ≤ u^(2*a-4)*(C*u) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hu.1.le _)
    _ = C*(u^(2*a-4)*u) := by ring
    _ = C*u^(2*a-3) := by
      congr 1
      calc
        _ = u^((2*a-4)+1) := by rw [Real.rpow_add hu.1,Real.rpow_one]
        _ = _ := by congr 1; ring

def regularThird (a t : ℝ) (z : ℂ) : ℂ :=
  exponential a t z*(iteratedDeriv 3 kernelComplex z+
    3*phaseJet a t 1 z*iteratedDeriv 2 kernelComplex z+
    3*(phaseJet a t 2 z+(phaseJet a t 1 z)^2)*iteratedDeriv 1 kernelComplex z+
    (3*phaseJet a t 1 z*phaseJet a t 2 z+(phaseJet a t 1 z)^3)*kernelComplex z)

def regularFourth (a t : ℝ) (z : ℂ) : ℂ :=
  exponential a t z*(iteratedDeriv 4 kernelComplex z+
    4*phaseJet a t 1 z*iteratedDeriv 3 kernelComplex z+
    6*(phaseJet a t 2 z+(phaseJet a t 1 z)^2)*iteratedDeriv 2 kernelComplex z+
    4*(phaseJet a t 3 z+3*phaseJet a t 1 z*phaseJet a t 2 z+
      (phaseJet a t 1 z)^3)*iteratedDeriv 1 kernelComplex z+
    (4*phaseJet a t 1 z*phaseJet a t 3 z+3*(phaseJet a t 2 z)^2+
      6*(phaseJet a t 1 z)^2*phaseJet a t 2 z+(phaseJet a t 1 z)^4)*kernelComplex z)

def cutoff (a t u : ℝ) : ℂ := phaseJet a t 3 (u : ℂ)*kernelComplex 0*(Real.exp (-u) : ℂ)
def remainder (a t u : ℝ) : ℂ :=
  iteratedDeriv 3 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)-cutoff a t u

theorem cutoff_hasDerivAt (a t u : ℝ) (hu : 0 < u) :
    HasDerivAt (cutoff a t)
      ((phaseJet a t 4 (u : ℂ)-phaseJet a t 3 (u : ℂ))*kernelComplex 0*(Real.exp (-u) : ℂ)) u := by
  have hp := (phaseJet_hasDerivAt a t 3 (u : ℂ)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hu))).comp_ofReal
  have he := (((hasDerivAt_id u).neg).exp).ofReal_comp
  convert (hp.mul_const (kernelComplex 0)).mul he using 1
  · rfl
  · simp only [Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one,Pi.neg_apply,id_eq]
    ring

theorem remainder_hasDerivAt (a t u : ℝ) (hu : 0 < u) :
    HasDerivAt (remainder a t)
      (iteratedDeriv 4 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)-
        (phaseJet a t 4 (u : ℂ)-phaseJet a t 3 (u : ℂ))*kernelComplex 0*(Real.exp (-u) : ℂ)) u :=
  (RiemannRealOrderFractionalDensity.density_profile_hasDerivAt 3 a t u hu).sub
    (cutoff_hasDerivAt a t u hu)

theorem remainder_eq (a t u : ℝ) (hu : 0 < u) :
    remainder a t u = phaseJet a t 3 (u : ℂ)*endpointDifference a t u+
      regularThird a t (u : ℂ) := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)
  rw [remainder,density_third_derivative a t (u : ℂ)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hu)) he,endpointDifference_actual a t u hu.le]
  unfold cutoff regularThird RiemannRealOrderFractionalDensity.density exponential
  ring

theorem remainder_derivative_eq (a t u : ℝ) (hu : 0 < u) :
    deriv (remainder a t) u = phaseJet a t 4 (u : ℂ)*endpointDifference a t u+
      cutoff a t u+regularFourth a t (u : ℂ) := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)
  rw [(remainder_hasDerivAt a t u hu).deriv,density_fourth_derivative a t (u : ℂ)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hu)) he,endpointDifference_actual a t u hu.le]
  unfold cutoff regularFourth RiemannRealOrderFractionalDensity.density exponential
  ring

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalJets
