import Foundation.RiemannRealOrderFractionalRemainder

/-! Actual fifth derivatives on the principal-power and arithmetic-kernel domains.
The older finite jet definition and its order-four boundary are unchanged. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFifthDerivative
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets

def fifthBell (a t : ℝ) (z : ℂ) : ℂ :=
  phaseJet a t 5 z+5*phaseJet a t 1 z*phaseJet a t 4 z+
    10*phaseJet a t 2 z*phaseJet a t 3 z+10*(phaseJet a t 1 z)^2*phaseJet a t 3 z+
    15*phaseJet a t 1 z*(phaseJet a t 2 z)^2+
    10*(phaseJet a t 1 z)^3*phaseJet a t 2 z+(phaseJet a t 1 z)^5

def fifthExponential (a t : ℝ) (z : ℂ) : ℂ := fifthBell a t z*exponential a t z

theorem fourth_exponential_hasDerivAt (a t : ℝ) (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (exponentialJet a t 4) (fifthExponential a t z) z := by
  have hp (n : ℕ) := phaseJet_hasDerivAt a t n z hz
  have hb := ((((hp 4).add (((hp 1).mul (hp 3)).const_mul 4)).add
    (((hp 2).pow 2).const_mul 3)).add
    ((((hp 1).pow 2).mul (hp 2)).const_mul 6)).add (((hp 1).pow 4))
  have h := hb.mul (exponential_hasDerivAt a t z hz)
  convert h using 1
  · funext w
    simp only [exponentialJet,bell,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
    ring
  · simp only [fifthExponential,fifthBell,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
    ring

theorem exponential_fifth_derivative (a t : ℝ) (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv 5 (exponential a t) z=fifthExponential a t z := by
  have hlocal : iteratedDeriv 4 (exponential a t) =ᶠ[𝓝 z] exponentialJet a t 4 := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
    exact exponential_iteratedDeriv 4 (by omega) w hw
  rw [show 5=4+1 by rfl,iteratedDeriv_succ,hlocal.deriv_eq]
  exact (fourth_exponential_hasDerivAt a t z hz).deriv

theorem density_fifth_derivative (a t : ℝ) (z : ℂ) (hz : z ∈ Complex.slitPlane)
    (hK : 0 < (Complex.exp (4*z)).re) :
    iteratedDeriv 5 (RiemannRealOrderFractionalDensity.density a t) z =
      exponential a t z*(iteratedDeriv 5 kernelComplex z+
        5*phaseJet a t 1 z*iteratedDeriv 4 kernelComplex z+
        10*(phaseJet a t 2 z+(phaseJet a t 1 z)^2)*iteratedDeriv 3 kernelComplex z+
        10*(phaseJet a t 3 z+3*phaseJet a t 1 z*phaseJet a t 2 z+
          (phaseJet a t 1 z)^3)*iteratedDeriv 2 kernelComplex z+
        5*(phaseJet a t 4 z+4*phaseJet a t 1 z*phaseJet a t 3 z+
          3*(phaseJet a t 2 z)^2+6*(phaseJet a t 1 z)^2*phaseJet a t 2 z+
          (phaseJet a t 1 z)^4)*iteratedDeriv 1 kernelComplex z+
        fifthBell a t z*kernelComplex z) := by
  have h := iteratedDeriv_fun_mul (n := 5) (x := z)
    (exponential_analyticAt a t z hz).contDiffAt (kernelComplex_analyticAt z hK).contDiffAt
  change iteratedDeriv 5 (fun w => exponential a t w*kernelComplex w) z=_
  rw [h]
  norm_num [Finset.sum_range_succ,exponential_fifth_derivative,
    exponential_iteratedDeriv,hz,exponentialJet,bell,fifthExponential,Nat.choose] <;> ring

def regularFifth (a t : ℝ) (z : ℂ) : ℂ :=
  exponential a t z*(iteratedDeriv 5 kernelComplex z+
    5*phaseJet a t 1 z*iteratedDeriv 4 kernelComplex z+
    10*(phaseJet a t 2 z+(phaseJet a t 1 z)^2)*iteratedDeriv 3 kernelComplex z+
    10*(phaseJet a t 3 z+3*phaseJet a t 1 z*phaseJet a t 2 z+
      (phaseJet a t 1 z)^3)*iteratedDeriv 2 kernelComplex z+
    5*(phaseJet a t 4 z+4*phaseJet a t 1 z*phaseJet a t 3 z+
      3*(phaseJet a t 2 z)^2+6*(phaseJet a t 1 z)^2*phaseJet a t 2 z+
      (phaseJet a t 1 z)^4)*iteratedDeriv 1 kernelComplex z+
    (5*phaseJet a t 1 z*phaseJet a t 4 z+
      10*phaseJet a t 2 z*phaseJet a t 3 z+10*(phaseJet a t 1 z)^2*phaseJet a t 3 z+
      15*phaseJet a t 1 z*(phaseJet a t 2 z)^2+
      10*(phaseJet a t 1 z)^3*phaseJet a t 2 z+(phaseJet a t 1 z)^5)*kernelComplex z)

def fourthCutoff (a t u : ℝ) : ℂ :=
  phaseJet a t 4 (u : ℂ)*kernelComplex 0*(Real.exp (-u) : ℂ)

def fourthRemainder (a t u : ℝ) : ℂ :=
  iteratedDeriv 4 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)-fourthCutoff a t u

theorem fourthCutoff_hasDerivAt (a t u : ℝ) (hu : 0 < u) :
    HasDerivAt (fourthCutoff a t)
      ((phaseJet a t 5 (u : ℂ)-phaseJet a t 4 (u : ℂ))*kernelComplex 0*(Real.exp (-u) : ℂ)) u := by
  have hp := (phaseJet_hasDerivAt a t 4 (u : ℂ)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hu))).comp_ofReal
  have he := (((hasDerivAt_id u).neg).exp).ofReal_comp
  convert (hp.mul_const (kernelComplex 0)).mul he using 1
  · rfl
  · simp only [Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one,Pi.neg_apply,id_eq]
    ring

theorem fourthRemainder_hasDerivAt (a t u : ℝ) (hu : 0 < u) :
    HasDerivAt (fourthRemainder a t)
      (iteratedDeriv 5 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)-
        (phaseJet a t 5 (u : ℂ)-phaseJet a t 4 (u : ℂ))*kernelComplex 0*(Real.exp (-u) : ℂ)) u :=
  (RiemannRealOrderFractionalDensity.density_profile_hasDerivAt 4 a t u hu).sub
    (fourthCutoff_hasDerivAt a t u hu)

theorem fourthRemainder_eq (a t u : ℝ) (hu : 0 < u) :
    fourthRemainder a t u = phaseJet a t 4 (u : ℂ)*endpointDifference a t u+
      regularFourth a t (u : ℂ) := by
  have hK : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)
  rw [fourthRemainder,density_fourth_derivative a t (u : ℂ)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hu)) hK,endpointDifference_actual a t u hu.le]
  unfold fourthCutoff regularFourth RiemannRealOrderFractionalDensity.density exponential
  ring

theorem fourthRemainder_derivative_eq (a t u : ℝ) (hu : 0 < u) :
    deriv (fourthRemainder a t) u = phaseJet a t 5 (u : ℂ)*endpointDifference a t u+
      fourthCutoff a t u+regularFifth a t (u : ℂ) := by
  have hK : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)
  rw [(fourthRemainder_hasDerivAt a t u hu).deriv,density_fifth_derivative a t (u : ℂ)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hu)) hK,endpointDifference_actual a t u hu.le]
  unfold fourthCutoff regularFifth fifthBell RiemannRealOrderFractionalDensity.density exponential
  ring

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFifthDerivative
