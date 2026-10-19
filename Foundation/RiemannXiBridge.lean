import Foundation.RiemannXiNormalization
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The literal arithmetic quartic flow starts at the actual normalized
completed-zeta entire function, throughout the complex spatial plane. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannXiBridge
open RiemannXiNormalization RiemannQuarticFlow RiemannQuarticReality

def normalizedXi (z : ℂ) : ℂ := entireXi ((1 : ℂ)/2+Complex.I*z/2)/8

theorem normalizedXi_differentiable : Differentiable ℂ normalizedXi := by
  have ha : Differentiable ℂ (fun z : ℂ => (1 : ℂ)/2+Complex.I*z/2) := by fun_prop
  exact (entireXi_differentiable.comp ha).div_const 8

theorem flow_zero_eq_normalizedXi : flow 0 = normalizedXi := by
  have hf : AnalyticOnNhd ℂ (flow 0) univ :=
    (flow_differentiable 0).differentiableOn.analyticOnNhd isOpen_univ
  have hg : AnalyticOnNhd ℂ normalizedXi univ :=
    normalizedXi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero] using!
      Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
        (fun x (hx : x ∈ ({(0 : ℝ)}ᶜ)) => by
          change (x : ℂ) ≠ 0
          change x ≠ 0 at hx
          exact_mod_cast hx)
  have hh : ∃ᶠ z : ℂ in 𝓝[≠] 0, flow 0 z=normalizedXi z := by
    apply ht.frequently
    exact (Eventually.of_forall fun x : ℝ => flow_zero_real_eq_entireXi x).frequently
  exact hf.eq_of_frequently_eq hg hh

theorem flow_zero_complex (z : ℂ) :
    flow 0 z = entireXi ((1 : ℂ)/2+Complex.I*z/2)/8 := by
  exact congrFun flow_zero_eq_normalizedXi z

theorem normalizedXi_ne_zero_on_imaginary_axis (y : ℝ) :
    normalizedXi (Complex.I*(y : ℂ)) ≠ 0 := by
  rw [← flow_zero_eq_normalizedXi]
  exact flow_ne_zero_on_imaginary_axis 0 y

end OperatorDerivativeRewrite.Foundation.RiemannXiBridge
