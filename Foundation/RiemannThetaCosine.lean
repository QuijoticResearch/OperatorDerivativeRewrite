import Foundation.RiemannThetaDecay
import Foundation.RiemannQuarticReality
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The actual arithmetic Fourier kernel as a differentiated theta primitive,
with all improper boundary terms evaluated. -/
noncomputable section
open MeasureTheory Filter Set Real Asymptotics
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaCosine
open RiemannQuarticKernel RiemannThetaDifferentiation RiemannThetaModularity
open RiemannThetaDecay RiemannQuarticFlow RiemannQuarticReality

theorem mul_cos_integrable (f : ℝ → ℝ) (hf : IntegrableOn f (Ici 0)) (x : ℝ) :
    IntegrableOn (fun u => f u*cos (x*u)) (Ici 0) := by
  apply hf.mul_bdd (c := 1)
    (by fun_prop : Measurable (fun u : ℝ => cos (x*u))).aestronglyMeasurable
  exact Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using abs_cos_le_one (x*u)

def flux (x u : ℝ) : ℝ := psiPrime u*cos (x*u)+x*(psi u*sin (x*u))

def fluxDerivative (x u : ℝ) : ℝ := (psiSecond u+x^2*psi u)*cos (x*u)

theorem flux_hasDerivAt (x u : ℝ) : HasDerivAt (flux x) (fluxDerivative x u) u := by
  have h := ((psiPrime_hasDerivAt u).mul (((hasDerivAt_id u).const_mul x).cos)).add
    (((psi_hasDerivAt u).mul (((hasDerivAt_id u).const_mul x).sin)).const_mul x)
  convert h using 1
  · rfl
  · simp only [fluxDerivative, id_eq]
    ring

theorem fluxDerivative_integrable (x : ℝ) : IntegrableOn (fluxDerivative x) (Ici 0) := by
  exact mul_cos_integrable _ (psiSecond_integrable.add (psi_integrable.const_mul (x^2))) x

theorem flux_isBigO (x : ℝ) : flux x =O[atTop] fun u : ℝ => exp (-u) := by
  have hc : (fun u : ℝ => cos (x*u)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall fun u => by simpa using abs_cos_le_one (x*u)
  have hs : (fun u : ℝ => sin (x*u)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall fun u => by simpa using abs_sin_le_one (x*u)
  have h := (psiPrime_isBigO.mul hc).add ((psi_isBigO.mul hs).const_mul_left x)
  simpa only [flux, Pi.mul_apply, Pi.add_apply, mul_one] using! h

theorem flux_tendsto (x : ℝ) : Tendsto (flux x) atTop (𝓝 0) :=
  (flux_isBigO x).trans_tendsto Real.tendsto_exp_neg_atTop_nhds_zero

theorem fluxDerivative_integral (x : ℝ) :
    ∫ u in Ici (0 : ℝ), fluxDerivative x u = 1/2 := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (m := 0) (fun u _ => flux_hasDerivAt x u)
    ((fluxDerivative_integrable x).mono_set Ioi_subset_Ici_self) (flux_tendsto x)
  norm_num [flux, psiPrime_zero] at h
  exact h

def primitiveCosine (x : ℝ) : ℝ := ∫ u, psi u*cos (x*u) ∂halfLine

theorem realFlow_zero_eq_primitive (x : ℝ) :
    realFlow 0 x = 1/16-(1+x^2)/8*primitiveCosine x := by
  have hf := fluxDerivative_integral x
  have hψ := mul_cos_integrable psi psi_integrable x
  have hK := mul_cos_integrable kernel kernel_integrable x
  have he : fluxDerivative x = fun u => 8*(kernel u*cos (x*u))+
      (1+x^2)*(psi u*cos (x*u)) := by
    funext u
    have hh := kernel_differential_identity u
    have hsecond : psiSecond u=psi u+8*kernel u := by linarith
    rw [fluxDerivative, hsecond]
    ring
  rw [he, integral_add (hK.const_mul 8) (hψ.const_mul (1+x^2)),
    integral_const_mul, integral_const_mul] at hf
  have hr : realFlow 0 x = ∫ u in Ici (0 : ℝ), kernel u*cos (x*u) := by
    unfold realFlow
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by simp [RiemannQuarticDomain.weighted, mul_comm]
  rw [hr]
  change (∫ u in Ici (0 : ℝ), kernel u*cos (x*u)) =
    1/16-(1+x^2)/8*(∫ u in Ici (0 : ℝ), psi u*cos (x*u))
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannThetaCosine
