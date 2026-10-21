import Foundation.RiemannRealOrderFourthFourier
import Foundation.RiemannRealOrderFractionalCoefficient

/-! Reconstruction of the actual flow from the fourth density cosine transform. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourthReconstruction
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets
open RiemannRealOrderFractionalRemainder RiemannRealOrderFractionalFourier
open RiemannRealOrderFractionalReconstruction RiemannRealOrderFractionalCoefficient
open RiemannRealOrderFifthDerivative RiemannRealOrderFourthRemainder RiemannRealOrderFourthFourier

theorem third_density_endpoint (a t : ℝ) (ha : 3/2 < a) :
    Tendsto (fun u : ℝ => iteratedDeriv 3 (RiemannRealOrderFractionalDensity.density a t)
      (u : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hp := phaseJet_continuousOn a t 3 (by norm_num; linarith)
  have hq : ContinuousOn (cutoff a t) (Ici 0) := by
    unfold cutoff
    exact (hp.mul continuousOn_const).mul (by fun_prop)
  have hq0 : cutoff a t 0=0 := by
    rw [cutoff,Complex.ofReal_zero,phaseJet_zero_of_pos a t 3 (by norm_num; linarith)]
    ring
  have hc := hq 0 (by simp)
  have hqt : Tendsto (cutoff a t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [hq0] using
      (hc.mono (show Ioi (0 : ℝ) ⊆ Ici 0 from fun u hu => (show 0 < u from hu).le)).tendsto
  have h := (remainder_tendsto_zero a t (by linarith)).add hqt
  simpa only [RiemannRealOrderFractionalJets.remainder,sub_add_cancel,zero_add] using h

theorem thirdSine_fourthCosine (a t x : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    (x : ℂ)*thirdSine a t x=fourthCosine a t x := by
  let f : ℝ → ℂ := fun u => iteratedDeriv 3 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)
  let fp : ℝ → ℂ := fun u => iteratedDeriv 4 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)
  let g : ℝ → ℂ := fun u => (Real.cos (x*u) : ℂ)
  let gp : ℝ → ℂ := fun u => -(x : ℂ)*(Real.sin (x*u) : ℂ)
  have hf (u : ℝ) (hu : u ∈ Ioi 0) : HasDerivAt f (fp u) u :=
    RiemannRealOrderFractionalDensity.density_profile_hasDerivAt 3 a t u hu
  have hg (u : ℝ) : HasDerivAt g (gp u) u := by
    convert (((hasDerivAt_id u).const_mul x).cos).ofReal_comp using 1
    · rfl
    · simp [g,gp,Complex.ofReal_mul,mul_comm]
  have hfg : IntegrableOn (f*gp) (Ioi 0) := by
    apply ((thirdSine_integrable a t x (by linarith) ha2).const_mul (-(x : ℂ))).congr
    filter_upwards with u
    simp only [Pi.mul_apply,f,gp]
    ring
  have hfp : IntegrableOn (fp*g) (Ioi 0) := fourthCosine_integrable a t x ha ha2
  have hzero : Tendsto (f*g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous g := by dsimp [g]; fun_prop
    simpa only [zero_mul,Pi.mul_def] using (third_density_endpoint a t ha).mul
      (hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  have htop : Tendsto (f*g) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun u => ?_)
      (tendsto_zero_iff_norm_tendsto_zero.mp
        (RiemannRealOrderFractionalDensity.density_iteratedDeriv_tendsto_zero 3 a t (by linarith) ha2))
    simp only [Pi.mul_apply,norm_mul,f,g]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one (x*u))
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hf (fun u _ => hg u) hfg hfp hzero htop
  have he : (∫ u : ℝ in Ioi 0, f u*gp u)= -(x : ℂ)*thirdSine a t x := by
    rw [thirdSine,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp [f,gp]
    ring
  rw [he] at h
  apply neg_injective
  simpa only [sub_zero,zero_sub,neg_mul,fp,g,fourthCosine] using h

theorem actual_fourth_identity (a t x : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    (x : ℂ)^4*RiemannRealOrderFlow.flow a t (x : ℂ)=fourthCosine a t x := by
  calc
    _ = (x : ℂ)*((x : ℂ)^3*RiemannRealOrderFlow.flow a t (x : ℂ)) := by ring
    _ = (x : ℂ)*thirdSine a t x := by rw [actual_third_identity a t x (by linarith) ha2]
    _ = _ := thirdSine_fourthCosine a t x ha ha2

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourthReconstruction
