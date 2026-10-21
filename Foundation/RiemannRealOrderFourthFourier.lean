import Foundation.RiemannRealOrderFourthRemainder
import Foundation.RiemannRealOrderFractionalReconstruction

/-! Genuine fourth-density cosine transforms and integration by parts. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourthFourier
open RiemannRealOrderFractionalJets RiemannRealOrderFractionalRemainder
open RiemannRealOrderFifthDerivative RiemannRealOrderFourthRemainder
open RiemannRealOrderFractionalFourier RiemannRealOrderFractionalReconstruction

private theorem sine_integrable (f : ℝ → ℂ) (hf : IntegrableOn f (Ioi 0)) (x : ℝ) :
    IntegrableOn (fun u : ℝ => f u*(Real.sin (x*u) : ℂ)) (Ioi 0) := by
  apply hf.mul_bdd (c := 1) (by fun_prop)
  filter_upwards with u
  simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one (x*u)

private theorem cosine_integrable (f : ℝ → ℂ) (hf : IntegrableOn f (Ioi 0)) (x : ℝ) :
    IntegrableOn (fun u : ℝ => f u*(Real.cos (x*u) : ℂ)) (Ioi 0) := by
  apply hf.mul_bdd (c := 1) (by fun_prop)
  filter_upwards with u
  simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one (x*u)

def cosineRemainder (a t x : ℝ) : ℂ :=
  ∫ u : ℝ in Ioi 0, fourthRemainder a t u*(Real.cos (x*u) : ℂ)

def fourthCosine (a t x : ℝ) : ℂ := ∫ u : ℝ in Ioi 0,
  iteratedDeriv 4 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)*(Real.cos (x*u) : ℂ)

theorem cosineRemainder_integrable (a t x : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ => fourthRemainder a t u*(Real.cos (x*u) : ℂ)) (Ioi 0) :=
  cosine_integrable _ (fourthRemainder_integrable a t ha ha2) x

theorem fourthCosine_integrable (a t x : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ => iteratedDeriv 4 (RiemannRealOrderFractionalDensity.density a t)
      (u : ℂ)*(Real.cos (x*u) : ℂ)) (Ioi 0) :=
  cosine_integrable _ (fourth_density_integrable a t ha ha2) x

theorem cosineRemainder_ibp (a t x : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    (x : ℂ)*cosineRemainder a t x =
      -(∫ u : ℝ in Ioi 0, deriv (fourthRemainder a t) u*(Real.sin (x*u) : ℂ)) := by
  let g : ℝ → ℂ := fun u => (Real.sin (x*u) : ℂ)
  let gp : ℝ → ℂ := fun u => (x : ℂ)*(Real.cos (x*u) : ℂ)
  have hg (u : ℝ) : HasDerivAt g (gp u) u := by
    convert (((hasDerivAt_id u).const_mul x).sin).ofReal_comp using 1
    · rfl
    · simp [g,gp,Complex.ofReal_mul,mul_comm]
  have hf (u : ℝ) (hu : u ∈ Ioi 0) : HasDerivAt (fourthRemainder a t)
      (deriv (fourthRemainder a t) u) u :=
    (fourthRemainder_hasDerivAt a t u hu).differentiableAt.hasDerivAt
  have hfg : IntegrableOn ((fourthRemainder a t)*gp) (Ioi 0) := by
    apply ((cosineRemainder_integrable a t x ha ha2).const_mul (x : ℂ)).congr
    filter_upwards with u
    simp only [Pi.mul_apply,gp]
    ring
  have hfp := sine_integrable _ (fourthRemainder_derivative_integrable a t ha ha2) x
  have hzero : Tendsto ((fourthRemainder a t)*g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hg0 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous g := by dsimp [g]; fun_prop
      have hct : ContinuousAt g (0 : ℝ) := hc.continuousAt
      simpa [g] using hct.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [mul_zero,Pi.mul_def] using (fourthRemainder_endpoint a t ha).mul hg0
  have htop : Tendsto ((fourthRemainder a t)*g) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun u => ?_)
      (tendsto_zero_iff_norm_tendsto_zero.mp (fourthRemainder_tendsto_zero_atTop a t ha ha2))
    simp only [Pi.mul_apply,norm_mul,g]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one (x*u))
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hf (fun u _ => hg u) hfg hfp hzero htop
  have he : (∫ u : ℝ in Ioi 0, fourthRemainder a t u*gp u)=(x : ℂ)*cosineRemainder a t x := by
    rw [cosineRemainder,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp [gp]
    ring
  rw [he] at h
  simpa only [sub_zero,zero_sub,g] using h

theorem cosineRemainder_norm_bound (a t x : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    |x| * ‖cosineRemainder a t x‖ ≤ ∫ u : ℝ in Ioi 0, ‖deriv (fourthRemainder a t) u‖ := by
  have hx : ‖(x : ℂ)‖=|x| := by simp only [Complex.norm_real,Real.norm_eq_abs]
  rw [← hx,← norm_mul,cosineRemainder_ibp a t x ha ha2,norm_neg]
  apply norm_integral_le_of_norm_le (fourthRemainder_derivative_integrable a t ha ha2).norm
  filter_upwards with u
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one (x*u))

theorem scaled_cosineRemainder_limit (a t b : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) (hb : b < 1) :
    Tendsto (fun x : ℝ => ((x^b : ℝ) : ℂ)*cosineRemainder a t x) atTop (𝓝 0) := by
  let C := ∫ u : ℝ in Ioi 0, ‖deriv (fourthRemainder a t) u‖
  have ht : Tendsto (fun x : ℝ => x^(b-1)*C) atTop (𝓝 0) := by
    simpa only [neg_sub,sub_zero,zero_mul] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hb)).mul_const C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.eventually_atTop.2 ⟨1,fun x hx => ?_⟩) ht
  have hx0 : 0 < x := by linarith
  have hbound := cosineRemainder_norm_bound a t x ha ha2
  rw [abs_of_pos hx0] at hbound
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  calc
    _ = x^(b-1)*(x*‖cosineRemainder a t x‖) := by
      rw [Real.rpow_sub_one hx0.ne' b]
      field_simp
    _ ≤ x^(b-1)*C := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hx0.le _)

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourthFourier
