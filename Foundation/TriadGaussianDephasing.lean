import Foundation.TriadGaussianFlow
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact Gaussian dephasing of one triad coordinate coexists with a centered
fixed coordinate and a norm-preserving Koopman operator on all of L2. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.TriadGaussianDephasing
open TriadGaussianFlow
set_option backward.isDefEq.respectTransparency false

def planeSample (ω : InfiniteGaussian.SampleSpace) : Plane := WithLp.toLp 2 ![ω 0,ω 1]

theorem planeSample_preserving : MeasurePreserving planeSample InfiniteGaussian.gaussianProduct planeGaussian :=
  (measurePreserving_snd (μ := γ) (ν := planeGaussian)).comp
    (encode_preserving.comp sampleVector_preserving)

theorem planeSample_apply (ω : InfiniteGaussian.SampleSpace) (i : Fin 2) :
    planeSample ω i=ω (i : ℕ) := by fin_cases i <;> rfl

theorem plane_moment (i j : Fin 2) :
    (∫ z : Plane, z i*z j ∂planeGaussian)=if i=j then 1 else 0 := by
  have he := integral_map (μ := InfiniteGaussian.gaussianProduct)
    planeSample_preserving.measurable.aemeasurable (f := fun z : Plane => z i*z j) (by fun_prop)
  rw [planeSample_preserving.map_eq] at he
  rw [he]
  simp_rw [planeSample_apply]
  simpa only [InfiniteGaussian.coordinate,Fin.val_inj] using
    InfiniteGaussian.coordinate_product_integral (i : ℕ) (j : ℕ)

theorem plane_mean (i : Fin 2) : (∫ z : Plane, z i ∂planeGaussian)=0 := by
  have he := integral_map (μ := InfiniteGaussian.gaussianProduct)
    planeSample_preserving.measurable.aemeasurable (f := fun z : Plane => z i) (by fun_prop)
  rw [planeSample_preserving.map_eq] at he
  rw [he]
  simp_rw [planeSample_apply]
  exact InfiniteGaussian.coordinate_integral (i : ℕ)

theorem plane_product_integrable (i j : Fin 2) : Integrable (fun z : Plane => z i*z j) planeGaussian := by
  have hi : Integrable (fun z : Plane => z i*z i) planeGaussian :=
    integrable_of_integral_eq_one (by simpa using plane_moment i i)
  have hj : Integrable (fun z : Plane => z j*z j) planeGaussian :=
    integrable_of_integral_eq_one (by simpa using plane_moment j j)
  apply Integrable.mono' (hi.add hj) (by fun_prop)
  filter_upwards [] with z
  change ‖z i*z j‖ ≤ z i*z i+z j*z j
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (z i+z j),sq_nonneg (z i-z j),
    sq_nonneg (z i),sq_nonneg (z j)]

theorem gaussian_square : (∫ c : ℝ, c^2 ∂γ)=1 := by
  have h := GaussianCore.polynomial_stein (Polynomial.X : Polynomial ℝ)
  simpa [pow_two] using h

theorem cosine_integrable (t : ℝ) : Integrable (fun c : ℝ => Real.cos (t*c)) γ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  exact ae_of_all _ (fun c => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*c))

theorem sine_integrable (t : ℝ) : Integrable (fun c : ℝ => Real.sin (t*c)) γ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  exact ae_of_all _ (fun c => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (t*c))

theorem gaussian_cosine (t : ℝ) : (∫ c : ℝ, Real.cos (t*c) ∂γ)=Real.exp (-t^2/2) := by
  have hi : Integrable (fun c : ℝ => Complex.exp ((t*c : ℝ)*Complex.I)) γ := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    filter_upwards [] with c
    simp [Complex.norm_exp,Complex.mul_re]
  have h := charFun_gaussianReal (μ := 0) (v := 1) t
  rw [charFun_apply_real] at h
  have hp : (∫ c : ℝ, Complex.exp ((t*c : ℝ)*Complex.I) ∂γ)=Complex.exp (-(t : ℂ)^2/2) := by
    simpa [γ,GaussianCore.γ,neg_div] using h
  have hr := congrArg Complex.re hp
  change RCLike.re (∫ c : ℝ, Complex.exp ((t*c : ℝ)*Complex.I) ∂γ) = _ at hr
  rw [← integral_re hi] at hr
  simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im,pow_two] using hr

def correlation (t : ℝ) : ℝ := ∫ x : State, (flow t x).2 0*x.2 0 ∂law

theorem correlation_formula (t : ℝ) : correlation t=Real.exp (-t^2/2) := by
  have he : (fun x : State => (flow t x).2 0*x.2 0)=fun x : State =>
      Real.cos (t*x.1)*(x.2 0*x.2 0)+Real.sin (t*x.1)*(x.2 1*x.2 0) := by
    funext x
    simp [flow,rotate_apply]
    ring
  have hi := (cosine_integrable t).mul_prod (plane_product_integrable 0 0)
  have hj := (sine_integrable t).mul_prod (plane_product_integrable 1 0)
  unfold correlation
  rw [he,integral_add hi hj]
  change (∫ x : ℝ × Plane, Real.cos (t*x.1)*(x.2 0*x.2 0) ∂γ.prod planeGaussian) +
    (∫ x : ℝ × Plane, Real.sin (t*x.1)*(x.2 1*x.2 0) ∂γ.prod planeGaussian) = _
  rw [integral_prod_mul (fun c : ℝ => Real.cos (t*c)) (fun z : Plane => z 0*z 0),
    integral_prod_mul (fun c : ℝ => Real.sin (t*c)) (fun z : Plane => z 1*z 0),
    plane_moment,plane_moment]
  simp [gaussian_cosine]

theorem correlation_tendsto_zero : Tendsto correlation atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t^2/2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num : (0 : ℝ)<2) (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have he : correlation=fun t : ℝ => Real.exp (-t^2/2) := funext correlation_formula
  rw [he]
  simpa only [Function.comp_def,neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht

theorem state_plane_mean (i : Fin 2) : (∫ x : State, x.2 i ∂law)=0 := by
  have h := integral_prod_mul (μ := γ) (ν := planeGaussian) (fun _ : ℝ => (1 : ℝ)) (fun z : Plane => z i)
  simpa [plane_mean] using h

theorem state_plane_second (i : Fin 2) : (∫ x : State, (x.2 i)^2 ∂law)=1 := by
  have h := integral_prod_mul (μ := γ) (ν := planeGaussian)
    (fun _ : ℝ => (1 : ℝ)) (fun z : Plane => z i*z i)
  simpa [plane_moment,pow_two] using h

theorem flow_integral (t : ℝ) (f : State → ℝ) (hf : Measurable f) :
    (∫ x, f (flow t x) ∂law)=∫ x, f x ∂law := by
  have h := integral_map (μ := law) (flow_preserving t).measurable.aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [(flow_preserving t).map_eq] at h
  exact h.symm

theorem first_mean_zero (t : ℝ) : (∫ x : State, (flow t x).2 0 ∂law)=0 :=
  (flow_integral t (fun x : State => x.2 0) (by fun_prop)).trans (state_plane_mean 0)

theorem first_second_one (t : ℝ) : (∫ x : State, ((flow t x).2 0)^2 ∂law)=1 :=
  (flow_integral t (fun x : State => (x.2 0)^2) (by fun_prop)).trans (state_plane_second 0)

theorem fixed_mean_zero : (∫ x : State, x.1 ∂law)=0 := by
  have h := integral_prod_mul (μ := γ) (ν := planeGaussian) (fun c : ℝ => c) (fun _ : Plane => (1 : ℝ))
  simpa [γ,GaussianCore.γ] using h

theorem fixed_second_one : (∫ x : State, (x.1)^2 ∂law)=1 := by
  have h := integral_prod_mul (μ := γ) (ν := planeGaussian)
    (fun c : ℝ => c^2) (fun _ : Plane => (1 : ℝ))
  simpa [gaussian_square] using h

theorem fixed_correlation (t : ℝ) : (∫ x : State, (flow t x).1*x.1 ∂law)=1 := by
  simpa only [flow,pow_two] using fixed_second_one

theorem fixed_memLp : MemLp (fun x : State => x.1) 2 law :=
  (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_fst (μ := γ) (ν := planeGaussian))

def fixedClass : Lp ℝ 2 law := fixed_memLp.toLp (fun x : State => x.1)

theorem fixedClass_coeFn : fixedClass =ᵐ[law] fun x : State => x.1 := fixed_memLp.coeFn_toLp

theorem fixedClass_centered : (∫ x, fixedClass x ∂law)=0 :=
  (integral_congr_ae fixedClass_coeFn).trans fixed_mean_zero

theorem fixedClass_norm_sq : ‖fixedClass‖^2=1 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ x : State, (x.1)^2 ∂law := by
      apply integral_congr_ae
      filter_upwards [fixedClass_coeFn] with x hx
      simp [hx,Real.norm_eq_abs,sq_abs]
    _ = _ := fixed_second_one

theorem fixedClass_norm : ‖fixedClass‖=1 := by
  have h := fixedClass_norm_sq
  nlinarith [norm_nonneg fixedClass]

def koopman (t : ℝ) : Lp ℝ 2 law →ₗᵢ[ℝ] Lp ℝ 2 law :=
  Lp.compMeasurePreservingₗᵢ ℝ (flow t) (flow_preserving t)

theorem koopman_norm (t : ℝ) (f : Lp ℝ 2 law) : ‖koopman t f‖=‖f‖ := (koopman t).norm_map f

theorem koopman_fixed (t : ℝ) : koopman t fixedClass=fixedClass := by
  apply Lp.ext
  have hc := (flow_preserving t).quasiMeasurePreserving.ae_eq_comp fixedClass_coeFn
  filter_upwards [Lp.coeFn_compMeasurePreserving fixedClass (flow_preserving t),
    hc,fixedClass_coeFn] with x hk hx hf
  change (Lp.compMeasurePreserving (flow t) (flow_preserving t) fixedClass) x=fixedClass x
  rw [hk,hx,hf]
  rfl

theorem no_strict_centered_contraction (t q : ℝ) (hq : q < 1) :
    ¬ (∀ f : Lp ℝ 2 law, (∫ x, f x ∂law)=0 → ‖koopman t f‖ ≤ q*‖f‖) := by
  intro h
  have he := h fixedClass fixedClass_centered
  rw [koopman_norm,fixedClass_norm,mul_one] at he
  exact not_le.mpr hq he

theorem fixed_correlation_not_tendsto_zero :
    ¬ Tendsto (fun t : ℝ => ∫ x : State, (flow t x).1*x.1 ∂law) atTop (𝓝 0) := by
  intro h
  have he : (fun t : ℝ => ∫ x : State, (flow t x).1*x.1 ∂law)=fun _ : ℝ => (1 : ℝ) :=
    funext fixed_correlation
  rw [he] at h
  have hh : (1 : ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at hh

/-- Individual-coordinate dephasing does not imply decay for every centered L2 test. -/
theorem not_all_centered_correlations_decay :
    ¬ (∀ f : State → ℝ, Measurable f → MemLp f 2 law → (∫ x, f x ∂law)=0 →
      Tendsto (fun t : ℝ => ∫ x, f (flow t x)*f x ∂law) atTop (𝓝 0)) := by
  intro h
  exact fixed_correlation_not_tendsto_zero (h Prod.fst measurable_fst fixed_memLp fixed_mean_zero)

end OperatorDerivativeRewrite.Foundation.TriadGaussianDephasing
