import Foundation.HermitianTriadFourier

/-! Positive spectral bumps, a second curl plane, and actual Schwartz advection. -/
noncomputable section
open MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap LineDeriv
namespace OperatorDerivativeRewrite.Foundation.ConeInteractionCore
set_option backward.isDefEq.respectTransparency false
open DivergenceFreeConeWitness

structure SpectralBump (δ : ℝ) where
  b : Space → ℝ
  compact : HasCompactSupport b
  smooth : ContDiff ℝ (⊤ : ℕ∞) b
  nonneg : ∀ ξ, 0≤b ξ
  le_one : ∀ ξ, b ξ≤1
  center : b (axis 0)=1
  support : tsupport b ⊆ SingleConeReality.cone (axis 0) δ

theorem spectralBump_nonempty (δ : ℝ) (hδ : 0<δ) : Nonempty (SpectralBump δ) := by
  obtain ⟨b, hs, hc, hd, hb, hn⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (SingleConeComplexWitness.cone_mem_nhds (axis 0) (axis_norm 0) δ hδ)
  exact ⟨⟨b, hc, hd, fun ξ => (hb ⟨ξ,rfl⟩).1, fun ξ => (hb ⟨ξ,rfl⟩).2, hn, hs⟩⟩

def bumpFourier {δ : ℝ} (B : SpectralBump δ) : 𝓢(Space, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (B.compact.toSchwartzMap B.smooth)
def bumpField {δ : ℝ} (B : SpectralBump δ) : 𝓢(Space, ℂ) := 𝓕⁻ (bumpFourier B)

theorem fourier_bumpField {δ : ℝ} (B : SpectralBump δ) (ξ : Space) :
    𝓕 (bumpField B) ξ=(B.b ξ : ℂ) := by
  change 𝓕 (𝓕⁻ (bumpFourier B)) ξ=(B.b ξ : ℂ)
  rw [FourierTransform.fourier_fourierInv_eq]
  rfl

theorem bumpField_tsupport {δ : ℝ} (B : SpectralBump δ) :
    tsupport (fun ξ => 𝓕 (bumpField B) ξ) ⊆ SingleConeReality.cone (axis 0) δ := by
  have he : Function.support (fun ξ => 𝓕 (bumpField B) ξ)=Function.support B.b := by
    ext ξ
    change (𝓕 (bumpField B) ξ≠0) ↔ B.b ξ≠0
    rw [fourier_bumpField]
    simp
  change closure (Function.support (fun ξ => 𝓕 (bumpField B) ξ)) ⊆ _
  rw [he]
  exact B.support

def curl02 (f : 𝓢(Space, ℂ)) : 𝓢(Space, Values) :=
  lift 0 (∂_{axis 2} f) + -(lift 2 (∂_{axis 0} f))

theorem fourier_curl02 (f : 𝓢(Space, ℂ)) (ξ : Space) :
    𝓕 (curl02 f) ξ=(kappa*(ξ 2 : ℂ)*𝓕 f ξ) • EuclideanSpace.single 0 (1:ℂ) +
      -((kappa*(ξ 0 : ℂ)*𝓕 f ξ) • EuclideanSpace.single 2 (1:ℂ)) := by
  simp only [curl02, FourierTransform.fourier_add, FourierTransform.fourier_neg,
    add_apply, neg_apply, fourier_lift, fourier_partial]

theorem fourier_curl02_zero (f : 𝓢(Space, ℂ)) (ξ : Space) :
    𝓕 (curl02 f) ξ 0=kappa*(ξ 2 : ℂ)*𝓕 f ξ := by rw [fourier_curl02]; simp
theorem fourier_curl02_one (f : 𝓢(Space, ℂ)) (ξ : Space) : 𝓕 (curl02 f) ξ 1=0 := by
  rw [fourier_curl02]; simp
theorem fourier_curl02_two (f : 𝓢(Space, ℂ)) (ξ : Space) :
    𝓕 (curl02 f) ξ 2= -(kappa*(ξ 0 : ℂ)*𝓕 f ξ) := by rw [fourier_curl02]; simp

theorem curl02_divergence_zero (f : 𝓢(Space, ℂ)) : divergence (curl02 f)=0 := by
  have hh : 𝓕 (divergence (curl02 f))=0 := by
    ext ξ
    change 𝓕 (divergence (curl02 f)) ξ=(0:ℂ)
    rw [fourier_divergence, Fin.sum_univ_three, fourier_curl02_zero,
      fourier_curl02_one, fourier_curl02_two]
    ring
  have hi := congrArg (fun h : 𝓢(Space, ℂ) => 𝓕⁻ h) hh
  simpa using hi

theorem curl02_physical_divergence (f : 𝓢(Space, ℂ)) (x : Space) :
    (∑ i : Fin 3, fderiv ℝ (fun y : Space => curl02 f y i) x (axis i))=0 := by
  have hh := congrArg (fun h : 𝓢(Space, ℂ) => h x) (curl02_divergence_zero f)
  simpa only [divergence_apply, zero_apply] using hh

theorem curl02_fourier_support (f : 𝓢(Space, ℂ)) :
    Function.support (fun ξ => 𝓕 (curl02 f) ξ) ⊆ Function.support (fun ξ => 𝓕 f ξ) := by
  intro ξ hξ hz
  change 𝓕 f ξ=0 at hz
  apply hξ
  change 𝓕 (curl02 f) ξ=0
  rw [fourier_curl02, hz]
  simp

theorem curl02_fourier_tsupport (f : 𝓢(Space, ℂ)) :
    tsupport (fun ξ => 𝓕 (curl02 f) ξ) ⊆ tsupport (fun ξ => 𝓕 f ξ) :=
  closure_mono (curl02_fourier_support f)

def inputU {δ : ℝ} (B : SpectralBump δ) : 𝓢(Space, Values) := curlField (bumpField B)
def inputV {δ : ℝ} (B : SpectralBump δ) : 𝓢(Space, Values) := curl02 (∂_{axis 1} (bumpField B))

theorem inputs_divergence_free {δ : ℝ} (B : SpectralBump δ) :
    divergence (inputU B)=0 ∧ divergence (inputV B)=0 :=
  ⟨curl_divergence_zero _, curl02_divergence_zero _⟩

theorem inputU_tsupport {δ : ℝ} (B : SpectralBump δ) :
    tsupport (fun ξ => 𝓕 (inputU B) ξ) ⊆ SingleConeReality.cone (axis 0) δ :=
  (curl_fourier_tsupport _).trans (bumpField_tsupport B)

theorem inputV_tsupport {δ : ℝ} (B : SpectralBump δ) :
    tsupport (fun ξ => 𝓕 (inputV B) ξ) ⊆ SingleConeReality.cone (axis 0) δ :=
  (curl02_fourier_tsupport _).trans
    ((closure_mono (SingleConeTrilinear.partial_fourier_support _ 1)).trans (bumpField_tsupport B))

def advectComponent (u v : 𝓢(Space, Values)) (j : Fin 3) : 𝓢(Space, ℂ) :=
  ∑ i : Fin 3, SingleConeTrilinear.product (coordinate i u) (∂_{axis i} (coordinate j v))
def advect (u v : 𝓢(Space, Values)) : 𝓢(Space, Values) :=
  ∑ j : Fin 3, lift j (advectComponent u v j)

theorem advectComponent_apply (u v : 𝓢(Space, Values)) (j : Fin 3) (x : Space) :
    advectComponent u v j x=∑ i : Fin 3, u x i*fderiv ℝ (fun y : Space => v y j) x (axis i) := by
  simp only [advectComponent, sum_apply, SingleConeTrilinear.product_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

theorem lift_apply_component (f : 𝓢(Space, ℂ)) (i j : Fin 3) (x : Space) :
    lift i f x j=if j=i then f x else 0 := by
  change (f x • EuclideanSpace.single i (1:ℂ)) j=if j=i then f x else 0
  by_cases h : j=i
  · subst j; simp
  · simp [h]

theorem advect_apply (u v : 𝓢(Space, Values)) (x : Space) (j : Fin 3) :
    advect u v x j=∑ i : Fin 3, u x i*fderiv ℝ (fun y : Space => v y j) x (axis i) := by
  change coordinateMap j ((∑ k : Fin 3, lift k (advectComponent u v k)) x)=_
  rw [sum_apply, map_sum]
  change (∑ k : Fin 3, lift k (advectComponent u v k) x j)=_
  simp only [lift_apply_component]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true, advectComponent_apply]
  · intro b hb hbj
    simp [Ne.symm hbj]
  · simp

theorem fourier_advectComponent (u v : 𝓢(Space, Values)) (j : Fin 3) (ξ : Space) :
    𝓕 (advectComponent u v j) ξ=∑ i : Fin 3,
      ∫ p : Space, 𝓕 u p i*(kappa*((ξ-p) i : ℂ)*𝓕 v (ξ-p) j) := by
  simp only [advectComponent, FourierTransform.fourier_sum, sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [SingleConeTrilinear.fourier_product, SchwartzMap.convolution_apply]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  change 𝓕 (coordinate i u) p*𝓕 (∂_{axis i} (coordinate j v)) (ξ-p)=_
  rw [fourier_coordinate, fourier_partial, fourier_coordinate]

theorem fourier_advect_component (u v : 𝓢(Space, Values)) (j : Fin 3) (ξ : Space) :
    𝓕 (advect u v) ξ j=∑ i : Fin 3,
      ∫ p : Space, 𝓕 u p i*(kappa*((ξ-p) i : ℂ)*𝓕 v (ξ-p) j) := by
  have he : coordinate j (advect u v)=advectComponent u v j := by
    ext x
    exact advect_apply u v x j
  rw [← fourier_coordinate, he, fourier_advectComponent]

def advectKernel (u v : 𝓢(Space, Values)) (j : Fin 3) (ξ p : Space) : ℂ :=
  kappa*(∑ i : Fin 3, 𝓕 u p i*((ξ-p) i : ℂ))*𝓕 v (ξ-p) j

theorem advectKernel_eq_sum (u v : 𝓢(Space, Values)) (j : Fin 3) (ξ p : Space) :
    advectKernel u v j ξ p=∑ i : Fin 3, 𝓕 u p i*(kappa*((ξ-p) i : ℂ)*𝓕 v (ξ-p) j) := by
  unfold advectKernel
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem advect_term_integrable (u v : 𝓢(Space, Values)) (i j : Fin 3) (ξ : Space) :
    Integrable (fun p : Space => 𝓕 u p i*(kappa*((ξ-p) i : ℂ)*𝓕 v (ξ-p) j)) volume := by
  simpa only [fourier_coordinate, fourier_partial] using
    SingleConeTrilinear.convolution_integrand_integrable (coordinate i u)
      (∂_{axis i} (coordinate j v)) ξ

theorem advectKernel_integrable (u v : 𝓢(Space, Values)) (j : Fin 3) (ξ : Space) :
    Integrable (advectKernel u v j ξ) volume := by
  have he := funext (advectKernel_eq_sum u v j ξ)
  rw [he]
  exact integrable_finsetSum _ (fun i _ => advect_term_integrable u v i j ξ)

theorem fourier_advect_kernel (u v : 𝓢(Space, Values)) (j : Fin 3) (ξ : Space) :
    𝓕 (advect u v) ξ j=∫ p : Space, advectKernel u v j ξ p := by
  rw [fourier_advect_component, ← integral_finsetSum _ (fun i _ => advect_term_integrable u v i j ξ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => (advectKernel_eq_sum u v j ξ p).symm)

def centralFrequency : Space := (2:ℝ) • axis 0
def centralDensity {δ : ℝ} (B : SpectralBump δ) (p : Space) : ℝ :=
  (p 1)^2*(2-p 0)*B.b p*B.b (centralFrequency-p)

theorem central_kernel_identity {δ : ℝ} (B : SpectralBump δ) (p : Space) :
    advectKernel (inputU B) (inputV B) 2 centralFrequency p =
      2*kappa^4*(centralDensity B p : ℂ) := by
  unfold advectKernel
  rw [Fin.sum_univ_three]
  simp only [inputU, inputV, fourier_curl_zero, fourier_curl_one, fourier_curl_two,
    fourier_curl02_two, fourier_partial, fourier_bumpField]
  simp [centralDensity, centralFrequency, axis]
  ring

theorem central_fourier_identity {δ : ℝ} (B : SpectralBump δ) :
    𝓕 (advect (inputU B) (inputV B)) centralFrequency 2 =
      2*kappa^4*(∫ p : Space, (centralDensity B p : ℂ)) := by
  rw [fourier_advect_kernel, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (central_kernel_identity B)

theorem centralDensity_compact {δ : ℝ} (B : SpectralBump δ) : HasCompactSupport (centralDensity B) := by
  have hb : HasCompactSupport (fun p : Space => (p 1)^2*(2-p 0)*B.b p) := B.compact.mul_left
  exact hb.mul_right

theorem centralDensity_continuous {δ : ℝ} (B : SpectralBump δ) : Continuous (centralDensity B) := by
  have hb : Continuous B.b := B.smooth.continuous
  have h0 : Continuous (fun p : Space => p 0) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 : Space →L[ℝ] ℝ).continuous
  have h1 : Continuous (fun p : Space => p 1) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1 : Space →L[ℝ] ℝ).continuous
  exact (((h1.pow 2).mul (continuous_const.sub h0)).mul hb).mul
    (hb.comp (continuous_const.sub continuous_id))

theorem centralDensity_integrable {δ : ℝ} (B : SpectralBump δ) : Integrable (centralDensity B) volume :=
  (centralDensity_continuous B).integrable_of_hasCompactSupport (centralDensity_compact B)

theorem centralDensity_nonneg {δ : ℝ} (B : SpectralBump δ) (hδ : δ≤1) (p : Space) :
    0≤centralDensity B p := by
  by_cases hh : B.b (centralFrequency-p)=0
  · simp [centralDensity, hh]
  · have hc := B.support ((subset_tsupport B.b) hh)
    have hp := SingleConeTrilinear.cone_subset_positive (axis 0) δ hδ hc
    change 0 < inner ℝ (centralFrequency-p) (EuclideanSpace.basisFun (Fin 3) ℝ 0) at hp
    rw [EuclideanSpace.inner_basisFun_real] at hp
    have hq : 0<2-p 0 := by simpa [centralFrequency, axis] using hp
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hq.le) (B.nonneg _)) (B.nonneg _)

theorem central_density_complex_integral {δ : ℝ} (B : SpectralBump δ) :
    (∫ p : Space, (centralDensity B p : ℂ))=(∫ p : Space, centralDensity B p : ℝ) :=
  Complex.ofRealCLM.integral_comp_comm (centralDensity_integrable B)

theorem kappa_fourth : kappa^4=(((2*Real.pi)^4 : ℝ) : ℂ) := by
  norm_num [kappa, mul_pow]

theorem central_fourier_real_identity {δ : ℝ} (B : SpectralBump δ) :
    𝓕 (advect (inputU B) (inputV B)) centralFrequency 2 =
      ((2*(2*Real.pi)^4*(∫ p : Space, centralDensity B p) : ℝ) : ℂ) := by
  rw [central_fourier_identity, kappa_fourth, central_density_complex_integral]
  push_cast
  ring

theorem central_fourier_nonneg {δ : ℝ} (B : SpectralBump δ) (hδ : δ≤1) :
    0≤(𝓕 (advect (inputU B) (inputV B)) centralFrequency 2).re := by
  rw [central_fourier_real_identity]
  simp only [Complex.ofReal_re]
  have hi : 0≤∫ p : Space, centralDensity B p := integral_nonneg (centralDensity_nonneg B hδ)
  positivity

theorem centralDensity_positive_somewhere {δ : ℝ} (B : SpectralBump δ) :
    ∃ p : Space, 0<centralDensity B p := by
  let G : Space → ℝ := fun p => (2-p 0)*B.b p*B.b (centralFrequency-p)
  have hb : Continuous B.b := B.smooth.continuous
  have h0 : Continuous (fun p : Space => p 0) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 : Space →L[ℝ] ℝ).continuous
  have hG : Continuous G :=
    ((continuous_const.sub h0).mul hb).mul (hb.comp (continuous_const.sub continuous_id))
  have he : centralFrequency-axis 0=axis 0 := by
    unfold centralFrequency
    rw [two_smul]
    abel
  have hG0 : G (axis 0)=1 := by
    dsimp [G]
    rw [he, B.center]
    norm_num [axis]
  have hs : Continuous (fun t : ℝ => axis 0+t • axis 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : ∀ᶠ t : ℝ in 𝓝 0, 0<G (axis 0+t • axis 1) :=
    (hG.comp hs).continuousAt.tendsto.eventually
      (eventually_gt_nhds (by simpa using (show 0<G (axis 0) by rw [hG0]; norm_num)))
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp ht
  have hp : 0<G (axis 0+(ε/2) • axis 1) := by
    apply hεs
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
    rw [abs_of_pos (half_pos hε)]
    linarith
  refine ⟨axis 0+(ε/2) • axis 1, ?_⟩
  have hd (p : Space) : centralDensity B p=(p 1)^2*G p := by
    dsimp [centralDensity, G]
    ring
  rw [hd]
  have hc : (axis 0+(ε/2) • axis 1) 1=ε/2 := by simp [axis]
  rw [hc]
  exact mul_pos (sq_pos_of_pos (half_pos hε)) hp

theorem centralDensity_integral_pos {δ : ℝ} (B : SpectralBump δ) (hδ : δ≤1) :
    0<∫ p : Space, centralDensity B p := by
  apply (integral_pos_iff_support_of_nonneg (f := centralDensity B)
    (centralDensity_nonneg B hδ) (centralDensity_integrable B)).mpr
  obtain ⟨p, hp⟩ := centralDensity_positive_somewhere B
  have ho : IsOpen (Function.support (centralDensity B)) := by
    change IsOpen ((centralDensity B) ⁻¹' (({(0:ℝ)} : Set ℝ)ᶜ))
    exact isOpen_compl_singleton.preimage (centralDensity_continuous B)
  exact ho.measure_pos volume ⟨p, ne_of_gt hp⟩

theorem central_fourier_positive {δ : ℝ} (B : SpectralBump δ) (hδ : δ≤1) :
    0<(𝓕 (advect (inputU B) (inputV B)) centralFrequency 2).re := by
  rw [central_fourier_real_identity]
  simp only [Complex.ofReal_re]
  have hi := centralDensity_integral_pos B hδ
  positivity

theorem advection_nonzero {δ : ℝ} (B : SpectralBump δ) (hδ : δ≤1) :
    advect (inputU B) (inputV B)≠0 := by
  intro hz
  have hp := central_fourier_positive B hδ
  simpa [hz] using hp

end OperatorDerivativeRewrite.Foundation.ConeInteractionCore
