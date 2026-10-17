import Foundation.ConeSupportAlgebra

/-! A divergence-free Hermitian test for the nonzero cone interaction. -/
noncomputable section
open MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap LineDeriv Pointwise
namespace OperatorDerivativeRewrite.Foundation.ConeInteractionWitness
set_option backward.isDefEq.respectTransparency false
open DivergenceFreeConeWitness ConeInteractionCore

def rotor (N : 𝓢(Space, Values)) : 𝓢(Space, ℂ) :=
  ∂_{axis 2} (coordinate 0 N) + -(∂_{axis 0} (coordinate 2 N))

theorem fourier_rotor (N : 𝓢(Space, Values)) (ξ : Space) :
    𝓕 (rotor N) ξ=kappa*(ξ 2 : ℂ)*𝓕 N ξ 0 + -(kappa*(ξ 0 : ℂ)*𝓕 N ξ 2) := by
  simp only [rotor, FourierTransform.fourier_add, FourierTransform.fourier_neg,
    add_apply, neg_apply, fourier_partial, fourier_coordinate]

theorem rotor_nonzero {δ : ℝ} (B : SpectralBump δ) (hδ : δ≤1) :
    rotor (advect (inputU B) (inputV B))≠0 := by
  have hN : 𝓕 (advect (inputU B) (inputV B)) centralFrequency 2≠0 := by
    intro hz
    have hp := central_fourier_positive B hδ
    simpa [hz] using hp
  have hc : 𝓕 (rotor (advect (inputU B) (inputV B))) centralFrequency =
      -(2:ℂ)*kappa*𝓕 (advect (inputU B) (inputV B)) centralFrequency 2 := by
    have h0 : centralFrequency 0=(2:ℝ) := by simp [centralFrequency, axis]
    have h2 : centralFrequency 2=(0:ℝ) := by simp [centralFrequency, axis]
    rw [fourier_rotor, h0, h2]
    push_cast
    ring
  have hn : 𝓕 (rotor (advect (inputU B) (inputV B))) centralFrequency≠0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero (by norm_num) kappa_ne_zero) hN
  intro hz
  apply hn
  simp [hz]

def hermitianBilin : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).bilinearComp (ContinuousLinearMap.id ℝ ℂ)
    Complex.conjCLE.toContinuousLinearMap

theorem hermitianBilin_apply (z t : ℂ) : hermitianBilin z t=z*starRingEnd ℂ t := rfl

theorem hermitian_ibp (f g : 𝓢(Space, ℂ)) (i : Fin 3) :
    (∫ x : Space, f x*starRingEnd ℂ (∂_{axis i} g x)) =
      -∫ x : Space, ∂_{axis i} f x*starRingEnd ℂ (g x) := by
  exact SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left f g hermitianBilin (axis i)

theorem scalar_pair_integrable (f g : 𝓢(Space, ℂ)) :
    Integrable (fun x : Space => f x*starRingEnd ℂ (g x)) volume := by
  simpa only [RCLike.inner_apply] using SingleConePairings.hermitian_integrable g f

theorem curl02_apply_zero (f : 𝓢(Space, ℂ)) (x : Space) : curl02 f x 0=∂_{axis 2} f x := by
  simp [curl02, lift_apply_component]
theorem curl02_apply_one (f : 𝓢(Space, ℂ)) (x : Space) : curl02 f x 1=0 := by
  simp [curl02, lift_apply_component]
theorem curl02_apply_two (f : 𝓢(Space, ℂ)) (x : Space) : curl02 f x 2= -(∂_{axis 0} f x) := by
  simp [curl02, lift_apply_component]

theorem rotor_energy_identity (N : 𝓢(Space, Values)) :
    SingleConePairings.hermitianPairing (curl02 (rotor N)) N =
      -SingleConePairings.hermitianPairing (rotor N) (rotor N) := by
  let r := rotor N
  let a := ∂_{axis 2} (coordinate 0 N)
  let b := ∂_{axis 0} (coordinate 2 N)
  have hR : SingleConePairings.hermitianPairing r r =
      (∫ x : Space, a x*starRingEnd ℂ (r x)) - (∫ x : Space, b x*starRingEnd ℂ (r x)) := by
    rw [SingleConePairings.scalar_hermitian_formula]
    have he : (fun x : Space => r x*starRingEnd ℂ (r x)) =
        (fun x => a x*starRingEnd ℂ (r x) - b x*starRingEnd ℂ (r x)) := by
      ext x
      change (a x + -b x)*starRingEnd ℂ (r x)=_
      ring
    rw [he, integral_sub (scalar_pair_integrable a r) (scalar_pair_integrable b r)]
  calc
    _ = (∫ x : Space, coordinate 0 N x*starRingEnd ℂ (∂_{axis 2} r x)) -
        (∫ x : Space, coordinate 2 N x*starRingEnd ℂ (∂_{axis 0} r x)) := by
      calc
        _ = ∫ x : Space,
            coordinate 0 N x*starRingEnd ℂ (∂_{axis 2} r x) -
              coordinate 2 N x*starRingEnd ℂ (∂_{axis 0} r x) := by
          unfold SingleConePairings.hermitianPairing
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro x
          simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three, curl02_apply_zero,
            curl02_apply_one, curl02_apply_two, sub_eq_add_neg]
          rfl
        _ = _ := integral_sub (scalar_pair_integrable (coordinate 0 N) (∂_{axis 2} r))
          (scalar_pair_integrable (coordinate 2 N) (∂_{axis 0} r))
    _ = -((∫ x : Space, a x*starRingEnd ℂ (r x)) -
        (∫ x : Space, b x*starRingEnd ℂ (r x))) := by
      rw [hermitian_ibp, hermitian_ibp]
      ring
    _ = _ := congrArg Neg.neg hR.symm

theorem hermitian_advection (u v w : 𝓢(Space, Values)) :
    HermitianTriadFourier.hermitianTrilinear u v w =
      SingleConePairings.hermitianPairing w (advect u v) := by
  unfold HermitianTriadFourier.hermitianTrilinear SingleConePairings.hermitianPairing
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [PiLp.inner_apply, RCLike.inner_apply, advect_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]

def response {δ : ℝ} (B : SpectralBump δ) : 𝓢(Space, Values) :=
  curl02 (rotor (advect (inputU B) (inputV B)))

theorem response_physical_divergence {δ : ℝ} (B : SpectralBump δ) (x : Space) :
    (∑ i : Fin 3, fderiv ℝ (fun y : Space => response B y i) x (axis i))=0 :=
  curl02_physical_divergence _ x

theorem interaction_real_negative {δ : ℝ} (B : SpectralBump δ) (hδ : δ≤1) :
    (HermitianTriadFourier.hermitianTrilinear (inputU B) (inputV B) (response B)).re<0 := by
  rw [hermitian_advection]
  unfold response
  rw [rotor_energy_identity]
  have hp := SingleConePairings.hermitian_self_positive _ (rotor_nonzero B hδ)
  simpa using neg_neg_of_pos hp

theorem interaction_ne_zero {δ : ℝ} (B : SpectralBump δ) (hδ : δ≤1) :
    HermitianTriadFourier.hermitianTrilinear (inputU B) (inputV B) (response B)≠0 := by
  intro hz
  have hp := interaction_real_negative B hδ
  simpa [hz] using hp

theorem rotor_fourier_support (N : 𝓢(Space, Values)) :
    Function.support (fun ξ => 𝓕 (rotor N) ξ) ⊆ Function.support (fun ξ => 𝓕 N ξ) := by
  intro ξ hξ hz
  change 𝓕 N ξ=0 at hz
  apply hξ
  change 𝓕 (rotor N) ξ=0
  rw [fourier_rotor, hz]
  simp

theorem rotor_fourier_tsupport (N : 𝓢(Space, Values)) :
    tsupport (fun ξ => 𝓕 (rotor N) ξ) ⊆ tsupport (fun ξ => 𝓕 N ξ) :=
  closure_mono (rotor_fourier_support N)

theorem response_tsupport {δ : ℝ} (B : SpectralBump δ) (hδ0 : 0<δ) (hδ1 : δ≤1) :
    tsupport (fun ξ => 𝓕 (response B) ξ) ⊆ SingleConeReality.cone (axis 0) δ :=
  (curl02_fourier_tsupport _).trans ((rotor_fourier_tsupport _).trans
    (ConeSupportAlgebra.advection_tsupport_cone B hδ0 hδ1))

def solenoidal (F : 𝓢(Space, Values)) : Prop :=
  ∀ x, (∑ i : Fin 3, fderiv ℝ (fun y : Space => F y i) x (axis i))=0

theorem inputs_solenoidal {δ : ℝ} (B : SpectralBump δ) :
    solenoidal (inputU B) ∧ solenoidal (inputV B) :=
  ⟨curl_physical_divergence _, curl02_physical_divergence _⟩

theorem inputs_response_nonzero {δ : ℝ} (B : SpectralBump δ) (hδ : δ≤1) :
    inputU B≠0 ∧ inputV B≠0 ∧ response B≠0 := by
  have hT := interaction_ne_zero B hδ
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    apply hT
    simp [hz, HermitianTriadFourier.hermitianTrilinear]
  · intro hz
    apply hT
    simp [hz, HermitianTriadFourier.hermitianTrilinear]
  · intro hz
    apply hT
    simp [hz, HermitianTriadFourier.hermitianTrilinear]

theorem literal_interaction_zero {δ : ℝ} (B : SpectralBump δ) (hδ0 : 0<δ) (hδ1 : δ≤1) :
    SingleConeTrilinear.trilinear (inputU B) (inputV B) (response B)=0 :=
  SingleConeTrilinear.cone_trilinear_zero _ _ _ (axis 0) δ hδ1
    ((subset_tsupport _).trans (inputU_tsupport B))
    ((subset_tsupport _).trans (inputV_tsupport B))
    ((subset_tsupport _).trans (response_tsupport B hδ0 hδ1))

theorem pairings_unequal {δ : ℝ} (B : SpectralBump δ) (hδ0 : 0<δ) (hδ1 : δ≤1) :
    SingleConeTrilinear.trilinear (inputU B) (inputV B) (response B) ≠
      HermitianTriadFourier.hermitianTrilinear (inputU B) (inputV B) (response B) := by
  rw [literal_interaction_zero B hδ0 hδ1]
  exact (interaction_ne_zero B hδ1).symm

theorem source_form_distinction {δ : ℝ} (B : SpectralBump δ) (hδ0 : 0<δ) (hδ1 : δ≤1) :
    SingleConeTrilinear.trilinear (inputU B) (inputV B) (response B) ≠
      ∫ z : Space × Space, HermitianTriadFourier.vectorKernel (inputU B) (inputV B) (response B) z
        ∂((volume : Measure Space).prod volume) := by
  rw [← HermitianTriadFourier.vector_fourier_representation_prod]
  exact pairings_unequal B hδ0 hδ1

theorem exists_full_cone_interaction (δ : ℝ) (hδ0 : 0<δ) (hδ1 : δ≤1) :
    ∃ u v w : 𝓢(Space, Values), u≠0 ∧ v≠0 ∧ w≠0 ∧
      solenoidal u ∧ solenoidal v ∧ solenoidal w ∧
      tsupport (fun ξ => 𝓕 u ξ) ⊆ SingleConeReality.cone (axis 0) δ ∧
      tsupport (fun ξ => 𝓕 v ξ) ⊆ SingleConeReality.cone (axis 0) δ ∧
      tsupport (fun ξ => 𝓕 w ξ) ⊆ SingleConeReality.cone (axis 0) δ ∧
      SingleConeTrilinear.trilinear u v w=0 ∧
      (HermitianTriadFourier.hermitianTrilinear u v w).re<0 ∧
      SingleConeTrilinear.trilinear u v w≠HermitianTriadFourier.hermitianTrilinear u v w := by
  obtain ⟨B⟩ := spectralBump_nonempty δ hδ0
  have hNZ := inputs_response_nonzero B hδ1
  have hD := inputs_solenoidal B
  exact ⟨inputU B, inputV B, response B, hNZ.1, hNZ.2.1, hNZ.2.2, hD.1, hD.2,
    response_physical_divergence B, inputU_tsupport B, inputV_tsupport B,
    response_tsupport B hδ0 hδ1, literal_interaction_zero B hδ0 hδ1,
    interaction_real_negative B hδ1, pairings_unequal B hδ0 hδ1⟩

end OperatorDerivativeRewrite.Foundation.ConeInteractionWitness
