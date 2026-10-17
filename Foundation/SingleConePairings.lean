import Foundation.SingleConeEnergyLimit

/-! Bilinear and Hermitian pairings for complex single-cone fields. -/
noncomputable section
open MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap ENNReal
namespace OperatorDerivativeRewrite.Foundation.SingleConePairings
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def bilinearPairing (f g : 𝓢(V, ℂ)) : ℂ := ∫ x : V, f x*g x

theorem product_integrable (f g : 𝓢(V, ℂ)) : Integrable (fun x : V => f x*g x) volume :=
  memLp_one_iff_integrable.mp ((f.memLp 2 volume).fun_mul (g.memLp 2 volume))

theorem inverse_fourier_reflection (g : 𝓢(V, ℂ)) (ξ : V) : 𝓕⁻ g ξ=𝓕 g (-ξ) := rfl

theorem bilinear_fourier_reflection (f g : 𝓢(V, ℂ)) :
    bilinearPairing f g = ∫ ξ : V, 𝓕 f ξ*𝓕 g (-ξ) := by
  have hh := SchwartzMap.integral_fourier_mul_eq f (𝓕⁻ g)
  simpa only [bilinearPairing, FourierTransform.fourier_fourierInv_eq,
    inverse_fourier_reflection] using hh.symm

theorem reflected_product_integrable (f g : 𝓢(V, ℂ)) :
    Integrable (fun ξ : V => 𝓕 f ξ*𝓕 g (-ξ)) volume := by
  simpa only [inverse_fourier_reflection] using product_integrable (𝓕 f) (𝓕⁻ g)

theorem same_cone_fourier_product_zero (f g : 𝓢(V, ℂ)) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hf : Function.support (fun ξ => 𝓕 f ξ) ⊆ SingleConeReality.cone n δ)
    (hg : Function.support (fun ξ => 𝓕 g ξ) ⊆ SingleConeReality.cone n δ) (ξ : V) :
    𝓕 f ξ*𝓕 g (-ξ)=0 := by
  by_cases hF : 𝓕 f ξ=0
  · rw [hF, zero_mul]
  · have hG : 𝓕 g (-ξ)=0 := by
      by_contra hh
      exact SingleConeReality.cone_no_antipodes n δ hδ (hf hF) (hg hh)
    rw [hG, mul_zero]

theorem same_cone_bilinear_zero (f g : 𝓢(V, ℂ)) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hf : Function.support (fun ξ => 𝓕 f ξ) ⊆ SingleConeReality.cone n δ)
    (hg : Function.support (fun ξ => 𝓕 g ξ) ⊆ SingleConeReality.cone n δ) :
    bilinearPairing f g=0 := by
  rw [bilinear_fourier_reflection]
  simp only [same_cone_fourier_product_zero f g n δ hδ hf hg, integral_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hermitianPairing (f g : 𝓢(V, H)) : ℂ := ∫ x : V, inner ℂ (f x) (g x)

theorem hermitian_integrable (f g : 𝓢(V, H)) :
    Integrable (fun x : V => inner ℂ (f x) (g x)) volume := by
  have hh := L2.integrable_inner (𝕜 := ℂ) (f.toLp 2) (g.toLp 2)
  apply hh.congr
  filter_upwards [f.coeFn_toLp 2, g.coeFn_toLp 2] with x hf hg
  rw [hf, hg]

theorem hermitian_eq_l2_inner (f g : 𝓢(V, H)) :
    hermitianPairing f g=inner ℂ (f.toLp 2) (g.toLp 2) := by
  unfold hermitianPairing
  exact (SchwartzMap.inner_toL2_toL2_eq f g volume).symm

theorem hermitian_self_positive (f : 𝓢(V, H)) (hf : f≠0) :
    0<(hermitianPairing f f).re := by
  rw [hermitian_eq_l2_inner]
  apply (re_inner_self_pos (𝕜 := ℂ)).mpr
  intro hh
  apply hf
  apply SchwartzMap.injective_toLp 2 volume
  change f.toLp 2 volume=(SchwartzMap.toLpCLM ℂ H 2 volume) 0
  rw [map_zero]
  exact hh

theorem scalar_hermitian_formula (f g : 𝓢(V, ℂ)) :
    hermitianPairing g f=∫ x : V, f x*starRingEnd ℂ (g x) := by
  simp only [hermitianPairing, RCLike.inner_apply]

theorem scalar_hermitian_fourier (f g : 𝓢(V, ℂ)) :
    (∫ x : V, f x*starRingEnd ℂ (g x)) =
      ∫ ξ : V, 𝓕 f ξ*starRingEnd ℂ (𝓕 g ξ) := by
  simpa only [RCLike.inner_apply] using (SchwartzMap.integral_inner_fourier_fourier g f).symm

theorem same_cone_pairing_distinction (f : 𝓢(V, ℂ)) (hf : f≠0) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hs : Function.support (fun ξ => 𝓕 f ξ) ⊆ SingleConeReality.cone n δ) :
    bilinearPairing f f=0 ∧ 0<(hermitianPairing f f).re :=
  ⟨same_cone_bilinear_zero f f n δ hδ hs hs, hermitian_self_positive f hf⟩

theorem same_cone_pairings_unequal (f : 𝓢(V, ℂ)) (hf : f≠0) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hs : Function.support (fun ξ => 𝓕 f ξ) ⊆ SingleConeReality.cone n δ) :
    bilinearPairing f f≠hermitianPairing f f := by
  intro hh
  have hp := hermitian_self_positive f hf
  rw [← hh, same_cone_bilinear_zero f f n δ hδ hs hs] at hp
  simp at hp

theorem scalar_postcomp_fourier_support (f : 𝓢(V, H)) (L : H →L[ℂ] ℂ) :
    Function.support (fun ξ => 𝓕 (SchwartzMap.postcompCLM L f) ξ) ⊆
      Function.support (fun ξ => 𝓕 f ξ) := by
  intro ξ hξ
  intro hz
  change 𝓕 f ξ=0 at hz
  apply hξ
  change 𝓕 (SchwartzMap.postcompCLM L f) ξ=0
  rw [SingleConeReality.fourier_postcomp_scalar, hz, map_zero]

variable {ι : Type*} [Fintype ι]

def vectorBilinearPairing (f g : 𝓢(V, EuclideanSpace ℂ ι)) : ℂ :=
  ∫ x : V, ∑ i, f x i*g x i

theorem vector_product_integrable (f g : 𝓢(V, EuclideanSpace ℂ ι)) :
    Integrable (fun x : V => ∑ i, f x i*g x i) volume := by
  apply integrable_finsetSum
  intro i hi
  let L : EuclideanSpace ℂ ι →L[ℂ] ℂ := PiLp.proj 2 (fun _ : ι => ℂ) i
  exact product_integrable (SchwartzMap.postcompCLM L f) (SchwartzMap.postcompCLM L g)

theorem same_cone_vector_bilinear_zero (f g : 𝓢(V, EuclideanSpace ℂ ι))
    (n : V) (δ : ℝ) (hδ : δ≤1)
    (hf : Function.support (fun ξ => 𝓕 f ξ) ⊆ SingleConeReality.cone n δ)
    (hg : Function.support (fun ξ => 𝓕 g ξ) ⊆ SingleConeReality.cone n δ) :
    vectorBilinearPairing f g=0 := by
  unfold vectorBilinearPairing
  have hi (i : ι) : Integrable (fun x : V => f x i*g x i) volume := by
    let L : EuclideanSpace ℂ ι →L[ℂ] ℂ := PiLp.proj 2 (fun _ : ι => ℂ) i
    exact product_integrable (SchwartzMap.postcompCLM L f) (SchwartzMap.postcompCLM L g)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i hm
  let L : EuclideanSpace ℂ ι →L[ℂ] ℂ := PiLp.proj 2 (fun _ : ι => ℂ) i
  exact same_cone_bilinear_zero (SchwartzMap.postcompCLM L f) (SchwartzMap.postcompCLM L g)
    n δ hδ ((scalar_postcomp_fourier_support f L).trans hf)
    ((scalar_postcomp_fourier_support g L).trans hg)

theorem same_cone_vector_pairing_distinction (f : 𝓢(V, EuclideanSpace ℂ ι)) (hf : f≠0)
    (n : V) (δ : ℝ) (hδ : δ≤1)
    (hs : Function.support (fun ξ => 𝓕 f ξ) ⊆ SingleConeReality.cone n δ) :
    vectorBilinearPairing f f=0 ∧ 0<(hermitianPairing f f).re :=
  ⟨same_cone_vector_bilinear_zero f f n δ hδ hs hs, hermitian_self_positive f hf⟩

end OperatorDerivativeRewrite.Foundation.SingleConePairings
