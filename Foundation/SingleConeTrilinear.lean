import Foundation.DivergenceFreeConeWitness
import Mathlib.Analysis.Fourier.Convolution

/-! The literal bilinear trilinear integral on positive-frequency cone fields. -/
noncomputable section
open MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap Pointwise Convolution LineDeriv
namespace OperatorDerivativeRewrite.Foundation.SingleConeTrilinear
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def positiveHalfspace (n : V) : Set V := {ξ | 0 < inner ℝ ξ n}

theorem cone_subset_positive (n : V) (δ : ℝ) (hδ : δ≤1) :
    SingleConeReality.cone n δ ⊆ positiveHalfspace n := by
  intro ξ hξ
  have hd := norm_sub_sq_real (SingleConeReality.direction ξ) n
  rw [SingleConeReality.direction_norm hξ.1] at hd
  have hb : ‖SingleConeReality.direction ξ-n‖<1 := hξ.2.trans_le hδ
  have hp : 0 < inner ℝ (SingleConeReality.direction ξ) n := by
    nlinarith [norm_nonneg (SingleConeReality.direction ξ-n), sq_nonneg ‖n‖]
  have he : inner ℝ (SingleConeReality.direction ξ) n=‖ξ‖⁻¹*inner ℝ ξ n := by
    simp [SingleConeReality.direction, real_inner_smul_left]
  rw [he] at hp
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hξ.1))).mp hp

theorem positive_add (n : V) : positiveHalfspace n + positiveHalfspace n ⊆ positiveHalfspace n := by
  rintro ξ ⟨p, hp, q, hq, rfl⟩
  change 0 < inner ℝ (p+q) n
  rw [inner_add_left]
  exact add_pos hp hq

def product (f g : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g

theorem product_apply (f g : 𝓢(V, ℂ)) (x : V) : product f g x=f x*g x := rfl

theorem fourier_twice (f : 𝓢(V, ℂ)) (ξ : V) : 𝓕 (𝓕 f) ξ=f (-ξ) := by
  have hi : (𝓕⁻ (𝓕 f : 𝓢(V, ℂ)) : 𝓢(V, ℂ))=f := FourierTransform.fourierInv_fourier_eq f
  have hh := congrArg (fun h : 𝓢(V, ℂ) => h (-ξ)) hi
  simpa only [SingleConePairings.inverse_fourier_reflection, neg_neg] using hh

theorem fourier_product (f g : 𝓢(V, ℂ)) :
    𝓕 (product f g)=SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  have hh : 𝓕 (𝓕 (product f g))=
      𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g)) := by
    ext ξ
    rw [fourier_twice, SchwartzMap.fourier_convolution]
    change f (-ξ)*g (-ξ)=𝓕 (𝓕 f) ξ*𝓕 (𝓕 g) ξ
    rw [fourier_twice, fourier_twice]
  have hi := congrArg (fun h : 𝓢(V, ℂ) => 𝓕⁻ h) hh
  simpa using hi

theorem convolution_integrand_integrable (f g : 𝓢(V, ℂ)) (ξ : V) :
    Integrable (fun η : V => 𝓕 f η*𝓕 g (ξ-η)) volume := by
  have hg : AEStronglyMeasurable (fun η : V => 𝓕 g (ξ-η)) volume :=
    ((𝓕 g).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hb : ∀ᵐ η : V ∂volume,
      ‖𝓕 g (ξ-η)‖≤SchwartzMap.seminorm ℝ 0 0 (𝓕 g) :=
    Filter.Eventually.of_forall (fun η => SchwartzMap.norm_le_seminorm ℝ (𝓕 g) (ξ-η))
  exact (𝓕 f).integrable.mul_bdd hg hb

theorem fourier_product_support (f g : 𝓢(V, ℂ)) :
    Function.support (fun ξ => 𝓕 (product f g) ξ) ⊆
      Function.support (fun ξ => 𝓕 f ξ) + Function.support (fun ξ => 𝓕 g ξ) := by
  have he : (fun ξ => 𝓕 (product f g) ξ)=
      (((𝓕 f : 𝓢(V, ℂ)) : V → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        ((𝓕 g : 𝓢(V, ℂ)) : V → ℂ)) := by
    ext ξ
    rw [fourier_product, SchwartzMap.convolution_apply]
  rw [he]
  exact support_convolution_subset _

theorem positive_product_support (f g : 𝓢(V, ℂ)) (n : V)
    (hf : Function.support (fun ξ => 𝓕 f ξ) ⊆ positiveHalfspace n)
    (hg : Function.support (fun ξ => 𝓕 g ξ) ⊆ positiveHalfspace n) :
    Function.support (fun ξ => 𝓕 (product f g) ξ) ⊆ positiveHalfspace n :=
  (fourier_product_support f g).trans ((add_subset_add hf hg).trans (positive_add n))

theorem positive_bilinear_zero (f g : 𝓢(V, ℂ)) (n : V)
    (hf : Function.support (fun ξ => 𝓕 f ξ) ⊆ positiveHalfspace n)
    (hg : Function.support (fun ξ => 𝓕 g ξ) ⊆ positiveHalfspace n) :
    SingleConePairings.bilinearPairing f g=0 := by
  rw [SingleConePairings.bilinear_fourier_reflection]
  have hp : ∀ ξ : V, 𝓕 f ξ*𝓕 g (-ξ)=0 := by
    intro ξ
    by_cases hh : 𝓕 f ξ=0
    · rw [hh, zero_mul]
    · have hn : 𝓕 g (-ξ)=0 := by
        by_contra hz
        have hfp := hf hh
        have hgp := hg hz
        change 0 < inner ℝ ξ n at hfp
        change 0 < inner ℝ (-ξ) n at hgp
        rw [inner_neg_left] at hgp
        linarith
      rw [hn, mul_zero]
  simp only [hp, integral_zero]

theorem triple_integrable (f g h : 𝓢(V, ℂ)) :
    Integrable (fun x : V => f x*g x*h x) volume :=
  SingleConePairings.product_integrable (product f g) h

theorem positive_triple_zero (f g h : 𝓢(V, ℂ)) (n : V)
    (hf : Function.support (fun ξ => 𝓕 f ξ) ⊆ positiveHalfspace n)
    (hg : Function.support (fun ξ => 𝓕 g ξ) ⊆ positiveHalfspace n)
    (hh : Function.support (fun ξ => 𝓕 h ξ) ⊆ positiveHalfspace n) :
    (∫ x : V, f x*g x*h x)=0 := by
  exact positive_bilinear_zero (product f g) h n (positive_product_support f g n hf hg) hh

open DivergenceFreeConeWitness

theorem partial_fourier_support (f : 𝓢(Space, ℂ)) (i : Fin 3) :
    Function.support (fun ξ => 𝓕 (∂_{axis i} f) ξ) ⊆ Function.support (fun ξ => 𝓕 f ξ) := by
  intro ξ hξ hz
  change 𝓕 f ξ=0 at hz
  apply hξ
  change 𝓕 (∂_{axis i} f) ξ=0
  rw [fourier_partial, hz]
  ring

def trilinearSummand (u v w : 𝓢(Space, Values)) (i j : Fin 3) : 𝓢(Space, ℂ) :=
  product (product (coordinate i u) (∂_{axis i} (coordinate j v))) (coordinate j w)

theorem trilinearSummand_apply (u v w : 𝓢(Space, Values)) (i j : Fin 3) (x : Space) :
    trilinearSummand u v w i j x=
      u x i*(fderiv ℝ (fun y : Space => v y j) x (axis i))*w x j := rfl

def trilinear (u v w : 𝓢(Space, Values)) : ℂ :=
  ∫ x : Space, ∑ i : Fin 3, ∑ j : Fin 3,
    u x i*(fderiv ℝ (fun y : Space => v y j) x (axis i))*w x j

theorem trilinear_integrable (u v w : 𝓢(Space, Values)) :
    Integrable (fun x : Space => ∑ i : Fin 3, ∑ j : Fin 3,
      u x i*(fderiv ℝ (fun y : Space => v y j) x (axis i))*w x j) volume := by
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (trilinearSummand u v w i j).integrable

theorem cone_trilinear_zero (u v w : 𝓢(Space, Values)) (n : Space)
    (δ : ℝ) (hδ : δ≤1)
    (hu : Function.support (fun ξ => 𝓕 u ξ) ⊆ SingleConeReality.cone n δ)
    (hv : Function.support (fun ξ => 𝓕 v ξ) ⊆ SingleConeReality.cone n δ)
    (hw : Function.support (fun ξ => 𝓕 w ξ) ⊆ SingleConeReality.cone n δ) :
    trilinear u v w=0 := by
  have hc := cone_subset_positive n δ hδ
  have hU (i : Fin 3) : Function.support (fun ξ => 𝓕 (coordinate i u) ξ) ⊆ positiveHalfspace n :=
    (SingleConePairings.scalar_postcomp_fourier_support u (coordinateMap i)).trans (hu.trans hc)
  have hV (j : Fin 3) : Function.support (fun ξ => 𝓕 (coordinate j v) ξ) ⊆ positiveHalfspace n :=
    (SingleConePairings.scalar_postcomp_fourier_support v (coordinateMap j)).trans (hv.trans hc)
  have hW (j : Fin 3) : Function.support (fun ξ => 𝓕 (coordinate j w) ξ) ⊆ positiveHalfspace n :=
    (SingleConePairings.scalar_postcomp_fourier_support w (coordinateMap j)).trans (hw.trans hc)
  have hi (i j : Fin 3) : Integrable (fun x : Space =>
      u x i*(fderiv ℝ (fun y : Space => v y j) x (axis i))*w x j) volume :=
    (trilinearSummand u v w i j).integrable
  unfold trilinear
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_eq_zero
  intro i hmi
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_eq_zero
  intro j hmj
  exact positive_triple_zero (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w) n
    (hU i) ((partial_fourier_support _ i).trans (hV j)) (hW j)

theorem cone_trilinear_physical_bound (u v w : 𝓢(Space, Values)) (n : Space)
    (δ : ℝ) (hδ0 : 0≤δ) (hδ : δ≤1) (C : ℝ) (hC : 0≤C)
    (hu : tsupport (fun ξ => 𝓕 u ξ) ⊆ SingleConeReality.cone n δ)
    (hv : tsupport (fun ξ => 𝓕 v ξ) ⊆ SingleConeReality.cone n δ)
    (hw : tsupport (fun ξ => 𝓕 w ξ) ⊆ SingleConeReality.cone n δ) :
    ‖trilinear u v w‖ ≤ C*δ*
      ‖SchwartzFractionalL2Fields.physicalField (2*Real.pi) (by positivity) u 1‖*
      ‖SchwartzFractionalL2Fields.physicalField (2*Real.pi) (by positivity) v 3‖*
      ‖SchwartzFractionalL2Fields.physicalField (2*Real.pi) (by positivity) w 1‖ := by
  rw [cone_trilinear_zero u v w n δ hδ ((subset_tsupport _).trans hu)
    ((subset_tsupport _).trans hv) ((subset_tsupport _).trans hw), norm_zero]
  positivity

end OperatorDerivativeRewrite.Foundation.SingleConeTrilinear
