import Foundation.ConeInteractionCore

/-! Narrow cone addition and closed nonlinear Fourier support. -/
noncomputable section
open MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap Pointwise LineDeriv
namespace OperatorDerivativeRewrite.Foundation.ConeSupportAlgebra
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def slope (δ : ℝ) : ℝ := 2-δ^2

theorem cone_linear_iff (n : V) (hn : ‖n‖=1) (δ : ℝ) (hδ : 0<δ) (ξ : V) (hξ : ξ≠0) :
    ξ∈SingleConeReality.cone n δ ↔ slope δ*‖ξ‖<2*inner ℝ ξ n := by
  have hr : 0<‖ξ‖ := norm_pos_iff.mpr hξ
  have hd := norm_sub_sq_real (SingleConeReality.direction ξ) n
  rw [SingleConeReality.direction_norm hξ, hn] at hd
  have he : ‖ξ‖*inner ℝ (SingleConeReality.direction ξ) n=inner ℝ ξ n := by
    simp only [SingleConeReality.direction, real_inner_smul_left]
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  constructor
  · intro hc
    have hsq := (sq_lt_sq₀ (norm_nonneg (SingleConeReality.direction ξ-n)) hδ.le).mpr hc.2
    have hi : slope δ<2*inner ℝ (SingleConeReality.direction ξ) n := by
      dsimp [slope]
      nlinarith
    have hm := mul_lt_mul_of_pos_left hi hr
    nlinarith [he]
  · intro hc
    have hi : slope δ<2*inner ℝ (SingleConeReality.direction ξ) n := by
      by_contra hh
      have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hh) hr.le
      nlinarith [he]
    have hsq : ‖SingleConeReality.direction ξ-n‖^2<δ^2 := by
      dsimp [slope] at hi
      nlinarith
    exact ⟨hξ, (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp hsq⟩

theorem cone_add_mem [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : ‖n‖=1) (δ : ℝ) (hδ0 : 0<δ) (hδ1 : δ≤1) {p q : V}
    (hp : p∈SingleConeReality.cone n δ) (hq : q∈SingleConeReality.cone n δ) :
    p+q∈SingleConeReality.cone n δ := by
  have hpn := SingleConeTrilinear.cone_subset_positive n δ hδ1 hp
  have hqn := SingleConeTrilinear.cone_subset_positive n δ hδ1 hq
  have hs : 0 < inner ℝ (p+q) n := by
    rw [inner_add_left]
    exact add_pos hpn hqn
  have hne : p+q≠0 := by intro hh; simpa [hh] using hs
  have hp' := (cone_linear_iff n hn δ hδ0 p hp.1).mp hp
  have hq' := (cone_linear_iff n hn δ hδ0 q hq.1).mp hq
  have hsq : δ^2≤1 := by simpa using (sq_le_sq₀ hδ0.le zero_le_one).mpr hδ1
  have hsl : 0≤slope δ := by dsimp [slope]; linarith
  have hm := mul_le_mul_of_nonneg_left (norm_add_le p q) hsl
  apply (cone_linear_iff n hn δ hδ0 (p+q) hne).mpr
  rw [inner_add_left]
  nlinarith

theorem cone_add_subset [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : ‖n‖=1) (δ : ℝ) (hδ0 : 0<δ) (hδ1 : δ≤1) :
    SingleConeReality.cone n δ + SingleConeReality.cone n δ ⊆ SingleConeReality.cone n δ := by
  rintro ξ ⟨p, hp, q, hq, rfl⟩
  exact cone_add_mem n hn δ hδ0 hδ1 hp hq

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem product_tsupport_subset_sum (f g : 𝓢(V, ℂ)) (A : Set V) (hA : IsCompact A)
    (hf : tsupport (fun ξ => 𝓕 f ξ) ⊆ A) (hg : tsupport (fun ξ => 𝓕 g ξ) ⊆ A) :
    tsupport (fun ξ => 𝓕 (SingleConeTrilinear.product f g) ξ) ⊆ A+A := by
  apply (hA.add hA).isClosed.closure_subset_iff.mpr
  exact (SingleConeTrilinear.fourier_product_support f g).trans
    (add_subset_add ((subset_tsupport _).trans hf) ((subset_tsupport _).trans hg))

open DivergenceFreeConeWitness ConeInteractionCore

theorem fourier_advect_coordinate (u v : 𝓢(Space, Values)) (j : Fin 3) (ξ : Space) :
    𝓕 (advect u v) ξ j=𝓕 (advectComponent u v j) ξ := by
  have he : coordinate j (advect u v)=advectComponent u v j := by
    ext x
    exact advect_apply u v x j
  rw [← fourier_coordinate, he]

theorem advect_tsupport_subset_sum (u v : 𝓢(Space, Values)) (A : Set Space) (hA : IsCompact A)
    (hu : tsupport (fun ξ => 𝓕 u ξ) ⊆ A) (hv : tsupport (fun ξ => 𝓕 v ξ) ⊆ A) :
    tsupport (fun ξ => 𝓕 (advect u v) ξ) ⊆ A+A := by
  have hU (i : Fin 3) : tsupport (fun ξ => 𝓕 (coordinate i u) ξ) ⊆ A :=
    (closure_mono (SingleConePairings.scalar_postcomp_fourier_support u (coordinateMap i))).trans hu
  have hV (i j : Fin 3) : tsupport (fun ξ => 𝓕 (∂_{axis i} (coordinate j v)) ξ) ⊆ A :=
    (closure_mono (SingleConeTrilinear.partial_fourier_support _ i)).trans
      ((closure_mono (SingleConePairings.scalar_postcomp_fourier_support v (coordinateMap j))).trans hv)
  have hP (i j : Fin 3) : tsupport (fun ξ =>
      𝓕 (SingleConeTrilinear.product (coordinate i u) (∂_{axis i} (coordinate j v))) ξ) ⊆ A+A :=
    product_tsupport_subset_sum _ _ A hA (hU i) (hV i j)
  apply (hA.add hA).isClosed.closure_subset_iff.mpr
  intro ξ hξ
  by_contra hout
  apply hξ
  ext j
  change 𝓕 (advect u v) ξ j=0
  rw [fourier_advect_coordinate]
  simp only [advectComponent, FourierTransform.fourier_sum, sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hh
  exact hout (hP i j ((subset_tsupport _) hh))

theorem bumpField_tsupport_bump {δ : ℝ} (B : SpectralBump δ) :
    tsupport (fun ξ => 𝓕 (bumpField B) ξ) ⊆ tsupport B.b := by
  apply closure_mono
  intro ξ hξ
  change B.b ξ≠0
  intro hz
  apply hξ
  change 𝓕 (bumpField B) ξ=0
  rw [fourier_bumpField, hz]
  rfl

theorem inputU_tsupport_bump {δ : ℝ} (B : SpectralBump δ) :
    tsupport (fun ξ => 𝓕 (inputU B) ξ) ⊆ tsupport B.b :=
  (curl_fourier_tsupport _).trans (bumpField_tsupport_bump B)

theorem inputV_tsupport_bump {δ : ℝ} (B : SpectralBump δ) :
    tsupport (fun ξ => 𝓕 (inputV B) ξ) ⊆ tsupport B.b :=
  (curl02_fourier_tsupport _).trans
    ((closure_mono (SingleConeTrilinear.partial_fourier_support _ 1)).trans (bumpField_tsupport_bump B))

theorem advection_tsupport_cone {δ : ℝ} (B : SpectralBump δ) (hδ0 : 0<δ) (hδ1 : δ≤1) :
    tsupport (fun ξ => 𝓕 (advect (inputU B) (inputV B)) ξ) ⊆
      SingleConeReality.cone (axis 0) δ :=
  (advect_tsupport_subset_sum _ _ (tsupport B.b) B.compact (inputU_tsupport_bump B)
    (inputV_tsupport_bump B)).trans
      ((add_subset_add B.support B.support).trans
        (cone_add_subset (axis 0) (axis_norm 0) δ hδ0 hδ1))

end OperatorDerivativeRewrite.Foundation.ConeSupportAlgebra
