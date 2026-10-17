import Foundation.SingleConeTrilinear
import Mathlib.MeasureTheory.Group.Prod

/-! Proper double Fourier integrals for conjugated trilinear tests. -/
noncomputable section
open MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap Convolution LineDeriv
namespace OperatorDerivativeRewrite.Foundation.HermitianTriadFourier
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def conjugate (h : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap h
theorem conjugate_apply (h : 𝓢(V, ℂ)) (x : V) : conjugate h x=starRingEnd ℂ (h x) := rfl

def hermitianTriple (f g h : 𝓢(V, ℂ)) : ℂ := ∫ x : V, f x*g x*starRingEnd ℂ (h x)
def triadKernel (f g h : 𝓢(V, ℂ)) (z : V × V) : ℂ :=
  𝓕 f z.1*𝓕 g z.2*starRingEnd ℂ (𝓕 h (z.1+z.2))
def convolutionKernel (f g h : 𝓢(V, ℂ)) (z : V × V) : ℂ :=
  𝓕 f z.2*𝓕 g (z.1-z.2)*starRingEnd ℂ (𝓕 h z.1)

theorem hermitianTriple_integrable (f g h : 𝓢(V, ℂ)) :
    Integrable (fun x : V => f x*g x*starRingEnd ℂ (h x)) volume :=
  SingleConeTrilinear.triple_integrable f g (conjugate h)

theorem triadKernel_integrable (f g h : 𝓢(V, ℂ)) :
    Integrable (triadKernel f g h) ((volume : Measure V).prod volume) := by
  have hi : Integrable (fun z : V × V => 𝓕 f z.1*𝓕 g z.2)
      ((volume : Measure V).prod volume) :=
    (𝓕 f).integrable.mul_prod (𝓕 g).integrable
  have hm : AEStronglyMeasurable
      (fun z : V × V => starRingEnd ℂ (𝓕 h (z.1+z.2))) (volume.prod volume) :=
    (Complex.conjCLE.continuous.comp ((𝓕 h).continuous.comp
      (continuous_fst.add continuous_snd))).aestronglyMeasurable
  have hb : ∀ᵐ z : V × V ∂(volume.prod volume),
      ‖starRingEnd ℂ (𝓕 h (z.1+z.2))‖≤SchwartzMap.seminorm ℝ 0 0 (𝓕 h) := by
    apply Filter.Eventually.of_forall
    intro z
    simpa using SchwartzMap.norm_le_seminorm ℝ (𝓕 h) (z.1+z.2)
  exact hi.mul_bdd hm hb

def frequencyShear : (V × V) ≃ₜ (V × V) where
  toFun z := (z.2, z.1-z.2)
  invFun z := (z.1+z.2, z.1)
  left_inv z := by ext <;> dsimp <;> abel
  right_inv z := by ext <;> dsimp <;> abel
  continuous_toFun := continuous_snd.prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun := (continuous_fst.add continuous_snd).prodMk continuous_fst

theorem frequencyShear_preserving :
    MeasurePreserving (frequencyShear : V × V → V × V)
      ((volume : Measure V).prod volume) (volume.prod volume) :=
  (measurePreserving_prod_sub volume volume).comp Measure.measurePreserving_swap

theorem convolutionKernel_eq_comp (f g h : 𝓢(V, ℂ)) :
    convolutionKernel f g h=triadKernel f g h ∘ frequencyShear := by
  ext z
  dsimp [convolutionKernel, triadKernel, frequencyShear]
  rw [show z.2+(z.1-z.2)=z.1 by abel]

theorem convolutionKernel_integrable (f g h : 𝓢(V, ℂ)) :
    Integrable (convolutionKernel f g h) ((volume : Measure V).prod volume) := by
  rw [convolutionKernel_eq_comp]
  exact frequencyShear_preserving.integrable_comp_of_integrable (triadKernel_integrable f g h)

theorem shear_integral (f g h : 𝓢(V, ℂ)) :
    (∫ z : V × V, convolutionKernel f g h z ∂((volume : Measure V).prod volume)) =
      ∫ z : V × V, triadKernel f g h z ∂(volume.prod volume) := by
  rw [convolutionKernel_eq_comp]
  exact frequencyShear_preserving.integral_comp frequencyShear.measurableEmbedding _

theorem iterated_kernel_identity (f g h : 𝓢(V, ℂ)) :
    (∫ ξ : V, ∫ p : V, convolutionKernel f g h (ξ,p)) =
      ∫ p : V, ∫ q : V, triadKernel f g h (p,q) := by
  rw [← integral_prod _ (convolutionKernel_integrable f g h), shear_integral]
  exact integral_prod _ (triadKernel_integrable f g h)

theorem scalar_fourier_representation (f g h : 𝓢(V, ℂ)) :
    hermitianTriple f g h=∫ p : V, ∫ q : V, triadKernel f g h (p,q) := by
  calc
    _ = ∫ ξ : V, 𝓕 (SingleConeTrilinear.product f g) ξ*starRingEnd ℂ (𝓕 h ξ) := by
      simpa only [hermitianTriple, SingleConeTrilinear.product_apply] using
        SingleConePairings.scalar_hermitian_fourier (SingleConeTrilinear.product f g) h
    _ = ∫ ξ : V, ∫ p : V, convolutionKernel f g h (ξ,p) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ξ
      change 𝓕 (SingleConeTrilinear.product f g) ξ*starRingEnd ℂ (𝓕 h ξ)=
        ∫ p : V, convolutionKernel f g h (ξ,p)
      rw [SingleConeTrilinear.fourier_product, SchwartzMap.convolution_apply]
      change ((∫ p : V, 𝓕 f p*𝓕 g (ξ-p))*starRingEnd ℂ (𝓕 h ξ)) =
        ∫ p : V, convolutionKernel f g h (ξ,p)
      rw [← integral_mul_const]
      rfl
    _ = _ := iterated_kernel_identity f g h

theorem scalar_fourier_representation_prod (f g h : 𝓢(V, ℂ)) :
    hermitianTriple f g h=∫ z : V × V, triadKernel f g h z ∂((volume : Measure V).prod volume) := by
  rw [scalar_fourier_representation]
  exact (integral_prod _ (triadKernel_integrable f g h)).symm

open DivergenceFreeConeWitness

def vectorKernel (u v w : 𝓢(Space, Values)) (z : Space × Space) : ℂ :=
  kappa*(∑ i : Fin 3, 𝓕 u z.1 i*(z.2 i : ℂ))*
    (∑ j : Fin 3, 𝓕 v z.2 j*starRingEnd ℂ (𝓕 w (z.1+z.2) j))

def hermitianTrilinear (u v w : 𝓢(Space, Values)) : ℂ :=
  ∫ x : Space, ∑ i : Fin 3, ∑ j : Fin 3,
    u x i*(fderiv ℝ (fun y : Space => v y j) x (axis i))*starRingEnd ℂ (w x j)

theorem vectorKernel_eq_sum (u v w : 𝓢(Space, Values)) (z : Space × Space) :
    vectorKernel u v w z=∑ i : Fin 3, ∑ j : Fin 3,
      triadKernel (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w) z := by
  have ht (i j : Fin 3) :
      triadKernel (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w) z =
        kappa*(𝓕 u z.1 i*(z.2 i : ℂ))*
          (𝓕 v z.2 j*starRingEnd ℂ (𝓕 w (z.1+z.2) j)) := by
    unfold triadKernel
    rw [fourier_coordinate, fourier_partial, fourier_coordinate, fourier_coordinate]
    ring
  unfold vectorKernel
  simp_rw [ht, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem vectorKernel_integrable (u v w : 𝓢(Space, Values)) :
    Integrable (vectorKernel u v w) ((volume : Measure Space).prod volume) := by
  have he : vectorKernel u v w=(fun z : Space × Space => ∑ i : Fin 3, ∑ j : Fin 3,
      triadKernel (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w) z) :=
    funext (vectorKernel_eq_sum u v w)
  rw [he]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact triadKernel_integrable (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w)

theorem hermitianTrilinear_integrable (u v w : 𝓢(Space, Values)) :
    Integrable (fun x : Space => ∑ i : Fin 3, ∑ j : Fin 3,
      u x i*(fderiv ℝ (fun y : Space => v y j) x (axis i))*starRingEnd ℂ (w x j)) volume := by
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact hermitianTriple_integrable (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w)

theorem vector_fourier_representation_prod (u v w : 𝓢(Space, Values)) :
    hermitianTrilinear u v w=
      ∫ z : Space × Space, vectorKernel u v w z ∂((volume : Measure Space).prod volume) := by
  have hi (i j : Fin 3) : Integrable (fun x : Space =>
      u x i*(fderiv ℝ (fun y : Space => v y j) x (axis i))*starRingEnd ℂ (w x j)) volume :=
    hermitianTriple_integrable (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w)
  have hk (i j : Fin 3) : Integrable
      (triadKernel (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w))
        ((volume : Measure Space).prod volume) :=
    triadKernel_integrable (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w)
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        hermitianTriple (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w) := by
      unfold hermitianTrilinear
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i hmi
      rw [integral_finsetSum _ (fun j _ => hi i j)]
      rfl
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Space × Space,
          triadKernel (coordinate i u) (∂_{axis i} (coordinate j v)) (coordinate j w) z
            ∂((volume : Measure Space).prod volume) := by
      simp_rw [scalar_fourier_representation_prod]
    _ = _ := by
      simp_rw [vectorKernel_eq_sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hk i j))]
      apply Finset.sum_congr rfl
      intro i hmi
      rw [integral_finsetSum _ (fun j _ => hk i j)]

theorem vector_fourier_representation (u v w : 𝓢(Space, Values)) :
    hermitianTrilinear u v w=∫ p : Space, ∫ q : Space,
      kappa*(∑ i : Fin 3, 𝓕 u p i*(q i : ℂ))*
        (∑ j : Fin 3, 𝓕 v q j*starRingEnd ℂ (𝓕 w (p+q) j)) := by
  rw [vector_fourier_representation_prod]
  exact integral_prod _ (vectorKernel_integrable u v w)

end OperatorDerivativeRewrite.Foundation.HermitianTriadFourier
