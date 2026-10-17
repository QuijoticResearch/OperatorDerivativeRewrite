import Foundation.SingleConeComplexWitness

/-! An actual complex divergence-free Schwartz witness in a three-dimensional Fourier cap. -/
noncomputable section
open MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap LineDeriv
namespace OperatorDerivativeRewrite.Foundation.DivergenceFreeConeWitness
set_option backward.isDefEq.respectTransparency false

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Values := EuclideanSpace ℂ (Fin 3)
def axis (i : Fin 3) : Space := EuclideanSpace.basisFun (Fin 3) ℝ i
def kappa : ℂ := 2*(Real.pi : ℂ)*Complex.I
def coordinateMap (i : Fin 3) : Values →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 3 => ℂ) i
def coordinate (i : Fin 3) (F : 𝓢(Space, Values)) : 𝓢(Space, ℂ) :=
  SchwartzMap.postcompCLM (coordinateMap i) F
def lift (i : Fin 3) (f : 𝓢(Space, ℂ)) : 𝓢(Space, Values) :=
  SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight
    (EuclideanSpace.single i (1:ℂ))) f
def curlField (f : 𝓢(Space, ℂ)) : 𝓢(Space, Values) :=
  lift 0 (∂_{axis 1} f) + -(lift 1 (∂_{axis 0} f))
def divergence (F : 𝓢(Space, Values)) : 𝓢(Space, ℂ) :=
  ∑ i : Fin 3, ∂_{axis i} (coordinate i F)

theorem axis_norm (i : Fin 3) : ‖axis i‖=1 := by
  simp [axis, PiLp.norm_single]

theorem kappa_ne_zero : kappa≠0 := by simp [kappa, Real.pi_ne_zero]

theorem fourier_partial (f : 𝓢(Space, ℂ)) (i : Fin 3) (ξ : Space) :
    𝓕 (∂_{axis i} f) ξ=kappa*(ξ i : ℂ)*𝓕 f ξ := by
  have hg : (inner ℝ · (axis i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (axis i)).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
  change kappa • ((inner ℝ ξ (axis i)) • 𝓕 f ξ)=kappa*(ξ i : ℂ)*𝓕 f ξ
  simp only [axis, EuclideanSpace.inner_basisFun_real]
  change kappa*((ξ i : ℂ)*𝓕 f ξ)=kappa*(ξ i : ℂ)*𝓕 f ξ
  ring

theorem fourier_lift (f : 𝓢(Space, ℂ)) (i : Fin 3) (ξ : Space) :
    𝓕 (lift i f) ξ=𝓕 f ξ • EuclideanSpace.single i (1:ℂ) :=
  SingleConeComplexWitness.fourier_postcomp f _ ξ

theorem fourier_curl (f : 𝓢(Space, ℂ)) (ξ : Space) :
    𝓕 (curlField f) ξ =
      (kappa*(ξ 1 : ℂ)*𝓕 f ξ) • EuclideanSpace.single 0 (1:ℂ) +
        -((kappa*(ξ 0 : ℂ)*𝓕 f ξ) • EuclideanSpace.single 1 (1:ℂ)) := by
  simp only [curlField, FourierTransform.fourier_add, FourierTransform.fourier_neg,
    add_apply, neg_apply, fourier_lift, fourier_partial]

theorem fourier_curl_zero (f : 𝓢(Space, ℂ)) (ξ : Space) :
    𝓕 (curlField f) ξ 0=kappa*(ξ 1 : ℂ)*𝓕 f ξ := by
  rw [fourier_curl]
  simp

theorem fourier_curl_one (f : 𝓢(Space, ℂ)) (ξ : Space) :
    𝓕 (curlField f) ξ 1= -(kappa*(ξ 0 : ℂ)*𝓕 f ξ) := by
  rw [fourier_curl]
  simp

theorem fourier_curl_two (f : 𝓢(Space, ℂ)) (ξ : Space) : 𝓕 (curlField f) ξ 2=0 := by
  rw [fourier_curl]
  simp

theorem fourier_coordinate (F : 𝓢(Space, Values)) (i : Fin 3) (ξ : Space) :
    𝓕 (coordinate i F) ξ=𝓕 F ξ i :=
  SingleConeReality.fourier_postcomp_scalar F (coordinateMap i) ξ

theorem divergence_apply (F : 𝓢(Space, Values)) (x : Space) :
    divergence F x=∑ i : Fin 3, fderiv ℝ (fun y : Space => F y i) x (axis i) := by
  simp only [divergence, sum_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

theorem fourier_divergence (F : 𝓢(Space, Values)) (ξ : Space) :
    𝓕 (divergence F) ξ=kappa*∑ i : Fin 3, (ξ i : ℂ)*𝓕 F ξ i := by
  simp only [divergence, FourierTransform.fourier_sum, sum_apply, fourier_partial,
    fourier_coordinate, Finset.mul_sum, mul_assoc]

theorem curl_divergence_zero (f : 𝓢(Space, ℂ)) : divergence (curlField f)=0 := by
  have hh : 𝓕 (divergence (curlField f))=0 := by
    ext ξ
    change 𝓕 (divergence (curlField f)) ξ=(0:ℂ)
    rw [fourier_divergence, Fin.sum_univ_three, fourier_curl_zero, fourier_curl_one,
      fourier_curl_two]
    ring
  have hi := congrArg (fun h : 𝓢(Space, ℂ) => 𝓕⁻ h) hh
  simpa using hi

theorem curl_physical_divergence (f : 𝓢(Space, ℂ)) (x : Space) :
    (∑ i : Fin 3, fderiv ℝ (fun y : Space => curlField f y i) x (axis i))=0 := by
  have hh := congrArg (fun h : 𝓢(Space, ℂ) => h x) (curl_divergence_zero f)
  simpa only [divergence_apply, zero_apply] using hh

theorem curl_fourier_support (f : 𝓢(Space, ℂ)) :
    Function.support (fun ξ => 𝓕 (curlField f) ξ) ⊆ Function.support (fun ξ => 𝓕 f ξ) := by
  intro ξ hξ hz
  change 𝓕 f ξ=0 at hz
  apply hξ
  change 𝓕 (curlField f) ξ=0
  rw [fourier_curl, hz]
  simp

theorem curl_fourier_tsupport (f : 𝓢(Space, ℂ)) :
    tsupport (fun ξ => 𝓕 (curlField f) ξ) ⊆ tsupport (fun ξ => 𝓕 f ξ) :=
  closure_mono (curl_fourier_support f)

theorem curl_nonzero_at_axis (f : 𝓢(Space, ℂ)) (hf : 𝓕 f (axis 0)=1) : curlField f≠0 := by
  have hh : 𝓕 (curlField f) (axis 0) 1= -kappa := by
    rw [fourier_curl_one, hf]
    simp [axis]
  intro hz
  have he : (0:ℂ)= -kappa := by simpa [hz] using hh
  exact kappa_ne_zero (neg_eq_zero.mp he.symm)

theorem exists_divergence_free_cone_witness (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
    ∃ F : 𝓢(Space, Values), F≠0 ∧
      tsupport (fun ξ => 𝓕 F ξ) ⊆ SingleConeReality.cone (axis 0) δ ∧
      (∀ x, (∑ i : Fin 3, fderiv ℝ (fun y : Space => F y i) x (axis i))=0) ∧
      ¬(∀ x i, starRingEnd ℂ (F x i)=F x i) ∧
      SingleConePairings.vectorBilinearPairing F F=0 ∧
      0<(SingleConePairings.hermitianPairing F F).re := by
  obtain ⟨f, hfn, hf, hs⟩ :=
    SingleConeComplexWitness.exists_single_cone_schwartz_tsupport (axis 0) (axis_norm 0) δ hδ
  have hF := curl_nonzero_at_axis f hfn
  have hS := (curl_fourier_tsupport f).trans hs
  have hSf := (subset_tsupport _).trans hS
  refine ⟨curlField f, hF, hS, curl_physical_divergence f, ?_,
    SingleConePairings.same_cone_vector_bilinear_zero _ _ (axis 0) δ hδ1 hSf hSf,
    SingleConePairings.hermitian_self_positive _ hF⟩
  intro hr
  exact hF (SingleConeReality.real_vector_schwartz_single_cone_zero _ _ δ hδ1 hr hSf)

end OperatorDerivativeRewrite.Foundation.DivergenceFreeConeWitness
