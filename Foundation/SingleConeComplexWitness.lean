import Foundation.SingleConePairings
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Nonzero complex Schwartz witnesses in one Fourier cap. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.SingleConeComplexWitness
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem cone_mem_nhds (n : V) (hn : ‖n‖=1) (δ : ℝ) (hδ : 0<δ) :
    SingleConeReality.cone n δ ∈ 𝓝 n := by
  have hne : n≠0 := by
    intro hh
    simpa [hh] using hn
  have hd : ContinuousAt (SingleConeReality.direction : V → V) n :=
    (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hne)).smul continuousAt_id
  have he : SingleConeReality.direction n=n := by simp [SingleConeReality.direction, hn]
  have hz : ∀ᶠ ξ : V in 𝓝 n, ξ≠0 := isOpen_compl_singleton.mem_nhds hne
  have hs : ∀ᶠ ξ : V in 𝓝 n, ‖SingleConeReality.direction ξ-n‖<δ :=
    (hd.sub continuousAt_const).norm.tendsto.eventually
      (eventually_lt_nhds (by
        change ‖SingleConeReality.direction n-n‖<δ
        rwa [he, sub_self, norm_zero]))
  filter_upwards [hz, hs] with ξ hξ hsξ
  exact ⟨hξ, hsξ⟩

theorem exists_single_cone_schwartz_tsupport (n : V) (hn : ‖n‖=1) (δ : ℝ) (hδ : 0<δ) :
    ∃ f : 𝓢(V, ℂ), 𝓕 f n=1 ∧ f≠0 ∧
      tsupport (fun ξ => 𝓕 f ξ) ⊆ SingleConeReality.cone n δ := by
  obtain ⟨b, hs, hc, hd, hb, hval⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (cone_mem_nhds n hn δ hδ)
  let bR : 𝓢(V, ℝ) := hc.toSchwartzMap hd
  let bC : 𝓢(V, ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM bR
  let f : 𝓢(V, ℂ) := 𝓕⁻ bC
  have hF : 𝓕 f=bC := FourierTransform.fourier_fourierInv_eq _
  have hFn : 𝓕 f n=1 := by
    rw [hF]
    change (b n : ℂ)=1
    rw [hval]
    norm_num
  refine ⟨f, hFn, ?_, ?_⟩
  · intro hh
    simpa [hh] using hFn
  · have he : Function.support (fun ξ => 𝓕 f ξ)=Function.support b := by
      ext ξ
      change (𝓕 f ξ≠0) ↔ b ξ≠0
      rw [hF]
      change ((b ξ : ℂ)≠0) ↔ b ξ≠0
      simp
    change closure (Function.support (fun ξ => 𝓕 f ξ)) ⊆ _
    rw [he]
    exact hs

theorem exists_single_cone_schwartz (n : V) (hn : ‖n‖=1) (δ : ℝ) (hδ : 0<δ) :
    ∃ f : 𝓢(V, ℂ), 𝓕 f n=1 ∧ f≠0 ∧
      Function.support (fun ξ => 𝓕 f ξ) ⊆ SingleConeReality.cone n δ := by
  obtain ⟨f, hFn, hf, hs⟩ := exists_single_cone_schwartz_tsupport n hn δ hδ
  exact ⟨f, hFn, hf, (subset_tsupport _).trans hs⟩

theorem exists_pairing_witness (n : V) (hn : ‖n‖=1) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
    ∃ f : 𝓢(V, ℂ), f≠0 ∧
      Function.support (fun ξ => 𝓕 f ξ) ⊆ SingleConeReality.cone n δ ∧
      ¬(∀ x, starRingEnd ℂ (f x)=f x) ∧
      SingleConePairings.bilinearPairing f f=0 ∧
      0<(SingleConePairings.hermitianPairing f f).re ∧
      SingleConePairings.bilinearPairing f f≠SingleConePairings.hermitianPairing f f := by
  obtain ⟨f, hFn, hf, hs⟩ := exists_single_cone_schwartz n hn δ hδ
  refine ⟨f, hf, hs, ?_, ?_, ?_, ?_⟩
  · intro hr
    exact hf (SingleConeReality.real_schwartz_single_cone_zero f n δ hδ1 hr hs)
  · exact SingleConePairings.same_cone_bilinear_zero f f n δ hδ1 hs hs
  · exact SingleConePairings.hermitian_self_positive f hf
  · exact SingleConePairings.same_cone_pairings_unequal f hf n δ hδ1 hs

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem fourier_postcomp (f : 𝓢(V, ℂ)) (L : ℂ →L[ℂ] H) (ξ : V) :
    𝓕 (SchwartzMap.postcompCLM L f) ξ=L (𝓕 f ξ) := by
  change 𝓕 (fun x : V => L (f x)) ξ=L (𝓕 (f : V → ℂ) ξ)
  rw [Real.fourier_eq, Real.fourier_eq,
    ← L.integral_comp_comm ((Real.fourierIntegral_convergent_iff ξ).mpr f.integrable)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [Circle.smul_def]
  exact (L.map_smul _ _).symm

theorem exists_vector_cone_field (n : V) (hn : ‖n‖=1) (δ : ℝ) (hδ : 0<δ)
    (v : H) (hv : v≠0) : ∃ F : 𝓢(V, H), 𝓕 F n=v ∧ F≠0 ∧
      Function.support (fun ξ => 𝓕 F ξ) ⊆ SingleConeReality.cone n δ := by
  obtain ⟨f, hFn, hf, hs⟩ := exists_single_cone_schwartz n hn δ hδ
  let L : ℂ →L[ℂ] H := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  let F : 𝓢(V, H) := SchwartzMap.postcompCLM L f
  have hFn' : 𝓕 F n=v := by
    change 𝓕 (SchwartzMap.postcompCLM L f) n=v
    rw [fourier_postcomp, hFn]
    simp [L]
  refine ⟨F, hFn', ?_, ?_⟩
  · intro hh
    have hh' : (0:H)=v := by simpa [hh] using hFn'
    exact hv hh'.symm
  · intro ξ hξ
    apply hs
    intro hz
    change 𝓕 f ξ=0 at hz
    apply hξ
    change 𝓕 (SchwartzMap.postcompCLM L f) ξ=0
    rw [fourier_postcomp, hz, map_zero]

theorem exists_vector_pairing_witness {ι : Type*} [Fintype ι]
    (n : V) (hn : ‖n‖=1) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1)
    (v : EuclideanSpace ℂ ι) (hv : v≠0) :
    ∃ F : 𝓢(V, EuclideanSpace ℂ ι), 𝓕 F n=v ∧ F≠0 ∧
      Function.support (fun ξ => 𝓕 F ξ) ⊆ SingleConeReality.cone n δ ∧
      ¬(∀ x i, starRingEnd ℂ (F x i)=F x i) ∧
      SingleConePairings.vectorBilinearPairing F F=0 ∧
      0<(SingleConePairings.hermitianPairing F F).re := by
  obtain ⟨F, hFn, hF, hs⟩ := exists_vector_cone_field n hn δ hδ v hv
  refine ⟨F, hFn, hF, hs, ?_, ?_, ?_⟩
  · intro hr
    exact hF (SingleConeReality.real_vector_schwartz_single_cone_zero F n δ hδ1 hr hs)
  · exact SingleConePairings.same_cone_vector_bilinear_zero F F n δ hδ1 hs hs
  · exact SingleConePairings.hermitian_self_positive F hF

end OperatorDerivativeRewrite.Foundation.SingleConeComplexWitness
