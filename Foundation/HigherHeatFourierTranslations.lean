import Foundation.HigherHeatFourierBanach

/-! Actual isometric path translations on the completed Fourier test space. -/
noncomputable section
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierTranslations
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach

def zeroPath : Path := ⟨0, rfl⟩

def addPath (h ω : Path) : Path := ⟨h.val+ω.val, by simp [h.property, ω.property]⟩

def negPath (h : Path) : Path := ⟨-h.val, by simp [h.property]⟩

def scalePath (t : ℝ) (h : Path) : Path := ⟨t • h.val, by simp [h.property]⟩

theorem addPath_zero (h : Path) : addPath h zeroPath=h := by apply Subtype.ext; exact add_zero _

theorem zero_addPath (h : Path) : addPath zeroPath h=h := by apply Subtype.ext; exact zero_add _

theorem addPath_comm (h k : Path) : addPath h k=addPath k h := by apply Subtype.ext; exact add_comm _ _

theorem addPath_assoc (h k ω : Path) : addPath (addPath h k) ω=addPath h (addPath k ω) := by
  apply Subtype.ext
  exact add_assoc _ _ _

theorem addPath_neg (h : Path) : addPath h (negPath h)=zeroPath := by apply Subtype.ext; exact add_neg_cancel _

theorem neg_addPath (h : Path) : addPath (negPath h) h=zeroPath := by apply Subtype.ext; exact neg_add_cancel _

theorem addPath_continuous : Continuous (fun p : Path × Path => addPath p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

theorem shift_continuous (h : Path) : Continuous (addPath h) :=
  addPath_continuous.comp (continuous_const.prodMk continuous_id)

theorem scalePath_continuous (h : Path) : Continuous (fun t => scalePath t h) := by
  apply Continuous.subtype_mk
  exact continuous_id.smul continuous_const

theorem configurationPhase_add {ι : Type*} [Fintype ι] (ξ x y : ι → ℝ) :
    SignedDensityIntegral.configurationPhase ξ (x+y)=
      SignedDensityIntegral.configurationPhase ξ x * SignedDensityIntegral.configurationPhase ξ y := by
  unfold SignedDensityIntegral.configurationPhase
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem value_norm (h : Path) (i : ℕ) : ‖characterTest levels ξ i h‖=1 :=
  HigherHeatMixedFourierPaths.character_norm _ _ i h

theorem value_add (h ω : Path) (i : ℕ) : characterTest levels ξ i (addPath h ω)=
    characterTest levels ξ i h * characterTest levels ξ i ω := by
  change SignedDensityIntegral.configurationPhase (spectrumFrequency levels ξ i)
    (sample (spectrumLevels levels i) (addPath h ω))=_
  have hs : sample (spectrumLevels levels i) (addPath h ω)=
      sample (spectrumLevels levels i) h+sample (spectrumLevels levels i) ω := rfl
  rw [hs, configurationPhase_add]
  rfl

theorem value_zero (i : ℕ) : characterTest levels ξ i zeroPath=1 := by
  change SignedDensityIntegral.configurationPhase (spectrumFrequency levels ξ i)
    (0 : Grid (spectrumLevels levels i))=1
  simp [SignedDensityIntegral.configurationPhase]

def diagonal (h : Path) : Coeff →L[ℂ] Coeff :=
  lp.mapCLM 1 (term (fun i => characterTest levels ξ i h)) zero_le_one
    (term_norm_le _ (fun i => (value_norm levels ξ h i).le))

theorem diagonal_apply (h : Path) (a : Coeff) (i : ℕ) :
    diagonal levels ξ h a i=a i * characterTest levels ξ i h := rfl

theorem diagonal_bound (h : Path) (a : Coeff) : ‖diagonal levels ξ h a‖ ≤ ‖a‖ := by
  have hn : ‖diagonal levels ξ h‖ ≤ 1 := lp.norm_mapCLM_le 1 _ _ _
  simpa only [one_mul] using (diagonal levels ξ h).le_of_opNorm_le hn a

theorem realization_diagonal (h ω : Path) (a : Coeff) :
    realization levels ξ (diagonal levels ξ h a) ω=realization levels ξ a (addPath h ω) := by
  rw [realization_apply, realization_apply]
  unfold HigherHeatMixedFourierPaths.series
  apply tsum_congr
  intro i
  change (a i * characterTest levels ξ i h) * characterTest levels ξ i ω=
    a i * characterTest levels ξ i (addPath h ω)
  rw [value_add, mul_assoc]

theorem diagonal_preserves_kernel (h : Path) (a : Coeff) (ha : a ∈ kernel levels ξ) :
    diagonal levels ξ h a ∈ kernel levels ξ := by
  change realization levels ξ a=0 at ha
  change realization levels ξ (diagonal levels ξ h a)=0
  ext ω
  rw [realization_diagonal, ha]
  rfl

theorem translation_kernel (h : Path) :
    kernel levels ξ ≤ (((kernel levels ξ).mkQL).comp (diagonal levels ξ h)).ker := by
  intro a ha
  change (kernel levels ξ).mkQ (diagonal levels ξ h a)=0
  exact (Submodule.Quotient.mk_eq_zero _).mpr (diagonal_preserves_kernel levels ξ h a ha)

def translation (h : Path) : TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  (kernel levels ξ).liftQL (((kernel levels ξ).mkQL).comp (diagonal levels ξ h))
    (translation_kernel levels ξ h)

theorem translation_mk (h : Path) (a : Coeff) :
    translation levels ξ h ((kernel levels ξ).mkQ a)=(kernel levels ξ).mkQ (diagonal levels ξ h a) := rfl

theorem realize_translation (h : Path) (q : TestSpace levels ξ) (ω : Path) :
    realize levels ξ (translation levels ξ h q) ω=realize levels ξ q (addPath h ω) := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [translation_mk, realize_mk, realize_mk, realization_diagonal]

theorem translation_zero (q : TestSpace levels ξ) : translation levels ξ zeroPath q=q := by
  apply realize_injective levels ξ
  ext ω
  rw [realize_translation, zero_addPath]

theorem translation_add (h k : Path) (q : TestSpace levels ξ) :
    translation levels ξ h (translation levels ξ k q)=translation levels ξ (addPath h k) q := by
  apply realize_injective levels ξ
  ext ω
  rw [realize_translation, realize_translation, realize_translation, ← addPath_assoc, addPath_comm k h]

theorem translation_bound (h : Path) (q : TestSpace levels ξ) : ‖translation levels ξ h q‖ ≤ ‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,hna⟩ := Submodule.Quotient.norm_mk_lt q hε
  have he : translation levels ξ h q=(kernel levels ξ).mkQ (diagonal levels ξ h a) := by
    rw [← ha]
    rfl
  rw [he]
  exact (Submodule.Quotient.norm_mk_le _ _).trans ((diagonal_bound levels ξ h a).trans hna.le)

theorem translation_norm (h : Path) (q : TestSpace levels ξ) : ‖translation levels ξ h q‖=‖q‖ := by
  apply le_antisymm (translation_bound levels ξ h q)
  have hh := translation_bound levels ξ (negPath h) (translation levels ξ h q)
  rwa [translation_add, neg_addPath, translation_zero] at hh

def translationEquiv (h : Path) : TestSpace levels ξ ≃ₗᵢ[ℂ] TestSpace levels ξ where
  toLinearEquiv :=
    { toLinearMap := (translation levels ξ h).toLinearMap
      invFun := translation levels ξ (negPath h)
      left_inv q := by
        change translation levels ξ (negPath h) (translation levels ξ h q)=q
        rw [translation_add, neg_addPath, translation_zero]
      right_inv q := by
        change translation levels ξ h (translation levels ξ (negPath h) q)=q
        rw [translation_add, addPath_neg, translation_zero] }
  norm_map' := translation_norm levels ξ h

theorem translation_generator (h : Path) (i : ℕ) :
    translation levels ξ h (generator levels ξ i)=characterTest levels ξ i h • generator levels ξ i := by
  apply realize_injective levels ξ
  ext ω
  rw [realize_translation, map_smul, realize_generator]
  exact value_add levels ξ h ω i

theorem translation_unit (h : Path) : translation levels ξ h (unit levels ξ)=unit levels ξ := by
  apply realize_injective levels ξ
  ext ω
  rw [realize_translation, realize_unit]
  rfl

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierTranslations
