import Foundation.HigherHeatFourierTranslationContinuity

/-! Actual higher-heat evolution on the completed Fourier path test space. -/
noncomputable section
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathSemigroup
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach HigherHeatFourierTranslations

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def multiplier (m : ℕ) (T : ℝ≥0) (i : ℕ) : ℂ :=
  ∏ j : Fin (gridSize (spectrumLevels levels i)),
    HigherHeatL2.symbol m (duration T (spectrumLevels levels i))
      (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k)

theorem multiplier_bound (m : ℕ) (T : ℝ≥0) (i : ℕ) : ‖multiplier levels ξ m T i‖ ≤ 1 := by
  rw [multiplier, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun _ _ => HigherHeatL2.symbol_norm_le _ _ _)

theorem multiplier_zero (m : ℕ) (i : ℕ) : multiplier levels ξ m 0 i=1 := by
  simp [multiplier, duration, HigherHeatL2.symbol_zero]

theorem multiplier_add (m : ℕ) (S T : ℝ≥0) (i : ℕ) :
    multiplier levels ξ m (S+T) i=multiplier levels ξ m S i*multiplier levels ξ m T i := by
  simp only [multiplier, duration, add_div, HigherHeatL2.symbol_add, Finset.prod_mul_distrib]

theorem multiplier_expected (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    HigherHeatMixedFourierPaths.expectedCharacter (spectrumLevels levels)
      (spectrumFrequency levels ξ) m hm T hT i=multiplier levels ξ m T i := by
  unfold HigherHeatMixedFourierPaths.expectedCharacter
  rw [law, SignedDensityIntegral.positionLaw_fourier]
  rfl

def coefficientEvolution (m : ℕ) (T : ℝ≥0) : Coeff →L[ℂ] Coeff :=
  lp.mapCLM 1 (term (multiplier levels ξ m T)) zero_le_one
    (term_norm_le _ (multiplier_bound levels ξ m T))

theorem coefficientEvolution_apply (m : ℕ) (T : ℝ≥0) (a : Coeff) (i : ℕ) :
    coefficientEvolution levels ξ m T a i=a i*multiplier levels ξ m T i := rfl

theorem coefficientEvolution_bound (m : ℕ) (T : ℝ≥0) (a : Coeff) :
    ‖coefficientEvolution levels ξ m T a‖ ≤ ‖a‖ := by
  have hn : ‖coefficientEvolution levels ξ m T‖ ≤ 1 := lp.norm_mapCLM_le 1 _ _ _
  simpa only [one_mul] using (coefficientEvolution levels ξ m T).le_of_opNorm_le hn a

theorem coefficientEvolution_zero (m : ℕ) (a : Coeff) : coefficientEvolution levels ξ m 0 a=a := by
  apply Subtype.ext
  funext i
  change a i*multiplier levels ξ m 0 i=a i
  rw [multiplier_zero, mul_one]

theorem coefficientEvolution_add (m : ℕ) (S T : ℝ≥0) (a : Coeff) :
    coefficientEvolution levels ξ m S (coefficientEvolution levels ξ m T a)=
      coefficientEvolution levels ξ m (S+T) a := by
  apply Subtype.ext
  funext i
  change (a i*multiplier levels ξ m T i)*multiplier levels ξ m S i=
    a i*multiplier levels ξ m (S+T) i
  rw [multiplier_add]
  ring

theorem realization_evolution (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (ω : Path) :
    realization levels ξ (coefficientEvolution levels ξ m T a) ω=
      coefficientExpectation levels ξ m hm T hT (diagonal levels ξ ω a) := by
  rw [realization_apply, coefficientExpectation_apply]
  unfold HigherHeatMixedFourierPaths.series HigherHeatMixedFourierPaths.expectedSeries
  apply tsum_congr
  intro i
  change (a i*multiplier levels ξ m T i)*characterTest levels ξ i ω=
    (a i*characterTest levels ξ i ω)*_
  rw [multiplier_expected]
  ring

theorem evolution_preserves_kernel (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (a : Coeff) (ha : a ∈ kernel levels ξ) :
    coefficientEvolution levels ξ m T a ∈ kernel levels ξ := by
  by_cases hT : T=0
  · simpa only [hT, coefficientEvolution_zero] using ha
  have ht : 0 < T := lt_of_le_of_ne (show 0 ≤ T from bot_le) (Ne.symm hT)
  change realization levels ξ (coefficientEvolution levels ξ m T a)=0
  ext ω
  rw [realization_evolution levels ξ m hm T ht]
  exact kernel_le_expectation levels ξ m hm T ht
    (diagonal_preserves_kernel levels ξ ω a ha)

theorem evolution_kernel (m : ℕ) (hm : 0 < m) (T : ℝ≥0) :
    kernel levels ξ ≤
      (((kernel levels ξ).mkQL).comp (coefficientEvolution levels ξ m T)).ker := by
  intro a ha
  change (kernel levels ξ).mkQ (coefficientEvolution levels ξ m T a)=0
  exact (Submodule.Quotient.mk_eq_zero _).mpr (evolution_preserves_kernel levels ξ m hm T a ha)

def evolution (m : ℕ) (hm : 0 < m) (T : ℝ≥0) :
    TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  (kernel levels ξ).liftQL (((kernel levels ξ).mkQL).comp (coefficientEvolution levels ξ m T))
    (evolution_kernel levels ξ m hm T)

theorem evolution_mk (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (a : Coeff) :
    evolution levels ξ m hm T ((kernel levels ξ).mkQ a)=
      (kernel levels ξ).mkQ (coefficientEvolution levels ξ m T a) := rfl

theorem evolution_zero (m : ℕ) (hm : 0 < m) (q : TestSpace levels ξ) :
    evolution levels ξ m hm 0 q=q := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [evolution_mk, coefficientEvolution_zero]

theorem evolution_add (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (q : TestSpace levels ξ) :
    evolution levels ξ m hm S (evolution levels ξ m hm T q)=
      evolution levels ξ m hm (S+T) q := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [evolution_mk, evolution_mk, evolution_mk, coefficientEvolution_add]

theorem evolution_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (q : TestSpace levels ξ) :
    ‖evolution levels ξ m hm T q‖ ≤ ‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,hna⟩ := Submodule.Quotient.norm_mk_lt q hε
  have he : evolution levels ξ m hm T q=
      (kernel levels ξ).mkQ (coefficientEvolution levels ξ m T a) := by
    rw [← ha]
    rfl
  rw [he]
  exact (Submodule.Quotient.norm_mk_le _ _).trans
    ((coefficientEvolution_bound levels ξ m T a).trans hna.le)

theorem realize_evolution (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : Path) :
    realize levels ξ (evolution levels ξ m hm T q) ω=
      expectation levels ξ m hm T hT (translation levels ξ ω q) := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [evolution_mk, realize_mk, translation_mk, expectation_mk, realization_evolution]

theorem expectation_at_zero (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) :
    realize levels ξ (evolution levels ξ m hm T q) zeroPath=expectation levels ξ m hm T hT q := by
  rw [realize_evolution levels ξ m hm T hT, translation_zero]

theorem evolution_translation (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (h : Path) (q : TestSpace levels ξ) :
    evolution levels ξ m hm T (translation levels ξ h q)=
      translation levels ξ h (evolution levels ξ m hm T q) := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [translation_mk, evolution_mk, evolution_mk, translation_mk]
  congr 1
  apply Subtype.ext
  funext i
  change (a i*characterTest levels ξ i h)*multiplier levels ξ m T i=
    (a i*multiplier levels ξ m T i)*characterTest levels ξ i h
  ring

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathSemigroup
