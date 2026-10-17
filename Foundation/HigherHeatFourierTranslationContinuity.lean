import Foundation.HigherHeatFourierTranslations

/-! Strong and joint continuity of the actual Fourier path translation group. -/
noncomputable section
open Filter
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierTranslationContinuity
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach HigherHeatFourierTranslations

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem diagonal_difference_bound (a : Coeff) (h k : Path) (i : ℕ) :
    ‖a i * characterTest levels ξ i h-a i * characterTest levels ξ i k‖ ≤ 2*‖a i‖ := by
  simpa only [norm_mul, value_norm, mul_one, two_mul] using
    norm_sub_le (a i * characterTest levels ξ i h) (a i * characterTest levels ξ i k)

theorem diagonal_tendsto (a : Coeff) (h₀ : Path) :
    Tendsto (fun h => diagonal levels ξ h a) (𝓝 h₀) (𝓝 (diagonal levels ξ h₀ a)) := by
  have hi (i : ℕ) : Tendsto (fun h => ‖a i * characterTest levels ξ i h-
      a i * characterTest levels ξ i h₀‖) (𝓝 h₀) (𝓝 (0:ℝ)) := by
    have hc : Continuous (fun h => a i * characterTest levels ξ i h-a i * characterTest levels ξ i h₀) :=
      (continuous_const.mul (characterTest levels ξ i).continuous).sub continuous_const
    simpa only [sub_self, norm_zero] using hc.norm.tendsto h₀
  have ht := tendsto_tsum_of_dominated_convergence ((coeff_summable a).mul_left (2:ℝ)) hi
    (Eventually.of_forall (fun h i => by
      simpa only [Real.norm_eq_abs, abs_norm] using
        diagonal_difference_bound levels ξ a h h₀ i))
  have hs : Tendsto (fun h => ∑' i, ‖a i * characterTest levels ξ i h-
      a i * characterTest levels ξ i h₀‖) (𝓝 h₀) (𝓝 (0:ℝ)) := by simpa using ht
  have hn (h : Path) : ‖diagonal levels ξ h a-diagonal levels ξ h₀ a‖=
      ∑' i, ‖a i * characterTest levels ξ i h-a i * characterTest levels ξ i h₀‖ := by
    rw [← coeff_norm]
    apply tsum_congr
    intro i
    change ‖diagonal levels ξ h a i-diagonal levels ξ h₀ a i‖=_
    rw [diagonal_apply, diagonal_apply]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact hs.congr' (Eventually.of_forall fun h => (hn h).symm)

theorem diagonal_continuous (a : Coeff) : Continuous (fun h => diagonal levels ξ h a) :=
  continuous_iff_continuousAt.mpr (diagonal_tendsto levels ξ a)

theorem translation_strong_continuous (q : TestSpace levels ξ) :
    Continuous (fun h => translation levels ξ h q) := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  change Continuous (fun h => (kernel levels ξ).mkQL (diagonal levels ξ h a))
  exact (kernel levels ξ).mkQL.continuous.comp (diagonal_continuous levels ξ a)

theorem translation_difference_bound (h k : Path) (x y : TestSpace levels ξ) :
    ‖translation levels ξ h x-translation levels ξ k y‖ ≤
      ‖x-y‖+‖translation levels ξ h y-translation levels ξ k y‖ := by
  calc
    ‖translation levels ξ h x-translation levels ξ k y‖ =
        ‖(translation levels ξ h x-translation levels ξ h y)+
          (translation levels ξ h y-translation levels ξ k y)‖ := by congr 1; abel
    _ ≤ ‖translation levels ξ h x-translation levels ξ h y‖+
        ‖translation levels ξ h y-translation levels ξ k y‖ := norm_add_le _ _
    _ = _ := by rw [← map_sub, translation_norm]

theorem translation_jointly_continuous :
    Continuous (fun p : Path × TestSpace levels ξ => translation levels ξ p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h₁ : Tendsto (fun z : Path × TestSpace levels ξ => ‖z.2-p.2‖) (𝓝 p) (𝓝 (0:ℝ)) := by
    have hc : Continuous (fun z : Path × TestSpace levels ξ => z.2-p.2) := continuous_snd.sub continuous_const
    simpa only [sub_self, norm_zero] using hc.norm.tendsto p
  have h₂ : Tendsto (fun z : Path × TestSpace levels ξ =>
      ‖translation levels ξ z.1 p.2-translation levels ξ p.1 p.2‖) (𝓝 p) (𝓝 (0:ℝ)) := by
    have hc : Continuous (fun z : Path × TestSpace levels ξ =>
        translation levels ξ z.1 p.2-translation levels ξ p.1 p.2) :=
      ((translation_strong_continuous levels ξ p.2).comp continuous_fst).sub continuous_const
    simpa only [sub_self, norm_zero] using hc.norm.tendsto p
  have hb : Tendsto (fun z : Path × TestSpace levels ξ =>
      ‖z.2-p.2‖+‖translation levels ξ z.1 p.2-translation levels ξ p.1 p.2‖)
      (𝓝 p) (𝓝 (0:ℝ)) := by
    simpa only [zero_add] using h₁.add h₂
  exact squeeze_zero
    (fun z : Path × TestSpace levels ξ => norm_nonneg
      (translation levels ξ z.1 z.2-translation levels ξ p.1 p.2))
    (fun z => translation_difference_bound levels ξ z.1 p.1 z.2 p.2) hb

theorem scalePath_zero (h : Path) : scalePath 0 h=zeroPath := by apply Subtype.ext; exact zero_smul _ _

theorem scalePath_add (s t : ℝ) (h : Path) :
    scalePath (s+t) h=addPath (scalePath s h) (scalePath t h) := by
  apply Subtype.ext
  exact add_smul _ _ _

def along (h : Path) (t : ℝ) : TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  translation levels ξ (scalePath t h)

theorem along_zero (h : Path) (q : TestSpace levels ξ) : along levels ξ h 0 q=q := by
  change translation levels ξ (scalePath 0 h) q=q
  rw [scalePath_zero, translation_zero]

theorem along_add (h : Path) (s t : ℝ) (q : TestSpace levels ξ) :
    along levels ξ h s (along levels ξ h t q)=along levels ξ h (s+t) q := by
  change translation levels ξ (scalePath s h) (translation levels ξ (scalePath t h) q)=
    translation levels ξ (scalePath (s+t) h) q
  rw [scalePath_add, translation_add]

theorem along_norm (h : Path) (t : ℝ) (q : TestSpace levels ξ) : ‖along levels ξ h t q‖=‖q‖ :=
  translation_norm levels ξ _ q

theorem along_continuous (h : Path) (q : TestSpace levels ξ) : Continuous (fun t => along levels ξ h t q) :=
  (translation_strong_continuous levels ξ q).comp (scalePath_continuous h)

theorem along_tendsto_zero (h : Path) (q : TestSpace levels ξ) :
    Tendsto (fun t => along levels ξ h t q) (𝓝 0) (𝓝 q) := by
  have ht := (along_continuous levels ξ h q).tendsto 0
  rwa [along_zero] at ht

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierTranslationContinuity
