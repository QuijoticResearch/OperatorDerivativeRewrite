import Foundation.IBMClippedClockLimit

/-! Actual bounded current/terminal multipliers of centered clock increments.
Products used to control cross-cell energies retain their generated domains. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianTerminalBracketProducts
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence GaussianTimeSpaceHermite GaussianTimeFieldNorm
open GaussianTerminalBracketPrediction GaussianConditionalGraph IBMTerminalBracketWeights

private theorem product_memLp (f : GaussianL2) (b : SampleSpace → ℝ)
    (hm : Measurable b) (hb : ∀ Y, ‖b Y‖ ≤ 1) :
    MemLp (fun Y => f Y*b Y) 2 gaussianProduct := by
  apply (Lp.memLp f).norm.mono' ((Lp.memLp f).aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact ae_of_all _ fun Y => by
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb Y)

private def product (f : GaussianL2) (b : SampleSpace → ℝ)
    (hm : Measurable b) (hb : ∀ Y, ‖b Y‖ ≤ 1) : GaussianL2 :=
  (product_memLp f b hm hb).toLp _

private theorem product_actual (f : GaussianL2) (b : SampleSpace → ℝ)
    (hm : Measurable b) (hb : ∀ Y, ‖b Y‖ ≤ 1) :
    product f b hm hb =ᵐ[gaussianProduct] fun Y => f Y*b Y :=
  (product_memLp f b hm hb).coeFn_toLp

private theorem product_norm (f : GaussianL2) (b : SampleSpace → ℝ)
    (hm : Measurable b) (hb : ∀ Y, ‖b Y‖ ≤ 1) : ‖product f b hm hb‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [product_actual f b hm hb] with Y hY
  rw [hY,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hb Y)

private theorem value_measurable (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (s T : ℝ≥0) :
    Measurable (value φ s T) :=
  hφ.comp ((process_stronglyMeasurable s).measurable.prodMk
    (process_stronglyMeasurable T).measurable)

def term (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (s t T : ℝ≥0) : GaussianL2 :=
  product (wick (incrementDirection s t) 2) (value φ s T)
    (value_measurable φ hφ s T) (fun Y => hb _)

theorem term_actual (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (s t T : ℝ≥0) (hst : s ≤ t) :
    term φ hφ hb s t T =ᵐ[gaussianProduct] fun Y =>
      ((process t Y-process s Y)^2-((t:ℝ)-s))*φ (process s Y,process T Y) := by
  filter_upwards [product_actual (wick (incrementDirection s t) 2) (value φ s T)
    (value_measurable φ hφ s T) (fun Y => hb _),increment_wick_actual s t hst] with Y hY hw
  change term φ hφ hb s t T Y = _ at hY
  rw [hY,hw]
  rfl

theorem wick_norm_bound (s t : ℝ≥0) (hst : s ≤ t) :
    ‖(wick (incrementDirection s t) 2 : GaussianL2)‖ ≤ 2*((t:ℝ)-s) := by
  rw [← IBMQuarticSecondChaos.cross_self]
  have h := IBMQuadraticSpatialCalculus.cross_norm_le (incrementDirection s t) (incrementDirection s t)
  simpa only [← pow_two,incrementDirection_norm_sq s t hst,mul_assoc] using h

theorem term_norm_bound (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (s t T : ℝ≥0) (hst : s ≤ t) : ‖term φ hφ hb s t T‖ ≤ 2*((t:ℝ)-s) :=
  (product_norm _ _ _ _).trans (wick_norm_bound s t hst)

def pairCoefficient (φ ψ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hbφ : ∀ x, ‖φ x‖ ≤ 1) (hbψ : ∀ x, ‖ψ x‖ ≤ 1) (s t u T : ℝ≥0) : GaussianL2 :=
  product (wick (incrementDirection s t) 2)
    (fun Y => value φ s T Y*value ψ u T Y)
    ((value_measurable φ hφ s T).mul (value_measurable ψ hψ u T))
    (fun Y => by rw [norm_mul]; exact mul_le_one₀ (hbφ _) (norm_nonneg _) (hbψ _))

theorem pairCoefficient_actual (φ ψ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hbφ : ∀ x, ‖φ x‖ ≤ 1) (hbψ : ∀ x, ‖ψ x‖ ≤ 1) (s t u T : ℝ≥0) (hst : s ≤ t) :
    pairCoefficient φ ψ hφ hψ hbφ hbψ s t u T =ᵐ[gaussianProduct] fun Y =>
      ((process t Y-process s Y)^2-((t:ℝ)-s))*
        (φ (process s Y,process T Y)*ψ (process u Y,process T Y)) := by
  filter_upwards [product_actual (wick (incrementDirection s t) 2)
    (fun Y => value φ s T Y*value ψ u T Y)
    ((value_measurable φ hφ s T).mul (value_measurable ψ hψ u T))
    (fun Y => by rw [norm_mul]; exact mul_le_one₀ (hbφ _) (norm_nonneg _) (hbψ _)),
    increment_wick_actual s t hst] with Y hY hw
  change pairCoefficient φ ψ hφ hψ hbφ hbψ s t u T Y = _ at hY
  rw [hY,hw]
  rfl

theorem pairCoefficient_norm_bound (φ ψ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hbφ : ∀ x, ‖φ x‖ ≤ 1) (hbψ : ∀ x, ‖ψ x‖ ≤ 1) (s t u T : ℝ≥0) (hst : s ≤ t) :
    ‖pairCoefficient φ ψ hφ hψ hbφ hbψ s t u T‖ ≤ 2*((t:ℝ)-s) :=
  (product_norm _ _ _ _).trans (wick_norm_bound s t hst)

theorem pairCoefficient_generated (φ ψ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hbφ : ∀ x, ‖φ x‖ ≤ 1) (hbψ : ∀ x, ‖ψ x‖ ≤ 1) (s t u T : ℝ≥0)
    (hst : s ≤ t) (htu : t ≤ u) :
    pairCoefficient φ ψ hφ hψ hbφ hbψ s t u T ∈ generated (observation u T) := by
  let m := MeasurableSpace.comap (firstChaosFamily (observation u T)) inferInstance
  have hj (i : Option (Iic u)) : Measurable[m]
      (fun Y => firstChaosFamily (observation u T) Y i) :=
    (measurable_pi_apply i).comp (comap_measurable (firstChaosFamily (observation u T)))
  have hs : Measurable[m] (process s) := hj (some ⟨s,hst.trans htu⟩)
  have ht : Measurable[m] (process t) := hj (some ⟨t,htu⟩)
  have hu : Measurable[m] (process u) := hj (some ⟨u,by simp⟩)
  have hT : Measurable[m] (process T) := hj none
  exact ⟨_, (((ht.sub hs).pow_const 2).sub measurable_const).mul
    ((hφ.comp (hs.prodMk hT)).mul (hψ.comp (hu.prodMk hT))) |>.stronglyMeasurable,
    pairCoefficient_actual φ ψ hφ hψ hbφ hbψ s t u T hst⟩

theorem term_inner_pairCoefficient (φ ψ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hbφ : ∀ x, ‖φ x‖ ≤ 1) (hbψ : ∀ x, ‖ψ x‖ ≤ 1) (s t u v T : ℝ≥0)
    (hst : s ≤ t) (huv : u ≤ v) :
    inner ℝ (term φ hφ hbφ s t T) (term ψ hψ hbψ u v T) =
      inner ℝ (wick (incrementDirection u v) 2 : GaussianL2)
        (pairCoefficient φ ψ hφ hψ hbφ hbψ s t u T) := by
  rw [L2_inner_eq_integral,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [term_actual φ hφ hbφ s t T hst,term_actual ψ hψ hbψ u v T huv,
    pairCoefficient_actual φ ψ hφ hψ hbφ hbψ s t u T hst,
    increment_wick_actual u v huv] with Y h1 h2 h3 h4
  rw [h1,h2,h3,h4,Real.inner_apply,Real.inner_apply]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianTerminalBracketProducts
