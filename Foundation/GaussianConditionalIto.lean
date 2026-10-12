import Foundation.GaussianPredictableCutoff
import Foundation.GaussianBrownianPRP
import Foundation.GaussianConditionalGraph

/-! Conditional expectations of actual stochastic integrals, first on genuine polynomial steps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianConditionalIto
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeDivergence
open GaussianTimeProductL2 GaussianPredictableFull GaussianPredictableCutoff
open GaussianContinuousRigidity GaussianSensitivityCore GaussianPredictableL2Completion
open GaussianTimePolynomialPairing GaussianTimePastDensity GaussianBrownianGeneratedSpace
open SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

def pastL2 (T : ℝ≥0) : Submodule ℝ GaussianL2 :=
  lpMeas ℝ ℝ (naturalFiltration T) 2 gaussianProduct

theorem pastL2_isClosed (T : ℝ≥0) : IsClosed (pastL2 T : Set GaussianL2) :=
  isClosed_aestronglyMeasurable (naturalFiltration.le T)

instance pastL2_complete (T : ℝ≥0) : CompleteSpace (pastL2 T) :=
  (pastL2_isClosed T).completeSpace_coe

def pastProjection (T : ℝ≥0) : GaussianL2 →L[ℝ] GaussianL2 := (pastL2 T).starProjection

theorem pastProjection_ae (T : ℝ≥0) (F : GaussianL2) :
    pastProjection T F =ᵐ[gaussianProduct] gaussianProduct[F | naturalFiltration T] := by
  change (condExpL2 ℝ ℝ (naturalFiltration.le T) F : GaussianL2) =ᵐ[_] _
  simpa only [Lp.toLp_coeFn] using
    (Lp.memLp F).condExpL2_ae_eq_condExp (𝕜 := ℝ) (naturalFiltration.le T)

theorem incrementProduct_mem_past {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) (s t T : ℝ≥0)
    (hr : ∀ i, r i ≤ T) (hs : s ≤ T) (ht : t ≤ T) :
    incrementProductL2 r p s t ∈ pastL2 T := by
  have hm : Measurable[naturalFiltration T] (fun ω =>
      MvPolynomial.eval (fun i => process (r i) ω) p * (process t ω - process s ω)) := by
    letI : MeasurableSpace SampleSpace := naturalFiltration T
    exact (p.continuous_eval.measurable.comp
      (Measurable.of_eval fun i => ((process_stronglyAdapted (r i)).mono
        (naturalFiltration.mono (hr i))).measurable)).mul
      (((process_stronglyAdapted t).mono (naturalFiltration.mono ht)).measurable.sub
        ((process_stronglyAdapted s).mono (naturalFiltration.mono hs)).measurable)
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr (incrementProductL2_coeFn r p s t).symm

theorem tensor_eq_zero_of_le (s t : ℝ≥0) (hst : t ≤ s) (A : GaussianL2) :
    productTensor (intervalVector s t) A = 0 := by
  apply Lp.ext
  have ht := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn s t)
  filter_upwards [productTensor_coeFn (intervalVector s t) A, ht,
    Lp.coeFn_zero ℝ 2 timeProbability] with z hz ht h0
  simp only [Function.comp_apply] at ht
  rw [hz, ht, h0]
  simp [Ioc_eq_empty_of_le (show (t : ℝ) ≤ s from hst)]

theorem integral_cut_step_mem_past {n : ℕ} (T s t : ℝ≥0) (hst : s ≤ t)
    (r : Fin n → ℝ≥0) (hr : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ) :
    integralExtension (cut T (pastStep s t r hr p)) ∈ pastL2 T := by
  change integralExtension (cut T (productTensor (intervalVector s t) (pastCoefficient r p))) ∈ _
  rw [cut_tensor]
  by_cases hs : s ≤ T
  · change integralExtension (pastStep s (min t T) r hr p) ∈ _
    rw [integralExtension_eq, ito_pastStep _ _ (le_min hst hs)]
    exact incrementProduct_mem_past r p s (min t T) T (fun i => (hr i).trans hs) hs (min_le_right _ _)
  · have hz := tensor_eq_zero_of_le s (min t T)
      ((min_le_right _ _).trans (le_of_not_ge hs)) (pastCoefficient r p)
    simp only [NNReal.coe_min] at hz
    rw [hz, map_zero]
    exact (pastL2 T).zero_mem

theorem pastPolynomial_inner_future_increment {n : ℕ} {κ : Type*} [Fintype κ]
    (q : κ → ℝ≥0) (v : MvPolynomial κ ℝ)
    (r : Fin n → ℝ≥0) (p : MvPolynomial (Fin n) ℝ) (a b : ℝ≥0)
    (hq : ∀ i, q i ≤ a) (hr : ∀ i, r i ≤ a) (hab : a ≤ b) :
    inner ℝ (pastCoefficient q v : GaussianL2) (incrementProductL2 r p a b) = 0 := by
  let f := pastCoefficient q v
  let g := pastCoefficient r p
  let k := incrementDirection a b
  have hD : (fun ω => inner ℝ (polynomialDerivative (polynomialProduct f g) ω) k)
      =ᵐ[gaussianProduct] fun _ => (0 : ℝ) := by
    filter_upwards [polynomialDerivative_product_ae f g,
      pastCoefficient_gradient_inner_increment q v a b hq hab,
      pastCoefficient_gradient_inner_increment r p a b hr hab] with ω hd hf hg
    rw [hd, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    change (f : GaussianL2) ω * inner ℝ (polynomialDerivative g ω) k +
      (g : GaussianL2) ω * inner ℝ (polynomialDerivative f ω) k = 0
    rw [hg, hf]; ring
  have he : (fun ω => (polynomialProduct f g : GaussianL2) ω * firstChaosEmbedding k ω)
      =ᵐ[gaussianProduct] fun ω => (f : GaussianL2) ω * incrementProductL2 r p a b ω := by
    filter_upwards [polynomialProductL2_coeFn f g, pastCoefficient_coeFn r p,
      process_increment_ae a b hab, incrementProductL2_coeFn r p a b] with ω hp hg hk hi
    change (polynomialProduct f g : GaussianL2) ω * firstChaosEmbedding (incrementDirection a b) ω = _
    change (polynomialProduct f g : GaussianL2) ω = _ at hp
    change firstChaosEmbedding (incrementDirection a b) ω = _ at hk
    rw [hp, hk, hi]
    change (f : GaussianL2) ω * (pastCoefficient r p : GaussianL2) ω * _ = _
    rw [hg]; ring
  have hs := polynomialDerivative_stein (polynomialProduct f g) k
  rw [integral_congr_ae hD, integral_congr_ae he, integral_zero] at hs
  rw [L2_inner_eq_integral]
  simpa only [Real.inner_apply, mul_comm] using hs.symm

theorem pastPolynomial_inner_future_step {n : ℕ} {κ : Type*} [Fintype κ] (T s t : ℝ≥0)
    (r : Fin n → ℝ≥0) (hr : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ)
    (q : κ → ℝ≥0) (hq : ∀ i, q i ≤ T) (v : MvPolynomial κ ℝ) :
    inner ℝ (pastCoefficient q v : GaussianL2)
      (integralExtension ((pastStep s t r hr p : TimeProbabilityL2) - cut T (pastStep s t r hr p))) = 0 := by
  change inner ℝ _ (integralExtension
    (productTensor (intervalVector s t) (pastCoefficient r p) -
      cut T (productTensor (intervalVector s t) (pastCoefficient r p)))) = 0
  rw [sub_cut_tensor]
  by_cases ht : max s T ≤ t
  · have hr' : ∀ i, r i ≤ max s T := fun i => (hr i).trans (le_max_left _ _)
    change inner ℝ _ (integralExtension (pastStep (max s T) t r hr' p)) = 0
    rw [integralExtension_eq, ito_pastStep _ _ ht]
    exact pastPolynomial_inner_future_increment q v r p _ _
      (fun i => (hq i).trans (le_max_right _ _)) hr' ht
  · have hz := tensor_eq_zero_of_le (max s T) t (le_of_not_ge ht) (pastCoefficient r p)
    simp only [NNReal.coe_max] at hz
    rw [hz, map_zero, inner_zero_right]

theorem integral_cut_mem_past (T : ℝ≥0) (U : fullPredictable) :
    itoIntegral (predictableCut T U) ∈ pastL2 T := by
  have h : closedProductSteps ≤
      (pastL2 T).comap (integralExtension.comp (cut T)).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rw [productStepSpan, Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro z ⟨n, r, p, s, t, hr, hst, rfl⟩
      exact integral_cut_step_mem_past T s t hst r hr p
    · exact (pastL2_isClosed T).preimage (integralExtension.comp (cut T)).continuous
  have hu : (U : TimeProbabilityL2) ∈ closedProductSteps := by
    simpa only [closedProductSteps_eq_fullPredictable] using U.property
  have hh := h hu
  change integralExtension (predictableCut T U) ∈ pastL2 T at hh
  rwa [integralExtension_eq] at hh

theorem polynomial_inner_future_integral {κ : Type*} [Fintype κ]
    (T : ℝ≥0) (q : κ → ℝ≥0) (hq : ∀ i, q i ≤ T) (v : MvPolynomial κ ℝ)
    (U : fullPredictable) :
    inner ℝ (pastCoefficient q v : GaussianL2)
      (itoIntegral (U - predictableCut T U)) = 0 := by
  let L := (innerSL ℝ (pastCoefficient q v : GaussianL2)).comp
    (integralExtension.comp (ContinuousLinearMap.id ℝ TimeProbabilityL2 - cut T))
  have h : closedProductSteps ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal
    · rw [productStepSpan, Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro z ⟨n, r, p, s, t, hr, hst, rfl⟩
      exact pastPolynomial_inner_future_step T s t r hr p q hq v
    · exact L.isClosed_ker
  have hu : (U : TimeProbabilityL2) ∈ closedProductSteps := by
    simpa only [closedProductSteps_eq_fullPredictable] using U.property
  have hh := h hu
  change inner ℝ (pastCoefficient q v : GaussianL2)
    (integralExtension (U - predictableCut T U : fullPredictable)) = 0 at hh
  rwa [integralExtension_eq] at hh

theorem past_inner_future_integral (T : ℝ≥0) (G : GaussianL2) (hG : G ∈ pastL2 T)
    (U : fullPredictable) : inner ℝ G (itoIntegral (U - predictableCut T U)) = 0 := by
  classical
  let L := innerSL ℝ (itoIntegral (U - predictableCut T U))
  have h : pastL2 T ≤ L.ker := by
    change lpMeas ℝ ℝ (naturalFiltration T) 2 gaussianProduct ≤ _
    rw [← pastPolynomial_closure]
    apply Submodule.topologicalClosure_minimal
    · rintro F ⟨p, rfl⟩
      obtain ⟨s, p, rfl⟩ := MvPolynomial.exists_finset_rename p
      change inner ℝ (itoIntegral (U - predictableCut T U))
        (familyPolynomialEmbedding
          (fun t : Iic T => hilbertEmbedding TimeHilbert (timeVector t))
          (MvPolynomial.rename Subtype.val p)) = 0
      rw [familyPolynomial_rename, real_inner_comm]
      exact polynomial_inner_future_integral T (fun i : s => (i.val : ℝ≥0))
        (fun i => i.val.property) p U
    · exact L.isClosed_ker
  have hh := h hG
  change inner ℝ (itoIntegral (U - predictableCut T U)) G = 0 at hh
  rwa [real_inner_comm] at hh

/-- Conditional expectation commutes with the actual stochastic integral by time cutoff.
Both directions use proved polynomial-step calculations and genuine L2 density. -/
theorem pastProjection_integral (T : ℝ≥0) (U : fullPredictable) :
    pastProjection T (itoIntegral U) = itoIntegral (predictableCut T U) := by
  apply (pastL2 T).eq_starProjection_of_mem_of_inner_eq_zero (integral_cut_mem_past T U)
  intro G hG
  rw [← map_sub, real_inner_comm]
  exact past_inner_future_integral T G hG U

end OperatorDerivativeRewrite.Foundation.GaussianConditionalIto
