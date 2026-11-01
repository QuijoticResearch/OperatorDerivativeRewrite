import Foundation.GaussianParameterizedItoTensor
import Foundation.GaussianFiniteHorizonAdjoint
import Foundation.StochasticCauchyBrownianRealization

/-! Exact mixed Gram terms for the existing native parameterized Ito maps.
Independent reference noises do not make arbitrary future-parameter integrals
orthogonal.  Joint chronological predictability remains a separate domain. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyParameterizedObstruction
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto
open GaussianParameterizedIto GaussianParameterizedItoTensor ProductL2Curry
open IBMSourceLaws
local instance predictableTime : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable naturalFiltration
local instance finiteL2Exponent : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] realPredictableL2_secondCountable predictableL2_secondCountable

abbrev Domain (T : ℝ≥0) := Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)
abbrev JointL2 := Lp ℝ 2 (gaussianProduct.prod gaussianProduct)

def firstIntegral (T : ℝ≥0) : Domain T →ₗᵢ[ℝ] JointL2 := realFlat gaussianProduct T

def secondIntegral (T : ℝ≥0) : Domain T →ₗᵢ[ℝ] JointL2 :=
  (swap gaussianProduct gaussianProduct).comp (firstIntegral T)

def tensorInput (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : GaussianL2) : Domain T :=
  productTensor (predictableMeasure T) gaussianProduct a h

theorem first_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : GaussianL2) :
    firstIntegral T (tensorInput T a h) =
      productTensor gaussianProduct gaussianProduct (realIto T a) h :=
  realFlat_tensor gaussianProduct T a h

theorem second_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : GaussianL2) :
    secondIntegral T (tensorInput T a h) =
      productTensor gaussianProduct gaussianProduct h (realIto T a) := by
  change swap gaussianProduct gaussianProduct (firstIntegral T (tensorInput T a h)) = _
  rw [first_tensor, swap_productTensor]


/-- The overlap contains EVERY tensor of centered terminal-past observables,
by direct reuse of the existing exact finite-horizon representation theorem.
No assertion of joint predictability is made for these parameterized inputs. -/
theorem centered_past_tensor_overlap (T : ℝ≥0) (F G : GaussianL2)
    (hF : F ∈ GaussianConditionalIto.pastL2 T) (hG : G ∈ GaussianConditionalIto.pastL2 T)
    (hmF : (∫ w, F w ∂gaussianProduct) = 0) (hmG : (∫ w, G w ∂gaussianProduct) = 0) :
    productTensor gaussianProduct gaussianProduct F G ∈ (firstIntegral T).toLinearMap.range ∧
    productTensor gaussianProduct gaussianProduct F G ∈ (secondIntegral T).toLinearMap.range := by
  let a := GaussianComplexHorizonIto.trimEquiv T (GaussianFiniteHorizonAdjoint.finiteAdjoint T F)
  let b := GaussianComplexHorizonIto.trimEquiv T (GaussianFiniteHorizonAdjoint.finiteAdjoint T G)
  have ha : realIto T a = F := by
    rw [realIto_trim, GaussianFiniteHorizonAdjoint.finiteAdjoint_representation T F hF,
      hmF, zero_smul, sub_zero]
  have hb : realIto T b = G := by
    rw [realIto_trim, GaussianFiniteHorizonAdjoint.finiteAdjoint_representation T G hG,
      hmG, zero_smul, sub_zero]
  constructor
  · refine ⟨tensorInput T a G, ?_⟩
    exact (first_tensor T a G).trans (congrArg (fun f =>
      productTensor gaussianProduct gaussianProduct f G) ha)
  · refine ⟨tensorInput T b F, ?_⟩
    exact (second_tensor T b F).trans (congrArg (fun g =>
      productTensor gaussianProduct gaussianProduct F g) hb)

theorem tensor_inner (a b c d : GaussianL2) :
    inner ℝ (productTensor gaussianProduct gaussianProduct a b)
      (productTensor gaussianProduct gaussianProduct c d) = inner ℝ a c * inner ℝ b d := by
  rw [L2_inner_eq_integral]
  calc
    _ = ∫ w : SampleSpace × SampleSpace, inner ℝ (a w.1) (c w.1) *
        inner ℝ (b w.2) (d w.2) ∂gaussianProduct.prod gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct a b,
        productTensor_coeFn gaussianProduct gaussianProduct c d] with w hab hcd
      simp only [hab, hcd, Real.inner_apply, smul_eq_mul]
      ring
    _ = _ := by
      rw [integral_prod_mul (fun w => inner ℝ (a w) (c w))
        (fun w => inner ℝ (b w) (d w)), ← L2_inner_eq_integral, ← L2_inner_eq_integral]

/-- Exact mixed-sector Gram term for actual native stochastic tensors. -/
theorem tensor_cross_inner (T : ℝ≥0) (a b : Lp ℝ 2 (predictableMeasure T))
    (h k : GaussianL2) :
    inner ℝ (firstIntegral T (tensorInput T a h)) (secondIntegral T (tensorInput T b k)) =
      inner ℝ (realIto T a) k * inner ℝ h (realIto T b) := by
  rw [first_tensor, second_tensor]
  exact tensor_inner _ _ _ _


/-- Source independence DOES give orthogonality when each coefficient uses only
its own native predictable noise, with no other-source random parameter. -/
theorem constant_parameter_orthogonal (T : ℝ≥0) (a b : Lp ℝ 2 (predictableMeasure T)) :
    inner ℝ (firstIntegral T (tensorInput T a gaussianOne))
      (secondIntegral T (tensorInput T b gaussianOne)) = 0 := by
  rw [tensor_cross_inner, gaussianOne_inner_eq_integral]
  have hm : (∫ w, realIto T b w ∂gaussianProduct) = 0 :=
    GaussianPredictableHorizon.itoIntegral_centered T
      ((GaussianComplexHorizonIto.trimEquiv T).symm b)
  rw [hm, mul_zero]


private theorem pastIncrement_inner_past (s t : ℝ≥0) (hst : s ≤ t) (A G : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hG : G ∈ GaussianConditionalIto.pastL2 s) :
    inner ℝ (GaussianPastStepCompletion.pastIncrement s t hst A hA) G = 0 := by
  let U : GaussianPredictableFull.fullPredictable :=
    ⟨GaussianTimeProductL2.productTensor (GaussianTimeHilbert.intervalVector s t) A,
      GaussianPredictableFull.past_step_mem_fullPredictable s t A hA⟩
  have hU : GaussianPredictableFull.itoIntegral U =
      GaussianPastStepCompletion.pastIncrement s t hst A hA := by
    apply Lp.ext
    exact (GaussianPredictableFull.itoIntegral_past_step s t hst A hA).trans
      (GaussianPastStepCompletion.pastIncrement_coeFn s t hst A hA).symm
  have hcut : GaussianPredictableCutoff.predictableCut s U = 0 := by
    apply Subtype.ext
    change GaussianPredictableCutoff.cut s
      (GaussianTimeProductL2.productTensor (GaussianTimeHilbert.intervalVector s t) A) = 0
    rw [GaussianPredictableCutoff.cut_tensor,
      min_eq_right (show (s : ℝ) ≤ t from hst)]
    have ht : (GaussianTimeHilbert.intervalVector s s : ℝ → ℝ) =ᵐ[volume] fun _ => 0 := by
      simpa using GaussianTimeHilbert.intervalVector_coeFn s s
    have hp := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := gaussianProduct)).ae_eq_comp ht
    apply Lp.ext
    filter_upwards [GaussianTimeProductL2.productTensor_coeFn
      (GaussianTimeHilbert.intervalVector s s) A, hp,
      Lp.coeFn_zero ℝ 2 GaussianTimeProductL2.timeProbability] with w hw ht h0
    simp only [Function.comp_apply] at ht
    simpa only [Pi.zero_apply, hw, ht, zero_mul] using h0.symm
  have he := GaussianConditionalIto.past_inner_future_integral s G hG U
  rw [hcut, sub_zero, hU, real_inner_comm] at he
  exact he

/-- Positive joint-past result: actual separable stochastic step integrals in
opposite independent noises are orthogonal, including OVERLAPPING intervals.
Both own-source and other-source coefficients are known at their start times. -/
theorem joint_past_steps_orthogonal (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v)
    (A B C D : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : B ∈ GaussianConditionalIto.pastL2 s)
    (hC : AEStronglyMeasurable[naturalFiltration u] C gaussianProduct)
    (hD : D ∈ GaussianConditionalIto.pastL2 u) :
    inner ℝ (productTensor gaussianProduct gaussianProduct
      (GaussianPastStepCompletion.pastIncrement s t hst A hA) B)
      (productTensor gaussianProduct gaussianProduct D
        (GaussianPastStepCompletion.pastIncrement u v huv C hC)) = 0 := by
  rw [tensor_inner]
  rcases le_total s u with hsu | hus
  · have hBu : B ∈ GaussianConditionalIto.pastL2 u :=
      (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct).mono
        (naturalFiltration.mono hsu)
    have he := pastIncrement_inner_past u v huv C B hC hBu
    rw [real_inner_comm] at he
    rw [he, mul_zero]
  · have hDs : D ∈ GaussianConditionalIto.pastL2 s :=
      (hD : AEStronglyMeasurable[naturalFiltration u] D gaussianProduct).mono
        (naturalFiltration.mono hus)
    rw [pastIncrement_inner_past s t hst A D hA hDs, zero_mul]


/-- Actual step output energy, valid for unbounded L2 coefficients. -/
theorem step_tensor_energy (s t : ℝ≥0) (hst : s ≤ t) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    ‖productTensor gaussianProduct gaussianProduct
      (GaussianPastStepCompletion.pastIncrement s t hst A hA) B‖ ^ 2 =
      ((t : ℝ)-s) * ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, tensor_inner,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    GaussianPastStepCompletion.pastIncrement_norm, mul_pow,
    ← GaussianTimeHilbert.timeVector_sub s t hst,
    GaussianTimeHilbert.timeVector_sub_norm_sq s t hst]

/-- A genuine positive two-channel stochastic step isometry. No disjointness
between the two integration intervals is required. -/
theorem joint_past_steps_energy (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v)
    (A B C D : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : B ∈ GaussianConditionalIto.pastL2 s)
    (hC : AEStronglyMeasurable[naturalFiltration u] C gaussianProduct)
    (hD : D ∈ GaussianConditionalIto.pastL2 u) :
    ‖productTensor gaussianProduct gaussianProduct
      (GaussianPastStepCompletion.pastIncrement s t hst A hA) B +
      productTensor gaussianProduct gaussianProduct D
        (GaussianPastStepCompletion.pastIncrement u v huv C hC)‖ ^ 2 =
      ((t : ℝ)-s) * ‖A‖ ^ 2 * ‖B‖ ^ 2 + ((v : ℝ)-u) * ‖C‖ ^ 2 * ‖D‖ ^ 2 := by
  rw [norm_add_sq_real, joint_past_steps_orthogonal s t u v hst huv A B C D hA hB hC hD,
    mul_zero, add_zero, step_tensor_energy]
  congr 1
  rw [← swap_productTensor gaussianProduct gaussianProduct
    (GaussianPastStepCompletion.pastIncrement u v huv C hC) D,
    (swap gaussianProduct gaussianProduct).norm_map, step_tensor_energy]

/-- An admissible native parameter tensor. The parameter is the OTHER source's
terminal integral, which need not be jointly predictable during integration. -/
def overlapInput (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) : Domain T :=
  tensorInput T a (realIto T a)

theorem overlap_outputs_equal (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) :
    firstIntegral T (overlapInput T a) = secondIntegral T (overlapInput T a) := by
  exact (first_tensor T a _).trans (second_tensor T a _).symm

theorem overlap_cross_energy (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) :
    inner ℝ (firstIntegral T (overlapInput T a)) (secondIntegral T (overlapInput T a)) =
      ‖a‖ ^ 4 := by
  rw [overlapInput, tensor_cross_inner, real_inner_self_eq_norm_sq,
    (realIto T).norm_map]
  ring

theorem overlap_input_energy (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) :
    ‖overlapInput T a‖ ^ 2 = ‖a‖ ^ 4 := by
  have he := overlap_cross_energy T a
  rw [← overlap_outputs_equal T a] at he
  simpa only [real_inner_self_eq_norm_sq, (firstIntegral T).norm_map] using he

theorem overlap_input_nonzero (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (ha : a ≠ 0) :
    overlapInput T a ≠ 0 := by
  intro hz
  have he := overlap_input_energy T a
  rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
  exact (pow_pos (norm_pos_iff.mpr ha) 4).ne' he.symm

/-- On this native tensor, the false orthogonal sum energy is off by factor2. -/
theorem overlap_sum_energy (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) :
    ‖firstIntegral T (overlapInput T a) + secondIntegral T (overlapInput T a)‖ ^ 2 =
      4 * ‖a‖ ^ 4 := by
  rw [norm_add_sq_real, (firstIntegral T).norm_map, (secondIntegral T).norm_map,
    overlap_input_energy, overlap_cross_energy]
  ring

/-- A valid bound survives on the FULL parameterized pair domain. -/
theorem sum_energy_bound (T : ℝ≥0) (u v : Domain T) :
    ‖firstIntegral T u + secondIntegral T v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hb := norm_add_le (firstIntegral T u) (secondIntegral T v)
  rw [(firstIntegral T).norm_map, (secondIntegral T).norm_map] at hb
  nlinarith [norm_nonneg (firstIntegral T u + secondIntegral T v),
    norm_nonneg u, norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]

/-- The factor2 bound is optimal whenever the native scalar domain is nonzero. -/
theorem bound_constant_ge_two (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (ha : a ≠ 0)
    (C : ℝ) (hC : ∀ u v : Domain T,
      ‖firstIntegral T u + secondIntegral T v‖ ^ 2 ≤ C * (‖u‖ ^ 2 + ‖v‖ ^ 2)) : 2 ≤ C := by
  have hh := hC (overlapInput T a) (overlapInput T a)
  rw [overlap_sum_energy, overlap_input_energy] at hh
  have hp : 0 < ‖a‖ ^ 4 := pow_pos (norm_pos_iff.mpr ha) 4
  have he : 4 * ‖a‖ ^ 4 ≤ (2*C) * ‖a‖ ^ 4 := by nlinarith [hh]
  have := (mul_le_mul_iff_of_pos_right hp).mp he
  linarith

/-- The unrestricted two-source sum also has a genuine nonzero kernel pair. -/
theorem nonzero_cancellation (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (ha : a ≠ 0) :
    ∃ u v : Domain T, u ≠ 0 ∧ v ≠ 0 ∧ firstIntegral T u + secondIntegral T v = 0 := by
  refine ⟨overlapInput T a, -overlapInput T a, overlap_input_nonzero T a ha, ?_, ?_⟩
  · exact neg_ne_zero.mpr (overlap_input_nonzero T a ha)
  · rw [map_neg, ← overlap_outputs_equal T a, add_neg_cancel]

/-- A concrete native predictable mode whose integral is the actual Brownian
terminal class. This uses the existing exact finite-horizon representation. -/
def terminalMode (T : ℝ≥0) : Lp ℝ 2 (predictableMeasure T) :=
  GaussianComplexHorizonIto.trimEquiv T (GaussianFiniteHorizonAdjoint.finiteAdjoint T (wienerL2 T))

theorem terminalMode_integral (T : ℝ≥0) : realIto T (terminalMode T) = wienerL2 T := by
  rw [terminalMode, realIto_trim, GaussianFiniteHorizonAdjoint.finiteAdjoint_representation]
  · have hm : (∫ w, wienerL2 T w ∂gaussianProduct) = 0 := process_integral T
    rw [hm, zero_smul, sub_zero]
  · exact (GaussianTimeProcess.process_stronglyAdapted T).aestronglyMeasurable

theorem terminalMode_energy (T : ℝ≥0) : ‖terminalMode T‖ ^ 2 = (T : ℝ) := by
  rw [← (realIto T).norm_map, terminalMode_integral]
  have he := wienerL2_sub_norm_sq 0 T (by positivity)
  rwa [wienerL2_zero, sub_zero, NNReal.coe_zero, sub_zero] at he

theorem terminalMode_nonzero (T : ℝ≥0) (hT : 0 < T) : terminalMode T ≠ 0 := by
  intro hz
  have he := terminalMode_energy T
  rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
  exact hT.ne' (by exact_mod_cast he.symm)

/-- The overlap is an actual terminal product of the constructed complex
Brownian coordinates, not merely equality of two abstract range elements. -/
theorem terminal_overlap_value (T : ℝ≥0) :
    firstIntegral T (overlapInput T (terminalMode T)) =ᵐ[jointMeasure]
      (fun w => (StochasticCauchyBrownianRealization.value T w).re *
        (StochasticCauchyBrownianRealization.value T w).im) := by
  have he : firstIntegral T (overlapInput T (terminalMode T)) =
      productTensor gaussianProduct gaussianProduct (wienerL2 T) (wienerL2 T) := by
    rw [overlapInput, first_tensor, terminalMode_integral]
  rw [he]
  have h1 := (measurePreserving_fst (μ := gaussianProduct)
    (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (IBMConstructedSources.clockPath_coordinate_ae T)
  have h2 := (measurePreserving_snd (μ := gaussianProduct)
    (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (IBMConstructedSources.clockPath_coordinate_ae T)
  filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct (wienerL2 T) (wienerL2 T),
    h1, h2] with w ht hx hy
  simp only [Function.comp_apply] at hx hy
  simpa only [StochasticCauchyBrownianRealization.value_eq, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, sub_zero, zero_add,
    add_zero, hx, hy, process, smul_eq_mul] using ht

end OperatorDerivativeRewrite.Foundation.StochasticCauchyParameterizedObstruction
