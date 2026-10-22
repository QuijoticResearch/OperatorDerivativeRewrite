import Foundation.IBMCovarianceCauchySchwarz
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Separate-energy product control and literal completed signed IBM stochastic pairing. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompletedSignedCovarianceIntegral
open IBMTimeAveragedObservable IBMPredictableRectangles IBMJointPredictableEnergyMeasure
open IBMPredictableCovarianceMeasure IBMCovarianceVariationControl IBMCovarianceCauchySchwarz
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F
local instance (F G : JointL2) : IsFiniteMeasure (covariance F G).variation := finite_variation F G

def control (F G : JointL2) : Measure Space := predictableMeasure F + predictableMeasure G
local instance (F G : JointL2) : IsFiniteMeasure (control F G) := by unfold control; infer_instance

def density (F G : JointL2) (μ : Measure Space) (p : Space) : ℝ :=
  (μ.rnDeriv (control F G) p).toReal

theorem control_left (F G : JointL2) : predictableMeasure F ≪ control F G :=
  Measure.AbsolutelyContinuous.rfl.add_right _

theorem control_right (F G : JointL2) : predictableMeasure G ≪ control F G :=
  Measure.AbsolutelyContinuous.rfl.add_right' _

theorem control_variation (F G : JointL2) : (covariance F G).variation ≪ control F G :=
  (variation_ac_left F G).trans (control_left F G)

theorem density_measurable (F G : JointL2) (μ : Measure Space) : Measurable (density F G μ) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem density_nonneg (F G : JointL2) (μ : Measure Space) (p : Space) : 0 ≤ density F G μ p :=
  ENNReal.toReal_nonneg

theorem density_integrable (F G : JointL2) (μ : Measure Space) [IsFiniteMeasure μ] :
    Integrable (density F G μ) (control F G) := by
  exact integrableOn_univ.mp (Measure.integrableOn_toReal_rnDeriv (μ := μ)
    (ν := control F G) (s := univ) (measure_ne_top _ _))

theorem density_setIntegral (F G : JointL2) (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : μ ≪ control F G) (E : Set Space) :
    (∫ p in E, density F G μ p ∂control F G) = μ.real E :=
  Measure.setIntegral_toReal_rnDeriv hμ E

theorem density_young (F G : JointL2) (c : ℝ) :
    ∀ᵐ p ∂control F G, |c| * density F G (covariance F G).variation p ≤
      (1/2 : ℝ) * (density F G (predictableMeasure F) p +
        c^2*density F G (predictableMeasure G) p) := by
  apply ae_le_of_forall_setIntegral_le
    ((density_integrable F G _).const_mul |c|)
    (((density_integrable F G _).add ((density_integrable F G _).const_mul (c^2))).const_mul (1/2))
  intro E hE _
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_const_mul,
    integral_add ((density_integrable F G _).integrableOn)
      (((density_integrable F G _).const_mul (c^2)).integrableOn), integral_const_mul,
    density_setIntegral F G _ (control_variation F G),
    density_setIntegral F G _ (control_left F G), density_setIntegral F G _ (control_right F G)]
  exact variation_young F G c hE

theorem density_psd (F G : JointL2) :
    ∀ᵐ p ∂control F G, (density F G (covariance F G).variation p)^2 ≤
      density F G (predictableMeasure F) p * density F G (predictableMeasure G) p := by
  have hall : ∀ᵐ p ∂control F G, ∀ q : ℚ,
      |(q : ℝ)| * density F G (covariance F G).variation p ≤
        (1/2 : ℝ) * (density F G (predictableMeasure F) p +
          (q : ℝ)^2*density F G (predictableMeasure G) p) :=
    ae_all_iff.mpr (fun q => density_young F G q)
  filter_upwards [hall] with p hp
  have hc : ∀ c : ℝ, |c| * density F G (covariance F G).variation p ≤
      (1/2 : ℝ) * (density F G (predictableMeasure F) p +
        c^2*density F G (predictableMeasure G) p) := by
    intro c
    exact Rat.denseRange_cast.induction_on c (isClosed_le (by fun_prop) (by fun_prop)) hp
  have hd := discrim_le_zero (a := density F G (predictableMeasure G) p)
    (b := -2*density F G (covariance F G).variation p)
    (c := density F G (predictableMeasure F) p) (fun c => by
      have hy := hc c
      have hv := mul_le_mul_of_nonneg_right (le_abs_self c)
        (density_nonneg F G (covariance F G).variation p)
      nlinarith)
  dsimp [discrim] at hd
  nlinarith

theorem scalar_product_young {a b v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : 0 ≤ v)
    (h : v^2 ≤ a*b) (x y : ℝ) : v * |x*y| ≤ (1/2 : ℝ)*(a*x^2+b*y^2) := by
  have hs : v ≤ Real.sqrt a * Real.sqrt b := by
    rw [← Real.sqrt_mul ha]
    exact (Real.le_sqrt hv (mul_nonneg ha hb)).mpr h
  have hm := mul_le_mul_of_nonneg_right hs (abs_nonneg (x*y))
  have hy := two_mul_le_add_sq (Real.sqrt a * |x|) (Real.sqrt b * |y|)
  simp only [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, sq_abs] at hy
  rw [abs_mul] at hm ⊢
  nlinarith

theorem measurable_product_integrable (F G : JointL2) {H K : Space → ℝ}
    (hH : MemLp H 2 (predictableMeasure F)) (hK : MemLp K 2 (predictableMeasure G))
    (hmH : StronglyMeasurable H) (hmK : StronglyMeasurable K) :
    Integrable (fun p => H p*K p) (covariance F G).variation := by
  have hiH : Integrable (fun p => density F G (predictableMeasure F) p * H p^2) (control F G) :=
    (integrable_toReal_rnDeriv_mul_iff (control_left F G)).mpr hH.integrable_sq
  have hiK : Integrable (fun p => density F G (predictableMeasure G) p * K p^2) (control F G) :=
    (integrable_toReal_rnDeriv_mul_iff (control_right F G)).mpr hK.integrable_sq
  apply (integrable_toReal_rnDeriv_mul_iff (control_variation F G)).mp
  apply ((hiH.add hiK).const_mul (1/2 : ℝ)).mono'
    (((density_measurable F G _).stronglyMeasurable.mul (hmH.mul hmK)).aestronglyMeasurable)
  filter_upwards [density_psd F G] with p hp
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg F G _ p)]
  exact scalar_product_young (density_nonneg F G _ p) (density_nonneg F G _ p)
    (density_nonneg F G _ p) hp (H p) (K p)

theorem product_integrable (F G : JointL2) {H K : Space → ℝ}
    (hH : MemLp H 2 (predictableMeasure F)) (hK : MemLp K 2 (predictableMeasure G)) :
    Integrable (fun p => H p*K p) (covariance F G).variation := by
  let H' := hH.aestronglyMeasurable.mk H
  let K' := hK.aestronglyMeasurable.mk K
  have hh : H =ᵐ[predictableMeasure F] H' := hH.aestronglyMeasurable.ae_eq_mk
  have hk : K =ᵐ[predictableMeasure G] K' := hK.aestronglyMeasurable.ae_eq_mk
  exact (measurable_product_integrable F G (hH.ae_eq hh) (hK.ae_eq hk)
    hH.aestronglyMeasurable.stronglyMeasurable_mk hK.aestronglyMeasurable.stronglyMeasurable_mk).congr
      (product_ae_congr F G hh hk).symm

theorem integral_young (F G : JointL2) {H K : Space → ℝ}
    (hH : MemLp H 2 (predictableMeasure F)) (hK : MemLp K 2 (predictableMeasure G))
    (c : ℝ) :
    |c| * (∫ p, |H p*K p| ∂(covariance F G).variation) ≤ (1/2 : ℝ)*
      (c^2*(∫ p, H p^2 ∂predictableMeasure F) + ∫ p, K p^2 ∂predictableMeasure G) := by
  have hiH : Integrable (fun p => density F G (predictableMeasure F) p * H p^2) (control F G) :=
    (integrable_toReal_rnDeriv_mul_iff (control_left F G)).mpr hH.integrable_sq
  have hiK : Integrable (fun p => density F G (predictableMeasure G) p * K p^2) (control F G) :=
    (integrable_toReal_rnDeriv_mul_iff (control_right F G)).mpr hK.integrable_sq
  have hiP : Integrable (fun p => density F G (covariance F G).variation p * |H p*K p|) (control F G) :=
    (integrable_toReal_rnDeriv_mul_iff (control_variation F G)).mpr
      (product_integrable F G hH hK).abs
  have hb : (∫ p, |c| * (density F G (covariance F G).variation p * |H p*K p|) ∂control F G) ≤
      ∫ p, (1/2 : ℝ) * (c^2*(density F G (predictableMeasure F) p * H p^2) +
        density F G (predictableMeasure G) p * K p^2) ∂control F G := by
    apply integral_mono_ae (hiP.const_mul |c|) (((hiH.const_mul (c^2)).add hiK).const_mul (1/2))
    filter_upwards [density_psd F G] with p hp
    have hy := scalar_product_young (density_nonneg F G _ p) (density_nonneg F G _ p)
      (density_nonneg F G _ p) hp (c*H p) (K p)
    simp only [abs_mul, mul_pow, Pi.add_apply] at hy ⊢
    nlinarith [sq_abs c]
  rw [integral_const_mul, integral_const_mul,
    integral_add ((hiH.const_mul (c^2))) hiK, integral_const_mul] at hb
  unfold density at hb
  rw [integral_toReal_rnDeriv_mul (control_variation F G),
    integral_toReal_rnDeriv_mul (control_left F G),
    integral_toReal_rnDeriv_mul (control_right F G)] at hb
  exact hb

theorem integral_sq_bound (F G : JointL2) {H K : Space → ℝ}
    (hH : MemLp H 2 (predictableMeasure F)) (hK : MemLp K 2 (predictableMeasure G)) :
    (∫ p, |H p*K p| ∂(covariance F G).variation)^2 ≤
      (∫ p, H p^2 ∂predictableMeasure F) * ∫ p, K p^2 ∂predictableMeasure G := by
  have hd := discrim_le_zero (a := ∫ p, H p^2 ∂predictableMeasure F)
    (b := -2*(∫ p, |H p*K p| ∂(covariance F G).variation))
    (c := ∫ p, K p^2 ∂predictableMeasure G) (fun c => by
      have hy := integral_young F G hH hK c
      have hv := mul_le_mul_of_nonneg_right (le_abs_self c)
        (integral_nonneg (fun p => abs_nonneg (H p*K p)) (μ := (covariance F G).variation))
      nlinarith)
  dsimp [discrim] at hd
  nlinarith

theorem integral_norm_bound (F G : JointL2)
    (H : IBMPredictableLpDictionary.PredictableL2 F) (K : IBMPredictableLpDictionary.PredictableL2 G) :
    (∫ p, |H p*K p| ∂(covariance F G).variation) ≤ ‖H‖ * ‖K‖ := by
  have hH : (∫ p, H p^2 ∂predictableMeasure F) = ‖H‖^2 := by
    have hx := real_inner_self_eq_norm_sq H
    rw [L2.inner_def] at hx
    simpa only [Real.inner_apply, pow_two] using hx
  have hK : (∫ p, K p^2 ∂predictableMeasure G) = ‖K‖^2 := by
    have hx := real_inner_self_eq_norm_sq K
    rw [L2.inner_def] at hx
    simpa only [Real.inner_apply, pow_two] using hx
  have hb := integral_sq_bound F G (Lp.memLp H) (Lp.memLp K)
  rw [hH, hK] at hb
  exact (sq_le_sq₀ (integral_nonneg (fun p => abs_nonneg (H p*K p)))
    (mul_nonneg (norm_nonneg H) (norm_nonneg K))).mp (by simpa only [mul_pow] using hb)

theorem product_difference_bound (F G : JointL2)
    (H H' : IBMPredictableLpDictionary.PredictableL2 F)
    (K K' : IBMPredictableLpDictionary.PredictableL2 G) :
    (∫ p, |H p*K p-H' p*K' p| ∂(covariance F G).variation) ≤
      ‖H-H'‖ * ‖K‖ + ‖H'‖ * ‖K-K'‖ := by
  have hi := product_integrable F G (Lp.memLp (H-H')) (Lp.memLp K)
  have hj := product_integrable F G (Lp.memLp H') (Lp.memLp (K-K'))
  have he : (fun p => |H p*K p-H' p*K' p|) =ᵐ[(covariance F G).variation]
      (fun p => |(H-H') p*K p+H' p*(K-K') p|) := by
    filter_upwards [(variation_ac_left F G).ae_le (Lp.coeFn_sub H H'),
      (variation_ac_right F G).ae_le (Lp.coeFn_sub K K')] with p hp hq
    rw [hp, hq]
    simp only [Pi.sub_apply]
    congr 1
    ring
  rw [integral_congr_ae he]
  calc
    _ ≤ ∫ p, |(H-H') p*K p| + |H' p*(K-K') p| ∂(covariance F G).variation :=
      integral_mono_ae (hi.add hj).abs (hi.abs.add hj.abs)
        (Eventually.of_forall fun _ => abs_add_le _ _)
    _ = _ := integral_add hi.abs hj.abs
    _ ≤ _ := add_le_add (integral_norm_bound F G (H-H') K)
      (integral_norm_bound F G H' (K-K'))

theorem product_L1_limit (F G : JointL2)
    {H : ℕ → IBMPredictableLpDictionary.PredictableL2 F}
    {K : ℕ → IBMPredictableLpDictionary.PredictableL2 G}
    {h : IBMPredictableLpDictionary.PredictableL2 F}
    {k : IBMPredictableLpDictionary.PredictableL2 G}
    (hH : Tendsto H atTop (𝓝 h)) (hK : Tendsto K atTop (𝓝 k)) :
    Tendsto (fun n => ∫ p, |H n p*K n p-h p*k p| ∂(covariance F G).variation)
      atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ‖H n-h‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hH.sub (tendsto_const_nhds (x := h))).norm
  have hk : Tendsto (fun n => ‖K n-k‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hK.sub (tendsto_const_nhds (x := k))).norm
  apply squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => product_difference_bound F G (H n) h (K n) k)
  simpa only [zero_mul, mul_zero, zero_add] using
    (hh.mul hK.norm).add (tendsto_const_nhds.mul hk)

theorem signed_integral_limit (F G : JointL2)
    {H : ℕ → IBMPredictableLpDictionary.PredictableL2 F}
    {K : ℕ → IBMPredictableLpDictionary.PredictableL2 G}
    {h : IBMPredictableLpDictionary.PredictableL2 F}
    {k : IBMPredictableLpDictionary.PredictableL2 G}
    (hH : Tendsto H atTop (𝓝 h)) (hK : Tendsto K atTop (𝓝 k)) :
    Tendsto (fun n => ∫ᵛ p, H n p*K n p ∂<•covariance F G) atTop
      (𝓝 (∫ᵛ p, h p*k p ∂<•covariance F G)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (show Tendsto (fun n => ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip‖ *
      (∫ p, |H n p*K n p-h p*k p| ∂(covariance F G).variation)) atTop (𝓝 0) by
      simpa only [mul_zero] using (tendsto_const_nhds
        (x := ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip‖)).mul
          (product_L1_limit F G hH hK))
  rw [dist_eq_norm, ← VectorMeasure.integral_sub
    (product_integrable F G (Lp.memLp (H n)) (Lp.memLp (K n)))
    (product_integrable F G (Lp.memLp h) (Lp.memLp k))]
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using (VectorMeasure.norm_integral_le_integral_norm
    (μ := covariance F G) (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (f := fun p => H n p*K n p-h p*k p))

theorem actual_completed_signed_identity (F G : JointL2)
    (H : IBMPredictableLpDictionary.PredictableL2 F) (K : IBMPredictableLpDictionary.PredictableL2 G) :
    (∫ᵛ p, H p*K p ∂<•covariance F G) =
      inner ℝ (IBMFullPredictableIntegral.integral F H) (IBMFullPredictableIntegral.integral G K) := by
  obtain ⟨a, ha, hIa⟩ := IBMFullPredictableIntegral.exists_actual_approximation F H
  obtain ⟨b, hb, hIb⟩ := IBMFullPredictableIntegral.exists_actual_approximation G K
  have hs := signed_integral_limit F G ha hb
  have he : ∀ n, (∫ᵛ p, IBMPredictableLpDictionary.dictionary F (a n) p *
      IBMPredictableLpDictionary.dictionary G (b n) p ∂<•covariance F G) =
        inner ℝ (IBMPredictableFiniteIntegral.integralLinear F (a n))
          (IBMPredictableFiniteIntegral.integralLinear G (b n)) := by
    intro n
    exact (signed_integral_ae_congr F G (IBMPredictableLpDictionary.dictionary_ae F (a n))
      (IBMPredictableLpDictionary.dictionary_ae G (b n))).trans
        (IBMFiniteSignedCovarianceIntegral.finite_signed_pairing F G (a n) (b n))
  exact tendsto_nhds_unique hs (by simpa only [he] using hIa.inner (𝕜 := ℝ) hIb)

end OperatorDerivativeRewrite.Foundation.IBMCompletedSignedCovarianceIntegral
