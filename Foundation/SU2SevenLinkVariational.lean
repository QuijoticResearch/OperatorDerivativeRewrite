import Foundation.SU2SevenLinkTransfer

/-! Reversible bounded quadratic-form identities for the actual seven-link
Wilson transfer. These serve the specific positive-supersolution / odd-trial
comparison; no stationary vacuum or physical mass gap is assumed. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkVariational
open QuaternionSU2Representation SU2WilsonConvolution SU2SevenLinkTransfer

private theorem inverse_product {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]
    [Inv G] [Inv H] [MeasurableInv G] [MeasurableInv H]
    (μ : Measure G) (ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ.map Inv.inv=μ) (hν : ν.map Inv.inv=ν) :
    (μ.prod ν).map Inv.inv=μ.prod ν := by
  change (μ.prod ν).map (Prod.map Inv.inv Inv.inv)=μ.prod ν
  rw [← Measure.map_prod_map μ ν measurable_inv measurable_inv,hμ,hν]

private theorem product_measurableInv (G H : Type*) [MeasurableSpace G] [MeasurableSpace H]
    [Inv G] [Inv H] [MeasurableInv G] [MeasurableInv H] : MeasurableInv (G × H) where
  measurable_inv := (measurable_inv.comp measurable_fst).prodMk (measurable_inv.comp measurable_snd)

theorem noise_inverse (β : ℝ) : (noise β).map Inv.inv=noise β := by
  let ν := increment β
  letI := increment_probability β
  letI m2 : MeasurableInv (SU2 × SU2) := product_measurableInv _ _
  letI m3 : MeasurableInv (SU2 × SU2 × SU2) := product_measurableInv _ _
  letI m4 : MeasurableInv (SU2 × SU2 × SU2 × SU2) := product_measurableInv _ _
  letI m5 : MeasurableInv (SU2 × SU2 × SU2 × SU2 × SU2) := product_measurableInv _ _
  letI m6 : MeasurableInv (SU2 × SU2 × SU2 × SU2 × SU2 × SU2) := product_measurableInv _ _
  have hν : ν.map Inv.inv=ν := increment_inv β
  have h2 := inverse_product ν ν hν hν
  have h3 := inverse_product ν (ν.prod ν) hν h2
  have h4 := inverse_product ν (ν.prod (ν.prod ν)) hν h3
  have h5 := inverse_product ν (ν.prod (ν.prod (ν.prod ν))) hν h4
  have h6 := inverse_product ν (ν.prod (ν.prod (ν.prod (ν.prod ν)))) hν h5
  have h7 := inverse_product ν (ν.prod (ν.prod (ν.prod (ν.prod (ν.prod ν))))) hν h6
  exact h7

def pairing (β : ℝ) (f g : State → ℝ) : ℝ := ∫ s, f s*SU2SevenLinkTransfer.step β g s ∂haar

private theorem joint_integrable (β : ℝ) (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |g s| ≤ C) :
    Integrable (fun p : State × State => f p.1*g (p.1*p.2)) (haar.prod (noise β)) := by
  letI := noise_probability β
  apply Integrable.of_bound ((hf.comp measurable_fst).mul (hg.comp continuous_mul.measurable)).aestronglyMeasurable
    (|B| * |C|)
  filter_upwards with p
  change ‖f p.1*g (p.1*p.2)‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul ((hb p.1).trans (le_abs_self B)) ((hc (p.1*p.2)).trans (le_abs_self C))
    (abs_nonneg _) (abs_nonneg _)

theorem pairing_noise (β : ℝ) (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |g s| ≤ C) :
    pairing β f g=∫ v, ∫ s, f s*g (s*v) ∂haar ∂noise β := by
  letI := noise_probability β
  unfold pairing SU2SevenLinkTransfer.step
  simp_rw [← integral_const_mul]
  exact integral_integral_swap (joint_integrable β f g hf hg B C hb hc)

/-- Reversibility on a genuine integrable bounded core; not a postulated symmetry. -/
theorem pairing_symmetric (β : ℝ) (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |g s| ≤ C) :
    pairing β f g=pairing β g f := by
  letI : (noise β).IsInvInvariant := ⟨noise_inverse β⟩
  rw [pairing_noise β f g hf hg B C hb hc]
  have hv (v : State) : (∫ s, f s*g (s*v) ∂haar)=∫ s, g s*f (s*v⁻¹) ∂haar := by
    have h := integral_mul_right_eq_self (μ := haar) (fun s => g s*f (s*v⁻¹)) v
    simp only [mul_inv_cancel_right] at h
    simpa only [mul_comm] using h
  simp_rw [hv]
  have h := integral_inv_eq_self (fun v : State => ∫ s, g s*f (s*v) ∂haar) (noise β)
  rw [h]
  exact (pairing_noise β g f hg hf C B hc hb).symm

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkVariational

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkVariational
open SU2SevenLinkTransfer

theorem pairing_product (β : ℝ) (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |g s| ≤ C) :
    pairing β f g=∫ p : State × State, f p.1*g (p.1*p.2) ∂haar.prod (noise β) := by
  letI := noise_probability β
  unfold pairing SU2SevenLinkTransfer.step
  simp_rw [← integral_const_mul]
  exact (integral_prod _ (joint_integrable β f g hf hg B C hb hc)).symm

theorem pairing_integrable (β : ℝ) (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |g s| ≤ C) :
    Integrable (fun s => f s*SU2SevenLinkTransfer.step β g s) haar := by
  letI := noise_probability β
  have h := (joint_integrable β f g hf hg B C hb hc).integral_prod_left
  simpa only [integral_const_mul,SU2SevenLinkTransfer.step] using h

/-- Integrated square comparison on the actual reversible seven-link law. -/
theorem pairing_square_comparison (β : ℝ) (u r : State → ℝ)
    (hu : Measurable u) (hr : Measurable r) (hpos : ∀ s, 0 ≤ u s)
    (U R : ℝ) (hU : ∀ s, |u s| ≤ U) (hR : ∀ s, |r s| ≤ R) :
    pairing β (fun s => u s*r s) (fun s => u s*r s) ≤
      pairing β (fun s => u s*r s^2) u := by
  letI := noise_probability β
  let A := fun s => u s*r s
  let B := fun s => u s*r s^2
  have hA : Measurable A := hu.mul hr
  have hB : Measurable B := hu.mul (hr.pow_const 2)
  have hbA (s : State) : |A s| ≤ |U| * |R| := by
    dsimp [A]
    rw [abs_mul]
    exact mul_le_mul ((hU s).trans (le_abs_self U)) ((hR s).trans (le_abs_self R)) (abs_nonneg _) (abs_nonneg _)
  have hbB (s : State) : |B s| ≤ |U| * |R|^2 := by
    dsimp [B]
    rw [abs_mul,abs_pow]
    exact mul_le_mul ((hU s).trans (le_abs_self U))
      (pow_le_pow_left₀ (abs_nonneg _) ((hR s).trans (le_abs_self R)) 2) (sq_nonneg _) (abs_nonneg _)
  have hi1 := joint_integrable β A A hA hA _ _ hbA hbA
  have hi2 := joint_integrable β B u hB hu _ U hbB hU
  have hi3 := joint_integrable β u B hu hB U _ hU hbB
  have hp (p : State × State) : A p.1*A (p.1*p.2) ≤
      (B p.1*u (p.1*p.2)+u p.1*B (p.1*p.2))/2 := by
    dsimp [A,B]
    nlinarith [mul_nonneg (mul_nonneg (hpos p.1) (hpos (p.1*p.2))) (sq_nonneg (r p.1-r (p.1*p.2)))]
  have hi := integral_mono hi1 ((hi2.add hi3).div_const 2) hp
  have hadd := integral_add hi2 hi3
  rw [integral_div] at hi
  change (∫ p : State × State, A p.1*A (p.1*p.2) ∂haar.prod (noise β)) ≤
    (∫ p : State × State, B p.1*u (p.1*p.2)+u p.1*B (p.1*p.2) ∂haar.prod (noise β))/2 at hi
  rw [hadd,← pairing_product β A A hA hA _ _ hbA hbA,
    ← pairing_product β B u hB hu _ U hbB hU,
    ← pairing_product β u B hu hB U _ hU hbB] at hi
  rw [pairing_symmetric β u B hu hB U _ hU hbB] at hi
  change pairing β A A ≤ pairing β B u
  linarith

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkVariational

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkVariational
open SU2SevenLinkTransfer

def halfWeight (t : ℝ) (s : State) : ℝ := Real.exp (t*first s/2)

theorem halfWeight_measurable (t : ℝ) : Measurable (halfWeight t) :=
  ((measurable_const.mul first_measurable).div_const 2).exp

theorem halfWeight_bound (t : ℝ) (s : State) : |halfWeight t s| ≤ Real.exp (|t|/2) := by
  rw [halfWeight,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h : t*first s ≤ |t| := calc
    _ ≤ |t*first s| := le_abs_self _
    _ = |t| * |first s| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (first_bound s) (abs_nonneg t)
    _ = |t| := mul_one _
  linarith

def spatialPairing (β t : ℝ) (f g : State → ℝ) : ℝ :=
  pairing β (fun s => halfWeight t s*f s) (fun s => halfWeight t s*g s)

theorem spatialPairing_integral (β t : ℝ) (f g : State → ℝ) :
    spatialPairing β t f g=∫ s, f s*spatialStep β t g s ∂haar := by
  unfold spatialPairing pairing spatialStep
  apply integral_congr_ae
  filter_upwards with s
  unfold halfWeight
  ring

/-- A positive supersolution yields an actual quadratic-form upper bound.
The explicit bounded domain u*r is sufficient for the proposed variational test;
this theorem does not construct a vacuum or a completed self-adjoint operator. -/
theorem supersolution_form_bound (β t q : ℝ) (u r : State → ℝ)
    (hu : Measurable u) (hr : Measurable r) (hpos : ∀ s, 0 ≤ u s)
    (U R : ℝ) (hU : ∀ s, |u s| ≤ U) (hR : ∀ s, |r s| ≤ R)
    (hsuper : ∀ s, spatialStep β t u s ≤ q*u s) :
    spatialPairing β t (fun s => u s*r s) (fun s => u s*r s) ≤
      q*(∫ s, (u s*r s)^2 ∂haar) := by
  let W := fun s => halfWeight t s*u s
  have hW : Measurable W := (halfWeight_measurable t).mul hu
  have hWpos (s : State) : 0 ≤ W s := mul_nonneg (Real.exp_pos _).le (hpos s)
  let D := Real.exp (|t|/2)*|U|
  have hbW (s : State) : |W s| ≤ D := by
    dsimp [W,D]
    rw [abs_mul]
    exact mul_le_mul (halfWeight_bound t s) ((hU s).trans (le_abs_self U)) (abs_nonneg _) (Real.exp_pos _).le
  have hB : Measurable (fun s => W s*r s^2) := hW.mul (hr.pow_const 2)
  have hbB (s : State) : |W s*r s^2| ≤ |D| * |R|^2 := by
    rw [abs_mul,abs_pow]
    exact mul_le_mul ((hbW s).trans (le_abs_self D))
      (pow_le_pow_left₀ (abs_nonneg _) ((hR s).trans (le_abs_self R)) 2) (sq_nonneg _) (abs_nonneg _)
  have hi := pairing_integrable β (fun s => W s*r s^2) W hB hW _ D hbB hbW
  have hsq : Integrable (fun s => (u s*r s)^2) haar := by
    apply Integrable.of_bound ((hu.mul hr).pow_const 2).aestronglyMeasurable ((|U| * |R|)^2)
    filter_upwards with s
    change ‖(u s*r s)^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_pow,abs_mul]
    exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_le_mul ((hU s).trans (le_abs_self U)) ((hR s).trans (le_abs_self R)) (abs_nonneg _) (abs_nonneg _)) 2
  have hp (s : State) : (W s*r s^2)*SU2SevenLinkTransfer.step β W s ≤ q*(u s*r s)^2 := by
    have h := mul_le_mul_of_nonneg_left (hsuper s) (mul_nonneg (hpos s) (sq_nonneg (r s)))
    change (u s*(r s)^2)*(halfWeight t s*SU2SevenLinkTransfer.step β W s) ≤
      (u s*(r s)^2)*(q*u s) at h
    dsimp [W]
    dsimp [W] at h
    nlinarith [h]
  have hiBound := integral_mono hi (hsq.const_mul q) hp
  rw [integral_const_mul] at hiBound
  have hs := pairing_square_comparison β W r hW hr hWpos D R hbW hR
  have he : spatialPairing β t (fun s => u s*r s) (fun s => u s*r s)=
      pairing β (fun s => W s*r s) (fun s => W s*r s) := by
    unfold spatialPairing
    congr 1 <;> funext s <;> dsimp [W] <;> ring
  rw [he]
  exact hs.trans hiBound

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkVariational

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkVariational
open SU2SevenLinkTransfer SU2WilsonGroundCertificate SU2WilsonConvolution

theorem trialVacuum_measurable (β t : ℝ) : Measurable (trialVacuum β t) := by
  unfold trialVacuum trial
  exact (halfWeight_measurable t).mul
    ((measurable_const.add (measurable_const.mul first_measurable)).add
      (measurable_const.mul ((first_measurable.pow_const 2).sub measurable_const)))

theorem trialVacuum_bound (β t : ℝ) (ht : |t| ≤ 1) (s : State) :
    |trialVacuum β t s| ≤ Real.exp (|t|/2)*
      (1+|linearCoefficient (coefficient β^4)|+
        |quadraticTrialCoefficient (coefficient β^4) (SU2QuadraticWilsonChannel.quadraticCoefficient β^4)|) := by
  change |halfWeight t s*trial _ _ t (first s)| ≤ _
  rw [abs_mul]
  exact mul_le_mul (halfWeight_bound t s) (trial_bound _ _ _ _ ht (first_bound s)) (abs_nonneg _) (Real.exp_pos _).le

/-- The verified vacuum upper certificate now controls the actual spatial form
on the explicitly displayed bounded reweighted domain. -/
theorem trialVacuum_form_bound (β t : ℝ) (ht : |t| ≤ 1)
    (hsmall : |linearCoefficient (coefficient β^4)| * |t|+
      |quadraticTrialCoefficient (coefficient β^4) (SU2QuadraticWilsonChannel.quadraticCoefficient β^4)| * |t|^2 ≤ 1/2)
    (r : State → ℝ) (hr : Measurable r) (R : ℝ) (hR : ∀ s, |r s| ≤ R) :
    spatialPairing β t (fun s => trialVacuum β t s*r s) (fun s => trialVacuum β t s*r s) ≤
      (1+vacuumSecond (coefficient β^4)*t^2+
        2*eigenErrorConstant (coefficient β^4) (SU2QuadraticWilsonChannel.quadraticCoefficient β^4)*|t|^3)*
      (∫ s, (trialVacuum β t s*r s)^2 ∂haar) := by
  exact supersolution_form_bound β t _ (trialVacuum β t) r (trialVacuum_measurable β t) hr
    (fun s => (trialVacuum_positive β t hsmall s).le) _ R (trialVacuum_bound β t ht) hR
    (spatialStep_trialVacuum_supersolution β t ht hsmall)

/-- Conjugating the variational trial removes the spatial exponential from its
kinetic numerator, leaving the exponential only in the Haar denominator. -/
def unweight (t : ℝ) (f : State → ℝ) (s : State) : ℝ := Real.exp (-t*first s/2)*f s

theorem unweight_measurable (t : ℝ) (f : State → ℝ) (hf : Measurable f) :
    Measurable (unweight t f) :=
  (((measurable_const.mul first_measurable).div_const 2).exp).mul hf

theorem halfWeight_unweight (t : ℝ) (f : State → ℝ) (s : State) :
    halfWeight t s*unweight t f s=f s := by
  unfold halfWeight unweight
  rw [← mul_assoc,← Real.exp_add,show t*first s/2+ -t*first s/2=0 by ring,Real.exp_zero,one_mul]

theorem spatialPairing_unweight (β t : ℝ) (f g : State → ℝ) :
    spatialPairing β t (unweight t f) (unweight t g)=pairing β f g := by
  unfold spatialPairing
  simp_rw [halfWeight_unweight]

theorem unweight_square_integral (t : ℝ) (f : State → ℝ) :
    (∫ s, (unweight t f s)^2 ∂haar)=∫ s, Real.exp (-t*first s)*(f s)^2 ∂haar := by
  apply integral_congr_ae
  filter_upwards with s
  unfold unweight
  rw [mul_pow,pow_two (Real.exp _),← Real.exp_add,
    show -t*first s/2+ -t*first s/2= -t*first s by ring]

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkVariational
