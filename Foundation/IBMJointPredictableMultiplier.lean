import Foundation.IBMCompletedTimeCutoff

/-! Full signed joint-energy bounds for actual bounded predictable multipliers. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMJointPredictableMultiplier
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableLpDictionary
open IBMJointPredictableEnergyMeasure IBMPredictableCovarianceMeasure
open IBMCompletedSignedCovarianceIntegral IBMCovarianceCauchySchwarz
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
set_option backward.isDefEq.respectTransparency false

structure BoundedPredictable where
  function : Space → ℝ
  measurable : Measurable function
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounded : ∀ p, ‖function p‖ ≤ bound

theorem multiply_memLp (g : BoundedPredictable) (F : JointL2) (H : PredictableL2 F) :
    MemLp (g.function * (H : Space → ℝ)) 2 (predictableMeasure F) := by
  apply (Lp.memLp H).of_le_mul (c := g.bound)
    (g.measurable.aestronglyMeasurable.mul (Lp.memLp H).aestronglyMeasurable)
  exact Eventually.of_forall fun p => (norm_mul _ _).le.trans
    (mul_le_mul_of_nonneg_right (g.bounded p) (norm_nonneg _))

def multiply (g : BoundedPredictable) (F : JointL2) (H : PredictableL2 F) : PredictableL2 F :=
  (multiply_memLp g F H).toLp _

theorem multiply_ae (g : BoundedPredictable) (F : JointL2) (H : PredictableL2 F) :
    multiply g F H =ᵐ[predictableMeasure F] g.function * H := (multiply_memLp g F H).coeFn_toLp

def multiplyLinear (g : BoundedPredictable) (F : JointL2) : PredictableL2 F →ₗ[ℝ] PredictableL2 F where
  toFun := multiply g F
  map_add' H K := by
    apply Lp.ext
    filter_upwards [multiply_ae g F (H+K), multiply_ae g F H, multiply_ae g F K,
      Lp.coeFn_add H K, Lp.coeFn_add (multiply g F H) (multiply g F K)] with p hc hh hk hs ht
    rw [hc, ht, Pi.add_apply, hh, hk]
    simp only [Pi.mul_apply] at *
    rw [hs, Pi.add_apply, mul_add]
  map_smul' a H := by
    apply Lp.ext
    filter_upwards [multiply_ae g F (a • H), multiply_ae g F H,
      Lp.coeFn_smul a H, Lp.coeFn_smul a (multiply g F H)] with p hc hh hs ht
    change multiply g F (a • H) p = (a • multiply g F H) p
    rw [hc, ht, Pi.smul_apply, hh]
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at *
    rw [hs]
    ring

theorem multiply_norm (g : BoundedPredictable) (F : JointL2) (H : PredictableL2 F) :
    ‖multiply g F H‖ ≤ g.bound*‖H‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae g F H] with p hp
  rw [hp, Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (g.bounded p) (norm_nonneg _)

def multiplier (g : BoundedPredictable) (F : JointL2) : PredictableL2 F →L[ℝ] PredictableL2 F :=
  (multiplyLinear g F).mkContinuous g.bound (fun H => multiply_norm g F H)

theorem multiplier_ae (g : BoundedPredictable) (F : JointL2) (H : PredictableL2 F) :
    multiplier g F H =ᵐ[predictableMeasure F] g.function * H := multiply_ae g F H

theorem square_bound (g : BoundedPredictable) (p : Space) : g.function p ^ 2 ≤ g.bound ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (g.function p)) (g.bounded p) 2
  simpa only [Real.norm_eq_abs, sq_abs] using h

def complement (g : BoundedPredictable) : BoundedPredictable where
  function p := Real.sqrt (g.bound^2-g.function p^2)
  measurable := Real.continuous_sqrt.measurable.comp (measurable_const.sub (g.measurable.pow_const 2))
  bound := g.bound
  bound_nonneg := g.bound_nonneg
  bounded p := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_iff.mpr
    exact ⟨g.bound_nonneg, by nlinarith [sq_nonneg (g.function p)]⟩

theorem square_partition (g : BoundedPredictable) (p : Space) :
    g.function p^2 + (complement g).function p^2 = g.bound^2 := by
  have h := Real.sq_sqrt (sub_nonneg.mpr (square_bound g p))
  change g.function p^2 + (Real.sqrt (g.bound^2-g.function p^2))^2 = g.bound^2
  linarith

theorem pairing_partition (g : BoundedPredictable) (F G : JointL2)
    (H : PredictableL2 F) (K : PredictableL2 G) :
    inner ℝ (IBMFullPredictableIntegral.integral F (multiplier g F H))
      (IBMFullPredictableIntegral.integral G (multiplier g G K)) +
    inner ℝ (IBMFullPredictableIntegral.integral F (multiplier (complement g) F H))
      (IBMFullPredictableIntegral.integral G (multiplier (complement g) G K)) =
    g.bound^2 * inner ℝ (IBMFullPredictableIntegral.integral F H) (IBMFullPredictableIntegral.integral G K) := by
  rw [← actual_completed_signed_identity, ← actual_completed_signed_identity,
    ← actual_completed_signed_identity, ← VectorMeasure.integral_add
      (product_integrable F G (Lp.memLp (multiplier g F H)) (Lp.memLp (multiplier g G K)))
      (product_integrable F G (Lp.memLp (multiplier (complement g) F H))
        (Lp.memLp (multiplier (complement g) G K)))]
  have he : (fun p => multiplier g F H p*multiplier g G K p +
      multiplier (complement g) F H p*multiplier (complement g) G K p) =ᵐ[(covariance F G).variation]
      (fun p => g.bound^2 * (H p*K p)) := by
    filter_upwards [(variation_ac_left F G).ae_le (multiplier_ae g F H),
      (variation_ac_right F G).ae_le (multiplier_ae g G K),
      (variation_ac_left F G).ae_le (multiplier_ae (complement g) F H),
      (variation_ac_right F G).ae_le (multiplier_ae (complement g) G K)] with p h1 h2 h3 h4
    rw [h1,h2,h3,h4]
    simp only [Pi.mul_apply]
    have hp := square_partition g p
    nlinarith [congrArg (fun x : ℝ => x*(H p*K p)) hp]
  calc
    _ = (∫ᵛ p, g.bound^2*(H p*K p) ∂<•covariance F G) :=
      VectorMeasure.integral_congr_ae (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) he
    _ = _ := by
      simpa only [smul_eq_mul] using VectorMeasure.integral_fun_smul (covariance F G)
        (ContinuousLinearMap.lsmul ℝ ℝ).flip (g.bound^2) (fun p => H p*K p)

theorem finite_energy_partition {ι : Type*} (g : BoundedPredictable) (F : ι → JointL2)
    (s : Finset ι) (H : ∀ i, PredictableL2 (F i)) :
    IBMMultichannelCompletion.finiteEnergy F s (fun i => multiplier g (F i) (H i)) +
      IBMMultichannelCompletion.finiteEnergy F s (fun i => multiplier (complement g) (F i) (H i)) =
      g.bound^2 * IBMMultichannelCompletion.finiteEnergy F s H := by
  simp only [IBMMultichannelCompletion.finiteEnergy_actual, ← real_inner_self_eq_norm_sq,
    sum_inner, inner_sum]
  rw [← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, ← Finset.mul_sum, pairing_partition]

theorem finite_energy_bound {ι : Type*} (g : BoundedPredictable) (F : ι → JointL2)
    (s : Finset ι) (H : ∀ i, PredictableL2 (F i)) :
    IBMMultichannelCompletion.finiteEnergy F s (fun i => multiplier g (F i) (H i)) ≤
      g.bound^2 * IBMMultichannelCompletion.finiteEnergy F s H := by
  have he := finite_energy_partition g F s H
  have hn : 0 ≤ IBMMultichannelCompletion.finiteEnergy F s
      (fun i => multiplier (complement g) (F i) (H i)) := by
    rw [IBMMultichannelCompletion.finiteEnergy_actual]
    positivity
  linarith



theorem finite_stochastic_bound {ι : Type*} (g : BoundedPredictable) (F : ι → JointL2)
    (s : Finset ι) (H : ∀ i, PredictableL2 (F i)) :
    ‖∑ i ∈ s, IBMFullPredictableIntegral.integral (F i) (multiplier g (F i) (H i))‖ ≤
      g.bound*‖∑ i ∈ s, IBMFullPredictableIntegral.integral (F i) (H i)‖ := by
  have he := finite_energy_bound g F s H
  rw [IBMMultichannelCompletion.finiteEnergy_actual,
    IBMMultichannelCompletion.finiteEnergy_actual] at he
  rw [← mul_pow] at he
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg g.bound_nonneg (norm_nonneg _))).mp he

def constant (a : ℝ) : BoundedPredictable where
  function _ := a
  measurable := measurable_const
  bound := ‖a‖
  bound_nonneg := norm_nonneg a
  bounded _ := le_rfl

def add (g h : BoundedPredictable) : BoundedPredictable where
  function p := g.function p+h.function p
  measurable := g.measurable.add h.measurable
  bound := g.bound+h.bound
  bound_nonneg := add_nonneg g.bound_nonneg h.bound_nonneg
  bounded p := (norm_add_le _ _).trans (add_le_add (g.bounded p) (h.bounded p))

def mul (g h : BoundedPredictable) : BoundedPredictable where
  function p := g.function p*h.function p
  measurable := g.measurable.mul h.measurable
  bound := g.bound*h.bound
  bound_nonneg := mul_nonneg g.bound_nonneg h.bound_nonneg
  bounded p := by
    rw [norm_mul]
    exact mul_le_mul (g.bounded p) (h.bounded p) (norm_nonneg _) g.bound_nonneg

theorem multiplier_congr (g h : BoundedPredictable) (he : ∀ p, g.function p=h.function p)
    (F : JointL2) (H : PredictableL2 F) : multiplier g F H = multiplier h F H := by
  apply Lp.ext
  filter_upwards [multiplier_ae g F H, multiplier_ae h F H] with p hg hh
  rw [hg,hh,Pi.mul_apply,Pi.mul_apply,he]

theorem multiplier_constant (a : ℝ) (F : JointL2) (H : PredictableL2 F) :
    multiplier (constant a) F H = a • H := by
  apply Lp.ext
  filter_upwards [multiplier_ae (constant a) F H, Lp.coeFn_smul a H] with p hp hs
  rw [hp,hs]
  rfl

theorem multiplier_add (g h : BoundedPredictable) (F : JointL2) (H : PredictableL2 F) :
    multiplier (add g h) F H = multiplier g F H+multiplier h F H := by
  apply Lp.ext
  filter_upwards [multiplier_ae (add g h) F H, multiplier_ae g F H, multiplier_ae h F H,
    Lp.coeFn_add (multiplier g F H) (multiplier h F H)] with p hp hg hh hs
  rw [hp,hs,Pi.add_apply,hg,hh]
  change (g.function p+h.function p)*H p = g.function p*H p+h.function p*H p
  ring

theorem multiplier_mul (g h : BoundedPredictable) (F : JointL2) (H : PredictableL2 F) :
    multiplier (mul g h) F H = multiplier g F (multiplier h F H) := by
  apply Lp.ext
  filter_upwards [multiplier_ae (mul g h) F H,
    multiplier_ae g F (multiplier h F H), multiplier_ae h F H] with p hp hg hh
  rw [hp,hg,Pi.mul_apply,Pi.mul_apply,hh]
  change (g.function p*h.function p)*H p = g.function p*(h.function p*H p)
  ring

end OperatorDerivativeRewrite.Foundation.IBMJointPredictableMultiplier
