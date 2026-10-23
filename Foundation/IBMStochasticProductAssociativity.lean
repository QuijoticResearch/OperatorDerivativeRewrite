import Foundation.IBMStochasticIntegratorEnergy

/-! Literal product-domain isometry and actual stochastic associativity on
the full original output-channel predictable L2 space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMStochasticProductAssociativity
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableLpDictionary
open IBMJointPredictableEnergyMeasure IBMStochasticIntegratorEnergy
open IBMJointPredictableMultiplier IBMPredictableRectanglePullout
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
set_option backward.isDefEq.respectTransparency false
variable (F : JointL2) (H : PredictableL2 F)

theorem density_measurable : Measurable (fun p => ENNReal.ofReal (H p^2)) :=
  ((Lp.stronglyMeasurable H).measurable.pow_const 2).ennreal_ofReal

theorem change_integrable (f : Space → ℝ)
    (hf : Integrable f (predictableMeasure (IBMFullPredictableIntegral.integral F H))) :
    Integrable f (weightedMeasure F H) := by
  rw [energy_change F H] at hf
  exact hf

theorem change_integral (f : Space → ℝ) :
    (∫ p, f p ∂predictableMeasure (IBMFullPredictableIntegral.integral F H)) =
      ∫ p, f p ∂weightedMeasure F H := by rw [energy_change F H]

theorem product_memLp (K : PredictableL2 (IBMFullPredictableIntegral.integral F H)) :
    MemLp (fun p => H p*K p) 2 (predictableMeasure F) := by
  have hK := change_integrable F H (fun p => K p^2) (Lp.memLp K).integrable_sq
  change Integrable (fun p => K p^2)
    ((predictableMeasure F).withDensity (fun p => ENNReal.ofReal (H p^2))) at hK
  have hi := (integrable_withDensity_iff_integrable_smul₀' (density_measurable F H).aemeasurable
    (Eventually.of_forall fun p => ENNReal.ofReal_lt_top)).mp hK
  apply (memLp_two_iff_integrable_sq
    ((Lp.stronglyMeasurable H).mul (Lp.stronglyMeasurable K)).aestronglyMeasurable).mpr
  convert hi using 1
  funext p
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  simp only [smul_eq_mul,Pi.mul_apply,mul_pow]

def product (K : PredictableL2 (IBMFullPredictableIntegral.integral F H)) : PredictableL2 F :=
  (product_memLp F H K).toLp _

theorem product_ae (K : PredictableL2 (IBMFullPredictableIntegral.integral F H)) :
    product F H K =ᵐ[predictableMeasure F] (fun p => H p*K p) := (product_memLp F H K).coeFn_toLp

theorem weighted_ae {k l : Space → ℝ}
    (he : k =ᵐ[predictableMeasure (IBMFullPredictableIntegral.integral F H)] l) :
    (fun p => H p*k p) =ᵐ[predictableMeasure F] (fun p => H p*l p) := by
  rw [energy_change F H] at he
  have hh := (ae_withDensity_iff (density_measurable F H)).mp he
  filter_upwards [hh] with p hp
  by_cases hz : H p=0
  · simp only [hz,zero_mul]
  · rw [hp (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hz)).ne']

def productLinear : PredictableL2 (IBMFullPredictableIntegral.integral F H) →ₗ[ℝ] PredictableL2 F where
  toFun := product F H
  map_add' K L := by
    apply Lp.ext
    have hc := weighted_ae F H (Lp.coeFn_add K L)
    filter_upwards [hc,product_ae F H (K+L),product_ae F H K,product_ae F H L,
      Lp.coeFn_add (product F H K) (product F H L)] with p hc hp hk hl hs
    simp only [Pi.add_apply] at hc hs ⊢
    rw [hp,hc,hs,hk,hl,mul_add]
  map_smul' a K := by
    apply Lp.ext
    have hc := weighted_ae F H (Lp.coeFn_smul a K)
    filter_upwards [hc,product_ae F H (a • K),product_ae F H K,
      Lp.coeFn_smul a (product F H K)] with p hc hp hk hs
    change product F H (a • K) p = (a • product F H K) p
    simp only [Pi.smul_apply] at hc hs ⊢
    rw [hp,hc,hs,hk]
    simp only [smul_eq_mul]
    ring

theorem product_norm (K : PredictableL2 (IBMFullPredictableIntegral.integral F H)) :
    ‖product F H K‖ = ‖K‖ := by
  have he : ‖product F H K‖^2=‖K‖^2 := by
    rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def]
    rw [change_integral F H (fun p => inner ℝ (K p) (K p))]
    change (∫ p, inner ℝ (product F H K p) (product F H K p) ∂predictableMeasure F) =
      ∫ p, inner ℝ (K p) (K p) ∂(predictableMeasure F).withDensity (fun p => ENNReal.ofReal (H p^2))
    rw [integral_withDensity_eq_integral_toReal_smul (density_measurable F H)
      (Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [product_ae F H K] with p hp
    rw [hp,ENNReal.toReal_ofReal (sq_nonneg _)]
    simp only [Real.inner_apply,smul_eq_mul]
    ring
  nlinarith [norm_nonneg (product F H K),norm_nonneg K]

def productIsometry : PredictableL2 (IBMFullPredictableIntegral.integral F H) →ₗᵢ[ℝ] PredictableL2 F where
  toLinearMap := productLinear F H
  norm_map' := product_norm F H

theorem product_cell (d : IBMPredictableFiniteIntegral.Index) :
    productIsometry F H (cell (IBMFullPredictableIntegral.integral F H) d) =
      multiplier (rectangleMultiplier (IBMPredictableFiniteIntegral.left d) (IBMPredictableFiniteIntegral.right d)
        (IBMPredictableFiniteIntegral.event d) (IBMPredictableFiniteIntegral.event_measurable d)) F H := by
  apply Lp.ext
  have hc := weighted_ae F H (cell_ae (IBMFullPredictableIntegral.integral F H) d)
  filter_upwards [hc,product_ae F H (cell (IBMFullPredictableIntegral.integral F H) d),
    multiplier_ae (rectangleMultiplier (IBMPredictableFiniteIntegral.left d) (IBMPredictableFiniteIntegral.right d)
      (IBMPredictableFiniteIntegral.event d) (IBMPredictableFiniteIntegral.event_measurable d)) F H]
    with p hc hp hm
  change product F H _ p = _
  rw [hp,hc,hm]
  change H p*IBMPredictableFiniteIntegral.basisProcess d p =
    IBMPredictableFiniteIntegral.basisProcess d p*H p
  exact mul_comm _ _

theorem actual_associativity (K : PredictableL2 (IBMFullPredictableIntegral.integral F H)) :
    IBMFullPredictableIntegral.integral F (productIsometry F H K) =
      IBMFullPredictableIntegral.integral (IBMFullPredictableIntegral.integral F H) K := by
  let Y := IBMFullPredictableIntegral.integral F H
  let L : PredictableL2 Y →L[ℝ] JointL2 :=
    (IBMFullPredictableIntegral.integral F).toContinuousLinearMap.comp (productIsometry F H).toContinuousLinearMap
  let R : PredictableL2 Y →L[ℝ] JointL2 := (IBMFullPredictableIntegral.integral Y).toContinuousLinearMap
  have he : L.toLinearMap.comp (dictionary Y) = R.toLinearMap.comp (dictionary Y) := by
    apply Finsupp.lhom_ext'
    intro d
    apply LinearMap.ext
    intro a
    have hc : dictionary Y (Finsupp.single d a)=a • cell Y d := by
      rw [show Finsupp.single d a=a • Finsupp.single d 1 by simp,map_smul]
      rfl
    change L (dictionary Y (Finsupp.single d a))=R (dictionary Y (Finsupp.single d a))
    rw [hc,map_smul,map_smul]
    apply congrArg (fun v : JointL2 => a • v)
    change IBMFullPredictableIntegral.integral F (productIsometry F H (cell Y d)) =
      IBMFullPredictableIntegral.integral Y (cell Y d)
    rw [product_cell,rectangle_integral F (IBMPredictableFiniteIntegral.ordered d),
      stepOutput_eq_stepClass _ (IBMPredictableFiniteIntegral.ordered d),cell_integral]
    rfl
  exact congrFun ((IBMPredictableDictionaryDensity.dictionary_dense Y).equalizer L.continuous R.continuous
    (funext fun l => DFunLike.congr_fun he l)) K



local instance (Y : JointL2) : IsFiniteMeasure (predictableMeasure Y) := finite_measure Y

def boundedClass (g : BoundedPredictable) (Y : JointL2) : PredictableL2 Y :=
  (MemLp.of_bound g.measurable.aestronglyMeasurable g.bound
    (Eventually.of_forall g.bounded)).toLp g.function

theorem boundedClass_ae (g : BoundedPredictable) (Y : JointL2) :
    boundedClass g Y =ᵐ[predictableMeasure Y] g.function :=
  (MemLp.of_bound g.measurable.aestronglyMeasurable g.bound
    (Eventually.of_forall g.bounded)).coeFn_toLp

theorem bounded_product (g : BoundedPredictable) :
    productIsometry F H (boundedClass g (IBMFullPredictableIntegral.integral F H)) = multiplier g F H := by
  apply Lp.ext
  have hc := weighted_ae F H (boundedClass_ae g (IBMFullPredictableIntegral.integral F H))
  filter_upwards [hc,product_ae F H (boundedClass g (IBMFullPredictableIntegral.integral F H)),
    multiplier_ae g F H] with p hc hp hm
  change product F H _ p = _
  rw [hp,hc,hm,Pi.mul_apply]
  exact mul_comm _ _

theorem bounded_associativity (g : BoundedPredictable) :
    IBMFullPredictableIntegral.integral (IBMFullPredictableIntegral.integral F H)
      (boundedClass g (IBMFullPredictableIntegral.integral F H)) =
      IBMFullPredictableIntegral.integral F (multiplier g F H) := by
  rw [← actual_associativity F H,bounded_product]

open IBMMultichannelCompletion
attribute [local instance] componentAdd componentGroup componentModule componentZeroDec

theorem completed_single_associativity {ι : Type*} [DecidableEq ι] (G : ι → JointL2)
    (i : ι) (h : PredictableL2 (G i)) (g : BoundedPredictable) :
    completedIntegral G (IBMCompletedPredictableMultiplier.operator G g
      (IBMMultichannelCompletion.embed G (DirectSum.lof ℝ ι _ i h))) =
      IBMFullPredictableIntegral.integral (IBMFullPredictableIntegral.integral (G i) h)
        (boundedClass g (IBMFullPredictableIntegral.integral (G i) h)) := by
  rw [IBMCompletedPredictableMultiplier.operator_single,completedIntegral_embed,rawIntegral_single]
  exact (bounded_associativity (G i) h g).symm

end OperatorDerivativeRewrite.Foundation.IBMStochasticProductAssociativity
