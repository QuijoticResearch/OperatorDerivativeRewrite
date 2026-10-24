import Foundation.IBMTimeWeightedClockStrong
import Foundation.IBMIntrinsicChainEnergy
import Foundation.FiniteMeasureL2Integration

/-! Actual weighted IBM observables and their ORIGINAL full joint derivative
depend continuously on time-L2 classes. Both channels share the same input. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightedGraphOperator
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMClockOverlapEnergy IBMTimeWeightedClockOperator IBMTimeWeightedSineValue
open IBMTimeWeightedSineCalculus
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem timeL1_bound (T : ℝ≥0) (g : TimeL2 T) :
    (∫ t, ‖g t‖ ∂window T) ≤ Real.sqrt T * ‖g‖ := by
  have hb := FiniteMeasureL2Integration.square_integral_le (fun t => ‖g t‖) (Lp.memLp g).norm
  change (∫ t, ‖g t‖ ∂window T)^2 ≤
    (window T).real univ * (∫ t, ‖g t‖^2 ∂window T) at hb
  have hm : (window T).real univ = (T:ℝ) :=
    IBMNonlinearClockEnergy.window_mass (T := (T:ℝ)) T.property
  rw [hm,← BochnerL2Dominated.norm_sq_integral g] at hb
  have hs : (Real.sqrt (T:ℝ))^2 = (T:ℝ) := Real.sq_sqrt T.property
  have he : (Real.sqrt T * ‖g‖)^2 = (T:ℝ)*‖g‖^2 := by
    rw [mul_pow,hs]
  have hp := mul_nonneg (Real.sqrt_nonneg (T:ℝ)) (norm_nonneg g)
  have hI : 0 ≤ ∫ t, ‖g t‖ ∂window T := integral_nonneg (fun t => norm_nonneg (g t))
  nlinarith

def valueLinear (T : ℝ≥0) : TimeL2 T →ₗ[ℝ] IntrinsicSpace where
  toFun g := actual g T
  map_add' g h := by
    rw [actual_congr_ae _ _ T (Lp.coeFn_add g h)]
    unfold actual
    simp only [Pi.add_apply,add_smul]
    exact integral_add (intrinsic_integrable g T (Lp.memLp g))
      (intrinsic_integrable h T (Lp.memLp h))
  map_smul' c g := by
    change actual (⇑(c • g)) T = c • actual g T
    rw [actual_congr_ae _ _ T (Lp.coeFn_smul c g)]
    unfold actual
    simp only [Pi.smul_apply,smul_eq_mul,mul_smul]
    exact integral_smul c _

theorem value_bound (T : ℝ≥0) (g : TimeL2 T) : ‖valueLinear T g‖ ≤ Real.sqrt T * ‖g‖ := by
  change ‖∫ t, g t • IBMActualSineDomainObstruction.sinePoint t.toNNReal ∂window T‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans
  apply le_trans _ (timeL1_bound T g)
  apply integral_mono_ae (intrinsic_integrable g T (Lp.memLp g)).norm
    ((Lp.memLp g).integrable (by norm_num)).norm
  exact ae_of_all _ fun t => by
    change ‖g t • IBMActualSineDomainObstruction.sinePoint t.toNNReal‖ ≤ ‖g t‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (point_norm_le _) (norm_nonneg _)).trans_eq (mul_one _)

def valueOperator (T : ℝ≥0) : TimeL2 T →L[ℝ] IntrinsicSpace :=
  (valueLinear T).mkContinuous (Real.sqrt T) (value_bound T)

def domainLinear (T : ℝ≥0) : TimeL2 T →ₗ[ℝ] jointDerivative.domain :=
  (valueLinear T).codRestrict jointDerivative.domain (fun g => actual_joint_domain g T (Lp.memLp g))

def derivativeLinear (T : ℝ≥0) : TimeL2 T →ₗ[ℝ] JointFieldSpace :=
  jointDerivative.toFun.comp (domainLinear T)

theorem derivative_eq (T : ℝ≥0) (g : TimeL2 T) :
    derivativeLinear T g = gradient g T (Lp.memLp g) := rfl

attribute [local irreducible] actual gradient domainValue valueLinear derivativeLinear

theorem clock_bound (T : ℝ≥0) (g : TimeL2 T) :
    ‖gradient g T (Lp.memLp g) 1‖ ≤ bound T * ‖g‖ :=
  le_of_tendsto (IBMTimeWeightedClockStrong.native_tendsto g T (Lp.memLp g)).norm
    (Eventually.of_forall fun n => nativeLinear_bound n T g)

theorem source_bound (T : ℝ≥0) (g : TimeL2 T) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t ∈ Icc (0 : ℝ≥0) T,
      ‖IBMActualSineDomainObstruction.sineSourceGradient t‖ ≤ C) :
    ‖gradient g T (Lp.memLp g) 0‖ ≤ (C*Real.sqrt T)*‖g‖ := by
  rw [source_formula]
  change ‖∫ t, g t • IBMActualSineDomainObstruction.sineSourceGradient t.toNNReal ∂window T‖ ≤ _
  calc
    _ ≤ ∫ t, ‖g t • IBMActualSineDomainObstruction.sineSourceGradient t.toNNReal‖ ∂window T :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖g t‖*C ∂window T := by
      apply integral_mono_ae (source_integrable g T (Lp.memLp g)).norm
        (((Lp.memLp g).integrable (by norm_num)).norm.mul_const C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (hb t.toNNReal ⟨by positivity,Real.toNNReal_le_iff_le_coe.mpr ht.2⟩) (norm_nonneg _)
    _ = C*(∫ t, ‖g t‖ ∂window T) := by rw [integral_mul_const]; ring
    _ ≤ C*(Real.sqrt T*‖g‖) := mul_le_mul_of_nonneg_left (timeL1_bound T g) hC
    _ = _ := by ring

theorem derivative_bounded (T : ℝ≥0) : ∃ C : ℝ, ∀ g : TimeL2 T,
    ‖derivativeLinear T g‖ ≤ C * ‖g‖ := by
  obtain ⟨C,hC,hb⟩ := IBMSineAverageSourceDomain.sourceGradient_bounded T
  refine ⟨C*Real.sqrt T+bound T,fun g => ?_⟩
  rw [derivative_eq]
  have hs := source_bound T g C hC hb
  have hc := clock_bound T g
  have hj := IBMIntrinsicChainEnergy.joint_norm_sq (gradient g T (Lp.memLp g))
  have hsum : ‖gradient g T (Lp.memLp g)‖ ≤
      ‖gradient g T (Lp.memLp g) 0‖+‖gradient g T (Lp.memLp g) 1‖ := by
    nlinarith [norm_nonneg (gradient g T (Lp.memLp g)),
      norm_nonneg (gradient g T (Lp.memLp g) 0),norm_nonneg (gradient g T (Lp.memLp g) 1),
      mul_nonneg (norm_nonneg (gradient g T (Lp.memLp g) 0))
        (norm_nonneg (gradient g T (Lp.memLp g) 1))]
  nlinarith

def derivativeOperator (T : ℝ≥0) : TimeL2 T →L[ℝ] JointFieldSpace :=
  (derivativeLinear T).mkContinuousOfExistsBound (derivative_bounded T)

def graphOperator (T : ℝ≥0) : TimeL2 T →L[ℝ] (IntrinsicSpace × JointFieldSpace) :=
  (valueOperator T).prod (derivativeOperator T)

theorem graphOperator_eq (T : ℝ≥0) (g : TimeL2 T) : graphOperator T g =
    (actual g T,gradient g T (Lp.memLp g)) := by
  change (valueLinear T g,derivativeLinear T g) = _
  rw [derivative_eq]
  unfold valueLinear
  rfl

theorem graphOperator_mem (T : ℝ≥0) (g : TimeL2 T) :
    graphOperator T g ∈ jointDerivative.graph := by
  rw [graphOperator_eq]
  simpa only [gradient,domainValue] using jointDerivative.mem_graph (domainValue g T (Lp.memLp g))

theorem graph_tendsto (T : ℝ≥0) (g : ℕ → TimeL2 T) (u : TimeL2 T)
    (hg : Tendsto g atTop (𝓝 u)) :
    Tendsto (fun n => (actual (g n) T,gradient (g n) T (Lp.memLp (g n)))) atTop
      (𝓝 (actual u T,gradient u T (Lp.memLp u))) := by
  simpa only [Function.comp_def,graphOperator_eq] using
    (graphOperator T).continuous.continuousAt.tendsto.comp hg

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightedGraphOperator
