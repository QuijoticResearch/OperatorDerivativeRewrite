import Foundation.IBMQuarticScalarRecovery

/-! The native joint class is the literal scalar Itô--Tanaka correction
formed from the actual scenery fields and continuous Tanaka mass path.
Product coordinates remain (clock, source). -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticLiteralJoint
open InfiniteGaussian IBMQuarticScalarRecovery IBMQuarticTimeProjection
open IBMQuarticJointRealization IBMQuarticOriginProjection

def originValue (n : ℕ) (ω : SampleSpace) : ℝ :=
  (1/6 : ℝ)*(IBMDyadicExtension.field n 0 ω 0)^3*IBMDyadicExtension.field n 1 ω 0

theorem originValue_measurable (n : ℕ) : Measurable (originValue n) :=
  (((IBMDyadicExtension.field_coordinate_measurable n 0 0).pow_const 3).const_mul (1/6 : ℝ)).mul
    (IBMDyadicExtension.field_coordinate_measurable n 1 0)

def scalarWhole (n : ℕ) (T : ℝ≥0) (p : SampleSpace × SampleSpace) : ℝ :=
  BrownianMassContinuousLimit.limitPath p.1 T * originValue n p.2 +
    (1/2 : ℝ)*scalarTimeIntegral n T p

theorem scalarWhole_measurable (n : ℕ) (T : ℝ≥0) : Measurable (scalarWhole n T) := by
  have hm : Measurable (fun p : SampleSpace × SampleSpace => BrownianMassContinuousLimit.limitPath p.1 T) :=
    BrownianMassLimitIdentification.jointly_measurable.comp (measurable_const.prodMk measurable_fst)
  exact (hm.mul ((originValue_measurable n).comp measurable_snd)).add
    ((scalarTimeIntegral_measurable n T).const_mul (1/2 : ℝ))

theorem whole_scalar_sections (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ ωY ∂gaussianProduct, wholeCorrection n T ωY =ᵐ[gaussianProduct]
      fun ωX => scalarWhole n T (ωY,ωX) := by
  have hm : BrownianMassLimitIdentification.coordinateClass T =ᵐ[gaussianProduct]
      fun ω => BrownianMassContinuousLimit.limitPath ω T :=
    MemLp.coeFn_toLp (BrownianMassLimitIdentification.coordinate_memLp T)
  filter_upwards [hm] with ωY hm
  let a : ℝ := BrownianMassLimitIdentification.coordinateClass T ωY
  let V : GaussianL2 := ∫ s in 0..(T : ℝ), IBMQuarticSecondGeometry.spatialQuartic n
    |IBMConstructedSources.clockPath ωY s.toNNReal|
  have hv : V =ᵐ[gaussianProduct] fun ωX => scalarTimeIntegral n T (ωY,ωX) :=
    integratedCurvature_coeFn n ωY T
  have ho : originClass n =ᵐ[gaussianProduct] originValue n := originClass_coeFn n
  filter_upwards [Lp.coeFn_add (a • originClass n) ((1/2 : ℝ) • V),
    Lp.coeFn_smul a (originClass n), Lp.coeFn_smul (1/2 : ℝ) V, ho, hv]
      with ωX hadd hmul hhalf ho hv
  change (a • originClass n + (1/2 : ℝ) • V) ωX = _
  rw [hadd, Pi.add_apply, hmul, hhalf, Pi.smul_apply, Pi.smul_apply, ho, hv]
  change a*originValue n ωX + (1/2 : ℝ)*scalarTimeIntegral n T (ωY,ωX) = _
  dsimp only [a]
  rw [hm]
  rfl

/-- Product almost-everywhere equality, not just separate fixed-time
versions, identifies the literal correction with its native joint class. -/
theorem jointClass_coeFn (n : ℕ) (T : ℝ≥0) :
    jointClass n T =ᵐ[jointMeasure] scalarWhole n T := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable (jointClass n T)).measurable
      (scalarWhole_measurable n T))).mpr
  filter_upwards [joint_sections n T, whole_scalar_sections n T] with ωY hj hw
  exact hj.symm.trans hw

theorem scalarWhole_memLp (n : ℕ) (T : ℝ≥0) : MemLp (scalarWhole n T) 2 jointMeasure :=
  (Lp.memLp (jointClass n T)).ae_eq (jointClass_coeFn n T)

def literalClass (n : ℕ) (T : ℝ≥0) : Lp ℝ 2 jointMeasure := (scalarWhole_memLp n T).toLp _

theorem literalClass_eq_joint (n : ℕ) (T : ℝ≥0) : literalClass n T = jointClass n T := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (scalarWhole_memLp n T)).trans (jointClass_coeFn n T).symm

/-- The native source-two/clock-zero limit now applies to the literal
scalar correction, with both stochastic terms and their actual domains. -/
theorem literal_native_block_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => (condExpL2 ℝ ℝ sourceSigma_le
      (jointSourceSector 2 (literalClass n T)) : Lp ℝ 2 jointMeasure)) atTop
      (𝓝 (sourceLift (IBMQuarticClockTerminal.terminalLimit T))) := by
  simp_rw [literalClass_eq_joint, sourceSector_jointClass]
  exact native_block_tendsto T hT

end OperatorDerivativeRewrite.Foundation.IBMQuarticLiteralJoint
