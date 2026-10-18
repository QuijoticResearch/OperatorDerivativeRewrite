import Foundation.IBMSchwartzJointRealization

/-! The native joint class is the literal nonlinear Schwartz correction.
Product coordinates are (clock, source), as in the reused source operators. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzLiteralJoint
open InfiniteGaussian IBMCorrectionStein IBMSchwartzScalarRecovery IBMSchwartzTimeProjection
open IBMSchwartzJointRealization
open IBMQuarticJointRealization (jointMeasure jointSourceSector sourceLift sourceSigma_le)

variable (g : SchwartzMap ℝ ℝ) (a : ℝ)

def originValue (n : ℕ) (ω : SampleSpace) : ℝ :=
  shiftedJet g a 1 (IBMDyadicExtension.field n 0 ω 0)*IBMDyadicExtension.field n 1 ω 0

theorem originValue_measurable (n : ℕ) : Measurable (originValue g a n) :=
  ((shiftedJet_smooth g a 1).continuous.measurable.comp
    (IBMDyadicExtension.field_coordinate_measurable n 0 0)).mul
    (IBMDyadicExtension.field_coordinate_measurable n 1 0)

def scalarWhole (n : ℕ) (T : ℝ≥0) (p : SampleSpace × SampleSpace) : ℝ :=
  BrownianMassContinuousLimit.limitPath p.1 T*originValue g a n p.2 +
    (1/2 : ℝ)*scalarTimeIntegral g a n T p

theorem scalarWhole_measurable (n : ℕ) (T : ℝ≥0) : Measurable (scalarWhole g a n T) := by
  have hm : Measurable (fun p : SampleSpace × SampleSpace => BrownianMassContinuousLimit.limitPath p.1 T) :=
    BrownianMassLimitIdentification.jointly_measurable.comp (measurable_const.prodMk measurable_fst)
  exact (hm.mul ((originValue_measurable g a n).comp measurable_snd)).add
    ((scalarTimeIntegral_measurable g a n T).const_mul (1/2 : ℝ))

theorem whole_scalar_sections (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ ωY ∂gaussianProduct, wholeCorrection g a n T ωY =ᵐ[gaussianProduct]
      fun ωX => scalarWhole g a n T (ωY,ωX) := by
  have hm : BrownianMassLimitIdentification.coordinateClass T =ᵐ[gaussianProduct]
      fun ω => BrownianMassContinuousLimit.limitPath ω T :=
    MemLp.coeFn_toLp (BrownianMassLimitIdentification.coordinate_memLp T)
  filter_upwards [hm] with ωY hy
  filter_upwards [wholeCorrection_coeFn g a n ωY T] with ωX hx
  rw [hx, hy]
  rfl

/-- A single product-a.e. equality identifies the actual scalar correction
with the independently constructed native joint L2 class. -/
theorem jointClass_coeFn (n : ℕ) (T : ℝ≥0) :
    jointClass g a n T =ᵐ[jointMeasure] scalarWhole g a n T := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable (jointClass g a n T)).measurable
      (scalarWhole_measurable g a n T))).mpr
  filter_upwards [joint_sections g a n T, whole_scalar_sections g a n T] with ωY hj hw
  exact hj.symm.trans hw

theorem scalarWhole_memLp (n : ℕ) (T : ℝ≥0) : MemLp (scalarWhole g a n T) 2 jointMeasure :=
  (Lp.memLp (jointClass g a n T)).ae_eq (jointClass_coeFn g a n T)

def literalClass (n : ℕ) (T : ℝ≥0) : Lp ℝ 2 jointMeasure :=
  (scalarWhole_memLp g a n T).toLp _

theorem literalClass_eq_joint (n : ℕ) (T : ℝ≥0) : literalClass g a n T = jointClass g a n T := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (scalarWhole_memLp g a n T)).trans (jointClass_coeFn g a n T).symm

/-- Strong native product-L2 convergence of the source-two/clock-zero
block of the literal correction, including its actual origin term. -/
theorem literal_native_block_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => (condExpL2 ℝ ℝ sourceSigma_le
      (jointSourceSector 2 (literalClass g a n T)) : Lp ℝ 2 jointMeasure)) atTop
      (𝓝 (sourceLift (IBMSchwartzPrimitiveLimit.terminalLimit g a T))) := by
  simp_rw [literalClass_eq_joint, sourceSector_jointClass]
  exact native_block_tendsto g a T hT

theorem scalarWhole_zero (n : ℕ) :
    scalarWhole g a n 0 =ᵐ[jointMeasure] fun _ => (0 : ℝ) := by
  have hm := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
    (BrownianMassContinuousLimit.limitPath_properties.mono fun ω h => h.1)
  filter_upwards [hm] with p hp
  simp only [scalarWhole, scalarTimeIntegral, NNReal.coe_zero, intervalIntegral.integral_same,
    hp, zero_mul, mul_zero, add_zero]

theorem literalClass_zero (n : ℕ) : literalClass g a n 0 = 0 := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (scalarWhole_memLp g a n 0), scalarWhole_zero g a n,
    Lp.coeFn_zero ℝ 2 jointMeasure] with p hc hs hz
  change literalClass g a n 0 p = scalarWhole g a n 0 p at hc
  rw [hc, hs, hz]
  rfl

theorem terminalLimit_zero : IBMSchwartzPrimitiveLimit.terminalLimit g a 0 = 0 := by
  have hc := (IBMConstructedSources.clockPath_coordinate_ae 0).trans GaussianTimeProcess.process_zero_ae
  unfold IBMSchwartzPrimitiveLimit.terminalLimit
  have he : (fun ω => IBMSchwartzPrimitiveLimit.limitPrimitive g a
      |IBMConstructedSources.clockPath ω 0|) =ᵐ[gaussianProduct] fun _ => (0 : GaussianL2) := by
    filter_upwards [hc] with ω hω
    simp only [hω, abs_zero, IBMSchwartzPrimitiveLimit.limitPrimitive_zero]
  rw [integral_congr_ae he, integral_zero]

/-- Includes zero horizon via the actual zero time integral and actual
zero-initialized mass/clock classes, without a heat formula at T=0. -/
theorem literal_native_block_tendsto_all (T : ℝ≥0) :
    Tendsto (fun n => (condExpL2 ℝ ℝ sourceSigma_le
      (jointSourceSector 2 (literalClass g a n T)) : Lp ℝ 2 jointMeasure)) atTop
      (𝓝 (sourceLift (IBMSchwartzPrimitiveLimit.terminalLimit g a T))) := by
  by_cases hT : T = 0
  · subst T
    simpa [literalClass_zero, terminalLimit_zero, jointSourceSector] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Lp ℝ 2 jointMeasure)) atTop (𝓝 0))
  · exact literal_native_block_tendsto g a T (pos_iff_ne_zero.mpr hT)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzLiteralJoint
