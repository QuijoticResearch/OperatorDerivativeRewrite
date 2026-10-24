import Foundation.IBMPhysicalRunningIntegrand

/-! A running clock Ito identity for actual scenery-tested IBM. The correction
is the strong limit of the explicit native local-time and curvature terms.
No bounded-variation assertion or unprojected intrinsic formula is inferred. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalRunningIto
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalRunningPrimitive
open GaussianPredictableFull GaussianTimeProductL2 GaussianClockBochnerContraction
open IBMPhysicalSceneryTestClockGraph

def nativeValue (n : ℕ) (T : ℝ≥0) (L : Tests) : GaussianL2 :=
  projection L (IBMFirstSourceClockGraph.flip (IBMRandomTimeHilbert.randomMollifiedL2 n T))

theorem nativeValue_coeFn (n : ℕ) (T : ℝ≥0) (L : Tests) :
    nativeValue n T L =ᵐ[gaussianProduct] fun Y =>
      value n L |IBMConstructedSources.clockPath Y T| := by
  rw [nativeValue, projection_flip]
  filter_upwards [(innerSL ℝ (testNoise L)).coeFn_compLpL
      (IBMRandomTimeHilbert.randomMollifiedL2 n T),
    (IBMRandomTimeHilbert.randomMollifiedClass_memLp n T).coeFn_toLp,
    IBMConstructedSources.clockPath_coordinate_ae T] with Y hp hu hc
  change IBMRandomTimeHilbert.randomMollifiedL2 n T Y = _ at hu
  rw [hp, hu]
  simp only [innerSL_apply_apply, IBMRandomTimeHilbert.randomMollifiedClass, ← hc]
  rfl

def endpoint (n : ℕ) (T : ℝ≥0) (L : Tests) : GaussianL2 :=
  nativeValue n T L - Lp.const 2 gaussianProduct (value n L 0)

theorem endpoint_coeFn (n : ℕ) (T : ℝ≥0) (L : Tests) :
    endpoint n T L =ᵐ[gaussianProduct] fun Y =>
      value n L |IBMConstructedSources.clockPath Y T| - value n L 0 := by
  filter_upwards [Lp.coeFn_sub (nativeValue n T L)
      (Lp.const 2 gaussianProduct (value n L 0)), nativeValue_coeFn n T L,
    Lp.coeFn_const 2 gaussianProduct (value n L 0)] with Y hs hv hc
  rw [endpoint, hs, Pi.sub_apply, hv, hc]
  rfl

def correction (n : ℕ) (T : ℝ≥0) (L : Tests) : GaussianL2 :=
  first n L 0 • BrownianMassLimitIdentification.coordinateClass T +
    (1/2 : ℝ) • GaussianReflectedC2Ito.drift
      (value n L) (value_C2 n L) (bound1 n L) (second_bound n L) T

theorem correction_coeFn (n : ℕ) (T : ℝ≥0) (L : Tests) :
    correction n T L =ᵐ[gaussianProduct] fun Y =>
      L (IBMPhysicalDirac.translated n 0) * BrownianMassContinuousLimit.limitPath Y T +
        (1/2 : ℝ) * ∫ s in 0..(T : ℝ), second n L |IBMConstructedSources.clockPath Y s.toNNReal| := by
  filter_upwards [Lp.coeFn_add
      (first n L 0 • BrownianMassLimitIdentification.coordinateClass T)
      ((1/2 : ℝ) • GaussianReflectedC2Ito.drift
        (value n L) (value_C2 n L) (bound1 n L) (second_bound n L) T),
    Lp.coeFn_smul (first n L 0) (BrownianMassLimitIdentification.coordinateClass T),
    Lp.coeFn_smul (1/2 : ℝ) (GaussianReflectedC2Ito.drift
      (value n L) (value_C2 n L) (bound1 n L) (second_bound n L) T),
    (BrownianMassLimitIdentification.coordinate_memLp T).coeFn_toLp,
    GaussianReflectedC2Ito.drift_coeFn (value n L) (value_C2 n L)
      (bound1 n L) (second_bound n L) T] with Y ha hs hd hc hf
  change correction n T L Y = _ at ha
  change BrownianMassLimitIdentification.coordinateClass T Y = _ at hc
  rw [ha, Pi.add_apply, hs, hd]
  simp only [Pi.smul_apply, smul_eq_mul, hc, hf, value_second_deriv, first_physical]

theorem native_identity (n : ℕ) (T : ℝ≥0) (L : Tests) :
    endpoint n T L = itoIntegral (IBMPhysicalRunningIntegrand.native n T L) +
      correction n T L := by
  apply Lp.ext
  filter_upwards [endpoint_coeFn n T L,
    GaussianReflectedC2Ito.reflected_ito_ae (value n L) (value_C2 n L)
      (bound0 n L) (bound1 n L) (first_bound n L) (second_bound n L) T,
    Lp.coeFn_add (itoIntegral (IBMPhysicalRunningIntegrand.native n T L))
      (correction n T L),
    Lp.coeFn_add (first n L 0 • BrownianMassLimitIdentification.coordinateClass T)
      ((1/2 : ℝ) • GaussianReflectedC2Ito.drift
        (value n L) (value_C2 n L) (bound1 n L) (second_bound n L) T),
    Lp.coeFn_smul (first n L 0) (BrownianMassLimitIdentification.coordinateClass T),
    Lp.coeFn_smul (1/2 : ℝ) (GaussianReflectedC2Ito.drift
      (value n L) (value_C2 n L) (bound1 n L) (second_bound n L) T),
    (BrownianMassLimitIdentification.coordinate_memLp T).coeFn_toLp] with Y he hi ha hb hs hd hc
  rw [he, ha, Pi.add_apply]
  change correction n T L Y = _ at hb
  rw [hb, Pi.add_apply, hs, hd]
  change BrownianMassLimitIdentification.coordinateClass T Y = _ at hc
  simp only [Pi.smul_apply, smul_eq_mul, hc]
  simpa only [value_deriv, Pi.smul_apply, smul_eq_mul, add_assoc,
    IBMPhysicalRunningIntegrand.native] using hi

theorem endpoint_tendsto (T : ℝ≥0) (L : Tests) :
    Tendsto (fun n => endpoint n T L) atTop (nhds (point T L)) := by
  have hc := (Lp.constL 2 gaussianProduct ℝ).continuous.tendsto 0 |>.comp (value_zero_tendsto L)
  have h := (native_value_tendsto T L).sub hc
  simpa only [endpoint, nativeValue, Function.comp_def, map_zero, sub_zero,
    Lp.constL_apply] using h

def correctionLimit (T : ℝ≥0) (L : Tests) : GaussianL2 :=
  point T L - itoIntegral (IBMPhysicalRunningIntegrand.limitIntegrand T L)

theorem correction_tendsto (T : ℝ≥0) (L : Tests) :
    Tendsto (fun n => correction n T L) atTop (nhds (correctionLimit T L)) := by
  have he (n : ℕ) : correction n T L = endpoint n T L -
      itoIntegral (IBMPhysicalRunningIntegrand.native n T L) := by
    rw [native_identity]
    abel
  simp only [he, correctionLimit]
  exact (endpoint_tendsto T L).sub (IBMPhysicalRunningIntegrand.stochastic_tendsto T L)

theorem running_identity (T : ℝ≥0) (L : Tests) :
    point T L = itoIntegral (IBMPhysicalRunningIntegrand.limitIntegrand T L) +
      correctionLimit T L := by
  unfold correctionLimit
  abel

theorem actual_running_identity (T : ℝ≥0) (L : Tests) :
    (fun Y => ∫ X, IBMConstructedSources.ibmValue T (X,Y) * testNoise L X ∂gaussianProduct)
      =ᵐ[gaussianProduct] fun Y =>
        itoIntegral (IBMPhysicalRunningIntegrand.limitIntegrand T L) Y + correctionLimit T L Y := by
  filter_upwards [point_actual_ae T L,
    Lp.coeFn_add (itoIntegral (IBMPhysicalRunningIntegrand.limitIntegrand T L))
      (correctionLimit T L)] with Y hp ha
  rw [← hp, ← Pi.add_apply, ← ha, ← running_identity]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalRunningIto
