import Foundation.IBMActualQuadraticRandomReconstruction
import Foundation.IBMMixedClockStrongL2

/-! Genuine L2 versions of actual quadratic IBM source contractions, and
L1 convergence after arbitrary square-integrable clock weighting. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMActualQuadraticL2Reconstruction
open InfiniteGaussian GaussianTimeProcess IBMClippedClockCrossing
open IBMRawGridMixedObservable IBMMixedClockLimit

theorem endpoint_memLp (H R S : ℝ≥0) : MemLp
    (fun Y => cap (process R Y) (process H Y)*cap (process S Y) (process H Y))
      2 gaussianProduct := by
  apply ((process_memLp H 4 (by norm_num)).fun_mul
    (process_memLp H 4 (by norm_num))).norm.mono'
    (mixed_endpoint_integrable H R S).aestronglyMeasurable
  exact Eventually.of_forall fun Y => by
    have hn (r : ℝ) : 0 ≤ cap r (process H Y) := le_min (abs_nonneg _) (abs_nonneg _)
    rw [norm_mul,Real.norm_of_nonneg (hn _),Real.norm_of_nonneg (hn _),norm_mul]
    simpa only [Real.norm_eq_abs,cap] using mul_le_mul
      (min_le_left |process H Y| |process R Y|)
      (min_le_left |process H Y| |process S Y|) (hn _) (abs_nonneg _)

def endpoint (H R S : ℝ≥0) : GaussianL2 := (endpoint_memLp H R S).toLp _

theorem endpoint_actual (H R S : ℝ≥0) :
    endpoint H R S =ᵐ[gaussianProduct] fun Y =>
      cap (process R Y) (process H Y)*cap (process S Y) (process H Y) :=
  (endpoint_memLp H R S).coeFn_toLp

def native (H R S : ℝ≥0) (N : ℕ) : GaussianL2 :=
  endpoint H R S-IBMMixedClockStrongL2.mixedL2 H R S N

def reconstruction (H R S : ℝ≥0) : GaussianL2 :=
  endpoint H R S-IBMMixedClockStrongL2.occupationL2 H R S

theorem native_actual (H R S : ℝ≥0) (N : ℕ) :
    native H R S N =ᵐ[gaussianProduct] fun Y => mixedEnergy (H/(N+1)) (N+1) R S Y := by
  filter_upwards [Lp.coeFn_sub (endpoint H R S) (IBMMixedClockStrongL2.mixedL2 H R S N),
    endpoint_actual H R S,IBMMixedClockStrongL2.mixedL2_actual H R S N] with Y ha he hm
  change native H R S N Y = _ at ha
  rw [ha,Pi.sub_apply,he,hm,mixedEnergy_identity]

theorem reconstruction_actual (H R S : ℝ≥0) :
    reconstruction H R S =ᵐ[gaussianProduct] fun Y =>
      cap (process R Y) (process H Y)*cap (process S Y) (process H Y)-
        mixedOccupation H R S Y := by
  filter_upwards [Lp.coeFn_sub (endpoint H R S) (IBMMixedClockStrongL2.occupationL2 H R S),
    endpoint_actual H R S,IBMMixedClockStrongL2.occupationL2_actual H R S] with Y ha he ho
  change reconstruction H R S Y = _ at ha
  rw [ha,Pi.sub_apply,he,ho]

theorem native_lower (H R S : ℝ≥0) (N : ℕ) :
    IBMClippedClockStrongLimit.clockL1 (native H R S N) =
      IBMActualQuadraticRandomReconstruction.native H R S N := by
  apply Lp.ext
  exact (IBMClippedClockStrongLimit.clockL1_actual _).trans
    ((native_actual H R S N).trans
      (IBMActualQuadraticRandomReconstruction.native_actual H R S N).symm)

theorem reconstruction_lower (H R S : ℝ≥0) :
    IBMClippedClockStrongLimit.clockL1 (reconstruction H R S) =
      IBMActualQuadraticRandomReconstruction.reconstruction H R S := by
  apply Lp.ext
  exact (IBMClippedClockStrongLimit.clockL1_actual _).trans
    ((reconstruction_actual H R S).trans
      (IBMActualQuadraticRandomReconstruction.reconstruction_actual H R S).symm)

theorem native_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (native H R S) atTop (𝓝 (reconstruction H R S)) :=
  tendsto_const_nhds.sub (IBMMixedClockStrongL2.mixedL2_tendsto H R S hH)

theorem weighted_absolute_tendsto (H R S : ℝ≥0) (hH : 0 < H) (a : GaussianL2) :
    Tendsto (fun N : ℕ => ∫ Y, |a Y*(mixedEnergy (H/(N+1)) (N+1) R S Y-
      (cap (process R Y) (process H Y)*cap (process S Y) (process H Y)-
        mixedOccupation H R S Y))| ∂gaussianProduct) atTop (𝓝 0) := by
  have ht := (tendsto_iff_norm_sub_tendsto_zero.mp (native_tendsto H R S hH)).const_mul ‖a‖
  simp only [mul_zero] at ht
  apply squeeze_zero (fun N => integral_nonneg fun _ => abs_nonneg _) (fun N => ?_) ht
  have hb := BochnerL2RepresentativeFubini.pairing_norm_integral_le a
    (native H R S N-reconstruction H R S)
  have he : (∫ Y, |a Y*(mixedEnergy (H/(N+1)) (N+1) R S Y-
      (cap (process R Y) (process H Y)*cap (process S Y) (process H Y)-
        mixedOccupation H R S Y))| ∂gaussianProduct) =
      ∫ Y, ‖inner ℝ (a Y) ((native H R S N-reconstruction H R S) Y)‖ ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (native H R S N) (reconstruction H R S),
      native_actual H R S N,reconstruction_actual H R S] with Y hs hn hr
    rw [hs,Pi.sub_apply,hn,hr,Real.inner_apply,Real.norm_eq_abs]
  rw [he]
  exact hb

end OperatorDerivativeRewrite.Foundation.IBMActualQuadraticL2Reconstruction
