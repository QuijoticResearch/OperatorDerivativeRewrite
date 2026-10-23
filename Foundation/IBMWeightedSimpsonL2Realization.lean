import Foundation.IBMWeightedSimpsonL2Error
import Foundation.BochnerL2Approximation

/-! Genuine unclipped time-weighted IBM Simpson integration in L2.
Bounded C5 primitives give a deterministic majorant for the exact path sums;
the stochastic quadrature error uses the proved actual tenth moments. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMWeightedSimpsonL2Realization
open IBMSourceLaws IBMConstructedSources IBMTimeWeightedSimpson IBMActualSimpson
open IBMUniformClockGridEnergy IBMContinuousQuadrature IBMUniformSimpsonProcess
attribute [local irreducible] ibmValue clockPath sceneryPath

theorem pathSum_target_bound (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F : ℝ) (hF : ∀ z, |f z| ≤ F) (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ n ω, |pathSum h (deriv f) T n ω| ≤ C) ∧
      (∀ ω, |target h (deriv f) T ω| ≤ C) := by
  obtain ⟨B,K,hB0,hK,hB,hd,hLip⟩ :=
    IBMTimeWeightQuadrature.compact_weight_bounds h hh T.coe_nonneg
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  let C : ℝ := 2*F*(B+K*T)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (n : ℕ) (ω : JointSample) : |pathSum h (deriv f) T n ω| ≤ C := by
    apply weighted_prefix_bound (fun i => h (time T (n+1) i))
      (fun i => lineIntegral (deriv f) (grid (T/(n+1)) (i+1)) ω -
        lineIntegral (deriv f) (grid (T/(n+1)) i) ω)
      (n+1) (by omega) (2*F) B (K*T) (by positivity)
      (fun i hi => hB _ (time_mem T.coe_nonneg (by omega) (by omega)))
      ?_ (variation_bound T.coe_nonneg hK h (n+1) (by omega) hLip)
    intro m hm
    rw [Finset.sum_range_sub (fun i => lineIntegral (deriv f) (grid (T/(n+1)) i) ω) m]
    have hz : lineIntegral (deriv f) (grid (T/(n+1)) 0) ω = 0 := by
      simp [grid, lineIntegral]
    rw [hz, sub_zero, derivative_lineIntegral f (hf.of_le (by norm_num))]
    have ha := hF (ibmValue (grid (T/(n+1)) m) ω)
    have hb := hF (ibmValue 0 ω)
    exact (abs_sub _ _).trans (by linarith)
  refine ⟨C,hC,hp,fun ω => ?_⟩
  exact le_of_tendsto ((pathSum_tendsto h (deriv f) hh
    (hf.continuous_deriv (by norm_num)) T ω).abs) (Eventually.of_forall fun n => hp n ω)

theorem pathSum_memLp (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F : ℝ) (hF : ∀ z, |f z| ≤ F) (T : ℝ≥0) (n : ℕ) :
    MemLp (pathSum h (deriv f) T n) 2 jointMeasure := by
  obtain ⟨C,hC,hp,ht⟩ := pathSum_target_bound h f hh hf F hF T
  exact MemLp.of_bound
    (pathSum_measurable h (deriv f) (hf.continuous_deriv (by norm_num)) T n).aestronglyMeasurable
    C (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hp n ω)

theorem target_memLp (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F : ℝ) (hF : ∀ z, |f z| ≤ F) (T : ℝ≥0) :
    MemLp (target h (deriv f) T) 2 jointMeasure := by
  obtain ⟨C,hC,hp,ht⟩ := pathSum_target_bound h f hh hf F hF T
  exact MemLp.of_bound
    (target_measurable h (deriv f) hh (hf.continuous_deriv (by norm_num)) T).aestronglyMeasurable
    C (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using ht ω)

def exactClass (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F : ℝ) (hF : ∀ z, |f z| ≤ F) (T : ℝ≥0) (n : ℕ) :
    Lp ℝ 2 jointMeasure := (pathSum_memLp h f hh hf F hF T n).toLp _

def targetClass (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F : ℝ) (hF : ∀ z, |f z| ≤ F) (T : ℝ≥0) :
    Lp ℝ 2 jointMeasure := (target_memLp h f hh hf F hF T).toLp _

theorem exactClass_actual_ae (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F : ℝ) (hF : ∀ z, |f z| ≤ F) (T : ℝ≥0) (n : ℕ) :
    exactClass h f hh hf F hF T n =ᵐ[jointMeasure] pathSum h (deriv f) T n :=
  (pathSum_memLp h f hh hf F hF T n).coeFn_toLp

theorem targetClass_actual_ae (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F : ℝ) (hF : ∀ z, |f z| ≤ F) (T : ℝ≥0) :
    targetClass h f hh hf F hF T =ᵐ[jointMeasure] target h (deriv f) T :=
  (target_memLp h f hh hf F hF T).coeFn_toLp

theorem exactClass_tendsto (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F : ℝ) (hF : ∀ z, |f z| ≤ F) (T : ℝ≥0) :
    Tendsto (exactClass h f hh hf F hF T) atTop (𝓝 (targetClass h f hh hf F hF T)) := by
  obtain ⟨C,hC,hp,ht⟩ := pathSum_target_bound h f hh hf F hF T
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (Lp.const 2 jointMeasure C)
  · intro n
    filter_upwards [exactClass_actual_ae h f hh hf F hF T n,
      Lp.coeFn_const (p := 2) (μ := jointMeasure) (c := C)] with ω he hc
    rw [he,hc]
    simpa only [Real.norm_eq_abs, Function.const_apply, abs_of_nonneg hC] using hp n ω
  · filter_upwards [targetClass_actual_ae h f hh hf F hF T,
      Lp.coeFn_const (p := 2) (μ := jointMeasure) (c := C)] with ω he hc
    rw [he,hc]
    simpa only [Real.norm_eq_abs, Function.const_apply, abs_of_nonneg hC] using ht ω
  · filter_upwards [ae_all_iff.mpr (fun n => exactClass_actual_ae h f hh hf F hF T n),
      targetClass_actual_ae h f hh hf F hF T] with ω he ht
    simpa only [he,ht] using pathSum_tendsto h (deriv f) hh
      (hf.continuous_deriv (by norm_num)) T ω

theorem weighted_memLp (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F M : ℝ) (hF : ∀ z, |f z| ≤ F)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) :
    MemLp (weighted h (deriv f) T n) 2 jointMeasure := by
  obtain ⟨B,K,hB0,hK,hB,hd,hLip⟩ :=
    IBMTimeWeightQuadrature.compact_weight_bounds h hh T.coe_nonneg
  have hm := (IBMWeightedSimpsonL2Error.weighted_error_memLp h f hf M B hM T hB n).add
    (pathSum_memLp h f hh hf F hF T n)
  change MemLp ((weighted h (deriv f) T n-pathSum h (deriv f) T n)+
    pathSum h (deriv f) T n) 2 jointMeasure at hm
  simpa only [sub_add_cancel] using hm

def valueClass (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F M : ℝ) (hF : ∀ z, |f z| ≤ F)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) :
    Lp ℝ 2 jointMeasure := (weighted_memLp h f hh hf F M hF hM T n).toLp _

theorem valueClass_actual_ae (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F M : ℝ) (hF : ∀ z, |f z| ≤ F)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) :
    valueClass h f hh hf F M hF hM T n =ᵐ[jointMeasure] weighted h (deriv f) T n :=
  (weighted_memLp h f hh hf F M hF hM T n).coeFn_toLp

/-- Actual time-dependent spatial stochastic integration, in original-law L2. -/
theorem valueClass_tendsto (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 5 f) (F M : ℝ) (hF : ∀ z, |f z| ≤ F)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) :
    Tendsto (valueClass h f hh hf F M hF hM T) atTop
      (𝓝 (targetClass h f hh hf F hF T)) := by
  obtain ⟨B,K,hB0,hK,hB,hd,hLip⟩ :=
    IBMTimeWeightQuadrature.compact_weight_bounds h hh T.coe_nonneg
  have he (n : ℕ) : IBMWeightedSimpsonL2Error.errorClass h f hf M B hM T hB n +
      exactClass h f hh hf F hF T n = valueClass h f hh hf F M hF hM T n := by
    apply Lp.ext
    filter_upwards [IBMWeightedSimpsonL2Error.errorClass_actual_ae h f hf M B hM T hB n,
      exactClass_actual_ae h f hh hf F hF T n,
      valueClass_actual_ae h f hh hf F M hF hM T n,
      Lp.coeFn_add (IBMWeightedSimpsonL2Error.errorClass h f hf M B hM T hB n)
        (exactClass h f hh hf F hF T n)] with ω he hp hv ha
    rw [ha]
    simp only [Pi.add_apply, he,hp,hv,weightedError,sub_add_cancel]
  have ht := (IBMWeightedSimpsonL2Error.errorClass_tendsto h f hf M B hM T hB).add
    (exactClass_tendsto h f hh hf F hF T)
  rw [zero_add] at ht
  exact ht.congr' (Eventually.of_forall he)

end OperatorDerivativeRewrite.Foundation.IBMWeightedSimpsonL2Realization
