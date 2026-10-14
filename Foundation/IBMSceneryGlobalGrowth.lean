import Foundation.IBMWholeLineSmoothing
import Foundation.IBMClockCubicRepresentative

/-! Global polynomial growth of actual compact-kernel Gaussian scenery classes. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMSceneryGlobalGrowth
open InfiniteGaussian IBMContinuousScenery IBMFiniteScenerySmoothing
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

theorem sourceScenery_norm_sq (r : ℝ) : ‖sourceScenery r‖^2=|r| := by
  rw [sourceScenery,LinearIsometry.norm_map]
  simpa only [direction,show (2 : ℝ)*(1/2)=1 by norm_num,Real.rpow_one] using
    FractionalSpectralGeometry.normalized_norm_sq (1/2) (by norm_num) (by norm_num) r

theorem sourceScenery_norm_le (r : ℝ) : ‖sourceScenery r‖ ≤ 1+|r| := by
  have hs := sourceScenery_norm_sq r
  nlinarith [norm_nonneg (sourceScenery r),abs_nonneg r,sq_nonneg |r|]

theorem compact_kernel_global_growth (ρ : ℝ → ℝ) (hc : HasCompactSupport ρ) (hρ : Continuous ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖wholeLineScenery ρ x‖ ≤ C*(1+|x|) := by
  obtain ⟨R0,hR0⟩ := hc.isBounded.exists_norm_le
  let R := max R0 1
  have hR : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  have hsupport (z : ℝ) (hz : ρ z≠0) : |z| ≤ R := by
    have hb : |z| ≤ R0 := by
      simpa only [Real.norm_eq_abs] using hR0 z (subset_tsupport ρ hz)
    exact hb.trans (le_max_left _ _)
  obtain ⟨M0,hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hρ.continuousOn
    (s := Set.Icc (-R) R)
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hkernel (z : ℝ) : |ρ z| ≤ M := by
    by_cases hz : ρ z=0
    · simp only [hz,abs_zero]; exact hM
    · have hzs := abs_le.mp (hsupport z hz)
      have hb : |ρ z| ≤ M0 := by simpa only [Real.norm_eq_abs] using hM0 z hzs
      exact hb.trans (le_max_left _ _)
  refine ⟨2*R*M*(1+R),by positivity, ?_⟩
  intro x
  have he : wholeLineScenery ρ x=kernelScenery (x-R) (x+R) x ρ := by
    apply wholeLineScenery_eq_kernelScenery
    intro r hr
    by_contra hz
    have hb := abs_le.mp (hsupport (x-r) hz)
    exact hr ⟨by linarith,by linarith⟩
  have hb (r : ℝ) (hr : r∈Set.Icc (x-R) (x+R)) :
      ‖ρ (x-r) • sourceScenery r‖ ≤ M*(1+R)*(1+|x|) := by
    have hdist : |r-x| ≤ R := abs_le.mpr ⟨by linarith [hr.1],by linarith [hr.2]⟩
    have habs : |r| ≤ |x|+R := by
      have hi := abs_add_le x (r-x)
      rw [show x+(r-x)=r by ring] at hi
      linarith
    have hs : ‖sourceScenery r‖ ≤ (1+R)*(1+|x|) := by
      have hn := sourceScenery_norm_le r
      nlinarith [mul_nonneg hR (abs_nonneg x)]
    rw [norm_smul,Real.norm_eq_abs]
    have hm := mul_le_mul (hkernel (x-r)) hs (norm_nonneg (sourceScenery r)) hM
    nlinarith [hm]
  have hi := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure ℝ)) (s := Set.Icc (x-R) (x+R))
    isCompact_Icc.measure_lt_top hb
  have hvol : volume.real (Set.Icc (x-R) (x+R))=2*R := by
    rw [measureReal_def,Real.volume_Icc,show x+R-(x-R)=2*R by ring,
      ENNReal.toReal_ofReal (by positivity)]
  rw [he,kernelScenery]
  rw [hvol] at hi
  nlinarith [hi]

theorem tripleCoefficient_global_growth (n : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖IBMGaussianSteinMoments.tripleCoefficient n x i‖ ≤ C*(1+|x|) := by
  obtain ⟨C,hC,hbound⟩ := compact_kernel_global_growth (IBMJointMollifierGaussian.derivativeKernel n i)
    (IBMDyadicExtension.derivativeKernel_regular n i).1
    (IBMDyadicExtension.derivativeKernel_regular n i).2.continuous
  refine ⟨C,hC, ?_⟩
  intro x
  have hb := hbound x
  rw [IBMJointMollifierGaussian.wholeLineScenery_eq_sourceEmbedding,
    LinearIsometry.norm_map] at hb
  simpa only [IBMGaussianSteinMoments.tripleCoefficient,LinearIsometry.norm_map] using hb

end OperatorDerivativeRewrite.Foundation.IBMSceneryGlobalGrowth
