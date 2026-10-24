import Foundation.IBMPhysicalSceneryTestClarkOcone
import Foundation.IBMSchwartzPhysicalGlobalBounds

/-! Actual smooth scenery-tested primitives and a spatially UNIFORM physical
Dirac approximation. These are inputs to a running Ito limit, not its conclusion. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalRunningPrimitive
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalNoiseCalculus IBMPhysicalNoiseClock
open IBMPhysicalDerivativeKernel IBMPhysicalDirac IBMPhysicalNegativeEmbedding
open IBMPhysicalNoiseRealization IBMPhysicalNoiseVectors IBMContinuousScenery
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _

theorem translated_error (n : ℕ) (r : ℝ) :
    ‖translated n r-dirac r‖ ≤ ‖physicalDerivative‖*Real.sqrt (IBMMollifier.bump n).rOut := by
  have he : translated n r-dirac r =
      -physicalDerivative (convolutionKernel (IBMMollifier.kernel n) r-vector r) := by
    rw [translated_eq, dirac, map_sub]
    abel
  rw [he, norm_neg]
  exact (physicalDerivative.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (IBMSchwartzPhysicalSlope.convolution_error n r) (norm_nonneg _))

def value (n : ℕ) (L : Tests) (r : ℝ) : ℝ :=
  inner ℝ (testNoise L) (wholeLineScenery (IBMMollifier.kernel n) r)

def first (n : ℕ) (L : Tests) (r : ℝ) : ℝ :=
  inner ℝ (testNoise L) (wholeLineScenery (deriv (IBMMollifier.kernel n)) r)

def second (n : ℕ) (L : Tests) (r : ℝ) : ℝ :=
  inner ℝ (testNoise L) (wholeLineScenery (deriv (deriv (IBMMollifier.kernel n))) r)

theorem value_hasDerivAt (n : ℕ) (L : Tests) (r : ℝ) :
    HasDerivAt (value n L) (first n L r) r :=
  (innerSL ℝ (testNoise L)).hasFDerivAt.comp_hasDerivAt r
    (wholeLineScenery_hasDerivAt (IBMMollifier.kernel_compactSupport n)
      ((IBMMollifier.kernel_smooth n).of_le (by norm_num)) r)

theorem first_hasDerivAt (n : ℕ) (L : Tests) (r : ℝ) :
    HasDerivAt (first n L) (second n L r) r :=
  (innerSL ℝ (testNoise L)).hasFDerivAt.comp_hasDerivAt r
    (wholeLineScenery_hasDerivAt (IBMMollifier.kernel_compactSupport n).deriv
      (((IBMMollifier.kernel_smooth n).of_le (by norm_num) :
        ContDiff ℝ 2 (IBMMollifier.kernel n)).deriv') r)

theorem second_continuous (n : ℕ) (L : Tests) : Continuous (second n L) := by
  have h3 : ContDiff ℝ 3 (IBMMollifier.kernel n) :=
    (IBMMollifier.kernel_smooth n).of_le (by norm_num)
  have h1 : ContDiff ℝ 1 (deriv (deriv (IBMMollifier.kernel n))) :=
    (h3.deriv' (n := 2)).deriv'
  exact continuous_iff_continuousAt.mpr fun r =>
    ((innerSL ℝ (testNoise L)).hasFDerivAt.comp_hasDerivAt r
      (wholeLineScenery_hasDerivAt (IBMMollifier.kernel_compactSupport n).deriv.deriv h1 r)).continuousAt

theorem value_C2 (n : ℕ) (L : Tests) : ContDiff ℝ 2 (value n L) := by
  have he : deriv (value n L) = first n L := funext fun r => (value_hasDerivAt n L r).deriv
  have hd : deriv (first n L) = second n L := funext fun r => (first_hasDerivAt n L r).deriv
  have h1 : ContDiff ℝ 1 (first n L) := contDiff_one_iff_deriv.mpr
    ⟨fun r => (first_hasDerivAt n L r).differentiableAt,
      by rw [hd]; exact second_continuous n L⟩
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨fun r => (value_hasDerivAt n L r).differentiableAt,
    by simp, by rw [he]; exact h1⟩

theorem value_deriv (n : ℕ) (L : Tests) (r : ℝ) : deriv (value n L) r = first n L r :=
  (value_hasDerivAt n L r).deriv

theorem value_second_deriv (n : ℕ) (L : Tests) (r : ℝ) :
    deriv (deriv (value n L)) r = second n L r := by
  rw [show deriv (value n L) = first n L from funext (value_deriv n L)]
  exact (first_hasDerivAt n L r).deriv

theorem source_pairing (ρ : ℝ → ℝ) (hc : Continuous ρ) (hs : HasCompactSupport ρ)
    (L : Tests) (r : ℝ) :
    inner ℝ (testNoise L) (wholeLineScenery ρ r) = L (embedding (convolutionKernel ρ r)) := by
  rw [← convolutionKernel_realizes hc hs r, real_inner_comm]
  exact actual_pairing _ L

theorem first_physical (n : ℕ) (L : Tests) (r : ℝ) : first n L r = L (translated n r) := by
  rw [first, source_pairing _
    ((IBMMollifier.kernel_smooth n).continuous_deriv (by norm_num))
    (IBMMollifier.kernel_compactSupport n).deriv,
    derivative_eq_translated ((IBMMollifier.kernel_smooth n).of_le (by norm_num))
      (IBMMollifier.kernel_compactSupport n)]
  rfl

theorem second_physical (n : ℕ) (L : Tests) (r : ℝ) : second n L r =
    L (embedding (translatedClass (deriv (IBMMollifier.kernel n))
      ((IBMMollifier.kernel_smooth n).continuous_deriv (by norm_num))
      (IBMMollifier.kernel_compactSupport n).deriv r)) := by
  have h2 : ContDiff ℝ 2 (IBMMollifier.kernel n) :=
    (IBMMollifier.kernel_smooth n).of_le (by norm_num)
  rw [second, source_pairing _ (h2.deriv'.continuous_deriv le_rfl)
    (IBMMollifier.kernel_compactSupport n).deriv.deriv,
    derivative_eq_translated h2.deriv' (IBMMollifier.kernel_compactSupport n).deriv]

def bound0 (n : ℕ) (L : Tests) : ℝ≥0 :=
  ⟨‖L‖*‖embedding‖*(eLpNorm (IBMMollifier.kernel n) 2 volume).toReal, by positivity⟩

def bound1 (n : ℕ) (L : Tests) : ℝ≥0 :=
  ⟨‖L‖*‖embedding‖*(eLpNorm (deriv (IBMMollifier.kernel n)) 2 volume).toReal, by positivity⟩

theorem first_bound (n : ℕ) (L : Tests) (r : ℝ) : ‖deriv (value n L) r‖ ≤ bound0 n L := by
  rw [value_deriv, first_physical]
  change ‖L (embedding (translatedClass (IBMMollifier.kernel n)
    (IBMMollifier.kernel_smooth n).continuous (IBMMollifier.kernel_compactSupport n) r))‖ ≤ _
  exact ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (embedding.le_opNorm _)
    (norm_nonneg _))).trans_eq (by
      rw [IBMSchwartzPhysicalGlobalBounds.translated_norm]
      change ‖L‖ * (‖embedding‖ * _) = ‖L‖ * ‖embedding‖ * _
      exact (mul_assoc _ _ _).symm)

theorem second_bound (n : ℕ) (L : Tests) (r : ℝ) :
    ‖deriv (deriv (value n L)) r‖ ≤ bound1 n L := by
  rw [value_second_deriv, second_physical]
  exact ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (embedding.le_opNorm _)
    (norm_nonneg _))).trans_eq (by
      rw [IBMSchwartzPhysicalGlobalBounds.translated_norm]
      change ‖L‖ * (‖embedding‖ * _) = ‖L‖ * ‖embedding‖ * _
      exact (mul_assoc _ _ _).symm)

theorem first_tendsto (L : Tests) (r : ℝ) :
    Tendsto (fun n => first n L r) atTop (nhds (L (dirac r))) := by
  simpa only [Function.comp_def, first_physical] using
    L.continuous.tendsto _ |>.comp (translated_tendsto r)

theorem value_zero_tendsto (L : Tests) : Tendsto (fun n => value n L 0) atTop (nhds 0) := by
  have h := (L.comp embedding).continuous.tendsto _ |>.comp (mollifier_kernel_tendsto 0)
  simpa only [value, source_pairing _ (IBMMollifier.kernel_smooth _).continuous
    (IBMMollifier.kernel_compactSupport _), vector_zero, map_zero,
    Function.comp_def, ContinuousLinearMap.comp_apply] using h

end OperatorDerivativeRewrite.Foundation.IBMPhysicalRunningPrimitive
