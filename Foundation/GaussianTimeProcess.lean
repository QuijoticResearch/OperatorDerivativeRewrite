import Foundation.GaussianHilbertProcess
import Foundation.GaussianTimeHilbert
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Adapted

/-!
# A concrete pre-Brownian process on the countable Gaussian product

Time indicators in actual Lebesgue L² are sent through the constructed Hilbert
embedding and first-chaos isometry. Brownian finite-dimensional laws and
independent increments are derived from their covariance. No path continuity,
completed natural filtration, or stochastic-integral completion is asserted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianTimeProcess

open InfiniteGaussian GaussianTimeHilbert GaussianHilbertProcess
attribute [local instance] timeHilbert_secondCountable

/-- The actual L² Gaussian class of the indicator of `(0,t]`. -/
def wienerL2 (t : ℝ≥0) : GaussianL2 := isonormalEmbedding TimeHilbert (timeVector t)

/-- Chosen measurable representatives, with all finite-dimensional laws proved below. -/
def process (t : ℝ≥0) : SampleSpace → ℝ := wienerL2 t

theorem process_stronglyMeasurable (t : ℝ≥0) : StronglyMeasurable (process t) :=
  Lp.stronglyMeasurable (wienerL2 t)

theorem process_memLp (t : ℝ≥0) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (process t) p gaussianProduct := isonormal_memLp (timeVector t) p hp

theorem process_integral (t : ℝ≥0) : (∫ ω, process t ω ∂gaussianProduct) = 0 :=
  isonormal_integral (timeVector t)

theorem process_product_integrable (s t : ℝ≥0) :
    Integrable (fun ω => process s ω * process t ω) gaussianProduct :=
  isonormal_product_integrable (timeVector s) (timeVector t)

theorem process_product_integral (s t : ℝ≥0) :
    (∫ ω, process s ω * process t ω ∂gaussianProduct) = min (s : ℝ) (t : ℝ) := by
  exact (isonormal_product_integral (timeVector s) (timeVector t)).trans (timeVector_inner s t)

theorem process_covariance (s t : ℝ≥0) :
    cov[process s, process t; gaussianProduct] = min (s : ℝ) (t : ℝ) :=
  (isonormal_covariance (timeVector s) (timeVector t)).trans (timeVector_inner s t)

theorem process_isGaussianProcess : IsGaussianProcess process gaussianProduct :=
  isonormal_isGaussianProcess.comp_right timeVector

/-- Actual Brownian finite-dimensional distributions, derived rather than postulated. -/
theorem process_isPreBrownian : IsPreBrownianReal process gaussianProduct :=
  process_isGaussianProcess.isPreBrownianReal_of_covariance process_integral
    (fun s t hst => by
      rw [process_covariance]
      exact min_eq_left (show (s : ℝ) ≤ (t : ℝ) from hst))

theorem process_hasLaw (t : ℝ≥0) : HasLaw (process t) (gaussianReal 0 t) gaussianProduct :=
  process_isPreBrownian.hasLaw_eval t

theorem wienerL2_zero : wienerL2 0 = 0 := by
  unfold wienerL2
  rw [timeVector_zero, map_zero]

theorem process_zero_ae : process 0 =ᵐ[gaussianProduct] fun _ => (0 : ℝ) :=
  process_isPreBrownian.eval_zero_ae_eq_zero

/-- The actual increment class is the isonormal image of its interval indicator. -/
theorem wienerL2_sub (s t : ℝ≥0) (hst : s ≤ t) :
    wienerL2 t - wienerL2 s = isonormalEmbedding TimeHilbert (intervalVector s t) := by
  unfold wienerL2
  rw [← map_sub, timeVector_sub s t hst]

theorem process_increment_ae (s t : ℝ≥0) (hst : s ≤ t) :
    isonormal TimeHilbert (intervalVector s t) =ᵐ[gaussianProduct]
      fun ω => process t ω - process s ω := by
  rw [← timeVector_sub s t hst]
  exact isonormal_sub_ae (timeVector t) (timeVector s)

theorem wienerL2_sub_norm_sq (s t : ℝ≥0) (hst : s ≤ t) :
    ‖wienerL2 t - wienerL2 s‖ ^ 2 = (t : ℝ) - s := by
  unfold wienerL2
  rw [← map_sub, (isonormalEmbedding TimeHilbert).norm_map]
  exact timeVector_sub_norm_sq s t hst

theorem process_increment_hasLaw (s t : ℝ≥0) :
    HasLaw (process t - process s) (gaussianReal 0 (nndist (t : ℝ) (s : ℝ)))
      gaussianProduct := process_isPreBrownian.hasLaw_sub t s

/-- Mutual independence of increments over any ordered finite time partition. -/
theorem process_hasIndepIncrements : HasIndepIncrements process gaussianProduct :=
  process_isPreBrownian.hasIndepIncrements

private theorem disjoint_increments_aux {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} (hB : HasIndepIncrements B μ)
    (a b c d : ℝ≥0)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    IndepFun (fun ω => B b ω - B a ω) (fun ω => B d ω - B c ω) μ := by
  let τ : Fin 4 → ℝ≥0 := ![a, b, c, d]
  have hτ : Monotone τ := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp [τ, hab, hbc, hcd]
  exact (hB 3 τ hτ).indepFun (by decide : (0 : Fin 3) ≠ 2)

/-- Independence for two nonoverlapping increments, allowing zero-length intervals. -/
theorem process_disjoint_increments_independent (a b c d : ℝ≥0)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    IndepFun (fun ω => process b ω - process a ω)
      (fun ω => process d ω - process c ω) gaussianProduct :=
  disjoint_increments_aux process_hasIndepIncrements a b c d hab hbc hcd

/-- The actual natural filtration of the constructed representatives. -/
def naturalFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) :=
  Filtration.natural process process_stronglyMeasurable

theorem process_stronglyAdapted : StronglyAdapted naturalFiltration process :=
  Filtration.stronglyAdapted_natural process_stronglyMeasurable

end OperatorDerivativeRewrite.Foundation.GaussianTimeProcess
