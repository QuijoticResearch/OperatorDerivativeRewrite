import Foundation.IBMSineSpatialBoundary
import Foundation.BochnerL2Approximation
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Completed local nonlinear stochastic source integral: genuine strong
convergence of the original native operators on EVERY rough spatial L2 input. -/
noncomputable section
open MeasureTheory Filter Set Bornology
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearSpatialLimit
open InfiniteGaussian IBMNonlinearSpatialOperator
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def core (a b : ℝ) : Set (Space a b) :=
  {u | ∃ φ : ℝ → ℝ, u =ᵐ[volume.restrict (Ioc a b)] φ ∧
    HasCompactSupport φ ∧ ContDiff ℝ (↑(⊤ : ENat)) φ}

theorem core_dense (a b : ℝ) : Dense (core a b) :=
  MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num : (2 : ℝ≥0∞) ≠ ∞)

theorem core_converges {a b : ℝ} (hab : a ≤ b) (u : Space a b) (hu : u ∈ core a b) :
    ∃ v : GaussianL2, Tendsto (fun n => operator n hab u) atTop (𝓝 v) := by
  obtain ⟨φ,hφ,_,hs⟩ := hu
  exact ⟨_, IBMSineSpatialBoundary.operator_core_tendsto φ
    (hs.of_le (by norm_num)) hab u hφ⟩

theorem distance_bound (n : ℕ) {a b : ℝ} (hab : a ≤ b) (u v : Space a b) :
    dist (operator n hab u) (operator n hab v) ≤ Real.sqrt (1+4*(b-a)) * dist u v := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact native_bound n hab (u-v)

/-- Cauchy convergence is proved from the genuine dense smooth core and the
uniform bound; it is not an assumed closure or convergence hypothesis. -/
theorem native_cauchy {a b : ℝ} (hab : a ≤ b) (u : Space a b) :
    CauchySeq (fun n => operator n hab u) := by
  let M := Real.sqrt (1+4*(b-a))
  have hM : 0 < M := Real.sqrt_pos.2 (by linarith)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨v,hv,hclose⟩ := (core_dense a b).exists_dist_lt u
    (show 0 < ε/(4*M) by positivity)
  obtain ⟨w,hw⟩ := core_converges hab v hv
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hw.cauchySeq (ε/2) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmid := hN m hm n hn
  have hleft := distance_bound m hab u v
  have hright := distance_bound n hab v u
  rw [dist_comm v u] at hright
  have hsmall : dist u v * (4*M) < ε :=
    (lt_div_iff₀ (show 0 < 4*M by positivity)).mp hclose
  have ht1 := dist_triangle (operator m hab u) (operator m hab v) (operator n hab u)
  have ht2 := dist_triangle (operator m hab v) (operator n hab v) (operator n hab u)
  change dist (operator m hab u) (operator m hab v) ≤ M * dist u v at hleft
  change dist (operator n hab v) (operator n hab u) ≤ M * dist u v at hright
  nlinarith

def value {a b : ℝ} (hab : a ≤ b) (u : Space a b) : GaussianL2 :=
  Classical.choose (cauchySeq_tendsto_of_complete (native_cauchy hab u))

theorem value_tendsto {a b : ℝ} (hab : a ≤ b) (u : Space a b) :
    Tendsto (fun n => operator n hab u) atTop (𝓝 (value hab u)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (native_cauchy hab u))

/-- Existing Mathlib pointwise bounded-limit construction supplies linearity
and continuity of the completed actual stochastic source integral. -/
def completed {a b : ℝ} (hab : a ≤ b) : Space a b →L[ℝ] GaussianL2 :=
  ContinuousLinearMap.ofTendstoOfBoundedRange (value hab) (fun n => operator n hab)
    (tendsto_pi_nhds.mpr (value_tendsto hab))
    (isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt (1+4*(b-a)), by
      rintro _ ⟨n,rfl⟩
      exact operator_norm_le n hab⟩)

theorem completed_apply {a b : ℝ} (hab : a ≤ b) (u : Space a b) :
    completed hab u = value hab u := rfl

attribute [local irreducible] completed value

/-- Strong source-L2 convergence at EVERY rough spatial-L2 input. This is
pointwise strong operator convergence, not operator-norm convergence. -/
theorem completed_tendsto {a b : ℝ} (hab : a ≤ b) (u : Space a b) :
    Tendsto (fun n => operator n hab u) atTop (𝓝 (completed hab u)) := by
  rw [completed_apply]
  exact value_tendsto hab u

theorem completed_bound {a b : ℝ} (hab : a ≤ b) (u : Space a b) :
    ‖completed hab u‖ ≤ Real.sqrt (1+4*(b-a)) * ‖u‖ :=
  le_of_tendsto (completed_tendsto hab u).norm
    (Eventually.of_forall fun n => native_bound n hab u)

theorem completed_norm_le {a b : ℝ} (hab : a ≤ b) :
    ‖completed hab‖ ≤ Real.sqrt (1+4*(b-a)) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (completed_bound hab)

theorem completed_core {a b : ℝ} (hab : a ≤ b) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (u : Space a b) (hu : u =ᵐ[volume.restrict (Ioc a b)] φ) :
    completed hab u = IBMSineSpatialBoundary.boundaryClass φ hφ hab none :=
  tendsto_nhds_unique (completed_tendsto hab u)
    (IBMSineSpatialBoundary.operator_core_tendsto φ hφ hab u hu)

theorem completed_core_ae {a b : ℝ} (hab : a ≤ b) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (u : Space a b) (hu : u =ᵐ[volume.restrict (Ioc a b)] φ) :
    completed hab u =ᵐ[gaussianProduct] fun ω =>
      φ b * Real.sin (IBMConstructedSources.sceneryPath ω b) -
        φ a * Real.sin (IBMConstructedSources.sceneryPath ω a) -
          ∫ r in a..b, deriv φ r * Real.sin (IBMConstructedSources.sceneryPath ω r) := by
  rw [completed_core hab φ hφ u hu]
  filter_upwards [IBMSineSpatialBoundary.boundaryClass_ae φ hφ hab none] with ω hω
  simpa only [IBMSineSpatialBoundary.sample, IBMSineSpatialBoundary.tested,
    IBMSineSpatialDistribution.path, IBMSineSpatialDistribution.tested, sub_eq_add_neg] using hω

/-- Actual Bochner clock-L2 fields of rough spatial tests also converge
strongly on the fixed finite window. Native IBM clock identification is separate. -/
theorem clock_lift_tendsto {a b : ℝ} (hab : a ≤ b)
    (u : Lp (Space a b) 2 gaussianProduct) :
    Tendsto (fun n => (operator n hab).compLpL 2 gaussianProduct u) atTop
      (𝓝 ((completed hab).compLpL 2 gaussianProduct u)) := by
  let M := Real.sqrt (1+4*(b-a))
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hm : MemLp (fun Y => M*‖u Y‖) 2 gaussianProduct := (Lp.memLp u).norm.const_mul M
  let B := hm.toLp (fun Y => M*‖u Y‖)
  apply BochnerL2Approximation.tendsto_of_dominated _ _ B
  · intro n
    filter_upwards [(operator n hab).coeFn_compLpL u, hm.coeFn_toLp] with Y hu hB
    change B Y = M*‖u Y‖ at hB
    rw [hu, hB, Real.norm_of_nonneg (mul_nonneg hM (norm_nonneg _))]
    exact native_bound n hab (u Y)
  · filter_upwards [(completed hab).coeFn_compLpL u, hm.coeFn_toLp] with Y hu hB
    change B Y = M*‖u Y‖ at hB
    rw [hu, hB, Real.norm_of_nonneg (mul_nonneg hM (norm_nonneg _))]
    exact completed_bound hab (u Y)
  · filter_upwards [ae_all_iff.mpr (fun n => (operator n hab).coeFn_compLpL u),
      (completed hab).coeFn_compLpL u] with Y hn hA
    have he : (fun n => ((operator n hab).compLpL 2 gaussianProduct u) Y) =
        fun n => operator n hab (u Y) := funext hn
    rw [he, hA]
    exact completed_tendsto hab (u Y)

end OperatorDerivativeRewrite.Foundation.IBMNonlinearSpatialLimit
