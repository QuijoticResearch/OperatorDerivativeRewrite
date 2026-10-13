import Foundation.GaussianStoppedComposition
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Actual finite-dimensional differential and covariance-Hessian contraction.
All derivative data below are Mathlib Frechet derivatives of the given function. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteCovarianceHessian
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def direction (i : ι) : ι → ℝ := Pi.single i 1

def partialDerivative (Φ : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ Φ x (direction i)

def hessian (Φ : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ Φ) x

def mixedPartial (Φ : (ι → ℝ) → ℝ) (i j : ι) (x : ι → ℝ) : ℝ :=
  hessian Φ x (direction i) (direction j)

theorem direction_norm (i : ι) : ‖direction i‖ = 1 := by simp [direction, Pi.norm_single]

theorem coordinate_expansion (v : ι → ℝ) :
    v = ∑ i, v i • direction i := by
  simpa only [direction, ← Pi.single_smul, smul_eq_mul, mul_one] using (Finset.univ_sum_single v).symm

theorem differential_expansion (Φ : (ι → ℝ) → ℝ) (x v : ι → ℝ) :
    fderiv ℝ Φ x v = ∑ i, v i * partialDerivative Φ i x := by
  conv_lhs => rw [coordinate_expansion v]
  simp only [map_sum, map_smul, partialDerivative, smul_eq_mul]

theorem hessian_expansion (Φ : (ι → ℝ) → ℝ) (x v w : ι → ℝ) :
    hessian Φ x v w = ∑ i, ∑ j, v i * w j * mixedPartial Φ i j x := by
  calc
    _ = hessian Φ x (∑ i, v i • direction i) (∑ j, w j • direction j) := by
      rw [← coordinate_expansion, ← coordinate_expansion]
    _ = _ := by
      simp only [mixedPartial, map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem line_hasDerivAt (Φ : (ι → ℝ) → ℝ) (hΦ : Differentiable ℝ Φ)
    (x v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Φ (x + s • v)) (fderiv ℝ Φ (x + t • v) v) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hΦ (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl

theorem line_second_hasDerivAt (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (x v : ι → ℝ) (t : ℝ) :
    HasDerivAt (deriv (fun s : ℝ => Φ (x + s • v)))
      (hessian Φ (x + t • v) v v) t := by
  have hD : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hd := ((hD.differentiable (by norm_num) (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl).clm_apply
    (hasDerivAt_const t v)
  have he : deriv (fun s : ℝ => Φ (x + s • v)) = fun s => fderiv ℝ Φ (x + s • v) v :=
    funext fun s => (line_hasDerivAt Φ (hΦ.differentiable (by norm_num)) x v s).deriv
  rw [he]
  simpa [hessian] using hd

theorem partial_contDiff_one (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ) (i : ι) :
    ContDiff ℝ 1 (partialDerivative Φ i) :=
  (hΦ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem mixedPartial_continuous (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ) (i j : ι) :
    Continuous (mixedPartial Φ i j) :=
  (((hΦ.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply
    continuous_const).clm_apply continuous_const

theorem partial_bound (Φ : (ι → ℝ) → ℝ) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ Φ x‖ ≤ M) (i : ι) (x : ι → ℝ) : ‖partialDerivative Φ i x‖ ≤ M := by
  calc
    _ ≤ ‖fderiv ℝ Φ x‖ * ‖direction i‖ := (fderiv ℝ Φ x).le_opNorm _
    _ ≤ M := by rw [direction_norm, mul_one]; exact hM x

theorem mixedPartial_bound (Φ : (ι → ℝ) → ℝ) {M : ℝ}
    (hM : ∀ x, ‖hessian Φ x‖ ≤ M) (i j : ι) (x : ι → ℝ) : ‖mixedPartial Φ i j x‖ ≤ M := by
  calc
    _ ≤ ‖hessian Φ x (direction i)‖ * ‖direction j‖ := (hessian Φ x (direction i)).le_opNorm _
    _ ≤ ‖hessian Φ x‖ := by
      rw [direction_norm, mul_one]
      simpa only [direction_norm, mul_one] using (hessian Φ x).le_opNorm (direction i)
    _ ≤ M := hM x

/-- A covariance matrix constructed from genuine finite noise directions. -/
def covariance {κ : Type*} [Fintype κ] (k : κ → ι → ℝ) (i j : ι) : ℝ :=
  ∑ a, k a i * k a j

theorem covariance_symmetric {κ : Type*} [Fintype κ] (k : κ → ι → ℝ) (i j : ι) :
    covariance k i j = covariance k j i := by simp only [covariance, mul_comm]

theorem covariance_nonneg {κ : Type*} [Fintype κ] (k : κ → ι → ℝ) (v : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * covariance k i j * v j := by
  have he : (∑ i, ∑ j, v i * covariance k i j * v j) = ∑ a, (∑ i, v i * k a i)^2 := by
    calc
      _ = ∑ i, ∑ j, ∑ a, v i * (k a i * k a j) * v j := by
        simp only [covariance, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ i, ∑ a, ∑ j, v i * (k a i * k a j) * v j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ j, v i * (k a i * k a j) * v j := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [he]
  exact Finset.sum_nonneg (fun a _ => sq_nonneg _)

theorem covariance_hessian_contraction {κ : Type*} [Fintype κ]
    (Φ : (ι → ℝ) → ℝ) (x : ι → ℝ) (k : κ → ι → ℝ) :
    (∑ a, hessian Φ x (k a) (k a)) =
      ∑ i, ∑ j, mixedPartial Φ i j x * covariance k i j := by
  simp only [hessian_expansion, covariance, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Mixed partials are derivatives of actual coordinate partial derivatives. -/
theorem partial_hasFDerivAt (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ) (j : ι) (x : ι → ℝ) :
    HasFDerivAt (partialDerivative Φ j) ((hessian Φ x).flip (direction j)) x := by
  have hD : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  convert ((hD.differentiable (by norm_num) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const (direction j) x)) using 1 <;> (try funext y) <;> simp [partialDerivative, hessian]

theorem mixedPartial_eq_fderiv_partial (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (i j : ι) (x : ι → ℝ) :
    mixedPartial Φ i j x = fderiv ℝ (partialDerivative Φ j) x (direction i) := by
  rw [(partial_hasFDerivAt Φ hΦ j x).fderiv]
  rfl

theorem mixedPartial_symmetric (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (i j : ι) (x : ι → ℝ) : mixedPartial Φ i j x = mixedPartial Φ j i x :=
  hΦ.contDiffAt.isSymmSndFDerivAt (by simp) (direction i) (direction j)
end OperatorDerivativeRewrite.Foundation.FiniteCovarianceHessian
