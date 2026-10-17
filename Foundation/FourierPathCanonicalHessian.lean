import Foundation.FourierPathTimeHessian

/-! Canonical Hessians and actual time densities independent of positive heat partitions. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathCanonicalHessian
open HigherHeatDyadicLaws HigherHeatFourierBanach FourierPathBoundedControls
open FourierPathControlGradient FourierPathControlHessian FourierPathTimeHessian
open HigherHeatFourierTranslations

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem hessian_partition (m : ℕ) (hm : 0 < m) (S T A B : ℝ≥0)
    (hS : 0 < S) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) (he : S+T=A+B)
    (q : TestSpace levels ξ) :
    hessian levels ξ m hm S T hS hT q = hessian levels ξ m hm A B hA hB q := by
  have hs := derivative_hasFDerivAt levels ξ m hm S T hS hT q 0
  have ht := derivative_hasFDerivAt levels ξ m hm A B hA hB q 0
  rw [FourierPathControlFrechet.direction_zero, translation_zero] at hs ht
  have hs' : HasFDerivAt
      (fun v => gradient levels ξ m hm (A+B) (add_pos hA hB) (translation levels ξ (direction v) q))
      (hessian levels ξ m hm S T hS hT q) 0 := by
    simpa only [he] using hs
  exact hs'.unique ht

theorem timeHessian_partition (m : ℕ) (hm : 0 < m) (S T A B : ℝ≥0)
    (hS : 0 < S) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) (he : S+T=A+B)
    (q : TestSpace levels ξ) :
    timeHessian levels ξ m hm S T hS hT q = timeHessian levels ξ m hm A B hA hB q := by
  apply timeHessian_unique levels ξ m hm A B hA hB q
  intro u v
  rw [timeHessian_pairing, hessian_partition levels ξ m hm S T A B hS hT hA hB he q]

def canonicalHessian (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    Control →L[ℝ] (Control →L[ℝ] TestSpace levels ξ) :=
  hessian levels ξ m hm (T/2) (T/2) (div_pos hT (by norm_num)) (div_pos hT (by norm_num)) q

def canonicalTimeHessian (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    BochnerTimeControlPairing.Field (BochnerTimeControlPairing.Field (TestSpace levels ξ)) :=
  timeHessian levels ξ m hm (T/2) (T/2) (div_pos hT (by norm_num)) (div_pos hT (by norm_num)) q

theorem canonical_partition (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A B : ℝ≥0) (hA : 0 < A) (hB : 0 < B) (he : A+B=T) (q : TestSpace levels ξ) :
    timeHessian levels ξ m hm A B hA hB q = canonicalTimeHessian levels ξ m hm T hT q := by
  apply timeHessian_partition levels ξ m hm A B (T/2) (T/2) hA hB
    (div_pos hT (by norm_num)) (div_pos hT (by norm_num)) _ q
  rw [he]
  ring

end OperatorDerivativeRewrite.Foundation.FourierPathCanonicalHessian
