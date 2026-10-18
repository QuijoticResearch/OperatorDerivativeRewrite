import Foundation.MultivariatePolynomialNilpotence
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Actual complete directional heat operators and their finite signed-kernel realization. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.MultivariateFactorialHeat
open MultivariateFactorialDomain MultivariatePolynomialNilpotence
variable {ι : Type*} [DecidableEq ι]

def evolution (p : ℕ) (a : ℝ) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) : H ι →L[ℝ] H ι :=
  NormedSpace.exp (a • (derivative v hv)^p)

def polynomialEvolution (p : ℕ) (a : ℝ) (v : ι → ℝ) (P : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ k ∈ Finset.range (P.totalDegree+1), (a^k/(k.factorial : ℝ)) •
    ((polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[p*k] P)

omit [DecidableEq ι] in
theorem scaled_pow (a : ℝ) (A : H ι →L[ℝ] H ι) (k : ℕ) : (a • A)^k = a^k • A^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    apply ContinuousLinearMap.ext
    intro u
    change a^k • ((A^k) (a • A u)) = (a^k*a) • ((A^k) (A u))
    rw [map_smul, smul_smul]

theorem evolution_series (p : ℕ) (a : ℝ) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (u : H ι) :
    HasSum (fun k : ℕ => (a^k/(k.factorial : ℝ)) • (((derivative v hv)^(p*k)) u))
      (evolution p a v hv u) := by
  have h := (ContinuousLinearMap.apply ℝ (H ι) u).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a • (derivative v hv)^p))
  convert h using 1
  · funext k
    rw [scaled_pow, ← pow_mul]
    change (a^k/(k.factorial : ℝ)) • (((derivative v hv)^(p*k)) u) =
      (k.factorial : ℝ)⁻¹ • (a^k • (((derivative v hv)^(p*k)) u))
    rw [smul_smul]
    congr 1
    ring
  · rfl

theorem evolution_polynomial (p : ℕ) (hp : 0 < p) (a : ℝ) (v : ι → ℝ)
    (hv : ∀ i, |v i| ≤ 1) (P : MvPolynomial ι ℝ) :
    evolution p a v hv (polynomial P) = polynomial (polynomialEvolution p a v P) := by
  have hs := evolution_series p a v hv (polynomial P)
  have hf := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range (P.totalDegree+1))
    (f := fun k : ℕ => (a^k/(k.factorial : ℝ)) • (((derivative v hv)^(p*k)) (polynomial P)))
    (fun k hk => by
      have hk' : P.totalDegree < p*k := by
        have he : P.totalDegree+1 ≤ k := Nat.le_of_not_gt (by simpa using hk)
        have hpk : k ≤ p*k := by nlinarith
        omega
      rw [completed_iterate_zero v hv P (p*k) hk', smul_zero])
  rw [hs.unique hf]
  change _ = polynomialMap (∑ k ∈ Finset.range (P.totalDegree+1), _)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]
  exact congrArg (fun u : H ι => (a^k/(k.factorial:ℝ)) • u) (derivative_iterate_core v hv (p*k) P)

theorem evolution_bound (p : ℕ) (a : ℝ) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) :
    ‖evolution p a v hv‖ ≤ Real.exp |a| := by
  have hr : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) * |a|^k) (Real.exp |a|) := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) |a|
  apply (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    (a • (derivative v hv)^p)).norm_le_of_bounded hr
  intro k
  rw [scaled_pow, ← pow_mul, norm_smul, norm_smul, norm_inv, Real.norm_natCast,
    Real.norm_eq_abs, abs_pow]
  have hs := derivative_power_norm v hv (p*k)
  calc
    _ ≤ (k.factorial : ℝ)⁻¹ * (|a|^k * 1) := by gcongr
    _ = _ := by ring

theorem evolution_zero (p : ℕ) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) :
    evolution p 0 v hv = ContinuousLinearMap.id ℝ (H ι) := by
  have hz : (0:ℝ) • (derivative v hv)^p = (0 : H ι →L[ℝ] H ι) := by
    ext u
    simp only [zero_smul, zero_apply]
  let : NormedAlgebra ℚ (H ι →L[ℝ] H ι) := NormedAlgebra.restrictScalars ℚ ℝ _
  rw [evolution, hz, NormedSpace.exp_zero]
  rfl

theorem evolution_add (p : ℕ) (a b : ℝ) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) :
    (evolution p a v hv).comp (evolution p b v hv) = evolution p (a+b) v hv := by
  let A := (derivative v hv)^p
  have hc : Commute (a • A) (b • A) := by
    apply ContinuousLinearMap.ext
    intro u
    change a • (A (b • A u)) = b • (A (a • A u))
    rw [map_smul, map_smul, smul_smul, smul_smul]
    congr 1
    ring
  let : NormedAlgebra ℚ (H ι →L[ℝ] H ι) := NormedAlgebra.restrictScalars ℚ ℝ _
  change NormedSpace.exp (a • A) * NormedSpace.exp (b • A) = NormedSpace.exp ((a+b) • A)
  have ha : (a+b) • A = a • A + b • A := by
    ext u
    simp only [smul_apply, add_apply, add_smul]
  rw [ha, NormedSpace.exp_add_of_commute hc]

theorem evolution_unique (p : ℕ) (hp : 0 < p) (a : ℝ) (v : ι → ℝ)
    (hv : ∀ i, |v i| ≤ 1) (L : H ι →L[ℝ] H ι)
    (hL : ∀ P, L (polynomial P) = polynomial (polynomialEvolution p a v P)) :
    L = evolution p a v hv := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer L.continuous (evolution p a v hv).continuous
  funext P
  exact (hL P).trans (evolution_polynomial p hp a v hv P).symm

omit [DecidableEq ι] in
theorem polynomialEvolution_bound (p : ℕ) (hp : 0 < p) (a : ℝ) (v : ι → ℝ)
    (hv : ∀ i, |v i| ≤ 1) (P : MvPolynomial ι ℝ) :
    ‖polynomial (polynomialEvolution p a v P)‖ ≤ Real.exp |a| * ‖polynomial P‖ := by
  classical
  rw [← evolution_polynomial p hp a v hv]
  exact (evolution p a v hv).le_of_opNorm_le (evolution_bound p a v hv) _

end OperatorDerivativeRewrite.Foundation.MultivariateFactorialHeat
