import Foundation.GaussianTimeSpaceHermite
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Algebraic backward-heat calculus for actual bivariate polynomials.
Coordinate 0 is time and coordinate 1 is space. -/
noncomputable section
open MvPolynomial Set
namespace OperatorDerivativeRewrite.Foundation.GaussianPolynomialHeat
abbrev SpaceTimePolynomial := MvPolynomial (Fin 2) ℝ

def raise (p : SpaceTimePolynomial) : SpaceTimePolynomial :=
  X 1 * p - X 0 * pderiv 1 p

def hermite : ℕ → SpaceTimePolynomial
  | 0 => 1
  | n + 1 => raise (hermite n)

@[simp] theorem hermite_zero : hermite 0 = 1 := rfl
theorem hermite_succ (n : ℕ) : hermite (n + 1) = raise (hermite n) := rfl
@[simp] theorem hermite_one : hermite 1 = X 1 := by simp [hermite_succ, raise]

theorem raise_smul (c : ℝ) (p : SpaceTimePolynomial) : raise (c • p) = c • raise p := by
  simp only [raise, Derivation.map_smul, mul_smul_comm, smul_sub]

theorem spatial_raise (p : SpaceTimePolynomial) :
    pderiv 1 (raise p) = p + raise (pderiv 1 p) := by
  simp [raise, pderiv_mul]
  ring

theorem hermite_spatial (n : ℕ) : pderiv 1 (hermite (n + 1)) = (n + 1 : ℝ) • hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ, spatial_raise, ih, raise_smul, ← hermite_succ]
    push_cast
    module

theorem hermite_recursion (n : ℕ) :
    hermite (n + 2) = X 1 * hermite (n + 1) - (n + 1 : ℝ) • (X 0 * hermite n) := by
  rw [hermite_succ, raise, hermite_spatial, mul_smul_comm]

def heat : SpaceTimePolynomial →ₗ[ℝ] SpaceTimePolynomial :=
  (pderiv 0).toLinearMap + (1 / 2 : ℝ) • ((pderiv 1).toLinearMap.comp (pderiv 1).toLinearMap)

theorem heat_apply (p : SpaceTimePolynomial) :
    heat p = pderiv 0 p + (1 / 2 : ℝ) • pderiv 1 (pderiv 1 p) := rfl

theorem mixed_pderiv (p : SpaceTimePolynomial) :
    pderiv 0 (pderiv 1 p) = pderiv 1 (pderiv 0 p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i ih => fin_cases i <;> simp [pderiv_mul, ih] <;> ring

theorem heat_raise (p : SpaceTimePolynomial) : heat (raise p) = raise (heat p) := by
  simp only [heat_apply, raise, map_sub, map_add, Derivation.map_smul, pderiv_mul]
  simp
  rw [mixed_pderiv]
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, mul_sub]
  module

theorem hermite_heat (n : ℕ) : heat (hermite n) = 0 := by
  induction n with
  | zero => simp [heat_apply]
  | succ n ih => rw [hermite_succ, heat_raise, ih]; simp [raise]

def basisPolynomial (kn : ℕ × ℕ) : SpaceTimePolynomial := X 0 ^ kn.1 * hermite kn.2

theorem heat_time_mul (k : ℕ) (p : SpaceTimePolynomial) :
    heat (X 0 ^ k * p) = (k : ℝ) • (X 0 ^ (k - 1) * p) + X 0 ^ k * heat p := by
  simp [heat_apply, pderiv_pow, Algebra.smul_def]
  ring

theorem basis_heat (k n : ℕ) :
    heat (basisPolynomial (k, n)) = (k : ℝ) • basisPolynomial (k - 1, n) := by
  simp only [basisPolynomial, heat_time_mul, hermite_heat, mul_zero, add_zero]

theorem basis_spatial_succ (k n : ℕ) :
    pderiv 1 (basisPolynomial (k, n + 1)) = (n + 1 : ℝ) • basisPolynomial (k, n) := by
  simp [basisPolynomial, pderiv_pow, hermite_spatial, mul_smul_comm]

theorem basis_spatial_zero (k : ℕ) : pderiv 1 (basisPolynomial (k, 0)) = 0 := by
  simp [basisPolynomial, pderiv_pow]

def specialize (t : ℝ) : SpaceTimePolynomial →ₐ[ℝ] MvPolynomial Unit ℝ :=
  aeval (fun i => if i = 0 then C t else X ())

@[simp] theorem specialize_time (t : ℝ) : specialize t (X 0) = C t := by simp [specialize]
@[simp] theorem specialize_space (t : ℝ) : specialize t (X 1) = X () := by simp [specialize]

theorem specialize_spatial (t : ℝ) (p : SpaceTimePolynomial) :
    specialize t (pderiv 1 p) = pderiv () (specialize t p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [specialize]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i ih => fin_cases i <;> simp [ih]

theorem specialize_hermite (t : ℝ) (n : ℕ) :
    specialize t (hermite n) = GaussianTimeSpaceHermite.polynomial t n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ, raise, map_sub, map_mul, map_mul, specialize_spatial,
      specialize_time, specialize_space, ih, GaussianTimeSpaceHermite.polynomial_succ]
    simp [GaussianTimeSpaceHermite.raise, Algebra.smul_def]

theorem specialize_basis (t : ℝ) (k n : ℕ) :
    specialize t (basisPolynomial (k, n)) =
      t ^ k • GaussianTimeSpaceHermite.polynomial t n := by
  simp only [basisPolynomial, map_mul, map_pow, specialize_time, specialize_hermite]
  simp [Algebra.smul_def]

theorem eval_specialize (t x : ℝ) (p : SpaceTimePolynomial) :
    eval (fun _ : Unit => x) (specialize t p) = eval ![t, x] p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [specialize]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i ih => fin_cases i <;> simp [ih]

theorem basisPolynomial_span : Submodule.span ℝ (Set.range basisPolynomial) = ⊤ := by
  let S := Submodule.span ℝ (Set.range basisPolynomial)
  have hm (k n : ℕ) : X 0 ^ k * hermite n ∈ S := Submodule.subset_span ⟨(k, n), rfl⟩
  have hx (p : SpaceTimePolynomial) (hp : p ∈ S) (i : Fin 2) : p * X i ∈ S := by
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨⟨k, n⟩, rfl⟩ := hp
      change X 0 ^ k * hermite n * X i ∈ S
      fin_cases i
      · convert hm (k + 1) n using 1 <;> simp [pow_succ] <;> ring
      · cases n with
        | zero => simpa using hm k 1
        | succ n =>
          have he : X 0 ^ k * hermite (n + 1) * X 1 =
              X 0 ^ k * hermite (n + 2) +
                (n + 1 : ℝ) • (X 0 ^ (k + 1) * hermite n) := by
            rw [hermite_recursion]
            simp only [Algebra.smul_def, pow_succ]
            ring
          change X 0 ^ k * hermite (n + 1) * X 1 ∈ S
          rw [he]
          exact S.add_mem (hm k (n + 2)) (S.smul_mem _ (hm (k + 1) n))
    | zero => simpa using S.zero_mem
    | add p q hp hq ihp ihq => simpa only [add_mul] using S.add_mem ihp ihq
    | smul c p hp ih => simpa only [smul_mul_assoc] using S.smul_mem c ih
  apply top_unique
  intro p hp
  clear hp
  change p ∈ S
  induction p using MvPolynomial.induction_on with
  | C c => simpa [Algebra.smul_def] using S.smul_mem c (hm 0 0)
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact hx p hp i

end OperatorDerivativeRewrite.Foundation.GaussianPolynomialHeat
