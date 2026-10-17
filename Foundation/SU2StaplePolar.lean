import Foundation.QuaternionSU2Representation

/-! A finite SU(2) staple sum has an exact quaternion polar factorization. -/
noncomputable section
open scoped Quaternion Matrix
namespace OperatorDerivativeRewrite.Foundation.SU2StaplePolar
open QuaternionSU2Representation SU2TraceHessianModel
set_option backward.isDefEq.respectTransparency false

def reprLinear : ℍ →ₗ[ℝ] M2 where
  toFun := QuaternionSU2Representation.repr
  map_add' q r := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [QuaternionSU2Representation.repr, Complex.mul_re, Complex.mul_im] <;> ring
  map_smul' r q := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [QuaternionSU2Representation.repr, Complex.mul_re, Complex.mul_im]

def direction (q : ℍ) : QuaternionAngularHaar.Group := by
  classical
  exact if h : q = 0 then 1 else
    ⟨NormedSpace.normalize q, QuaternionAngularHaar.mem_unitary_of_norm_one _
      (NormedSpace.norm_normalize h)⟩

def orientation (q : ℍ) : SU2 := hom (direction q)

theorem repr_polar (q : ℍ) :
    QuaternionSU2Representation.repr q = ‖q‖ • (orientation q : M2) := by
  classical
  by_cases h : q = 0
  · subst q
    simp only [norm_zero, zero_smul]
    change reprLinear 0 = 0
    exact map_zero reprLinear
  · have hd : (direction q : ℍ) = NormedSpace.normalize q := by
      simp only [direction, dite_eq_right h]
    change reprLinear q = ‖q‖ • reprLinear (direction q : ℍ)
    rw [hd, ← map_smul, NormedSpace.norm_smul_normalize]

variable {ι : Type*}

def quaternionSum (s : Finset ι) (U : ι → SU2) : ℍ :=
  ∑ i ∈ s, recover (U i : M2)

def staple (s : Finset ι) (U : ι → SU2) : M2 := ∑ i ∈ s, (U i : M2)

theorem repr_sum (s : Finset ι) (U : ι → SU2) :
    QuaternionSU2Representation.repr (quaternionSum s U) = staple s U := by
  change reprLinear (∑ i ∈ s, recover (U i : M2)) = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact repr_recover _ (U i).property

theorem staple_polar (s : Finset ι) (U : ι → SU2) :
    staple s U = ‖quaternionSum s U‖ • (orientation (quaternionSum s U) : M2) := by
  rw [← repr_sum]
  exact repr_polar _

theorem radius_bound (s : Finset ι) (U : ι → SU2) :
    ‖quaternionSum s U‖ ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ i ∈ s, ‖recover (U i : M2)‖ := norm_sum_le _ _
    _ = (s.card : ℝ) := by
      have h (i : ι) : ‖recover (U i : M2)‖ = 1 :=
        CStarRing.norm_of_mem_unitary (recover_mem (U i))
      simp only [h, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem staple_zero_iff (s : Finset ι) (U : ι → SU2) :
    staple s U = 0 ↔ quaternionSum s U = 0 := by
  rw [← repr_sum]
  have hz : QuaternionSU2Representation.repr 0 = 0 := map_zero reprLinear
  exact ⟨fun h => repr_injective (h.trans hz.symm), fun h => h ▸ hz⟩

theorem staple_star_mul (s : Finset ι) (U : ι → SU2) :
    (staple s U)ᴴ * staple s U =
      ((‖quaternionSum s U‖^2 : ℝ) : ℂ) • (1 : M2) := by
  rw [← repr_sum, ← repr_star, ← repr_mul, Quaternion.star_mul_self, repr_real,
    Quaternion.normSq_eq_norm_mul_self, pow_two]

theorem trace_tilt (s : Finset ι) (U : ι → SU2) (A : SU2) :
    traceReal ((A : M2) * staple s U) / 2 =
      ‖quaternionSum s U‖ * halfTrace (orientation (quaternionSum s U) * A) := by
  rw [staple_polar, Matrix.mul_smul]
  have ht (r : ℝ) (M : M2) : traceReal (r • M) = r * traceReal M := by
    simp [traceReal, Matrix.trace_smul]
  rw [ht]
  have hc : traceReal ((A : M2) * (orientation (quaternionSum s U) : M2)) =
      traceReal ((orientation (quaternionSum s U) : M2) * (A : M2)) := by
    unfold traceReal
    rw [Matrix.trace_mul_comm]
  rw [hc]
  change _ = ‖quaternionSum s U‖ *
    (traceReal ((orientation (quaternionSum s U) : M2) * (A : M2)) / 2)
  ring

end OperatorDerivativeRewrite.Foundation.SU2StaplePolar
