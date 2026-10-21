import Foundation.NilpotentVectorEuler
import Foundation.FactorialAnalyticHeat

/-! Finite even-derivative corrections on the existing factorial jet space.
Their Euler powers converge in jet norm to the verified order-two transport on
EVERY finite real polynomial. The actual symmetric-shift identification and its
complex local-uniform limit remain separate obligations. Xi is not asserted to
belong to this bounded jet domain. -/
noncomputable section
open Polynomial Filter Finset
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PolynomialDerivativeEuler
open FactorialAnalyticDomain

def correction (N : ℕ) (s : ℝ) (n : ℕ) : H →L[ℝ] H :=
  ∑ j∈range (N+1),
    (((-1:ℝ)^(j+1)*(2*s)^(j+1)/((2*j+2).factorial:ℝ)) *
      (1/((n+1:ℕ):ℝ))^j) • shift^(2*j+2)

theorem correction_apply (N : ℕ) (s : ℝ) (n : ℕ) (u : H) (k : ℕ) :
    correction N s n u k=∑ j∈range (N+1),
      (((-1:ℝ)^(j+1)*(2*s)^(j+1)/((2*j+2).factorial:ℝ)) *
        (1/((n+1:ℕ):ℝ))^j)*u (k+(2*j+2)) := by
  simp only [correction,_root_.sum_apply,_root_.smul_apply,
    lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,shift_pow_apply]

theorem correction_limit (N : ℕ) (s : ℝ) :
    Tendsto (correction N s) atTop (𝓝 ((-s) • shift^2)) := by
  have hpow (j : ℕ) : Tendsto
      (fun n : ℕ => (((-1:ℝ)^(j+1)*(2*s)^(j+1)/((2*j+2).factorial:ℝ))*
        (1/((n+1:ℕ):ℝ))^j) • shift^(2*j+2))
      atTop (𝓝 (if j=0 then (-s) • shift^2 else 0)) := by
    by_cases hj : j=0
    · subst j
      simp only [pow_one,Nat.mul_zero,zero_add,Nat.factorial_two,Nat.cast_ofNat,
        pow_zero,mul_one,ite_true]
      have hc : (-1:ℝ)*(2*s)/2= -s := by ring
      rw [hc]
      exact tendsto_const_nhds
    · have hbase : Tendsto (fun n : ℕ => 1/((n+1:ℕ):ℝ)) atTop (𝓝 (0:ℝ)) :=
        (tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 (0:ℝ))).comp (tendsto_add_atTop_nat 1)
      have hz : Tendsto (fun n : ℕ => (1/((n+1:ℕ):ℝ))^j) atTop (𝓝 (0:ℝ)) := by
        have he := hbase.pow j
        rw [zero_pow hj] at he
        exact he
      have he : Tendsto
          (fun n : ℕ => (((-1:ℝ)^(j+1)*(2*s)^(j+1)/((2*j+2).factorial:ℝ)) *
            (1/((n+1:ℕ):ℝ))^j) • (shift^(2*j+2):H →L[ℝ] H))
          atTop (𝓝 ((0:ℝ) • (shift^(2*j+2):H →L[ℝ] H))) := by
        have ha : Tendsto
            (fun n : ℕ => ((-1:ℝ)^(j+1)*(2*s)^(j+1)/((2*j+2).factorial:ℝ)) *
              (1/((n+1:ℕ):ℝ))^j) atTop (𝓝 (0:ℝ)) := by
          simpa only [mul_zero] using hz.const_mul
            (((-1:ℝ)^(j+1)*(2*s)^(j+1)/((2*j+2).factorial:ℝ)))
        exact ha.smul_const (shift^(2*j+2):H →L[ℝ] H)
      have he0 : (0:ℝ) • (shift^(2*j+2):H →L[ℝ] H)=(0:H →L[ℝ] H)  := by
        ext u k
        change (0:ℝ)*((shift^(2*j+2)) u k)=0
        exact zero_mul _
      rw [he0] at he
      simp only [ite_eq_right hj]
      exact he
  have he := tendsto_finsetSum (s:=range (N+1)) (fun j hj => hpow j)
  have hr := he
  simp only [sum_ite_eq',mem_range,Nat.zero_lt_succ,ite_true] at hr
  exact hr

theorem correction_power_support (N : ℕ) (s : ℝ) (n M r : ℕ) (u : H)
    (hu : ∀ k : ℕ,M≤k → u k=0) (k : ℕ) (hk : M≤k+2*r) :
    (correction N s n^r) u k=0 := by
  induction r generalizing k with
  | zero => simpa using hu k (by simpa using hk)
  | succ r ih =>
    rw [pow_succ']
    change correction N s n ((correction N s n^r) u) k=0
    rw [correction_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [ih (k+(2*j+2)) (by omega),mul_zero]

theorem correction_power_polynomial_zero (N : ℕ) (s : ℝ) (n : ℕ) (P : ℝ[X]) :
    (correction N s n^(P.natDegree+1)) (polynomial P)=0 := by
  ext k
  apply correction_power_support N s n (P.natDegree+1) (P.natDegree+1) (polynomial P)
  · intro j hj
    simp only [polynomial_apply,Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree<j),mul_zero]
  · omega

theorem correction_euler_polynomial_limit (N : ℕ) (s : ℝ) (P : ℝ[X]) :
    Tendsto (fun n : ℕ =>
      ((1+(1/((n+1:ℕ):ℝ)) • correction N s n)^(n+1)) (polynomial P))
      atTop (𝓝 (polynomial (PureOrderPolynomialTransport.transport 2 (-s) P))) := by
  have he := NilpotentVectorEuler.nilpotent_vector_euler_limit (correction N s)
    ((-s) • shift^2) (polynomial P) (P.natDegree+1) (correction_limit N s)
    (fun n => correction_power_polynomial_zero N s n P)
  change Tendsto _ atTop (𝓝 (FactorialAnalyticHeat.evolution 2 (-s) (polynomial P))) at he
  rw [FactorialAnalyticHeat.evolution_polynomial 2 (by norm_num)] at he
  exact he

end OperatorDerivativeRewrite.Foundation.PolynomialDerivativeEuler
