import Foundation.PseudoFiniteGramObstruction

/-! A genuine quartic finite residue-block recovery, with an explicit failure of global duality for its finite dual. -/
noncomputable section
open Polynomial
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BiharmonicFiniteRecovery
open PseudoPolynomialStein PseudoClarkOconeObstruction

theorem pair_power (p : ℕ) (a : ℝ) (n k : ℕ) : pairing p a (X^n) (X^k)=moment p a (n+k) := by
  rw [pairing,← pow_add,expectation_X_pow]

theorem pair_smul_right (p : ℕ) (a c : ℝ) (P Q : Polynomial ℝ) :
    pairing p a P (c • Q)=c*pairing p a P Q := by
  rw [pairing,mul_smul_comm,map_smul]
  rfl

theorem pair_smul_left (p : ℕ) (a c : ℝ) (P Q : Polynomial ℝ) :
    pairing p a (c • P) Q=c*pairing p a P Q := by
  rw [pairing,smul_mul_assoc,map_smul]
  rfl

theorem pair_add_left (p : ℕ) (a : ℝ) (P Q R : Polynomial ℝ) :
    pairing p a (P+Q) R=pairing p a P R+pairing p a Q R := by
  rw [pairing,add_mul,map_add]
  rfl

theorem pair_sub_left (p : ℕ) (a : ℝ) (P Q R : Polynomial ℝ) :
    pairing p a (P-Q) R=pairing p a P R-pairing p a Q R := by
  rw [pairing,sub_mul,map_sub]
  rfl

def basis (i : Fin 4) : Polynomial ℝ := X^i.val

def complement (i : Fin 4) : ℕ := if i=0 then 0 else 4-i.val

def scale (a : ℝ) (i : Fin 4) : ℝ := if i=0 then 1 else (24*a)⁻¹

def dual (a : ℝ) (i : Fin 4) : Polynomial ℝ := scale a i • (X:Polynomial ℝ)^(complement i)

theorem basis_duality (a : ℝ) (ha : a ≠ 0) (i j : Fin 4) :
    pairing 4 a (basis i) (dual a j)=if i=j then 1 else 0 := by
  change pairing 4 a (X^i.val) (scale a j • (X:Polynomial ℝ)^(complement j))=_
  rw [pair_smul_right,pair_power]
  fin_cases i <;> fin_cases j <;>
    norm_num [scale,complement,moment] <;> field_simp [ha] <;> ring

def recover (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i : Fin 4, pairing 4 a P (dual a i) • basis i

theorem recover_add (a : ℝ) (P Q : Polynomial ℝ) : recover a (P+Q)=recover a P+recover a Q := by
  simp only [recover,pair_add_left,add_smul,Finset.sum_add_distrib]

theorem recover_smul (a c : ℝ) (P : Polynomial ℝ) : recover a (c • P)=c • recover a P := by
  simp only [recover,pair_smul_left,mul_smul,Finset.smul_sum]

def recovery (a : ℝ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun := recover a
  map_add' := recover_add a
  map_smul' c P := recover_smul a c P

theorem recover_basis (a : ℝ) (ha : a ≠ 0) (i : Fin 4) : recover a (basis i)=basis i := by
  classical
  simp only [recover,basis_duality a ha,ite_smul,one_smul,zero_smul]
  simp

theorem recover_core (a : ℝ) (ha : a ≠ 0) (c : Fin 4 → ℝ) :
    recover a (∑ i : Fin 4, c i • basis i)=∑ i : Fin 4, c i • basis i := by
  change recovery a (∑ i : Fin 4, c i • basis i)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  exact congrArg (fun P : Polynomial ℝ => c i • P) (recover_basis a ha i)

theorem recover_idempotent (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℝ) :
    recover a (recover a P)=recover a P := by
  exact recover_core a ha (fun i => pairing 4 a P (dual a i))

theorem actual_recovery_formula (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    recover (-(t:ℝ)) P=
      ∑ i : Fin 4, HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht
        (P*dual (-(t:ℝ)) i) • basis i := by
  unfold recover
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [HigherHeatPolynomialRealization.kernelExpectation_eq_moments,pairing]
  norm_num

def fifthProbe (a : ℝ) : Polynomial ℝ := X^5-(120*a) • (X:Polynomial ℝ)^1

theorem fifthProbe_mean_zero (a : ℝ) : expectation 4 a (fifthProbe a)=0 := by
  unfold fifthProbe
  rw [map_sub,map_smul,expectation_X_pow,expectation_X_pow]
  norm_num [moment]

theorem finite_dual_leakage (a : ℝ) (ha : a ≠ 0) :
    pairing 4 a (fifthProbe a) (dual a 1)=720*a := by
  change pairing 4 a ((X:Polynomial ℝ)^5-(120*a) • (X:Polynomial ℝ)^1)
    ((24*a)⁻¹ • (X:Polynomial ℝ)^3)=_
  rw [pair_smul_right,pair_sub_left,pair_smul_left,pair_power,pair_power]
  norm_num [moment]
  field_simp [ha]
  ring

theorem finite_dual_not_global (a : ℝ) (ha : a ≠ 0) : pairing 4 a (fifthProbe a) (dual a 1) ≠ 0 := by
  rw [finite_dual_leakage a ha]
  exact mul_ne_zero (by norm_num) ha

end OperatorDerivativeRewrite.Foundation.BiharmonicFiniteRecovery
