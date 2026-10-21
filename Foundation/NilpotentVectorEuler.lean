import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

/-! A finite-vector Euler limit using existing Banach exponential and binomial
asymptotics. A common power annihilates the specified vector; the operators need
not be globally nilpotent. This is intended for finite polynomial derivatives,
not an assertion that the Xi function belongs to a bounded jet domain. -/
noncomputable section
open Filter Finset
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.NilpotentVectorEuler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pow_apply_zero_of_le (A : E →L[ℝ] E) (v : E) (D j : ℕ)
    (hD : (A^D) v=0) (hj : D≤j) : (A^j) v=0 := by
  have he : j=(j-D)+D := by omega
  rw [he,pow_add]
  change (A^(j-D)) ((A^D) v)=0
  rw [hD,map_zero]

theorem binomial_apply (A : E →L[ℝ] E) (v : E) (r : ℝ) (n : ℕ) :
    ((1+r • A)^n) v=∑ j∈range (n+1),((n.choose j:ℝ)*r^j) • ((A^j) v) := by
  have he := (Commute.one_right (r • A)).add_pow n
  rw [add_comm 1 (r • A),he,_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_pow]
  simp [mul_comm]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]

theorem binomial_apply_truncate (A : E →L[ℝ] E) (v : E) (r : ℝ) (D n : ℕ)
    (hD : (A^D) v=0) (hn : D≤n+1) :
    ((1+r • A)^n) v=∑ j∈range D,((n.choose j:ℝ)*r^j) • ((A^j) v) := by
  rw [binomial_apply]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro j hj hjD
  have hle : D≤j := by simpa only [mem_range,not_lt] using hjD
  rw [pow_apply_zero_of_le A v D j hD hle,smul_zero]

theorem binomial_coefficient_limit (j : ℕ) :
    Tendsto (fun n : ℕ => ((n+1).choose j:ℝ)*(1/((n+1:ℕ):ℝ))^j)
      atTop (𝓝 (1/(j.factorial:ℝ))) := by
  have hr : Tendsto (fun n : ℕ => (n:ℝ)*(1/(n:ℝ))) atTop (𝓝 (1:ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hne : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
    field_simp
  simpa only [Function.comp_def,one_pow] using
    (ProbabilityTheory.tendsto_choose_mul_pow_atTop j hr).comp (tendsto_add_atTop_nat 1)

theorem finite_euler_limit (A : ℕ → E →L[ℝ] E) (B : E →L[ℝ] E) (v : E) (D : ℕ)
    (hA : Tendsto A atTop (𝓝 B)) (hD : ∀ n : ℕ,(A n^D) v=0) :
    Tendsto (fun n : ℕ => ((1+(1/((n+1:ℕ):ℝ)) • A n)^(n+1)) v)
      atTop (𝓝 (∑ j∈range D,(1/(j.factorial:ℝ)) • ((B^j) v))) := by
  have hs : Tendsto
      (fun n : ℕ => ∑ j∈range D,(((n+1).choose j:ℝ)*(1/((n+1:ℕ):ℝ))^j) • ((A n^j) v))
      atTop (𝓝 (∑ j∈range D,(1/(j.factorial:ℝ)) • ((B^j) v))) := by
    apply tendsto_finsetSum
    intro j hj
    exact (binomial_coefficient_limit j).smul (((ContinuousLinearMap.apply ℝ E v).continuous.tendsto (B^j)).comp (hA.pow j))
  apply hs.congr'
  filter_upwards [eventually_ge_atTop D] with n hn
  exact (binomial_apply_truncate (A n) v (1/((n+1:ℕ):ℝ)) D (n+1) (hD n) (by omega)).symm

variable [CompleteSpace E]

theorem exp_apply_finite (B : E →L[ℝ] E) (v : E) (D : ℕ) (hD : (B^D) v=0) :
    (NormedSpace.exp B) v=∑ j∈range D,(1/(j.factorial:ℝ)) • ((B^j) v) := by
  have hs := (ContinuousLinearMap.apply ℝ E v).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) B)
  change HasSum (fun j : ℕ => (j.factorial:ℝ)⁻¹ • ((B^j) v)) ((NormedSpace.exp B) v) at hs
  rw [← hs.tsum_eq]
  simpa only [one_div] using tsum_eq_sum (s:=range D) (fun j hj => by
    rw [pow_apply_zero_of_le B v D j hD (by simpa only [mem_range,not_lt] using hj),smul_zero])

theorem nilpotent_vector_euler_limit (A : ℕ → E →L[ℝ] E) (B : E →L[ℝ] E) (v : E) (D : ℕ)
    (hA : Tendsto A atTop (𝓝 B)) (hD : ∀ n : ℕ,(A n^D) v=0) :
    Tendsto (fun n : ℕ => ((1+(1/((n+1:ℕ):ℝ)) • A n)^(n+1)) v)
      atTop (𝓝 ((NormedSpace.exp B) v)) := by
  have hdlim := ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto (B^D)).comp (hA.pow D)
  have hzlim : Tendsto (fun n : ℕ => (A n^D) v) atTop (𝓝 (0:E)) := by
    simpa only [hD] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:E)) atTop (𝓝 0))
  have hB : (B^D) v=0 := tendsto_nhds_unique hdlim hzlim
  rw [exp_apply_finite B v D hB]
  exact finite_euler_limit A B v D hA hD

end OperatorDerivativeRewrite.Foundation.NilpotentVectorEuler
