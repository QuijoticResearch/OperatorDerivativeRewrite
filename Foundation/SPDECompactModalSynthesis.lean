import Foundation.SPDEExponentialForcing
import Foundation.PoissonRecoveryCompactness
import Mathlib.Analysis.Normed.Lp.lpHolder

/-! Compact deterministic modal synthesis need not admit unit-amplitude Gaussian forcing. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDECompactModalSynthesis
open InfiniteGaussian GaussianTimeHilbert SPDECountableModes SPDEExponentialForcing
attribute [local instance] timeHilbert_secondCountable

def column (v : TimeHilbert) : ℝ →L[ℝ] TimeHilbert :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight v

theorem column_norm (v : TimeHilbert) : ‖column v‖=‖v‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
    intro x
    simp [column,norm_smul,mul_comm]
  · have h := (column v).le_opNorm (1 : ℝ)
    simpa [column] using h

def synthesis (v : ℕ → TimeHilbert) (M : ℝ) (hM : 0≤M) (hv : ∀ n,‖v n‖≤M) :
    CoefficientSpace →L[ℝ] GaussianL2 :=
  gaussianModes_orthogonal.linearIsometry.toContinuousLinearMap.comp
    (lp.mapCLM 2 (fun n => column (v n)) hM (fun n => (column_norm _).le.trans (hv n)))

theorem synthesis_apply (v : ℕ → TimeHilbert) (M : ℝ) (hM : 0≤M)
    (hv : ∀ n,‖v n‖≤M) (c : CoefficientSpace) :
    synthesis v M hM hv c=infiniteResponse c v := by
  change (∑' n,gaussianMode n ((lp.mapCLM 2 (fun n => column (v n)) hM _) c n))=_
  change (∑' n,gaussianMode n (c n • v n))=infiniteResponse c v
  simp only [map_smul,infiniteResponse]

theorem synthesis_norm (v : ℕ → TimeHilbert) (M : ℝ) (hM : 0≤M)
    (hv : ∀ n,‖v n‖≤M) : ‖synthesis v M hM hv‖≤M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro c
  change ‖gaussianModes_orthogonal.linearIsometry ((lp.mapCLM 2 (fun n => column (v n)) hM _) c)‖≤_
  rw [LinearIsometry.norm_map]
  exact ContinuousLinearMap.le_of_opNorm_le _ (lp.norm_mapCLM_le _ _ hM _) c

theorem synthesis_single (v : ℕ → TimeHilbert) (M : ℝ) (hM : 0≤M)
    (hv : ∀ n,‖v n‖≤M) (n : ℕ) :
    synthesis v M hM hv (lp.single 2 n (1 : ℝ))=gaussianMode n (v n) := by
  rw [synthesis_apply,infiniteResponse]
  rw [tsum_eq_single n]
  · simp
  · intro k hk
    simp [lp.single_apply,hk,Ne.symm hk]

def partialSynthesis (v : ℕ → TimeHilbert) (N : ℕ) : CoefficientSpace →L[ℝ] GaussianL2 :=
  ∑ n∈Finset.range N, (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).smulRight (gaussianMode n (v n))

theorem partialSynthesis_apply (v : ℕ → TimeHilbert) (N : ℕ) (c : CoefficientSpace) :
    partialSynthesis v N c=∑ n∈Finset.range N,c n • gaussianMode n (v n) := by
  simp [partialSynthesis,lp.evalCLM,lp.evalₗ]

theorem partialSynthesis_compact (v : ℕ → TimeHilbert) (N : ℕ) :
    IsCompactOperator (partialSynthesis v N) := by
  have hterm (n : ℕ) : IsCompactOperator
      ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).smulRight (gaussianMode n (v n))) := by
    exact (isCompactOperator_of_locallyCompactSpace_rng
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (gaussianMode n (v n)))).comp_clm (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n)
  unfold partialSynthesis
  induction Finset.range N using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact isCompactOperator_zero
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      exact (hterm n).add ih

theorem synthesis_tail_bound (v : ℕ → TimeHilbert) (M : ℝ) (hM : 0≤M)
    (hv : ∀ n,‖v n‖≤M) (N : ℕ) (C : ℝ) (hC : 0≤C)
    (htail : ∀ n,N≤n → ‖v n‖≤C) :
    ‖synthesis v M hM hv-partialSynthesis v N‖≤C := by
  let w : ℕ → TimeHilbert := fun n => if n<N then 0 else v n
  have hw (n : ℕ) : ‖w n‖≤C := by
    by_cases hn : n<N
    · simpa [w,hn] using hC
    · simpa [w,hn] using htail n (by omega)
  have he : synthesis v M hM hv-partialSynthesis v N=synthesis w C hC hw := by
    apply ContinuousLinearMap.ext
    intro c
    rw [ContinuousLinearMap.sub_apply,synthesis_apply,synthesis_apply,partialSynthesis_apply]
    have hp : HasSum (fun n => if n∈Finset.range N then c n • gaussianMode n (v n) else 0)
        (∑ n∈Finset.range N,c n • gaussianMode n (v n)) := by
      simpa only [Finset.sum_ite_mem,Finset.inter_self] using
        (hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := Finset.range N)
          (f := fun n => if n∈Finset.range N then c n • gaussianMode n (v n) else 0) (fun n hn => by simp [hn]))
    have hs := gaussianModes_orthogonal.hasSum_linearIsometry
      ((lp.mapCLM 2 (fun n => column (v n)) hM (fun n => (column_norm _).le.trans (hv n))) c)
    have hs' : HasSum (fun n => c n • gaussianMode n (v n)) (infiniteResponse c v) := by
      change HasSum (fun n => gaussianMode n (c n • v n))
        (∑' n,gaussianMode n (c n • v n)) at hs
      simpa only [map_smul,infiniteResponse] using hs
    have hs'' := hs'.sub hp
    have heq (n : ℕ) : c n • gaussianMode n (v n)-
        (if n∈Finset.range N then c n • gaussianMode n (v n) else 0)=c n • gaussianMode n (w n) := by
      by_cases hn : n<N <;> simp [w,Finset.mem_range,hn]
    exact (by simpa only [heq,infiniteResponse] using hs''.tsum_eq.symm)
  rw [he]
  exact synthesis_norm w C hC hw

theorem synthesis_compact (v : ℕ → TimeHilbert) (M : ℝ) (hM : 0≤M)
    (hv : ∀ n,‖v n‖≤M) (C : ℕ → ℝ) (hC : ∀ N,0≤C N)
    (htail : ∀ N n,N≤n → ‖v n‖≤C N) (hlim : Tendsto C atTop (𝓝 0)) :
    IsCompactOperator (synthesis v M hM hv) := by
  have ht : Tendsto (partialSynthesis v) atTop (𝓝 (synthesis v M hM hv)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
    intro N
    rw [norm_sub_rev]
    exact synthesis_tail_bound v M hM hv N (C N) (hC N) (htail N)
  exact isCompactOperator_of_tendsto ht (Eventually.of_forall (partialSynthesis_compact v))

def modalTail (N : ℕ) : ℝ := Real.sqrt ((N+1 : ℝ)⁻¹)

theorem linear_profile_tail (t : ℝ≥0) (N n : ℕ) (hn : N≤n) :
    ‖responseVector (linearRates n) t‖≤modalTail N := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  change ‖responseVector (linearRates n) t‖^2≤(Real.sqrt ((N+1 : ℝ)⁻¹))^2
  rw [Real.sq_sqrt (by positivity)]
  have hr : 0<linearRates n := by simp [linearRates]
  have hu := responseVector_energy_upper (linearRates n) t hr
  apply hu.trans
  rw [one_div]
  apply inv_anti₀ (by positivity)
  change (N : ℝ)+1≤2*((n : ℝ)+1)
  have hn' : (N : ℝ)≤n := by exact_mod_cast hn
  linarith [Nat.cast_nonneg n (α := ℝ)]

theorem modalTail_tendsto : Tendsto modalTail atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N+1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun N : ℕ => Real.sqrt ((N+1 : ℝ)⁻¹)) atTop (𝓝 0)
  simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_inv_atTop_zero.comp hn)

theorem linear_profile_bound (t : ℝ≥0) (n : ℕ) : ‖responseVector (linearRates n) t‖≤1 := by
  simpa [modalTail] using linear_profile_tail t 0 n (Nat.zero_le n)

def linearSynthesis (t : ℝ≥0) : CoefficientSpace →L[ℝ] GaussianL2 :=
  synthesis (fun n => responseVector (linearRates n) t) 1 zero_le_one (linear_profile_bound t)

theorem linearSynthesis_compact (t : ℝ≥0) : IsCompactOperator (linearSynthesis t) :=
  synthesis_compact _ _ _ _ modalTail (fun _ => Real.sqrt_nonneg _) (linear_profile_tail t) modalTail_tendsto

theorem linearSynthesis_single (t : ℝ≥0) (n : ℕ) :
    linearSynthesis t (lp.single 2 n (1 : ℝ))=gaussianMode n (responseVector (linearRates n) t) :=
  synthesis_single _ _ _ _ n

theorem linearSynthesis_infinite_trace (t : ℝ≥0) (ht : 0<t) :
    ¬ Summable (fun n => ‖linearSynthesis t (lp.single 2 n (1 : ℝ))‖^2) := by
  simp only [linearSynthesis_single,LinearIsometry.norm_map]
  intro hs
  apply linear_forcing_not_summable t ht
  apply (gaussianSeries_summable_iff (fun _ => (1 : ℝ)) _).mpr
    (by simpa only [one_pow,one_mul] using hs) |>.congr
  intro n
  simp

theorem compact_does_not_imply_stochastic_trace : ∃ T : CoefficientSpace →L[ℝ] GaussianL2,
    IsCompactOperator T ∧ ¬ Summable (fun n => ‖T (lp.single 2 n (1 : ℝ))‖^2) :=
  ⟨linearSynthesis 1,linearSynthesis_compact 1,linearSynthesis_infinite_trace 1 (by norm_num)⟩

end OperatorDerivativeRewrite.Foundation.SPDECompactModalSynthesis




