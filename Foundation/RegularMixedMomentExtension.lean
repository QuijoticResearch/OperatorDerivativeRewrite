import Foundation.RegularMixedMomentRealization
import Foundation.MixedCubicThirdDegree
import Foundation.TruncatedPolynomialIntegration

/-! Actual finite spectral laws above the regular sixth-moment floor. -/
noncomputable section
open MeasureTheory Polynomial Matrix
namespace OperatorDerivativeRewrite.Foundation.RegularMixedMomentExtension
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def prefixChain (r b s d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0,r,0; r,b,s; 0,s,d]
def chain (r b s d e : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,r,0,0; r,b,s,0; 0,s,d,e; 0,0,e,0]

theorem chain_prefix (r b s d e : ℝ) (n : ℕ) (hn : n ≤ 5) :
    ((chain r b s d e)^n) 0 0 = ((prefixChain r b s d)^n) 0 0 := by
  interval_cases n <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, chain,prefixChain,Matrix.one_apply] <;> ring

theorem chain_sixth (r b s d e : ℝ) :
    ((chain r b s d e)^6) 0 0 = ((prefixChain r b s d)^6) 0 0+r^2*s^2*e^2 := by
  norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, chain,prefixChain,Matrix.one_apply]
  ring

def coupling (v k t m : ℝ) : ℝ := Real.sqrt ((m-RegularMixedMomentRealization.floor v k t)*v/RegularMixedMomentRealization.delta v k)
def jacobi (v k t m : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  chain (Real.sqrt v) (k/v) (Real.sqrt (RegularMixedMomentRealization.delta v k)/v) (RegularMixedMomentRealization.tailDiagonal v k t)
    (coupling v k t m)

theorem jacobi_hermitian (v k t m : ℝ) : (jacobi v k t m).IsHermitian := by
  change (jacobi v k t m).conjTranspose = jacobi v k t m
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobi,chain,Matrix.conjTranspose_apply]

def law (v k t m : ℝ) : Measure ℝ :=
  FiniteMatrixSpectralMeasure.law (jacobi_hermitian v k t m) 0

instance law_probability (v k t m : ℝ) : IsProbabilityMeasure (law v k t m) :=
  FiniteMatrixSpectralMeasure.law_probability _ _

theorem law_integrable (v k t m : ℝ) (f : ℝ → ℝ) : Integrable f (law v k t m) :=
  FiniteMatrixSpectralMeasure.law_integrable _ _ _

theorem law_moment (v k t m : ℝ) (n : ℕ) :
    (∫ x : ℝ, x^n ∂law v k t m) = ((jacobi v k t m)^n) 0 0 :=
  FiniteMatrixSpectralMeasure.law_moment _ _ _

theorem law_prefix (v k t m : ℝ) (n : ℕ) (hn : n ≤ 5) :
    (∫ x : ℝ, x^n ∂law v k t m) = ∫ x : ℝ, x^n ∂RegularMixedMomentRealization.extremalLaw v k t := by
  rw [law_moment,RegularMixedMomentRealization.extremalLaw_moment]
  exact chain_prefix _ _ _ _ _ n hn

theorem law_sixth (v k t m : ℝ) (hv : 0 < v) (hd : 0 < RegularMixedMomentRealization.delta v k)
    (hm : RegularMixedMomentRealization.floor v k t ≤ m) : (∫ x : ℝ, x^6 ∂law v k t m) = m := by
  have he : (coupling v k t m)^2 = (m-RegularMixedMomentRealization.floor v k t)*v/RegularMixedMomentRealization.delta v k :=
    Real.sq_sqrt (div_nonneg (mul_nonneg (sub_nonneg.mpr hm) hv.le) hd.le)
  have hs := Real.sq_sqrt hd.le
  have hr := Real.sq_sqrt hv.le
  have hbase := (RegularMixedMomentRealization.extremalLaw_first_seven v k t hv hd).2.2.2.2.2.2
  rw [RegularMixedMomentRealization.extremalLaw_moment] at hbase
  rw [law_moment]
  change ((chain _ _ _ _ _)^6) 0 0 = _
  rw [chain_sixth]
  change ((RegularMixedMomentRealization.jacobi v k t)^6) 0 0 + _ = _
  rw [hbase,div_pow,hr,hs,he]
  field_simp [hv.ne',hd.ne']
  ring

theorem law_first_seven (v k t m : ℝ) (hv : 0 < v) (hd : 0 < RegularMixedMomentRealization.delta v k)
    (hm : RegularMixedMomentRealization.floor v k t ≤ m) :
    (∫ x : ℝ, x^0 ∂law v k t m) = 1 ∧
    (∫ x : ℝ, x^1 ∂law v k t m) = 0 ∧
    (∫ x : ℝ, x^2 ∂law v k t m) = v ∧
    (∫ x : ℝ, x^3 ∂law v k t m) = k ∧
    (∫ x : ℝ, x^4 ∂law v k t m) = 3*v^2 ∧
    (∫ x : ℝ, x^5 ∂law v k t m) = t ∧
    (∫ x : ℝ, x^6 ∂law v k t m) = m := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := RegularMixedMomentRealization.extremalLaw_first_seven v k t hv hd
  exact ⟨(law_prefix v k t m 0 (by norm_num)).trans h0,
    (law_prefix v k t m 1 (by norm_num)).trans h1,
    (law_prefix v k t m 2 (by norm_num)).trans h2,
    (law_prefix v k t m 3 (by norm_num)).trans h3,
    (law_prefix v k t m 4 (by norm_num)).trans h4,
    (law_prefix v k t m 5 (by norm_num)).trans h5,law_sixth v k t m hv hd hm⟩

def RepresentsSix (μ : Measure ℝ) (v k : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ n ≤ 6, Integrable (fun x : ℝ => x^n) μ) ∧
    ∀ n ≤ 6, (∫ x : ℝ, x^n ∂μ) = MixedCubicMomentPositivity.moment v k n

theorem regular_mixed_realization (v k : ℝ) (hv : 0 < v) (hD : 0 ≤ MixedCubicThirdDegree.determinant v k) :
    RepresentsSix (law v k (10*v*k) (15*v^3+10*k^2)) v k := by
  have hd : 0 < RegularMixedMomentRealization.delta v k := MixedCubicThirdDegree.determinant_nonneg_delta_pos v k hv hD
  have hgap := RegularMixedMomentRealization.mixed_sixth_gap v k hd.ne'
  have hm : RegularMixedMomentRealization.floor v k (10*v*k) ≤ 15*v^3+10*k^2 := by
    have hn : 0 ≤ MixedCubicThirdDegree.determinant v k/RegularMixedMomentRealization.delta v k := div_nonneg hD hd.le
    change 0 ≤ (12*v^6-24*v^3*k^2-9*k^4)/RegularMixedMomentRealization.delta v k at hn
    linarith
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := law_first_seven v k (10*v*k) (15*v^3+10*k^2) hv hd hm
  refine ⟨inferInstance,fun n _ => law_integrable _ _ _ _ _,fun n hn => ?_⟩
  interval_cases n <;> norm_num [MixedCubicMomentPositivity.moment] at * <;> first | assumption | nlinarith only [h4,h5,h6]

theorem representation_cubic_positive (μ : Measure ℝ) (v k : ℝ) (hμ : RepresentsSix μ v k) :
    ∀ g : Polynomial ℝ, g.natDegree ≤ 3 →
      0 ≤ MixedCubicMomentPositivity.expectation v k (g^2) := by
  rcases hμ with ⟨hprob,hi,hm⟩
  intro g hg
  have hg2 : (g^2).natDegree ≤ 6 :=
    natDegree_pow_le.trans (by omega : 2*g.natDegree ≤ 6)
  have hmatch : ∀ n ≤ 6, (∫ x : ℝ, x^n ∂μ) =
      MixedCubicMomentPositivity.expectation v k (X^n) := by
    intro n hn
    rw [MixedCubicMomentPositivity.expectation_X_pow]
    exact hm n hn
  have he := (TruncatedPolynomialIntegration.polynomial_integral_match μ
    (MixedCubicMomentPositivity.expectation v k) 6 hi hmatch (g^2) hg2).2
  rw [← he]
  apply integral_nonneg
  intro x
  simpa only [eval_pow, Pi.zero_apply] using sq_nonneg (g.eval x)

theorem zero_representation : RepresentsSix (Measure.dirac (0 : ℝ)) 0 0 := by
  refine ⟨inferInstance,fun n _ => integrable_dirac (by finiteness),fun n _ => ?_⟩
  cases n with
  | zero => simp [MixedCubicMomentPositivity.moment]
  | succ n => simp [MixedCubicMomentPositivity.moment]

theorem mixed_six_realizable_iff (v k : ℝ) :
    (∃ μ : Measure ℝ, RepresentsSix μ v k) ↔
      0 ≤ v ∧ 0 ≤ MixedCubicThirdDegree.determinant v k := by
  constructor
  · rintro ⟨μ,hμ⟩
    exact (MixedCubicThirdDegree.cubic_positivity_all_parameters_iff v k).mp
      (representation_cubic_positive μ v k hμ)
  · rintro ⟨hv,hD⟩
    by_cases hz : v = 0
    · have hk : k = 0 := by
        by_contra hk
        have hp : 0 < (k^2)^2 := pow_pos (sq_pos_of_ne_zero hk) 2
        simp only [MixedCubicThirdDegree.determinant,hz,zero_pow (by norm_num : 6 ≠ 0),
          zero_pow (by norm_num : 3 ≠ 0),mul_zero,zero_mul,zero_sub] at hD
        nlinarith
      subst v
      subst k
      exact ⟨Measure.dirac 0,zero_representation⟩
    · have hv' : 0 < v := lt_of_le_of_ne hv (Ne.symm hz)
      exact ⟨law v k (10*v*k) (15*v^3+10*k^2),regular_mixed_realization v k hv' hD⟩

theorem mixed_six_realizable_iff_cubic_positive (v k : ℝ) :
    (∃ μ : Measure ℝ, RepresentsSix μ v k) ↔
      ∀ g : Polynomial ℝ, g.natDegree ≤ 3 →
        0 ≤ MixedCubicMomentPositivity.expectation v k (g^2) := by
  rw [mixed_six_realizable_iff,MixedCubicThirdDegree.cubic_positivity_all_parameters_iff]

end OperatorDerivativeRewrite.Foundation.RegularMixedMomentExtension
