import Foundation.MixedCubicFourthDegree
import Foundation.TridiagonalMomentIntertwining

/-! Actual spectral probability realization of the mixed moments through degree eight. -/
noncomputable section
open MeasureTheory Polynomial Matrix
namespace OperatorDerivativeRewrite.Foundation.MixedCubicEighthRealization
open MixedCubicMomentPositivity MixedCubicThirdDegree MixedCubicFourthDegree
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000

def diagonalTwo (v k : ℝ) : ℝ := k*(4*v^3+k^2)/(v*delta v k)
def diagonalThree (v k : ℝ) : ℝ :=
  72*v^2*k*(v^3-k^2)/determinant v k-6*v^2*k/delta v k

def jacobi (v k : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  TridiagonalMomentIntertwining.symmetric (k/v) (diagonalTwo v k) (diagonalThree v k) 0
    (Real.sqrt v) (Real.sqrt (delta v k)/v)
    (Real.sqrt (v*determinant v k)/delta v k)
    (Real.sqrt (delta v k*fourthDeterminant v k)/determinant v k)

def monicJacobi (v k : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  TridiagonalMomentIntertwining.monic (k/v) (diagonalTwo v k) (diagonalThree v k) 0
    v (delta v k/v^2) (v*determinant v k/(delta v k)^2)
    (delta v k*fourthDeterminant v k/(determinant v k)^2)

theorem jacobi_hermitian (v k : ℝ) : (jacobi v k).IsHermitian := by
  change (jacobi v k).conjTranspose = jacobi v k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacobi,TridiagonalMomentIntertwining.symmetric,Matrix.conjTranspose_apply]

theorem power_monic (v k : ℝ) (hv : 0 < v) (h4 : 0 ≤ fourthDeterminant v k) (n : ℕ) :
    ((jacobi v k)^n) 0 0 = ((monicJacobi v k)^n) 0 0 := by
  have hD := fourth_nonneg_cubic_pos v k hv h4
  have hd := determinant_nonneg_delta_pos v k hv hD.le
  have hr := Real.sq_sqrt hv.le
  have hs := Real.sq_sqrt hd.le
  have he := Real.sq_sqrt (mul_pos hv hD).le
  have hh := Real.sq_sqrt (mul_nonneg hd.le h4)
  simpa only [jacobi,monicJacobi,div_pow,hr,hs,he,hh] using
    TridiagonalMomentIntertwining.coordinate_moment (k/v) (diagonalTwo v k)
      (diagonalThree v k) 0 (Real.sqrt v) (Real.sqrt (delta v k)/v)
      (Real.sqrt (v*determinant v k)/delta v k)
      (Real.sqrt (delta v k*fourthDeterminant v k)/determinant v k) n

theorem monic_moments (v k : ℝ) (hv : 0 < v) (hd : 0 < delta v k)
    (hD : 0 < determinant v k) (n : ℕ) (hn : n ≤ 8) :
    ((monicJacobi v k)^n) 0 0 = moment v k n := by
  interval_cases n <;>
    norm_num [pow_succ,Matrix.mul_apply,Fin.sum_univ_succ,monicJacobi,
      TridiagonalMomentIntertwining.monic,Matrix.one_apply,moment] <;>
    (try dsimp [diagonalTwo,diagonalThree]) <;>
    (try field_simp [hv.ne',hd.ne',hD.ne']) <;>
    (try simp only [delta,determinant,fourthDeterminant]) <;> ring_nf <;> simp

def law (v k : ℝ) : Measure ℝ :=
  FiniteMatrixSpectralMeasure.law (jacobi_hermitian v k) 0

instance law_probability (v k : ℝ) : IsProbabilityMeasure (law v k) :=
  FiniteMatrixSpectralMeasure.law_probability _ _

theorem law_integrable (v k : ℝ) (f : ℝ → ℝ) : Integrable f (law v k) :=
  FiniteMatrixSpectralMeasure.law_integrable _ _ _

theorem law_moment (v k : ℝ) (n : ℕ) :
    (∫ x : ℝ, x^n ∂law v k) = ((jacobi v k)^n) 0 0 :=
  FiniteMatrixSpectralMeasure.law_moment _ _ _

theorem law_matches (v k : ℝ) (hv : 0 < v) (h4 : 0 ≤ fourthDeterminant v k)
    (n : ℕ) (hn : n ≤ 8) : (∫ x : ℝ, x^n ∂law v k) = moment v k n := by
  have hD := fourth_nonneg_cubic_pos v k hv h4
  have hd := determinant_nonneg_delta_pos v k hv hD.le
  rw [law_moment,power_monic v k hv h4]
  exact monic_moments v k hv hd hD n hn

theorem law_represents_eight (v k : ℝ) (hv : 0 < v) (h4 : 0 ≤ fourthDeterminant v k) :
    MixedCubicBoundaryQuartic.RepresentsEight (law v k) v k :=
  ⟨inferInstance,fun n _ => law_integrable v k _,law_matches v k hv h4⟩

theorem representation_quartic_positive (μ : Measure ℝ) (v k : ℝ)
    (hμ : MixedCubicBoundaryQuartic.RepresentsEight μ v k) :
    ∀ g : Polynomial ℝ, g.natDegree ≤ 4 → 0 ≤ expectation v k (g^2) := by
  rcases hμ with ⟨hprob,hi,hm⟩
  intro g hg
  have hg2 : (g^2).natDegree ≤ 8 := natDegree_pow_le.trans (by omega)
  have hmatch : ∀ n ≤ 8, (∫ x : ℝ, x^n ∂μ) = expectation v k (X^n) := by
    intro n hn
    rw [expectation_X_pow]
    exact hm n hn
  have he := (TruncatedPolynomialIntegration.polynomial_integral_match μ
    (expectation v k) 8 hi hmatch (g^2) hg2).2
  rw [← he]
  apply integral_nonneg
  intro x
  simpa only [eval_pow,Pi.zero_apply] using sq_nonneg (g.eval x)

theorem zero_representation :
    MixedCubicBoundaryQuartic.RepresentsEight (Measure.dirac (0 : ℝ)) 0 0 := by
  refine ⟨inferInstance,fun n _ => integrable_dirac (by finiteness),fun n _ => ?_⟩
  cases n with
  | zero => simp [moment]
  | succ n => simp [moment]

theorem mixed_eight_realizable_iff (v k : ℝ) :
    (∃ μ, MixedCubicBoundaryQuartic.RepresentsEight μ v k) ↔
      (v=0 ∧ k=0) ∨ (0<v ∧ 0≤fourthDeterminant v k) := by
  constructor
  · rintro ⟨μ,hμ⟩
    exact (quartic_positivity_all_parameters_iff v k).mp (representation_quartic_positive μ v k hμ)
  · rintro (⟨rfl,rfl⟩ | ⟨hv,h4⟩)
    · exact ⟨Measure.dirac 0,zero_representation⟩
    · exact ⟨law v k,law_represents_eight v k hv h4⟩

theorem mixed_eight_realizable_iff_quartic_positive (v k : ℝ) :
    (∃ μ, MixedCubicBoundaryQuartic.RepresentsEight μ v k) ↔
      ∀ g : Polynomial ℝ, g.natDegree ≤ 4 → 0 ≤ expectation v k (g^2) := by
  rw [mixed_eight_realizable_iff,quartic_positivity_all_parameters_iff]

end OperatorDerivativeRewrite.Foundation.MixedCubicEighthRealization
