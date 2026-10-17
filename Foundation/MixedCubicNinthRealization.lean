import Foundation.MixedCubicEighthRealization
import Foundation.TridiagonalNinthSteering

/-! Every ninth moment is attainable above the strict mixed quartic boundary. -/
noncomputable section
open MeasureTheory Polynomial Matrix
namespace OperatorDerivativeRewrite.Foundation.MixedCubicNinthRealization
open MixedCubicMomentPositivity MixedCubicThirdDegree MixedCubicFourthDegree
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def jacobi (v k f : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  TridiagonalMomentIntertwining.symmetric (k/v)
    (MixedCubicEighthRealization.diagonalTwo v k) (MixedCubicEighthRealization.diagonalThree v k) f
    (Real.sqrt v) (Real.sqrt (delta v k)/v)
    (Real.sqrt (v*determinant v k)/delta v k)
    (Real.sqrt (delta v k*fourthDeterminant v k)/determinant v k)

theorem jacobi_hermitian (v k f : ℝ) : (jacobi v k f).IsHermitian := by
  change (jacobi v k f).conjTranspose = jacobi v k f
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacobi,TridiagonalMomentIntertwining.symmetric,Matrix.conjTranspose_apply]

theorem power_prefix (v k f : ℝ) (n : ℕ) (hn : n ≤ 8) :
    ((jacobi v k f)^n) 0 0 = ((MixedCubicEighthRealization.jacobi v k)^n) 0 0 :=
  TridiagonalNinthSteering.symmetric_prefix _ _ _ _ _ _ _ _ n hn

theorem power_ninth (v k f : ℝ) (hv : 0 < v) (h4 : 0 ≤ fourthDeterminant v k) :
    ((jacobi v k f)^9) 0 0 = ((MixedCubicEighthRealization.jacobi v k)^9) 0 0+
      fourthDeterminant v k/determinant v k*f := by
  have hD := fourth_nonneg_cubic_pos v k hv h4
  have hd := determinant_nonneg_delta_pos v k hv hD.le
  have hr := Real.sq_sqrt hv.le
  have hs := Real.sq_sqrt hd.le
  have he := Real.sq_sqrt (mul_pos hv hD).le
  have hh := Real.sq_sqrt (mul_nonneg hd.le h4)
  have h := TridiagonalNinthSteering.symmetric_ninth (k/v)
    (MixedCubicEighthRealization.diagonalTwo v k) (MixedCubicEighthRealization.diagonalThree v k) f
    (Real.sqrt v) (Real.sqrt (delta v k)/v)
    (Real.sqrt (v*determinant v k)/delta v k)
    (Real.sqrt (delta v k*fourthDeterminant v k)/determinant v k)
  change ((jacobi v k f)^9) 0 0 = ((MixedCubicEighthRealization.jacobi v k)^9) 0 0+_ at h
  rw [h]
  simp only [div_pow,hr,hs,he,hh]
  field_simp [hv.ne',hd.ne',hD.ne'] <;> ring

def law (v k f : ℝ) : Measure ℝ :=
  FiniteMatrixSpectralMeasure.law (jacobi_hermitian v k f) 0

instance law_probability (v k f : ℝ) : IsProbabilityMeasure (law v k f) :=
  FiniteMatrixSpectralMeasure.law_probability _ _

theorem law_integrable (v k f : ℝ) (g : ℝ → ℝ) : Integrable g (law v k f) :=
  FiniteMatrixSpectralMeasure.law_integrable _ _ _

theorem law_moment (v k f : ℝ) (n : ℕ) :
    (∫ x : ℝ, x^n ∂law v k f) = ((jacobi v k f)^n) 0 0 :=
  FiniteMatrixSpectralMeasure.law_moment _ _ _

theorem law_prefix (v k f : ℝ) (n : ℕ) (hn : n ≤ 8) :
    (∫ x : ℝ, x^n ∂law v k f) = ∫ x : ℝ, x^n ∂MixedCubicEighthRealization.law v k := by
  rw [law_moment,MixedCubicEighthRealization.law_moment,power_prefix v k f n hn]

theorem law_ninth (v k f : ℝ) (hv : 0 < v) (h4 : 0 ≤ fourthDeterminant v k) :
    (∫ x : ℝ, x^9 ∂law v k f) =
      (∫ x : ℝ, x^9 ∂MixedCubicEighthRealization.law v k)+
        fourthDeterminant v k/determinant v k*f := by
  rw [law_moment,MixedCubicEighthRealization.law_moment,power_ninth v k f hv h4]

def steering (v k target : ℝ) : ℝ :=
  (target-(∫ x : ℝ, x^9 ∂MixedCubicEighthRealization.law v k))*
    determinant v k/fourthDeterminant v k

theorem law_hits_target (v k target : ℝ) (hv : 0 < v) (h4 : 0 < fourthDeterminant v k) :
    (∫ x : ℝ, x^9 ∂law v k (steering v k target)) = target := by
  have hD := fourth_nonneg_cubic_pos v k hv h4.le
  rw [law_ninth v k _ hv h4.le,steering]
  field_simp [hD.ne',h4.ne']
  ring

theorem law_matches_eight (v k f : ℝ) (hv : 0 < v) (h4 : 0 ≤ fourthDeterminant v k)
    (n : ℕ) (hn : n ≤ 8) : (∫ x : ℝ, x^n ∂law v k f) = moment v k n := by
  rw [law_prefix v k f n hn]
  exact MixedCubicEighthRealization.law_matches v k hv h4 n hn

theorem arbitrary_ninth_realization (v k target : ℝ) (hv : 0 < v)
    (h4 : 0 < fourthDeterminant v k) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ n : ℕ, Integrable (fun x : ℝ => x^n) μ) ∧
      (∀ n ≤ 8, (∫ x : ℝ, x^n ∂μ) = moment v k n) ∧
      (∫ x : ℝ, x^9 ∂μ) = target := by
  refine ⟨law v k (steering v k target),inferInstance,fun n => law_integrable _ _ _ _,?_,?_⟩
  · exact law_matches_eight v k _ hv h4.le
  · exact law_hits_target v k target hv h4

theorem moment_nine (v k : ℝ) : moment v k 9 = 1260*v^3*k+280*k^3 := by
  norm_num [moment]
  ring

def RepresentsNine (μ : Measure ℝ) (v k : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ n ≤ 9, Integrable (fun x : ℝ => x^n) μ) ∧
    ∀ n ≤ 9, (∫ x : ℝ, x^n ∂μ) = moment v k n

theorem strict_mixed_nine_realization (v k : ℝ) (hv : 0 < v)
    (h4 : 0 < fourthDeterminant v k) :
    RepresentsNine (law v k (steering v k (moment v k 9))) v k := by
  refine ⟨inferInstance,fun n _ => law_integrable _ _ _ _,fun n hn => ?_⟩
  by_cases h : n=9
  · subst n
    exact law_hits_target v k (moment v k 9) hv h4
  · exact law_matches_eight v k _ hv h4.le n (by omega)

theorem nine_implies_eight (μ : Measure ℝ) (v k : ℝ) (hμ : RepresentsNine μ v k) :
    MixedCubicBoundaryQuartic.RepresentsEight μ v k :=
  ⟨hμ.1,fun n hn => hμ.2.1 n (by omega),fun n hn => hμ.2.2 n (by omega)⟩

theorem nine_parameter_necessary (v k : ℝ) (h : ∃ μ, RepresentsNine μ v k) :
    (v=0 ∧ k=0) ∨ (0<v ∧ 0≤fourthDeterminant v k) := by
  obtain ⟨μ,hμ⟩ := h
  exact (MixedCubicEighthRealization.mixed_eight_realizable_iff v k).mp
    ⟨μ,nine_implies_eight μ v k hμ⟩

theorem zero_representation : RepresentsNine (Measure.dirac (0 : ℝ)) 0 0 := by
  refine ⟨inferInstance,fun n _ => integrable_dirac (by finiteness),fun n _ => ?_⟩
  cases n with
  | zero => simp [moment]
  | succ n => simp [moment]

end OperatorDerivativeRewrite.Foundation.MixedCubicNinthRealization
