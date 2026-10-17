import Foundation.FiniteMatrixSpectralMeasure
import Foundation.SingularTruncatedMomentObstruction

/-! Genuine probability moment vectors converge to singular non-realizable data. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.TruncatedMomentEscape
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def baseMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0,Real.sqrt 2; Real.sqrt 2,2]

theorem baseMatrix_hermitian : baseMatrix.IsHermitian := by
  change baseMatrix.conjTranspose = baseMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp [baseMatrix, Matrix.conjTranspose_apply]

def baseLaw : Measure ℝ := FiniteMatrixSpectralMeasure.law baseMatrix_hermitian 0
instance baseLaw_probability : IsProbabilityMeasure baseLaw :=
  FiniteMatrixSpectralMeasure.law_probability _ _

theorem baseLaw_integrable (f : ℝ → ℝ) : Integrable f baseLaw :=
  FiniteMatrixSpectralMeasure.law_integrable _ _ _

def baseMoment (p : ℕ) : ℝ := if p = 6 then 88 else SingularTruncatedMomentObstruction.moment p

theorem baseLaw_moment (p : ℕ) (hp : p ≤ 6) :
    (∫ x : ℝ, x^p ∂baseLaw) = baseMoment p := by
  have h2 : (Real.sqrt 2)^2 = 2 := by norm_num
  have h4 : (Real.sqrt 2)^4 = 4 := by
    calc (Real.sqrt 2)^4 = ((Real.sqrt 2)^2)^2 := by ring
         _ = 4 := by rw [h2]; norm_num
  have h6 : (Real.sqrt 2)^6 = 8 := by
    calc (Real.sqrt 2)^6 = ((Real.sqrt 2)^2)^3 := by ring
         _ = 8 := by rw [h2]; norm_num
  change (∫ x : ℝ, x^p ∂FiniteMatrixSpectralMeasure.law baseMatrix_hermitian 0) = _
  rw [FiniteMatrixSpectralMeasure.law_moment]
  interval_cases p <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, baseMatrix, Matrix.one_apply,
      baseMoment, SingularTruncatedMomentObstruction.moment] <;>
    ring_nf <;> norm_num [h2,h4,h6]

def location (n : ℕ) : ℝ := (n : ℝ)+1
def epsilon (n : ℕ) : ℝ := (location n)⁻¹^6

theorem location_ge_one (n : ℕ) : 1 ≤ location n := by
  unfold location
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith
theorem location_pos (n : ℕ) : 0 < location n := lt_of_lt_of_le zero_lt_one (location_ge_one n)
theorem epsilon_nonneg (n : ℕ) : 0 ≤ epsilon n := by unfold epsilon; positivity
theorem epsilon_le_one (n : ℕ) : epsilon n ≤ 1 :=
  pow_le_one₀ (inv_nonneg.mpr (location_pos n).le) (inv_le_one_of_one_le₀ (location_ge_one n))

def law (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1-epsilon n) • baseLaw + ENNReal.ofReal (epsilon n) • Measure.dirac (location n)

instance law_probability (n : ℕ) : IsProbabilityMeasure (law n) := by
  constructor
  simp only [law, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr (epsilon_le_one n)) (epsilon_nonneg n)]
  simp

theorem law_integrable (n : ℕ) (f : ℝ → ℝ) : Integrable f (law n) :=
  ((baseLaw_integrable f).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

theorem law_integral (n : ℕ) (f : ℝ → ℝ) :
    (∫ x, f x ∂law n) = (1-epsilon n)*(∫ x, f x ∂baseLaw)+epsilon n*f (location n) := by
  have h0 := (baseLaw_integrable f).smul_measure (c := ENNReal.ofReal (1-epsilon n))
    ENNReal.ofReal_ne_top
  have h1 : Integrable f (ENNReal.ofReal (epsilon n) • Measure.dirac (location n)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [law, integral_add_measure h0 h1, integral_smul_measure, integral_smul_measure, integral_dirac]
  simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr (epsilon_le_one n)),
    ENNReal.toReal_ofReal (epsilon_nonneg n), smul_eq_mul]

theorem escape_cancellation (n p : ℕ) (hp : p ≤ 6) :
    epsilon n*(location n)^p = ((location n)⁻¹)^(6-p) := by
  unfold epsilon
  conv_lhs => arg 1; rw [show 6 = (6-p)+p by omega, pow_add]
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt (location_pos n)), one_pow, mul_one]

theorem law_moment (n p : ℕ) (hp : p ≤ 6) :
    (∫ x : ℝ, x^p ∂law n) =
      (1-epsilon n)*baseMoment p+((location n)⁻¹)^(6-p) := by
  rw [law_integral, baseLaw_moment p hp, escape_cancellation n p hp]

theorem inverse_location_tendsto :
    Tendsto (fun n => (location n)⁻¹) atTop (𝓝 0) := by
  have ht : Tendsto location atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact tendsto_inv_atTop_zero.comp ht

theorem epsilon_tendsto : Tendsto epsilon atTop (𝓝 0) := by
  change Tendsto (fun n => (location n)⁻¹^6) atTop (𝓝 0)
  simpa only [zero_pow (by omega : 6 ≠ 0)] using inverse_location_tendsto.pow 6

theorem bounded_observables_tendsto (f : ℝ → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) :
    Tendsto (fun n => ∫ x, f x ∂law n) atTop (𝓝 (∫ x, f x ∂baseLaw)) := by
  have htail : Tendsto (fun n => epsilon n*f (location n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
    · simpa using epsilon_tendsto.mul_const C
    · simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (epsilon_nonneg n)]
      exact mul_le_mul_of_nonneg_left (hf _) (epsilon_nonneg n)
  have hbase : Tendsto (fun n => (1-epsilon n)*(∫ x, f x ∂baseLaw)) atTop
      (𝓝 (∫ x, f x ∂baseLaw)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub epsilon_tendsto).mul_const
      (∫ x, f x ∂baseLaw)
  have ht := hbase.add htail
  have h := ht.congr' (Eventually.of_forall fun n => (law_integral n f).symm)
  simpa only [add_zero] using h

theorem moment_tendsto (p : ℕ) (hp : p ≤ 6) :
    Tendsto (fun n => ∫ x : ℝ, x^p ∂law n) atTop
      (𝓝 (SingularTruncatedMomentObstruction.moment p)) := by
  have hbase : Tendsto (fun n => (1-epsilon n)*baseMoment p) atTop (𝓝 (baseMoment p)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub epsilon_tendsto).mul_const (baseMoment p)
  by_cases he : p = 6
  · subst p
    have ht := hbase.add (tendsto_const_nhds (x := (1 : ℝ)))
    have hEq (n : ℕ) : (∫ x : ℝ, x^6 ∂law n) = (1-epsilon n)*baseMoment 6+1 := by
      rw [law_moment n 6 (by omega)]; norm_num
    have h := ht.congr' (Eventually.of_forall fun n => (hEq n).symm)
    have hval : baseMoment 6+1 = SingularTruncatedMomentObstruction.moment 6 := by
      norm_num [baseMoment, SingularTruncatedMomentObstruction.moment]
    simpa only [hval] using h
  · have hlt : p < 6 := by omega
    have htail : Tendsto (fun n => ((location n)⁻¹)^(6-p)) atTop (𝓝 0) := by
      simpa only [zero_pow (by omega : 6-p ≠ 0)] using inverse_location_tendsto.pow (6-p)
    have ht := hbase.add htail
    have h := ht.congr' (Eventually.of_forall fun n => (law_moment n p hp).symm)
    simpa only [add_zero, baseMoment, ite_eq_right he] using h

theorem sixth_moment_defect :
    Tendsto (fun n => ∫ x : ℝ, x^6 ∂law n) atTop (𝓝 89) ∧
      (∫ x : ℝ, x^6 ∂baseLaw) = 88 := by
  constructor
  · simpa only [SingularTruncatedMomentObstruction.moment] using moment_tendsto 6 (by omega)
  · simpa only [baseMoment, ite_true] using baseLaw_moment 6 (by omega)

theorem sixth_moment_bound (n : ℕ) : (∫ x : ℝ, x^6 ∂law n) ≤ 89 := by
  rw [law_moment n 6 (by omega)]
  norm_num [baseMoment]
  nlinarith [epsilon_nonneg n]

def sixthTail (R x : ℝ) : ℝ := if R < |x| then |x|^6 else 0

theorem sixthTail_nonneg (R x : ℝ) : 0 ≤ sixthTail R x := by
  unfold sixthTail
  split_ifs <;> positivity

theorem sixth_tail_lower (n : ℕ) (R : ℝ) (hR : R < location n) :
    1 ≤ ∫ x, sixthTail R x ∂law n := by
  rw [law_integral]
  have hloc : sixthTail R (location n) = (location n)^6 := by
    simp only [sixthTail, abs_of_nonneg (location_pos n).le, ite_eq_left hR]
  rw [hloc]
  have he : epsilon n*(location n)^6 = 1 := by
    simpa only [Nat.sub_self, pow_zero] using escape_cancellation n 6 (by omega)
  rw [he]
  have hi : 0 ≤ ∫ x, sixthTail R x ∂baseLaw := integral_nonneg (sixthTail_nonneg R)
  have hw := mul_nonneg (sub_nonneg.mpr (epsilon_le_one n)) hi
  linarith

theorem sixth_tail_nonvanishing (R : ℝ) :
    ∃ n : ℕ, 1 ≤ ∫ x, sixthTail R x ∂law n := by
  obtain ⟨n, hn⟩ := exists_nat_gt R
  refine ⟨n, sixth_tail_lower n R ?_⟩
  unfold location
  linarith

theorem no_uniform_sixth_tail_control :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n : ℕ, (∫ x, sixthTail R x ∂law n) < ε := by
  intro h
  obtain ⟨R, hR⟩ := h (1/2) (by norm_num)
  obtain ⟨n, hn⟩ := sixth_tail_nonvanishing R
  have hu := hR n
  linarith

def realizable : Set (Fin 7 → ℝ) :=
  {m | ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
    (∀ p : Fin 7, Integrable (fun x : ℝ => x^p.val) μ) ∧
      ∀ p : Fin 7, (∫ x : ℝ, x^p.val ∂μ) = m p}

def target (p : Fin 7) : ℝ := SingularTruncatedMomentObstruction.moment p.val
def momentVector (n : ℕ) (p : Fin 7) : ℝ := ∫ x : ℝ, x^p.val ∂law n

theorem momentVector_mem (n : ℕ) : momentVector n ∈ realizable :=
  ⟨law n, inferInstance, fun _ => law_integrable n _, fun _ => rfl⟩

theorem momentVector_tendsto : Tendsto momentVector atTop (𝓝 target) := by
  apply tendsto_pi_nhds.mpr
  intro p
  exact moment_tendsto p.val (by omega)

theorem target_not_mem : target ∉ realizable := by
  rintro ⟨μ, hμ, hi, hm⟩
  have hi' : ∀ n ≤ 6, Integrable (fun x : ℝ => x^n) μ := by
    intro n hn
    exact hi ⟨n, by omega⟩
  apply SingularTruncatedMomentObstruction.no_measure_truncated_realization μ hi'
  intro n hn
  exact hm ⟨n, by omega⟩

theorem realizable_not_isClosed : ¬ IsClosed realizable := by
  intro hc
  exact target_not_mem (hc.mem_of_tendsto momentVector_tendsto
    (Eventually.of_forall momentVector_mem))

end OperatorDerivativeRewrite.Foundation.TruncatedMomentEscape
