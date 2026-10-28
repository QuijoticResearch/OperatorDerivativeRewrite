import Foundation.FiniteWilsonTorusCharacters

/-! All-centered-function kinetic gap and failure of its unchanged retention
under the realized homogeneous spatial Wilson weight. Scope: the finite Z2
periodic torus already constructed, not continuous SU2 or physical4D. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusGap
open FiniteWilsonTorusKernel FiniteWilsonTorusCharacters
open FiniteWilsonTorusStationary FiniteWilsonTorusProbe

def coefficient (a : State) (f : State → ℝ) : ℝ := ∑ i,character a i*f i

def quadratic (f : State → ℝ) : ℝ := ∑ i,f i*(∑ j,kinetic i j*f j)

private theorem weighted_expansion (c f : State → ℝ) :
    (∑ a,c a*(coefficient a f)^2)=
      ∑ i,∑ j,f i*f j*(∑ a,c a*character a i*character a j) := by
  simp only [coefficient,pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- This identity verifies completeness on ALL real functions, not merely
orthogonality on a selection of tested character modes. -/
theorem parseval (f : State → ℝ) : (∑ a,(coefficient a f)^2)=32*(∑ i,f i^2) := by
  have h := weighted_expansion (fun _ => 1) f
  simp only [one_mul,gram,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at h
  calc
    _ = ∑ i,f i*f i*32 := h
    _ = 32*(∑ i,f i^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The exact quadratic form of the actual kinetic transition matrix. -/
theorem quadratic_synthesis (f : State → ℝ) :
    2097152*quadratic f=∑ a,(eigenNumerator a:ℝ)*(coefficient a f)^2 := by
  calc
    _ = ∑ i,∑ j,f i*f j*(2097152*kinetic i j) := by
      simp only [quadratic,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i,∑ j,f i*f j*(∑ a,(eigenNumerator a:ℝ)*character a i*character a j) := by
      simp only [kinetic_fourier]
    _ = _ := (weighted_expansion (fun a => (eigenNumerator a:ℝ)) f).symm

theorem coefficient_zero (f : State → ℝ) : coefficient 0 f=∑ i,f i := by
  simp [coefficient,character_zero]

theorem coefficient_character (a b : State) :
    coefficient a (character b)=if a=b then 32 else 0 := by
  calc
    _ = ∑ i,character i a*character i b := by
      unfold coefficient
      apply Finset.sum_congr rfl
      intro i hi
      rw [character_symmetric a i,character_symmetric b i]
    _ = _ := gram a b

/-- The missing all-centered-function bound, rather than a diagnostic eigenvalue. -/
theorem bare_centered_quadratic (f : State → ℝ) (hf : (∑ i,f i)=0) :
    quadratic f ≤ (1/4:ℝ)*(∑ i,f i^2) := by
  have hz : coefficient 0 f=0 := by rw [coefficient_zero,hf]
  have hs : (∑ a,(eigenNumerator a:ℝ)*(coefficient a f)^2) ≤
      ∑ a,(16384:ℝ)*(coefficient a f)^2 := by
    apply Finset.sum_le_sum
    intro a ha
    by_cases hzero : a=0
    · subst a
      simp [hz]
    · exact mul_le_mul_of_nonneg_right (nonconstant_numerator_bound a hzero) (sq_nonneg _)
  rw [← Finset.mul_sum,parseval,← quadratic_synthesis] at hs
  nlinarith

theorem bare_poincare (f : State → ℝ) (hf : bareMean f=0) :
    (3/4:ℝ)*bareSecondMoment f ≤ bareSecondMoment f-bareLagPairing f := by
  have hsum : (∑ i,f i)=0 := by
    change (∑ i,f i)/32=0 at hf
    exact (div_eq_zero_iff.mp hf).resolve_right (by norm_num)
  have h := bare_centered_quadratic f hsum
  unfold quadratic at h
  unfold bareSecondMoment bareLagPairing
  nlinarith

/-- The3/4 kinetic Poincare gap is attained by a nonzero centered winding mode. -/
theorem bare_gap_sharp : ∃ f : State → ℝ, bareMean f=0 ∧ 0 < bareSecondMoment f ∧
    bareLagPairing f=(1/4:ℝ)*bareSecondMoment f := by
  have hm := coefficient_character 0 8
  rw [coefficient_zero] at hm
  norm_num at hm
  have hv := gram (8:State) 8
  have hsq : (∑ i,(character 8 i)^2)=32 := by
    have hr : (∑ i,character 8 i*character 8 i)=∑ i,character i 8*character i 8 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [character_symmetric 8 i]
    rw [← hr] at hv
    simpa [pow_two] using hv
  have hq := quadratic_synthesis (character 8)
  norm_num [coefficient_character,eigenNumerator,Fin.sum_univ_succ] at hq
  refine ⟨character 8, ?_, ?_, ?_⟩
  · unfold bareMean
    rw [hm]
    norm_num
  · unfold bareSecondMoment
    rw [hsq]
    norm_num
  · change quadratic (character 8)/32=(1/4:ℝ)*((∑ i,(character 8 i)^2)/32)
    rw [hsq]
    nlinarith

/-- The same3/4 kinetic gap lower bound fails for the actual stationary
spatially weighted operator, with positive variance and exact centering. -/
theorem homogeneous_gap_counterexample : ∃ f : State → ℝ,
    mean f=0 ∧ 0 < secondMoment f ∧
      secondMoment f-lagPairing f < (3/4:ℝ)*secondMoment f := by
  have h := (lt_div_iff₀ probe_secondMoment_pos).mp stationary_probe_above_quarter
  exact ⟨probe,probe_mean,probe_secondMoment_pos,by nlinarith⟩

theorem unchanged_gap_fails : ¬∀ f : State → ℝ, mean f=0 →
    (3/4:ℝ)*secondMoment f ≤ secondMoment f-lagPairing f := by
  intro h
  obtain ⟨f,hf,hv,hbad⟩ := homogeneous_gap_counterexample
  exact (not_lt_of_ge (h f hf)) hbad

/-- A quantitative variational upper bound for the actual stationary gap. -/
theorem stationary_gap_upper : secondMoment probe-lagPairing probe ≤
    (39/64:ℝ)*secondMoment probe := by
  have hr : (25/64:ℝ) ≤ lagPairing probe/secondMoment probe := by
    rw [probe_rayleigh]
    apply (le_div_iff₀ FiniteWilsonTorusGround.value_pos).mpr
    nlinarith [FiniteWilsonTorusGround.value_bounds.2]
  have hl := (le_div_iff₀ probe_secondMoment_pos).mp hr
  nlinarith

/-- Any all-centered comparison with the sharp kinetic gap must pay a strictly
positive correction in this fixed homogeneous example. -/
theorem comparison_error_necessary (ε : ℝ)
    (h : ∀ f : State → ℝ, mean f=0 →
      ((3/4:ℝ)-ε)*secondMoment f ≤ secondMoment f-lagPairing f) : (9/64:ℝ) ≤ ε := by
  have hc := h probe probe_mean
  have hu := stationary_gap_upper
  by_contra hε
  have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hε)) probe_secondMoment_pos
  nlinarith

end OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusGap
