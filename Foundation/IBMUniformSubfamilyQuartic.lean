import Foundation.IBMUniformQuarticProbability

/-! Quartic fluctuations for deterministic subfamilies of ONE common uniform
grid. Selection is deterministic; no random scenery weights are inserted. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformSubfamilyQuartic
open InfiniteGaussian IBMSourceLaws IBMConstructedSources
open IBMUniformClockGridEnergy IBMUniformClockMaximum IBMClockTraversalEnvelope
open IBMQuarticOccupationEnergy
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.sceneryPath

def quartic (I : Finset (ℝ≥0 × ℝ≥0)) (ω : JointSample) : ℝ :=
  ∑ p ∈ I, (ibmValue p.2 ω - ibmValue p.1 ω) ^ 4

def mean (I : Finset (ℝ≥0 × ℝ≥0)) (y : SampleSpace) : ℝ :=
  ∑ p ∈ I, 3 * (|clockPath y p.2| - |clockPath y p.1|) ^ 2

def residual (I : Finset (ℝ≥0 × ℝ≥0)) (ω : JointSample) : ℝ :=
  quartic I ω - mean I ω.2

theorem quartic_measurable (I : Finset (ℝ≥0 × ℝ≥0)) : Measurable (quartic I) := by
  apply Finset.measurable_sum
  intro p hp
  exact ((ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)).sub
    (ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id))).pow_const 4

theorem mean_measurable (I : Finset (ℝ≥0 × ℝ≥0)) : Measurable (mean I) := by
  apply Finset.measurable_sum
  intro p hp
  exact ((continuous_abs.measurable.comp
    ((ContinuousMap.measurable_eval p.2).comp clockPath_measurable)).sub
    (continuous_abs.measurable.comp
    ((ContinuousMap.measurable_eval p.1).comp clockPath_measurable))).pow_const 2 |>.const_mul 3

theorem residual_measurable (I : Finset (ℝ≥0 × ℝ≥0)) : Measurable (residual I) :=
  (quartic_measurable I).sub ((mean_measurable I).comp measurable_snd)

private abbrev oldQuartic (I : Finset (ℝ≥0 × ℝ≥0)) (x y : SampleSpace) : ℝ :=
  IBMFiniteQuartic.quarticSum (fun r ω => sceneryPath ω r) (fun t ω => clockPath ω t)
    (fun ω => (sceneryPath ω).continuous) (fun ω => (clockPath ω).continuous) I x y

private theorem oldQuartic_eq (I : Finset (ℝ≥0 × ℝ≥0)) (x y : SampleSpace) :
    oldQuartic I x y = quartic I (x,y) := by
  unfold oldQuartic IBMFiniteQuartic.quarticSum quartic
  apply Finset.sum_congr rfl
  intro p hp
  simp only [IBMContinuousComposition.value_eq, IBMModificationBridge.sceneryPath_apply,
    IBMModificationBridge.clockPath_apply, ibmValue_eq]

theorem conditional_mean (I : Finset (ℝ≥0 × ℝ≥0)) (y : SampleSpace) :
    (∫ x, quartic I (x,y) ∂gaussianProduct) = mean I y := by
  have h := IBMFiniteQuartic.conditional_quarticSum_expectation
    (fun r ω => sceneryPath ω r) (fun t ω => clockPath ω t)
    (fun ω => (sceneryPath ω).continuous) (fun ω => (clockPath ω).continuous)
    sceneryPath_coordinate_ae I y
  change (∫ x, oldQuartic I x y ∂gaussianProduct) = _ at h
  simpa only [oldQuartic_eq, mean] using h

theorem conditional_quartic_memLp (I : Finset (ℝ≥0 × ℝ≥0)) (y : SampleSpace) :
    MemLp (fun x => quartic I (x,y)) 2 gaussianProduct := by
  have h := conditional_quartic_memLp_two
    (fun r ω => sceneryPath ω r) (fun t ω => clockPath ω t)
    (fun ω => (sceneryPath ω).continuous) (fun ω => (clockPath ω).continuous)
    sceneryPath_coordinate_ae I y
  change MemLp (fun x => oldQuartic I x y) 2 gaussianProduct at h
  simpa only [oldQuartic_eq] using h

theorem conditional_residual_square_integrable (I : Finset (ℝ≥0 × ℝ≥0))
    (y : SampleSpace) : Integrable (fun x => residual I (x,y) ^ 2) gaussianProduct := by
  have hc : MemLp (fun _ : SampleSpace => mean I y) 2 gaussianProduct := memLp_const _
  have hm : MemLp (fun x => residual I (x,y)) 2 gaussianProduct :=
    (conditional_quartic_memLp I y).sub hc
  simpa only [Real.norm_eq_abs, sq_abs] using hm.integrable_norm_pow'

/-- Removing intervals decreases traversal multiplicity and hence its energy.
Spatial returns retain their multiplicities regardless of orientation. -/
theorem count_square_mono {I J : Finset (ℝ≥0 × ℝ≥0)} (hIJ : I ⊆ J)
    (a b : (ℝ≥0 × ℝ≥0) → ℝ) :
    (∫ x, count I a b x ^ 2) ≤ ∫ x, count J a b x ^ 2 := by
  apply integral_mono (count_square_integrable I a b) (count_square_integrable J a b)
  intro x
  have hi : 0 ≤ count I a b x := Finset.sum_nonneg fun _ _ => hit_nonneg _ _ _
  have hij : count I a b x ≤ count J a b x :=
    Finset.sum_le_sum_of_subset_of_nonneg hIJ (fun _ _ _ => hit_nonneg _ _ _)
  nlinarith

theorem conditional_residual_square_le {T : ℝ≥0} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (I : Finset (ℝ≥0 × ℝ≥0))
    (hI : I ⊆ IBMUniformQuarticFamily.intervals T n)
    {δ : ℝ} (hδ : 0 ≤ δ) {y : SampleSpace} (hy : y ∉ bad T n δ) :
    (∫ x, residual I (x,y) ^ 2 ∂gaussianProduct) ≤
      96 * δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ y := by
  have hmesh : ∀ p ∈ I, abs (|clockPath y p.2| - |clockPath y p.1|) ≤ δ := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (hI hp)
    exact reflected_mesh_of_not_bad T n δ hy ⟨k, Finset.mem_range.mp hk⟩
  have h := actual_conditional_centered_square_le I y δ hδ hmesh
  change (∫ x, (oldQuartic I x y -
    ∫ z, oldQuartic I z y ∂gaussianProduct) ^ 2 ∂gaussianProduct) ≤ _ at h
  simp_rw [oldQuartic_eq, conditional_mean] at h
  have hm := count_square_mono hI (fun p => |clockPath y p.1|)
    (fun p => |clockPath y p.2|)
  have he : (∫ x, count (IBMUniformQuarticFamily.intervals T n)
      (fun p => |clockPath y p.1|) (fun p => |clockPath y p.2|) x ^ 2) =
      IBMUniformClockOccupation.occupation T n y := by
    have hc (x : ℝ) : count (IBMUniformQuarticFamily.intervals T n)
        (fun p => |clockPath y p.1|) (fun p => |clockPath y p.2|) x =
        count (Finset.range n) (fun k => |clockPath y (grid (T / n) k)|)
          (fun k => |clockPath y (grid (T / n) (k + 1))|) x :=
      IBMUniformQuarticFamily.sum_intervals hT n hn _
    simp_rw [hc]
    rfl
  rw [he] at hm
  exact h.trans (mul_le_mul_of_nonneg_left
    (hm.trans (IBMUniformClockOccupation.occupation_le_envelope T n hδ hy)) (by positivity))

def tailEvent (I : Finset (ℝ≥0 × ℝ≥0)) (ε : ℝ) : Set JointSample :=
  {ω | ε ≤ |residual I ω|}

theorem tailEvent_measurable (I : Finset (ℝ≥0 × ℝ≥0)) (ε : ℝ) :
    MeasurableSet (tailEvent I ε) :=
  measurableSet_le measurable_const (continuous_abs.measurable.comp (residual_measurable I))

def conditionalTail (I : Finset (ℝ≥0 × ℝ≥0)) (ε : ℝ) (y : SampleSpace) : ℝ :=
  ∫ x, (tailEvent I ε).indicator (fun _ => (1 : ℝ)) (x,y) ∂gaussianProduct

theorem conditionalTail_eq_measure (I : Finset (ℝ≥0 × ℝ≥0)) (ε : ℝ) (y : SampleSpace) :
    conditionalTail I ε y = gaussianProduct.real {x | ε ≤ |residual I (x,y)|} := by
  change (∫ x, ({x | ε ≤ |residual I (x,y)|}).indicator
    (fun _ => (1 : ℝ)) x ∂gaussianProduct) = _
  rw [integral_indicator_const]
  · simp
  · exact (tailEvent_measurable I ε).preimage (measurable_id.prodMk measurable_const)

theorem conditionalTail_le_one (I : Finset (ℝ≥0 × ℝ≥0)) (ε : ℝ) (y : SampleSpace) :
    conditionalTail I ε y ≤ 1 := by
  rw [conditionalTail_eq_measure]
  exact measureReal_le_one

theorem joint_indicator_integrable (I : Finset (ℝ≥0 × ℝ≥0)) (ε : ℝ) :
    Integrable ((tailEvent I ε).indicator (fun _ => (1 : ℝ))) jointMeasure :=
  (integrable_const 1).indicator (tailEvent_measurable I ε)

theorem conditionalTail_integrable (I : Finset (ℝ≥0 × ℝ≥0)) (ε : ℝ) :
    Integrable (conditionalTail I ε) gaussianProduct :=
  (joint_indicator_integrable I ε).integral_prod_right

/-- Fubini identifies the integral of genuine conditional tail probabilities
with the tail probability under the original joint scenery-clock measure. -/
theorem joint_tail_eq_integral (I : Finset (ℝ≥0 × ℝ≥0)) (ε : ℝ) :
    jointMeasure.real (tailEvent I ε) =
      ∫ y, conditionalTail I ε y ∂gaussianProduct := by
  calc
    _ = ∫ ω, (tailEvent I ε).indicator (fun _ => (1 : ℝ)) ω ∂jointMeasure := by
      rw [integral_indicator_const 1 (tailEvent_measurable I ε)]
      simp
    _ = _ := integral_prod_symm _ (joint_indicator_integrable I ε)

theorem conditionalTail_chebyshev (I : Finset (ℝ≥0 × ℝ≥0))
    {ε : ℝ} (hε : 0 < ε) (y : SampleSpace) :
    conditionalTail I ε y ≤
      (∫ x, residual I (x,y) ^ 2 ∂gaussianProduct) / ε ^ 2 := by
  rw [conditionalTail_eq_measure]
  calc
    _ ≤ gaussianProduct.real {x | ε ^ 2 ≤ residual I (x,y) ^ 2} := by
      apply measureReal_mono (h₂ := by finiteness)
      intro x hx
      change ε ≤ |residual I (x,y)| at hx
      change ε ^ 2 ≤ residual I (x,y) ^ 2
      rw [← sq_abs (residual I (x,y))]
      gcongr
    _ ≤ _ := by
      apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
      rw [mul_comm]
      exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
        (conditional_residual_square_integrable I y) (ε ^ 2)

theorem conditionalTail_good_le {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (I : Finset (ℝ≥0 × ℝ≥0)) (hI : I ⊆ IBMUniformQuarticFamily.intervals T n)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) {y : SampleSpace}
    (hy : y ∉ bad T n δ) :
    conditionalTail I ε y ≤
      (96 / ε ^ 2) * (δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ y) := by
  exact (conditionalTail_chebyshev I hε y).trans
    ((div_le_div_of_nonneg_right (conditional_residual_square_le hT n hn I hI hδ hy)
      (sq_nonneg ε)).trans_eq (by ring))

/-- No global scenery-clock L2 error bound is assumed: a bounded indicator
and an integrable good-clock envelope suffice for the joint probability. -/
theorem joint_tail_le {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (I : Finset (ℝ≥0 × ℝ≥0)) (hI : I ⊆ IBMUniformQuarticFamily.intervals T n)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    jointMeasure.real (tailEvent I ε) ≤ gaussianProduct.real (bad T n δ) +
      (96 / ε ^ 2) * (∫ y, δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ y
        ∂gaussianProduct) := by
  let B := (bad T n δ).indicator (fun _ => (1 : ℝ))
  let E := fun y => δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ y
  let c := 96 / ε ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he (y : SampleSpace) : 0 ≤ E y := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => tent_nonneg _ _
  have hiB : Integrable B gaussianProduct :=
    (integrable_const 1).indicator (bad_measurable T n δ)
  have hiE : Integrable E gaussianProduct :=
    (energy_integrable (Finset.range n) (grid (T / n)) hδ.le).const_mul _
  rw [joint_tail_eq_integral]
  calc
    _ ≤ ∫ y, B y + c * E y ∂gaussianProduct := by
      apply integral_mono (conditionalTail_integrable I ε) (hiB.add (hiE.const_mul c))
      intro y
      change conditionalTail I ε y ≤ B y + c * E y
      by_cases hy : y ∈ bad T n δ
      · have hBy : B y = 1 := indicator_of_mem hy _
        rw [hBy]
        exact (conditionalTail_le_one I ε y).trans (le_add_of_nonneg_right (mul_nonneg hc (he y)))
      · have hBy : B y = 0 := indicator_of_notMem hy _
        rw [hBy, zero_add]
        exact conditionalTail_good_le hT n hn I hI hδ.le hε hy
    _ = _ := by
      rw [integral_add hiB (hiE.const_mul c), integral_const_mul]
      have hBmass : (∫ y, B y ∂gaussianProduct) = gaussianProduct.real (bad T n δ) := by
        dsimp only [B]
        rw [integral_indicator_const (1 : ℝ) (bad_measurable T n δ)]
        simp
      rw [hBmass]


attribute [local irreducible] IBMClockTraversalEnvelope.energy IBMUniformClockMaximum.bad

/-- Uniform deterministic selection is allowed to vary arbitrarily with N.
This is not a statement about a supremum over selections or random selection. -/
theorem residual_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (I : ℕ → Finset (ℝ≥0 × ℝ≥0))
    (hI : ∀ n, I n ⊆ IBMUniformQuarticFamily.intervals T (n + 1)) :
    TendstoInMeasure jointMeasure (fun n => residual (I n))
      Filter.atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  simp only [sub_zero, Real.norm_eq_abs]
  change Filter.Tendsto (fun n : ℕ => jointMeasure.real (tailEvent (I n) ε))
    Filter.atTop (nhds 0)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n =>
    joint_tail_le hT (n + 1) (by omega) (I n) (hI n)
      (δ := (n + 1 : ℝ) ^ (-(4/9 : ℝ)))
      (Real.rpow_pos_of_pos (by positivity : 0 < (n + 1 : ℝ)) (-(4/9 : ℝ))) hε)
  simpa only [Nat.cast_add, Nat.cast_one, mul_zero, add_zero] using
    (bad_probability_tendsto T).add
      ((actual_weighted_energy_tendsto hT).const_mul (96 / ε ^ 2))

def prefixIntervals (T : ℝ≥0) (n m : ℕ) : Finset (ℝ≥0 × ℝ≥0) :=
  (Finset.range m).image (IBMUniformQuarticFamily.segment T n)

theorem prefix_subset (T : ℝ≥0) {n m : ℕ} (hm : m ≤ n) :
    prefixIntervals T n m ⊆ IBMUniformQuarticFamily.intervals T n :=
  Finset.image_subset_image (Finset.range_mono hm)

theorem sum_prefix {T : ℝ≥0} (hT : 0 < T) (n m : ℕ)
    (f : (ℝ≥0 × ℝ≥0) → ℝ) :
    (∑ p ∈ prefixIntervals T (n + 1) m, f p) =
      ∑ k ∈ Finset.range m, f (IBMUniformQuarticFamily.segment T (n + 1) k) := by
  unfold prefixIntervals
  rw [Finset.sum_image]
  intro i hi j hj hij
  exact grid_injective (div_pos hT (by positivity))
    (congrArg Prod.fst hij)

/-- Prefixes stay on the original horizon's grid rather than being remeshed
over a different horizon. Their exact conditional fluctuations vanish. -/
theorem prefix_residual_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (m : ℕ → ℕ) (hm : ∀ n, m n ≤ n + 1) :
    TendstoInMeasure jointMeasure (fun n => residual (prefixIntervals T (n + 1) (m n)))
      Filter.atTop (fun _ => (0 : ℝ)) :=
  residual_tendstoInMeasure hT _ (fun n => prefix_subset T (hm n))

end OperatorDerivativeRewrite.Foundation.IBMUniformSubfamilyQuartic
