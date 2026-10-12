import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Process.Predictable
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Elementary integration against an actual pre-Brownian process. Coefficients are
measurable functions of its entire past and genuinely square integrable; independence,
centering and the one-step Itô isometry are proved from the Gaussian process law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianPredictableStep
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The full coordinate process up to and including `s`. -/
def pastProcess (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : Set.Iic s → ℝ :=
  fun r => B r ω

/-- A coefficient determined by the past; its integrability is a separate obligation. -/
def pastCoefficient (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0)
    (a : (Set.Iic s → ℝ) → ℝ) (ω : Ω) : ℝ := a (pastProcess B s ω)

/-- The actual process increment, including the zero-length case. -/
def increment (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (ω : Ω) : ℝ := B t ω - B s ω

/-- The elementary stochastic integral is actual multiplication by an increment. -/
def stepIntegral (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (a : (Set.Iic s → ℝ) → ℝ) (ω : Ω) : ℝ :=
  pastCoefficient B s a ω * increment B s t ω

omit [IsProbabilityMeasure μ] in
/-- A measurable past coefficient is independent of the following increment. -/
theorem pastCoefficient_indep_increment (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) {a : (Set.Iic s → ℝ) → ℝ} (ha : Measurable a) :
    IndepFun (pastCoefficient B s a) (increment B s t) μ := by
  have hi := (hB.indepFun_shift s).symm.comp ha
    (measurable_pi_apply (t - s))
  unfold pastCoefficient pastProcess increment
  simpa only [Function.comp_def,
    add_tsub_cancel_of_le hst] using hi

omit [IsProbabilityMeasure μ] in
/-- Increments have all Gaussian moments; this records the square-integrable one. -/
theorem increment_memLp (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    MemLp (increment B s t) 2 μ :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
    (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two

omit [IsProbabilityMeasure μ] in
theorem integral_increment (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    (∫ ω, increment B s t ω ∂μ) = 0 := by
  simp only [increment]
  rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
    hB.integral_eval, hB.integral_eval, sub_self]

/-- The variance normalization is elapsed time, not its square or square root. -/
theorem integral_increment_sq (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, increment B s t ω ^ 2 ∂μ) = (t : ℝ) - s := by
  have hc := covariance_self (increment_memLp hB s t).aestronglyMeasurable.aemeasurable
  rw [covariance_eq_sub (increment_memLp hB s t) (increment_memLp hB s t),
    integral_increment hB, mul_zero, sub_zero] at hc
  have hv := (hB.hasLaw_sub t s).variance_eq
  rw [variance_id_gaussianReal] at hv
  have hv' : Var[increment B s t; μ] = |(t : ℝ) - (s : ℝ)| := hv
  rw [abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst)), ← hc] at hv'
  simpa only [pow_two, Pi.mul_apply] using hv'

omit [IsProbabilityMeasure μ] in
/-- Independence of the squared factors supplies genuine integrability of the product square. -/
theorem stepIntegral_sq_integrable (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) {a : (Set.Iic s → ℝ) → ℝ} (ha : Measurable a)
    (hA : MemLp (pastCoefficient B s a) 2 μ) :
    Integrable (fun ω => stepIntegral B s t a ω ^ 2) μ := by
  have hi := (pastCoefficient_indep_increment hB hst ha).comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  convert hi.integrable_mul hA.integrable_sq (increment_memLp hB s t).integrable_sq using 1
  ext ω
  simp [stepIntegral, Function.comp_def, Pi.mul_apply, mul_pow]

omit [IsProbabilityMeasure μ] in
theorem stepIntegral_memLp (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) {a : (Set.Iic s → ℝ) → ℝ} (ha : Measurable a)
    (hA : MemLp (pastCoefficient B s a) 2 μ) : MemLp (stepIntegral B s t a) 2 μ :=
  (memLp_two_iff_integrable_sq
    (hA.aestronglyMeasurable.mul (increment_memLp hB s t).aestronglyMeasurable)).2
    (stepIntegral_sq_integrable hB hst ha hA)

theorem stepIntegral_integrable (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) {a : (Set.Iic s → ℝ) → ℝ} (ha : Measurable a)
    (hA : MemLp (pastCoefficient B s a) 2 μ) : Integrable (stepIntegral B s t a) μ :=
  (stepIntegral_memLp hB hst ha hA).integrable (by norm_num)

omit [IsProbabilityMeasure μ] in
/-- Centering of a genuinely random square-integrable coefficient times its future increment. -/
theorem integral_stepIntegral (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) {a : (Set.Iic s → ℝ) → ℝ} (ha : Measurable a)
    (hA : MemLp (pastCoefficient B s a) 2 μ) :
    (∫ ω, stepIntegral B s t a ω ∂μ) = 0 := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  suffices h : Integrable (stepIntegral B s t a) μ ∧
      (∫ ω, stepIntegral B s t a ω ∂μ) = 0 from h.2
  refine ⟨stepIntegral_integrable hB hst ha hA, ?_⟩
  have hi := (pastCoefficient_indep_increment hB hst ha).integral_fun_mul_eq_mul_integral
    hA.aestronglyMeasurable (increment_memLp hB s t).aestronglyMeasurable
  simpa [stepIntegral, integral_increment hB s t] using hi

/-- The one-step Itô isometry with no boundedness assumption on the past coefficient. -/
theorem integral_stepIntegral_sq (hB : IsPreBrownianReal B μ)
    {s t : ℝ≥0} (hst : s ≤ t) {a : (Set.Iic s → ℝ) → ℝ} (ha : Measurable a)
    (hA : MemLp (pastCoefficient B s a) 2 μ) :
    (∫ ω, stepIntegral B s t a ω ^ 2 ∂μ) =
      ((t : ℝ) - s) * ∫ ω, pastCoefficient B s a ω ^ 2 ∂μ := by
  suffices h : Integrable (fun ω => stepIntegral B s t a ω ^ 2) μ ∧
      (∫ ω, stepIntegral B s t a ω ^ 2 ∂μ) =
        ((t : ℝ) - s) * ∫ ω, pastCoefficient B s a ω ^ 2 ∂μ from h.2
  refine ⟨stepIntegral_sq_integrable hB hst ha hA, ?_⟩
  have hi := (pastCoefficient_indep_increment hB hst ha).comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have he := hi.integral_fun_mul_eq_mul_integral
    hA.integrable_sq.aestronglyMeasurable
    (increment_memLp hB s t).integrable_sq.aestronglyMeasurable
  simpa [stepIntegral, Function.comp_def, mul_pow, integral_increment_sq hB hst,
    mul_comm] using he

omit [IsProbabilityMeasure μ] in
/-- Pairings of two valid elementary integrals are genuinely integrable. -/
theorem stepIntegral_mul_integrable (hB : IsPreBrownianReal B μ)
    {s t r v : ℝ≥0} (hst : s ≤ t) (hrv : r ≤ v)
    {a : (Set.Iic s → ℝ) → ℝ} {b : (Set.Iic r → ℝ) → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hA : MemLp (pastCoefficient B s a) 2 μ) (hC : MemLp (pastCoefficient B r b) 2 μ) :
    Integrable (fun ω => stepIntegral B s t a ω * stepIntegral B r v b ω) μ :=
  (stepIntegral_memLp hB hst ha hA).integrable_mul (stepIntegral_memLp hB hrv hb hC)

omit [IsProbabilityMeasure μ] in
/-- Ordered disjoint predictable steps are orthogonal, even when both coefficients are random. -/
theorem integral_stepIntegral_mul_stepIntegral (hB : IsPreBrownianReal B μ)
    {s t r v : ℝ≥0} (hst : s ≤ t) (htr : t ≤ r) (hrv : r ≤ v)
    {a : (Set.Iic s → ℝ) → ℝ} {b : (Set.Iic r → ℝ) → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hA : MemLp (pastCoefficient B s a) 2 μ) (hC : MemLp (pastCoefficient B r b) 2 μ) :
    (∫ ω, stepIntegral B s t a ω * stepIntegral B r v b ω ∂μ) = 0 := by
  suffices h : Integrable (fun ω => stepIntegral B s t a ω * stepIntegral B r v b ω) μ ∧
      (∫ ω, stepIntegral B s t a ω * stepIntegral B r v b ω ∂μ) = 0 from h.2
  refine ⟨stepIntegral_mul_integrable hB hst hrv ha hb hA hC, ?_⟩
  let c : (Set.Iic r → ℝ) → ℝ := fun z =>
    (a (fun j => z ⟨j, j.property.trans (hst.trans htr)⟩) *
      (z ⟨t, htr⟩ - z ⟨s, hst.trans htr⟩)) * b z
  have hc : Measurable c := by dsimp [c]; fun_prop
  have hcInt : Integrable (pastCoefficient B r c) μ :=
    (stepIntegral_memLp hB hst ha hA).integrable_mul hC
  have hi := (pastCoefficient_indep_increment hB hrv hc).integral_fun_mul_eq_mul_integral
    hcInt.aestronglyMeasurable (increment_memLp hB r v).aestronglyMeasurable
  have hz : (∫ ω, pastCoefficient B r c ω * increment B r v ω ∂μ) = 0 := by
    simpa [integral_increment hB r v] using hi
  calc
    _ = ∫ ω, pastCoefficient B r c ω * increment B r v ω ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change stepIntegral B s t a ω *
            (pastCoefficient B r b ω * increment B r v ω) =
          (stepIntegral B s t a ω * pastCoefficient B r b ω) * increment B r v ω
        ring
    _ = 0 := hz

/-- The time process represented by a single predictable step. -/
def stepProcess (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (a : (Set.Iic s → ℝ) → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  (Set.Ioc s t).indicator (fun _ => pastCoefficient B s a ω) r

omit [IsProbabilityMeasure μ] in
/-- Measurable functions of the coordinate past are measurable in the actual natural filtration. -/
theorem pastCoefficient_measurable_natural (hBm : ∀ t, Measurable (B t))
    (s : ℝ≥0) {a : (Set.Iic s → ℝ) → ℝ} (ha : Measurable a) :
    Measurable[Filtration.natural B (fun t => (hBm t).stronglyMeasurable) s]
      (pastCoefficient B s a) := by
  rw [Filtration.natural_eq_comap]
  exact ha.comp (comap_measurable (pastProcess B s))

omit [IsProbabilityMeasure μ] in
/-- The past-function parametrization covers exactly all real coefficients measurable
for the raw natural filtration; it imposes no finite-coordinate or polynomial restriction. -/
theorem measurable_natural_iff_exists_pastCoefficient (hBm : ∀ t, Measurable (B t))
    (s : ℝ≥0) (A : Ω → ℝ) :
    Measurable[Filtration.natural B (fun t => (hBm t).stronglyMeasurable) s] A ↔
      ∃ a : (Set.Iic s → ℝ) → ℝ, Measurable a ∧ A = pastCoefficient B s a := by
  constructor
  · intro hA
    rw [Filtration.natural_eq_comap] at hA
    obtain ⟨a, ha, he⟩ := hA.exists_eq_measurable_comp
    exact ⟨a, ha, he⟩
  · rintro ⟨a, ha, rfl⟩
    exact pastCoefficient_measurable_natural hBm s ha

/-- The one-step isometry stated directly for every square-integrable coefficient
measurable for the raw natural filtration. -/
theorem integral_natural_step_sq (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {A : Ω → ℝ}
    (hAm : Measurable[Filtration.natural B (fun t => (hBm t).stronglyMeasurable) s] A)
    (hA : MemLp A 2 μ) :
    Integrable (fun ω => (A ω * (B t ω - B s ω)) ^ 2) μ ∧
      (∫ ω, (A ω * (B t ω - B s ω)) ^ 2 ∂μ) =
        ((t : ℝ) - s) * ∫ ω, A ω ^ 2 ∂μ := by
  obtain ⟨a, ha, rfl⟩ :=
    (measurable_natural_iff_exists_pastCoefficient hBm s A).1 hAm
  exact ⟨stepIntegral_sq_integrable hB hst ha hA, integral_stepIntegral_sq hB hst ha hA⟩

omit [IsProbabilityMeasure μ] in
/-- The actual step process is strongly predictable for the natural filtration.
No path continuity or coefficient boundedness is needed. -/
theorem stepProcess_stronglyPredictable (hBm : ∀ t, Measurable (B t))
    (s t : ℝ≥0) {a : (Set.Iic s → ℝ) → ℝ} (ha : Measurable a) :
    IsStronglyPredictable (Filtration.natural B (fun t => (hBm t).stronglyMeasurable))
      (stepProcess B s t a) := by
  let 𝓕 := Filtration.natural B (fun t => (hBm t).stronglyMeasurable)
  have hA : Measurable[𝓕 s] (pastCoefficient B s a) :=
    pastCoefficient_measurable_natural hBm s ha
  have hm : @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable _
      (Function.uncurry (stepProcess B s t a)) := by
    intro U hU
    have hAU := measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) s t (hA hU)
    have hI := measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) s t
      (s := (Set.univ : Set Ω)) MeasurableSet.univ
    by_cases hz : (0 : ℝ) ∈ U
    · convert hAU.union hI.compl using 1
      ext z
      by_cases hr : z.1 ∈ Set.Ioc s t <;>
        simp [stepProcess, Function.uncurry, Set.indicator, hr, hz]
    · convert hAU using 1
      ext z
      by_cases hr : z.1 ∈ Set.Ioc s t <;>
        simp [stepProcess, Function.uncurry, Set.indicator, hr, hz]
  exact hm.stronglyMeasurable

/-- The actual finite sum of predictable-step integrals along a deterministic time partition. -/
def partitionIntegral {n : ℕ} (B : ℝ≥0 → Ω → ℝ) (τ : Fin (n + 1) → ℝ≥0)
    (a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ) (ω : Ω) : ℝ :=
  ∑ i, stepIntegral B (τ i.castSucc) (τ i.succ) (a i) ω

/-- The actual random predictable integrand attached to the finite increment sum. -/
def partitionProcess {n : ℕ} (B : ℝ≥0 → Ω → ℝ) (τ : Fin (n + 1) → ℝ≥0)
    (a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, stepProcess B (τ i.castSucc) (τ i.succ) (a i) r ω

omit [IsProbabilityMeasure μ] in
/-- A finite sum of the constructed steps is strongly predictable in the natural filtration. -/
theorem partitionProcess_stronglyPredictable (hBm : ∀ t, Measurable (B t))
    {n : ℕ} (τ : Fin (n + 1) → ℝ≥0)
    {a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ}
    (ha : ∀ i, Measurable (a i)) :
    IsStronglyPredictable (Filtration.natural B (fun t => (hBm t).stronglyMeasurable))
      (partitionProcess B τ a) := by
  let 𝓕 := Filtration.natural B (fun t => (hBm t).stronglyMeasurable)
  have hs (i : Fin n) : StronglyMeasurable[𝓕.predictable]
      (fun z : ℝ≥0 × Ω => stepProcess B (τ i.castSucc) (τ i.succ) (a i) z.1 z.2) :=
    stepProcess_stronglyPredictable hBm (τ i.castSucc) (τ i.succ) (ha i)
  change StronglyMeasurable[𝓕.predictable] (fun z : ℝ≥0 × Ω =>
    ∑ i : Fin n, stepProcess B (τ i.castSucc) (τ i.succ) (a i) z.1 z.2)
  exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ => hs i)

omit [IsProbabilityMeasure μ] in
/-- The finite integral is genuinely square integrable. Repeated times and an empty
partition are allowed. -/
theorem partitionIntegral_memLp (hB : IsPreBrownianReal B μ)
    {n : ℕ} {τ : Fin (n + 1) → ℝ≥0} (hτ : Monotone τ)
    {a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ}
    (ha : ∀ i, Measurable (a i))
    (hA : ∀ i, MemLp (pastCoefficient B (τ i.castSucc) (a i)) 2 μ) :
    MemLp (partitionIntegral B τ a) 2 μ := by
  exact memLp_finsetSum Finset.univ fun i _ =>
    stepIntegral_memLp hB (hτ (Fin.castSucc_le_succ i)) (ha i) (hA i)

/-- Centering of the finite predictable integral. -/
theorem integral_partitionIntegral (hB : IsPreBrownianReal B μ)
    {n : ℕ} {τ : Fin (n + 1) → ℝ≥0} (hτ : Monotone τ)
    {a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ}
    (ha : ∀ i, Measurable (a i))
    (hA : ∀ i, MemLp (pastCoefficient B (τ i.castSucc) (a i)) 2 μ) :
    (∫ ω, partitionIntegral B τ a ω ∂μ) = 0 := by
  unfold partitionIntegral
  rw [integral_finsetSum _ (fun i _ =>
    stepIntegral_integrable hB (hτ (Fin.castSucc_le_succ i)) (ha i) (hA i))]
  exact Finset.sum_eq_zero fun i _ =>
    integral_stepIntegral hB (hτ (Fin.castSucc_le_succ i)) (ha i) (hA i)

/-- The Itô isometry for finite predictable steps with arbitrary square-integrable
past-measurable coefficients. No independence of the coefficients is assumed. -/
theorem integral_partitionIntegral_sq (hB : IsPreBrownianReal B μ)
    {n : ℕ} {τ : Fin (n + 1) → ℝ≥0} (hτ : Monotone τ)
    {a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ}
    (ha : ∀ i, Measurable (a i))
    (hA : ∀ i, MemLp (pastCoefficient B (τ i.castSucc) (a i)) 2 μ) :
    (∫ ω, partitionIntegral B τ a ω ^ 2 ∂μ) =
      ∑ i, ((τ i.succ : ℝ) - τ i.castSucc) *
        ∫ ω, pastCoefficient B (τ i.castSucc) (a i) ω ^ 2 ∂μ := by
  let X (i : Fin n) := stepIntegral B (τ i.castSucc) (τ i.succ) (a i)
  have hX (i : Fin n) : MemLp (X i) 2 μ :=
    stepIntegral_memLp hB (hτ (Fin.castSucc_le_succ i)) (ha i) (hA i)
  have hij (i j : Fin n) (hne : i ≠ j) : (∫ ω, X i ω * X j ω ∂μ) = 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact integral_stepIntegral_mul_stepIntegral hB
        (hτ (Fin.castSucc_le_succ i)) (hτ hlt)
        (hτ (Fin.castSucc_le_succ j)) (ha i) (ha j) (hA i) (hA j)
    · have he := integral_stepIntegral_mul_stepIntegral hB
        (hτ (Fin.castSucc_le_succ j)) (hτ hlt)
        (hτ (Fin.castSucc_le_succ i)) (ha j) (ha i) (hA j) (hA i)
      simpa only [mul_comm] using he
  calc
    _ = ∫ ω, ∑ i, ∑ j, X i ω * X j ω ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        simp only [partitionIntegral, pow_two, Finset.sum_mul, Finset.mul_sum, X]
        rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∫ ω, X i ω * X j ω ∂μ := by
      have hXX (i j : Fin n) : Integrable (fun ω => X i ω * X j ω) μ :=
        (hX i).integrable_mul (hX j)
      have ho (i : Fin n) : Integrable (fun ω => ∑ j, X i ω * X j ω) μ :=
        integrable_finsetSum _ (fun j _ => hXX i j)
      rw [integral_finsetSum _ (fun i _ => ho i)]
      congr 1
      ext i
      exact integral_finsetSum _ (fun j _ => hXX i j)
    _ = ∑ i, ∫ ω, X i ω ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp only [pow_two]
      · intro j _ hji
        exact hij i j hji.symm
      · simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_stepIntegral_sq hB (hτ (Fin.castSucc_le_succ i)) (ha i) (hA i)

end OperatorDerivativeRewrite.Foundation.GaussianPredictableStep
