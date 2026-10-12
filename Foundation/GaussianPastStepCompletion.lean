import Foundation.GaussianTimePastDensity
import Foundation.GaussianPredictableL2Completion
import Foundation.GaussianTimeStepIntegral

/-! Arbitrary square-integrable past coefficients belong to the existing
closed polynomial predictable-step domain. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPastStepCompletion
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeDivergence
open GaussianTimeProductL2 GaussianPredictableL2Completion GaussianTimePastDensity
attribute [local instance] timeHilbert_secondCountable

/-- Tensoring with a fixed time function is linear on actual L2 classes. -/
def productTensorLinear (h : TimeHilbert) : GaussianL2 →ₗ[ℝ] TimeProbabilityL2 where
  toFun := productTensor h
  map_add' A B := by
    apply Lp.ext
    have hab := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (Lp.coeFn_add A B)
    filter_upwards [productTensor_coeFn h (A+B), productTensor_coeFn h A,
      productTensor_coeFn h B, Lp.coeFn_add (productTensor h A) (productTensor h B), hab]
      with z hs ha hb he hab
    change productTensor h (A+B) z = (productTensor h A + productTensor h B) z
    simp only [Function.comp_apply, Pi.add_apply] at hab
    rw [hs, he]
    simp only [Pi.add_apply, ha, hb, hab]
    exact mul_add _ _ _
  map_smul' c A := by
    apply Lp.ext
    have hca := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (Lp.coeFn_smul c A)
    filter_upwards [productTensor_coeFn h (c • A), productTensor_coeFn h A,
      Lp.coeFn_smul c (productTensor h A), hca] with z hs ha he hca
    change productTensor h (c • A) z = (c • productTensor h A) z
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hca
    rw [hs, he]
    simp only [Pi.smul_apply, smul_eq_mul, ha, hca]
    ring

theorem productTensor_norm (h : TimeHilbert) (A : GaussianL2) :
    ‖productTensor h A‖ = ‖h‖ * ‖A‖ := by
  have he := productTensor_inner h h A A
  simp only [real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (productTensor h A), norm_nonneg h, norm_nonneg A,
    mul_nonneg (norm_nonneg h) (norm_nonneg A)]

/-- Continuity is proved from product integration, not postulated. -/
def productTensorContinuous (h : TimeHilbert) : GaussianL2 →L[ℝ] TimeProbabilityL2 :=
  (productTensorLinear h).mkContinuous ‖h‖ (fun A => (productTensor_norm h A).le)

/-- No boundedness or derivative assumption on the past coefficient is needed. -/
theorem past_step_mem_closedProductSteps (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    productTensor (intervalVector s t) A ∈ closedProductSteps := by
  let T := productTensorContinuous (intervalVector s t)
  have hc : A ∈ (pastPolynomialEmbedding s).range.topologicalClosure := by
    rw [pastPolynomial_closure]
    exact hA
  have hp : (pastPolynomialEmbedding s).range.topologicalClosure ≤
      closedProductSteps.comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro F ⟨p, rfl⟩
      obtain ⟨v, q, rfl⟩ := MvPolynomial.exists_finset_rename p
      change productTensor (intervalVector s t)
        (familyPolynomialEmbedding
          (fun r : Set.Iic s => SeparableHilbertEmbedding.hilbertEmbedding TimeHilbert
            (timeVector r)) (MvPolynomial.rename Subtype.val q)) ∈ closedProductSteps
      rw [familyPolynomial_rename]
      let e := Fintype.equivFin v
      let r : v → ℝ≥0 := fun i => i.val
      have he := pastCoefficient_equiv e r q
      have hm := (productAssembly (stepRelation (Fintype.card v)
        (r ∘ e.symm) (MvPolynomial.rename e q) s t
        (fun i => (e.symm i).val.property) hst)).property
      change productTensor (intervalVector s t)
        (pastCoefficient (r ∘ e.symm) (MvPolynomial.rename e q)) ∈ closedProductSteps at hm
      rw [he] at hm
      exact hm
    · exact productStepSpan.isClosed_topologicalClosure.preimage T.continuous
  exact hp hc

/-- The existing completed integral now accepts arbitrary L2 past steps. -/
def pastStep (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) : closedProductSteps :=
  ⟨productTensor (intervalVector s t) A, past_step_mem_closedProductSteps s t hst A hA⟩

/-- Finite partitions with arbitrary L2 past coefficients are in the old domain. -/
theorem past_partition_mem_closedProductSteps {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) (A : Fin n → GaussianL2)
    (hA : ∀ i, AEStronglyMeasurable[naturalFiltration (τ i.castSucc)] (A i) gaussianProduct) :
    partitionL2 τ A ∈ closedProductSteps := by
  apply Submodule.sum_mem
  intro i _
  exact past_step_mem_closedProductSteps _ _ (hτ (Fin.castSucc_le_succ i)) (A i) (hA i)

/-- The independence estimate extends to a.e. past-measurable L2 classes by
choosing a measurable version; it is not an all-L2 multiplication assertion. -/
theorem past_increment_sq (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    Integrable (fun ω => (A ω * (process t ω - process s ω)) ^ 2) gaussianProduct ∧
      (∫ ω, (A ω * (process t ω - process s ω)) ^ 2 ∂gaussianProduct) =
        ((t : ℝ) - s) * ∫ ω, A ω ^ 2 ∂gaussianProduct := by
  have hp := timeStep_integrable_sq_and_isometry hst hA.stronglyMeasurable_mk.measurable
    ((Lp.memLp A).ae_eq hA.ae_eq_mk)
  have he : (fun ω => (A ω * (process t ω - process s ω)) ^ 2) =ᵐ[gaussianProduct]
      (fun ω => (hA.mk A ω * (process t ω - process s ω)) ^ 2) := by
    filter_upwards [hA.ae_eq_mk] with ω he
    rw [he]
  refine ⟨hp.1.congr he.symm, ?_⟩
  rw [integral_congr_ae he, hp.2]
  congr 1
  apply integral_congr_ae
  filter_upwards [hA.ae_eq_mk] with ω he
  rw [he]

theorem past_increment_memLp (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    MemLp (fun ω => A ω * (process t ω - process s ω)) 2 gaussianProduct :=
  (memLp_two_iff_integrable_sq ((Lp.stronglyMeasurable A).mul
    ((process_stronglyMeasurable t).sub (process_stronglyMeasurable s))).aestronglyMeasurable).2
    (past_increment_sq s t hst A hA).1

/-- The actual product with the increment, constructed only after integrability. -/
def pastIncrement (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) : GaussianL2 :=
  (past_increment_memLp s t hst A hA).toLp _

theorem pastIncrement_coeFn (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    pastIncrement s t hst A hA =ᵐ[gaussianProduct]
      fun ω => A ω * (process t ω - process s ω) := MemLp.coeFn_toLp _

theorem pastIncrement_norm (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    ‖pastIncrement s t hst A hA‖ = ‖intervalVector s t‖ * ‖A‖ := by
  have hnorm (B : GaussianL2) : ‖B‖ ^ 2 = ∫ ω, B ω ^ 2 ∂gaussianProduct := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
    simp only [Real.inner_apply, pow_two]
  have hi : ‖intervalVector s t‖ ^ 2 = (t : ℝ) - s := by
    rw [← timeVector_sub s t hst]
    exact timeVector_sub_norm_sq s t hst
  have he : ‖pastIncrement s t hst A hA‖ ^ 2 = ((t : ℝ) - s) * ‖A‖ ^ 2 := by
    rw [hnorm, hnorm]
    calc
      _ = ∫ ω, (A ω * (process t ω - process s ω)) ^ 2 ∂gaussianProduct := by
        apply integral_congr_ae
        filter_upwards [pastIncrement_coeFn s t hst A hA] with ω he
        rw [he]
      _ = _ := (past_increment_sq s t hst A hA).2
  rw [← hi] at he
  nlinarith [norm_nonneg (pastIncrement s t hst A hA),
    mul_nonneg (norm_nonneg (intervalVector s t)) (norm_nonneg A)]

theorem pastIncrement_sub (s t : ℝ≥0) (hst : s ≤ t) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    pastIncrement s t hst A hA - pastIncrement s t hst B hB =
      pastIncrement s t hst (A-B) ((hA.sub hB).congr (Lp.coeFn_sub A B).symm) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (pastIncrement s t hst A hA) (pastIncrement s t hst B hB),
    pastIncrement_coeFn s t hst A hA, pastIncrement_coeFn s t hst B hB,
    pastIncrement_coeFn s t hst (A-B) ((hA.sub hB).congr (Lp.coeFn_sub A B).symm),
    Lp.coeFn_sub A B]
    with ω he ha hb hd hab
  simp only [Pi.sub_apply] at he hab
  rw [he, ha, hb, hd, hab]
  ring

theorem past_polynomial_measurable {n : ℕ} (s : ℝ≥0) (r : Fin n → ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ) :
    AEStronglyMeasurable[naturalFiltration s] (pastCoefficient r p : GaussianL2)
      gaussianProduct := by
  have hp := isonormalPolynomial_aestronglyMeasurable
    (fun i => SeparableHilbertEmbedding.hilbertEmbedding TimeHilbert (timeVector (r i))) p
  exact hp.mono (GaussianTimeObservationDensity.observationSigma_le_natural s
    (fun i => ⟨r i, hrs i⟩))

theorem productIntegral_pastStep_polynomial {n : ℕ} (r : Fin n → ℝ≥0)
    (p : MvPolynomial (Fin n) ℝ) (s t : ℝ≥0) (hrs : ∀ i, r i ≤ s) (hst : s ≤ t)
    (hB : AEStronglyMeasurable[naturalFiltration s] (pastCoefficient r p : GaussianL2)
      gaussianProduct) :
    productIntegral (pastStep s t hst (pastCoefficient r p) hB) =
      pastIncrement s t hst (pastCoefficient r p) hB := by
  have he : pastStep s t hst (pastCoefficient r p) hB =
      productAssembly (stepRelation n r p s t hrs hst) := rfl
  rw [he, productIntegral_step]
  apply Lp.ext
  filter_upwards [incrementProductL2_coeFn r p s t,
    pastIncrement_coeFn s t hst (pastCoefficient r p) hB, pastCoefficient_coeFn r p]
    with ω hl hr hp
  rw [hl, hr, hp]

/-- Continuity and genuine full-past polynomial density identify the OLD
completed integral with the actual product for every L2 past coefficient. -/
theorem productIntegral_pastStep (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    productIntegral (pastStep s t hst A hA) = pastIncrement s t hst A hA := by
  apply eq_of_forall_dist_le
  intro ε hε
  let C := ‖intervalVector s t‖
  have hC : 0 ≤ C := norm_nonneg _
  have hd : 0 < 2*C+1 := by positivity
  obtain ⟨n, r, p, hrs, hp⟩ := exists_fin_pastPolynomial_approx s A hA
    (ε / (2*C+1)) (div_pos hε hd)
  let B : GaussianL2 := pastCoefficient r p
  have hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct :=
    past_polynomial_measurable s r hrs p
  have hI := productIntegral_pastStep_polynomial r p s t hrs hst hB
  have he : ‖productIntegral (pastStep s t hst A hA) -
      productIntegral (pastStep s t hst B hB)‖ = C * ‖A-B‖ := by
    rw [← map_sub, productIntegral_norm]
    change ‖productTensorLinear (intervalVector s t) A -
      productTensorLinear (intervalVector s t) B‖ = _
    rw [← map_sub]
    exact productTensor_norm _ _
  have ht := norm_sub_le_norm_sub_add_norm_sub (productIntegral (pastStep s t hst A hA))
    (productIntegral (pastStep s t hst B hB)) (pastIncrement s t hst A hA)
  rw [he, hI, norm_sub_rev (pastIncrement s t hst B hB),
    pastIncrement_sub, pastIncrement_norm] at ht
  rw [dist_eq_norm]
  have hp' : ‖A-B‖ * (2*C+1) < ε := (lt_div_iff₀ hd).mp hp
  change _ ≤ C * ‖A-B‖ + C * ‖A-B‖ at ht
  nlinarith [norm_nonneg (A-B)]

theorem productIntegral_pastStep_coeFn (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    productIntegral (pastStep s t hst A hA) =ᵐ[gaussianProduct]
      fun ω => A ω * (process t ω - process s ω) := by
  rw [productIntegral_pastStep]
  exact pastIncrement_coeFn s t hst A hA

/-- Arbitrary square-integrable past coefficients on a finite time partition,
as elements of the previously constructed integral domain. -/
def pastPartition {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (A : Fin n → GaussianL2)
    (hA : ∀ i, AEStronglyMeasurable[naturalFiltration (τ i.castSucc)] (A i) gaussianProduct) :
    closedProductSteps :=
  ∑ i : Fin n, pastStep (τ i.castSucc) (τ i.succ)
    (hτ (Fin.castSucc_le_succ i)) (A i) (hA i)

attribute [local irreducible] naturalFiltration
theorem pastPartition_coe {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (A : Fin n → GaussianL2)
    (hA : ∀ i, AEStronglyMeasurable[naturalFiltration (τ i.castSucc)] (A i) gaussianProduct) :
    (pastPartition τ hτ A hA : TimeProbabilityL2) = partitionL2 τ A := by
  simp only [pastPartition, Submodule.coe_sum, pastStep, partitionL2]

/-- Agreement with the elementary stochastic sum for all L2 past coefficients. -/
theorem productIntegral_pastPartition_coeFn {n : ℕ} (τ : Fin (n + 1) → ℝ≥0)
    (hτ : Monotone τ) (A : Fin n → GaussianL2)
    (hA : ∀ i, AEStronglyMeasurable[naturalFiltration (τ i.castSucc)] (A i) gaussianProduct) :
    productIntegral (pastPartition τ hτ A hA) =ᵐ[gaussianProduct]
      fun ω => ∑ i, A i ω * (process (τ i.succ) ω - process (τ i.castSucc) ω) := by
  rw [pastPartition, map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n =>
      productIntegral (pastStep (τ i.castSucc) (τ i.succ)
        (hτ (Fin.castSucc_le_succ i)) (A i) (hA i))),
    Filter.eventually_all.2 (fun i : Fin n =>
      productIntegral_pastStep_coeFn (τ i.castSucc) (τ i.succ)
      (hτ (Fin.castSucc_le_succ i)) (A i) (hA i))] with ω hsum hi
  rw [hsum]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => hi i)

end OperatorDerivativeRewrite.Foundation.GaussianPastStepCompletion
