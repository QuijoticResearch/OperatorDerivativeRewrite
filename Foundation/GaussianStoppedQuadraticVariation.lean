import Foundation.GaussianStoppedSmoothFields
import Foundation.GaussianWeightedQuadraticVariation

/-! Mixed weighted quadratic variation for actual stopped Brownian coordinates
on partitions aligned with the stopping horizons. Alignment is an explicit
geometric condition, not a quadratic-variation or convergence assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianStoppedQuadraticVariation
open InfiniteGaussian GaussianTimeProcess GaussianStoppedComposition
open GaussianPredictableStep GaussianWeightedQuadraticVariation GaussianBrownianQuadraticVariation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Whether a coordinate is active throughout an aligned cell ending at t. -/
def active (t r : ℝ≥0) : ℝ := if t ≤ r then 1 else 0

theorem stopped_increment (s t r : ℝ≥0) (hst : s ≤ t)
    (halign : r ≤ s ∨ t ≤ r) (ω : SampleSpace) :
    process (min t r) ω - process (min s r) ω =
      active t r * (process t ω - process s ω) := by
  by_cases ht : t ≤ r
  · simp [active, ht, min_eq_left ht, min_eq_left (hst.trans ht)]
  · have hr : r ≤ s := halign.resolve_right ht
    simp [active, ht, min_eq_right hr, min_eq_right (hr.trans hst)]

theorem stopped_time_increment (s t r : ℝ≥0) (hst : s ≤ t)
    (halign : r ≤ s ∨ t ≤ r) :
    ((min t r : ℝ≥0):ℝ) - min s r = active t r * ((t:ℝ)-s) := by
  by_cases ht : t ≤ r
  · simp [active, ht, min_eq_left ht, min_eq_left (hst.trans ht)]
  · have hr : r ≤ s := halign.resolve_right ht
    simp [active, ht, min_eq_right hr, min_eq_right (hr.trans hst)]

theorem active_mul (t r q : ℝ≥0) : active t r * active t q = active t (min r q) := by
  by_cases hr : t ≤ r <;> by_cases hq : t ≤ q <;> simp [active, hr, hq, le_min_iff]

theorem min_aligned (s t r q : ℝ≥0) (hr : r ≤ s ∨ t ≤ r) (hq : q ≤ s ∨ t ≤ q) :
    min r q ≤ s ∨ t ≤ min r q := by
  rcases hr with hr | hr
  · exact Or.inl ((min_le_left _ _).trans hr)
  · rcases hq with hq | hq
    · exact Or.inl ((min_le_right _ _).trans hq)
    · exact Or.inr (le_min hr hq)

theorem covariance_cell (s t r q : ℝ≥0) (hst : s ≤ t)
    (hr : r ≤ s ∨ t ≤ r) (hq : q ≤ s ∨ t ≤ q) :
    active t r * active t q * ((t:ℝ)-s) =
      ((min t (min r q):ℝ≥0):ℝ) - min s (min r q) := by
  rw [active_mul]
  exact (stopped_time_increment s t (min r q) hst (min_aligned s t r q hr hq)).symm

/-- Coefficients depend measurably on actual past coordinates. -/
def weight (Φ : (ι → ℝ) → ℝ) (r : ι → ℝ≥0) (s t p q : ℝ≥0)
    (v : Iic s → ℝ) : ℝ :=
  Φ (fun i => v ⟨min s (r i), by exact min_le_left s (r i)⟩) * active t p * active t q

theorem weight_measurable {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ)
    (r : ι → ℝ≥0) (s t p q : ℝ≥0) : Measurable (weight Φ r s t p q) :=
  ((hΦ.measurable.comp (Measurable.of_eval (fun i => measurable_pi_apply
    (⟨min s (r i), by exact min_le_left s (r i)⟩ : Iic s)))).mul_const _).mul_const _

theorem weight_bound {Φ : (ι → ℝ) → ℝ} {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) (s t p q : ℝ≥0) (v : Iic s → ℝ) : ‖weight Φ r s t p q v‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg (Φ 0)).trans (hM 0)
  by_cases hp : t ≤ p <;> by_cases hq : t ≤ q <;>
    simp only [weight, active, hp, hq, ite_true, ite_false, mul_one, mul_zero, norm_zero]
  · exact hM _
  all_goals exact hM0

theorem weight_memLp {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) (s t p q : ℝ≥0) :
    MemLp (pastCoefficient process s (weight Φ r s t p q)) 2 gaussianProduct := by
  apply MemLp.of_bound (C := M)
  · exact ((weight_measurable hΦ r s t p q).comp
      (Measurable.of_eval (fun x => (process_stronglyMeasurable x).measurable))).aestronglyMeasurable
  · exact Eventually.of_forall (fun ω => weight_bound hM r s t p q _)

theorem weight_energy {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) (s t p q : ℝ≥0) :
    (∫ ω, pastCoefficient process s (weight Φ r s t p q) ω ^ 2 ∂gaussianProduct) ≤ M^2 := by
  have h : ∀ ω, pastCoefficient process s (weight Φ r s t p q) ω ^ 2 ≤ M^2 := by
    intro ω
    have hb := pow_le_pow_left₀ (norm_nonneg _) (weight_bound hM r s t p q (pastProcess process s ω)) 2
    simpa only [pastCoefficient, Real.norm_eq_abs, sq_abs] using hb
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
    integral_mono (weight_memLp hΦ hM r s t p q).integrable_sq (integrable_const (M^2)) h

def mixedError {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (p q : ℝ≥0) : GaussianL2 :=
  weightedError τ (fun i => weight Φ r (τ i.castSucc) (τ i.succ) p q)
    (fun i => weight_measurable hΦ r _ _ _ _) (fun i => weight_memLp hΦ hM r _ _ _ _)

/-- The actual mixed-increment error; independent of the L2 construction. -/
def rawMixedError (Φ : (ι → ℝ) → ℝ) (r : ι → ℝ≥0) {n : ℕ}
    (τ : Fin (n+1) → ℝ≥0) (p q : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∑ i : Fin n, Φ (coordinates r (τ i.castSucc) ω) *
    ((process (min (τ i.succ) p) ω - process (min (τ i.castSucc) p) ω) *
      (process (min (τ i.succ) q) ω - process (min (τ i.castSucc) q) ω) -
      (((min (τ i.succ) (min p q):ℝ≥0):ℝ) - min (τ i.castSucc) (min p q)))
theorem mixedError_coeFn {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (p q : ℝ≥0)
    (hp : ∀ i : Fin n, p ≤ τ i.castSucc ∨ τ i.succ ≤ p)
    (hq : ∀ i : Fin n, q ≤ τ i.castSucc ∨ τ i.succ ≤ q) :
    mixedError hΦ hM r τ p q =ᵐ[gaussianProduct] fun ω => ∑ i : Fin n,
      Φ (coordinates r (τ i.castSucc) ω) *
        ((process (min (τ i.succ) p) ω - process (min (τ i.castSucc) p) ω) *
          (process (min (τ i.succ) q) ω - process (min (τ i.castSucc) q) ω) -
          (((min (τ i.succ) (min p q):ℝ≥0):ℝ) - min (τ i.castSucc) (min p q))) := by
  filter_upwards [weightedError_coeFn τ hτ
    (fun i => weight Φ r (τ i.castSucc) (τ i.succ) p q)
    (fun i => weight_measurable hΦ r _ _ _ _) (fun i => weight_memLp hΦ hM r _ _ _ _)] with ω he
  change mixedError hΦ hM r τ p q ω = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [stopped_increment _ _ p (hτ (Fin.castSucc_le_succ i)) (hp i),
    stopped_increment _ _ q (hτ (Fin.castSucc_le_succ i)) (hq i),
    ← covariance_cell _ _ p q (hτ (Fin.castSucc_le_succ i)) (hp i) (hq i)]
  simp only [pastCoefficient, pastProcess, weight]
  unfold GaussianStoppedComposition.coordinates
  ring

theorem mixedError_mesh_bound {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (p q : ℝ≥0)
    (ε : ℝ) (hmesh : ∀ i : Fin n, (τ i.succ:ℝ)-τ i.castSucc ≤ ε) :
    ‖mixedError hΦ hM r τ p q‖^2 ≤ 2*M^2*ε*((τ (Fin.last n):ℝ)-τ 0) :=
  weightedError_mesh_bound τ hτ _ _ _ (M^2) ε (sq_nonneg _)
    (fun i => weight_energy hΦ hM r _ _ _ _) hmesh

theorem mixedError_tendsto {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (p q : ℝ≥0) (L : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ N, 0 ≤ ε N) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (i : Fin (m N)), (τ N i.succ:ℝ)-τ N i.castSucc ≤ ε N)
    (hlength : ∀ N, (τ N (Fin.last (m N)):ℝ)-τ N 0 ≤ L) :
    Tendsto (fun N => mixedError hΦ hM r (τ N) p q) atTop (𝓝 0) :=
  weightedError_tendsto_of_mesh m τ hτ _ _ _ (M^2) L (sq_nonneg _) ε hε hlim
    (fun N i => weight_energy hΦ hM r _ _ _ _) hmesh hlength

theorem rawMixedError_memLp {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (p q : ℝ≥0)
    (hp : ∀ i : Fin n, p ≤ τ i.castSucc ∨ τ i.succ ≤ p)
    (hq : ∀ i : Fin n, q ≤ τ i.castSucc ∨ τ i.succ ≤ q) :
    MemLp (rawMixedError Φ r τ p q) 2 gaussianProduct :=
  (Lp.memLp _).ae_eq (mixedError_coeFn hΦ hM r τ hτ p q hp hq)

theorem rawMixedError_integral_sq {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (p q : ℝ≥0)
    (hp : ∀ i : Fin n, p ≤ τ i.castSucc ∨ τ i.succ ≤ p)
    (hq : ∀ i : Fin n, q ≤ τ i.castSucc ∨ τ i.succ ≤ q) :
    (∫ ω, rawMixedError Φ r τ p q ω ^ 2 ∂gaussianProduct) = ‖mixedError hΦ hM r τ p q‖^2 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [mixedError_coeFn hΦ hM r τ hτ p q hp hq] with ω he
  change _ = rawMixedError Φ r τ p q ω at he
  rw [he]
  simp [Real.norm_eq_abs, sq_abs]

/-- Genuine mean-square convergence of the raw mixed weighted error on an
aligned refining mesh, with square integrability established above. -/
theorem rawMixedError_sq_tendsto {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ x, ‖Φ x‖ ≤ M)
    (r : ι → ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (p q : ℝ≥0) (L : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ N, 0 ≤ ε N) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (i : Fin (m N)), (τ N i.succ:ℝ)-τ N i.castSucc ≤ ε N)
    (hlength : ∀ N, (τ N (Fin.last (m N)):ℝ)-τ N 0 ≤ L)
    (hp : ∀ N (i : Fin (m N)), p ≤ τ N i.castSucc ∨ τ N i.succ ≤ p)
    (hq : ∀ N (i : Fin (m N)), q ≤ τ N i.castSucc ∨ τ N i.succ ≤ q) :
    Tendsto (fun N => ∫ ω, rawMixedError Φ r (τ N) p q ω ^ 2 ∂gaussianProduct) atTop (𝓝 0) := by
  simp_rw [rawMixedError_integral_sq hΦ hM r _ (hτ _) p q (hp _) (hq _)]
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using
    ((mixedError_tendsto hΦ hM r m τ hτ p q L ε hε hlim hmesh hlength).norm.pow 2)
end OperatorDerivativeRewrite.Foundation.GaussianStoppedQuadraticVariation
