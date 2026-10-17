import Foundation.FourierPathStopping

/-! Actual contractive transport between Fourier dictionaries, including dyadic stopping. -/
noncomputable section
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathDictionaryTransport
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach FourierPathStopping

section Transport
variable (levels targetLevels : ℕ → ℕ)
  (ξ : (i : ℕ) → Grid (levels i)) (η : (i : ℕ) → Grid (targetLevels i))
  (Φ : Path → Path)
  (hΦ : ∀ i path, characterTest targetLevels η i path = characterTest levels ξ i (Φ path))
include hΦ

theorem realization_pullback (a : Coeff) (path : Path) :
    realization targetLevels η a path = realization levels ξ a (Φ path) := by
  simp only [realization_apply, HigherHeatMixedFourierPaths.series]
  apply tsum_congr
  intro i
  exact congrArg (fun z : ℂ => a i * z) (hΦ i path)

theorem kernel_transport : kernel levels ξ ≤ ((kernel targetLevels η).mkQL).ker := by
  intro a ha
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change realization targetLevels η a = 0
  change realization levels ξ a = 0 at ha
  ext path
  rw [realization_pullback levels targetLevels ξ η Φ hΦ, ha]
  rfl

def transport : TestSpace levels ξ →L[ℂ] TestSpace targetLevels η :=
  (kernel levels ξ).liftQL (kernel targetLevels η).mkQL
    (kernel_transport levels targetLevels ξ η Φ hΦ)

theorem transport_mk (a : Coeff) :
    transport levels targetLevels ξ η Φ hΦ ((kernel levels ξ).mkQ a) =
      (kernel targetLevels η).mkQ a := rfl

theorem realize_transport (q : TestSpace levels ξ) (path : Path) :
    realize targetLevels η (transport levels targetLevels ξ η Φ hΦ q) path =
      realize levels ξ q (Φ path) := by
  obtain ⟨a, rfl⟩ := (kernel levels ξ).mkQ_surjective q
  exact realization_pullback levels targetLevels ξ η Φ hΦ a path

theorem transport_bound (q : TestSpace levels ξ) :
    ‖transport levels targetLevels ξ η Φ hΦ q‖ ≤ ‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, ha, hna⟩ := Submodule.Quotient.norm_mk_lt q hε
  have he : transport levels targetLevels ξ η Φ hΦ q = (kernel targetLevels η).mkQ a := by
    rw [← ha]
    rfl
  rw [he]
  exact (Submodule.Quotient.norm_mk_le _ _).trans hna.le

theorem transport_norm : ‖transport levels targetLevels ξ η Φ hΦ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  simpa only [one_mul] using transport_bound levels targetLevels ξ η Φ hΦ q

end Transport

def collapse {n : ℕ} (r : Fin (gridSize n) → Fin (gridSize n)) (ξ : Grid n) : Grid n :=
  fun j => ∑ i, if r i = j then ξ i else 0

theorem collapse_phase {n : ℕ} (r : Fin (gridSize n) → Fin (gridSize n))
    (ξ y : Grid n) : SignedDensityIntegral.configurationPhase (collapse r ξ) y =
      SignedDensityIntegral.configurationPhase ξ (fun i => y (r i)) := by
  classical
  have he : (∑ j, collapse r ξ j * y j) = ∑ i, ξ i * y (r i) := by
    simp only [collapse, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ite_mul, zero_mul]
    simp
  unfold SignedDensityIntegral.configurationPhase
  rw [he]

theorem sampleTime_monotone (n : ℕ) : Monotone (sampleTime n) := by
  intro i j hij
  change (time 1 n i : ℝ) ≤ (time 1 n j : ℝ)
  have hn : (i.val+1 : ℝ≥0) ≤ (j.val+1 : ℝ≥0) := by
    exact_mod_cast Nat.add_le_add_right hij 1
  exact_mod_cast mul_le_mul_of_nonneg_right hn (show 0 ≤ duration 1 n from bot_le)

def stoppingTime (n : ℕ) (k : Fin (gridSize n)) : ℝ≥0 := time 1 n k

theorem sample_stop (n : ℕ) (k i : Fin (gridSize n)) (path : Path) :
    sample n (stop (stoppingTime n k) path) i = sample n path (min i k) := by
  change path.val (min (sampleTime n i) (sampleTime n k)) =
    path.val (sampleTime n (min i k))
  rw [(sampleTime_monotone n).map_min]

def stoppedFrequency (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))
    (k : (i : ℕ) → Fin (gridSize (levels i))) : (i : ℕ) → Grid (levels i) :=
  fun i => collapse (fun j => min j (k i)) (ξ i)

theorem stopped_character (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))
    (k : (i : ℕ) → Fin (gridSize (levels i))) (t : ℝ≥0)
    (ht : ∀ i, stoppingTime (levels i) (k i) = t) (j : ℕ) (path : Path) :
    characterTest levels (stoppedFrequency levels ξ k) j path =
      characterTest levels ξ j (stop t path) := by
  cases j with
  | zero => simp [characterTest, HigherHeatMixedFourierPaths.character,
      SignedDensityIntegral.configurationPhase, spectrumFrequency]
  | succ i =>
    change SignedDensityIntegral.configurationPhase
      (collapse (fun j => min j (k i)) (ξ i)) (sample (levels i) path) = _
    rw [collapse_phase]
    congr 1
    funext a
    rw [← ht i]
    exact (sample_stop (levels i) (k i) a path).symm

def stopTransport (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))
    (k : (i : ℕ) → Fin (gridSize (levels i))) (t : ℝ≥0)
    (ht : ∀ i, stoppingTime (levels i) (k i) = t) :
    TestSpace levels ξ →L[ℂ] TestSpace levels (stoppedFrequency levels ξ k) :=
  transport levels levels ξ (stoppedFrequency levels ξ k) (stop t)
    (stopped_character levels ξ k t ht)

theorem stopTransport_realize (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))
    (k : (i : ℕ) → Fin (gridSize (levels i))) (t : ℝ≥0)
    (ht : ∀ i, stoppingTime (levels i) (k i) = t) (q : TestSpace levels ξ) (path : Path) :
    realize levels (stoppedFrequency levels ξ k) (stopTransport levels ξ k t ht q) path =
      realize levels ξ q (stop t path) :=
  realize_transport levels levels ξ (stoppedFrequency levels ξ k) (stop t)
    (stopped_character levels ξ k t ht) q path

theorem stopTransport_norm (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))
    (k : (i : ℕ) → Fin (gridSize (levels i))) (t : ℝ≥0)
    (ht : ∀ i, stoppingTime (levels i) (k i) = t) :
    ‖stopTransport levels ξ k t ht‖ ≤ 1 :=
  transport_norm levels levels ξ (stoppedFrequency levels ξ k) (stop t)
    (stopped_character levels ξ k t ht)

end OperatorDerivativeRewrite.Foundation.FourierPathDictionaryTransport
