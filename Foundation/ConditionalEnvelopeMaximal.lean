import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-! A finite-grid maximal estimate with explicitly adapted conditional
representatives. Positive parts enforce pointwise nonnegativity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.ConditionalEnvelopeMaximal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (F : Ω → ℝ)

def envelope (i : ℕ) (ω : Ω) : ℝ := max (μ[(fun x => ‖F x‖) | ℱ i] ω) 0

theorem envelope_submartingale : Submartingale (envelope μ ℱ F) ℱ μ := by
  exact (martingale_condExp (fun x => ‖F x‖) ℱ μ).submartingale.sup
    (martingale_zero ℝ ℱ μ).submartingale

theorem envelope_nonneg (i : ℕ) (ω : Ω) : 0 ≤ envelope μ ℱ F i ω := le_max_right _ _

theorem conditional_dominated (i : ℕ) :
    ∀ᵐ ω ∂μ, ‖μ[F | ℱ i] ω‖ ≤ envelope μ ℱ F i ω := by
  filter_upwards [norm_condExp_le (μ := μ) (m := ℱ i) F] with ω hω
  exact hω.trans (le_max_left _ _)

theorem envelope_ae (i : ℕ) : envelope μ ℱ F i =ᵐ[μ] μ[(fun x => ‖F x‖) | ℱ i] := by
  filter_upwards [condExp_nonneg (μ := μ) (m := ℱ i)
    (Eventually.of_forall (fun x => norm_nonneg (F x)))] with ω hω
  exact max_eq_left hω

def runningMax (f : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun i => f i ω)

theorem maximal_envelope (_hF : Integrable F μ) (ε : ℝ≥0) (N : ℕ) :
    (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤ runningMax (envelope μ ℱ F) N ω} ≤
      ENNReal.ofReal (∫ ω, ‖F ω‖ ∂μ) := by
  have h := maximal_ineq (envelope_submartingale μ ℱ F)
    (fun i ω => envelope_nonneg μ ℱ F i ω) (ε := ε) N
  change (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤ runningMax (envelope μ ℱ F) N ω} ≤ _ at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ ω, envelope μ ℱ F N ω ∂μ :=
      setIntegral_le_integral ((envelope_submartingale μ ℱ F).integrable N)
        (Eventually.of_forall (fun ω => envelope_nonneg μ ℱ F N ω))
    _ = ∫ ω, ‖F ω‖ ∂μ := by
      rw [integral_congr_ae (envelope_ae μ ℱ F N)]
      exact integral_condExp (ℱ.le N)

theorem maximal_of_ae_dominated (hF : Integrable F μ) (f : ℕ → Ω → ℝ)
    (hf : ∀ i, ∀ᵐ ω ∂μ, f i ω ≤ envelope μ ℱ F i ω) (ε : ℝ≥0) (N : ℕ) :
    (ε : ℝ≥0∞) * μ {ω | ∃ i ≤ N, (ε : ℝ) ≤ f i ω} ≤
      ENNReal.ofReal (∫ ω, ‖F ω‖ ∂μ) := by
  have hm : μ {ω | ∃ i ≤ N, (ε : ℝ) ≤ f i ω} ≤
      μ {ω | (ε : ℝ) ≤ runningMax (envelope μ ℱ F) N ω} := by
    apply measure_mono_ae
    filter_upwards [ae_all_iff.mpr hf] with ω hω
    rintro ⟨i, hi, he⟩
    exact (he.trans (hω i)).trans
      (Finset.le_sup' (f := fun j => envelope μ ℱ F j ω) (Finset.mem_range.mpr (by omega)))
  calc
    _ ≤ (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤ runningMax (envelope μ ℱ F) N ω} := by
      gcongr
    _ ≤ _ := maximal_envelope μ ℱ F hF ε N

end OperatorDerivativeRewrite.Foundation.ConditionalEnvelopeMaximal
