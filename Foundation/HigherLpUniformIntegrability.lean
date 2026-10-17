import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Foundation.CriticalLpSpike

/-! A quantitative higher-norm route to uniform integrability and actual Lp convergence. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherLpUniformIntegrability
set_option backward.isDefEq.respectTransparency false
variable {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable {μ : Measure Ω} {p q : ℝ≥0∞}

theorem restricted_higher_bound (hpq : p ≤ q) {f : Ω → E}
    (hf : AEStronglyMeasurable f μ) (s : Set Ω) :
    eLpNorm f p (μ.restrict s) ≤
      eLpNorm f q μ * (μ s)^(1/p.toReal-1/q.toReal) := by
  calc
    _ ≤ eLpNorm f q (μ.restrict s)*(μ s)^(1/p.toReal-1/q.toReal) := by
      simpa only [Measure.restrict_apply_univ] using
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s) hpq hf.restrict)
    _ ≤ _ := mul_le_mul' (eLpNorm_mono_measure f Measure.restrict_le_self) le_rfl

theorem restricted_L3_L4_bound {f : Ω → E} (hf : AEStronglyMeasurable f μ) (s : Set Ω) :
    eLpNorm f 3 (μ.restrict s) ≤ eLpNorm f 4 μ*(μ s)^((1 : ℝ)/12) := by
  have h := restricted_higher_bound (p := 3) (q := 4) (by norm_num) hf s
  norm_num at h ⊢
  exact h

theorem unifIntegrable_of_higher_bound (hpq : p ≤ q)
    (hgap : 0 < 1/p.toReal-1/q.toReal) (f : ι → Ω → E)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hb : ∀ i, eLpNorm (f i) q μ ≤ C) : UnifIntegrable f p μ := by
  unfold UnifIntegrable
  have ht := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hgap
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro ε
    exact bot_le
  · intro ε
    refine iSup_le fun i => iSup_le fun s => iSup_le fun hs => ?_
    exact (restricted_higher_bound hpq (hf i) s).trans
      (mul_le_mul' (hb i) (ENNReal.rpow_le_rpow hs hgap.le))

theorem uniformIntegrable_of_higher_bound [IsFiniteMeasure μ] (hpq : p ≤ q)
    (hgap : 0 < 1/p.toReal-1/q.toReal) (f : ι → Ω → E)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hb : ∀ i, eLpNorm (f i) q μ ≤ C) : UniformIntegrable f p μ := by
  refine ⟨unifIntegrable_of_higher_bound hpq hgap f hf C hC hb, ?_⟩
  let B := C*(μ univ)^(1/p.toReal-1/q.toReal)
  have hB : B ≠ ∞ := ENNReal.mul_ne_top hC
    (ENNReal.rpow_ne_top_of_nonneg hgap.le (measure_ne_top μ univ))
  refine ⟨B.toNNReal, fun i => ?_⟩
  rw [ENNReal.coe_toNNReal hB]
  exact (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq (hf i)).trans
    (mul_le_mul' (hb i) le_rfl)

theorem gap_pos_of_finite_exponents (hp : 0 < p) (hpq : p < q) (hq : q ≠ ∞) :
    0 < 1/p.toReal-1/q.toReal := by
  have hp' : p ≠ ∞ := ne_of_lt (lt_trans hpq (lt_top_iff_ne_top.mpr hq))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hp'
  have hpqr : p.toReal < q.toReal := (ENNReal.toReal_lt_toReal hp' hq).mpr hpq
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hpr hpqr)

theorem higher_bound_ae_Lp_convergence [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hpq : p ≤ q) (hgap : 0 < 1/p.toReal-1/q.toReal)
    (f : ℕ → Ω → E) (g : Ω → E) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hb : ∀ n, eLpNorm (f n) q μ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MemLp g p μ ∧ Tendsto (fun n => eLpNorm (f n-g) p μ) atTop (𝓝 0) := by
  have hui := uniformIntegrable_of_higher_bound hpq hgap f hf C hC hb
  have hg := hui.memLp_of_ae_tendsto hlim
  exact ⟨hg, tendsto_Lp_finite_of_tendsto_ae hp hp' hf hg hui.1 hlim⟩

theorem L4_bound_ae_L3_convergence [IsFiniteMeasure μ]
    (f : ℕ → Ω → E) (g : Ω → E) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hb : ∀ n, eLpNorm (f n) 4 μ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MemLp g 3 μ ∧ Tendsto (fun n => eLpNorm (f n-g) 3 μ) atTop (𝓝 0) := by
  exact higher_bound_ae_Lp_convergence (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) f g hf C hC hb hlim

theorem finite_higher_ae_Lp_convergence [IsFiniteMeasure μ] (hp : 1 ≤ p)
    (hpq : p < q) (hq : q ≠ ∞) (f : ℕ → Ω → E) (g : Ω → E)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hb : ∀ n, eLpNorm (f n) q μ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MemLp g p μ ∧ Tendsto (fun n => eLpNorm (f n-g) p μ) atTop (𝓝 0) := by
  exact higher_bound_ae_Lp_convergence hp (ne_of_lt (lt_trans hpq (lt_top_iff_ne_top.mpr hq)))
    hpq.le (gap_pos_of_finite_exponents (zero_lt_one.trans_le hp) hpq hq) f g hf C hC hb hlim

theorem higher_bound_ae_toLp_convergence [IsFiniteMeasure μ] [Fact (1 ≤ p)] (hp' : p ≠ ∞)
    (hpq : p ≤ q) (hgap : 0 < 1/p.toReal-1/q.toReal)
    (f : ℕ → Ω → E) (g : Ω → E) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hb : ∀ n, eLpNorm (f n) q μ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∃ (hfLp : ∀ n, MemLp (f n) p μ) (hgLp : MemLp g p μ),
      Tendsto (fun n => (hfLp n).toLp (f n)) atTop (𝓝 (hgLp.toLp g)) := by
  have hui := uniformIntegrable_of_higher_bound hpq hgap f hf C hC hb
  obtain ⟨hg, ht⟩ := higher_bound_ae_Lp_convergence Fact.out hp' hpq hgap f g hf C hC hb hlim
  refine ⟨fun n => hui.memLp n, hg, ?_⟩
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f (fun n => hui.memLp n) g hg).mpr ht

theorem critical_spike_no_finite_L4_bound :
    ¬ ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ n, eLpNorm (CriticalLpSpike.spike n) 4 CriticalLpSpike.unitLaw ≤ C := by
  rintro ⟨C,hC,hb⟩
  apply CriticalLpSpike.not_uniformIntegrable
  exact uniformIntegrable_of_higher_bound (p := 3) (q := 4) (by norm_num) (by norm_num)
    CriticalLpSpike.spike (fun n => (CriticalLpSpike.spike_memLp n).aestronglyMeasurable) C hC hb

end OperatorDerivativeRewrite.Foundation.HigherLpUniformIntegrability
