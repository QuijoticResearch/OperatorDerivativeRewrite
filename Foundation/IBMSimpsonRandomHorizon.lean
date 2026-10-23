import Foundation.IBMUniformSimpsonProcess
import Mathlib.MeasureTheory.Function.Floor

/-! Canonical left-grid random-horizon realization of the signed Simpson
integral process. Arbitrary measurable bounded times are allowed; no optional
sampling, martingale or adaptedness claim is made. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSimpsonRandomHorizon
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformSimpsonProcess IBMActualSimpson
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def index (T : ℝ≥0) (n : ℕ) (r : ℝ≥0) : ℕ :=
  ⌊(r : ℝ) / (T : ℝ) * (n + 1 : ℝ)⌋₊

def rounded (T : ℝ≥0) (n : ℕ) (r : ℝ≥0) : ℝ≥0 :=
  grid (T / (n + 1)) (index T n r)

theorem index_le {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (r : ℝ≥0) (hr : r ≤ T) :
    index T n r ≤ n + 1 := by
  have hTr : (0 : ℝ) < T := hT
  have hh : (r : ℝ) / (T : ℝ) ≤ 1 := (div_le_one hTr).mpr hr
  have hm := mul_le_mul_of_nonneg_right hh (by positivity : (0 : ℝ) ≤ n + 1)
  unfold index
  have h := Nat.floor_mono (by simpa only [one_mul] using hm)
  simpa only [show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast; rfl,
    Nat.floor_natCast] using h

theorem rounded_bounds {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (r : ℝ≥0) :
    (rounded T n r : ℝ) ≤ r ∧
      (r : ℝ) - (rounded T n r : ℝ) < (T : ℝ) / (n + 1) := by
  have hTr : (0 : ℝ) < T := hT
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hδ : 0 < (T : ℝ) / (n + 1) := div_pos hTr hN
  have hl := Nat.floor_le (by positivity : 0 ≤ (r : ℝ) / (T : ℝ) * (n + 1 : ℝ))
  have hu := Nat.lt_floor_add_one ((r : ℝ) / (T : ℝ) * (n + 1 : ℝ))
  have hscale : (T : ℝ) / (n + 1) * ((r : ℝ) / (T : ℝ) * (n + 1 : ℝ)) = r := by
    field_simp
  have htime : (rounded T n r : ℝ) =
      (T : ℝ) / (n + 1) * (index T n r : ℝ) := by
    simp only [rounded, grid, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
      NNReal.coe_add, NNReal.coe_one]
  have ha := mul_le_mul_of_nonneg_left hl hδ.le
  have hb := mul_lt_mul_of_pos_left hu hδ
  change (T : ℝ) / (n + 1) * (index T n r : ℝ) ≤
    (T : ℝ) / (n + 1) * ((r : ℝ) / (T : ℝ) * (n + 1 : ℝ)) at ha
  change (T : ℝ) / (n + 1) * ((r : ℝ) / (T : ℝ) * (n + 1 : ℝ)) <
    (T : ℝ) / (n + 1) * ((index T n r : ℝ) + 1) at hb
  rw [hscale] at ha hb
  constructor
  · simpa only [htime] using ha
  · rw [htime]
    nlinarith [hb]

theorem rounded_tendsto {T : ℝ≥0} (hT : 0 < T) (r : ℝ≥0) :
    Tendsto (fun n => rounded T n r) atTop (𝓝 r) := by
  have hstep : Tendsto (fun n : ℕ => (T : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hstep.eventually (gt_mem_nhds hε)] with n hn
  rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (rounded_bounds hT n r).1)]
  linarith [(rounded_bounds hT n r).2]

theorem index_measurable (T : ℝ≥0) (n : ℕ) : Measurable (index T n) := by
  have hc : Measurable (fun r : ℝ≥0 => (r : ℝ)) := measurable_coe_nnreal_real
  exact ((hc.div_const (T : ℝ)).mul_const (n + 1 : ℝ)).nat_floor

theorem rounded_measurable (T : ℝ≥0) (n : ℕ) : Measurable (rounded T n) :=
  (measurable_from_top : Measurable (grid (T / (n + 1)))).comp (index_measurable T n)

theorem stopped_sums_measurable (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n : ℕ)
    (τ : JointSample → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω => prefixSums g T n (index T n (τ ω)) ω) :=
  selected_sums_measurable g hg T n _ ((index_measurable T n).comp hτ)

theorem stopped_integral_measurable (g : ℝ → ℝ) (hg : Continuous g)
    (τ : JointSample → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω => lineIntegral g (τ ω) ω) :=
  (integral_jointly_measurable g hg).comp (hτ.prodMk measurable_id)

/-- Canonical floor-grid Simpson sums at ANY measurable time bounded by T
converge in probability to the actual continuous integral process at that time. -/
theorem stopped_sums_tendstoInMeasure (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g)
    {T : ℝ≥0} (hT : 0 < T) (τ : JointSample → ℝ≥0) (hτ : Measurable τ)
    (hτT : ∀ ω, τ ω ≤ T) :
    TendstoInMeasure jointMeasure
      (fun n ω => prefixSums g T n (index T n (τ ω)) ω) atTop
      (fun ω => lineIntegral g (τ ω) ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (stopped_sums_measurable g hg.continuous T n τ hτ).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hmax⟩ :=
    ((maximum_tendstoInMeasure g hg hT).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hmax] with ω hω
  have he : Tendsto (fun j => error g T (ns (ms j))
      (index T (ns (ms j)) (τ ω)) ω) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero, Real.norm_eq_abs]
    apply squeeze_zero (fun _ => abs_nonneg _)
      (fun j => error_le_maximum g T (ns (ms j)) _
        (index_le hT _ _ (hτT ω)) ω)
    simpa only [Function.comp_def] using hω
  have ht := ((integral_continuous g hg.continuous ω).tendsto (τ ω)).comp
    ((rounded_tendsto hT (τ ω)).comp (hns.comp hms).tendsto_atTop)
  have hs := he.add ht
  simpa only [IBMUniformSimpsonProcess.error, rounded, Function.comp_def,
    sub_add_cancel, zero_add] using hs

end OperatorDerivativeRewrite.Foundation.IBMSimpsonRandomHorizon
