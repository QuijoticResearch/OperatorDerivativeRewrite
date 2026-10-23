import Foundation.IBMContinuousQuadrature
import Foundation.IBMUniformPrefixMaximum
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine continuously weighted actual IBM quartic variation in probability,
using deterministic positive quadrature and the proved uniform prefix limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMContinuousWeightedQuartic
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy IBMUniformPrefixMaximum
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def weight (φ : ℝ → ℝ) (t : ℝ) (ω : JointSample) : ℝ :=
  φ (ibmValue (Real.toNNReal t) ω)

def weighted (T : ℝ≥0) (φ : ℝ → ℝ) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), φ (ibmValue (grid (T/(n + 1)) i) ω) *
    (ibmValue (grid (T/(n + 1)) (i + 1)) ω - ibmValue (grid (T/(n + 1)) i) ω)^4

def timeIntegral (T : ℝ≥0) (φ : ℝ → ℝ) (ω : JointSample) : ℝ :=
  ∫ t in (0 : ℝ)..(T : ℝ), weight φ t ω

theorem weight_continuous (φ : ℝ → ℝ) (hφ : Continuous φ) (ω : JointSample) :
    Continuous (fun t => weight φ t ω) :=
  hφ.comp ((ibmValue_continuous ω).comp continuous_real_toNNReal)

theorem weight_jointly_measurable (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Measurable (fun p : ℝ × JointSample => weight φ p.1 p.2) :=
  hφ.measurable.comp (ibmValue_jointly_measurable.comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd))

theorem weighted_measurable (T : ℝ≥0) (φ : ℝ → ℝ) (hφ : Continuous φ) (n : ℕ) :
    Measurable (weighted T φ n) := by
  apply Finset.measurable_sum
  intro i hi
  have hm (t : ℝ≥0) : Measurable (ibmValue t) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  exact (hφ.measurable.comp (hm _)).mul (((hm _).sub (hm _)).pow_const 4)

theorem timeIntegral_integrable (T : ℝ≥0) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (ω : JointSample) : IntervalIntegrable (fun t => weight φ t ω) volume 0 T :=
  (weight_continuous φ hφ ω).intervalIntegrable _ _

theorem timeIntegral_measurable (T : ℝ≥0) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Measurable (timeIntegral T φ) := by
  have hm := (weight_jointly_measurable φ hφ).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioc (0 : ℝ) T))
  have he : timeIntegral T φ = fun ω =>
      ∫ t, weight φ t ω ∂(volume.restrict (Ioc (0 : ℝ) T)) := by
    funext ω
    exact intervalIntegral.integral_of_le T.coe_nonneg
  rw [he]
  exact hm.measurable

theorem real_time_eq_grid (T : ℝ≥0) (N i : ℕ) :
    IBMContinuousQuadrature.time (T : ℝ) N i = (grid (T/N) i : ℝ) := by
  simp only [IBMContinuousQuadrature.time, grid, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_natCast]

theorem weight_at_grid (T : ℝ≥0) (φ : ℝ → ℝ) (N i : ℕ) (ω : JointSample) :
    weight φ (IBMContinuousQuadrature.time T N i) ω = φ (ibmValue (grid (T/N) i) ω) := by
  simp only [weight, real_time_eq_grid, Real.toNNReal_coe]

/-- All continuous spatial weights, including globally unbounded ones, are
evaluated on the ACTUAL process. The limit is its genuine pathwise time integral. -/
theorem weighted_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    TendstoInMeasure jointMeasure (weighted T φ) atTop
      (fun ω => 3 * timeIntegral T φ ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (weighted_measurable T φ hφ n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hmax⟩ :=
    ((maximum_tendstoInMeasure hT).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hmax] with ω hω
  let N : ℕ → ℕ := fun k => ns (ms k) + 1
  let q : ℕ → ℕ → ℝ := fun k i =>
    (ibmValue (grid (T/N k) (i + 1)) ω - ibmValue (grid (T/N k) i) ω)^4
  have hN : ∀ k, 0 < N k := fun _ => Nat.zero_lt_succ _
  have hNm : StrictMono N := by
    intro i j hij
    exact Nat.add_lt_add_right (hns (hms hij)) 1
  have hMlim : Tendsto (fun k => maximum T (ns (ms k)) ω) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hω
  have hpart (k m : ℕ) (hm : m ≤ N k) :
      |(∑ i ∈ Finset.range m, q k i) - 3*((T : ℝ)/(N k))*m| ≤
        maximum T (ns (ms k)) ω := by
    have hc : 3*((T : ℝ)/(N k))*m = (3*(T : ℝ)/(ns (ms k) + 1))*m := by
      dsimp [N]
      push_cast
      ring
    rw [hc]
    have he := Finset.le_sup' (fun j => |IBMUniformPrefixQuartic.error T (ns (ms k)) j ω|)
      (s := Finset.range (ns (ms k) + 2)) (b := m) (by
        apply Finset.mem_range.mpr
        dsimp [N] at hm
        omega)
    rw [error_eq hT] at he
    simpa only [q, N, cumulative, maximum, Nat.cast_add, Nat.cast_one] using he
  have hgen := IBMContinuousQuadrature.continuous_quadrature_tendsto
    T.coe_nonneg (by norm_num : (0 : ℝ) ≤ 3) (fun t => weight φ t ω)
    (weight_continuous φ hφ ω) N hN hNm.tendsto_atTop q
    (fun _ _ => by dsimp [q]; positivity) (fun k => maximum T (ns (ms k)) ω)
    (fun k => maximum_nonneg _ _ _) hMlim hpart
  have heq : (fun k => ∑ i ∈ Finset.range (N k),
      weight φ (IBMContinuousQuadrature.time T (N k) i) ω * q k i) =
      fun k => weighted T φ (ns (ms k)) ω := by
    funext k
    unfold weighted
    apply Finset.sum_congr rfl
    intro i hi
    simp only [weight_at_grid, q, N, Nat.cast_add, Nat.cast_one]
  rw [heq] at hgen
  exact hgen

end OperatorDerivativeRewrite.Foundation.IBMContinuousWeightedQuartic
