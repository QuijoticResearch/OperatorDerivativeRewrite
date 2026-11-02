import Foundation.SignedClockComposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.SignedClockLaplaceObstruction

def laplace (ν : SignedMeasure ℝ≥0) (q : ℝ) : ℝ :=
  ∫ᵛ s : ℝ≥0, Real.exp (-q*(s:ℝ)) ∂<•ν

def origin (ν : SignedMeasure ℝ≥0) : ℝ :=
  ∫ᵛ s : ℝ≥0, ({0}:Set ℝ≥0).indicator (fun _ => (1:ℝ)) s ∂<•ν

theorem laplace_limit (ν : SignedMeasure ℝ≥0) :
    Tendsto (laplace ν) atTop (𝓝 (origin ν)) := by
  let : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  apply VectorMeasure.tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun q => (by fun_prop : Continuous (fun s : ℝ≥0 => Real.exp (-q*(s:ℝ)))).measurable.aestronglyMeasurable
  · refine ⟨1,?_⟩
    filter_upwards [eventually_ge_atTop (0:ℝ)] with q hq
    exact Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [s.coe_nonneg])
  · exact Eventually.of_forall fun s => by
      by_cases hs : s=0
      · simp [hs]
      · have hp : 0<(s:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hs)
        have hh : Tendsto (fun q : ℝ => Real.exp (-(q*(s:ℝ)))) atTop (𝓝 0) :=
          Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hp)
        simpa only [mem_singleton_iff,hs,not_false_eq_true,indicator_of_notMem,
          Function.comp_def,neg_mul] using hh

theorem cosine_no_limit (a : ℝ) : ¬Tendsto Real.cos atTop (𝓝 a) := by
  intro h
  have he : Tendsto (fun n : ℕ => (n:ℝ)*(2*Real.pi)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
  have ho := tendsto_atTop_add_const_right atTop Real.pi he
  have hp : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 a) := by
    simpa only [Function.comp_def,Real.cos_nat_mul_two_pi] using h.comp he
  have hm : Tendsto (fun _ : ℕ => (-1:ℝ)) atTop (𝓝 a) := by
    simpa only [Function.comp_def,Real.cos_add_pi,Real.cos_nat_mul_two_pi] using h.comp ho
  have h1 := tendsto_nhds_unique hp tendsto_const_nhds
  have h2 := tendsto_nhds_unique hm tendsto_const_nhds
  linarith
theorem no_finite_clock (t : ℝ) (ht : 0<t) :
    ¬∃ ν : SignedMeasure ℝ≥0, ∀ q : ℝ, 0≤q → laplace ν q=Real.cos (t*Real.sqrt q) := by
  rintro ⟨ν,hν⟩
  have hr : Tendsto (fun x : ℝ => (x/t)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp (tendsto_id.atTop_div_const ht)
  have hh := (laplace_limit ν).comp hr
  have hc : Tendsto Real.cos atTop (𝓝 (origin ν)) := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    change laplace ν ((x/t)^2)=Real.cos x
    rw [hν _ (sq_nonneg _),Real.sqrt_sq (div_nonneg hx ht.le)]
    congr 1
    field_simp
  exact cosine_no_limit _ hc

theorem origin_eq_atom (ν : SignedMeasure ℝ≥0) : origin ν=ν {0} := by
  let : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  unfold origin
  rw [VectorMeasure.integral_eq_setToFun,
    setToFun_indicator_const _ (measurableSet_singleton 0) (measure_ne_top _ _) 1]
  change ν {0} • (1:ℝ)=ν {0}
  simp

/-- The exact order-two Mittag-Leffler series used in the source, not an assigned transform. -/
def inverseTwo (t q : ℝ) : ℝ :=
  ∑' n : ℕ, (-q*t^2)^n/Real.Gamma ((2*n:ℕ)+1)

theorem inverseTwo_eq_cos (t q : ℝ) (hq : 0≤q) :
    inverseTwo t q=Real.cos (t*Real.sqrt q) := by
  unfold inverseTwo
  rw [Real.cos_eq_tsum]
  apply tsum_congr
  intro n
  rw [Real.Gamma_nat_eq_factorial]
  have he : -q*t^2=-(t*Real.sqrt q)^2 := by
    nlinarith [Real.sq_sqrt hq]
  rw [he,neg_pow,pow_mul]

theorem inverseTwo_hasSum (t q : ℝ) (hq : 0≤q) :
    HasSum (fun n : ℕ => (-q*t^2)^n/Real.Gamma ((2*n:ℕ)+1))
      (Real.cos (t*Real.sqrt q)) := by
  have heq : (fun n : ℕ => (-q*t^2)^n/Real.Gamma ((2*n:ℕ)+1))=
      (fun n : ℕ => (-1)^n*(t*Real.sqrt q)^(2*n)/(2*n).factorial) := by
    funext n
    rw [Real.Gamma_nat_eq_factorial]
    have he : -q*t^2=-(t*Real.sqrt q)^2 := by nlinarith [Real.sq_sqrt hq]
    rw [he,neg_pow,pow_mul]
  rw [heq]
  exact Real.hasSum_cos _

theorem zero_time_clock : ∃ ν : SignedMeasure ℝ≥0,
    ∀ q : ℝ, 0≤q → laplace ν q=inverseTwo 0 q := by
  refine ⟨(Measure.dirac (0:ℝ≥0)).toSignedMeasure,fun q hq => ?_⟩
  rw [inverseTwo_eq_cos 0 q hq]
  simp [laplace]

theorem no_orderTwo_clock (t : ℝ) (ht : 0<t) :
    ¬∃ ν : SignedMeasure ℝ≥0, ∀ q : ℝ, 0≤q → laplace ν q=inverseTwo t q := by
  rintro ⟨ν,hν⟩
  exact no_finite_clock t ht ⟨ν,fun q hq => (hν q hq).trans (inverseTwo_eq_cos t q hq)⟩

/-- No single finite signed operational-time clock represents even the REAL parts
of the actual biharmonic heat multipliers with this time-order-two transform. -/
theorem no_biharmonic_clock (t : ℝ) (ht : 0<t) :
    ¬∃ ν : SignedMeasure ℝ≥0, ∀ ξ : ℝ,
      (∫ᵛ s : ℝ≥0, (HigherHeatL2.symbol 2 s ξ).re ∂<•ν)=
        inverseTwo t ((2*Real.pi*ξ)^4) := by
  rintro ⟨ν,hν⟩
  apply no_orderTwo_clock t ht
  refine ⟨ν,fun q hq => ?_⟩
  let ξ := Real.sqrt (Real.sqrt q)/(2*Real.pi)
  have hξ : (2*Real.pi*ξ)^4=q := by
    have he : 2*Real.pi*ξ=Real.sqrt (Real.sqrt q) := by
      dsimp [ξ]
      field_simp
    rw [he,show (4:ℕ)=2*2 from rfl,pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg q),Real.sq_sqrt hq]
  have hh := hν ξ
  have hh' : (∫ᵛ s : ℝ≥0, Real.exp (-(s:ℝ)*q) ∂<•ν)=inverseTwo t q := by
    simpa only [HigherHeatL2.symbol,Complex.ofReal_re,show 2*2=4 from rfl,hξ] using hh
  unfold laplace
  rw [show (fun s : ℝ≥0 => Real.exp (-q*(s:ℝ)))=
    (fun s : ℝ≥0 => Real.exp (-(s:ℝ)*q)) from by funext s;congr 1;ring]
  exact hh'

theorem inverseTwo_biharmonic (t ξ : ℝ) :
    inverseTwo t ((2*Real.pi*ξ)^4)=Real.cos (t*(2*Real.pi*ξ)^2) := by
  rw [inverseTwo_eq_cos t _ (by positivity),
    show (2*Real.pi*ξ)^4=((2*Real.pi*ξ)^2)^2 from by ring,
    Real.sqrt_sq (sq_nonneg _)]

/-- The missing sine channel prevents scalar independent-increment semigroup reuse. -/
theorem inverseTwo_add (s t q : ℝ) (hq : 0≤q) :
    inverseTwo (s+t) q=inverseTwo s q*inverseTwo t q-
      Real.sin (s*Real.sqrt q)*Real.sin (t*Real.sqrt q) := by
  rw [inverseTwo_eq_cos _ _ hq,inverseTwo_eq_cos _ _ hq,inverseTwo_eq_cos _ _ hq]
  rw [add_mul,Real.cos_add]

theorem inverseTwo_not_semigroup :
    ¬∀ s t : ℝ, 0≤s → 0≤t → inverseTwo (s+t) 1=inverseTwo s 1*inverseTwo t 1 := by
  intro h
  have hh := h (Real.pi/2) (Real.pi/2) (by positivity) (by positivity)
  rw [show Real.pi/2+Real.pi/2=Real.pi from by ring] at hh
  norm_num [inverseTwo_eq_cos,Real.cos_pi_div_two] at hh

end OperatorDerivativeRewrite.Foundation.SignedClockLaplaceObstruction
