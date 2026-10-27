import Foundation.CauchyPoissonDriftRate
import Mathlib.Analysis.ODE.Gronwall
/-! Real-time exponential relative-entropy contraction for actual forward laws.
Grönwall applies after positive burn-in; monotonicity permits the initial-time
limit without initial density or entropy continuity. No sharp LSI is asserted. -/
open Complex MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonExponentialEntropy
open CauchyPoissonMarkovKernel CauchyPoissonDensitySmooth CauchyPoissonForwardEntropy
open CauchyPoissonDriftRate CauchyPoissonFlow

theorem decay_of_production (q c : ℝ) (hq : |q| < 1) (μ : Measure Circle)
    [IsProbabilityMeasure μ]
    (hb : ∀ u : ℝ, 0 < u →
      (∫ w, Real.log (densityCurve q hq μ u w).re *
        (deriv (densityCurve q hq μ) u w).re ∂invariantLaw q) ≤
      -c*(klDiv ((kernel q u) ∘ₘ μ) (invariantLaw q)).toReal)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    (klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal ≤
      Real.exp (-c*(t-s))*(klDiv ((kernel q s) ∘ₘ μ) (invariantLaw q)).toReal := by
  let E := fun u => (klDiv ((kernel q u) ∘ₘ μ) (invariantLaw q)).toReal
  let D := fun u => ∫ w, Real.log (densityCurve q hq μ u w).re *
    (deriv (densityCurve q hq μ) u w).re ∂invariantLaw q
  have hd (u : ℝ) (hu : 0 < u) : HasDerivAt E (D u) u := actual_kl_derivative q u hq hu μ
  have hc : ContinuousOn E (Icc s t) := fun u hu =>
    (hd u (hs.trans_le hu.1)).continuousAt.continuousWithinAt
  have hh := le_gronwallBound_of_liminf_deriv_right_le (f := E) (f' := D)
    (δ := E s) (K := -c) (ε := 0) hc (fun u hu r hr => ?_) le_rfl
    (fun u hu => by simpa using hb u (hs.trans_le hu.1)) t ⟨hst,le_rfl⟩
  · simpa [gronwallBound_ε0,mul_comm] using hh
  · have hh := ((hd u (hs.trans_le hu.1)).tendsto_slope.mono_left (nhdsGT_le_nhdsNE u)).eventually
      (Iio_mem_nhds hr)
    exact hh.frequently

theorem entropy_exponential (q s t : ℝ) (hq : |q| < 1) (hs : 0 < s) (hst : s ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal ≤
      Real.exp (-(amplitude q*rate q)*(t-s)) *
        (klDiv ((kernel q s) ∘ₘ μ) (invariantLaw q)).toReal :=
  decay_of_production q (amplitude q*rate q) hq μ (fun u hu => production_bound q u hq hu μ) s t hs hst

theorem zero_entropy_exponential (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (klDiv ((kernel 0 t) ∘ₘ μ) (invariantLaw 0)).toReal ≤
      Real.exp (-(1/2)*(t-s)) * (klDiv ((kernel 0 s) ∘ₘ μ) (invariantLaw 0)).toReal :=
  decay_of_production 0 (1/2) (by norm_num) μ
    (fun u hu => CauchyPoissonQuantitativeEntropy.zero_entropy_production_bound u hu μ) s t hs hst



theorem entropy_initial_real (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ]
    (hfinite : klDiv μ (invariantLaw q) ≠ ⊤) :
    (klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal ≤
      Real.exp (-(amplitude q*rate q)*t) * (klDiv μ (invariantLaw q)).toReal := by
  rcases eq_or_lt_of_le ht with he | ht
  · subst t; simp [kernel_zero]
  let c := amplitude q*rate q
  let E0 := (klDiv μ (invariantLaw q)).toReal
  have hc : Continuous (fun s : ℝ => Real.exp (-c*(t-s))*E0) := by fun_prop
  have hl : Tendsto (fun s : ℝ => Real.exp (-c*(t-s))*E0)
      (𝓝[Ioi 0] 0) (𝓝 (Real.exp (-c*t)*E0)) := by
    simpa using (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs hslt
  change 0 < s at hs
  have hb := entropy_exponential q s t hq hs hslt.le μ
  have hm := ENNReal.toReal_mono hfinite
    (CauchyPoissonEntropy.relative_entropy_contracts q s hq hs.le μ)
  exact hb.trans (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)

theorem entropy_initial (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≤
      ENNReal.ofReal (Real.exp (-(amplitude q*rate q)*t)) * klDiv μ (invariantLaw q) := by
  by_cases hfinite : klDiv μ (invariantLaw q) = ⊤
  · rw [hfinite,ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))]
    exact le_top
  have hf := CauchyPoissonEntropy.entropy_stays_finite q t hq ht μ hfinite
  have hh := ENNReal.ofReal_le_ofReal (entropy_initial_real q t hq ht μ hfinite)
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_toReal hf,ENNReal.ofReal_toReal hfinite] at hh
  exact hh

end OperatorDerivativeRewrite.Foundation.CauchyPoissonExponentialEntropy

