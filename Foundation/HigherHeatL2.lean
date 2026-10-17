import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.Holder
import Foundation.BochnerL2Dominated

/-! Actual higher even-order heat Fourier evolution on Lebesgue L2(R).
No positivity or signed path measure is assumed. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatL2

abbrev H := Lp (α := ℝ) ℂ 2 volume

def symbol (m : ℕ) (t : ℝ≥0) (x : ℝ) : ℂ :=
  (Real.exp (-(t : ℝ) * (2 * Real.pi * x) ^ (2*m)) : ℝ)

theorem symbol_continuous (m : ℕ) (t : ℝ≥0) : Continuous (symbol m t) := by
  unfold symbol
  fun_prop

theorem symbol_norm_le (m : ℕ) (t : ℝ≥0) (x : ℝ) : ‖symbol m t x‖ ≤ 1 := by
  rw [symbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (by rw [pow_mul]; positivity))

theorem symbol_zero (m : ℕ) (x : ℝ) : symbol m 0 x = 1 := by simp [symbol]

theorem symbol_add (m : ℕ) (s t : ℝ≥0) (x : ℝ) :
    symbol m (s+t) x = symbol m s x * symbol m t x := by
  simp only [symbol, NNReal.coe_add, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem mulMem (m : ℕ) (t : ℝ≥0) (f : H) :
    MemLp (fun x => symbol m t x * f x) 2 volume := by
  apply (Lp.memLp f).of_le ((symbol_continuous m t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun x => by
    change ‖symbol m t x * f x‖ ≤ ‖f x‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (symbol_norm_le m t x)

def multiplier (m : ℕ) (t : ℝ≥0) (f : H) : H := (mulMem m t f).toLp _

theorem multiplier_ae (m : ℕ) (t : ℝ≥0) (f : H) :
    multiplier m t f =ᵐ[volume] fun x => symbol m t x * f x := (mulMem m t f).coeFn_toLp

theorem multiplier_norm (m : ℕ) (t : ℝ≥0) (f : H) : ‖multiplier m t f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [multiplier_ae m t f] with x hx
  rw [hx, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (symbol_norm_le m t x)

def multiplierCLM (m : ℕ) (t : ℝ≥0) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := multiplier m t
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [multiplier_ae m t (f+g), multiplier_ae m t f,
          multiplier_ae m t g, Lp.coeFn_add f g,
          Lp.coeFn_add (multiplier m t f) (multiplier m t g)] with x h1 h2 h3 h4 h5
        simp only [h1,h4,h5,Pi.add_apply,h2,h3,mul_add]
      map_smul' := by
        intro c f
        change multiplier m t (c • f) = c • multiplier m t f
        apply Lp.ext
        filter_upwards [multiplier_ae m t (c • f), multiplier_ae m t f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (multiplier m t f)] with x h1 h2 h3 h4
        simp only [h1,h3,h4,Pi.smul_apply,h2,smul_eq_mul]
        ring }
    1 (by intro f; simpa using multiplier_norm m t f)

def evolution (m : ℕ) (t : ℝ≥0) : H →L[ℂ] H :=
  (fourierInvCLM ℂ H).comp ((multiplierCLM m t).comp (fourierCLM ℂ H))

theorem evolution_apply (m : ℕ) (t : ℝ≥0) (f : H) :
    evolution m t f = 𝓕⁻ (multiplier m t (𝓕 f)) := rfl

theorem multiplier_zero (m : ℕ) (f : H) : multiplier m 0 f = f := by
  apply Lp.ext
  filter_upwards [multiplier_ae m 0 f] with x hx
  simpa [symbol_zero] using hx

theorem multiplier_add (m : ℕ) (s t : ℝ≥0) (f : H) :
    multiplier m s (multiplier m t f) = multiplier m (s+t) f := by
  apply Lp.ext
  filter_upwards [multiplier_ae m s (multiplier m t f),multiplier_ae m t f,
    multiplier_ae m (s+t) f] with x h1 h2 h3
  rw [h1,h2,h3,symbol_add,mul_assoc]

theorem evolution_zero (m : ℕ) : evolution m 0 = ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro f
  rw [evolution_apply,multiplier_zero,fourierInv_fourier_eq]
  rfl

theorem evolution_semigroup (m : ℕ) (s t : ℝ≥0) :
    (evolution m s).comp (evolution m t) = evolution m (s+t) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply,evolution_apply,fourier_fourierInv_eq,multiplier_add]

theorem evolution_contraction (m : ℕ) (t : ℝ≥0) (f : H) :
    ‖evolution m t f‖ ≤ ‖f‖ := by
  rw [evolution_apply, show 𝓕⁻ (multiplier m t (𝓕 f)) =
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm (multiplier m t (𝓕 f)) from rfl,
    LinearIsometryEquiv.norm_map]
  exact (multiplier_norm m t (𝓕 f)).trans_eq (Lp.norm_fourier_eq f)

theorem symbol_time_continuous (m : ℕ) (x : ℝ) :
    Continuous (fun t : ℝ≥0 => symbol m t x) := by
  unfold symbol
  fun_prop

theorem multiplier_strong_continuous (m : ℕ) (f : H) :
    Continuous (fun t : ℝ≥0 => multiplier m t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hd : Filter.Tendsto
      (fun t : ℝ≥0 => ∫ x, ‖(symbol m t x - symbol m t₀ x) * f x‖^2)
      (𝓝 t₀) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := 𝓝 t₀) (f := fun _ : ℝ => (0 : ℝ))
      (fun x => 4 * ‖f x‖^2)
      (Filter.Eventually.of_forall fun t =>
        (((symbol_continuous m t).aestronglyMeasurable.sub
          (symbol_continuous m t₀).aestronglyMeasurable).mul
            (Lp.aestronglyMeasurable f)).norm.pow 2)
      (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun x => by
        change ‖‖(symbol m t x - symbol m t₀ x) * f x‖^2‖ ≤ 4 * ‖f x‖^2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul]
        have hb : ‖symbol m t x - symbol m t₀ x‖ ≤ 2 :=
          (norm_sub_le _ _).trans (by linarith [symbol_norm_le m t x, symbol_norm_le m t₀ x])
        calc
          (‖symbol m t x - symbol m t₀ x‖ * ‖f x‖)^2 ≤ (2 * ‖f x‖)^2 := by gcongr
          _ = 4 * ‖f x‖^2 := by ring)
      (((Lp.memLp f).integrable_norm_pow (by decide)).const_mul 4)
      (Filter.Eventually.of_forall fun x => by
        change Filter.Tendsto (fun t : ℝ≥0 => ‖(symbol m t x - symbol m t₀ x) * f x‖^2) (𝓝 t₀) (𝓝 0)
        have hc : Continuous (fun t : ℝ≥0 => ‖(symbol m t x - symbol m t₀ x) * f x‖^2) :=
          (((symbol_time_continuous m x).sub continuous_const).mul continuous_const).norm.pow 2
        simpa using hc.continuousAt.tendsto (x := t₀))
    simpa using h
  have hs : Filter.Tendsto
      (fun t : ℝ≥0 => ‖multiplier m t f - multiplier m t₀ f‖^2)
      (𝓝 t₀) (𝓝 0) := by
    convert hd using 1
    funext t
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (multiplier m t f) (multiplier m t₀ f),
      multiplier_ae m t f, multiplier_ae m t₀ f] with x h1 h2 h3
    simp only [h1,Pi.sub_apply,h2,h3,sub_mul]
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero]
    using Real.continuous_sqrt.continuousAt.tendsto.comp hs

theorem evolution_strong_continuous (m : ℕ) (f : H) :
    Continuous (fun t : ℝ≥0 => evolution m t f) :=
  (fourierInvCLM ℂ H).continuous.comp (multiplier_strong_continuous m (𝓕 f))

end OperatorDerivativeRewrite.Foundation.HigherHeatL2
