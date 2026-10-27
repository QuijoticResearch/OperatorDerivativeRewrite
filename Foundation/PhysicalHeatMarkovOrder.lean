import Foundation.PhysicalHeatPositiveCone

/-!
# Real order and probability approximants for physical torus heat

For a covariance symbol with zero rate at the constant mode, the verified
physical `L²` evolution preserves real order intervals, real inputs, and
essential bounds. The last declarations construct genuine probability measures
from heat-evolved finite Fourier squares and compute their Fourier coefficients.
These measures depend on the chosen square. An exact transition law independent
of that choice, and a corresponding stochastic process, require a separate
approximate-identity and compactness argument.
-/

open MeasureTheory AddCircle
open scoped NNReal ComplexConjugate
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatMarkovOrder
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open PhysicalTorusWaveSemigroup PhysicalHeatPositiveCone
open WaveTorusCoreBridge PhysicalHeatSquareBridge

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem basis_zero_ae_one :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume, (basis 0) x = 1 := by
  have h := UnitAddTorus.coeFn_mFourierLp (p := 2) (n := (0 : Wave))
  filter_upwards [h] with x hx
  simpa [basis, UnitAddTorus.coe_mFourierBasis,
    UnitAddTorus.mFourier_zero] using hx

theorem physical_evolution_order_interval (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) (u : E) (M : ℝ)
    (hu : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ M) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((evolution r t u) x).im = 0 ∧
      0 ≤ ((evolution r t u) x).re ∧
      ((evolution r t u) x).re ≤ M := by
  have hnonneg : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).im = 0 ∧ 0 ≤ (u x).re := hu.mono (fun _ hx => ⟨hx.1,hx.2.1⟩)
  have hgap : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (((M : ℂ) • basis 0 - u) x).im = 0 ∧
        0 ≤ (((M : ℂ) • basis 0 - u) x).re := by
    filter_upwards [hu,basis_zero_ae_one,
      Lp.coeFn_smul (M : ℂ) (basis 0),
      Lp.coeFn_sub ((M : ℂ) • basis 0) u] with x hx hb hsm hsub
    simp only [Pi.sub_apply] at hsub
    rw [hsub,hsm, Pi.smul_apply, hb]
    constructor
    · simp [hx.1]
    · simpa using sub_nonneg.mpr hx.2.2
  have hout := PhysicalHeatPositiveCone.physical_evolution_positive_all
    r hr t u hnonneg
  have hgapout := PhysicalHeatPositiveCone.physical_evolution_positive_all
    r hr t ((M : ℂ) • basis 0 - u) hgap
  have hs : evolution r t ((M : ℂ) • basis 0 - u) =
      (M : ℂ) • basis 0 - evolution r t u := by
    rw [map_sub, map_smul, stationary_mode r 0 hr0 t]
  rw [hs] at hgapout
  filter_upwards [hout,hgapout,basis_zero_ae_one,
    Lp.coeFn_smul (M : ℂ) (basis 0),
    Lp.coeFn_sub ((M : ℂ) • basis 0) (evolution r t u)]
      with x hx hg hb hsm hsub
  refine ⟨hx.1,hx.2,?_⟩
  simp only [Pi.sub_apply] at hsub
  rw [hsub,hsm, Pi.smul_apply, hb] at hg
  have hm := hg.2
  simpa using sub_nonneg.mp hm

theorem physical_evolution_real_interval (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) (u : E) (m M : ℝ)
    (hu : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).im = 0 ∧ m ≤ (u x).re ∧ (u x).re ≤ M) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((evolution r t u) x).im = 0 ∧
      m ≤ ((evolution r t u) x).re ∧
      ((evolution r t u) x).re ≤ M := by
  have hlow : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((u - (m : ℂ) • basis 0) x).im = 0 ∧
        0 ≤ ((u - (m : ℂ) • basis 0) x).re := by
    filter_upwards [hu,basis_zero_ae_one,
      Lp.coeFn_smul (m : ℂ) (basis 0),
      Lp.coeFn_sub u ((m : ℂ) • basis 0)] with x hx hb hsm hsub
    simp only [Pi.sub_apply] at hsub
    rw [hsub,hsm,Pi.smul_apply,hb]
    constructor
    · simp [hx.1]
    · simpa using sub_nonneg.mpr hx.2.1
  have hhigh : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (((M : ℂ) • basis 0 - u) x).im = 0 ∧
        0 ≤ (((M : ℂ) • basis 0 - u) x).re := by
    filter_upwards [hu,basis_zero_ae_one,
      Lp.coeFn_smul (M : ℂ) (basis 0),
      Lp.coeFn_sub ((M : ℂ) • basis 0) u] with x hx hb hsm hsub
    simp only [Pi.sub_apply] at hsub
    rw [hsub,hsm,Pi.smul_apply,hb]
    constructor
    · simp [hx.1]
    · simpa using sub_nonneg.mpr hx.2.2
  have hlowout := PhysicalHeatPositiveCone.physical_evolution_positive_all
    r hr t (u - (m : ℂ) • basis 0) hlow
  have hhighout := PhysicalHeatPositiveCone.physical_evolution_positive_all
    r hr t ((M : ℂ) • basis 0 - u) hhigh
  have hloweq : evolution r t (u - (m : ℂ) • basis 0) =
      evolution r t u - (m : ℂ) • basis 0 := by
    rw [map_sub,map_smul,stationary_mode r 0 hr0 t]
  have hhigheq : evolution r t ((M : ℂ) • basis 0 - u) =
      (M : ℂ) • basis 0 - evolution r t u := by
    rw [map_sub,map_smul,stationary_mode r 0 hr0 t]
  rw [hloweq] at hlowout
  rw [hhigheq] at hhighout
  filter_upwards [hlowout,hhighout,basis_zero_ae_one,
    Lp.coeFn_smul (m : ℂ) (basis 0),
    Lp.coeFn_smul (M : ℂ) (basis 0),
    Lp.coeFn_sub (evolution r t u) ((m : ℂ) • basis 0),
    Lp.coeFn_sub ((M : ℂ) • basis 0) (evolution r t u)]
      with x hl hh hb hsm hsM hsl hsh
  simp only [Pi.sub_apply] at hsl hsh
  rw [hsl,hsm,Pi.smul_apply,hb] at hl
  rw [hsh,hsM,Pi.smul_apply,hb] at hh
  constructor
  · have hi := hl.1
    simpa using hi
  constructor
  · simpa using sub_nonneg.mp hl.2
  · simpa using sub_nonneg.mp hh.2

theorem physical_evolution_real_abs_bound (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) (u : E) (M : ℝ)
    (hu : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).im = 0 ∧ |(u x).re| ≤ M) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((evolution r t u) x).im = 0 ∧
      |((evolution r t u) x).re| ≤ M := by
  have hinterval : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).im = 0 ∧ -M ≤ (u x).re ∧ (u x).re ≤ M := by
    filter_upwards [hu] with x hx
    exact ⟨hx.1, (abs_le.mp hx.2).1, (abs_le.mp hx.2).2⟩
  filter_upwards [physical_evolution_real_interval r hr hr0 t u (-M) M hinterval]
    with x hx
  exact ⟨hx.1, abs_le.mpr ⟨hx.2.1,hx.2.2⟩⟩

theorem clip_sub_clip_neg_of_real (z : ℂ) (hz : z.im = 0) :
    PhysicalHeatPositiveCone.clip z - PhysicalHeatPositiveCone.clip (-z) = z := by
  apply Complex.ext
  · simp [PhysicalHeatPositiveCone.clip, posPart_sub_negPart]
  · simp [PhysicalHeatPositiveCone.clip, hz]

theorem clipL2_sub_clipL2_neg_of_real (u : E)
    (hu : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume, (u x).im = 0) :
    clipL2 u - clipL2 (-u) = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (clipL2 u) (clipL2 (-u)),
    LipschitzWith.coeFn_compLp clip_lipschitz clip_zero u,
    LipschitzWith.coeFn_compLp clip_lipschitz clip_zero (-u),
    Lp.coeFn_neg u, hu] with x hsub hp hn hneg hx
  simp only [Function.comp_def] at hp hn
  change (clipL2 u) x = clip (u x) at hp
  change (clipL2 (-u)) x = clip ((-u) x) at hn
  simp only [Pi.sub_apply] at hsub
  rw [hsub,hp,hn,hneg,Pi.neg_apply]
  exact clip_sub_clip_neg_of_real (u x) hx

theorem clipL2_nonnegative (u : E) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((clipL2 u) x).im = 0 ∧ 0 ≤ ((clipL2 u) x).re := by
  filter_upwards [LipschitzWith.coeFn_compLp clip_lipschitz clip_zero u]
    with x hx
  simp only [Function.comp_def] at hx
  change (clipL2 u) x = clip (u x) at hx
  rw [hx]
  simp [clip]

theorem physical_evolution_real (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (t : ℝ≥0) (u : E)
    (hu : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume, (u x).im = 0) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((evolution r t u) x).im = 0 := by
  have hdecomp := clipL2_sub_clipL2_neg_of_real u hu
  have hp := PhysicalHeatPositiveCone.physical_evolution_positive_all
    r hr t (clipL2 u) (clipL2_nonnegative u)
  have hn := PhysicalHeatPositiveCone.physical_evolution_positive_all
    r hr t (clipL2 (-u)) (clipL2_nonnegative (-u))
  rw [← hdecomp, map_sub]
  filter_upwards [hp,hn,
    Lp.coeFn_sub (evolution r t (clipL2 u)) (evolution r t (clipL2 (-u)))]
      with x hx hy hsub
  simp only [Pi.sub_apply] at hsub
  rw [hsub]
  simp [hx.1,hy.1]

theorem physical_evolution_monotone_real (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (t : ℝ≥0) (u v : E)
    (hu : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume, (u x).im = 0)
    (hv : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume, (v x).im = 0)
    (huv : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).re ≤ (v x).re) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((evolution r t u) x).im = 0 ∧
      ((evolution r t v) x).im = 0 ∧
      ((evolution r t u) x).re ≤ ((evolution r t v) x).re := by
  have hgap : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((v-u) x).im = 0 ∧ 0 ≤ ((v-u) x).re := by
    filter_upwards [hu,hv,huv,Lp.coeFn_sub v u] with x hux hvx hle hsub
    simp only [Pi.sub_apply] at hsub
    rw [hsub]
    exact ⟨by simp [hux,hvx], by simpa using sub_nonneg.mpr hle⟩
  have hout := PhysicalHeatPositiveCone.physical_evolution_positive_all
    r hr t (v-u) hgap
  rw [map_sub] at hout
  filter_upwards [physical_evolution_real r hr t u hu,
    physical_evolution_real r hr t v hv, hout,
    Lp.coeFn_sub (evolution r t v) (evolution r t u)]
      with x hux hvx hgapx hsub
  simp only [Pi.sub_apply] at hsub
  rw [hsub] at hgapx
  exact ⟨hux,hvx,by simpa using sub_nonneg.mp hgapx.2⟩

theorem integral_torusSynthesis (f : Fourier) :
    (∫ x : UnitAddTorus (Fin 3), (torusSynthesis f) x) = f.coeff 0 := by
  have h := lift_coeff f 0
  rw [← torusSynthesis_toLp, UnitAddTorus.mFourierCoeff_toLp] at h
  simpa [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero] using h

theorem integral_heat_square_real (r : Wave → ℝ≥0)
    (t : ℝ≥0) (f : Fourier) :
    (∫ x : UnitAddTorus (Fin 3),
      (torusSynthesis (FiniteHeatSquarePositivity.heatAction
        (fun k => (r k : ℝ)) (t : ℝ)
        (FiniteFourierReality.reflection f * f)) x).re) =
      ((FiniteHeatSquarePositivity.heatAction
        (fun k => (r k : ℝ)) (t : ℝ)
        (FiniteFourierReality.reflection f * f)).coeff 0).re := by
  have hint : Integrable (fun x : UnitAddTorus (Fin 3) =>
      (torusSynthesis (FiniteHeatSquarePositivity.heatAction
        (fun k => (r k : ℝ)) (t : ℝ)
        (FiniteFourierReality.reflection f * f))) x) volume :=
    (torusSynthesis _).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := congrArg Complex.re (integral_torusSynthesis
    (FiniteHeatSquarePositivity.heatAction
      (fun k => (r k : ℝ)) (t : ℝ)
      (FiniteFourierReality.reflection f * f)))
  simpa only [← RCLike.re_to_complex, integral_re hint] using h

theorem integral_heat_square_one (r : Wave → ℝ≥0)
    (hr0 : r 0 = 0) (t : ℝ≥0) (f : Fourier)
    (hf : (FiniteFourierReality.reflection f * f).coeff 0 = 1) :
    (∫ x : UnitAddTorus (Fin 3),
      (torusSynthesis (FiniteHeatSquarePositivity.heatAction
        (fun k => (r k : ℝ)) (t : ℝ)
        (FiniteFourierReality.reflection f * f)) x).re) = 1 := by
  rw [integral_heat_square_real]
  rw [heatAction_coeff, hr0, hf]
  norm_num

def heatSquareMeasure (r : Wave → ℝ≥0) (t : ℝ≥0) (f : Fourier) :
    Measure (UnitAddTorus (Fin 3)) :=
  volume.withDensity (fun x => ENNReal.ofReal
    (torusSynthesis (FiniteHeatSquarePositivity.heatAction
      (fun k => (r k : ℝ)) (t : ℝ)
      (FiniteFourierReality.reflection f * f)) x).re)

theorem heatSquareMeasure_probability (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) (f : Fourier)
    (hf : (FiniteFourierReality.reflection f * f).coeff 0 = 1) :
    IsProbabilityMeasure (heatSquareMeasure r t f) := by
  constructor
  change (volume.withDensity (fun x => ENNReal.ofReal
    (torusSynthesis (FiniteHeatSquarePositivity.heatAction
      (fun k => (r k : ℝ)) (t : ℝ)
      (FiniteFourierReality.reflection f * f)) x).re)) Set.univ = 1
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hint : Integrable (fun x : UnitAddTorus (Fin 3) =>
      (torusSynthesis (FiniteHeatSquarePositivity.heatAction
        (fun k => (r k : ℝ)) (t : ℝ)
        (FiniteFourierReality.reflection f * f)) x).re) volume :=
    (Complex.continuous_re.comp (torusSynthesis _).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnonneg : 0 ≤ᵐ[volume] (fun x : UnitAddTorus (Fin 3) =>
      (torusSynthesis (FiniteHeatSquarePositivity.heatAction
        (fun k => (r k : ℝ)) (t : ℝ)
        (FiniteFourierReality.reflection f * f)) x).re) :=
    Filter.Eventually.of_forall (fun x =>
      (torus_heat_square_nonnegative _ hr t t.coe_nonneg f x).2)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [integral_heat_square_one r hr0 t f hf]
  norm_num

theorem square_coeff_zero_energy (f : Fourier) :
    (FiniteFourierReality.reflection f * f).coeff 0 =
      ∑ k ∈ f.coeff.support, conj (f.coeff k) * f.coeff k := by
  rw [← integral_torusSynthesis]
  simp_rw [PhysicalHeatPositiveCone.torusSynthesis_square]
  rw [← physical_inner_lift f f]
  apply integral_congr_ae
  have h := (PhysicalHeatSquareBridge.torusSynthesis_toLp f).symm
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (E := ℂ) (p := 2)
    (volume : Measure (UnitAddTorus (Fin 3))) (torusSynthesis f)] with x hx
  rw [← h] at hx
  rw [hx]

theorem heatSquareMeasure_probability_of_energy (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) (f : Fourier)
    (hf : (∑ k ∈ f.coeff.support,
      conj (f.coeff k) * f.coeff k) = 1) :
    IsProbabilityMeasure (heatSquareMeasure r t f) := by
  apply heatSquareMeasure_probability r hr hr0 t f
  rw [square_coeff_zero_energy, hf]

def heatSquareProbability (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) (f : Fourier)
    (hf : (∑ k ∈ f.coeff.support,
      conj (f.coeff k) * f.coeff k) = 1) :
    ProbabilityMeasure (UnitAddTorus (Fin 3)) :=
  ⟨heatSquareMeasure r t f,
    heatSquareMeasure_probability_of_energy r hr hr0 t f hf⟩

theorem heatSquareMeasure_fourierCoeff (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (t : ℝ≥0) (f : Fourier) (k : Wave) :
    (∫ x : UnitAddTorus (Fin 3),
      (UnitAddTorus.mFourier (-k)) x ∂heatSquareMeasure r t f) =
      (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) *
        (FiniteFourierReality.reflection f * f).coeff k := by
  let g : C(UnitAddTorus (Fin 3), ℂ) :=
    torusSynthesis (FiniteHeatSquarePositivity.heatAction
      (fun j => (r j : ℝ)) (t : ℝ)
      (FiniteFourierReality.reflection f * f))
  have hg (x : UnitAddTorus (Fin 3)) :
      (g x).im = 0 ∧ 0 ≤ (g x).re :=
    torus_heat_square_nonnegative _ hr t t.coe_nonneg f x
  have hdens : Measurable (fun x : UnitAddTorus (Fin 3) =>
      ENNReal.ofReal (g x).re) :=
    (Complex.continuous_re.comp g.continuous).measurable.ennreal_ofReal
  have htop : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ENNReal.ofReal (g x).re < ⊤ := by
    filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
  change (∫ x, (UnitAddTorus.mFourier (-k)) x
      ∂volume.withDensity (fun x => ENNReal.ofReal (g x).re)) = _
  rw [integral_withDensity_eq_integral_toReal_smul hdens htop]
  have hpoint (x : UnitAddTorus (Fin 3)) :
      (ENNReal.ofReal (g x).re).toReal • (UnitAddTorus.mFourier (-k)) x =
        (UnitAddTorus.mFourier (-k)) x • g x := by
    rw [ENNReal.toReal_ofReal (hg x).2]
    have he : ((g x).re : ℂ) = g x := by
      apply Complex.ext
      · rfl
      · simp [hg x |>.1]
    simp [smul_eq_mul, he, mul_comm]
  simp_rw [hpoint]
  change UnitAddTorus.mFourierCoeff g k = _
  rw [← UnitAddTorus.mFourierCoeff_toLp, torusSynthesis_toLp,
    lift_coeff, heatAction_coeff]
  ring_nf

end OperatorDerivativeRewrite.Foundation.PhysicalHeatMarkovOrder
