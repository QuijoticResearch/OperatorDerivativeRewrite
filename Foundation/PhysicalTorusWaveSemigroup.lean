import Foundation.WaveDiagonalSemigroup
import Mathlib.Analysis.Fourier.AddCircleMulti
/-! A completed Haar-L² realization of nonnegative Fourier multiplier semigroups
on the unit-period three-torus. Mathlib's multivariate Fourier Hilbert basis
identifies physical L² with the verified coefficient ℓ² space. The real-coordinate
period-2π box-average model in `WavePhysicalFourierBridge` requires a separate
scaling identification; Markov positivity is not asserted here. -/
open MeasureTheory Filter Set AddCircle
open scoped Topology NNReal
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PhysicalTorusWaveSemigroup
open FiniteFourierDifferentialTrace WaveDiagonalSemigroup

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev E := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))
def basis : HilbertBasis Wave ℂ E := UnitAddTorus.mFourierBasis

def evolution (r : Wave → ℝ≥0) (t : ℝ≥0) : E →L[ℂ] E :=
  basis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WaveDiagonalSemigroup.evolution r t).comp
      basis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem repr_evolution (r : Wave → ℝ≥0) (t : ℝ≥0) (f : E) :
    basis.repr (evolution r t f) =
      WaveDiagonalSemigroup.evolution r t (basis.repr f) := by
  change basis.repr (basis.repr.symm
    (WaveDiagonalSemigroup.evolution r t (basis.repr f))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem evolution_coeff (r : Wave → ℝ≥0) (t : ℝ≥0) (f : E) (k : Wave) :
    UnitAddTorus.mFourierCoeff (evolution r t f) k =
      UnitAddTorus.mFourierCoeff f k * WaveDiagonalSemigroup.multiplier r t k := by
  have h : basis.repr (evolution r t f) k =
      basis.repr f k * WaveDiagonalSemigroup.multiplier r t k := by
    change basis.repr (basis.repr.symm
      (WaveDiagonalSemigroup.evolution r t (basis.repr f))) k = _
    rw [LinearIsometryEquiv.apply_symm_apply,WaveDiagonalSemigroup.evolution_apply]
  simpa only [basis,UnitAddTorus.mFourierBasis_repr] using h

theorem contraction (r : Wave → ℝ≥0) (t : ℝ≥0) (f : E) :
    ‖evolution r t f‖ ≤ ‖f‖ := by
  have h := WaveDiagonalSemigroup.contraction r t (basis.repr f)
  simpa [evolution] using h

theorem evolution_zero (r : Wave → ℝ≥0) (f : E) : evolution r 0 f = f := by
  apply basis.repr.injective
  ext k
  simp only [basis,UnitAddTorus.mFourierBasis_repr]
  simp [evolution_coeff,WaveDiagonalSemigroup.multiplier]

theorem evolution_add (r : Wave → ℝ≥0) (s t : ℝ≥0) (f : E) :
    evolution r s (evolution r t f) = evolution r (s+t) f := by
  apply basis.repr.injective
  ext k
  simp only [basis,UnitAddTorus.mFourierBasis_repr]
  simp only [evolution_coeff,WaveDiagonalSemigroup.multiplier,
    NNReal.coe_add,mul_add,Real.exp_add,Complex.ofReal_mul]
  ring

theorem evolution_mode (r : Wave → ℝ≥0) (t : ℝ≥0) (k : Wave) :
    evolution r t (basis k) =
      WaveDiagonalSemigroup.multiplier r t k • basis k := by
  apply basis.repr.injective
  rw [repr_evolution, map_smul, basis.repr_self]
  ext l
  simp only [WaveDiagonalSemigroup.evolution_apply, lp.coeFn_smul, Pi.smul_apply]
  by_cases h : l = k
  · subst l
    simp [lp.single_apply, smul_eq_mul, mul_comm]
  · simp [lp.single_apply, h]

theorem stationary_mode (r : Wave → ℝ≥0) (k : Wave) (hk : r k = 0)
    (t : ℝ≥0) : evolution r t (basis k) = basis k := by
  rw [evolution_mode]
  simp [WaveDiagonalSemigroup.multiplier, hk]

theorem strong_continuity (r : Wave → ℝ≥0) (f : E) :
    Continuous (fun t => evolution r t f) := by
  have h := WaveDiagonalSemigroup.strong_continuity r (basis.repr f)
  exact basis.repr.symm.continuous.comp h

def slope (r : Wave → ℝ≥0) (f : E) (t : ℝ) : E :=
  (t⁻¹:ℂ) • (evolution r t.toNNReal f-f)

theorem repr_slope (r : Wave → ℝ≥0) (f : E) (t : ℝ) :
    basis.repr (slope r f t) =
      WaveDiagonalSemigroup.slope r (basis.repr f) t := by
  simp only [slope,WaveDiagonalSemigroup.slope,map_smul,map_sub,repr_evolution]

theorem generator_iff (r : Wave → ℝ≥0) (f g : E) :
    Tendsto (slope r f) (𝓝[>] 0) (𝓝 g) ↔
      ∀ k : Wave, UnitAddTorus.mFourierCoeff g k =
        -((r k : ℝ):ℂ) * UnitAddTorus.mFourierCoeff f k := by
  have hb : Tendsto (slope r f) (𝓝[>] 0) (𝓝 g) ↔
      Tendsto (WaveDiagonalSemigroup.slope r (basis.repr f))
        (𝓝[>] 0) (𝓝 (basis.repr g)) := by
    constructor
    · intro h
      simpa only [Function.comp_def,repr_slope] using
        basis.repr.continuousAt.tendsto.comp h
    · intro h
      have hh : Tendsto (fun t => basis.repr.symm
          (WaveDiagonalSemigroup.slope r (basis.repr f) t))
          (𝓝[>] 0) (𝓝 g) := by
        simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using
          basis.repr.symm.continuousAt.tendsto.comp h
      convert hh using 1
      ext t
      rw [← repr_slope,LinearIsometryEquiv.symm_apply_apply]
  rw [hb,WaveDiagonalSemigroup.generator_iff]
  simp only [WaveDiagonalSemigroup.graph,Set.mem_ofPred_eq,
    basis,UnitAddTorus.mFourierBasis_repr]

theorem generator_domain (r : Wave → ℝ≥0) (f : E) :
    (∃ g : E, Tendsto (slope r f) (𝓝[>] 0) (𝓝 g)) ↔
      Memℓp (fun k : Wave => -((r k : ℝ):ℂ) *
        UnitAddTorus.mFourierCoeff f k) 2 := by
  constructor
  · rintro ⟨g,hg⟩
    have hh : (basis.repr f,basis.repr g) ∈ WaveDiagonalSemigroup.graph r := by
      intro k
      simpa only [basis,UnitAddTorus.mFourierBasis_repr] using
        ((generator_iff r f g).mp hg) k
    have hm := (WaveDiagonalSemigroup.graph_domain_iff r (basis.repr f)).mp
      ⟨basis.repr g,hh⟩
    simpa only [basis,UnitAddTorus.mFourierBasis_repr] using hm
  · intro h
    have hm : Memℓp (fun k : Wave => -((r k : ℝ):ℂ) * basis.repr f k) 2 := by
      simpa only [basis,UnitAddTorus.mFourierBasis_repr] using h
    rcases (WaveDiagonalSemigroup.graph_domain_iff r (basis.repr f)).mpr hm with ⟨v,hv⟩
    refine ⟨basis.repr.symm v, ?_⟩
    apply (generator_iff r f (basis.repr.symm v)).mpr
    intro k
    have he : basis.repr (basis.repr.symm v) k =
        -((r k : ℝ):ℂ) * basis.repr f k := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hv k
    simpa only [basis,UnitAddTorus.mFourierBasis_repr] using he

def graph (r : Wave → ℝ≥0) : Set (E × E) :=
  {p | ∀ k : Wave, UnitAddTorus.mFourierCoeff p.2 k =
    -((r k : ℝ):ℂ) * UnitAddTorus.mFourierCoeff p.1 k}

theorem graph_closed (r : Wave → ℝ≥0) : IsClosed (graph r) := by
  have hc (k : Wave) : Continuous (fun f : E => UnitAddTorus.mFourierCoeff f k) := by
    have h : Continuous (fun f : E => basis.repr f k) :=
      (lp.evalCLM ℂ (fun _ : Wave => ℂ) 2 k).continuous.comp basis.repr.continuous
    simpa only [basis,UnitAddTorus.mFourierBasis_repr] using h
  have he : graph r = ⋂ k : Wave, {p : E × E |
      UnitAddTorus.mFourierCoeff p.2 k =
        -((r k : ℝ):ℂ) * UnitAddTorus.mFourierCoeff p.1 k} := by
    ext p
    simp [graph]
  rw [he]
  exact isClosed_iInter fun k => isClosed_eq ((hc k).comp continuous_snd)
    (continuous_const.mul ((hc k).comp continuous_fst))

private theorem rate_cast (a γ : Fin 3 → ℝ) (ha : ∀ j, 0 ≤ a j) (k : Wave) :
    (((WaveDiagonalSemigroup.rate a γ ha k : ℝ) : ℂ)) =
      (AnisotropicStableGamma.anisotropicSymbol a γ k : ℂ) := rfl

theorem anisotropic_generator_iff (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (f g : E) :
    Tendsto (slope (WaveDiagonalSemigroup.rate a γ ha) f) (𝓝[>] 0) (𝓝 g) ↔
      ∀ k : Wave, UnitAddTorus.mFourierCoeff g k =
        -((AnisotropicStableGamma.anisotropicSymbol a γ k : ℝ):ℂ) *
          UnitAddTorus.mFourierCoeff f k := by
  simpa only [rate_cast] using
    (generator_iff (WaveDiagonalSemigroup.rate a γ ha) f g)

theorem anisotropic_generator_domain (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (f : E) :
    (∃ g : E, Tendsto (slope (WaveDiagonalSemigroup.rate a γ ha) f)
      (𝓝[>] 0) (𝓝 g)) ↔
      Memℓp (fun k : Wave =>
        -((AnisotropicStableGamma.anisotropicSymbol a γ k : ℝ):ℂ) *
          UnitAddTorus.mFourierCoeff f k) 2 := by
  simpa only [rate_cast] using
    (generator_domain (WaveDiagonalSemigroup.rate a γ ha) f)

end OperatorDerivativeRewrite.Foundation.PhysicalTorusWaveSemigroup
