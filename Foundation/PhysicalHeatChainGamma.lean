import Foundation.PhysicalHeatChainMarginals
import Foundation.FourierGammaNormalization

/-!
# The Fourier carré-du-champ as a physical heat-chain short-time covariance

The actual fixed-step heat chain started at the torus origin has an exact
finite-time pairing of conjugate character increments. Its real short-time
right derivative equals twice the previously verified Fourier Gamma kernel.
The frequency difference, symbol evenness and right-sided time domain are
explicit. This is a process-level covariance identity, not a positive
Bakry curvature or spectral-gap theorem.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open FourierGammaNormalization
open PhysicalHeatKernel PhysicalHeatChain
open FiniteStableGamma.Core
open MeasureTheory AddCircle ProbabilityTheory Function Preorder
open scoped NNReal ProbabilityTheory

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatChain

private theorem symbol_even (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0) (k : Wave) :
    r (-k) = r k := by
  have h0 : (fun j : Wave => (r j : ℝ)) 0 = 0 := by simp [hr0]
  have hp := (normalized_gamma_iff_covariance (fun j : Wave => (r j : ℝ)) h0).mpr hr
  have he := even_of_gamma_positive (fun j : Wave => (r j : ℝ)) h0 hp k
  exact_mod_cast he

theorem heatKernel_increment_pair (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (t : ℝ≥0) (k l : Wave) :
    (∫ z, (UnitAddTorus.mFourier (-k) z - 1) *
      (UnitAddTorus.mFourier l z - 1) ∂heatKernel r hr hr0 t (0 : UnitAddTorus (Fin 3))) =
      (Real.exp (-((t : ℝ) * (r (k-l) : ℝ))) : ℂ) -
      (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) -
      (Real.exp (-((t : ℝ) * (r l : ℝ))) : ℂ) + 1 := by
  let μ := heatKernel r hr hr0 t (0 : UnitAddTorus (Fin 3))
  have hprod (z : UnitAddTorus (Fin 3)) :
      UnitAddTorus.mFourier (-k) z * UnitAddTorus.mFourier l z =
        UnitAddTorus.mFourier (-(k-l)) z := by
    rw [← UnitAddTorus.mFourier_add]
    congr 1
    abel
  have hzero (q : Wave) :
      UnitAddTorus.mFourier q (0 : UnitAddTorus (Fin 3)) = 1 := by
    simp [UnitAddTorus.mFourier]
  have hI (q : Wave) :
      (∫ z, UnitAddTorus.mFourier (-q) z ∂μ) =
        (Real.exp (-((t : ℝ) * (r q : ℝ))) : ℂ) := by
    simpa [μ, hzero] using heatKernel_character r hr hr0 t 0 q
  have hl : (∫ z, UnitAddTorus.mFourier l z ∂μ) =
      (Real.exp (-((t : ℝ) * (r l : ℝ))) : ℂ) := by
    simpa [symbol_even r hr hr0 l] using hI (-l)
  have hint (q : Wave) : Integrable (fun z => UnitAddTorus.mFourier q z) μ :=
    (UnitAddTorus.mFourier q).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ z, (UnitAddTorus.mFourier (-(k-l)) z -
          UnitAddTorus.mFourier (-k) z - UnitAddTorus.mFourier l z + 1) ∂μ := by
        congr 1
        funext z
        rw [← hprod]
        ring
    _ = (∫ z, UnitAddTorus.mFourier (-(k-l)) z ∂μ) -
          (∫ z, UnitAddTorus.mFourier (-k) z ∂μ) -
          (∫ z, UnitAddTorus.mFourier l z ∂μ) + 1 := by
        have hA := hint (-(k-l))
        have hB := hint (-k)
        have hC := hint l
        rw [integral_add, integral_sub, integral_sub]
        all_goals first
          | exact hA
          | exact hB
          | exact hC
          | exact hA.sub hB
          | exact (hA.sub hB).sub hC
          | exact integrable_const _
          | simp
    _ = _ := by rw [hI (k-l), hI k, hl]

theorem chainLaw_increment_pair (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (t : ℝ≥0) (k l : Wave) :
    (∫ path, (UnitAddTorus.mFourier (-k) (path 1) - 1) *
      (UnitAddTorus.mFourier l (path 1) - 1)
      ∂chainLaw r hr hr0 t (0 : UnitAddTorus (Fin 3))) =
      (Real.exp (-((t : ℝ) * (r (k-l) : ℝ))) : ℂ) -
      (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) -
      (Real.exp (-((t : ℝ) * (r l : ℝ))) : ℂ) + 1 := by
  let f : UnitAddTorus (Fin 3) → ℂ := fun z =>
    (UnitAddTorus.mFourier (-k) z - 1) * (UnitAddTorus.mFourier l z - 1)
  change (∫ path, f (path 1) ∂chainLaw r hr hr0 t (0 : UnitAddTorus (Fin 3))) = _
  rw [← integral_map (by exact (measurable_pi_apply 1).aemeasurable)]
  · rw [chainLaw_one]
    exact heatKernel_increment_pair r hr hr0 t k l
  · have hc : Continuous (fun z : UnitAddTorus (Fin 3) =>
        (UnitAddTorus.mFourier (-k) z - 1) *
          (UnitAddTorus.mFourier l z - 1)) := by fun_prop
    exact hc.measurable.aestronglyMeasurable

theorem incrementPairValue_hasDerivAt_zero (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (k l : Wave) :
    HasDerivAt (fun t : ℝ =>
      Real.exp (-(t * (r (k-l) : ℝ))) -
      Real.exp (-(t * (r k : ℝ))) -
      Real.exp (-(t * (r l : ℝ))) + 1)
      (2 * kernel (fun q => (r q : ℝ)) k l) 0 := by
  have hExp (a : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-(t*a))) (-a) 0 := by
    have hl : HasDerivAt (fun t : ℝ => -(t*a)) (-a) 0 := by
      have hh := ((hasDerivAt_id (0:ℝ)).mul_const a).neg
      convert hh using 1
      · ext t
        rfl
      · simp
    have hh := (Real.hasDerivAt_exp (-((0:ℝ)*a))).comp 0 hl
    convert hh using 1
    · rfl
    · simp
  have h := (((hExp (r (k-l) : ℝ)).sub (hExp (r k : ℝ))).sub
    (hExp (r l : ℝ))).add_const 1
  have he : -((r (k-l) : ℝ)) - -((r k : ℝ)) - -((r l : ℝ)) =
      2 * kernel (fun q => (r q : ℝ)) k l := by
    simp only [kernel]
    have hswap : l-k = -(k-l) := by abel
    rw [hswap, symbol_even r hr hr0 (k-l)]
    ring
  simpa only [Pi.add_apply, Pi.sub_apply, he] using h

theorem chainLaw_incrementPair_hasDerivWithinAt_zero (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (k l : Wave) :
    HasDerivWithinAt (fun t : ℝ =>
      (∫ path, (UnitAddTorus.mFourier (-k) (path 1) - 1) *
        (UnitAddTorus.mFourier l (path 1) - 1)
        ∂chainLaw r hr hr0 (Real.toNNReal t) (0 : UnitAddTorus (Fin 3))).re)
      (2 * kernel (fun q => (r q : ℝ)) k l) (Set.Ici 0) 0 := by
  apply (incrementPairValue_hasDerivAt_zero r hr hr0 k l).hasDerivWithinAt.congr_of_mem
  · intro t ht
    rw [chainLaw_increment_pair]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    simp [max_eq_left (Set.mem_Ici.mp ht)]
  · simp

end OperatorDerivativeRewrite.Foundation.PhysicalHeatChain
