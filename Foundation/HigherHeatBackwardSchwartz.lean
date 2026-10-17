import Foundation.HigherHeatSchwartzTransition
import Foundation.HigherHeatSchwartzCalculus

/-! Genuine bounded backward Schwartz fields, signed-kernel martingale gains, and grid representations. -/
noncomputable section
open MeasureTheory FourierTransform Filter
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatBackwardSchwartz
open HigherHeatL2 HigherHeatSignedLaws HigherHeatSchwartzSemigroup HigherHeatSchwartzTransition
open HigherHeatBackwardFourier HigherHeatCylinderFourier

theorem evolve_fourier (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    𝓕 (evolve m hm t f) ξ=symbol m t ξ*𝓕 f ξ := by
  by_cases ht : 0 < t
  · rw [evolve_positive m hm t ht,SchwartzMap.fourier_convolution]
    simp only [GaussianSchwartzKernel.evenKernel_fourier,SchwartzMap.pairing_apply,
      ContinuousLinearMap.mul_apply',GaussianSchwartzKernel.evenSymbol_apply]
  · have ht0 : t=0 := le_antisymm (le_of_not_gt ht) (by positivity)
    subst t
    rw [evolve_zero,symbol_zero,one_mul]

theorem evolve_spectral_bound (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    ‖evolve m hm t f x‖ ≤ ∫ ξ : ℝ, ‖𝓕 f ξ‖ := by
  rw [← HigherHeatSchwartzCalculus.inverse_phase (evolve m hm t f) x]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Eventually.of_forall fun ξ => norm_nonneg _) (𝓕 f).integrable.norm
  exact Eventually.of_forall fun ξ => by
    change ‖𝓕 (evolve m hm t f) ξ*phase (-ξ) x‖ ≤ ‖𝓕 f ξ‖
    rw [evolve_fourier,norm_mul,phase_norm,mul_one,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (symbol_norm_le m t ξ)

def backward (m : ℕ) (hm : 0 < m) (T s : ℝ≥0) (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  evolve m hm (T-s) f

theorem backward_terminal (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    backward m hm T T f=f := by simp [backward,evolve_zero]

theorem backward_initial (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℂ)) :
    backward m hm T 0 f 0=HigherHeatSchwartzCalculus.mean m T f := by
  change evolve m hm (T-0) f 0=_
  rw [tsub_zero,← transition_evolve m hm T hT f 0]
  simp only [transition,zero_add]
  exact (HigherHeatSchwartzCalculus.mean_eq_kernel m hm T hT f).symm

theorem backward_bound (m : ℕ) (hm : 0 < m) (T s : ℝ≥0) (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    ‖backward m hm T s f x‖ ≤ ∫ ξ : ℝ, ‖𝓕 f ξ‖ := evolve_spectral_bound m hm (T-s) f x

theorem backward_step (m : ℕ) (hm : 0 < m) (T s t : ℝ≥0) (hst : s < t) (ht : t ≤ T)
    (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    transition m hm (t-s) (tsub_pos_iff_lt.mpr hst) (backward m hm T t f) x=
      backward m hm T s f x := by
  have he : (t-s)+(T-t)=T-s := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,NNReal.coe_sub ht,NNReal.coe_sub hst.le,
      NNReal.coe_sub (hst.le.trans ht)]
    ring
  change transition m hm (t-s) _ (evolve m hm (T-t) f) x=evolve m hm (T-s) f x
  rw [transition_evolve m hm (t-s) (tsub_pos_iff_lt.mpr hst),evolve_add,he]

def gain (m : ℕ) (hm : 0 < m) (T s t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) (x z : ℝ) : ℂ :=
  backward m hm T t f (x+z)-backward m hm T s f x

theorem gain_bound (m : ℕ) (hm : 0 < m) (T s t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) (x z : ℝ) :
    ‖gain m hm T s t f x z‖ ≤ 2*∫ ξ : ℝ, ‖𝓕 f ξ‖ :=
  (norm_sub_le _ _).trans (by linarith [backward_bound m hm T t f (x+z),backward_bound m hm T s f x])

theorem gain_kernel_zero (m : ℕ) (hm : 0 < m) (T s t : ℝ≥0) (hst : s < t) (ht : t ≤ T)
    (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    (∫ z : ℝ, gain m hm T s t f x z*(realKernel m hm (t-s) (tsub_pos_iff_lt.mpr hst) z:ℂ))=0 := by
  let K := realKernel m hm (t-s) (tsub_pos_iff_lt.mpr hst)
  have h1 := transition_integrable m hm (t-s) (tsub_pos_iff_lt.mpr hst) (backward m hm T t f) x
  have h2 := (K.integrable (μ := volume)).ofReal.const_mul (backward m hm T s f x)
  calc
    _ = ∫ z : ℝ, backward m hm T t f (x+z)*(K z:ℂ)-backward m hm T s f x*(K z:ℂ) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => sub_mul _ _ _
    _ = (∫ z : ℝ, backward m hm T t f (x+z)*(K z:ℂ))-
        (∫ z : ℝ, backward m hm T s f x*(K z:ℂ)) := integral_sub h1 h2
    _ = 0 := by
      change transition m hm (t-s) _ (backward m hm T t f) x-
        (∫ z : ℝ, backward m hm T s f x*(K z:ℂ))=0
      rw [backward_step m hm T s t hst ht,integral_const_mul,integral_complex_ofReal,realKernel_integral]
      simp

def gridIntegral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (f : 𝓢(ℝ,ℂ)) (x : ℕ → ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, gain m hm T (grid j) (grid (j+1)) f (x j) (x (j+1)-x j)

theorem grid_representation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℝ≥0) (n : ℕ) (h0 : grid 0=0) (hn : grid n=T)
    (f : 𝓢(ℝ,ℂ)) (x : ℕ → ℝ) (hx : x 0=0) :
    gridIntegral m hm T grid n f x=f (x n)-HigherHeatSchwartzCalculus.mean m T f := by
  unfold gridIntegral
  simp only [gain,add_sub_cancel]
  rw [Finset.sum_range_sub (fun j => backward m hm T (grid j) f (x j)) n,hn,h0,hx,
    backward_terminal,backward_initial m hm T hT]

theorem grid_eq_spectral_integral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℝ≥0) (n : ℕ) (hg : Monotone grid) (h0 : grid 0=0) (hn : grid n=T)
    (f : 𝓢(ℝ,ℂ)) (x : ℕ → ℝ) (hx : x 0=0) :
    gridIntegral m hm T grid n f x=HigherHeatSchwartzCalculus.spectralIntegral m T grid n f x := by
  rw [grid_representation m hm T hT grid n h0 hn f x hx]
  exact HigherHeatSchwartzCalculus.terminal_representation m T grid n hg h0 hn f x hx

end OperatorDerivativeRewrite.Foundation.HigherHeatBackwardSchwartz
