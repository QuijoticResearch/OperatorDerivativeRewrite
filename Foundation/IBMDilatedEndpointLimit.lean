import Foundation.IBMCompactKernelReflectedIto

/-! Actual full clock/source L2 endpoints for every positive width, with one
common unmollified IBM limit for every admissible compact profile. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMDilatedEndpointLimit
open InfiniteGaussian IBMConstructedSources IBMCorrectionStein
open IBMCompactKernelSchwartz IBMCompactKernelReflectedIto IBMDilatedMollifier
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

theorem endpoint_sequence_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => endpointClass g a (dilate_compact hc (hε n).ne')
      (dilate_contDiff hρ (ε n)) T) atTop
      (𝓝 (IBMSchwartzFullReflectedIto.endpointLimitClass g a T)) := by
  let hd n := dilate_compact hc (hε n).ne'
  let hs n := dilate_contDiff hρ (ε n)
  have hterminal : Tendsto (fun n => (endpoint_memLp g a (hd n) (hs n) T).toLp _)
      atTop (𝓝 (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T)) := by
    let C := SchwartzMap.seminorm ℝ 0 0 (jet g 0)
    have hC : 0 ≤ C := by positivity
    have hb : ∀ᵐ ω ∂gaussianProduct, ‖(C • gaussianOne : GaussianL2) ω‖ = C := by
      filter_upwards [Lp.coeFn_smul C gaussianOne,gaussianOne_coeFn] with ω hs ho
      simp only [hs,Pi.smul_apply,smul_eq_mul,ho,mul_one,Real.norm_eq_abs,abs_of_nonneg hC]
    apply BochnerL2Approximation.tendsto_of_dominated _ _ (C • gaussianOne)
    · intro n
      filter_upwards [(endpoint_memLp g a (hd n) (hs n) T).coeFn_toLp,hb] with ω he hω
      rw [he,hω]
      exact IBMSchwartzSourceDerivative.observable_bound g a 0 _
    · filter_upwards [IBMSchwartzPhysicalPrimitiveClock.endpointLimit_ae g a T,hb] with ω he hω
      rw [he,hω]
      exact IBMSchwartzSourceDerivative.observable_bound g a 0 _
    · filter_upwards [ae_all_iff.mpr (fun n =>
        (endpoint_memLp g a (hd n) (hs n) T).coeFn_toLp),
        IBMSchwartzPhysicalPrimitiveClock.endpointLimit_ae g a T] with ω hn hl
      simp only [hn,hl]
      exact spatial_tendsto hε hlim hρ.continuous hc hpos hmass g a _
  exact hterminal.sub ((Lp.constL 2 gaussianProduct ℝ).continuous.tendsto _ |>.comp
    (spatial_tendsto hε hlim hρ.continuous hc hpos hmass g a 0))

/-- The full positive-width filter is nontrivial, witnessed by actual positive widths. -/
theorem positive_width_filter_neBot :
    NeBot (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0)) := by
  let u (n : ℕ) : {x : ℝ // 0 < x} := ⟨1 / ((n : ℝ)+1),by positivity⟩
  have hu : Tendsto u atTop (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0)) :=
    tendsto_comap_iff.mpr IBMMollifierProfileAudit.width_tendsto_zero
  exact hu.neBot

/-- Genuine all-positive-epsilon convergence, in full joint L2. Sequential
testing is applied to EVERY width sequence, not just epsilon_n=1/(n+1). -/
theorem endpoint_continuum_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) (T : ℝ≥0) :
    Tendsto (fun ε : {x : ℝ // 0 < x} => endpointClass g a (dilate_compact hc ε.property.ne')
      (dilate_contDiff hρ ε.val) T)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0))
      (𝓝 (IBMSchwartzFullReflectedIto.endpointLimitClass g a T)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro u hu
  exact endpoint_sequence_tendsto g a hc hρ hpos hmass (fun n => (u n).property)
    (tendsto_comap_iff.mp hu) T

end OperatorDerivativeRewrite.Foundation.IBMDilatedEndpointLimit
