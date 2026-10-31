import Foundation.PeriodicHighActionSchur
import Foundation.PeriodicWindingRate
import Foundation.FiniteMeasureL2Integration
/-! Actual low Schur obstruction with the native variance AFTER harmonic lifting.
The source trials are global center-sensitive winding modes, not local glueballs. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicSchurWindingObstruction
open PeriodicSlabGround PeriodicSlabL2 PeriodicHighActionL2 PeriodicHighActionSchur
open SelfAdjointContractionIteration
variable {β : ℝ} (g : GroundData β)
private instance stationary_prob : IsProbabilityMeasure g.stationary := g.stationary_probability
attribute [local irreducible] represented completed operator cross schur harmonic compression

private theorem norm_square (F : StateL2 g) : ‖F‖^2=∫ U,(F U)^2 ∂g.stationary := by
  simpa only [Real.norm_eq_abs,sq_abs] using BochnerL2Dominated.norm_sq_integral F

theorem native_variance (F : StateL2 g) :
    variance F g.stationary=‖F‖^2-(∫ U,F U ∂g.stationary)^2 := by
  have h := variance_eq_sub (Lp.memLp F)
  change variance F g.stationary=(∫ U,(F U)^2 ∂g.stationary)-(∫ U,F U ∂g.stationary)^2 at h
  rw [← norm_square] at h
  exact h

private theorem mean_square (F : StateL2 g) :
    (∫ U,F U ∂g.stationary)^2 ≤ ‖F‖^2 := by
  have h := FiniteMeasureL2Integration.square_integral_le F (Lp.memLp F)
  simpa only [probReal_univ,one_mul,← norm_square] using h

private theorem mean_sub (F G : StateL2 g) :
    (∫ U,(F-G) U ∂g.stationary)=(∫ U,F U ∂g.stationary)-(∫ U,G U ∂g.stationary) := by
  rw [integral_congr_ae (Lp.coeFn_sub F G)]
  exact integral_sub ((Lp.memLp F).integrable (by norm_num)) ((Lp.memLp G).integrable (by norm_num))

private theorem stable_variance (N F : StateL2 g) (hN : ‖N‖=1)
    (hmean : (∫ U,N U ∂g.stationary)=0) (hclose : ‖N-F‖ ≤ (1/4 : ℝ)) :
    (1/2 : ℝ) ≤ variance F g.stationary := by
  have hm := mean_square g (F-N)
  rw [mean_sub,hmean,sub_zero] at hm
  have hd : ‖F-N‖ ≤ (1/4 : ℝ) := by simpa only [norm_sub_rev] using hclose
  have ht : 1 ≤ ‖F‖+‖F-N‖ := by
    calc
      _ = ‖N‖ := hN.symm
      _ = ‖F-(F-N)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  rw [native_variance]
  nlinarith [norm_nonneg F,norm_nonneg (F-N)]

private theorem residual_square (N : StateL2 g) :
    ‖N-operator g N‖^2 ≤ 2*dissipation (operator g) N := by
  have h := PeriodicTransferVariation.operator_residual g N
  have hs := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h
  rw [PeriodicWindingRate.native_dirichlet]
  have he := congrArg (fun t : ℝ => t^2) (norm_sub_rev N (operator g N))
  nlinarith only [hs,he]

/-- Native harmonic approximation and energy minimization for the SAME low vector. -/
theorem harmonic_approximation (hb : 16777216 ≤ β) (R : High g →L[ℝ] High g)
    (hL : (1-compression g threshold)*R=1) (hR : R*(1-compression g threshold)=1)
    (hNorm : ‖R‖ ≤ 2) (N : StateL2 g) :
    ∃ x : low g,‖N-harmonic g R x‖ ≤ 2*‖N-operator g N‖ ∧
      0 ≤ inner ℝ (schur g R x) x ∧ inner ℝ (schur g R x) x ≤ dissipation (operator g) N := by
  obtain ⟨x,y,he⟩ := native_decomposition g N
  have hc := residual_control g R hR hNorm x y
  have hrem := variational_remainder g hb R hL x y
  have hd : (x : StateL2 g)+(y : StateL2 g)-harmonic g R x=
      ((y-R (cross g x) : High g) : StateL2 g) := by
    simp only [harmonic,add_apply,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply]
    change (x : StateL2 g)+(y : StateL2 g)-((x : StateL2 g)+(R (cross g x) : StateL2 g))=
      (y : StateL2 g)-(R (cross g x) : StateL2 g)
    abel
  refine ⟨x,?_,schur_nonnegative g R hL x,?_⟩
  · rw [← he,hd]
    exact hc
  · rw [he] at hrem
    nlinarith only [hrem,sq_nonneg ‖y-R (cross g x)‖]

/-- A native centered unit trial of sufficiently small energy yields positive
ACTUAL variance after harmonic lifting, with no centering assumption on x. -/
theorem variance_trial (hb : 16777216 ≤ β) (R : High g →L[ℝ] High g)
    (hL : (1-compression g threshold)*R=1) (hR : R*(1-compression g threshold)=1)
    (hNorm : ‖R‖ ≤ 2) (N : StateL2 g) (hN : ‖N‖=1)
    (hmean : (∫ U,N U ∂g.stationary)=0) (ε : ℝ)
    (hE : dissipation (operator g) N ≤ ε) (hsmall : ε ≤ 1/128) :
    ∃ x : low g,(1/2 : ℝ) ≤ variance (harmonic g R x) g.stationary ∧
      0 ≤ inner ℝ (schur g R x) x ∧ inner ℝ (schur g R x) x ≤ ε := by
  obtain ⟨x,hclose,hpos,hbound⟩ := harmonic_approximation g hb R hL hR hNorm N
  have hr := residual_square g N
  have hs := sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*‖N-operator g N‖) |>.mpr hclose
  have hd : ‖N-harmonic g R x‖ ≤ (1/4 : ℝ) := by
    nlinarith [norm_nonneg (N-harmonic g R x)]
  exact ⟨x,stable_variance g N _ hN hmean hd,hpos,hbound.trans hE⟩

/-- The existing actual winding quasimodes give small Schur energy with a
nonvanishing variance of the SAME native harmonic lift, for every actual inverse. -/
theorem eventual_winding_trial : ∀ᶠ β : ℝ in atTop,∀ g : GroundData β,
    ∀ R : High g →L[ℝ] High g,
      (1-compression g threshold)*R=1 → R*(1-compression g threshold)=1 → ‖R‖ ≤ 2 →
      ∃ x : low g,(1/2 : ℝ) ≤ variance (harmonic g R x) g.stationary ∧
        0 ≤ inner ℝ (schur g R x) x ∧
        inner ℝ (schur g R x) x ≤ 1536*PeriodicEnergyRate.rate β ∧
        inner ℝ (schur g R x) x ≤
          (3072*PeriodicEnergyRate.rate β)*variance (harmonic g R x) g.stationary := by
  have hsmall := PeriodicEnergyRate.rate_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/196608))
  filter_upwards [PeriodicWindingRate.eventual_normalized_dirichlet,
    eventually_ge_atTop (16777216 : ℝ),hsmall] with β hTrial hb hs
  intro g R hL hR hNorm
  obtain ⟨N,_,hN,hmean,hE⟩ := hTrial g
  have hb1 : 1 ≤ β := by linarith
  have he := PeriodicEnergyRate.logarithmic_energy_bound g hb1
  have hn := PeriodicEnergyRate.rate_nonneg β hb1
  have hbound : dissipation (operator g) N ≤ 1536*PeriodicEnergyRate.rate β :=
    hE.trans (mul_le_mul_of_nonneg_left he (by norm_num))
  obtain ⟨x,hv,hpos,hS⟩ := variance_trial g hb R hL hR hNorm N hN hmean
    (1536*PeriodicEnergyRate.rate β) hbound (by linarith)
  refine ⟨x,hv,hpos,hS,?_⟩
  have hmul := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 3072*PeriodicEnergyRate.rate β)
  linarith only [hS,hmul]

/-- No coupling-uniform positive Schur gap relative to the genuine pulled-back
native variance on the FULL low domain. This concerns global winding modes. -/
theorem no_uniform_variance_gap (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop,∀ g : GroundData β,∀ R : High g →L[ℝ] High g,
      (1-compression g threshold)*R=1 → R*(1-compression g threshold)=1 → ‖R‖ ≤ 2 →
      ¬ ∀ x : low g,δ*variance (harmonic g R x) g.stationary ≤ inner ℝ (schur g R x) x := by
  have hsmall := PeriodicEnergyRate.rate_tendsto_zero.eventually
    (gt_mem_nhds (by positivity : (0:ℝ)<δ/3072))
  filter_upwards [eventual_winding_trial,hsmall] with β hTrial hs
  intro g R hL hR hNorm hc
  obtain ⟨x,hv,_,hS,_⟩ := hTrial g R hL hR hNorm
  have hδv := mul_le_mul_of_nonneg_left hv hδ.le
  have hcontra := hc x
  nlinarith only [hδv,hcontra,hS,hs]

end OperatorDerivativeRewrite.Foundation.PeriodicSchurWindingObstruction
