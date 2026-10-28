import Foundation.SU2StrongCouplingCovariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Foundation.HilbertRepresentation
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse
open OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium
open OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel
open OperatorDerivativeRewrite.Foundation.SU2StrongCouplingCovariance
namespace OperatorDerivativeRewrite.Foundation.SU2VariationalGap

def secondMoment (r : ℝ) : ℝ := ∫ p, F p ^ 2 ∂coupledLaw r
def energy (r : ℝ) : ℝ := secondMoment r - lagCov r 1
def quotient (r : ℝ) : ℝ := energy r / secondMoment r
def transfer (r : ℝ) (f : SU2 → ℝ) (C : SU2) : ℝ := ∫ D, f D ∂loopKernel r C

private theorem bounded_integrable (r : ℝ) (f : SU2 × SU2 → ℝ)
    (hf : Measurable f) (hb : ∀ p, |f p| ≤ 1) : Integrable f (coupledLaw r) := by
  letI := coupledLaw_probability r
  apply Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable
  filter_upwards with p
  simpa only [Real.norm_eq_abs] using hb p
private theorem Fsq_bound (p : SU2 × SU2) : |F p ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := abs_le.mp (halfTrace_bound p.1)
  change halfTrace p.1 ^ 2 ≤ 1
  nlinarith
private theorem Fsq_integrable (r : ℝ) : Integrable (fun p => F p ^ 2) (coupledLaw r) :=
  bounded_integrable r _ ((halfTrace_measurable.comp measurable_fst).pow_const 2) Fsq_bound
private theorem Gsq_integrable (r : ℝ) : Integrable (fun p => G p ^ 2) (coupledLaw r) :=
  bounded_integrable r _ ((halfTrace_measurable.comp measurable_snd).pow_const 2)
    (fun p => Fsq_bound p.swap)
private theorem X_integrable (r : ℝ) : Integrable X (coupledLaw r) := by
  apply bounded_integrable r _ ((halfTrace_measurable.comp measurable_fst).mul
    (halfTrace_measurable.comp measurable_snd))
  intro p
  exact (abs_mul (F p) (G p)).trans_le (by
    simpa [F, G] using mul_le_mul (halfTrace_bound p.1) (halfTrace_bound p.2)
      (abs_nonneg _) (by norm_num))

theorem secondMoment_le_one (r : ℝ) : secondMoment r ≤ 1 := by
  letI := coupledLaw_probability r
  have h := integral_mono (Fsq_integrable r) (integrable_const (1 : ℝ))
    (fun p => (le_abs_self _).trans (Fsq_bound p))
  simpa [secondMoment] using h

private theorem secondMoment_swap (r : ℝ) :
    (∫ p, G p ^ 2 ∂coupledLaw r) = secondMoment r := by
  have he := integral_map (μ := coupledLaw r) measurable_swap.aemeasurable
    (((halfTrace_measurable.comp measurable_fst).pow_const 2).aestronglyMeasurable)
  rw [coupledLaw_exchangeable] at he
  exact he.symm

theorem energy_eq_square (r : ℝ) :
    energy r = (∫ p, (F p - G p)^2 ∂coupledLaw r) / 2 := by
  have he : (fun p : SU2 × SU2 => (F p - G p)^2) =
      (fun p => F p^2 + G p^2 - 2 * X p) := by
    funext p
    simp only [X]
    ring
  rw [he]
  have hsub := integral_sub ((Fsq_integrable r).add (Gsq_integrable r)) ((X_integrable r).const_mul 2)
  change (∫ p, F p^2 + G p^2 - 2*X p ∂coupledLaw r) = _ at hsub
  rw [hsub]
  change energy r = ((∫ p, F p^2 + G p^2 ∂coupledLaw r) -
    (∫ p, 2*X p ∂coupledLaw r)) / 2
  rw [integral_add (Fsq_integrable r) (Gsq_integrable r), integral_const_mul, secondMoment_swap]
  rw [energy, lagCov_one, corr_eq_interaction_mean]
  change secondMoment r - _ = (secondMoment r + secondMoment r - _) / 2
  ring

theorem energy_nonneg (r : ℝ) : 0 ≤ energy r := by
  rw [energy_eq_square]
  exact div_nonneg (integral_nonneg (fun p => sq_nonneg _)) (by norm_num)

theorem energy_tendsto_zero : Tendsto energy atTop (𝓝 0) := by
  have hu : Tendsto (fun r : ℝ => 1 - lagCov r 1) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub stationary_lag_one_cov_tendsto_one
  apply squeeze_zero energy_nonneg ?_ hu
  intro r
  dsimp [energy]
  linarith [secondMoment_le_one r]

theorem secondMoment_tendsto_one : Tendsto secondMoment atTop (𝓝 1) := by
  have he : secondMoment = fun r => energy r + lagCov r 1 := by
    funext r
    simp [energy]
  rw [he]
  simpa using energy_tendsto_zero.add stationary_lag_one_cov_tendsto_one

theorem quotient_tendsto_zero : Tendsto quotient atTop (𝓝 0) := by
  change Tendsto (fun r => energy r / secondMoment r) atTop (𝓝 0)
  have h := energy_tendsto_zero.div secondMoment_tendsto_one (by norm_num : (1:ℝ) ≠ 0)
  change Tendsto (fun r => energy r / secondMoment r) atTop (𝓝 ((0:ℝ)/1)) at h
  simpa using h

theorem transfer_pairing (r : ℝ) :
    (∫ C, halfTrace C * transfer r halfTrace C ∂equilibriumLaw r) = lagCov r 1 := by
  letI := equilibriumLaw_probability r
  letI := loopKernel_markov r
  have hi : Integrable X (equilibriumLaw r ⊗ₘ loopKernel r) := by
    rw [equilibrium_edge]
    exact X_integrable r
  have he := Measure.integral_compProd hi
  rw [equilibrium_edge] at he
  have hh : (∫ C, ∫ D, X (C,D) ∂loopKernel r C ∂equilibriumLaw r) =
      (∫ C, halfTrace C * transfer r halfTrace C ∂equilibriumLaw r) := by
    apply integral_congr_ae
    filter_upwards with C
    simp only [X, F, G, integral_const_mul, transfer]
  rw [hh] at he
  rw [lagCov_one, corr_eq_interaction_mean]
  exact he.symm

theorem stationary_secondMoment (r : ℝ) :
    (∫ C, halfTrace C ^ 2 ∂equilibriumLaw r) = secondMoment r := by
  rw [equilibriumLaw_eq_fst]
  change (∫ C, halfTrace C ^ 2 ∂(coupledLaw r).map Prod.fst) = _
  rw [integral_map measurable_fst.aemeasurable
    ((halfTrace_measurable.pow_const 2).aestronglyMeasurable)]
  rfl

theorem stationary_mean_zero (r : ℝ) : (∫ C, halfTrace C ∂equilibriumLaw r) = 0 := by
  rw [equilibriumLaw_eq_fst]
  change (∫ C, halfTrace C ∂(coupledLaw r).map Prod.fst) = _
  rw [integral_map measurable_fst.aemeasurable halfTrace_measurable.aestronglyMeasurable]
  exact stationary_F_mean_zero r

theorem halfTrace_memLp_two (r : ℝ) : MemLp halfTrace 2 (equilibriumLaw r) := by
  letI := equilibriumLaw_probability r
  apply MemLp.of_bound halfTrace_measurable.aestronglyMeasurable 1
  filter_upwards with C
  simpa only [Real.norm_eq_abs] using halfTrace_bound C

theorem no_uniform_variational_gap (γ : ℝ) (hγ : 0 < γ) :
    ∃ r : ℝ, 0 ≤ r ∧ 0 < (∫ C, halfTrace C ^ 2 ∂equilibriumLaw r) ∧
      (∫ C, halfTrace C ^ 2 ∂equilibriumLaw r) -
        (∫ C, halfTrace C * transfer r halfTrace C ∂equilibriumLaw r) <
          γ * (∫ C, halfTrace C ^ 2 ∂equilibriumLaw r) := by
  have hq := (tendsto_order.mp quotient_tendsto_zero).2 γ hγ
  have hv := (tendsto_order.mp secondMoment_tendsto_one).1 0 (by norm_num)
  obtain ⟨r, hr, hqr, hvr⟩ := ((eventually_ge_atTop (0:ℝ)).and (hq.and hv)).exists
  refine ⟨r, hr, ?_, ?_⟩
  · rw [stationary_secondMoment]; exact hvr
  · rw [stationary_secondMoment, transfer_pairing]
    change energy r < γ * secondMoment r
    exact (div_lt_iff₀ hvr).mp hqr

abbrev StateL2 (r : ℝ) := Lp ℝ 2 (equilibriumLaw r)
abbrev EdgeL2 (r : ℝ) := Lp ℝ 2 (coupledLaw r)

theorem left_preserving (r : ℝ) : MeasurePreserving Prod.fst (coupledLaw r) (equilibriumLaw r) :=
  ⟨measurable_fst, (equilibriumLaw_eq_fst r).symm⟩

theorem right_preserving (r : ℝ) : MeasurePreserving Prod.snd (coupledLaw r) (equilibriumLaw r) := by
  have h := SU2LagEventCorrelation.stationaryLagLaw_snd r 1
  rw [stationaryLagLaw_one] at h
  exact ⟨measurable_snd, h⟩

def leftEmbedding (r : ℝ) : StateL2 r →ₗᵢ[ℝ] EdgeL2 r :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (left_preserving r)

def rightEmbedding (r : ℝ) : StateL2 r →ₗᵢ[ℝ] EdgeL2 r :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.snd (right_preserving r)

def operator (r : ℝ) : StateL2 r →L[ℝ] StateL2 r :=
  (HilbertRepresentation.predictableAdjoint (leftEmbedding r)).comp
    (rightEmbedding r).toContinuousLinearMap

theorem operator_pairing (r : ℝ) (f g : StateL2 r) :
    inner ℝ (operator r f) g = ∫ p, g p.1 * f p.2 ∂coupledLaw r := by
  rw [show inner ℝ (operator r f) g =
      inner ℝ (rightEmbedding r f) (leftEmbedding r g) from
    HilbertRepresentation.predictableAdjoint_pairing (leftEmbedding r) (rightEmbedding r f) g]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving f (right_preserving r),
    Lp.coeFn_compMeasurePreserving g (left_preserving r)] with p hf hg
  change inner ℝ (rightEmbedding r f p) (leftEmbedding r g p) = _
  change rightEmbedding r f p = f p.2 at hf
  change leftEmbedding r g p = g p.1 at hg
  rw [hf, hg]
  rfl

theorem operator_contraction (r : ℝ) (f : StateL2 r) : ‖operator r f‖ ≤ ‖f‖ := by
  have h := HilbertRepresentation.representation_norm_decomposition
    (leftEmbedding r) (rightEmbedding r f)
  rw [(rightEmbedding r).norm_map] at h
  change ‖f‖^2 = ‖operator r f‖^2 + _ at h
  nlinarith [sq_nonneg (‖rightEmbedding r f -
    HilbertRepresentation.representationProjection (leftEmbedding r) (rightEmbedding r f)‖),
    norm_nonneg (operator r f), norm_nonneg f]

theorem operator_symmetric (r : ℝ) (f g : StateL2 r) :
    inner ℝ (operator r f) g = inner ℝ f (operator r g) := by
  rw [← real_inner_comm f (operator r g), operator_pairing, operator_pairing]
  have hm : Measurable (fun p : SU2 × SU2 => g p.1 * f p.2) :=
    ((Lp.stronglyMeasurable g).measurable.comp measurable_fst).mul
      ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)
  have he := integral_map (μ := coupledLaw r) measurable_swap.aemeasurable hm.aestronglyMeasurable
  rw [coupledLaw_exchangeable] at he
  simpa [mul_comm] using he

theorem operator_selfadjoint (r : ℝ) : (operator r).adjoint = operator r :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr (operator_symmetric r)).symm

theorem operator_kernel_pairing (r : ℝ) (f g : StateL2 r) :
    inner ℝ (operator r f) g =
      ∫ C, g C * transfer r f C ∂equilibriumLaw r := by
  letI := equilibriumLaw_probability r
  letI := loopKernel_markov r
  have hi : Integrable (fun p : SU2 × SU2 => g p.1 * f p.2) (coupledLaw r) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (rightEmbedding r f) (leftEmbedding r g)).congr
    filter_upwards [Lp.coeFn_compMeasurePreserving f (right_preserving r),
      Lp.coeFn_compMeasurePreserving g (left_preserving r)] with p hf hg
    change rightEmbedding r f p = f p.2 at hf
    change leftEmbedding r g p = g p.1 at hg
    change inner ℝ (rightEmbedding r f p) (leftEmbedding r g p) = _
    rw [hf, hg]
    rfl
  rw [← equilibrium_edge r] at hi
  rw [operator_pairing, ← equilibrium_edge r, Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards with C
  simp only [transfer, integral_const_mul]

def coordinate (r : ℝ) : StateL2 r := (halfTrace_memLp_two r).toLp halfTrace

theorem coordinate_mean (r : ℝ) : (∫ C, coordinate r C ∂equilibriumLaw r) = 0 := by
  unfold coordinate
  rw [integral_congr_ae (MemLp.coeFn_toLp (halfTrace_memLp_two r))]
  exact stationary_mean_zero r

theorem coordinate_square (r : ℝ) : inner ℝ (coordinate r) (coordinate r) = secondMoment r := by
  rw [L2.inner_def, ← stationary_secondMoment]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (halfTrace_memLp_two r)] with C hC
  change coordinate r C = halfTrace C at hC
  rw [hC]
  simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem coordinate_operator_pairing (r : ℝ) :
    inner ℝ (operator r (coordinate r)) (coordinate r) = lagCov r 1 := by
  rw [operator_pairing, lagCov_one, corr_eq_interaction_mean]
  apply integral_congr_ae
  have hl := (left_preserving r).quasiMeasurePreserving.ae_eq_comp
    (MemLp.coeFn_toLp (halfTrace_memLp_two r))
  have hr := (right_preserving r).quasiMeasurePreserving.ae_eq_comp
    (MemLp.coeFn_toLp (halfTrace_memLp_two r))
  filter_upwards [hl, hr] with p hp hq
  change coordinate r p.1 = halfTrace p.1 at hp
  change coordinate r p.2 = halfTrace p.2 at hq
  rw [hp, hq]
  rfl

theorem no_uniform_L2_gap (γ : ℝ) (hγ : 0 < γ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ f : StateL2 r,
      (∫ C, f C ∂equilibriumLaw r) = 0 ∧ 0 < inner ℝ f f ∧
        inner ℝ f f - inner ℝ (operator r f) f < γ * inner ℝ f f := by
  obtain ⟨r, hr, hv, hg⟩ := no_uniform_variational_gap γ hγ
  refine ⟨r, hr, coordinate r, coordinate_mean r, ?_, ?_⟩
  · rw [coordinate_square]
    simpa only [stationary_secondMoment] using hv
  · rw [coordinate_square, coordinate_operator_pairing]
    simpa only [stationary_secondMoment, transfer_pairing] using hg

end OperatorDerivativeRewrite.Foundation.SU2VariationalGap
