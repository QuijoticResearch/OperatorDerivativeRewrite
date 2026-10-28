import Foundation.SU2StapleKernel
import Foundation.SU2TiltEnergyResponse

/-!
# A genuine one-word SU(2) boundary-changing Markov transfer

Use the already verified finite-staple conditional law with one boundary word
as a transition from the current SU(2) state to a newly sampled SU(2) state.
This is a concrete probability kernel on a common state space, so its powers
are defined. It is not the 2-by-2 lattice block transfer, a gauge-quotient
construction, or a continuum Yang--Mills result. Its zero-coupling section
provides an exact strong-coupling anchor for testing correlation mechanisms.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.SU2OneWordTransfer
open QuaternionSU2Representation
open SU2TraceHessianModel

def word (A : SU2) : Unit → SU2 := fun _ => A

theorem word_measurable : Measurable word :=
  measurable_pi_iff.mpr (fun _ => measurable_id)

variable (ν : Measure SU2) [IsProbabilityMeasure ν]

def transition (β : ℝ) : Kernel SU2 SU2 :=
  (SU2StapleKernel.kernel ν (Finset.univ : Finset Unit) β).comap word word_measurable

theorem transition_markov (β : ℝ) : IsMarkovKernel (transition ν β) := by
  let _ := SU2StapleKernel.kernel_markov ν (Finset.univ : Finset Unit) β
  exact inferInstanceAs (IsMarkovKernel
    ((SU2StapleKernel.kernel ν (Finset.univ : Finset Unit) β).comap word word_measurable))

variable [ν.IsHaarMeasure]

theorem transition_section (β : ℝ) (A : SU2) :
    transition ν β A =
      SU2StapleTiltLaw.stapleLaw ν (Finset.univ : Finset Unit) (word A) β := by
  exact SU2StapleKernel.kernel_eq_stapleLaw ν (Finset.univ : Finset Unit) β (word A)

theorem identity_concentration (β : ℝ) :
    SU2StapleTiltLaw.concentration (Finset.univ : Finset Unit) (word (1 : SU2)) β = β := by
  change SU2StapleTiltLaw.concentration (Finset.univ : Finset Unit)
    (fun _ : Unit => (1 : SU2)) β = β
  simpa using SU2StapleExtremes.identity_concentration (Finset.univ : Finset Unit) β

theorem identity_exponent (β : ℝ) (B : SU2) :
    SU2StapleKernel.exponent (Finset.univ : Finset Unit) β (word (1 : SU2)) B =
      β * halfTrace B := by
  simp [SU2StapleKernel.exponent, SU2StaplePolar.staple, word, halfTrace]
  ring

theorem transition_identity_law (β : ℝ) :
    transition ν β (1 : SU2) =
      BoundedExponentialTiltResponse.tiltedMeasure ν halfTrace β := by
  rw [transition_section, SU2StapleTiltLaw.stapleLaw_density,
    identity_concentration]
  unfold BoundedExponentialTiltResponse.tiltedMeasure
  congr 1
  funext B
  rw [← SU2StapleKernel.exponent, identity_exponent]
  simp [BoundedExponentialTiltResponse.density, div_eq_mul_inv]

theorem identity_mean_hasDerivAt_zero :
    HasDerivAt (fun β : ℝ => ∫ B, halfTrace B ∂(transition ν β (1 : SU2)))
      (1/4) 0 := by
  have hEq (β : ℝ) :
      (∫ B, halfTrace B ∂(transition ν β (1 : SU2))) =
        BoundedExponentialTiltResponse.expectation ν halfTrace halfTrace β := by
    rw [transition_identity_law]
    exact BoundedExponentialTiltResponse.tilted_integral ν halfTrace halfTrace
      halfTrace_measurable halfTrace_bound β
  have hd := BoundedExponentialTiltResponse.expectation_hasDerivAt_zero ν
    halfTrace halfTrace halfTrace_measurable halfTrace_measurable halfTrace_bound
    1 (by norm_num) halfTrace_bound
  obtain ⟨h1, h2, _, _, _⟩ := SU2TiltEnergyResponse.moment_values ν
  have hmul : (∫ B, halfTrace B * halfTrace B ∂ν) = (1/4 : ℝ) := by
    convert h2 using 1
    apply integral_congr_ae
    filter_upwards with B
    ring
  rw [hmul, h1] at hd
  norm_num at hd
  simpa only [hEq] using hd

theorem transition_zero (A : SU2) : transition ν 0 A = ν := by
  rw [transition_section]
  unfold SU2StapleTiltLaw.stapleLaw SU2StapleTiltLaw.concentration
  simp only [zero_mul]
  exact SU2StapleExtremes.zero_tilt ν _

theorem positive_identity_mean_near_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ β, 0 < β ∧ β < ε ∧
      0 < ∫ B, halfTrace B ∂(transition ν β (1 : SU2)) := by
  have hz : (∫ B, halfTrace B ∂(transition ν 0 (1 : SU2))) = 0 := by
    rw [transition_zero]
    exact (SU2TiltEnergyResponse.moment_values ν).1
  obtain ⟨β, hβ, hβε, hinc⟩ :=
    BoundedExponentialTiltResponse.positive_derivative_arbitrarily_small_increase
      (fun β : ℝ => ∫ B, halfTrace B ∂(transition ν β (1 : SU2)))
      (1/4) (identity_mean_hasDerivAt_zero ν) (by norm_num) ε hε
  rw [hz] at hinc
  exact ⟨β, hβ, hβε, hinc⟩

theorem transition_zero_kernel : transition ν 0 = Kernel.const SU2 ν := by
  ext A : 1
  exact transition_zero ν A

theorem transition_zero_law (μ : Measure SU2) [IsProbabilityMeasure μ] :
    transition ν 0 ∘ₘ μ = ν := by
  rw [transition_zero_kernel, Measure.const_comp, measure_univ, one_smul]

theorem haar_zero_transfer_changes_identity :
    transition law 0 (1 : SU2) ≠ Measure.dirac (1 : SU2) := by
  let t : Set SU2 := {A | ((A : SU2TraceHessianModel.M2) 0 0).re < 0}
  have hc : Continuous (fun A : SU2 => ((A : SU2TraceHessianModel.M2) 0 0).re) := by
    have h : Continuous (fun A : SU2 => (A : SU2TraceHessianModel.M2)) :=
      continuous_subtype_val
    exact Complex.continuous_re.comp ((continuous_apply 0).comp ((continuous_apply 0).comp h))
  have ht : IsOpen t := isOpen_lt hc continuous_const
  have hm : SU2StapleExtremes.minusOne ∈ t := by
    norm_num [t, SU2StapleExtremes.minusOne, QuaternionSU2Representation.hom,
      QuaternionSU2Representation.repr]
  have hpos : 0 < law t := IsOpen.measure_pos law ht ⟨SU2StapleExtremes.minusOne, hm⟩
  have hnot : (1 : SU2) ∉ t := by
    norm_num [t, Matrix.one_apply]
  rw [transition_zero]
  intro he
  rw [he] at hpos
  simp [hnot] at hpos

end OperatorDerivativeRewrite.Foundation.SU2OneWordTransfer
