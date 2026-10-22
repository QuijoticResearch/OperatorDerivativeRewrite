import Foundation.IBMClockObservationGraph
import Foundation.GaussianDirectionalRecovery

/-! Converse transport of the ORIGINAL full Gaussian derivative along an
actual normalized clock observation. The pullback is an isometry into a proper
subspace; its bounded adjoint, not a fictitious inverse, recovers derivatives. -/
noncomputable section
open MeasureTheory Filter Polynomial
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockObservationConverse
open InfiniteGaussian IBMClockObservationGraph GaussianChaosLowering
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem polynomial_ae (h : CoefficientSpace) (hh : ‖h‖ = 1) (p : ℝ[X]) :
    pullback h hh (GaussianCore.polynomialL2 p) =ᵐ[gaussianProduct]
      fun ω => p.eval (firstChaosEmbedding h ω) := by
  have hp := (observation_measurePreserving h hh).quasiMeasurePreserving.ae_eq_comp
    (GaussianCore.polynomialL2_coeFn p)
  exact (pullback_ae h hh _).trans hp

def polynomialCore (h : CoefficientSpace) (hh : ‖h‖ = 1) (p : ℝ[X]) :
    polynomialCylindricalDomain :=
  ⟨pullback h hh (GaussianCore.polynomialL2 p), by
    rw [pullback_polynomial]
    exact isonormalCylinderL2_mem_core _ _⟩

theorem polynomialCore_derivative (h : CoefficientSpace) (hh : ‖h‖ = 1) (p : ℝ[X]) :
    polynomialDerivative (polynomialCore h hh p) =
      scalarTensor h (pullback h hh (GaussianCore.polynomialL2 p.derivative)) := by
  exact closedCylindricalDerivative.mem_graph_snd_inj
    (closedCylindricalDerivative_core_graph (polynomialCore h hh p))
    (pullback_polynomial_graph h hh p) rfl

theorem rankDivergence_eq (h : CoefficientSpace) (hh : ‖h‖ = 1) (p : ℝ[X]) :
    rankDivergence (polynomialCore h hh p) h =
      pullback h hh (GaussianCore.polynomialL2 (GaussianCore.divergencePolynomial p)) := by
  apply Lp.ext
  filter_upwards [rankDivergence_coeFn (polynomialCore h hh p) h,
    scalarTensor_coeFn h (pullback h hh (GaussianCore.polynomialL2 p.derivative)),
    polynomial_ae h hh p, polynomial_ae h hh p.derivative,
    polynomial_ae h hh (GaussianCore.divergencePolynomial p)] with ω hr ht hp hd hv
  rw [hr, polynomialCore_derivative, ht, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hh, one_pow, mul_one]
  change (pullback h hh (GaussianCore.polynomialL2 p)) ω * firstChaosEmbedding h ω -
    (pullback h hh (GaussianCore.polynomialL2 p.derivative)) ω = _
  rw [hp, hd, hv]
  simp only [GaussianCore.divergencePolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_X]
  ring

theorem pullback_divergence_graph (h : CoefficientSpace) (hh : ‖h‖ = 1) (p : ℝ[X]) :
    (scalarTensor h (pullback h hh (GaussianCore.polynomialL2 p)),
      pullback h hh (GaussianCore.polynomialL2 (GaussianCore.divergencePolynomial p))) ∈
        hilbertDivergence.graph := by
  have hg := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (cylindricalDivergence_rank_graph (polynomialCore h hh p) h)
  change (scalarTensor h (pullback h hh (GaussianCore.polynomialL2 p)),
    rankDivergence (polynomialCore h hh p) h) ∈ _ at hg
  rwa [rankDivergence_eq] at hg

def recover (h : CoefficientSpace) (hh : ‖h‖ = 1) :
    GaussianVectorL2 →L[ℝ] GaussianCore.GaussianL2 :=
  (pullback h hh).toContinuousLinearMap.adjoint.comp (component h)

theorem recover_pairing (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (q : GaussianCore.GaussianL2) (U : GaussianVectorL2) :
    inner ℝ q (recover h hh U) = inner ℝ (scalarTensor h (pullback h hh q)) U := by
  change inner ℝ q ((pullback h hh).toContinuousLinearMap.adjoint (component h U)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (scalarTensor_inner h (pullback h hh q) U).symm

theorem recover_norm_le (h : CoefficientSpace) (hh : ‖h‖ = 1) (U : GaussianVectorL2) :
    ‖recover h hh U‖ ≤ ‖U‖ := by
  have hJ : ‖(pullback h hh).toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (pullback h hh).norm_toContinuousLinearMap_le
  change ‖(pullback h hh).toContinuousLinearMap.adjoint (component h U)‖ ≤ _
  calc
    _ ≤ ‖(pullback h hh).toContinuousLinearMap.adjoint‖ * ‖component h U‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖component h U‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
    _ ≤ ‖U‖ := by
      simpa only [one_mul, hh] using GaussianDirectionalRecovery.component_norm_le h U

theorem recover_tensor (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (g : GaussianCore.GaussianL2) :
    recover h hh (scalarTensor h (pullback h hh g)) = g := by
  apply ext_inner_left ℝ
  intro q
  rw [recover_pairing, GaussianTimeFieldNorm.scalarTensor_pair_inner,
    real_inner_self_eq_norm_sq, hh, one_pow, mul_one, (pullback h hh).inner_map_map]

theorem converse_graph (h : CoefficientSpace) (hh : ‖h‖ = 1)
    {f : GaussianCore.GaussianL2} {U : GaussianVectorL2}
    (hf : (pullback h hh f, U) ∈ closedCylindricalDerivative.graph) :
    (f, recover h hh U) ∈ GaussianCore.closedDerivative.graph := by
  rw [GaussianCore.closedDerivative_eq_divergence_adjoint,
    LinearPMap.adjoint_graph_eq_graph_adjoint GaussianCore.polynomialDivergence_dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro q r hqr
  rw [GaussianCore.polynomialDivergence_graph] at hqr
  obtain ⟨p, hp⟩ := hqr
  have hq : GaussianCore.polynomialL2 p = q := congrArg Prod.fst hp
  have hr : GaussianCore.polynomialL2 (GaussianCore.divergencePolynomial p) = r :=
    congrArg Prod.snd hp
  change inner ℝ r f - inner ℝ q (recover h hh U) = 0
  rw [← hq, ← hr]
  apply sub_eq_zero.mpr
  have hi := GaussianNumberSectors.graph_duality hf (pullback_divergence_graph h hh p)
  calc
    _ = inner ℝ f (GaussianCore.polynomialL2 (GaussianCore.divergencePolynomial p)) :=
      real_inner_comm _ _
    _ = inner ℝ (pullback h hh f)
        (pullback h hh (GaussianCore.polynomialL2 (GaussianCore.divergencePolynomial p))) :=
      ((pullback h hh).inner_map_map _ _).symm
    _ = inner ℝ U (scalarTensor h (pullback h hh (GaussianCore.polynomialL2 p))) := hi.symm
    _ = inner ℝ (scalarTensor h (pullback h hh (GaussianCore.polynomialL2 p))) U :=
      real_inner_comm _ _
    _ = _ := (recover_pairing h hh _ U).symm

theorem original_graph_iff (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (f : GaussianCore.GaussianL2) (U : GaussianVectorL2) :
    (pullback h hh f, U) ∈ closedCylindricalDerivative.graph ↔
      ∃ g : GaussianCore.GaussianL2, (f, g) ∈ GaussianCore.closedDerivative.graph ∧
        U = scalarTensor h (pullback h hh g) := by
  constructor
  · intro hf
    have hg := converse_graph h hh hf
    exact ⟨recover h hh U, hg, closedCylindricalDerivative.mem_graph_snd_inj
      hf (pullback_closed_graph h hh hg) rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact pullback_closed_graph h hh hg

theorem original_domain_iff (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (f : GaussianCore.GaussianL2) :
    pullback h hh f ∈ closedCylindricalDerivative.domain ↔ f ∈ GaussianCore.closedDerivative.domain := by
  rw [LinearPMap.mem_domain_iff, LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨recover h hh U, converse_graph h hh hU⟩
  · rintro ⟨g, hg⟩
    exact ⟨_, pullback_closed_graph h hh hg⟩

/-- On the actual graph, the bounded recovery loses no derivative energy. -/
theorem graph_energy (h : CoefficientSpace) (hh : ‖h‖ = 1)
    {f : GaussianCore.GaussianL2} {U : GaussianVectorL2}
    (hf : (pullback h hh f, U) ∈ closedCylindricalDerivative.graph) :
    ‖recover h hh U‖ = ‖U‖ := by
  have hg := converse_graph h hh hf
  have he := closedCylindricalDerivative.mem_graph_snd_inj
    hf (pullback_closed_graph h hh hg) rfl
  conv_rhs => rw [he, IBMClockAverageCandidate.scalarTensor_norm,
    (pullback h hh).norm_map, hh, mul_one]

end OperatorDerivativeRewrite.Foundation.IBMClockObservationConverse
