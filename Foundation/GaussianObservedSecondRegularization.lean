import Foundation.GaussianRegularizedSecondDerivative
import Foundation.IBMClockObservationGraph
import Foundation.GaussianPotentialPredictionRank

/-! One-coordinate second-derivative regularization uses ONE common Gaussian
number smoothing on the full sample space, independent of the observation. -/
noncomputable section
open MeasureTheory Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianObservedSecondRegularization
open InfiniteGaussian GaussianNumberSectors GaussianTimeSpaceHermite GaussianConditionalCompactness
open GaussianInverseNumberPotential
set_option backward.isDefEq.respectTransparency false

def commonSmoothing : GaussianL2 →L[ℝ] GaussianL2 := projection 0 + potentialOperator

theorem commonSmoothing_sector (n : ℕ) (f : sector n) :
    commonSmoothing f = GaussianRegularizedSecondDerivative.weight n • (f : GaussianL2) := by
  change projection 0 f + potentialOperator f = _
  rw [projection_of_sector f, GaussianPotentialPredictionRank.potential_sector n f]
  by_cases hn : n = 0
  · subst n; simp [GaussianRegularizedSecondDerivative.weight]
  · simp [hn, Ne.symm hn, GaussianRegularizedSecondDerivative.weight]

theorem commonSmoothing_hasSum (f : GaussianL2) :
    HasSum (fun n => GaussianRegularizedSecondDerivative.weight n • projection n f) (commonSmoothing f) := by
  have hs := (projection_hasSum f).map commonSmoothing.toAddMonoidHom commonSmoothing.continuous
  change HasSum (fun n => commonSmoothing (projection n f)) (commonSmoothing f) at hs
  have he (n : ℕ) : commonSmoothing (projection n f) =
      GaussianRegularizedSecondDerivative.weight n • projection n f :=
    commonSmoothing_sector n ⟨_, projection_mem n f⟩
  simpa only [he] using hs

/-- A common weaker norm must not identify a nonzero Gaussian vector with zero. -/
theorem commonSmoothing_eq_zero_iff (f : GaussianL2) : commonSmoothing f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have hh : inner ℝ (commonSmoothing f) f = 0 := by rw [hf, inner_zero_left]
    change inner ℝ (projection 0 f + potentialOperator f) f = 0 at hh
    rw [inner_add_left, projection_zero, real_inner_smul_left, potential_positive] at hh
    have hm : inner ℝ gaussianOne f = 0 := by nlinarith [sq_nonneg ‖GaussianDivergenceRecovery.recovery f‖]
    have hr : GaussianDivergenceRecovery.recovery f = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (GaussianDivergenceRecovery.recovery f)])
    have hg := GaussianDivergenceRecovery.recovery_graph f
    rw [hr, projection_zero, hm, zero_smul, sub_zero] at hg
    exact hilbertDivergence.graph_fst_eq_zero_snd hg rfl
  · rintro rfl
    exact map_zero _

theorem commonSmoothing_injective : Function.Injective commonSmoothing := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (commonSmoothing_eq_zero_iff (f - g)).mp
  rw [map_sub, hfg, sub_self]

theorem hermite_polynomial_bridge (n : ℕ) :
    (GaussianCore.hermitePolynomial n).toMvPolynomial () = polynomial 1 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [GaussianCore.hermitePolynomial_succ]
    simp only [GaussianCore.divergencePolynomial, map_sub, map_mul, Polynomial.toMvPolynomial_X,
      ← IBMClockObservationGraph.pderiv_univariate, ih]
    simp only [polynomial_succ, raise, one_smul]

theorem pullback_normalizedHermite (h : CoefficientSpace) (hh : ‖h‖ = 1) (n : ℕ) :
    IBMClockObservationGraph.pullback h hh (GaussianCore.normalizedHermite n) = normalizedWick h n := by
  change IBMClockObservationGraph.pullback h hh
    ((Real.sqrt (n.factorial : ℝ))⁻¹ • GaussianCore.polynomialL2 (GaussianCore.hermitePolynomial n)) = _
  rw [map_smul, IBMClockObservationGraph.pullback_polynomial, hermite_polynomial_bridge]
  change (Real.sqrt (n.factorial : ℝ))⁻¹ • isonormalCylinderL2 (fun _ : Unit => h) (polynomial 1 n) =
    (Real.sqrt (n.factorial : ℝ))⁻¹ • isonormalCylinderL2 (fun _ : Unit => h) (polynomial (‖h‖ ^ 2) n)
  rw [hh, one_pow]

theorem commonSmoothing_pullback_hermite (h : CoefficientSpace) (hh : ‖h‖ = 1) (n : ℕ) :
    commonSmoothing (IBMClockObservationGraph.pullback h hh (GaussianCore.normalizedHermite n)) =
      IBMClockObservationGraph.pullback h hh
        (GaussianRegularizedSecondDerivative.smoothing (GaussianCore.normalizedHermite n)) := by
  rw [pullback_normalizedHermite, GaussianRegularizedSecondDerivative.smoothing_hermite,
    map_smul, pullback_normalizedHermite]
  exact commonSmoothing_sector n ⟨_, (sector n).smul_mem _ (IBMCubicFirstChaos.wick_mem_sector h n)⟩

/-- Same common smoothing for EVERY actual unit Gaussian observation. -/
theorem commonSmoothing_pullback (h : CoefficientSpace) (hh : ‖h‖ = 1) (f : GaussianCore.GaussianL2) :
    commonSmoothing (IBMClockObservationGraph.pullback h hh f) =
      IBMClockObservationGraph.pullback h hh (GaussianRegularizedSecondDerivative.smoothing f) := by
  let J := (IBMClockObservationGraph.pullback h hh).toContinuousLinearMap
  let L := commonSmoothing.comp J - J.comp GaussianRegularizedSecondDerivative.smoothing
  have hs : Submodule.span ℝ (Set.range GaussianCore.normalizedHermite) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    change L (GaussianCore.normalizedHermite n) = 0
    exact sub_eq_zero.mpr (commonSmoothing_pullback_hermite h hh n)
  have hz : L f = 0 := GaussianCore.normalizedHermite_dense_span.induction
    (fun x hx => hs hx) (isClosed_eq L.continuous continuous_const) f
  exact sub_eq_zero.mp hz

def observedSecond (h : CoefficientSpace) (hh : ‖h‖ = 1) : GaussianCore.GaussianL2 →L[ℝ] GaussianL2 :=
  (IBMClockObservationGraph.pullback h hh).toContinuousLinearMap.comp
    GaussianRegularizedSecondDerivative.regularizedSecond

theorem observedSecond_norm_le (h : CoefficientSpace) (hh : ‖h‖ = 1) :
    ‖observedSecond h hh‖ ≤ Real.sqrt 6 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  change ‖IBMClockObservationGraph.pullback h hh
    (GaussianRegularizedSecondDerivative.regularizedSecond f)‖ ≤ _
  rw [(IBMClockObservationGraph.pullback h hh).norm_map]
  exact (GaussianRegularizedSecondDerivative.regularizedSecond.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right GaussianRegularizedSecondDerivative.regularizedSecond_norm_le (norm_nonneg f))

/-- Actual second closed-derivative graphs agree with the COMMON full-space
regularization, not an observation-dependent replacement of the target norm. -/
theorem observedSecond_actual_graph (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (f g q : GaussianCore.GaussianL2) (hf : (f, g) ∈ GaussianCore.closedDerivative.graph)
    (hg : (g, q) ∈ GaussianCore.closedDerivative.graph) :
    observedSecond h hh f = commonSmoothing (IBMClockObservationGraph.pullback h hh q) := by
  change IBMClockObservationGraph.pullback h hh
    (GaussianRegularizedSecondDerivative.regularizedSecond f) = _
  rw [GaussianRegularizedSecondDerivative.regularizedSecond_actual_graph f g q hf hg,
    commonSmoothing_pullback]

def fullObservedSecond (h : CoefficientSpace) (hh : ‖h‖ = 1) : GaussianL2 →L[ℝ] GaussianL2 :=
  (observedSecond h hh).comp (IBMClockObservationGraph.pullback h hh).toContinuousLinearMap.adjoint

theorem pullback_adjoint_contraction (h : CoefficientSpace) (hh : ‖h‖ = 1) (f : GaussianL2) :
    ‖(IBMClockObservationGraph.pullback h hh).toContinuousLinearMap.adjoint f‖ ≤ ‖f‖ := by
  let J := IBMClockObservationGraph.pullback h hh
  let x := J.toContinuousLinearMap.adjoint f
  have he := J.toContinuousLinearMap.adjoint_inner_left x f
  change inner ℝ x x = inner ℝ f (J x) at he
  have hn : |inner ℝ f (J x)| ≤ ‖f‖ * ‖J x‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) f (J x)
  have hb := (le_abs_self (inner ℝ f (J x))).trans hn
  rw [← he, real_inner_self_eq_norm_sq, J.norm_map] at hb
  change ‖x‖ ≤ ‖f‖
  by_cases hx : x = 0
  · simpa [hx] using norm_nonneg f
  · exact le_of_mul_le_mul_right (by simpa only [pow_two] using hb) (norm_pos_iff.mpr hx)

theorem fullObservedSecond_norm_le (h : CoefficientSpace) (hh : ‖h‖ = 1) :
    ‖fullObservedSecond h hh‖ ≤ Real.sqrt 6 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  exact ((observedSecond h hh).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (observedSecond_norm_le h hh) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (pullback_adjoint_contraction h hh f) (Real.sqrt_nonneg _)))

theorem fullObservedSecond_pullback (h : CoefficientSpace) (hh : ‖h‖ = 1) (f : GaussianCore.GaussianL2) :
    fullObservedSecond h hh (IBMClockObservationGraph.pullback h hh f) = observedSecond h hh f := by
  let J := IBMClockObservationGraph.pullback h hh
  have he := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self J.toContinuousLinearMap).mp J.norm_map
  have hf := congrArg (fun L : GaussianCore.GaussianL2 →L[ℝ] GaussianCore.GaussianL2 => L f) he
  change observedSecond h hh (J.toContinuousLinearMap.adjoint (J f)) = observedSecond h hh f
  rw [show J.toContinuousLinearMap.adjoint (J f) = f from hf]

/-- Source randomness is carried by the OUTER Gaussian factor. The same clock
smoothing and bound act on genuine Bochner L2 classes of clock functions. -/
abbrev SourceField := Lp GaussianL2 2 gaussianProduct

def sourceSmoothing : SourceField →L[ℝ] SourceField := commonSmoothing.compLpL 2 gaussianProduct

def sourceSecond (h : CoefficientSpace) (hh : ‖h‖ = 1) : SourceField →L[ℝ] SourceField :=
  (fullObservedSecond h hh).compLpL 2 gaussianProduct

theorem sourceSecond_norm_le (h : CoefficientSpace) (hh : ‖h‖ = 1) :
    ‖sourceSecond h hh‖ ≤ Real.sqrt 6 :=
  ((fullObservedSecond h hh).norm_compLpL_le).trans (fullObservedSecond_norm_le h hh)

theorem sourceSmoothing_injective : Function.Injective sourceSmoothing := by
  intro f g hfg
  apply Lp.ext
  filter_upwards [commonSmoothing.coeFn_compLpL f, commonSmoothing.coeFn_compLpL g] with ω hf hg
  apply commonSmoothing_injective
  have he := congrArg (fun v : SourceField => v ω) hfg
  exact hf.symm.trans (he.trans hg)

theorem sourceSecond_ae (h : CoefficientSpace) (hh : ‖h‖ = 1) (f : SourceField) :
    sourceSecond h hh f =ᵐ[gaussianProduct] fun ω => fullObservedSecond h hh (f ω) :=
  (fullObservedSecond h hh).coeFn_compLpL f

end OperatorDerivativeRewrite.Foundation.GaussianObservedSecondRegularization
