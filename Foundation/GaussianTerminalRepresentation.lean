import Foundation.GaussianHermiteIntegrand

/-! Algebraic completeness at every variance and actual predictable representation
of arbitrary single-time Brownian polynomials. This does not assert multitime PRP. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianTerminalRepresentation
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteRepresentation
open GaussianPredictableFull GaussianPredictableAdjoint GaussianTimeDivergence
open GaussianTimeHilbert SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

theorem polynomial_span (t : ℝ) :
    Submodule.span ℝ (Set.range (polynomial t)) = ⊤ := by
  let S := Submodule.span ℝ (Set.range (polynomial t))
  have hm (n : ℕ) : polynomial t n ∈ S := Submodule.subset_span ⟨n, rfl⟩
  have hx (p : MvPolynomial Unit ℝ) (hp : p ∈ S) : p * X () ∈ S := by
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨n, rfl⟩ := hp
      cases n with
      | zero => simpa using hm 1
      | succ n =>
        have he : polynomial t (n + 1) * X () = polynomial t (n + 2) +
            ((n + 1 : ℝ) * t) • polynomial t n := by rw [polynomial_recursion]; ring
        rw [he]
        exact S.add_mem (hm _) (S.smul_mem _ (hm _))
    | zero => simpa using S.zero_mem
    | add p q hp hq ihp ihq => simpa only [add_mul] using S.add_mem ihp ihq
    | smul a p hp ih => simpa only [smul_mul_assoc] using S.smul_mem a ih
  apply top_unique
  intro p hp
  clear hp
  change p ∈ S
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [polynomial_zero, Algebra.smul_def, algebraMap_eq, mul_one] using S.smul_mem a (hm 0)
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => cases i; exact hx p hp

def centering : GaussianL2 →L[ℝ] GaussianL2 :=
  ContinuousLinearMap.id ℝ GaussianL2 - (innerSL ℝ gaussianOne).smulRight
    gaussianOne

theorem centering_apply (F : GaussianL2) :
    centering F = F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  change F - inner ℝ gaussianOne F • _ = _
  rw [gaussianOne_inner_eq_integral]

def terminalPolynomial (T : ℝ≥0) : MvPolynomial Unit ℝ →ₗ[ℝ] GaussianL2 :=
  familyPolynomialEmbedding (fun _ => hilbertEmbedding TimeHilbert (timeVector T))

theorem terminalPolynomial_hermite (T : ℝ≥0) (n : ℕ) :
    terminalPolynomial T (polynomial T n) = (brownianCore T n : GaussianL2) := by
  apply Lp.ext
  exact (pastCoefficient_coeFn (fun _ : Unit => T) (polynomial T n)).trans
    (brownianCore_coeFn T n).symm

theorem centered_hermite_mem_range (T : ℝ≥0) (n : ℕ) :
    centering (brownianCore T n : GaussianL2) ∈ itoIntegral.toLinearMap.range := by
  cases n with
  | zero =>
    have he : (brownianCore T 0 : GaussianL2) = gaussianOne :=
      core_zero _ _
    rw [he]
    change gaussianOne -
      inner ℝ gaussianOne gaussianOne • _ ∈ _
    rw [GaussianDeterministicGraphCore.gaussianOne_inner_self, one_smul, sub_self]
    exact Submodule.zero_mem _
  | succ n =>
    change (brownianCore T (n + 1) : GaussianL2) - inner ℝ gaussianOne (brownianCore T (n + 1) : GaussianL2) • gaussianOne ∈ _
    rw [show inner ℝ gaussianOne (brownianCore T (n + 1) : GaussianL2) = 0 from wick_centered _ n, zero_smul, sub_zero]
    exact ⟨(n + 1 : ℝ) • hermiteIntegrand n T, by
      change itoIntegral ((n + 1 : ℝ) • hermiteIntegrand n T) = _
      rw [map_smul]
      exact (hermite_representation n T).symm⟩

theorem centered_terminalPolynomial_mem_range (T : ℝ≥0) (p : MvPolynomial Unit ℝ) :
    centering (terminalPolynomial T p) ∈ itoIntegral.toLinearMap.range := by
  have h : Submodule.span ℝ (Set.range (polynomial (T : ℝ))) ≤
      itoIntegral.toLinearMap.range.comap (centering.toLinearMap.comp (terminalPolynomial T)) := by
    apply Submodule.span_le.mpr
    rintro p ⟨n, rfl⟩
    change centering (terminalPolynomial T (polynomial T n)) ∈ itoIntegral.toLinearMap.range
    rw [terminalPolynomial_hermite]
    exact centered_hermite_mem_range T n
  rw [polynomial_span] at h
  exact h (Submodule.mem_top)

def terminalPolynomialIntegrand (T : ℝ≥0) (p : MvPolynomial Unit ℝ) : fullPredictable :=
  predictableAdjoint (centering (terminalPolynomial T p))

theorem terminalPolynomial_representation (T : ℝ≥0) (p : MvPolynomial Unit ℝ) :
    itoIntegral (terminalPolynomialIntegrand T p) =
      terminalPolynomial T p - (∫ ω, terminalPolynomial T p ω ∂gaussianProduct) •
        gaussianOne := by
  obtain ⟨u, hu⟩ := centered_terminalPolynomial_mem_range T p
  change itoIntegral u = _ at hu
  rw [← centering_apply]
  unfold terminalPolynomialIntegrand
  rw [← hu, predictableAdjoint_integral]

/-- This is the sigma-algebra of one observation, not the full Brownian past. -/
theorem terminalPolynomial_closure (T : ℝ≥0) :
    (terminalPolynomial T).range.topologicalClosure =
      lpMeas ℝ ℝ (MeasurableSpace.comap (GaussianTimeProcess.process T) inferInstance)
        2 gaussianProduct := by
  have he := familyPolynomial_closure
    (fun _ : Unit => hilbertEmbedding TimeHilbert (timeVector T))
  have hs : MeasurableSpace.comap (firstChaosFamily
      (fun _ : Unit => hilbertEmbedding TimeHilbert (timeVector T))) inferInstance =
      MeasurableSpace.comap (GaussianTimeProcess.process T) inferInstance := by
    change MeasurableSpace.comap (fun ω (_ : Unit) => GaussianTimeProcess.process T ω)
      inferInstance = _
    rw [MeasurableSpace.comap_process_pi]
    simp
  rw [hs] at he
  exact he

theorem centered_terminalL2_mem_range (T : ℝ≥0) (F : GaussianL2)
    (hF : AEStronglyMeasurable[MeasurableSpace.comap (GaussianTimeProcess.process T) inferInstance]
      F gaussianProduct) : centering F ∈ itoIntegral.toLinearMap.range := by
  have h : (terminalPolynomial T).range.topologicalClosure ≤
      itoIntegral.toLinearMap.range.comap centering.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro F ⟨p, rfl⟩
      exact centered_terminalPolynomial_mem_range T p
    · exact GaussianBrownianGeneratedSpace.integralRange_isClosed.preimage centering.continuous
  rw [terminalPolynomial_closure] at h
  exact h hF

theorem terminalL2_representation (T : ℝ≥0) (F : GaussianL2)
    (hF : AEStronglyMeasurable[MeasurableSpace.comap (GaussianTimeProcess.process T) inferInstance]
      F gaussianProduct) :
    itoIntegral (predictableAdjoint (centering F)) =
      F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  obtain ⟨u, hu⟩ := centered_terminalL2_mem_range T F hF
  change itoIntegral u = _ at hu
  rw [← centering_apply, ← hu, predictableAdjoint_integral]

end OperatorDerivativeRewrite.Foundation.GaussianTerminalRepresentation
