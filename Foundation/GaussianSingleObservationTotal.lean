import Foundation.GaussianVanishingPrediction
import Foundation.InfiniteGaussianDensity

/-! Totality of genuine one-direction Gaussian observation spaces, derived
from existing finite Gaussian moment and cylinder uniqueness. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianSingleObservationTotal
open InfiniteGaussian GaussianConditionalGraph GaussianSingleObservationPrediction
open FiniteGaussian

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def finiteDirection (s : Finset ℕ) (L : (s → ℝ) →L[ℝ] ℝ) : CoefficientSpace :=
  ∑ i : s, L (Pi.single i 1) • lp.single 2 i.val (1 : ℝ)

theorem finiteDirection_actual (s : Finset ℕ) (L : (s → ℝ) →L[ℝ] ℝ) :
    firstChaosEmbedding (finiteDirection s L) =ᵐ[gaussianProduct]
      fun ω => L (finiteProjection s ω) := by
  classical
  have he : firstChaosEmbedding (finiteDirection s L) =
      ∑ i : s, L (Pi.single i 1) • coordinateL2 i.val := by
    simp only [finiteDirection,map_sum,map_smul,firstChaos_single,one_smul]
  rw [he]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i : s => L (Pi.single i 1) • coordinateL2 i.val),
    ae_all_iff.mpr (fun i : s => Lp.coeFn_smul (L (Pi.single i 1)) (coordinateL2 i.val)),
    ae_all_iff.mpr (fun i : s => coordinateL2_coeFn i.val)] with ω hs hm hc
  rw [hs]
  simp only [Finset.sum_apply]
  have ha := linearPowerPolynomial_eval L 1 (finiteProjection s ω)
  simp only [linearPowerPolynomial,map_sum,map_mul,
    MvPolynomial.eval_C,MvPolynomial.eval_X,pow_one] at ha
  rw [← ha]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hm i,Pi.smul_apply,smul_eq_mul,hc i]
  congr 1
  · congr 1
    ext j
    simp [Pi.single_apply]

theorem finite_power_mem_single (s : Finset ℕ) (L : (s → ℝ) →L[ℝ] ℝ) (n : ℕ) :
    finitePullback s (productPolynomialL2 (linearPowerPolynomial L n)) ∈
      singleGenerated (finiteDirection s L) := by
  let u := finiteDirection s L
  have hu : firstChaosEmbedding u ∈ singleGenerated u := by
    exact GaussianWickConditionalProjection.firstChaos_mem_generated_of_sourceSpan
      (fun _ : Unit => u) u
      ((Submodule.span ℝ (range (fun _ : Unit => u))).le_topologicalClosure
        (Submodule.subset_span ⟨(),rfl⟩))
  have hxu : AEStronglyMeasurable[MeasurableSpace.comap
      (firstChaosFamily (fun _ : Unit => u)) inferInstance]
      (firstChaosEmbedding u) gaussianProduct := hu
  have hm : AEStronglyMeasurable[MeasurableSpace.comap
      (firstChaosFamily (fun _ : Unit => u)) inferInstance]
      (fun ω => (firstChaosEmbedding u ω)^n) gaussianProduct :=
    hxu.pow n
  have ha := (finiteProjection_measurePreserving s).quasiMeasurePreserving.ae_eq_comp
    (productPolynomialL2_coeFn (linearPowerPolynomial L n))
  apply hm.congr
  filter_upwards [finitePullback_coeFn s (productPolynomialL2 (linearPowerPolynomial L n)),
    ha,finiteDirection_actual s L] with ω hp ha hu
  change (firstChaosEmbedding (finiteDirection s L) ω)^n = _
  change productPolynomialL2 (linearPowerPolynomial L n) (finiteProjection s ω) =
    MvPolynomial.eval (finiteProjection s ω) (linearPowerPolynomial L n) at ha
  rw [hp,ha,linearPowerPolynomial_eval,hu]

theorem closed_submodule_eq_top (M : Submodule ℝ GaussianL2)
    (hM : IsClosed (M : Set GaussianL2))
    (hu : ∀ u : CoefficientSpace, singleGenerated u ≤ M) : M = ⊤ := by
  have hb : Mᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    have hz (s : Finset ℕ) : (finitePullback s).toContinuousLinearMap.adjoint f = 0 := by
      apply eq_zero_of_linear_power_integrals
      intro L n
      let p := linearPowerPolynomial L n
      have hi : inner ℝ ((finitePullback s).toContinuousLinearMap.adjoint f)
          (productPolynomialL2 p) = 0 := by
        rw [ContinuousLinearMap.adjoint_inner_left]
        exact M.inner_left_of_mem_orthogonal (hu _ (finite_power_mem_single s L n)) hf
      rw [L2.inner_def] at hi
      convert hi using 1
      apply integral_congr_ae
      filter_upwards [productPolynomialL2_coeFn p] with x hx
      rw [hx,linearPowerPolynomial_eval,Real.inner_apply]
    have hp : ∀ (s : Finset ℕ) (g : ScalarGaussianL2 s),
        inner ℝ f (finitePullback s g) = 0 := by
      intro s g
      change inner ℝ f ((finitePullback s).toContinuousLinearMap g) = 0
      rw [← ContinuousLinearMap.adjoint_inner_left,hz,inner_zero_left]
    have he := ae_zero_of_cylinder_integrals f ((Lp.memLp f).integrable (by norm_num))
      (fun s S hS => by
        have hi := hp s (indicatorConstLp 2 hS (measure_ne_top _ _) (1 : ℝ))
        change inner ℝ f (Lp.compMeasurePreserving (finiteProjection s)
          (finiteProjection_measurePreserving s) (indicatorConstLp 2 hS _ (1 : ℝ))) = 0 at hi
        rw [Lp.indicatorConstLp_compMeasurePreserving,real_inner_comm,
          L2.inner_indicatorConstLp_one] at hi
        exact hi)
    have hf0 : f = 0 := Lp.ext (he.trans (Lp.coeFn_zero ℝ 2 gaussianProduct).symm)
    simpa only [hf0] using (⊥ : Submodule ℝ GaussianL2).zero_mem
  have hc := Submodule.orthogonal_eq_bot_iff.mp hb
  simpa only [hM.submodule_topologicalClosure_eq] using hc


/-- Strong decay of every first-chaos prediction lifts to all Gaussian L2,
without monotone observation spaces or a finite index assumption. -/
theorem prediction_all {I : Type*} (h : ℕ → I → CoefficientSpace)
    (hu : ∀ u : CoefficientSpace, Tendsto
      (fun n => GaussianWickConditionalProjection.sourceProjection (h n) u) atTop (𝓝 0))
    (F : GaussianL2) :
    Tendsto (fun n => conditionalProjection (h n) F) atTop
      (𝓝 (GaussianVanishingPrediction.meanProjection F)) := by
  have hs := closed_submodule_eq_top (GaussianVanishingPrediction.convergenceSpace h)
    (GaussianVanishingPrediction.convergenceSpace_isClosed h)
    (fun u G hG => GaussianVanishingPrediction.single_tendsto h u (hu u) G hG)
  have hf : F ∈ GaussianVanishingPrediction.convergenceSpace h := hs.symm ▸ trivial
  exact hf

end OperatorDerivativeRewrite.Foundation.GaussianSingleObservationTotal
