import Foundation.IBMClockFractionalDomain
import Foundation.IBMClockAverageGraph
/-! Exact first clock Bessel / OLD native Bochner derivative domain bridge,
with the actual probability-factor flip and strong finite-gradient convergence.
Original scalar derivative and closed-graph foundations are reused unchanged. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianClockNativeDomain
open InfiniteGaussian GaussianClockValueOperators GaussianClockSpectralPowers GaussianNumberSectors
open IBMFirstSourceClockGraph IBMClockAverageGraph
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem flip_project (n : ℕ) (f : Field) :
    ProductL2Curry.flip gaussianProduct gaussianProduct (project n f) =
      (GaussianNumberSectors.projection n).compLpL 2 gaussianProduct
        (ProductL2Curry.flip gaussianProduct gaussianProduct f) := by
  exact flip_involutive _

private theorem lifted_projection_norm (n : ℕ) (f : Field) :
    ‖(GaussianNumberSectors.projection n).compLpL 2 gaussianProduct
      (ProductL2Curry.flip gaussianProduct gaussianProduct f)‖ = ‖project n f‖ := by
  rw [← flip_project]
  exact LinearIsometry.norm_map _ _

theorem lifted_projection_energy (u : Field) (n : ℕ) :
    (∫ x, ‖GaussianNumberSectors.projection n (u x)‖^2 ∂gaussianProduct) =
      ‖(GaussianNumberSectors.projection n).compLpL 2 gaussianProduct u‖^2 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [(GaussianNumberSectors.projection n).coeFn_compLpL u] with x hx
  rw [hx]

theorem native_energy_hasSum (u : Field) (v : VectorSpace) (huv : (u,v) ∈ clockDerivative.graph) :
    HasSum (fun (n : ℕ) => (n:ℝ)*‖(GaussianNumberSectors.projection n).compLpL 2 gaussianProduct u‖^2)
      (‖v‖^2) := by
  have hg := (BochnerClosedOperator.mem_lift_graph_iff gaussianProduct closedCylindricalDerivative u v).1 huv
  have hs : ∀ᵐ x ∂gaussianProduct, HasSum (fun (n : ℕ) => (n:ℝ)*‖GaussianNumberSectors.projection n (u x)‖^2)
      (‖v x‖^2) := hg.mono fun x hx => derivative_energy_hasSum hx
  have hi : Integrable (fun x => ∑' (n : ℕ), (n:ℝ)*‖GaussianNumberSectors.projection n (u x)‖^2)
      gaussianProduct := by
    apply ((Lp.memLp v).norm.integrable_sq).congr
    exact hs.mono fun x hx => hx.tsum_eq.symm
  have ht := hasSum_integral_of_dominated_convergence
    (fun (n : ℕ) x => (n:ℝ)*‖GaussianNumberSectors.projection n (u x)‖^2)
    (fun n => by fun_prop)
    (fun n => ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)])
    (hs.mono fun x hx => hx.summable) hi hs
  have he (n : ℕ) : (∫ x, (n:ℝ)*‖GaussianNumberSectors.projection n (u x)‖^2 ∂gaussianProduct) =
      (n:ℝ)*‖(GaussianNumberSectors.projection n).compLpL 2 gaussianProduct u‖^2 := by
    rw [integral_const_mul,lifted_projection_energy]
  simpa only [he,← BochnerL2Dominated.norm_sq_integral] using ht



theorem flip_clockLift (A : GaussianL2 →L[ℝ] GaussianL2) (f : Field) :
    ProductL2Curry.flip gaussianProduct gaussianProduct (clockLift A f) =
      A.compLpL 2 gaussianProduct (ProductL2Curry.flip gaussianProduct gaussianProduct f) :=
  flip_involutive _

private theorem projection_integrable (u : Field) (n : ℕ) :
    Integrable (fun x => ‖GaussianNumberSectors.projection n (u x)‖^2) gaussianProduct := by
  apply ((Lp.memLp ((GaussianNumberSectors.projection n).compLpL 2 gaussianProduct u)).norm.integrable_sq).congr
  filter_upwards [(GaussianNumberSectors.projection n).coeFn_compLpL u] with x hx
  rw [hx]

theorem finite_gradient_energy (N : ℕ) (u : Field) :
    ‖(gradientTruncation N).compLpL 2 gaussianProduct u‖^2 =
      ∑ n ∈ Finset.range (N+1), (n:ℝ)*‖(GaussianNumberSectors.projection n).compLpL 2 gaussianProduct u‖^2 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ x, ‖gradientTruncation N (u x)‖^2 ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [(gradientTruncation N).coeFn_compLpL u] with x hx
      rw [hx]
    _ = ∫ x, ∑ n ∈ Finset.range (N+1), (n:ℝ)*‖GaussianNumberSectors.projection n (u x)‖^2 ∂gaussianProduct := by
      congr 1; funext x
      simp only [gradientTruncation,ContinuousLinearMap.sum_apply,projectedGradient_sum_energy,
        projectedGradient_energy]
    _ = ∑ n ∈ Finset.range (N+1), ∫ x, (n:ℝ)*‖GaussianNumberSectors.projection n (u x)‖^2 ∂gaussianProduct :=
      integral_finset_sum _ (fun n hn => (projection_integrable u n).const_mul (n:ℝ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul,lifted_projection_energy]

theorem lifted_truncation_graph (N : ℕ) (u : Field) :
    ((truncation N).compLpL 2 gaussianProduct u,(gradientTruncation N).compLpL 2 gaussianProduct u)
      ∈ clockDerivative.graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [(truncation N).coeFn_compLpL u,(gradientTruncation N).coeFn_compLpL u] with x hx hg
  rw [hx,hg]
  exact truncation_graph N (u x)



open IBMClockFractionalDomain

theorem flipped_native_energy_hasSum (f : Field) (v : VectorSpace)
    (h : (ProductL2Curry.flip gaussianProduct gaussianProduct f,v) ∈ clockDerivative.graph) :
    HasSum (fun (n : ℕ) => (n:ℝ)*‖project n f‖^2) (‖v‖^2) := by
  simpa only [lifted_projection_norm] using native_energy_hasSum _ v h

theorem bessel_native_domain (f : Field) :
    f ∈ (bessel 1).domain ↔
      ProductL2Curry.flip gaussianProduct gaussianProduct f ∈ clockDerivative.domain := by
  constructor
  · intro hf
    let F := ProductL2Curry.flip gaussianProduct gaussianProduct
    let b : (bessel 1).domain := ⟨f,hf⟩
    have hs := operator_energy (fun n => ((n:ℝ)+1)^((1:ℝ)/2)) b
    simp only [bessel_weight_sq,Real.rpow_one] at hs
    change HasSum (fun (n : ℕ) => ((n:ℝ)+1)*‖project n f‖^2) (‖bessel 1 b‖^2) at hs
    have hbound (N : ℕ) : ‖(gradientTruncation N).compLpL 2 gaussianProduct (F f)‖ ≤ ‖bessel 1 b‖ := by
      have hb : ‖(gradientTruncation N).compLpL 2 gaussianProduct (F f)‖^2 ≤ ‖bessel 1 b‖^2 := by
        rw [finite_gradient_energy]
        simp only [F,lifted_projection_norm]
        calc
          _ ≤ ∑ n ∈ Finset.range (N+1), ((n:ℝ)+1)*‖project n f‖^2 := by
            apply Finset.sum_le_sum
            intro n hn
            nlinarith [sq_nonneg ‖project n f‖]
          _ ≤ _ := by
            rw [← hs.tsum_eq]
            exact hs.summable.sum_le_tsum _ (fun n hn => by positivity)
      nlinarith [norm_nonneg ((gradientTruncation N).compLpL 2 gaussianProduct (F f)),norm_nonneg (bessel 1 b)]
    have ht : Tendsto (fun N => (truncation N).compLpL 2 gaussianProduct (F f)) atTop (𝓝 (F f)) := by
      have hi := F.continuous.tendsto f |>.comp (clock_truncation_tendsto f)
      simpa only [F,Function.comp_def,flip_clockLift] using hi
    obtain ⟨hm,hb⟩ := clock_domain_of_bounded_graph_limit
      (fun N => (truncation N).compLpL 2 gaussianProduct (F f))
      (fun N => (gradientTruncation N).compLpL 2 gaussianProduct (F f)) (F f)
      ‖bessel 1 b‖ (norm_nonneg _) (fun N => lifted_truncation_graph N (F f)) ht hbound
    exact hm
  · intro hf
    let v := clockDerivative ⟨_,hf⟩
    have hs := (flipped_native_energy_hasSum f v (clockDerivative.mem_graph ⟨_,hf⟩)).add
      (project_hasSum_norm_sq f)
    rw [bessel_domain]
    have he (n : ℕ) : ((n:ℝ)+1)*‖project n f‖^2 =
        (n:ℝ)*‖project n f‖^2+‖project n f‖^2 := by ring
    simpa only [Real.rpow_one,he] using hs.summable

theorem bessel_native_energy (f : Field) (hf : f ∈ (bessel 1).domain) :
    ‖bessel 1 ⟨f,hf⟩‖^2 = ‖f‖^2+
      ‖clockDerivative ⟨ProductL2Curry.flip gaussianProduct gaussianProduct f,
        (bessel_native_domain f).1 hf⟩‖^2 := by
  let v := clockDerivative ⟨ProductL2Curry.flip gaussianProduct gaussianProduct f,
    (bessel_native_domain f).1 hf⟩
  have hv : (ProductL2Curry.flip gaussianProduct gaussianProduct f,v) ∈ clockDerivative.graph :=
    clockDerivative.mem_graph ⟨_,(bessel_native_domain f).1 hf⟩
  have hs := (flipped_native_energy_hasSum f v hv).add
    (project_hasSum_norm_sq f)
  have ht := operator_energy (fun n => ((n:ℝ)+1)^((1:ℝ)/2)) (⟨f,hf⟩ : (bessel 1).domain)
  simp only [bessel_weight_sq,Real.rpow_one] at ht
  have he (n : ℕ) : (n:ℝ)*‖project n f‖^2+‖project n f‖^2 =
      ((n:ℝ)+1)*‖project n f‖^2 := by ring
  simp only [he] at hs
  have hh := ht.unique hs
  change ‖bessel 1 ⟨f,hf⟩‖^2 = ‖v‖^2+‖f‖^2 at hh
  change ‖bessel 1 ⟨f,hf⟩‖^2 = ‖f‖^2+‖v‖^2
  linarith

theorem native_graph_truncation_tendsto (u : Field) (v : VectorSpace)
    (huv : (u,v) ∈ clockDerivative.graph) :
    Tendsto (fun N => ((truncation N).compLpL 2 gaussianProduct u,
      (gradientTruncation N).compLpL 2 gaussianProduct u)) atTop (𝓝 (u,v)) := by
  have hg := (BochnerClosedOperator.mem_lift_graph_iff gaussianProduct closedCylindricalDerivative u v).1 huv
  have hu : Tendsto (fun N => (truncation N).compLpL 2 gaussianProduct u) atTop (𝓝 u) := by
    let F := ProductL2Curry.flip gaussianProduct gaussianProduct
    have ht := F.continuous.tendsto (F u) |>.comp (clock_truncation_tendsto (F u))
    simpa only [F,Function.comp_def,flip_clockLift,flip_involutive] using ht
  have hv : Tendsto (fun N => (gradientTruncation N).compLpL 2 gaussianProduct u) atTop (𝓝 v) := by
    apply BochnerL2Dominated.tendsto_of_ae_norm_bound
    · intro N
      filter_upwards [hg,(gradientTruncation N).coeFn_compLpL u] with x hx hN
      rw [hN]
      have hb := projectedGradient_finite_bound hx (Finset.range (N+1))
      have he : ‖gradientTruncation N (u x)‖^2 =
          ∑ n ∈ Finset.range (N+1), ‖projectedGradient n (u x)‖^2 := by
        simp only [gradientTruncation,ContinuousLinearMap.sum_apply,projectedGradient_sum_energy]
      rw [← he] at hb
      nlinarith [norm_nonneg (gradientTruncation N (u x)),norm_nonneg (v x)]
    · have hc : ∀ᵐ x ∂gaussianProduct, ∀ N,
          ((gradientTruncation N).compLpL 2 gaussianProduct u) x = gradientTruncation N (u x) :=
        ae_all_iff.mpr (fun N => (gradientTruncation N).coeFn_compLpL u)
      filter_upwards [hg,hc] with x hx hc
      simp only [hc]
      exact (simultaneous_graph_tendsto hx).snd_nhds
  exact hu.prodMk_nhds hv

end OperatorDerivativeRewrite.Foundation.GaussianClockNativeDomain
