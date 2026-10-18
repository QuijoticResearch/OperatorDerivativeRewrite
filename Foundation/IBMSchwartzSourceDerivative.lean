import Foundation.IBMSchwartzSourceContinuity

/-! Full nonlinear source-Hilbert differentiation, before chaos projection.
The quadratic L2 remainder uses an actual Gaussian square, never ambient
multiplication of arbitrary L2 classes. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceDerivative
open InfiniteGaussian IBMCorrectionStein IBMFirstChaosMixedStein
open IBMSchwartzSecondProjection IBMSchwartzHeatBounds IBMGaussianMeanDerivative
open FractionalControlledEstimate

def observable (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) : GaussianL2 :=
  testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)

theorem observable_coeFn (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    observable g a j u =ᵐ[gaussianProduct] fun ω => shiftedJet g a j (firstChaosEmbedding u ω) :=
  testClass_coeFn _ _ _

theorem observable_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    ‖observable g a j u‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g j) := by
  apply GaussianBoundedApproximation.gaussian_norm_le (by positivity)
  filter_upwards [observable_coeFn g a j u] with ω hw
  rw [hw]
  exact shiftedJet_bound g a j _

def weightedOperator (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    GaussianL2 →L[ℝ] GaussianL2 :=
  LinearMap.mkContinuous
    { toFun := weightedClass g a u j
      map_add' := by
        intro f h
        apply Lp.ext
        filter_upwards [weightedClass_coeFn g a u j (f+h), weightedClass_coeFn g a u j f,
          weightedClass_coeFn g a u j h, Lp.coeFn_add f h,
          Lp.coeFn_add (weightedClass g a u j f) (weightedClass g a u j h)] with ω hd hf hh hs hw
        rw [hd, hw, Pi.add_apply, hf, hh, hs, Pi.add_apply]
        ring
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [weightedClass_coeFn g a u j (c • f), weightedClass_coeFn g a u j f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (weightedClass g a u j f)] with ω hd hf hs hw
        simp only [RingHom.id_apply]
        rw [hd, hw, Pi.smul_apply, hf, hs, Pi.smul_apply]
        simp only [smul_eq_mul]
        ring }
    (SchwartzMap.seminorm ℝ 0 0 (jet g j)) (weightedClass_norm_le g a u j)

def sourceDerivative (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    CoefficientSpace →L[ℝ] GaussianL2 :=
  (weightedOperator g a (j+1) u).comp firstChaosEmbedding.toContinuousLinearMap

theorem sourceDerivative_apply (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    (u v : CoefficientSpace) :
    sourceDerivative g a j u v = weightedClass g a u (j+1) (firstChaosEmbedding v) := rfl

theorem observable_remainder (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    (u v : CoefficientSpace) :
    ‖observable g a j v-observable g a j u-sourceDerivative g a j u (v-u)‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))*‖v-u‖^2 := by
  have hb : ‖observable g a j v-observable g a j u-sourceDerivative g a j u (v-u)‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))/2)*‖square (v-u)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [observable_coeFn g a j v, observable_coeFn g a j u,
      weightedClass_coeFn g a u (j+1) (firstChaosEmbedding (v-u)), square_coeFn (v-u),
      Lp.coeFn_sub (observable g a j v) (observable g a j u),
      Lp.coeFn_sub (observable g a j v-observable g a j u) (sourceDerivative g a j u (v-u)),
      Lp.coeFn_sub (firstChaosEmbedding v) (firstChaosEmbedding u)] with ω hv hu hw hq hs hr hd
    have he : firstChaosEmbedding (v-u) ω = firstChaosEmbedding v ω-firstChaosEmbedding u ω := by
      rw [map_sub, hd, Pi.sub_apply]
    rw [hr, Pi.sub_apply, hs, Pi.sub_apply, hv, hu, sourceDerivative_apply, hw, hq]
    have ht := first_order_remainder_bound (shiftedJet_smooth g a j)
      (C := SchwartzMap.seminorm ℝ 0 0 (jet g (j+2)))
      (by simpa only [shiftedJet_deriv] using shiftedJet_bound g a (j+1+1))
      (firstChaosEmbedding u ω) (firstChaosEmbedding v ω)
    simpa only [shiftedJet_deriv, he, Real.norm_eq_abs, abs_sq, sq_abs] using ht
  have hs := mul_le_mul_of_nonneg_left (square_norm_le (v-u))
    (by positivity : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))/2)
  exact hb.trans (hs.trans_eq (by ring))

/-- Actual Frechet derivative on the whole source Hilbert space, including
zero and every degenerate direction. No projection or formal series occurs. -/
theorem observable_hasFDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    HasFDerivAt (observable g a j) (sourceDerivative g a j u) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply (Asymptotics.IsBigO.of_bound
    (SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := CoefficientSpace) (n := 2) (by norm_num))
  exact Eventually.of_forall fun h => by
    simpa only [add_sub_cancel_left, norm_pow, norm_norm] using observable_remainder g a j u (u+h)

theorem observable_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) :
    Continuous (observable g a j) :=
  continuous_iff_continuousAt.mpr fun u => (observable_hasFDerivAt g a j u).continuousAt

theorem observable_comp_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    {u : ℝ → CoefficientSpace} {v : CoefficientSpace} {r : ℝ} (hu : HasDerivAt u v r) :
    HasDerivAt (fun x => observable g a j (u x))
      (weightedClass g a (u r) (j+1) (firstChaosEmbedding v)) r := by
  exact (observable_hasFDerivAt g a j (u r)).comp_hasDerivAt r hu

end OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceDerivative
