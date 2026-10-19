import Foundation.IBMSourceProductBounds
import Foundation.IBMFullSchwartzTerminal

/-! Operator-norm second source differentiation of the whole Schwartz
observable, and the actual unprojected spatial curvature identity. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceSecondDerivative
open InfiniteGaussian IBMCorrectionStein IBMSchwartzSourceDerivative
open IBMSchwartzSecondProjection IBMSchwartzSourceContinuity IBMSourceProductBounds
open IBMGaussianMeanDerivative IBMCubicFirstChaos

def secondDerivative (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    CoefficientSpace →L[ℝ] CoefficientSpace →L[ℝ] GaussianL2 :=
  ((ContinuousLinearMap.compL ℝ CoefficientSpace GaussianL2 GaussianL2)
    (weightedOperator g a (j+2) u)).comp rawBilinear

theorem secondDerivative_apply (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    (u h k : CoefficientSpace) :
    secondDerivative g a j u h k = weightedClass g a u (j+2) (rawProduct h k) := rfl

theorem weighted_remainder (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    (u v k : CoefficientSpace) :
    ‖weightedClass g a v j (firstChaosEmbedding k)-weightedClass g a u j (firstChaosEmbedding k)-
      weightedClass g a u (j+1) (rawProduct (v-u) k)‖ ≤
      (6*SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))*‖v-u‖^2)*‖k‖ := by
  have hb : ‖weightedClass g a v j (firstChaosEmbedding k)-
      weightedClass g a u j (firstChaosEmbedding k)-
      weightedClass g a u (j+1) (rawProduct (v-u) k)‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))/2)*‖mixedCube k (v-u)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [weightedClass_coeFn g a v j (firstChaosEmbedding k),
      weightedClass_coeFn g a u j (firstChaosEmbedding k),
      weightedClass_coeFn g a u (j+1) (rawProduct (v-u) k),
      rawProduct_coeFn (v-u) k, mixedCube_coeFn k (v-u),
      Lp.coeFn_sub (weightedClass g a v j (firstChaosEmbedding k))
        (weightedClass g a u j (firstChaosEmbedding k)),
      Lp.coeFn_sub (weightedClass g a v j (firstChaosEmbedding k)-
        weightedClass g a u j (firstChaosEmbedding k))
        (weightedClass g a u (j+1) (rawProduct (v-u) k)),
      Lp.coeFn_sub (firstChaosEmbedding v) (firstChaosEmbedding u)] with ω hv hu hw hp hm hs hr hd
    have he : firstChaosEmbedding (v-u) ω = firstChaosEmbedding v ω-firstChaosEmbedding u ω := by
      rw [map_sub, hd, Pi.sub_apply]
    rw [hr, Pi.sub_apply, hs, Pi.sub_apply, hv, hu, hw, hp, hm]
    have ht := first_order_remainder_bound (shiftedJet_smooth g a j)
      (C := SchwartzMap.seminorm ℝ 0 0 (jet g (j+2)))
      (by simpa only [shiftedJet_deriv] using shiftedJet_bound g a (j+1+1))
      (firstChaosEmbedding u ω) (firstChaosEmbedding v ω)
    rw [shiftedJet_deriv] at ht
    have halg : shiftedJet g a j (firstChaosEmbedding v ω)*firstChaosEmbedding k ω-
        shiftedJet g a j (firstChaosEmbedding u ω)*firstChaosEmbedding k ω-
        shiftedJet g a (j+1) (firstChaosEmbedding u ω)*
          (firstChaosEmbedding (v-u) ω*firstChaosEmbedding k ω) =
        (shiftedJet g a j (firstChaosEmbedding v ω)-shiftedJet g a j (firstChaosEmbedding u ω)-
          shiftedJet g a (j+1) (firstChaosEmbedding u ω)*
            (firstChaosEmbedding v ω-firstChaosEmbedding u ω))*firstChaosEmbedding k ω := by
      rw [he]; ring
    rw [halg, norm_mul]
    have hh := mul_le_mul_of_nonneg_right ht (norm_nonneg (firstChaosEmbedding k ω))
    simpa only [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs, he,
      mul_assoc, mul_comm, mul_left_comm] using hh
  have hc := mul_le_mul_of_nonneg_left (mixedCube_norm_separate k (v-u))
    (by positivity : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (jet g (j+2))/2)
  exact hb.trans (hc.trans_eq (by ring))

theorem derivative_remainder (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    (u v : CoefficientSpace) :
    ‖sourceDerivative g a j v-sourceDerivative g a j u-secondDerivative g a j u (v-u)‖ ≤
      6*SchwartzMap.seminorm ℝ 0 0 (jet g (j+3))*‖v-u‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro k
  simpa only [sub_apply, sourceDerivative_apply, secondDerivative_apply,
    show j+1+1=j+2 by omega, show j+1+2=j+3 by omega] using weighted_remainder g a (j+1) u v k

/-- Differentiation takes place in the normed space of bounded source
operators; consequently it is uniform in the differentiated direction. -/
theorem sourceDerivative_hasFDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    (u : CoefficientSpace) :
    HasFDerivAt (sourceDerivative g a j) (secondDerivative g a j u) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply (Asymptotics.IsBigO.of_bound
    (6*SchwartzMap.seminorm ℝ 0 0 (jet g (j+3))) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := CoefficientSpace) (n := 2) (by norm_num))
  exact Eventually.of_forall fun h => by
    simpa only [add_sub_cancel_left, norm_pow, norm_norm] using derivative_remainder g a j u (u+h)

theorem sourceDerivative_comp_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    {u : ℝ → CoefficientSpace} {v : CoefficientSpace} {r : ℝ} (hu : HasDerivAt u v r) :
    HasDerivAt (fun x => sourceDerivative g a j (u x)) (secondDerivative g a j (u r) v) r :=
  (sourceDerivative_hasFDerivAt g a j (u r)).comp_hasDerivAt r hu

theorem weighted_linear_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    {u v : ℝ → CoefficientSpace} {u' v' : CoefficientSpace} {r : ℝ}
    (hu : HasDerivAt u u' r) (hv : HasDerivAt v v' r) :
    HasDerivAt (fun x => weightedClass g a (u x) (j+1) (firstChaosEmbedding (v x)))
      (weightedClass g a (u r) (j+2) (rawProduct u' (v r))+
        weightedClass g a (u r) (j+1) (firstChaosEmbedding v')) r := by
  exact (sourceDerivative_comp_hasDerivAt g a j hu).clm_apply hv

theorem rawProduct_self (v : CoefficientSpace) :
    rawProduct v v = FractionalControlledEstimate.square v := by
  apply Lp.ext
  filter_upwards [rawProduct_coeFn v v, FractionalControlledEstimate.square_coeFn v] with ω hp hs
  rw [hp, hs, pow_two]

def spatialSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : GaussianL2 :=
  weightedClass g a (IBMGaussianSteinMoments.tripleCoefficient n r 0) 1
    (firstChaosEmbedding (IBMGaussianSteinMoments.tripleCoefficient n r 1))

theorem spatial_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (IBMFullSchwartzTerminal.spatial g a n) (spatialSlope g a n r) r :=
  IBMFullSchwartzTerminal.spatial_hasDerivAt g a n r

theorem spatialSlope_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (spatialSlope g a n) (mollifiedClass g a n r) r := by
  change HasDerivAt (fun x => weightedClass g a
    (IBMGaussianSteinMoments.tripleCoefficient n x 0) 1
    (firstChaosEmbedding (IBMGaussianSteinMoments.tripleCoefficient n x 1))) _ r
  simpa only [rawProduct_self, mollifiedClass, correctionClass,
    Nat.zero_add] using weighted_linear_hasDerivAt g a 0
    (IBMQuarticSecondPrimitive.coefficient_zero_hasDerivAt n r)
    (IBMQuarticSecondPrimitive.coefficient_one_hasDerivAt n r)

/-- Genuine full spatial second derivative, with no source projection. -/
theorem spatial_second_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    deriv (deriv (IBMFullSchwartzTerminal.spatial g a n)) r = mollifiedClass g a n r := by
  have he : deriv (IBMFullSchwartzTerminal.spatial g a n) = spatialSlope g a n :=
    funext fun x => (spatial_hasDerivAt g a n x).deriv
  rw [he]
  exact (spatialSlope_hasDerivAt g a n r).deriv

end OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceSecondDerivative
