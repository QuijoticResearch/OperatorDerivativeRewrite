import Foundation.IBMSchwartzClockMean

/-! Continuity of the actual nonlinear source curvature, using finite
Gaussian product witnesses rather than unrestricted L2 multiplication. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceContinuity
open InfiniteGaussian IBMCorrectionStein IBMSchwartzSecondProjection IBMSchwartzHeatBounds
open FractionalControlledEstimate IBMCubicFirstChaos IBMGaussianSteinMoments
open GaussianTimeSpaceHermite IBMQuarticSecondChaos

theorem weighted_sub (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ)
    (f h : GaussianL2) :
    weightedClass g a u j (f-h) = weightedClass g a u j f-weightedClass g a u j h := by
  apply Lp.ext
  filter_upwards [weightedClass_coeFn g a u j (f-h), weightedClass_coeFn g a u j f,
    weightedClass_coeFn g a u j h, Lp.coeFn_sub f h,
    Lp.coeFn_sub (weightedClass g a u j f) (weightedClass g a u j h)] with ω hd hf hh hs hw
  rw [hd, hw, Pi.sub_apply, hf, hh, hs, Pi.sub_apply]
  ring

theorem observation_difference_bound (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) (f H : GaussianL2)
    (hH : H =ᵐ[gaussianProduct] fun ω => firstChaosEmbedding (u-v) ω*f ω) :
    ‖weightedClass g a u j f-weightedClass g a v j f‖ ≤
      (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 (jet g j)) : ℝ)*‖H‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedClass_coeFn g a u j f, weightedClass_coeFn g a v j f,
    Lp.coeFn_sub (weightedClass g a u j f) (weightedClass g a v j f),
    Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding v), hH] with ω hu hv hw hs hh
  have hd : firstChaosEmbedding (u-v) ω = firstChaosEmbedding u ω-firstChaosEmbedding v ω := by
    rw [map_sub, hs, Pi.sub_apply]
  rw [hw, Pi.sub_apply, hu, hv, hh, hd, ← sub_mul, norm_mul, norm_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    ((shiftedJet_lipschitz g a j).norm_sub_le (firstChaosEmbedding u ω) (firstChaosEmbedding v ω))
    (norm_nonneg (f ω))

/-- The product witness is an actual L2 representative, with a proved
limit; no multiplication continuity on arbitrary L2 is assumed. -/
theorem weighted_tendsto {X : Type*} {l : Filter X} (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    (u : X → CoefficientSpace) (v : CoefficientSpace) (f H : X → GaussianL2) (f0 : GaussianL2)
    (hf : Tendsto f l (𝓝 f0)) (hH : Tendsto H l (𝓝 0))
    (hrep : ∀ x, H x =ᵐ[gaussianProduct] fun ω => firstChaosEmbedding (u x-v) ω*f0 ω) :
    Tendsto (fun x => weightedClass g a (u x) j (f x)) l (𝓝 (weightedClass g a v j f0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := ((hf.sub_const f0).norm.const_mul (SchwartzMap.seminorm ℝ 0 0 (jet g j))).add
    (hH.norm.const_mul (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 (jet g j)) : ℝ))
  apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_
    (by simpa only [sub_self, norm_zero, mul_zero, add_zero] using ht)
  exact Eventually.of_forall fun x => by
    have he : weightedClass g a (u x) j (f x)-weightedClass g a v j f0 =
        (weightedClass g a (u x) j (f x)-weightedClass g a (u x) j f0)+
        (weightedClass g a (u x) j f0-weightedClass g a v j f0) := by abel
    rw [he]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [← weighted_sub]
      exact weightedClass_norm_le g a (u x) j (f x-f0)
    · exact observation_difference_bound g a (u x) v j f0 (H x) (hrep x)

theorem square_eq_wick (u : CoefficientSpace) :
    square u = (wick u 2 : GaussianL2)+‖u‖^2 • gaussianOne := by
  apply Lp.ext
  filter_upwards [square_coeFn u, wickTwo_coeFn u,
    Lp.coeFn_add (wick u 2 : GaussianL2) (‖u‖^2 • gaussianOne),
    Lp.coeFn_smul (‖u‖^2) gaussianOne, gaussianOne_coeFn] with ω hs hw ha hm ho
  rw [hs, ha, Pi.add_apply, hw, hm, Pi.smul_apply, ho, smul_eq_mul]
  ring

theorem square_continuous : Continuous square := by
  change Continuous (fun u : CoefficientSpace => square u)
  simp_rw [square_eq_wick]
  exact (GaussianWickContinuity.wick_continuous 2).add
    ((continuous_norm.pow 2).smul continuous_const)

theorem cube_continuous : Continuous cube := by
  exact (GaussianWickContinuity.wick_continuous 3).add
    (((continuous_norm.pow 2).const_mul 3).smul (GaussianWickContinuity.wick_continuous 1))

theorem mixedCube_continuous_of {u v : ℝ → CoefficientSpace} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun r => mixedCube (u r) (v r)) :=
  (((cube_continuous.comp (hu.add hv)).add (cube_continuous.comp (hu.sub hv))).sub
    ((cube_continuous.comp hu).const_smul (2 : ℝ))).const_smul (1/6 : ℝ)

theorem mixedCube_zero_left (v : CoefficientSpace) : mixedCube 0 v = 0 := by
  apply Lp.ext
  filter_upwards [mixedCube_coeFn 0 v, Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hm hz
  rw [hm, hz]
  simp

def rawProduct (u v : CoefficientSpace) : GaussianL2 := (1/4 : ℝ) • (square (u+v)-square (u-v))

theorem rawProduct_coeFn (u v : CoefficientSpace) :
    rawProduct u v =ᵐ[gaussianProduct] fun ω => firstChaosEmbedding u ω*firstChaosEmbedding v ω := by
  filter_upwards [Lp.coeFn_smul (1/4 : ℝ) (square (u+v)-square (u-v)),
    Lp.coeFn_sub (square (u+v)) (square (u-v)), square_coeFn (u+v), square_coeFn (u-v),
    Lp.coeFn_add (firstChaosEmbedding u) (firstChaosEmbedding v),
    Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding v)] with ω hs hd hp hm ha hb
  rw [rawProduct, hs, Pi.smul_apply, hd, Pi.sub_apply, hp, hm, map_add, map_sub, ha, hb]
  simp only [Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem rawProduct_continuous_of {u v : ℝ → CoefficientSpace} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun r => rawProduct (u r) (v r)) :=
  ((square_continuous.comp (hu.add hv)).sub
    (square_continuous.comp (hu.sub hv))).const_smul (1/4 : ℝ)

theorem rawProduct_zero_left (v : CoefficientSpace) : rawProduct 0 v = 0 := by
  apply Lp.ext
  filter_upwards [rawProduct_coeFn 0 v, Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hm hz
  rw [hm, hz]
  simp

theorem weighted_square_continuous_of (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    {u v : ℝ → CoefficientSpace} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun r => weightedClass g a (u r) j (square (v r))) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  have hf := ((square_continuous.comp hv).continuousAt (x := r)).tendsto
  have huc : Continuous (fun x : ℝ => u x-u r) := hu.sub continuous_const
  have hH := (mixedCube_continuous_of huc
    (continuous_const : Continuous (fun _ : ℝ => v r))).continuousAt (x := r) |>.tendsto
  simp only [sub_self, mixedCube_zero_left] at hH
  apply weighted_tendsto g a j u (u r) (fun x => square (v x))
    (fun x => mixedCube (u x-u r) (v r)) (square (v r)) hf hH
  intro x
  filter_upwards [mixedCube_coeFn (u x-u r) (v r), square_coeFn (v r)] with ω hm hs
  rw [hm, hs]

theorem weighted_linear_continuous_of (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ)
    {u w : ℝ → CoefficientSpace} (hu : Continuous u) (hw : Continuous w) :
    Continuous (fun r => weightedClass g a (u r) j (firstChaosEmbedding (w r))) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  have hf := ((firstChaosEmbedding.continuous.comp hw).continuousAt (x := r)).tendsto
  have huc : Continuous (fun x : ℝ => u x-u r) := hu.sub continuous_const
  have hH := (rawProduct_continuous_of huc
    (continuous_const : Continuous (fun _ : ℝ => w r))).continuousAt (x := r) |>.tendsto
  simp only [sub_self, rawProduct_zero_left] at hH
  exact weighted_tendsto g a j u (u r) (fun x => firstChaosEmbedding (w x))
    (fun x => rawProduct (u x-u r) (w r)) (firstChaosEmbedding (w r)) hf hH
    (fun x => rawProduct_coeFn _ _)

theorem mollifiedClass_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Continuous (mollifiedClass g a n) := by
  have hc := IBMClockCubicTimeProjection.tripleCoefficient_continuous n
  exact (weighted_square_continuous_of g a 2 (hc 0) (hc 1)).add
    (weighted_linear_continuous_of g a 1 (hc 0) (hc 2))

end OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceContinuity
