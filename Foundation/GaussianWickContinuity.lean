import Foundation.IBMCubicFirstChaos

/-! Continuity of all finite Wick degrees in the actual Gaussian source
direction, derived from exact mixed moments rather than pointwise choices. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.GaussianWickContinuity
open InfiniteGaussian GaussianTimeSpaceHermite IBMCubicFirstChaos IBMGaussianSteinMoments

theorem wick_norm_sq (h : CoefficientSpace) (n : ℕ) :
    ‖(wick h n : GaussianL2)‖^2 = (n.factorial : ℝ)*(‖h‖^2)^n := by
  rw [← real_inner_self_eq_norm_sq, wick_inner, if_pos rfl, real_inner_self_eq_norm_sq]

theorem wick_distance_sq (h k : CoefficientSpace) (n : ℕ) :
    ‖(wick h n : GaussianL2)-(wick k n : GaussianL2)‖^2 =
      (n.factorial : ℝ)*((‖h‖^2)^n+(‖k‖^2)^n-2*(inner ℝ h k)^n) := by
  rw [norm_sub_sq_real, wick_norm_sq, wick_norm_sq, wick_inner, if_pos rfl]
  ring

theorem wick_continuous (n : ℕ) : Continuous (fun h : CoefficientSpace => (wick h n : GaussianL2)) := by
  apply continuous_iff_continuousAt.mpr
  intro k
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun h : CoefficientSpace => Real.sqrt
      ((n.factorial : ℝ)*((‖h‖^2)^n+(‖k‖^2)^n-2*(inner ℝ h k)^n))) := by fun_prop
  have he : (fun h : CoefficientSpace => ‖(wick h n : GaussianL2)-(wick k n : GaussianL2)‖) =
      (fun h : CoefficientSpace => Real.sqrt
        ((n.factorial : ℝ)*((‖h‖^2)^n+(‖k‖^2)^n-2*(inner ℝ h k)^n))) := by
    funext h
    rw [← wick_distance_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  simpa only [real_inner_self_eq_norm_sq, mul_zero, sub_self, show (2 : ℝ)*
    (‖k‖^2)^n = (‖k‖^2)^n+(‖k‖^2)^n by ring, Real.sqrt_zero] using hc.tendsto k

theorem cube_continuous : Continuous cube := by
  change Continuous (fun h : CoefficientSpace => (wick h 3 : GaussianL2) +
    (3*‖h‖^2) • (wick h 1 : GaussianL2))
  exact (wick_continuous 3).add
    ((continuous_const.mul (continuous_norm.pow 2)).smul (wick_continuous 1))

theorem correction_continuous_of {X : Type*} [TopologicalSpace X]
    (u v w : X → CoefficientSpace) (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x => correction (u x) (v x) (w x)) := by
  have hm (a b : X → CoefficientSpace) (ha : Continuous a) (hb : Continuous b) :
      Continuous (fun x => mixedCube (a x) (b x)) := by
    unfold mixedCube
    exact (((cube_continuous.comp (ha.add hb)).add
      (cube_continuous.comp (ha.sub hb))).sub
        ((cube_continuous.comp ha).const_smul (2 : ℝ))).const_smul (1/6 : ℝ)
  exact (hm u v hu hv).add ((hm w u hw hu).const_smul (1/2 : ℝ))

end OperatorDerivativeRewrite.Foundation.GaussianWickContinuity
