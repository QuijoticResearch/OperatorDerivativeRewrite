import Foundation.FourCubeMovingBoundaryQuadratic

/-! The actual joint interior/boundary quadratic action limit, with no unproved saddle hypothesis. -/
noncomputable section
open Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeMovingActionLimit
open QuaternionSU2Representation SU2JointPlaquetteCubic OneSidedCapComplex OneSidedBlockRank
open FourCubePinnedHaar FourCubePinnedCoercivity FourCubeBoundaryCoercivity
open FourCubeHemisphereCoercivity FourCubeScaledBoundaryControl FourCubeMovingBoundaryQuadratic

private theorem axis_zero (a : Fin 3) : axis a 0=1 := by
  apply (defect_zero_iff _).mp
  norm_num [defect,FourCubeWilsonCubic.axis_trace]

theorem movingBoundary_zero_amplitudes (t : ℝ) : movingBoundary t 0 0 0=(fun _ => (1 : SU2)) := by
  funext c
  cases c <;> simp [movingBoundary,FourCubeIntegratedCubic.boundaryData,axis_zero]

theorem movingBoundary_at_zero (x y z : ℝ) : movingBoundary 0 x y z=(fun _ => (1 : SU2)) := by
  funext c
  cases c <;> simp [movingBoundary,FourCubeIntegratedCubic.boundaryData,axis_zero]

theorem ribbon_vacuum (Y : FourCubeHemisphereCoercivity.Field) (p : Upper) (t : ℝ) :
    ribbonAction Y 0 0 0 p t=defect (fillPole 1 (chartField (t • Y)) (ribbonInterior p)) := by
  rw [ribbonAction,movingBoundary_zero_amplitudes]
  simp [FourCubeIntegratedCubic.word]

def movingRay (Y : FourCubeHemisphereCoercivity.Field) (x y z t : ℝ) : ℝ :=
  perturbedAction (movingBoundary t x y z) (chartField (t • Y))

def jointQuadratic (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) : ℝ :=
  FourCubeHaarQuadraticLimit.quadraticForm Y+
    ∑ p : Upper,(ribbonQuadratic Y x y z p-ribbonQuadratic Y 0 0 0 p)

theorem movingRay_reconstruct (Y : FourCubeHemisphereCoercivity.Field) (x y z t : ℝ) :
    movingRay Y x y z t=FourCubeHaarQuadraticLimit.ray Y t+
      ∑ p : Upper,(ribbonAction Y x y z p t-ribbonAction Y 0 0 0 p t) := by
  rw [movingRay,perturbedAction,boundaryAction_decomposition,
    FourCubeHaarQuadraticLimit.ray,pinnedAction,vacuum_decomposition]
  simp_rw [ribbon_vacuum]
  unfold ribbonEnergy ribbonAction
  rw [Finset.sum_sub_distrib]
  ring

theorem movingRay_contDiff (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) :
    ContDiff ℝ 2 (movingRay Y x y z) := by
  have he : movingRay Y x y z=(fun t => FourCubeHaarQuadraticLimit.ray Y t+
      ∑ p : Upper,(ribbonAction Y x y z p t-ribbonAction Y 0 0 0 p t)) :=
    funext (movingRay_reconstruct Y x y z)
  rw [he]
  exact (FourCubeHaarQuadraticLimit.ray_contDiff Y).add
    (ContDiff.sum (fun p _ => (ribbon_action_jets Y x y z p).1.sub (ribbon_action_jets Y 0 0 0 p).1))

theorem movingRay_deriv (Y : FourCubeHemisphereCoercivity.Field) (x y z t : ℝ) :
    deriv (movingRay Y x y z) t=deriv (FourCubeHaarQuadraticLimit.ray Y) t+
      ∑ p : Upper,(deriv (ribbonAction Y x y z p) t-deriv (ribbonAction Y 0 0 0 p) t) := by
  have h0 : HasDerivAt (FourCubeHaarQuadraticLimit.ray Y)
      (deriv (FourCubeHaarQuadraticLimit.ray Y) t) t :=
    ((FourCubeHaarQuadraticLimit.ray_contDiff Y).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hp (p : Upper) : HasDerivAt (fun u => ribbonAction Y x y z p u-ribbonAction Y 0 0 0 p u)
      (deriv (ribbonAction Y x y z p) t-deriv (ribbonAction Y 0 0 0 p) t) t :=
    (((ribbon_action_jets Y x y z p).1.differentiable (by norm_num)).differentiableAt.hasDerivAt).sub
      (((ribbon_action_jets Y 0 0 0 p).1.differentiable (by norm_num)).differentiableAt.hasDerivAt)
  have hh := h0.add (HasDerivAt.fun_sum (u := Finset.univ) (fun p _ => hp p))
  have he : movingRay Y x y z=(fun u => FourCubeHaarQuadraticLimit.ray Y u+
      ∑ p : Upper,(ribbonAction Y x y z p u-ribbonAction Y 0 0 0 p u)) :=
    funext (movingRay_reconstruct Y x y z)
  rw [he]
  convert! hh.deriv using 1

theorem ribbon_first_zero (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) (p : Upper) :
    deriv (ribbonAction Y x y z p) 0=0 := (ribbon_action_jets Y x y z p).2.1

theorem ribbon_second_zero (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) (p : Upper) :
    deriv (deriv (ribbonAction Y x y z p)) 0=ribbonQuadratic Y x y z p :=
  (ribbon_action_jets Y x y z p).2.2

theorem movingRay_first_zero (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) :
    deriv (movingRay Y x y z) 0=0 := by
  rw [movingRay_deriv,FourCubeHaarQuadraticLimit.ray_first_zero]
  simp only [ribbon_first_zero,sub_self,Finset.sum_const_zero,add_zero]

theorem movingRay_second_zero (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) :
    deriv (deriv (movingRay Y x y z)) 0=jointQuadratic Y x y z := by
  have he := funext (movingRay_deriv Y x y z)
  rw [he]
  have h0 : HasDerivAt (deriv (FourCubeHaarQuadraticLimit.ray Y))
      (deriv (deriv (FourCubeHaarQuadraticLimit.ray Y)) 0) 0 :=
    (FourCubeHaarQuadraticLimit.ray_contDiff Y).differentiable_deriv_two.differentiableAt.hasDerivAt
  have hp (p : Upper) : HasDerivAt (fun u => deriv (ribbonAction Y x y z p) u-
      deriv (ribbonAction Y 0 0 0 p) u)
      (deriv (deriv (ribbonAction Y x y z p)) 0-deriv (deriv (ribbonAction Y 0 0 0 p)) 0) 0 :=
    ((ribbon_action_jets Y x y z p).1.differentiable_deriv_two.differentiableAt.hasDerivAt).sub
      ((ribbon_action_jets Y 0 0 0 p).1.differentiable_deriv_two.differentiableAt.hasDerivAt)
  have hh := h0.add (HasDerivAt.fun_sum (u := Finset.univ) (fun p _ => hp p))
  have hd := hh.deriv
  simp only [FourCubeHaarQuadraticLimit.ray_second_gram,ribbon_second_zero] at hd
  convert! hd using 1

theorem movingRay_zero (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) :
    movingRay Y x y z 0=0 := by
  rw [movingRay,movingBoundary_at_zero]
  exact FourCubeHaarQuadraticLimit.ray_zero Y

theorem jointQuadratic_zero_amplitudes (Y : FourCubeHemisphereCoercivity.Field) :
    jointQuadratic Y 0 0 0=FourCubeHaarQuadraticLimit.quadraticForm Y := by
  simp [jointQuadratic]

theorem moving_taylor_polynomial (Y : FourCubeHemisphereCoercivity.Field) (x y z t : ℝ) :
    taylorWithinEval (movingRay Y x y z) 2 Set.univ 0 t=(jointQuadratic Y x y z/2)*t^2 := by
  simp [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_univ,
    iteratedDeriv_succ,iteratedDeriv_zero,movingRay_zero,movingRay_first_zero,movingRay_second_zero]
  ring

theorem moving_quadratic_remainder (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) :
    (fun t : ℝ => movingRay Y x y z t-(jointQuadratic Y x y z/2)*t^2) =o[𝓝 0] (fun t : ℝ => t^2) := by
  simpa only [moving_taylor_polynomial,sub_zero] using
    taylor_isLittleO_univ (x₀ := 0) (n := 2) (movingRay_contDiff Y x y z)

theorem moving_quadratic_limit (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) :
    Tendsto (fun t : ℝ => movingRay Y x y z t/t^2) (𝓝[≠] 0) (𝓝 (jointQuadratic Y x y z/2)) := by
  have hh := ((moving_quadratic_remainder Y x y z).tendsto_div_nhds_zero.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).add_const (jointQuadratic Y x y z/2)
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t ≠ 0 := ht
  field_simp [hn]
  ring

theorem moving_boltzmann_limit (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (-movingRay Y x y z t/t^2)) (𝓝[≠] 0)
      (𝓝 (Real.exp (-jointQuadratic Y x y z/2))) :=
  Real.continuous_exp.continuousAt.tendsto.comp
    (by simpa only [neg_div] using (moving_quadratic_limit Y x y z).neg)

theorem jointQuadratic_nonneg (Y : FourCubeHemisphereCoercivity.Field) (x y z : ℝ) :
    0 ≤ jointQuadratic Y x y z := by
  have hp (t : ℝ) : 0 ≤ movingRay Y x y z t :=
    (FourCubeHaarParity.fullAction_bounds (FourCubeIntegratedCubic.fill (movingBoundary t x y z)
      (fillPole 1 (chartField (t • Y))))).1
  have hh : 0 ≤ jointQuadratic Y x y z/2 :=
    ge_of_tendsto' (moving_quadratic_limit Y x y z) (fun t => div_nonneg (hp t) (sq_nonneg t))
  linarith

end OperatorDerivativeRewrite.Foundation.FourCubeMovingActionLimit
