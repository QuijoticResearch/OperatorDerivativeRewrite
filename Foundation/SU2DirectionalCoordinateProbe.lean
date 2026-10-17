import Foundation.SU2RadialCoordinateProbe

/-! All ordinary affine directions through a nonzero radial base point. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.SU2DirectionalCoordinateProbe
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

def speedSq (x y z : ℝ) : ℝ := x^2+y^2+z^2
def pathSquare (r x y z t : ℝ) : ℝ := r^2+2*r*z*t+speedSq x y z*t^2
def pathRadius (r x y z t : ℝ) : ℝ := Real.sqrt (pathSquare r x y z t)
def path (r x y z t : ℝ) : ℝ := 1-Real.cos (pathRadius r x y z t/2)
def pathSlope (r x y z t : ℝ) : ℝ :=
  (r*z+t*speedSq x y z)*(Real.sin (pathRadius r x y z t/2)/(2*pathRadius r x y z t))

theorem pathSquare_eq (r x y z t : ℝ) :
    pathSquare r x y z t=(t*x)^2+(t*y)^2+(r+t*z)^2 := by
  unfold pathSquare speedSq
  ring

theorem pathSquare_hasDerivAt (r x y z t : ℝ) :
    HasDerivAt (pathSquare r x y z) (2*(r*z+t*speedSq x y z)) t := by
  have hh := ((hasDerivAt_const t (r^2)).add
    ((hasDerivAt_id t).const_mul (2*r*z))).add
    (((hasDerivAt_id t).pow 2).const_mul (speedSq x y z))
  convert hh using 1 <;> first | rfl | (dsimp; ring)

theorem pathSquare_eventually_pos {r : ℝ} (hr : 0 < r) (x y z : ℝ) :
    ∀ᶠ t in 𝓝 (0:ℝ), 0 < pathSquare r x y z t := by
  have hc := (pathSquare_hasDerivAt r x y z 0).continuousAt
  apply hc.eventually (eventually_gt_nhds (show 0 < pathSquare r x y z 0 by
    simp only [pathSquare, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    positivity))

theorem pathRadius_zero {r : ℝ} (hr : 0 < r) (x y z : ℝ) :
    pathRadius r x y z 0=r := by
  simp [pathRadius, pathSquare, Real.sqrt_sq hr.le]

theorem pathRadius_hasDerivAt (r x y z t : ℝ) (hp : pathSquare r x y z t ≠ 0) :
    HasDerivAt (pathRadius r x y z)
      ((r*z+t*speedSq x y z)/pathRadius r x y z t) t := by
  have hh := (pathSquare_hasDerivAt r x y z t).sqrt hp
  convert hh using 1 <;> first | rfl | (dsimp [pathRadius]; ring)

theorem path_hasDerivAt (r x y z t : ℝ) (hp : pathSquare r x y z t ≠ 0) :
    HasDerivAt (path r x y z) (pathSlope r x y z t) t := by
  have hi := (pathRadius_hasDerivAt r x y z t hp).div_const 2
  have hh := (hasDerivAt_const t (1:ℝ)).sub
    ((Real.hasDerivAt_cos (pathRadius r x y z t/2)).comp t hi)
  convert hh using 1 <;> first | rfl | (dsimp [pathSlope]; ring)

theorem path_deriv_eventually {r : ℝ} (hr : 0 < r) (x y z : ℝ) :
    deriv (path r x y z) =ᶠ[𝓝 (0:ℝ)] pathSlope r x y z := by
  filter_upwards [pathSquare_eventually_pos hr x y z] with t ht
  exact (path_hasDerivAt r x y z t ht.ne').deriv

theorem pathSlope_hasDerivAt_zero {r : ℝ} (hr : 0 < r) (x y z : ℝ) :
    HasDerivAt (pathSlope r x y z)
      (Real.sin (r/2)/(2*r)*(x^2+y^2)+Real.cos (r/2)/4*z^2) 0 := by
  have hp : pathSquare r x y z 0 ≠ 0 := by simp [pathSquare, ne_of_gt hr]
  have hd : HasDerivAt (pathRadius r x y z) z 0 := by
    simpa [pathRadius_zero hr, ne_of_gt hr] using pathRadius_hasDerivAt r x y z 0 hp
  have hn := (Real.hasDerivAt_sin (pathRadius r x y z 0/2)).comp 0 (hd.div_const 2)
  have hden := hd.const_mul 2
  have hq := hn.div hden (by rw [pathRadius_zero hr]; positivity)
  have ha := (hasDerivAt_const (0:ℝ) (r*z)).add
    ((hasDerivAt_id (0:ℝ)).mul_const (speedSq x y z))
  have hh := ha.mul hq
  change HasDerivAt (pathSlope r x y z) _ 0 at hh
  convert hh using 1
  dsimp only [Pi.mul_apply, Pi.add_apply, Pi.div_apply, Function.comp_apply, id_eq]
  simp only [pathRadius_zero hr, zero_mul, add_zero, zero_add, one_mul]
  dsimp [speedSq]
  field_simp [hr.ne']
  ring

theorem path_second_derivative {r : ℝ} (hr : 0 < r) (x y z : ℝ) :
    deriv (deriv (path r x y z)) 0=
      Real.sin (r/2)/(2*r)*(x^2+y^2)+Real.cos (r/2)/4*z^2 := by
  rw [(path_deriv_eventually hr x y z).deriv_eq]
  exact (pathSlope_hasDerivAt_zero hr x y z).deriv

theorem path_eq (r x y z t : ℝ) :
    path r x y z t=1-Real.cos (Real.sqrt ((t*x)^2+(t*y)^2+(r+t*z)^2)/2) := by
  unfold path pathRadius
  rw [pathSquare_eq]

def coordinateTensor (r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  SU2RadialCoordinateProbe.radialTensor (Real.cos (r/2)/4) (Real.sin (r/2)/(2*r))

def coordinateQuadratic (r : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, v i*coordinateTensor r i j*v j

theorem coordinateQuadratic_eq (r : ℝ) (v : Fin 3 → ℝ) :
    coordinateQuadratic r v=Real.sin (r/2)/(2*r)*((v 0)^2+(v 1)^2)+
      Real.cos (r/2)/4*(v 2)^2 := by
  norm_num [coordinateQuadratic, coordinateTensor, SU2RadialCoordinateProbe.radialTensor,
    Matrix.diagonal, Fin.sum_univ_three]
  ring

theorem path_second_derivative_tensor {r : ℝ} (hr : 0 < r) (v : Fin 3 → ℝ) :
    deriv (deriv (path r (v 0) (v 1) (v 2))) 0=coordinateQuadratic r v := by
  rw [path_second_derivative hr, coordinateQuadratic_eq]

theorem coordinateTensor_trace (r : ℝ) :
    Matrix.trace (coordinateTensor r)=Real.cos (r/2)/4+Real.sin (r/2)/r := by
  rw [coordinateTensor, SU2RadialCoordinateProbe.radialTensor_trace]
  ring

theorem coordinateTensor_decomposition (r : ℝ) :
    coordinateTensor r=
      SU2RadialCoordinateProbe.scalarCoefficient (Real.cos (r/2)/4)
        (Real.sin (r/2)/(2*r)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)+
      (Real.cos (r/2)/4-Real.sin (r/2)/(2*r)) • SU2RadialCoordinateProbe.axial := by
  exact SU2RadialCoordinateProbe.radialTensor_decomposition _ _

theorem coordinate_scalar_residual (r : ℝ) :
    SU2RadialCoordinateProbe.scalarCoefficient (Real.cos (r/2)/4)
      (Real.sin (r/2)/(2*r))-Real.sin (r/2)/(2*r)=
      (Real.cos (r/2)/4-Real.sin (r/2)/(2*r))/3 := by
  exact SU2RadialCoordinateProbe.scalar_transverse_residual _ _

end OperatorDerivativeRewrite.Foundation.SU2DirectionalCoordinateProbe
