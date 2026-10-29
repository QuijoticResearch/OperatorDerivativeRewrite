import Foundation.FourCubeCubicCoordinates

/-! Volume-preserving color reflections of the actual centered pinned quadratic density. -/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeColorReflection
open FourCubeMovingOddAction FourCubeHaarQuadraticLimit FourCubeHaarLaplaceDensity
open FourCubeMovingSchurLimit FourCubeMovingLaplaceLimit FourCubeHemisphereCoercivity

abbrev Signs := Bool × Bool × Bool

def signAt (s : Signs) : Fin 3 → Bool := ![s.1,s.2.1,s.2.2]
def reflect (s : Signs) (Y : Coordinates) : Coordinates :=
  fun e a => if signAt s a then -Y e a else Y e a

def affine (s : Signs) (h Y : Coordinates) : Coordinates := h+reflect s (Y-h)

theorem reflect_preserving (s : Signs) : MeasurePreserving (reflect s) := by
  have hi : MeasurePreserving (fun u : SU2GaussianConeCoordinates.Triple =>
      (fun a : Fin 3 => if signAt s a then -u a else u a)) := by
    apply volume_preserving_pi (f := fun a (r : ℝ) => if signAt s a then -r else r)
    intro a
    cases hs : signAt s a
    · convert! (MeasurePreserving.id (volume : Measure ℝ)) using 1 <;> simp [hs]
    · convert! (Measure.measurePreserving_neg (volume : Measure ℝ)) using 1 <;> simp [hs]
  have hh := volume_preserving_pi (f := fun (_ : OneSidedPinnedInterior.Free)
    (u : SU2GaussianConeCoordinates.Triple) => (fun a : Fin 3 => if signAt s a then -u a else u a))
    (fun _ => hi)
  exact hh

theorem reflect_continuous (s : Signs) : Continuous (reflect s) := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro a
  unfold reflect
  cases hs : signAt s a <;> simp only [hs,Bool.false_eq_true,↓reduceIte] <;> fun_prop

theorem reflect_involutive (s : Signs) (Y : Coordinates) : reflect s (reflect s Y)=Y := by
  ext e a
  simp only [reflect]
  cases hs : signAt s a <;> simp [hs]

theorem affine_involutive (s : Signs) (h Y : Coordinates) : affine s h (affine s h Y)=Y := by
  have he : affine s h Y-h=reflect s (Y-h) := by unfold affine; abel
  rw [affine,he,reflect_involutive]
  abel

theorem affine_continuous (s : Signs) (h : Coordinates) : Continuous (affine s h) :=
  continuous_const.add ((reflect_continuous s).comp (continuous_id.sub continuous_const))

def affineHomeomorph (s : Signs) (h : Coordinates) : Coordinates ≃ₜ Coordinates where
  toFun := affine s h
  invFun := affine s h
  left_inv := affine_involutive s h
  right_inv := affine_involutive s h
  continuous_toFun := affine_continuous s h
  continuous_invFun := affine_continuous s h

theorem affine_preserving (s : Signs) (h : Coordinates) : MeasurePreserving (affine s h) := by
  have hsub : MeasurePreserving (fun Y : Coordinates => Y-h) := by
    convert! measurePreserving_add_right (volume : Measure Coordinates) (-h) using 1
  exact (measurePreserving_add_left (volume : Measure Coordinates) h).comp
    ((reflect_preserving s).comp hsub)

theorem quadraticForm_reflect (s : Signs) (Y : Coordinates) : quadraticForm (reflect s Y)=quadraticForm Y := by
  unfold quadraticForm
  apply Finset.sum_congr rfl
  intro a _
  cases hs : signAt s a
  · simp [reflect,hs]
  · have he : (fun e => reflect s Y e a)= -(fun e => Y e a) := by ext e; simp [reflect,hs]
    rw [he,Matrix.mulVec_neg,neg_dotProduct,dotProduct_neg,neg_neg]

theorem gaussianDensity_reflect (s : Signs) (Y : Coordinates) :
    gaussianDensity (reflect s Y)=gaussianDensity Y := by
  rw [gaussianDensity,gaussianDensity,quadraticForm_reflect]

theorem limitingDensity_affine (s : Signs) (x y z : ℝ) (Y : Coordinates) :
    limitingDensity x y z (affine s (harmonicShift x y z) Y)=limitingDensity x y z Y := by
  have he : affine s (harmonicShift x y z) Y-harmonicShift x y z=
      reflect s (Y-harmonicShift x y z) := by unfold affine; abel
  rw [limitingDensity_translate,limitingDensity_translate,he,gaussianDensity_reflect]

theorem integral_affine (s : Signs) (h : Coordinates) (f : Coordinates → ℝ) :
    (∫ Y : Coordinates,f (affine s h Y))=∫ Y : Coordinates,f Y :=
  (affine_preserving s h).integral_comp (affineHomeomorph s h).measurableEmbedding f

end OperatorDerivativeRewrite.Foundation.FourCubeColorReflection
