import Foundation.FourCubeFullQuadraticCenter

/-! Full32 raw-color reflections preserve the actual limiting quadratic density.
Pointwise cubic averaging is proved here; unbounded integral domains are separate obligations. -/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullColorSymmetry
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedSourceRows
open FourCubeFullChartOdd FourCubeFullChartQuadratic FourCubeFullQuadraticCenter
open FourCubeFullHaarGaussianLimit SU2QuaternionOddWord
open FourCubeColorReflection (Signs signAt)
open FourCubeCubicSignAverage (colorMix)

attribute [local irreducible] edges innerFaces upperFaces

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
  have hh := volume_preserving_pi (f := fun (_ : OneSidedBlockRank.Interior)
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

private theorem quadratic_neg (f : Field) :
    FourCubeCompletedGram.quadratic (-f)=FourCubeCompletedGram.quadratic f := by
  simp only [← FourCubeCompletedGram.gram_energy,Matrix.mulVec_neg,neg_dotProduct,dotProduct_neg,neg_neg]

theorem fluctuation_reflect (s : Signs) (Y : Coordinates) : fluctuation (reflect s Y)=fluctuation Y := by
  unfold fluctuation
  apply Finset.sum_congr rfl
  intro a ha
  cases hs : signAt s a
  · have he : interiorColor (reflect s Y) a=interiorColor Y a := by
      ext e
      simp [interiorColor,reflect,hs]
    rw [he]
  · have he : interiorColor (reflect s Y) a= -interiorColor Y a := by
      ext e
      simp [interiorColor,reflect,hs]
    rw [he,quadratic_neg]

theorem quadratic_affine (s : Signs) (x y z : ℝ) (Y : Coordinates) :
    completedQuadratic (affine s (center x y z) Y) x y z=completedQuadratic Y x y z := by
  have he : affine s (center x y z) Y-center x y z=reflect s (Y-center x y z) := by
    unfold affine
    abel
  rw [centered_energy (affine s (center x y z) Y),centered_energy Y,he,fluctuation_reflect]

theorem gaussianDensity_affine (s : Signs) (x y z : ℝ) (Y : Coordinates) :
    gaussianDensity x y z (affine s (center x y z) Y)=gaussianDensity x y z Y := by
  rw [gaussianDensity,gaussianDensity,quadratic_affine]

theorem integral_affine (s : Signs) (h : Coordinates) (f : Coordinates → ℝ) :
    (∫ Y : Coordinates,f (affine s h Y))=∫ Y : Coordinates,f Y :=
  (affine_preserving s h).integral_comp (affineHomeomorph s h).measurableEmbedding f

theorem rawVelocity_affine (s : Signs) (h Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    rawVelocity (affine s h Y) x y z e=colorMix s (rawVelocity h x y z e)
      (rawVelocity Y x y z e-rawVelocity h x y z e) := by
  ext a
  cases e with
  | inl e => rfl
  | inr c => simp [rawVelocity,colorMix]

theorem vectors_affine (s : Signs) (h Y : Coordinates) (x y z : ℝ) (p : FullFace) :
    vectors (affine s h Y) x y z p=(fun i => colorMix s (vectors h x y z p i)
      (vectors Y x y z p i-vectors h x y z p i)) := by
  funext i a
  fin_cases i
  · exact congrFun (rawVelocity_affine s h Y x y z _) a
  · exact congrFun (rawVelocity_affine s h Y x y z _) a
  · change (-rawVelocity (affine s h Y) x y z (OneSidedSourceRows.rowEdges p 2)) a=_
    rw [rawVelocity_affine]
    simp only [vectors,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,
      colorMix,Pi.neg_apply,Pi.sub_apply]
    cases hs : signAt s a <;> simp [hs] <;> ring
  · change (-rawVelocity (affine s h Y) x y z (OneSidedSourceRows.rowEdges p 3)) a=_
    rw [rawVelocity_affine]
    simp only [vectors,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,
      colorMix,Pi.neg_apply,Pi.sub_apply]
    cases hs : signAt s a <;> simp [hs] <;> ring

theorem actual_cubic_sign_sum (h Y : Coordinates) (x y z : ℝ) :
    (∑ s : Signs,cubicCoefficient (affine s h Y) x y z)=8*cubicCoefficient h x y z := by
  unfold cubicCoefficient
  rw [Finset.sum_comm]
  have he (p : FullFace) : (∑ s : Signs,cubic (vectors (affine s h Y) x y z p))=
      8*cubic (vectors h x y z p) := by
    simp_rw [vectors_affine]
    exact FourCubeCubicSignAverage.cubic_sign_sum _ _
  simp_rw [he]
  rw [Finset.mul_sum]


theorem weighted_cubic_sign_sum (x y z : ℝ) (Y : Coordinates) :
    (∑ s : Signs,cubicCoefficient (affine s (center x y z) Y) x y z*
      gaussianDensity x y z (affine s (center x y z) Y))=
      (8*cubicCoefficient (center x y z) x y z)*gaussianDensity x y z Y := by
  simp_rw [gaussianDensity_affine]
  rw [← Finset.sum_mul,actual_cubic_sign_sum]

theorem unit_center_cubic : cubicCoefficient (center 1 1 1) 1 1 1=(1784975 : ℝ)/2750517 := by
  rw [center_unit]
  exact FourCubeCompletedCubic.coefficient_value

theorem center_velocity_scale (x y z : ℝ) (e : FullEdge) (a : Fin 3) :
    rawVelocity (center x y z) x y z e a=FourCubeHarmonicAmplitude.amplitude x y z a*
      rawVelocity (center 1 1 1) 1 1 1 e a := by
  cases e with
  | inl e =>
    fin_cases a <;> simp [rawVelocity,FourCubeFullQuadraticCenter.center,FourCubeHarmonicAmplitude.amplitude]
  | inr c => exact FourCubeHarmonicAmplitude.raw_boundary_scale x y z c a

theorem center_vectors_scale (x y z : ℝ) (p : FullFace) :
    vectors (center x y z) x y z p=(fun i a => FourCubeHarmonicAmplitude.amplitude x y z a*
      vectors (center 1 1 1) 1 1 1 p i a) := by
  funext i a
  fin_cases i
  · exact center_velocity_scale x y z _ a
  · exact center_velocity_scale x y z _ a
  · change -rawVelocity (center x y z) x y z (rowEdges p 2) a=
      FourCubeHarmonicAmplitude.amplitude x y z a*(-rawVelocity (center 1 1 1) 1 1 1 (rowEdges p 2) a)
    rw [center_velocity_scale]
    ring
  · change -rawVelocity (center x y z) x y z (rowEdges p 3) a=
      FourCubeHarmonicAmplitude.amplitude x y z a*(-rawVelocity (center 1 1 1) 1 1 1 (rowEdges p 3) a)
    rw [center_velocity_scale]
    ring

theorem center_cubic_amplitudes (x y z : ℝ) :
    cubicCoefficient (center x y z) x y z=((1784975 : ℝ)/2750517)*x*y*z := by
  unfold cubicCoefficient
  simp_rw [center_vectors_scale x y z,FourCubeHarmonicAmplitude.cubic_scale]
  rw [← Finset.mul_sum]
  change x*y*z*cubicCoefficient (center 1 1 1) 1 1 1=_
  rw [unit_center_cubic]
  ring

end OperatorDerivativeRewrite.Foundation.FourCubeFullColorSymmetry
