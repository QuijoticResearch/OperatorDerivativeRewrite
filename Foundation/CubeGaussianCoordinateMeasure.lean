import Foundation.CubeGaussianKernelChannels
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Genuine Lebesgue scaling for the actual five-triple Gaussian coordinates. -/
noncomputable section
open MeasureTheory
open scoped Matrix
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianCoordinateMeasure
open CubeGaussianModes CubeChartAction

private def basisQ : Matrix (Fin 5) (Fin 5) ℚ :=
  !![-1,1/2,0,1,1/2;1,1/2,0,1,-1/2;0,1,0,0,1;0,0,1,0,-1;0,0,1,0,1]

private theorem basisQ_det : basisQ.det = -4 := by decide +kernel

theorem basis_det : basis.det = -4 := by
  have hb : basis=basisQ.map (Rat.castHom ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [basis,basisQ]
  rw [hb]
  have h := congrArg (Rat.castHom ℝ) basisQ_det
  rw [(Rat.castHom ℝ).map_det] at h
  simpa using h

def colorSwap : Boundary ≃ₗ[ℝ] (Fin 3 → Fin 5 → ℝ) where
  toFun X a i := X i a
  invFun X i a := X a i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def colorOperator : (Fin 3 → Fin 5 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 5 → ℝ) :=
  LinearMap.pi (fun a => (Matrix.toLin' basis).comp (LinearMap.proj a))

def synthesisLinear : Boundary →ₗ[ℝ] Boundary :=
  colorSwap.symm.toLinearMap.comp (colorOperator.comp colorSwap.toLinearMap)

theorem synthesisLinear_apply (X : Boundary) : synthesisLinear X=synthesis X := by
  funext i a
  simp [synthesisLinear,colorOperator,colorSwap,synthesis,Matrix.toLin'_apply,
    Matrix.mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem synthesisLinear_det : synthesisLinear.det = -64 := by
  have hd : synthesisLinear.det=colorOperator.det := by
    exact LinearMap.det_conj colorOperator colorSwap.symm
  rw [hd]
  unfold colorOperator
  rw [LinearMap.det_pi]
  simp only [LinearMap.det_toLin',basis_det]
  norm_num

theorem synthesis_continuous : Continuous synthesis := by
  have he : (synthesisLinear : Boundary → Boundary)=synthesis :=
    funext synthesisLinear_apply
  rw [← he]
  exact synthesisLinear.continuous_of_finiteDimensional

theorem synthesis_map : Measure.map synthesis (volume : Measure Boundary)=
    (1/64 : ENNReal) • (volume : Measure Boundary) := by
  have hn : synthesisLinear.det ≠ 0 := by rw [synthesisLinear_det]; norm_num
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure Boundary) hn
  have he : (synthesisLinear : Boundary → Boundary)=synthesis :=
    funext synthesisLinear_apply
  rw [he,synthesisLinear_det] at h
  norm_num at h ⊢
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<64)] at h
  exact h

theorem synthesis_integral (f : Boundary → ℝ) (hf : Measurable f) :
    (∫ X : Boundary,f X)=64*(∫ x : Boundary,f (synthesis x)) := by
  have h := integral_map (μ := (volume : Measure Boundary))
    synthesis_continuous.measurable.aemeasurable
    hf.aestronglyMeasurable
  rw [synthesis_map,integral_smul_measure] at h
  norm_num at h
  change (∫ X : Boundary,f X)=64*(∫ x : Boundary,f (synthesis x))
  linarith

theorem synthesis_integrable_iff (f : Boundary → ℝ) (hf : Measurable f) :
    Integrable (fun x => f (synthesis x)) ↔ Integrable f := by
  have h := integrable_map_measure (μ := (volume : Measure Boundary))
    hf.aestronglyMeasurable synthesis_continuous.measurable.aemeasurable
  rw [synthesis_map,integrable_smul_measure (by norm_num : (1/64:ENNReal)≠0)
    (by norm_num : (1/64:ENNReal)≠∞)] at h
  exact h.symm

end OperatorDerivativeRewrite.Foundation.CubeGaussianCoordinateMeasure
