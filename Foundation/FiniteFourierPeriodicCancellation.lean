import Foundation.FiniteFourierTorusAverage

/-! Actual derivative and torus-integral cancellation for complex finite
Fourier vector fields. Contractions are bilinear, extending the real formulas. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteFourierPeriodicCancellation
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

abbrev Field := Space → Fin 3 → ℂ
def realize (u : Fin 3 → Fourier) : Field := fun x i => synthesis x (u i)
def vectorCurl (F : Field) (x : Space) : Fin 3 → ℂ :=
  ![coordinateDerivative 1 (fun y => F y 2) x-coordinateDerivative 2 (fun y => F y 1) x,
    coordinateDerivative 2 (fun y => F y 0) x-coordinateDerivative 0 (fun y => F y 2) x,
    coordinateDerivative 0 (fun y => F y 1) x-coordinateDerivative 1 (fun y => F y 0) x]
def vectorDivergence (F : Field) (x : Space) : ℂ :=
  ∑ i, coordinateDerivative i (fun y => F y i) x
def symmetricGradient (F : Field) (x : Space) (i j : Fin 3) : ℂ :=
  (1/2 : ℂ)*(coordinateDerivative j (fun y => F y i) x+
    coordinateDerivative i (fun y => F y j) x)
def scalarLaplacian (f : Space → ℂ) (x : Space) : ℂ :=
  ∑ k, coordinateDerivative k (coordinateDerivative k f) x

def millerIntegrand (F : Field) (x : Space) : ℂ :=
  ∑ i, ∑ j, vectorCurl F x i*scalarLaplacian (fun y => symmetricGradient F y i j) x*vectorCurl F x j
def crossIntegrand (F : Field) (x : Space) : ℂ :=
  ∑ k, ∑ i, ∑ j, coordinateDerivative k (fun y => vectorCurl F y i) x*
    coordinateDerivative k (fun y => symmetricGradient F y i j) x*vectorCurl F x j

theorem derivative_synthesis_function (j : Fin 3) (f : Fourier) :
    coordinateDerivative j (fun x => synthesis x f)=fun x => synthesis x (derivative j f) :=
  funext (fun x => partial_synthesis f x j)

theorem curl_realize (u : Fin 3 → Fourier) (x : Space) :
    vectorCurl (realize u) x=fun i => synthesis x (curl derivative u i) := by
  ext i
  fin_cases i <;> simp [vectorCurl,realize,partial_synthesis,curl,axis,jacobian]

theorem curl_realize_function (u : Fin 3 → Fourier) (i : Fin 3) :
    (fun x => vectorCurl (realize u) x i)=fun x => synthesis x (curl derivative u i) := by
  funext x
  exact congrFun (curl_realize u x) i

theorem strain_realize (u : Fin 3 → Fourier) (x : Space) (i j : Fin 3) :
    symmetricGradient (realize u) x i j=synthesis x (strain derivative u i j) := by
  simp [symmetricGradient,realize,partial_synthesis,strain,twiceStrain,smul_eq_mul] <;> ring

theorem strain_realize_function (u : Fin 3 → Fourier) (i j : Fin 3) :
    (fun x => symmetricGradient (realize u) x i j)=fun x => synthesis x (strain derivative u i j) :=
  funext (fun x => strain_realize u x i j)

theorem laplacian_synthesis (f : Fourier) (x : Space) :
    scalarLaplacian (fun y => synthesis y f) x=synthesis x (lap derivative f) := by
  unfold scalarLaplacian
  simp_rw [derivative_synthesis_function]
  simp only [lap,map_sum]

theorem divergence_realize_zero (u : Fin 3 → Fourier)
    (hu : ∀ k : Wave, ∑ i, (k i : ℂ)*(u i).coeff k=0) (x : Space) :
    vectorDivergence (realize u) x=0 := by
  simp only [vectorDivergence,realize,partial_synthesis]
  rw [← map_sum]
  change synthesis x (divergence derivative u)=0
  rw [transverse_divergence_zero u hu,map_zero]

theorem miller_integrand_synthesis (u : Fin 3 → Fourier) (x : Space) :
    millerIntegrand (realize u) x=synthesis x
      (∑ i, ∑ j, curl derivative u i*lap derivative (strain derivative u i j)*curl derivative u j) := by
  simp only [millerIntegrand,curl_realize,strain_realize_function,laplacian_synthesis,
    map_sum,synthesis_mul]

theorem cross_integrand_synthesis (u : Fin 3 → Fourier) (x : Space) :
    crossIntegrand (realize u) x=synthesis x
      (crossContraction derivative (curl derivative u) (strain derivative u)) := by
  simp only [crossIntegrand,curl_realize_function,strain_realize_function,partial_synthesis,
    curl_realize,crossContraction,map_sum,synthesis_mul]

theorem periodic_miller_zero (u : Fin 3 → Fourier)
    (hu : ∀ k : Wave, ∑ i, (k i : ℂ)*(u i).coeff k=0) :
    boxAverage (millerIntegrand (realize u))=0 := by
  have he : millerIntegrand (realize u)=fun x => synthesis x
      (∑ i, ∑ j, curl derivative u i*lap derivative (strain derivative u i j)*curl derivative u j) :=
    funext (miller_integrand_synthesis u)
  rw [he,boxAverage_synthesis]
  exact fourier_miller_zero u hu

theorem periodic_cross_zero (u : Fin 3 → Fourier)
    (hu : ∀ k : Wave, ∑ i, (k i : ℂ)*(u i).coeff k=0) :
    boxAverage (crossIntegrand (realize u))=0 := by
  have he : crossIntegrand (realize u)=fun x => synthesis x
      (crossContraction derivative (curl derivative u) (strain derivative u)) :=
    funext (cross_integrand_synthesis u)
  rw [he,boxAverage_synthesis]
  exact fourier_cross_zero u hu

end OperatorDerivativeRewrite.Foundation.FiniteFourierPeriodicCancellation
