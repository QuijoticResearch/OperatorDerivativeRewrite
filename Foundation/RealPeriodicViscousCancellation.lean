import Foundation.RealFiniteFourierAnalysis

/-! Both periodic viscous cancellations for actual real finite Fourier
fields, with real coordinate derivatives and real interval averages. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RealPeriodicViscousCancellation
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality RealFiniteFourierAnalysis
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

abbrev RealField := Space → Fin 3 → ℝ
def realizeReal (u : Fin 3 → Fourier) : RealField := fun x i => realSynthesis (u i) x
def realCurl (F : RealField) (x : Space) : Fin 3 → ℝ :=
  ![realPartial 1 (fun y => F y 2) x-realPartial 2 (fun y => F y 1) x,
    realPartial 2 (fun y => F y 0) x-realPartial 0 (fun y => F y 2) x,
    realPartial 0 (fun y => F y 1) x-realPartial 1 (fun y => F y 0) x]
def realDivergence (F : RealField) (x : Space) : ℝ := ∑ i, realPartial i (fun y => F y i) x
def realStrain (F : RealField) (x : Space) (i j : Fin 3) : ℝ :=
  (1/2 : ℝ)*(realPartial j (fun y => F y i) x+realPartial i (fun y => F y j) x)
def realLaplacian (f : Space → ℝ) (x : Space) : ℝ := ∑ k, realPartial k (realPartial k f) x
def realMillerIntegrand (F : RealField) (x : Space) : ℝ :=
  ∑ i, ∑ j, realCurl F x i*realLaplacian (fun y => realStrain F y i j) x*realCurl F x j
def realCrossIntegrand (F : RealField) (x : Space) : ℝ :=
  ∑ k, ∑ i, ∑ j, realPartial k (fun y => realCurl F y i) x*
    realPartial k (fun y => realStrain F y i j) x*realCurl F x j

theorem realCurl_realize (u : Fin 3 → Fourier) (x : Space) :
    realCurl (realizeReal u) x=fun i => realSynthesis (curl derivative u i) x := by
  ext i
  fin_cases i <;> simp only [realCurl,realizeReal,realPartial_synthesis] <;>
    simp [realSynthesis,curl,axis,jacobian]

theorem realCurl_function (u : Fin 3 → Fourier) (i : Fin 3) :
    (fun x => realCurl (realizeReal u) x i)=realSynthesis (curl derivative u i) :=
  funext (fun x => congrFun (realCurl_realize u x) i)

theorem realStrain_realize (u : Fin 3 → Fourier) (x : Space) (i j : Fin 3) :
    realStrain (realizeReal u) x i j=realSynthesis (strain derivative u i j) x := by
  simp only [realStrain,realizeReal,realPartial_synthesis]
  simp [realSynthesis,strain,twiceStrain,
    smul_eq_mul,Complex.mul_re] <;> ring

theorem realStrain_function (u : Fin 3 → Fourier) (i j : Fin 3) :
    (fun x => realStrain (realizeReal u) x i j)=realSynthesis (strain derivative u i j) :=
  funext (fun x => realStrain_realize u x i j)

theorem realLaplacian_synthesis (f : Fourier) (x : Space) :
    realLaplacian (realSynthesis f) x=realSynthesis (lap derivative f) x := by
  unfold realLaplacian
  simp_rw [realPartial_synthesis_function]
  simp [lap,realSynthesis,map_sum]

theorem realDivergence_zero (u : Fin 3 → Fourier)
    (hu : ∀ k : Wave, ∑ i, (k i : ℂ)*(u i).coeff k=0) (x : Space) :
    realDivergence (realizeReal u) x=0 := by
  simp only [realDivergence,realizeReal,realPartial_synthesis]
  rw [← realSynthesis_sum]
  change realSynthesis (divergence derivative u) x=0
  rw [transverse_divergence_zero u hu]
  simp [realSynthesis]

theorem realMiller_synthesis (u : Fin 3 → Fourier) (hH : ∀ i, Hermitian (u i)) (x : Space) :
    realMillerIntegrand (realizeReal u) x=realSynthesis
      (∑ i, ∑ j, curl derivative u i*lap derivative (strain derivative u i j)*curl derivative u j) x := by
  simp only [realMillerIntegrand,realCurl_realize,realStrain_function,realLaplacian_synthesis,
    realSynthesis_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact realSynthesis_product _ _ _ (hermitian_curl u hH i)
    (hermitian_laplacian _ (hermitian_strain u hH i j)) (hermitian_curl u hH j) x

theorem realCross_synthesis (u : Fin 3 → Fourier) (hH : ∀ i, Hermitian (u i)) (x : Space) :
    realCrossIntegrand (realizeReal u) x=realSynthesis
      (crossContraction derivative (curl derivative u) (strain derivative u)) x := by
  simp only [realCrossIntegrand,realCurl_function,realStrain_function,realPartial_synthesis,
    realCurl_realize,crossContraction,realSynthesis_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact realSynthesis_product _ _ _
    (hermitian_derivative _ (hermitian_curl u hH i) k)
    (hermitian_derivative _ (hermitian_strain u hH i j) k) (hermitian_curl u hH j) x

theorem real_periodic_miller_zero (u : Fin 3 → Fourier) (hH : ∀ i, Hermitian (u i))
    (hu : ∀ k : Wave, ∑ i, (k i : ℂ)*(u i).coeff k=0) :
    realBoxAverage (realMillerIntegrand (realizeReal u))=0 := by
  have he : realMillerIntegrand (realizeReal u)=realSynthesis
      (∑ i, ∑ j, curl derivative u i*lap derivative (strain derivative u i j)*curl derivative u j) :=
    funext (realMiller_synthesis u hH)
  rw [he,realBoxAverage_synthesis,fourier_miller_zero u hu]
  rfl

theorem real_periodic_cross_zero (u : Fin 3 → Fourier) (hH : ∀ i, Hermitian (u i))
    (hu : ∀ k : Wave, ∑ i, (k i : ℂ)*(u i).coeff k=0) :
    realBoxAverage (realCrossIntegrand (realizeReal u))=0 := by
  have he : realCrossIntegrand (realizeReal u)=realSynthesis
      (crossContraction derivative (curl derivative u) (strain derivative u)) :=
    funext (realCross_synthesis u hH)
  rw [he,realBoxAverage_synthesis,fourier_cross_zero u hu]
  rfl

theorem real_component_periodic (u : Fin 3 → Fourier) (x : Space) (i j : Fin 3) :
    Function.Periodic (fun r => realizeReal u (Function.update x j r) i) (2*Real.pi) := by
  intro r
  exact congrArg Complex.re (synthesis_coordinate_periodic (u i) x j r)

theorem real_component_continuous (u : Fin 3 → Fourier) (i : Fin 3) :
    Continuous (fun x => realizeReal u x i) := by
  exact Complex.continuous_re.comp (synthesis_continuous (u i))

theorem real_component_coercion (u : Fin 3 → Fourier) (hH : ∀ i, Hermitian (u i))
    (x : Space) (i : Fin 3) : (realizeReal u x i : ℂ)=synthesis x (u i) :=
  ofReal_synthesis_re (u i) (hH i) x

end OperatorDerivativeRewrite.Foundation.RealPeriodicViscousCancellation
