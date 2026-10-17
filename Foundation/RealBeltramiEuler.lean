import Foundation.BeltramiAdvection

/-! Actual real coordinate derivatives for finite Fourier Beltrami fields. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RealBeltramiEuler
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality RealFiniteFourierAnalysis RealPeriodicViscousCancellation
  ABCFourierProfile BeltramiAdvection
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def realAdvection (F : RealField) (x : Space) (i : Fin 3) : ℝ :=
  ∑ j, realPartial j (fun y => F y i) x*F x j

theorem realSynthesis_mul (f g : Fourier) (hf : Hermitian f) (hg : Hermitian g)
    (x : Space) : realSynthesis (f*g) x=realSynthesis f x*realSynthesis g x := by
  simp [realSynthesis,synthesis_mul,Complex.mul_re,
    synthesis_im_zero f hf x,synthesis_im_zero g hg x]

theorem realAdvection_realize (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i))
    (x : Space) (i : Fin 3) :
    realAdvection (realizeReal u) x i=realSynthesis (advection derivative u u i) x := by
  simp only [realAdvection,realizeReal,realPartial_synthesis,advection,
    Matrix.mulVec,dotProduct,jacobian,realSynthesis_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (realSynthesis_mul _ _ (hermitian_derivative _ (hu i) j) (hu j) x).symm

theorem real_kinetic (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i)) (x : Space) :
    realSynthesis (kinetic (𝕜 := ℂ) u) x=
      (1/2 : ℝ)*∑ i, (realizeReal u x i)^2 := by
  simp [kinetic,energy,realizeReal,realSynthesis,map_sum,synthesis_mul,
    pow_two,Complex.mul_re,synthesis_im_zero _ (hu _) x]

theorem steady_euler (u : Fin 3 → Fourier) (hH : ∀ i, Hermitian (u i))
    (hu : curl derivative u=u) (x : Space) (i : Fin 3) :
    realAdvection (realizeReal u) x i+
      realPartial i (realSynthesis (-kinetic (𝕜 := ℂ) u)) x=0 := by
  rw [realAdvection_realize u hH,beltrami_advection derivative u hu,
    realPartial_synthesis]
  simp [gradient,realSynthesis]

theorem abc_real_curl (x : Space) : realCurl (realizeReal abc) x=realizeReal abc x := by
  rw [realCurl_realize,abc_curl]
  rfl

theorem abc_real_divergence (x : Space) : realDivergence (realizeReal abc) x=0 :=
  realDivergence_zero abc abc_transverse x

theorem abc_real_laplacian (x : Space) (i : Fin 3) :
    realLaplacian (fun y => realizeReal abc y i) x= -realizeReal abc x i := by
  change realLaplacian (realSynthesis (abc i)) x= -realSynthesis (abc i) x
  rw [realLaplacian_synthesis,abc_laplacian]
  simp [realSynthesis]

theorem abc_steady_euler (x : Space) (i : Fin 3) :
    realAdvection (realizeReal abc) x i+
      realPartial i (realSynthesis (-kinetic (𝕜 := ℂ) abc)) x=0 :=
  steady_euler abc abc_hermitian abc_curl x i

theorem abc_periodic (x : Space) (i j : Fin 3) :
    Function.Periodic (fun r => realizeReal abc (Function.update x j r) i) (2*Real.pi) :=
  real_component_periodic abc x i j

end OperatorDerivativeRewrite.Foundation.RealBeltramiEuler
