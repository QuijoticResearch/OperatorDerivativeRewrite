import Foundation.RealBeltramiEuler

/-! An explicit real periodic decaying Navier–Stokes solution, with ordinary
space and time derivatives. This is a smooth-flow calibration, not blow-up. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.ABCNavierStokesFlow
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality RealFiniteFourierAnalysis RealPeriodicViscousCancellation
  ABCFourierProfile BeltramiAdvection RealBeltramiEuler
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def amplitude (nu t : ℝ) : ℝ := Real.exp (-nu*t)
def state (nu t : ℝ) (i : Fin 3) : Fourier := (amplitude nu t : ℂ) • abc i
def velocity (nu t : ℝ) : RealField := realizeReal (state nu t)
def pressure (nu t : ℝ) : Space → ℝ :=
  realSynthesis (-kinetic (𝕜 := ℂ) (state nu t))

theorem state_hermitian (nu t : ℝ) (i : Fin 3) : Hermitian (state nu t i) :=
  hermitian_real_smul (amplitude nu t) _ (abc_hermitian i)

theorem state_curl (nu t : ℝ) : curl derivative (state nu t)=state nu t := by
  have hs : curl derivative (state nu t)=
      fun i => (amplitude nu t : ℂ) • curl derivative abc i := by
    ext i
    fin_cases i <;> simp [curl,axis,jacobian,state,Derivation.map_smul,smul_sub]
  rw [abc_curl] at hs
  exact hs

theorem state_laplacian (nu t : ℝ) (i : Fin 3) :
    lap derivative (state nu t i)= -state nu t i := by
  unfold state
  rw [lap_smul,abc_laplacian,smul_neg]

theorem state_transverse (nu t : ℝ) (k : Wave) :
    ∑ i, (k i : ℂ)*(state nu t i).coeff k=0 := by
  simp only [state,AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,smul_eq_mul]
  have h := congrArg (fun z : ℂ => (amplitude nu t : ℂ)*z) (abc_transverse k)
  simpa only [Finset.mul_sum,mul_zero,mul_left_comm] using h

theorem velocity_formula (nu t : ℝ) (x : Space) (i : Fin 3) :
    velocity nu t x i=amplitude nu t*realizeReal abc x i := by
  simp [velocity,realizeReal,state,realSynthesis,Complex.mul_re]

theorem amplitude_derivative (nu t : ℝ) :
    HasDerivAt (amplitude nu) (-nu*amplitude nu t) t := by
  change HasDerivAt (fun s => Real.exp (-nu*s)) (-nu*Real.exp (-nu*t)) t
  simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-nu)).exp

theorem velocity_time_derivative (nu t : ℝ) (x : Space) (i : Fin 3) :
    deriv (fun s => velocity nu s x i) t= -nu*velocity nu t x i := by
  have h := (amplitude_derivative nu t).mul_const (realizeReal abc x i)
  have he : (fun s => velocity nu s x i)=
      (fun s => amplitude nu s*realizeReal abc x i) :=
    funext (fun s => velocity_formula nu s x i)
  rw [he,h.deriv,velocity_formula]
  ring

theorem velocity_laplacian (nu t : ℝ) (x : Space) (i : Fin 3) :
    realLaplacian (fun y => velocity nu t y i) x= -velocity nu t x i := by
  change realLaplacian (realSynthesis (state nu t i)) x=
    -realSynthesis (state nu t i) x
  rw [realLaplacian_synthesis,state_laplacian]
  simp [realSynthesis]

theorem momentum (nu t : ℝ) (x : Space) (i : Fin 3) :
    deriv (fun s => velocity nu s x i) t+realAdvection (velocity nu t) x i+
      realPartial i (pressure nu t) x=
      nu*realLaplacian (fun y => velocity nu t y i) x := by
  have h := steady_euler (state nu t) (state_hermitian nu t) (state_curl nu t) x i
  change realAdvection (velocity nu t) x i+realPartial i (pressure nu t) x=0 at h
  rw [velocity_time_derivative,velocity_laplacian]
  linarith

theorem incompressible (nu t : ℝ) (x : Space) : realDivergence (velocity nu t) x=0 :=
  realDivergence_zero (state nu t) (state_transverse nu t) x

theorem periodic (nu t : ℝ) (x : Space) (i j : Fin 3) :
    Function.Periodic (fun r => velocity nu t (Function.update x j r) i) (2*Real.pi) :=
  real_component_periodic (state nu t) x i j

theorem amplitude_positive (nu t : ℝ) : 0<amplitude nu t := Real.exp_pos _

end OperatorDerivativeRewrite.Foundation.ABCNavierStokesFlow
