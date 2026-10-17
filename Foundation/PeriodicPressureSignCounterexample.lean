import Foundation.BeltramiViscousTrace

/-! A smooth periodic positive-viscosity test of the normalized plus-pressure
stretching balance. No regularity or Millennium equivalence claim is made. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicPressureSignCounterexample
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality RealFiniteFourierAnalysis RealPeriodicViscousCancellation
  ABCFourierProfile BeltramiAdvection RealBeltramiEuler ABCNavierStokesFlow ABCTraceMeans
  RealBeltramiMeans BeltramiViscousTrace
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem profile_smooth (i : Fin 3) : ContDiff ℝ ⊤ (fun x : Space => realizeReal abc x i) := by
  fin_cases i
  · simpa [abc_realization] using!
      ((contDiff_apply ℝ ℝ (2 : Fin 3)).sin.add (contDiff_apply ℝ ℝ (1 : Fin 3)).cos)
  · simpa [abc_realization] using!
      ((contDiff_apply ℝ ℝ (0 : Fin 3)).sin.add (contDiff_apply ℝ ℝ (2 : Fin 3)).cos)
  · simpa [abc_realization] using!
      ((contDiff_apply ℝ ℝ (1 : Fin 3)).sin.add (contDiff_apply ℝ ℝ (0 : Fin 3)).cos)

theorem velocity_smooth (nu : ℝ) (i : Fin 3) :
    ContDiff ℝ ⊤ (fun z : ℝ × Space => velocity nu z.1 z.2 i) := by
  have ha : ContDiff ℝ ⊤ (fun z : ℝ × Space => amplitude nu z.1) := by
    have h : ContDiff ℝ ⊤ (fun z : ℝ × Space => -nu*z.1) :=
      contDiff_const.mul contDiff_fst
    simpa only [amplitude] using h.exp
  have he : (fun z : ℝ × Space => velocity nu z.1 z.2 i)=
      (fun z => amplitude nu z.1*realizeReal abc z.2 i) :=
    funext (fun z => velocity_formula nu z.1 z.2 i)
  rw [he]
  exact ha.mul ((profile_smooth i).comp contDiff_snd)

theorem pressure_formula (nu t : ℝ) (x : Space) :
    pressure nu t x= -(1/2 : ℝ)*∑ i, (velocity nu t x i)^2 := by
  have hn (f : Fourier) : realSynthesis (-f) x= -realSynthesis f x := by
    simp [realSynthesis]
  unfold pressure
  rw [hn,real_kinetic (state nu t) (state_hermitian nu t)]
  change -(1/2*(∑ i, (velocity nu t x i)^2))= _
  ring

theorem pressure_smooth (nu : ℝ) :
    ContDiff ℝ ⊤ (fun z : ℝ × Space => pressure nu z.1 z.2) := by
  have he : (fun z : ℝ × Space => pressure nu z.1 z.2)=
      (fun z => -(1/2 : ℝ)*∑ i, (velocity nu z.1 z.2 i)^2) :=
    funext (fun z => pressure_formula nu z.1 z.2)
  rw [he]
  have hs : ContDiff ℝ ⊤ (fun z : ℝ × Space => ∑ i, (velocity nu z.1 z.2 i)^2) :=
    ContDiff.sum (fun i _ => (velocity_smooth nu i).pow 2)
  exact contDiff_const.mul hs

theorem pressure_periodic (nu t : ℝ) (x : Space) (j : Fin 3) :
    Function.Periodic (fun r => pressure nu t (Function.update x j r)) (2*Real.pi) := by
  intro r
  exact congrArg Complex.re (synthesis_coordinate_periodic
    (-kinetic (𝕜 := ℂ) (state nu t)) x j r)

theorem initial_state (nu : ℝ) : state nu 0=abc := by
  funext i
  simp [state,amplitude]

theorem initial_velocity (nu : ℝ) : velocity nu 0=realizeReal abc := by
  unfold velocity
  rw [initial_state]

theorem initial_pressure (nu : ℝ) : pressure nu 0=realSynthesis (-kinetic (𝕜 := ℂ) abc) := by
  unfold pressure
  rw [initial_state]

def plusPressureRHS (nu t : ℝ) : ℝ :=
  realBoxAverage (realAmplification (velocity nu t))+
    realBoxAverage (realPressureContraction (velocity nu t) (pressure nu t))-
      2*nu*realBoxAverage (realViscous (velocity nu t))

theorem plusPressureRHS_initial (nu : ℝ) : plusPressureRHS nu 0=3 := by
  rw [plusPressureRHS,initial_velocity,initial_pressure,abc_amplification_mean,
    abc_pressure_mean,abc_viscous_mean]
  ring

theorem plus_pressure_balance_fails (nu : ℝ) :
    deriv (fun s => realBoxAverage (realStretching (velocity nu s))) 0≠plusPressureRHS nu 0 := by
  rw [flow_stretching_mean_derivative,plusPressureRHS_initial]
  norm_num

theorem minus_pressure_initial (nu : ℝ) :
    realBoxAverage (realAmplification (velocity nu 0))-
      realBoxAverage (realPressureContraction (velocity nu 0) (pressure nu 0))-
        2*nu*realBoxAverage (realViscous (velocity nu 0))=0 := by
  rw [initial_velocity,initial_pressure,abc_amplification_mean,abc_pressure_mean,abc_viscous_mean]
  ring

end OperatorDerivativeRewrite.Foundation.PeriodicPressureSignCounterexample
