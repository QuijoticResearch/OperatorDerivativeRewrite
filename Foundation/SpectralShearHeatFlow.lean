import Foundation.ABCNavierStokesFlow

/-! Exact periodic shear heat solutions with two low modes and one high mode.
The nonlinear advection vanishes for the actual synthesized velocity. -/
noncomputable section
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.SpectralShearHeatFlow
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality RealFiniteFourierAnalysis RealPeriodicViscousCancellation
  ABCFourierProfile RealBeltramiEuler
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def wave (n : ℕ) : Wave := Pi.single 1 (n : ℤ)
def highSine (n : ℕ) : Fourier :=
  AddMonoidAlgebra.single (wave n) (-Complex.I/2) +
    AddMonoidAlgebra.single (-wave n) (Complex.I/2)

theorem high_hermitian (n : ℕ) : Hermitian (highSine n) := by
  rw [hermitian_iff_reflection]
  norm_num [highSine, reflection_single, add_comm, map_ofNat]

theorem lap_single (k : Wave) (c : ℂ) :
    lap derivative (AddMonoidAlgebra.single k c) =
      AddMonoidAlgebra.single k (-((k 0 : ℂ)^2+(k 1 : ℂ)^2+(k 2 : ℂ)^2)*c) := by
  ext q
  by_cases h : k = q
  · subst q
    simp [lap, derivative_apply, d_single, weight, Fin.sum_univ_succ]
    ring_nf
    simp [Complex.I_sq]
    ring
  · simp [lap, derivative_apply, d_single, weight, Fin.sum_univ_succ,
      Finsupp.single_apply, h]

theorem high_laplacian (n : ℕ) :
    lap derivative (highSine n) = (-(n : ℂ)^2) • highSine n := by
  rw [highSine, lap_add, lap_single, lap_single, smul_add]
  simp [wave, Pi.single_apply, Pi.neg_apply, smul_eq_mul,
    AddMonoidAlgebra.single_mul_single]

theorem high_derivative_zero (n : ℕ) : derivative 0 (highSine n) = 0 := by
  simp [highSine, derivative_apply, d_single, weight, wave, Pi.single_apply]

def decay (nu frequency t : ℝ) : ℝ := Real.exp (-nu*frequency^2*t)
def profile (n : ℕ) (a b c : ℝ) : Fourier :=
  (a : ℂ) • sine 1 + (b : ℂ) • sine 2 + (c : ℂ) • highSine n
def state (n : ℕ) (nu t : ℝ) : Fin 3 → Fourier :=
  ![profile n (2*decay nu 1 t) (decay nu 1 t) (decay nu n t), 0, 0]
def velocity (n : ℕ) (nu t : ℝ) : RealField := realizeReal (state n nu t)

theorem profile_laplacian (n : ℕ) (a b c : ℝ) :
    lap derivative (profile n a b c) = profile n (-a) (-b) (-((n : ℝ)^2)*c) := by
  unfold profile
  rw [lap_add, lap_add, lap_smul, lap_smul, lap_smul,
    lap_sine, lap_sine, high_laplacian]
  simp [smul_neg, smul_smul, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_pow, mul_comm]

theorem profile_derivative_zero (n : ℕ) (a b c : ℝ) :
    derivative 0 (profile n a b c) = 0 := by
  simp [profile, Derivation.map_smul, derivative_sine, high_derivative_zero]

theorem profile_hermitian (n : ℕ) (a b c : ℝ) : Hermitian (profile n a b c) :=
  hermitian_add _ _ (hermitian_add _ _
    (hermitian_real_smul a _ (sine_hermitian 1))
    (hermitian_real_smul b _ (sine_hermitian 2)))
    (hermitian_real_smul c _ (high_hermitian n))

theorem profile_realization (n : ℕ) (a b c : ℝ) (x : Space) :
    realSynthesis (profile n a b c) x =
      a*Real.sin (x 1)+b*Real.sin (x 2)+c*realSynthesis (highSine n) x := by
  have hm (d : ℝ) (f : Fourier) :
      realSynthesis ((d : ℂ) • f) x = d*realSynthesis f x := by
    simp [realSynthesis, Complex.mul_re]
  have ha (f g : Fourier) : realSynthesis (f+g) x =
      realSynthesis f x+realSynthesis g x := by simp [realSynthesis]
  simp only [profile, ha, hm, realize_sine]

theorem decay_derivative (nu frequency t : ℝ) :
    HasDerivAt (decay nu frequency) (-nu*frequency^2*decay nu frequency t) t := by
  change HasDerivAt (fun s => Real.exp ((-nu*frequency^2)*s))
    ((-nu*frequency^2)*Real.exp ((-nu*frequency^2)*t)) t
  simpa only [id_eq, mul_one, mul_comm] using
    ((hasDerivAt_id t).const_mul (-nu*frequency^2)).exp

theorem velocity_formula (n : ℕ) (nu t : ℝ) (x : Space) :
    velocity n nu t x = ![2*decay nu 1 t*Real.sin (x 1)+
      decay nu 1 t*Real.sin (x 2)+decay nu n t*realSynthesis (highSine n) x, 0, 0] := by
  ext i
  fin_cases i
  · exact profile_realization n _ _ _ x
  · simp [velocity, realizeReal, state, realSynthesis]
  · simp [velocity, realizeReal, state, realSynthesis]

theorem time_derivative (n : ℕ) (nu t : ℝ) (x : Space) (i : Fin 3) :
    deriv (fun s => velocity n nu s x i) t =
      nu*realLaplacian (fun y => velocity n nu t y i) x := by
  have he : (fun y => velocity n nu t y i) = realSynthesis (state n nu t i) := rfl
  rw [he, realLaplacian_synthesis]
  have hd := (((decay_derivative nu 1 t).const_mul 2).mul_const (Real.sin (x 1))).add
    ((decay_derivative nu 1 t).mul_const (Real.sin (x 2))) |>.add
    ((decay_derivative nu n t).mul_const (realSynthesis (highSine n) x))
  change HasDerivAt (fun s => 2*decay nu 1 s*Real.sin (x 1)+
    decay nu 1 s*Real.sin (x 2)+decay nu n s*realSynthesis (highSine n) x) _ t at hd
  fin_cases i
  · change deriv (fun s => velocity n nu s x 0) t =
      nu*realSynthesis (lap derivative (profile n (2*decay nu 1 t)
        (decay nu 1 t) (decay nu n t))) x
    have hf : (fun s => velocity n nu s x 0) = fun s =>
        2*decay nu 1 s*Real.sin (x 1)+decay nu 1 s*Real.sin (x 2)+
          decay nu n s*realSynthesis (highSine n) x := by
      funext s; rw [velocity_formula]; rfl
    rw [hf, hd.deriv]
    rw [profile_laplacian, profile_realization]
    norm_num
    ring
  · simp [velocity_formula, state, realSynthesis, lap]
  · simp [velocity_formula, state, realSynthesis, lap]

theorem advection_zero (n : ℕ) (nu t : ℝ) (x : Space) (i : Fin 3) :
    realAdvection (velocity n nu t) x i = 0 := by
  unfold realAdvection
  simp only [velocity, realizeReal, realPartial_synthesis]
  fin_cases i <;> simp [state, Fin.sum_univ_succ, profile_derivative_zero, realSynthesis]

theorem incompressible (n : ℕ) (nu t : ℝ) (x : Space) :
    realDivergence (velocity n nu t) x = 0 := by
  simp only [realDivergence, velocity, realizeReal, realPartial_synthesis]
  simp [state, Fin.sum_univ_succ, profile_derivative_zero, realSynthesis]

theorem momentum (n : ℕ) (nu t : ℝ) (x : Space) (i : Fin 3) :
    deriv (fun s => velocity n nu s x i) t + realAdvection (velocity n nu t) x i +
      realPartial i (fun _ : Space => (0 : ℝ)) x =
        nu*realLaplacian (fun y => velocity n nu t y i) x := by
  rw [time_derivative, advection_zero]
  simp [realPartial]

theorem periodic (n : ℕ) (nu t : ℝ) (x : Space) (i j : Fin 3) :
    Function.Periodic (fun r => velocity n nu t (Function.update x j r) i) (2*Real.pi) :=
  real_component_periodic (state n nu t) x i j

theorem high_realization (n : ℕ) (x : Space) :
    realSynthesis (highSine n) x = Real.sin ((n : ℝ)*x 1) := by
  simp [realSynthesis, highSine, synthesis_single, character_neg, character, phase,
    wave, Fin.sum_univ_succ, Complex.exp_re, Complex.exp_im,
    Complex.mul_re, Complex.mul_im]
  ring

theorem velocity_smooth (n : ℕ) (nu : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Space => velocity n nu p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  simp only [velocity_formula, high_realization]
  fin_cases i
  · change ContDiff ℝ ∞ (fun p : ℝ × Space =>
      2*decay nu 1 p.1*Real.sin (p.2 1)+decay nu 1 p.1*Real.sin (p.2 2)+
        decay nu n p.1*Real.sin ((n : ℝ)*p.2 1))
    unfold decay
    fun_prop
  · change ContDiff ℝ ∞ (fun _ : ℝ × Space => (0 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun _ : ℝ × Space => (0 : ℝ))
    exact contDiff_const

end OperatorDerivativeRewrite.Foundation.SpectralShearHeatFlow
