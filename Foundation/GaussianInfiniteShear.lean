import Foundation.GaussianPeriodicHeat
import Foundation.SpectralShearHeatFlow

/-! An actual periodic classical Navier–Stokes shear with a fixed initial
Gaussian Fourier series. Fourier-tail identification is a separate obligation. -/
noncomputable section
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianInfiniteShear
open FiniteFourierSynthesis RealFiniteFourierAnalysis RealPeriodicViscousCancellation
open RealBeltramiEuler GaussianFourierJets GaussianPeriodicHeat
set_option backward.isDefEq.respectTransparency false

def amplitude (nu t : ℝ) : ℝ := Real.exp (-nu*t)
def scalar (nu t : ℝ) (x : Space) : ℝ :=
  2*profile nu t (x 1)+amplitude nu t*Real.sin (x 2)
def velocity (nu t : ℝ) (x : Space) : Fin 3 → ℝ := ![scalar nu t x, 0, 0]

theorem scalar_partial (nu t : ℝ) (hs : 0 < 1+nu*t) (x : Space) (j : Fin 3) :
    realPartial j (scalar nu t) x =
      ![0, 2*jet 1 (1+nu*t) (x 1), amplitude nu t*Real.cos (x 2)] j := by
  fin_cases j
  · have he : (fun r => scalar nu t (Function.update x 0 r)) = fun _ => scalar nu t x := by
      funext r
      simp [scalar, Function.update_of_ne]
    change deriv (fun r => scalar nu t (Function.update x 0 r)) (x 0) = 0
    rw [he]
    simp
  · change deriv (fun r => 2*profile nu t r+amplitude nu t*Real.sin (x 2)) (x 1) = _
    exact (((spatial_derivative nu t (x 1) hs).const_mul 2).add_const _).deriv
  · change deriv (fun r => 2*profile nu t (x 1)+amplitude nu t*Real.sin r) (x 2) =
      amplitude nu t*Real.cos (x 2)
    simpa only [mul_comm] using
      (((Real.hasDerivAt_sin (x 2)).const_mul (amplitude nu t)).const_add _).deriv

theorem scalar_partial_function (nu t : ℝ) (hs : 0 < 1+nu*t) (j : Fin 3) :
    realPartial j (scalar nu t) = fun x =>
      ![0, 2*jet 1 (1+nu*t) (x 1), amplitude nu t*Real.cos (x 2)] j :=
  funext (fun x => scalar_partial nu t hs x j)

theorem scalar_laplacian (nu t : ℝ) (hs : 0 < 1+nu*t) (x : Space) :
    realLaplacian (scalar nu t) x =
      2*jet 2 (1+nu*t) (x 1)-amplitude nu t*Real.sin (x 2) := by
  unfold realLaplacian
  simp_rw [scalar_partial_function nu t hs]
  change realPartial 0 (fun _ : Space => (0 : ℝ)) x +
      (realPartial 1 (fun y => 2*jet 1 (1+nu*t) (y 1)) x +
      (realPartial 2 (fun y => amplitude nu t*Real.cos (y 2)) x+0)) = _
  have h1 : realPartial 1 (fun y => 2*jet 1 (1+nu*t) (y 1)) x =
      2*jet 2 (1+nu*t) (x 1) := by
    change deriv (fun r => 2*jet 1 (1+nu*t) r) (x 1) = _
    exact ((jet_derivative 1 _ hs _).const_mul 2).deriv
  have h2 : realPartial 2 (fun y => amplitude nu t*Real.cos (y 2)) x =
      -amplitude nu t*Real.sin (x 2) := by
    change deriv (fun r => amplitude nu t*Real.cos r) (x 2) = _
    simpa only [mul_neg, neg_mul] using
      ((Real.hasDerivAt_cos (x 2)).const_mul (amplitude nu t)).deriv
  rw [h1, h2]
  simp [realPartial, sub_eq_add_neg]

theorem amplitude_derivative (nu t : ℝ) : HasDerivAt (amplitude nu) (-nu*amplitude nu t) t := by
  change HasDerivAt (fun u => Real.exp (-nu*u)) (-nu*Real.exp (-nu*t)) t
  simpa [amplitude, mul_comm] using ((hasDerivAt_id t).const_mul (-nu)).exp

theorem scalar_time_derivative (nu t : ℝ) (hs : 0 < 1+nu*t) (x : Space) :
    HasDerivAt (fun u => scalar nu u x)
      (nu*(2*jet 2 (1+nu*t) (x 1)-amplitude nu t*Real.sin (x 2))) t := by
  have h := ((time_derivative nu t (x 1) hs).const_mul 2).add
    ((amplitude_derivative nu t).mul_const (Real.sin (x 2)))
  convert h using 1
  · rfl
  · ring

theorem advection_zero (nu t : ℝ) (hs : 0 < 1+nu*t) (x : Space) (i : Fin 3) :
    realAdvection (velocity nu t) x i = 0 := by
  fin_cases i
  · unfold realAdvection
    change realPartial 0 (scalar nu t) x*scalar nu t x+
      (realPartial 1 (scalar nu t) x*0+(realPartial 2 (scalar nu t) x*0+0)) = 0
    rw [scalar_partial nu t hs x 0]
    simp
  · simp [realAdvection, velocity, realPartial]
  · simp [realAdvection, velocity, realPartial]

theorem incompressible (nu t : ℝ) (hs : 0 < 1+nu*t) (x : Space) :
    realDivergence (velocity nu t) x = 0 := by
  change realPartial 0 (scalar nu t) x+
    (realPartial 1 (fun _ : Space => (0 : ℝ)) x+
    (realPartial 2 (fun _ : Space => (0 : ℝ)) x+0)) = 0
  rw [scalar_partial nu t hs x 0]
  simp [realPartial]

theorem momentum (nu t : ℝ) (hs : 0 < 1+nu*t) (x : Space) (i : Fin 3) :
    deriv (fun u => velocity nu u x i) t+realAdvection (velocity nu t) x i+
      realPartial i (fun _ : Space => (0 : ℝ)) x =
        nu*realLaplacian (fun y => velocity nu t y i) x := by
  rw [advection_zero nu t hs]
  fin_cases i
  · change deriv (fun u => scalar nu u x) t+0+
      realPartial 0 (fun _ : Space => (0 : ℝ)) x = nu*realLaplacian (scalar nu t) x
    rw [(scalar_time_derivative nu t hs x).deriv, scalar_laplacian nu t hs]
    simp [realPartial]
  · simp [velocity, realPartial, realLaplacian]
  · simp [velocity, realPartial, realLaplacian]

theorem spatial_smooth (nu t : ℝ) (hs : 0 < 1+nu*t) : ContDiff ℝ ∞ (velocity nu t) := by
  have heval : ContDiff ℝ ∞ (fun x : Space => x 1) := by fun_prop
  have ha : ContDiff ℝ ∞ (fun x : Space => profile nu t (x 1)) :=
    (profile_smooth nu t hs).comp heval
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Space => 2*profile nu t (x 1)+
      amplitude nu t*Real.sin (x 2))
    have hz : ContDiff ℝ ∞ (fun x : Space => Real.sin (x 2)) := by fun_prop
    exact (contDiff_const.mul ha).add (contDiff_const.mul hz)
  · change ContDiff ℝ ∞ (fun _ : Space => (0 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun _ : Space => (0 : ℝ))
    exact contDiff_const

theorem periodic (nu t : ℝ) (x : Space) (j : Fin 3) :
    Function.Periodic (fun r => velocity nu t (Function.update x j r)) (2*Real.pi) := by
  intro r
  ext i
  fin_cases j <;> fin_cases i <;>
    simp [velocity, scalar, Function.update_of_ne, profile_periodic nu t r,
      Real.sin_add_two_pi]

theorem initial (nu : ℝ) (x : Space) :
    velocity nu 0 x = ![2*jet 0 1 (x 1)+Real.sin (x 2), 0, 0] := by
  simp [velocity, scalar, GaussianPeriodicHeat.initial, amplitude]

theorem initial_smooth (nu : ℝ) : ContDiff ℝ ∞ (velocity nu 0) :=
  spatial_smooth nu 0 (by norm_num)

theorem solution_nonnegative (nu t : ℝ) (hnu : 0 ≤ nu) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (velocity nu t) ∧
      (∀ x, realDivergence (velocity nu t) x = 0) ∧
      (∀ x i, deriv (fun u => velocity nu u x i) t+realAdvection (velocity nu t) x i+
        realPartial i (fun _ : Space => (0 : ℝ)) x =
          nu*realLaplacian (fun y => velocity nu t y i) x) := by
  have hs := positive_parameter nu t hnu ht
  exact ⟨spatial_smooth nu t hs, incompressible nu t hs, momentum nu t hs⟩

end OperatorDerivativeRewrite.Foundation.GaussianInfiniteShear
