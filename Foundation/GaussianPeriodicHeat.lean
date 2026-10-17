import Foundation.GaussianFourierJets

/-! Parameter differentiation of the actual Gaussian Fourier series and its
classical periodic heat equation. The smoothing at time zero is fixed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianPeriodicHeat
open GaussianFourierJets
set_option backward.isDefEq.respectTransparency false

theorem bound_mono (k : ℕ) (s u : ℝ) (hsu : s ≤ u) (n : ℤ) :
    bound k u n ≤ bound k s n := by
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg _) _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (n : ℝ)]

theorem term_parameter_derivative (k : ℕ) (s : ℝ) (n : ℤ) (y : ℝ) :
    HasDerivAt (fun u => term k u n y) (term (k+2) s n y) s := by
  have h := (((hasDerivAt_id s).const_mul (-(n : ℝ)^2)).exp.const_mul
    ((n : ℝ)^k)).mul_const (Real.cos ((n : ℝ)*y+(k : ℝ)*Real.pi/2))
  simp only [id_eq, mul_one] at h
  convert h using 1
  · funext u
    simp [term, neg_mul, mul_comm]
  · simp only [term, Nat.cast_add, Nat.cast_ofNat, pow_add]
    rw [show (n : ℝ)*y+((k : ℝ)+2)*Real.pi/2 =
      ((n : ℝ)*y+(k : ℝ)*Real.pi/2)+Real.pi by ring, Real.cos_add_pi]
    ring_nf

theorem parameter_derivative (k : ℕ) (s : ℝ) (hs : 0 < s) (y : ℝ) :
    HasDerivAt (fun u => jet k u y) (jet (k+2) s y) s := by
  have hhalf : 0 < s/2 := by positivity
  have hmem : s ∈ Ioi (s/2) := by simp; linarith
  exact hasDerivAt_tsum_of_isPreconnected (bound_summable (k+2) (s/2) hhalf)
    isOpen_Ioi (convex_Ioi (s/2)).isPreconnected
    (fun n u _ => term_parameter_derivative k u n y)
    (fun n u hu => (term_bound (k+2) u n y).trans (bound_mono _ _ _ hu.le n))
    hmem (term_summable k s hs y) hmem

def profile (nu t y : ℝ) : ℝ := jet 0 (1+nu*t) y

theorem initial (nu y : ℝ) : profile nu 0 y = jet 0 1 y := by simp [profile]

theorem spatial_derivative (nu t y : ℝ) (hs : 0 < 1+nu*t) :
    HasDerivAt (profile nu t) (jet 1 (1+nu*t) y) y :=
  jet_derivative 0 _ hs y

theorem spatial_second_derivative (nu t y : ℝ) (hs : 0 < 1+nu*t) :
    deriv (deriv (profile nu t)) y = jet 2 (1+nu*t) y := by
  change deriv (deriv (jet 0 (1+nu*t))) y = _
  rw [deriv_jet 0 _ hs, deriv_jet 1 _ hs]

theorem time_derivative (nu t y : ℝ) (hs : 0 < 1+nu*t) :
    HasDerivAt (fun u => profile nu u y) (nu*jet 2 (1+nu*t) y) t := by
  have h := (parameter_derivative 0 _ hs y).comp t
    (((hasDerivAt_id t).const_mul nu).const_add 1)
  simpa only [profile, Function.comp_def, Nat.zero_add, mul_one, id_eq, mul_comm] using h

theorem heat_equation (nu t y : ℝ) (hs : 0 < 1+nu*t) :
    deriv (fun u => profile nu u y) t = nu*deriv (deriv (profile nu t)) y := by
  rw [(time_derivative nu t y hs).deriv, spatial_second_derivative nu t y hs]

theorem profile_smooth (nu t : ℝ) (hs : 0 < 1+nu*t) : ContDiff ℝ ∞ (profile nu t) :=
  jet_smooth 0 _ hs

theorem profile_periodic (nu t : ℝ) : Function.Periodic (profile nu t) (2*Real.pi) :=
  jet_periodic 0 _

theorem positive_parameter (nu t : ℝ) (hnu : 0 ≤ nu) (ht : 0 ≤ t) : 0 < 1+nu*t := by
  positivity

theorem jet_joint_continuous (k : ℕ) (s y : ℝ) (hs : 0 < s) :
    ContinuousAt (fun p : ℝ × ℝ => jet k p.1 p.2) (s,y) := by
  let U : Set (ℝ × ℝ) := {p | s/2 < p.1}
  have hhalf : 0 < s/2 := by positivity
  have hc : ContinuousOn (fun p : ℝ × ℝ => jet k p.1 p.2) U := by
    change ContinuousOn (fun p : ℝ × ℝ => ∑' n : ℤ, term k p.1 n p.2) U
    refine continuousOn_tsum (fun n => ?_) (bound_summable k (s/2) hhalf)
      (fun n p hp => (term_bound k p.1 n p.2).trans (bound_mono k _ _ hp.le n))
    ·
      have ht : Continuous (fun p : ℝ × ℝ => term k p.1 n p.2) := by
        unfold term
        fun_prop
      exact ht.continuousOn
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst
  have hmem : (s,y) ∈ U := by dsimp [U]; linarith
  exact hc.continuousAt (hU.mem_nhds hmem)

theorem profile_joint_continuous (nu t y : ℝ) (hs : 0 < 1+nu*t) :
    ContinuousAt (fun p : ℝ × ℝ => profile nu p.1 p.2) (t,y) := by
  have hg : Continuous (fun p : ℝ × ℝ => (1+nu*p.1, p.2)) := by fun_prop
  change ContinuousAt ((fun q : ℝ × ℝ => jet 0 q.1 q.2) ∘
    (fun p : ℝ × ℝ => (1+nu*p.1, p.2))) (t,y)
  exact (jet_joint_continuous 0 (1+nu*t) y hs).comp
    (f := fun p : ℝ × ℝ => (1+nu*p.1, p.2)) hg.continuousAt

end OperatorDerivativeRewrite.Foundation.GaussianPeriodicHeat
