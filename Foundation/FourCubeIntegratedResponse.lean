import Foundation.FourCubeIntegratedCubic
import Mathlib.Probability.Moments.MGFAnalytic

/-! Actual coupling derivatives of the three-boundary-axis cell partition.
The analytic hypotheses are discharged from the finite action bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.FourCubeIntegratedResponse
open FourCubeHaarParity FourCubeIntegratedCubic

def source (x y z : ℝ) (s : InteriorState) : ℝ := -cellAction x y z s

def partition3 (x y z : ℝ) : ℝ → ℝ := mgf (source x y z) interiorHaar

def freeEnergy3 (x y z : ℝ) (β : ℝ) : ℝ := -cgf (source x y z) interiorHaar β

theorem source_measurable (x y z : ℝ) : Measurable (source x y z) :=
  (cellAction_measurable x y z).neg

theorem source_memLp (x y z : ℝ) : MemLp (source x y z) 2 interiorHaar :=
  (cellAction_memLp x y z).neg

theorem exponential_integrable (x y z β : ℝ) :
    Integrable (fun s => Real.exp (β*source x y z s)) interiorHaar := by
  have hb (s : InteriorState) : |source x y z s/144| ≤ 1 := by
    rw [abs_div,source,abs_neg,abs_of_nonneg (cellAction_bounds x y z s).1,
      abs_of_pos (by norm_num : (0:ℝ)<144)]
    exact (div_le_one (by norm_num : (0:ℝ)<144)).mpr (cellAction_bounds x y z s).2
  have he : (fun s : InteriorState => Real.exp (β*source x y z s))=
      (fun s => Real.exp ((144*β)*(source x y z s/144))) := by
    funext s
    congr 1
    ring
  rw [he]
  exact BoundedExponentialTiltResponse.exponential_integrable interiorHaar
    (fun s => source x y z s/144) ((source_measurable x y z).div_const 144) hb (144*β)

theorem exponential_domain (x y z : ℝ) : integrableExpSet (source x y z) interiorHaar=Set.univ := by
  ext β
  simp only [Set.mem_univ,iff_true]
  exact exponential_integrable x y z β

theorem exponential_interior (x y z β : ℝ) :
    β∈interior (integrableExpSet (source x y z) interiorHaar) := by
  rw [exponential_domain,interior_univ]
  trivial

theorem partition3_integral (x y z β : ℝ) :
    partition3 x y z β=∫ s, Real.exp (-β*cellAction x y z s) ∂interiorHaar := by
  simp only [partition3,mgf,source,mul_neg,neg_mul]

theorem partition3_pos (x y z β : ℝ) : 0 < partition3 x y z β :=
  mgf_pos (exponential_integrable x y z β)

theorem partition3_analytic (x y z β : ℝ) : AnalyticAt ℝ (partition3 x y z) β :=
  analyticAt_mgf (exponential_interior x y z β)

theorem freeEnergy3_analytic (x y z β : ℝ) : AnalyticAt ℝ (freeEnergy3 x y z) β :=
  (analyticAt_cgf (exponential_interior x y z β)).neg

theorem freeEnergy3_second_zero (x y z : ℝ) :
    iteratedDeriv 2 (freeEnergy3 x y z) 0= -variance (cellAction x y z) interiorHaar := by
  have hm := exponential_interior x y z 0
  have hc := iteratedDeriv_two_cgf hm
  rw [deriv_cgf_zero hm] at hc
  simp only [zero_mul,Real.exp_zero,mul_one,mgf_zero,div_one,probReal_univ] at hc
  have hv := variance_eq_sub (source_memLp x y z)
  have he : iteratedDeriv 2 (cgf (source x y z) interiorHaar) 0=
      variance (source x y z) interiorHaar := hc.trans hv.symm
  change iteratedDeriv 2 (fun β => -cgf (source x y z) interiorHaar β) 0=_
  rw [iteratedDeriv_fun_neg,he]
  congr 1
  exact variance_fun_neg

theorem freeEnergy3_second_odd_y (x y z : ℝ) :
    iteratedDeriv 2 (freeEnergy3 x y z) 0-
      iteratedDeriv 2 (freeEnergy3 x (-y) z) 0=Real.sin x*Real.sin y*Real.sin z := by
  rw [freeEnergy3_second_zero,freeEnergy3_second_zero]
  linarith [variance_odd_y x y z]

theorem freeEnergy3_explicit_second_difference :
    iteratedDeriv 2 (freeEnergy3 (Real.pi/6) (Real.pi/6) (Real.pi/6)) 0-
      iteratedDeriv 2 (freeEnergy3 (Real.pi/6) (-(Real.pi/6)) (Real.pi/6)) 0=(1/8:ℝ) := by
  rw [freeEnergy3_second_odd_y,Real.sin_pi_div_six]
  norm_num

/-- Actual directional third boundary derivative of the second coupling
response: y is differentiated first, then x, then z. No interchange is assumed. -/
theorem second_response_boundary_y (x z : ℝ) :
    HasDerivAt (fun y => iteratedDeriv 2 (freeEnergy3 x y z) 0) (Real.sin x*Real.sin z/2) 0 := by
  have he : (fun y => iteratedDeriv 2 (freeEnergy3 x y z) 0)=
      (fun y => SU2JointPlaquetteCubic.action x y z/2-
        variance (residualAction x z) interiorHaar-3/4) := by
    funext y
    rw [freeEnergy3_second_zero,variance_formula]
    have ht := FourCubeWilsonCubic.triple_action x y z
    linarith
  have ha : HasDerivAt (fun y => SU2JointPlaquetteCubic.action x y z) (Real.sin x*Real.sin z) 0 := by
    have hs : (fun y => SU2JointPlaquetteCubic.action x y z)=
        (fun y => SU2JointPlaquetteCubic.action y x z) :=
      funext (fun y => SU2JointPlaquetteCubic.action_symmetric_xy x y z)
    rw [hs]
    simpa using SU2JointPlaquetteCubic.action_x_hasDerivAt 0 x z
  rw [he]
  exact ((ha.div_const 2).sub_const (variance (residualAction x z) interiorHaar)).sub_const (3/4)

theorem integrated_mixed_cubic :
    deriv (fun z => deriv (fun x => deriv (fun y =>
      iteratedDeriv 2 (freeEnergy3 x y z) 0) 0) 0) 0=(1/2:ℝ) := by
  have hy (x z : ℝ) : deriv (fun y => iteratedDeriv 2 (freeEnergy3 x y z) 0) 0=
      Real.sin x*Real.sin z/2 := (second_response_boundary_y x z).deriv
  simp_rw [hy]
  have hx (z : ℝ) : deriv (fun x => Real.sin x*Real.sin z/2) 0=Real.sin z/2 := by
    simpa using (((Real.hasDerivAt_sin 0).mul_const (Real.sin z)).div_const 2).deriv
  simp_rw [hx]
  simpa using ((Real.hasDerivAt_sin 0).div_const 2).deriv

/-- Exact non-evenness of the genuine partition at positive couplings
arbitrarily close to0; C^2 interval hypotheses are explicitly verified. -/
theorem exists_positive_coupling_nonparity_of_sine (x y z ε : ℝ) (hε : 0<ε)
    (hnonzero : Real.sin x*Real.sin y*Real.sin z ≠ 0) :
    ∃ β : ℝ, 0<β ∧ β<ε ∧ partition3 x y z β ≠ partition3 x (-y) z β := by
  by_contra hn
  push_neg at hn
  have heq : Set.EqOn (freeEnergy3 x y z) (freeEnergy3 x (-y) z) (Set.Icc 0 (ε/2)) := by
    intro β hβ
    by_cases hz : β=0
    · subst β
      simp [freeEnergy3,cgf_zero]
    · have hp : 0<β := lt_of_le_of_ne hβ.1 (Ne.symm hz)
      have hu : β<ε := by linarith [hβ.2]
      change -Real.log (partition3 x y z β)= -Real.log (partition3 x (-y) z β)
      rw [hn β hp hu]
  have hs : UniqueDiffOn ℝ (Set.Icc 0 (ε/2)) := uniqueDiffOn_Icc (by linarith)
  have hx : (0:ℝ)∈Set.Icc 0 (ε/2) := ⟨le_rfl,by linarith⟩
  have hd := iteratedDerivWithin_congr (n := 2) heq hx
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (freeEnergy3_analytic x y z 0).contDiffAt hx,
    iteratedDerivWithin_eq_iteratedDeriv hs (freeEnergy3_analytic x (-y) z 0).contDiffAt hx] at hd
  have hw := freeEnergy3_second_odd_y x y z
  rw [hd,sub_self] at hw
  exact hnonzero hw.symm

theorem exists_positive_coupling_nonparity (ε : ℝ) (hε : 0<ε) :
    ∃ β : ℝ, 0<β ∧ β<ε ∧
      partition3 (Real.pi/6) (Real.pi/6) (Real.pi/6) β ≠
        partition3 (Real.pi/6) (-(Real.pi/6)) (Real.pi/6) β := by
  apply exists_positive_coupling_nonparity_of_sine _ _ _ ε hε
  norm_num [Real.sin_pi_div_six]

/-- Both boundary angles and positive coupling can be made arbitrarily small.
This still gives no estimate in the large-beta/continuum regime. -/
theorem exists_small_boundary_nonparity (ε δ : ℝ) (hε : 0<ε) (hδ : 0<δ) :
    ∃ t : ℝ, 0<t ∧ t<δ ∧ ∃ β : ℝ, 0<β ∧ β<ε ∧
      partition3 t t t β ≠ partition3 t (-t) t β := by
  let t := min (δ/2) (Real.pi/2)
  have ht : 0<t := lt_min (by linarith) (by positivity)
  have hδt : t<δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hπt : t<Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  have hsin : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht hπt
  obtain ⟨β,hβ,hβε,hne⟩ := exists_positive_coupling_nonparity_of_sine t t t ε hε
    (mul_ne_zero (mul_ne_zero hsin.ne' hsin.ne') hsin.ne')
  exact ⟨t,ht,hδt,β,hβ,hβε,hne⟩

end OperatorDerivativeRewrite.Foundation.FourCubeIntegratedResponse
