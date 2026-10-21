import Foundation.RiemannQuadraticParabolic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Actual all-order quadratic-flow parabolic expansion and Hermite scaling.
The existing Gaussian Hermite raising/lowering identities identify every phase
coefficient. Cauchy estimates give one genuine L1 majorant for all finite Taylor
remainders. Finite integral linearity yields the actual flow expansion; vanishing
lower derivatives gives uniform finite-multiplicity limits on each complex disk.
Actual zero counts/splitting and global strip contraction are separate obligations. -/
noncomputable section
open Complex MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticAllOrders
open RiemannQuadraticHermite RiemannEvenFlow RiemannEvenDomain
open RiemannQuarticFlow (halfLine)

theorem value_hasDerivAt_raise (n : ℕ) (z : ℂ) :
    HasDerivAt (value n) ((z*value n z-value (n+1) z)/2) z := by
  cases n with
  | zero =>
    have he : value 0=(fun _ : ℂ => 1) := funext value_zero
    rw [he]
    simpa using hasDerivAt_const z (1 : ℂ)
  | succ n =>
    convert value_hasDerivAt n z using 1
    rw [show n+1+1=n+2 by omega,value_recursion]
    ring

def phase (w q : ℂ) : ℂ := Complex.exp (q*w-q^2)
def phaseJet (n : ℕ) (w q : ℂ) : ℂ := value n (w-2*q)*phase w q

theorem phase_hasDerivAt (w q : ℂ) :
    HasDerivAt (phase w) ((w-2*q)*phase w q) q := by
  have h := (((hasDerivAt_id q).mul_const w).sub ((hasDerivAt_id q).pow 2)).cexp
  change HasDerivAt (fun x : ℂ => Complex.exp (x*w-x^2))
    ((w-2*q)*Complex.exp (q*w-q^2)) q
  convert h using 1
  · funext x; rfl
  · simp only [Pi.sub_apply,Pi.pow_apply,id_eq]
    norm_num
    ring

theorem phaseJet_hasDerivAt (n : ℕ) (w q : ℂ) :
    HasDerivAt (phaseJet n w) (phaseJet (n+1) w q) q := by
  have hv : HasDerivAt (fun q : ℂ => w-2*q) (-2) q := by
    simpa [Pi.sub_def] using (hasDerivAt_const q w).sub ((hasDerivAt_id q).const_mul 2)
  have h := ((value_hasDerivAt_raise n (w-2*q)).comp q hv).mul (phase_hasDerivAt w q)
  change HasDerivAt (fun x : ℂ => value n (w-2*x)*phase w x)
    (value (n+1) (w-2*q)*phase w q) q
  convert h using 1
  · funext x; rfl
  · simp only [Function.comp_apply]
    ring

theorem phase_iteratedDeriv (n : ℕ) (w : ℂ) :
    iteratedDeriv n (phase w) = phaseJet n w := by
  induction n with
  | zero => funext q; simp [phaseJet]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext q
    exact (phaseJet_hasDerivAt n w q).deriv

theorem phase_iteratedDeriv_zero (n : ℕ) (w : ℂ) :
    iteratedDeriv n (phase w) 0 = value n w := by
  rw [phase_iteratedDeriv]
  simp [phaseJet,phase]

theorem phase_differentiable (w : ℂ) : Differentiable ℂ (phase w) :=
  fun q => (phase_hasDerivAt w q).differentiableAt

theorem phase_hasSum (w q : ℂ) :
    HasSum (fun n : ℕ => q^n*value n w/(n.factorial : ℂ)) (phase w q) := by
  have h := Complex.hasSum_taylorSeries_of_entire (phase_differentiable w) 0 q
  simpa only [phase_iteratedDeriv_zero,sub_zero,smul_eq_mul,div_eq_mul_inv,
    mul_comm,mul_left_comm,mul_assoc] using h

theorem scaled_phase_derivative_zero (n : ℕ) (c w : ℂ) :
    iteratedDeriv n (fun h : ℂ => phase w (c*h)) 0 = c^n*value n w := by
  rw [iteratedDeriv_comp_const_mul ((phase_differentiable w).contDiff)]
  simp [phase_iteratedDeriv_zero]

theorem scaled_phase_hasSum (c w h : ℂ) :
    HasSum (fun n : ℕ => h^n*(c^n*value n w)/(n.factorial : ℂ)) (phase w (c*h)) := by
  simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using phase_hasSum w (c*h)

theorem scaled_phase_norm (c w q : ℂ) (hq : ‖q‖ ≤ 1) :
    ‖phase w (c*q)‖ ≤ Real.exp (‖c‖*‖w‖+‖c‖^2) := by
  rw [phase,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖c*q*w-(c*q)^2‖ := Complex.re_le_norm _
    _ ≤ ‖c*q*w‖+‖(c*q)^2‖ := norm_sub_le _ _
    _ ≤ ‖c‖*‖w‖+‖c‖^2 := by
      simp only [norm_mul,norm_pow]
      have hh : ‖c‖*‖q‖ ≤ ‖c‖ := mul_le_of_le_one_right (norm_nonneg c) hq
      gcongr

theorem coefficient_norm_bound (n : ℕ) (c w : ℂ) :
    ‖c^n*value n w/(n.factorial : ℂ)‖ ≤ Real.exp (‖c‖*‖w‖+‖c‖^2) := by
  have hf : Differentiable ℂ (fun q : ℂ => phase w (c*q)) :=
    (phase_differentiable w).comp (by fun_prop)
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c := (0 : ℂ)) (R := 1) (C := Real.exp (‖c‖*‖w‖+‖c‖^2))
    (f := fun q : ℂ => phase w (c*q)) n
    (by norm_num : (0 : ℝ)<1)
    (DifferentiableOn.diffContOnCl hf.differentiableOn)
    (fun q hq => scaled_phase_norm c w q (by
      have hnorm : ‖q‖=(1 : ℝ) := by
        simpa only [Metric.mem_sphere,dist_zero_right] using hq
      exact hnorm.le))
  rw [scaled_phase_derivative_zero] at hc
  simp only [one_pow,div_one] at hc
  rw [norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n) : (0 : ℝ)<n.factorial)).mpr
  nlinarith [hc]

theorem scaled_phase_remainder_bound (N : ℕ) (c w h : ℂ) (hh : ‖h‖ ≤ 1/2) :
    ‖phase w (c*h)-∑ n ∈ Finset.range (N+1), h^n*(c^n*value n w)/(n.factorial : ℂ)‖ ≤
      2*Real.exp (‖c‖*‖w‖+‖c‖^2)*‖h‖^(N+1) := by
  have hb (n : ℕ) : ‖h^n*(c^n*value n w)/(n.factorial : ℂ)‖ ≤
      Real.exp (‖c‖*‖w‖+‖c‖^2)*‖h‖^n := by
    rw [mul_div_assoc,norm_mul,norm_pow]
    exact (mul_le_mul_of_nonneg_left (coefficient_norm_bound n c w)
      (pow_nonneg (norm_nonneg h) n)).trans_eq (mul_comm _ _)
  have he := norm_sub_le_of_geometric_bound_of_hasSum (by linarith : ‖h‖<1)
    hb (scaled_phase_hasSum c w h) (N+1)
  rw [norm_sub_rev] at he
  apply he.trans
  apply (div_le_iff₀ (by linarith : (0 : ℝ)<1-‖h‖)).mpr
  have hp : 0 ≤ Real.exp (‖c‖*‖w‖+‖c‖^2)*‖h‖^(N+1) := by positivity
  nlinarith

theorem value_neg (n : ℕ) (w : ℂ) : value n (-w)=(-1 : ℂ)^n*value n w := by
  have he : phase (-w)=(fun q : ℂ => phase w ((-1)*q)) := by
    funext q
    unfold phase
    congr 1
    ring
  calc
    _ = iteratedDeriv n (phase (-w)) 0 := (phase_iteratedDeriv_zero n (-w)).symm
    _ = _ := by rw [he,scaled_phase_derivative_zero]

theorem integrand_factor (j : ℕ) (t h u : ℝ) (z w : ℂ) :
    integrand 1 j (t+h^2) (z+(h : ℂ)*w) u =
      integrand 1 j t z u*phase w ((Complex.I*(u : ℂ))*(h : ℂ)) := by
  rw [RiemannQuadraticParabolic.actual_integrand_phase,phase]
  congr 1
  congr 1
  ring_nf
  simp [Complex.I_sq]

def remainder (N j : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ) (u : ℝ) : ℂ :=
  integrand 1 j (t+h^2) (z+(h : ℂ)*w) u -
    ∑ n ∈ Finset.range (N+1),
      (h : ℂ)^n*value n w/(n.factorial : ℂ)*integrand 1 (j+n) t z u

theorem remainder_factor (N j : ℕ) (t h u : ℝ) (z w : ℂ) :
    remainder N j t z h w u = integrand 1 j t z u *
      (phase w ((Complex.I*(u : ℂ))*(h : ℂ))-
        ∑ n ∈ Finset.range (N+1),
          (h : ℂ)^n*((Complex.I*(u : ℂ))^n*value n w)/(n.factorial : ℂ)) := by
  unfold remainder
  rw [integrand_factor j t h u z w,mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [integrand,pow_add]
  ring

theorem remainder_integrable (N j : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ) :
    Integrable (remainder N j t z h w) halfLine := by
  apply (integrand_integrable 1 j (t+h^2) (z+(h : ℂ)*w)).sub
  exact integrable_finsetSum _ (fun n _ => (integrand_integrable 1 (j+n) t z).const_mul _)

theorem remainder_bound (N j : ℕ) (t h R u : ℝ) (z w : ℂ)
    (hh : |h| ≤ 1/2) (hw : ‖w‖ ≤ R) (hu : 0 ≤ u) :
    ‖remainder N j t z h w u‖ ≤
      2*|h|^(N+1)*weighted 1 j (t+1) (‖z‖+R) u := by
  have hp := scaled_phase_remainder_bound N (Complex.I*(u : ℂ)) w (h : ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hh)
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hu] at hp
  rw [remainder_factor,norm_mul]
  calc
    _ ≤ weighted 1 j t ‖z‖ u*(2*Real.exp (u*R+u^2)*|h|^(N+1)) := by
      apply mul_le_mul (integrand_bound 1 j t z u hu) _ (norm_nonneg _)
        (weighted_nonneg 1 j t ‖z‖ u hu)
      apply hp.trans
      gcongr
    _ = _ := by
      unfold weighted
      rw [show (t+1)*u^(2*1)+(‖z‖+R)*u =
        (t*u^(2*1)+‖z‖*u)+(u*R+u^2) by ring]
      simp only [Real.exp_add]
      ring

theorem remainder_integral (N j : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ) :
    (∫ u, remainder N j t z h w u ∂halfLine) =
      jet 1 j (t+h^2) (z+(h : ℂ)*w) -
        ∑ n ∈ Finset.range (N+1),
          (h : ℂ)^n*value n w/(n.factorial : ℂ)*jet 1 (j+n) t z := by
  have hi (n : ℕ) : Integrable (fun u =>
      (h : ℂ)^n*value n w/(n.factorial : ℂ)*integrand 1 (j+n) t z u) halfLine :=
    (integrand_integrable 1 (j+n) t z).const_mul _
  unfold remainder
  rw [integral_sub (integrand_integrable 1 j (t+h^2) (z+(h : ℂ)*w))
      (integrable_finsetSum _ (fun n _ => hi n)),
    integral_finsetSum _ (fun n _ => hi n)]
  simp only [integral_const_mul,jet]

def budget (j : ℕ) (t : ℝ) (z : ℂ) (R : ℝ) : ℝ :=
  2*(∫ u, weighted 1 j (t+1) (‖z‖+R) u ∂halfLine)

theorem jet_expansion_bound (N j : ℕ) (t h R : ℝ) (z w : ℂ)
    (hh : |h| ≤ 1/2) (hw : ‖w‖ ≤ R) :
    ‖jet 1 j (t+h^2) (z+(h : ℂ)*w) -
      ∑ n ∈ Finset.range (N+1),
        (h : ℂ)^n*value n w/(n.factorial : ℂ)*jet 1 (j+n) t z‖ ≤
      budget j t z R*|h|^(N+1) := by
  have hi := (weighted_integrable 1 j (t+1) (‖z‖+R)).const_mul (2*|h|^(N+1))
  have hp : ∀ᵐ u ∂halfLine, ‖remainder N j t z h w u‖ ≤
      2*|h|^(N+1)*weighted 1 j (t+1) (‖z‖+R) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact remainder_bound N j t h R u z w hh hw hu
  have hb := norm_integral_le_of_norm_le hi hp
  rw [remainder_integral,integral_const_mul] at hb
  convert hb using 1 <;> dsimp [budget] <;> ring

def polynomialPart (N : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N+1),
    (h : ℂ)^n*value n w/(n.factorial : ℂ)*iteratedDeriv n (flow 1 t) z

theorem flow_expansion_bound (N : ℕ) (t h R : ℝ) (z w : ℂ)
    (hh : |h| ≤ 1/2) (hw : ‖w‖ ≤ R) :
    ‖flow 1 (t+h^2) (z+(h : ℂ)*w)-polynomialPart N t z h w‖ ≤
      budget 0 t z R*|h|^(N+1) := by
  have hp := jet_expansion_bound N 0 t h R z w hh hw
  have hn := jet_expansion_bound N 0 t h R (-z) (-w) hh
    (by simpa only [norm_neg] using hw)
  rw [show -z+(h : ℂ)*(-w)=-(z+(h : ℂ)*w) by ring] at hn
  let ep := jet 1 0 (t+h^2) (z+(h : ℂ)*w)-
    ∑ n ∈ Finset.range (N+1), (h : ℂ)^n*value n w/(n.factorial : ℂ)*jet 1 n t z
  let en := jet 1 0 (t+h^2) (-(z+(h : ℂ)*w))-
    ∑ n ∈ Finset.range (N+1), (h : ℂ)^n*value n (-w)/(n.factorial : ℂ)*jet 1 n t (-z)
  have hep : ‖ep‖ ≤ budget 0 t z R*|h|^(N+1) := by simpa only [ep,Nat.zero_add] using hp
  have hen : ‖en‖ ≤ budget 0 t z R*|h|^(N+1) := by
    simpa only [en,Nat.zero_add,budget,norm_neg] using hn
  have hs : polynomialPart N t z h w =
      ((∑ n ∈ Finset.range (N+1), (h : ℂ)^n*value n w/(n.factorial : ℂ)*jet 1 n t z)+
        ∑ n ∈ Finset.range (N+1), (h : ℂ)^n*value n (-w)/(n.factorial : ℂ)*jet 1 n t (-z))/2 := by
    rw [← Finset.sum_add_distrib,Finset.sum_div]
    unfold polynomialPart
    apply Finset.sum_congr rfl
    intro n hn
    rw [RiemannEvenEvolution.flow_iteratedDeriv]
    simp only [RiemannEvenEvolution.symmetricJet,value_neg]
    ring
  have he : flow 1 (t+h^2) (z+(h : ℂ)*w)-polynomialPart N t z h w=(ep+en)/2 := by
    rw [hs]
    dsimp [flow,ep,en]
    ring
  rw [he,norm_div,Complex.norm_ofNat]
  have ha := norm_add_le ep en
  linarith

theorem polynomialPart_at_multiplicity (m : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ)
    (hv : ∀ n < m, iteratedDeriv n (flow 1 t) z=0) :
    polynomialPart m t z h w =
      (h : ℂ)^m*(value m w/(m.factorial : ℂ)*iteratedDeriv m (flow 1 t) z) := by
  unfold polynomialPart
  rw [Finset.sum_range_succ]
  have hs : (∑ n ∈ Finset.range m,
      (h : ℂ)^n*value n w/(n.factorial : ℂ)*iteratedDeriv n (flow 1 t) z)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [hv n (Finset.mem_range.mp hn),mul_zero]
  rw [hs,zero_add]
  ring

theorem multiplicity_scaled_bound (m : ℕ) (t h R : ℝ) (z w : ℂ)
    (hv : ∀ n < m, iteratedDeriv n (flow 1 t) z=0)
    (hh : |h| ≤ 1/2) (hne : h ≠ 0) (hw : ‖w‖ ≤ R) :
    ‖flow 1 (t+h^2) (z+(h : ℂ)*w)/(h : ℂ)^m-
      value m w/(m.factorial : ℂ)*iteratedDeriv m (flow 1 t) z‖ ≤
      budget 0 t z R*|h| := by
  have hp := flow_expansion_bound m t h R z w hh hw
  rw [polynomialPart_at_multiplicity m t z h w hv] at hp
  let A := value m w/(m.factorial : ℂ)*iteratedDeriv m (flow 1 t) z
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hne
  have he : flow 1 (t+h^2) (z+(h : ℂ)*w)/(h : ℂ)^m-A =
      (flow 1 (t+h^2) (z+(h : ℂ)*w)-(h : ℂ)^m*A)/(h : ℂ)^m := by field_simp
  change ‖flow 1 (t+h^2) (z+(h : ℂ)*w)/(h : ℂ)^m-A‖ ≤ _
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  apply (div_le_iff₀ (pow_pos (abs_pos.mpr hne) m)).mpr
  simpa only [A,pow_succ,mul_assoc,mul_left_comm,mul_comm] using hp

theorem multiplicity_uniform_on_disk (m : ℕ) (t R : ℝ) (z : ℂ)
    (hv : ∀ n < m, iteratedDeriv n (flow 1 t) z=0) :
    TendstoUniformlyOn
      (fun h : ℝ => fun w : ℂ => flow 1 (t+h^2) (z+(h : ℂ)*w)/(h : ℂ)^m)
      (fun w => value m w/(m.factorial : ℂ)*iteratedDeriv m (flow 1 t) z)
      (𝓝[≠] 0) {w | ‖w‖ ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have habs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun h : ℝ => budget 0 t z R*|h|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul habs
  filter_upwards [habs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2)),
    hlim.eventually (Iio_mem_nhds hε),self_mem_nhdsWithin] with h hh he hne
  intro w hw
  rw [dist_comm,dist_eq_norm]
  exact (multiplicity_scaled_bound m t h R z w hv hh.le (by simpa using hne) hw).trans_lt he

theorem budget_nonneg (j : ℕ) (t : ℝ) (z : ℂ) (R : ℝ) : 0 ≤ budget j t z R := by
  apply mul_nonneg (by norm_num)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact weighted_nonneg 1 j (t+1) (‖z‖+R) u hu

theorem hermite_model_roots_real_simple (m : ℕ) (d w : ℂ) (hd : d ≠ 0)
    (hw : value m w/(m.factorial : ℂ)*d=0) :
    w.im=0 ∧ deriv (fun v : ℂ => value m v/(m.factorial : ℂ)*d) w ≠ 0 := by
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hroot : value m w=0 := (div_eq_zero_iff.mp ((mul_eq_zero.mp hw).resolve_right hd)).resolve_right hf
  refine ⟨roots_real m w hroot,?_⟩
  cases m with
  | zero => simp at hroot
  | succ n =>
    rw [((value_hasDerivAt n w).div_const ((n+1).factorial : ℂ) |>.mul_const d).deriv]
    apply mul_ne_zero _ hd
    apply div_ne_zero _ hf
    have he := derivative_ne_zero_at_root n w hroot
    rwa [(value_hasDerivAt n w).deriv] at he

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticAllOrders
