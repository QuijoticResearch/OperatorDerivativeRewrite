import Foundation.RiemannQuadraticAllOrders
import Foundation.RiemannQuarticFrequencyBranch
import Foundation.RiemannEvenWindowZeros
import Mathlib.Analysis.Analytic.Order

/-! Actual local quadratic-flow zero branches from the verified Hermite limit.
The existing scalar-ball surjectivity/injectivity machinery and Cauchy estimates
supply existence, uniqueness, simplicity and quantitative displacement. Conjugation
proves real splitting at a real original base point. Exhaustive counts and global
strip contraction are separate obligations. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticZeroTransfer
open RiemannQuadraticAllOrders RiemannQuadraticHermite RiemannEvenFlow

theorem local_derivative_bound (f g : ℂ → ℂ) (b d : ℂ) (r ε : ℝ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hr : 0 < r)
    (hsmall : ε ≤ ‖d‖*r/4)
    (hgder : ∀ w ∈ closedBall b r, ‖deriv g w-d‖ ≤ ‖d‖/4)
    (hclose : ∀ w ∈ closedBall b (2*r), ‖f w-g w‖ ≤ ε) :
    ∀ w ∈ closedBall b r, ‖deriv f w-d‖ ≤ ‖d‖/2 := by
  intro w hw
  have hsub : closedBall w r ⊆ closedBall b (2*r) := by
    intro v hv
    apply mem_closedBall.mpr
    have hv' := mem_closedBall.mp hv
    have hw' := mem_closedBall.mp hw
    linarith [dist_triangle v w b]
  have he := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (DifferentiableOn.diffContOnCl (hf.sub hg).differentiableOn)
    (fun v hv => hclose v (hsub (sphere_subset_closedBall hv)))
  change ‖deriv (f-g) w‖ ≤ ε/r at he
  rw [deriv_sub (hf w) (hg w)] at he
  have hε : ε/r ≤ ‖d‖/4 := (div_le_iff₀ hr).mpr (by linarith)
  have htri := norm_add_le (deriv f w-deriv g w) (deriv g w-d)
  rw [sub_add_sub_cancel] at htri
  linarith [hgder w hw]

theorem existsUnique_simple_zero_of_close (f g : ℂ → ℂ) (b d : ℂ) (r ε : ℝ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hr : 0 < r) (hd : d ≠ 0)
    (hzero : g b=0) (hsmall : ε ≤ ‖d‖*r/4)
    (hgder : ∀ w ∈ closedBall b r, ‖deriv g w-d‖ ≤ ‖d‖/4)
    (hclose : ∀ w ∈ closedBall b (2*r), ‖f w-g w‖ ≤ ε) :
    (∃! w, w ∈ closedBall b r ∧ f w=0) ∧
      ∀ w ∈ closedBall b r, f w=0 → deriv f w ≠ 0 ∧ ‖w-b‖ ≤ 2*ε/‖d‖ := by
  have hb := local_derivative_bound f g b d r ε hf hg hr hsmall hgder hclose
  have hbase : ‖f b‖ ≤ ε := by
    simpa only [hzero,sub_zero] using hclose b (mem_closedBall_self (by positivity))
  have hsurj := RiemannQuarticQuantitativeSaddle.scalar_ball_surj f b d r hr.le hd
    (fun w _ => hf w) hb
  have hm : (0 : ℂ) ∈ closedBall (f b) (‖d‖*r/2) := by
    rw [mem_closedBall,dist_zero_left]
    nlinarith [mul_nonneg (norm_nonneg d) hr.le]
  obtain ⟨w,hw,hfw⟩ := hsurj hm
  constructor
  · refine ⟨w,⟨hw,hfw⟩,?_⟩
    intro v hv
    exact RiemannQuarticQuantitativeSaddle.scalar_ball_injective f b d r hd
      (fun w _ => hf w) hb hv.1 hw (hv.2.trans hfw.symm)
  · intro v hv hz
    constructor
    · intro he
      have hh := hb v hv
      rw [he,zero_sub,norm_neg] at hh
      have hn := norm_pos_iff.mpr hd
      linarith
    · have hl := RiemannQuarticFrequencyBranch.scalar_ball_lower_bound f b d r
        (fun w _ => hf w) hb v b hv (mem_closedBall_self hr.le)
      rw [hz,zero_sub,norm_neg] at hl
      apply (le_div_iff₀ (norm_pos_iff.mpr hd)).mpr
      nlinarith

def model (m : ℕ) (t : ℝ) (z w : ℂ) : ℂ :=
  value m w/(m.factorial : ℂ)*iteratedDeriv m (flow 1 t) z

def scaled (m : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ) : ℂ :=
  flow 1 (t+h^2) (z+(h : ℂ)*w)/(h : ℂ)^m

theorem model_differentiable (m : ℕ) (t : ℝ) (z : ℂ) : Differentiable ℂ (model m t z) := by
  intro w
  exact (((value_hasDerivAt_raise m w).div_const (m.factorial : ℂ)).mul_const
    (iteratedDeriv m (flow 1 t) z)).differentiableAt

theorem scaled_hasDerivAt (m : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ) :
    HasDerivAt (scaled m t z h)
      (deriv (flow 1 (t+h^2)) (z+(h : ℂ)*w)*(h : ℂ)/(h : ℂ)^m) w := by
  have ha : HasDerivAt (fun v : ℂ => z+(h : ℂ)*v) (h : ℂ) w := by
    simpa [Pi.add_def] using (hasDerivAt_const w z).add ((hasDerivAt_id w).const_mul (h : ℂ))
  have he := (((flow_differentiable 1 (t+h^2)) (z+(h : ℂ)*w)).hasDerivAt.comp w ha).div_const ((h : ℂ)^m)
  change HasDerivAt (fun v : ℂ => flow 1 (t+h^2) (z+(h : ℂ)*v)/(h : ℂ)^m)
    (deriv (flow 1 (t+h^2)) (z+(h : ℂ)*w)*(h : ℂ)/(h : ℂ)^m) w
  exact he

theorem scaled_eq_zero_iff (m : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (hne : h ≠ 0) (w : ℂ) :
    scaled m t z h w=0 ↔ flow 1 (t+h^2) (z+(h : ℂ)*w)=0 := by
  have hc : (h : ℂ)^m ≠ 0 := pow_ne_zero m (Complex.ofReal_ne_zero.mpr hne)
  simp only [scaled,div_eq_zero_iff,hc,or_false]

theorem actual_unique_simple_near_model_root (m : ℕ) (t : ℝ) (z a : ℂ)
    (hv : ∀ n < m, iteratedDeriv n (flow 1 t) z=0)
    (hD : iteratedDeriv m (flow 1 t) z ≠ 0) (ha : value m a=0) :
    ∃ r > 0, ∃ C ≥ 0, ∀ᶠ h : ℝ in 𝓝[≠] 0,
      (∃! w, w ∈ closedBall a r ∧ flow 1 (t+h^2) (z+(h : ℂ)*w)=0) ∧
      ∀ w ∈ closedBall a r, flow 1 (t+h^2) (z+(h : ℂ)*w)=0 →
        deriv (flow 1 (t+h^2)) (z+(h : ℂ)*w) ≠ 0 ∧ ‖w-a‖ ≤ C*|h| := by
  have hg := model_differentiable m t z
  have hzero : model m t z a=0 := by simp [model,ha]
  have hd : deriv (model m t z) a ≠ 0 :=
    (hermite_model_roots_real_simple m (iteratedDeriv m (flow 1 t) z) a hD hzero).2
  let d := deriv (model m t z) a
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hcont : ContinuousAt (deriv (model m t z)) a := (hg.analyticAt a).deriv.continuousAt
  obtain ⟨δ,hδ,hder⟩ := Metric.continuousAt_iff.mp hcont (‖d‖/4) (by positivity)
  let r := δ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hderball : ∀ w ∈ closedBall a r, ‖deriv (model m t z) w-d‖ ≤ ‖d‖/4 := by
    intro w hw
    have hw' := mem_closedBall.mp hw
    have hwd : dist w a < δ := by dsimp [r] at hw'; linarith
    simpa only [dist_eq_norm] using (hder hwd).le
  let R := ‖a‖+2*r
  let B := budget 0 t z R
  let C := 2*B/‖d‖
  have hB : 0 ≤ B := budget_nonneg 0 t z R
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨r,hr,C,hC,?_⟩
  have habs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun h : ℝ => B*|h|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul habs
  filter_upwards [habs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2)),
    hlim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ)<‖d‖*r/4)),
    self_mem_nhdsWithin] with h hh hsmall hne
  have hne' : h ≠ 0 := by simpa using hne
  have hclose : ∀ w ∈ closedBall a (2*r), ‖scaled m t z h w-model m t z w‖ ≤ B*|h| := by
    intro w hw
    have hwn : ‖w‖ ≤ R := by
      have hnorm := norm_add_le (w-a) a
      rw [sub_add_cancel] at hnorm
      have hw' : ‖w-a‖ ≤ 2*r := by simpa only [mem_closedBall,dist_eq_norm] using hw
      dsimp [R]
      linarith
    exact multiplicity_scaled_bound m t h R z w hv hh.le hne' hwn
  have hs := existsUnique_simple_zero_of_close (scaled m t z h) (model m t z)
    a d r (B*|h|) (fun w => (scaled_hasDerivAt m t z h w).differentiableAt)
    hg hr hd hzero hsmall.le hderball hclose
  constructor
  · simpa only [scaled_eq_zero_iff m t z h hne'] using hs.1
  · intro w hw hz
    have hscaled := hs.2 w hw ((scaled_eq_zero_iff m t z h hne' w).mpr hz)
    constructor
    · intro hact
      have he := (scaled_hasDerivAt m t z h w).deriv
      rw [hact,zero_mul,zero_div] at he
      exact hscaled.1 he
    · calc
        ‖w-a‖ ≤ 2*(B*|h|)/‖d‖ := hscaled.2
        _ = C*|h| := by dsimp [C]; ring

theorem actual_root_real_of_unique (t x h : ℝ) (a : ℂ) (r : ℝ)
    (ha : a.im=0)
    (hu : ∃! w, w ∈ closedBall a r ∧ flow 1 t ((x : ℂ)+(h : ℂ)*w)=0)
    (w : ℂ) (hw : w ∈ closedBall a r) (hz : flow 1 t ((x : ℂ)+(h : ℂ)*w)=0) :
    w.im=0 := by
  have hac : conj a=a := by apply Complex.ext <;> simp [ha]
  have hm : conj w ∈ closedBall a r := by
    have he : ‖conj w-a‖=‖w-a‖ := by
      rw [show conj w-a=conj (w-a) by rw [map_sub,hac],norm_conj]
    simpa only [mem_closedBall,dist_eq_norm,he] using hw
  have hp : (x : ℂ)+(h : ℂ)*conj w=conj ((x : ℂ)+(h : ℂ)*w) := by simp
  have hc : flow 1 t ((x : ℂ)+(h : ℂ)*conj w)=0 := by
    rw [hp,RiemannEvenWindowZeros.flow_conj,hz,map_zero]
  have he := hu.unique ⟨hw,hz⟩ ⟨hm,hc⟩
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  linarith

theorem actual_real_unique_simple_near_model_root (m : ℕ) (t x : ℝ) (a : ℂ)
    (hv : ∀ n < m, iteratedDeriv n (flow 1 t) (x : ℂ)=0)
    (hD : iteratedDeriv m (flow 1 t) (x : ℂ) ≠ 0) (ha : value m a=0) :
    ∃ r > 0, ∃ C ≥ 0, ∀ᶠ h : ℝ in 𝓝[≠] 0,
      (∃! w, w ∈ closedBall a r ∧ flow 1 (t+h^2) ((x : ℂ)+(h : ℂ)*w)=0) ∧
      ∀ w ∈ closedBall a r, flow 1 (t+h^2) ((x : ℂ)+(h : ℂ)*w)=0 →
        w.im=0 ∧ (((x : ℂ)+(h : ℂ)*w)).im=0 ∧
          deriv (flow 1 (t+h^2)) ((x : ℂ)+(h : ℂ)*w) ≠ 0 ∧ ‖w-a‖ ≤ C*|h| := by
  obtain ⟨r,hr,C,hC,hs⟩ := actual_unique_simple_near_model_root m t (x : ℂ) a hv hD ha
  refine ⟨r,hr,C,hC,hs.mono ?_⟩
  intro h hh
  refine ⟨hh.1,?_⟩
  intro w hw hz
  have him := actual_root_real_of_unique (t+h^2) x h a r (roots_real m a ha) hh.1 w hw hz
  refine ⟨him,?_,hh.2 w hw hz⟩
  simp [Complex.add_im,Complex.mul_im,him]

theorem physical_displacement_bound (z a w : ℂ) (h C : ℝ)
    (hb : ‖w-a‖ ≤ C*|h|) :
    ‖z+(h : ℂ)*w-(z+(h : ℂ)*a)‖ ≤ C*|h|^2 := by
  rw [show z+(h : ℂ)*w-(z+(h : ℂ)*a)=(h : ℂ)*(w-a) by ring,
    norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg h)
  convert hm using 1 <;> ring

theorem actual_finite_multiplicity (t : ℝ) (z : ℂ) (hz : flow 1 t z=0) :
    ∃ m : ℕ, 0 < m ∧ (∀ n < m, iteratedDeriv n (flow 1 t) z=0) ∧
      iteratedDeriv m (flow 1 t) z ≠ 0 := by
  have ha : AnalyticOnNhd ℂ (flow 1 t) univ :=
    (flow_differentiable 1 t).differentiableOn.analyticOnNhd isOpen_univ
  have hn : flow 1 t 0 ≠ 0 := by
    intro he
    have hp := RiemannEvenNormalizedCompact.actual_flow_zero_pos 1 t
    rw [he,Complex.zero_re] at hp
    linarith
  have h0 : analyticOrderAt (flow 1 t) 0 ≠ ⊤ := by
    rw [(ha 0 (mem_univ _)).analyticOrderAt_eq_zero.mpr hn]
    simp
  have hf : analyticOrderAt (flow 1 t) z ≠ ⊤ :=
    (ha.exists_analyticOrderAt_ne_top_iff_forall isConnected_univ).mp
      ⟨⟨0,mem_univ _⟩,h0⟩ ⟨z,mem_univ _⟩
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hf
  have hp := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (ha z (mem_univ _))).mp hm.symm
  refine ⟨m,?_,hp⟩
  by_contra he
  have hm0 : m=0 := by omega
  subst m
  exact hp.2 (by simpa using hz)

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticZeroTransfer
