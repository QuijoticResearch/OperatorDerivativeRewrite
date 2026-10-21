import Foundation.RiemannQuadraticCluster
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-! Actual quadratic-flow zero confinement and exhaustive local Hermite clusters.
A fixed-budget joint remainder and the exact monic Hermite product exclude an
annulus. Compact positive-gap exclusion and existing local uniqueness complete
the exact finite cluster count. Constants are local; no global strip bound follows. -/
noncomputable section
open Set Metric Complex Filter Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticConfinement
open RiemannQuadraticCluster RiemannQuadraticHermite RiemannEvenFlow
open RiemannQuadraticZeroTransfer

theorem value_eq_prod (m : ℕ) (w : ℂ) :
    value m w=∏ a ∈ RiemannQuadraticCluster.roots m, (w-a) := by
  classical
  rw [← polynomial_eval,(IsAlgClosed.splits (polynomial m)).eval_eq_prod_roots_of_monic
    (polynomial_monic m)]
  rw [Finset.prod_eq_multiset_prod]
  simp only [RiemannQuadraticCluster.roots,Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (polynomial_roots_nodup m)]

def rootNormBound (m : ℕ) : ℝ := 1+∑ a ∈ RiemannQuadraticCluster.roots m, ‖a‖

theorem rootNormBound_one_le (m : ℕ) : 1 ≤ rootNormBound m := by
  have hs : 0 ≤ ∑ a ∈ RiemannQuadraticCluster.roots m, ‖a‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  dsimp [rootNormBound]
  linarith

theorem root_norm_le (m : ℕ) (a : ℂ) (ha : a ∈ RiemannQuadraticCluster.roots m) :
    ‖a‖ ≤ rootNormBound m := by
  have hs := Finset.single_le_sum (fun b (_ : b ∈ RiemannQuadraticCluster.roots m) => norm_nonneg b) ha
  dsimp [rootNormBound]
  linarith

theorem value_norm_lower (m : ℕ) (w : ℂ) (hw : 2*rootNormBound m ≤ ‖w‖) :
    (‖w‖/2)^m ≤ ‖value m w‖ := by
  classical
  have hf (a : ℂ) (ha : a ∈ RiemannQuadraticCluster.roots m) : ‖w‖/2 ≤ ‖w-a‖ := by
    have ht := norm_add_le (w-a) a
    rw [sub_add_cancel] at ht
    have hn := root_norm_le m a ha
    linarith
  calc
    _ = ∏ a ∈ RiemannQuadraticCluster.roots m, ‖w‖/2 := by
      rw [Finset.prod_const,RiemannQuadraticCluster.card_roots]
    _ ≤ ∏ a ∈ RiemannQuadraticCluster.roots m, ‖w-a‖ :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) hf
    _ = _ := by rw [value_eq_prod,norm_prod]

theorem homogeneous_leading_lower (m : ℕ) (h : ℝ) (v d : ℂ) (hne : h ≠ 0)
    (hw : 2*rootNormBound m ≤ ‖v/(h : ℂ)‖) :
    (‖d‖/((m.factorial : ℝ)*2^m))*‖v‖^m ≤
      ‖(h : ℂ)^m*(value m (v/(h : ℂ))/(m.factorial : ℂ)*d)‖ := by
  have hh : |h| ≠ 0 := abs_ne_zero.mpr hne
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hq := value_norm_lower m (v/(h : ℂ)) hw
  have he : |h|^m*((‖v/(h : ℂ)‖/2)^m/(m.factorial : ℝ)*‖d‖)=
      (‖d‖/((m.factorial : ℝ)*2^m))*‖v‖^m := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
    simp only [div_pow]
    field_simp
  calc
    _ = |h|^m*((‖v/(h : ℂ)‖/2)^m/(m.factorial : ℝ)*‖d‖) := he.symm
    _ ≤ |h|^m*(‖value m (v/(h : ℂ))‖/(m.factorial : ℝ)*‖d‖) := by gcongr
    _ = _ := by
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,norm_mul,norm_div,Complex.norm_natCast]

theorem actual_annular_confinement (m : ℕ) (t : ℝ) (z : ℂ)
    (hv : ∀ n < m, iteratedDeriv n (flow 1 t) z=0)
    (hD : iteratedDeriv m (flow 1 t) z ≠ 0) :
    ∃ δ > 0, ∃ R ≥ 1, ∀ h : ℝ, h ≠ 0 → |h| ≤ δ →
      ∀ v : ℂ, ‖v‖ ≤ δ → flow 1 (t+h^2) (z+v)=0 → ‖v‖ < R*|h| := by
  let d := iteratedDeriv m (flow 1 t) z
  let B := RiemannQuadraticAllOrders.budget 0 t z 1
  let k := ‖d‖/((m.factorial : ℝ)*2^m)
  let E := B*2^(m+1)
  let R := max 1 (2*rootNormBound m)
  let δ := min (1/4 : ℝ) (k/(2*(E+1)))
  have hB : 0 ≤ B := RiemannQuadraticAllOrders.budget_nonneg 0 t z 1
  have hd : 0 < ‖d‖ := norm_pos_iff.mpr hD
  have hf : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hk : 0 < k := by dsimp [k]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ4 : δ ≤ 1/4 := min_le_left _ _
  have hδsmall : δ ≤ k/(2*(E+1)) := min_le_right _ _
  have hcoef : E*δ ≤ k/2 := by
    have he := (le_div_iff₀ (by positivity : (0 : ℝ)<2*(E+1))).mp hδsmall
    nlinarith
  refine ⟨δ,hδ,R,le_max_left _ _,?_⟩
  intro h hne hh v hδv hz
  by_contra hbad
  have hann : R*|h| ≤ ‖v‖ := le_of_not_gt hbad
  have hR : 1 ≤ R := le_max_left _ _
  have hscale : |h| ≤ ‖v‖ := by nlinarith [abs_nonneg h]
  have hvpos : 0 < ‖v‖ := (abs_pos.mpr hne).trans_le hscale
  have hw : 2*rootNormBound m ≤ ‖v/(h : ℂ)‖ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
    apply (le_div_iff₀ (abs_pos.mpr hne)).mpr
    have hR2 : 2*rootNormBound m ≤ R := le_max_right _ _
    nlinarith [abs_nonneg h]
  have hl := homogeneous_leading_lower m h v d hne hw
  have hp := physical_multiplicity_remainder m t h z v hv hne (by linarith)
  rw [hz,zero_sub,norm_neg] at hp
  have hpow : (|h|+‖v‖)^(m+1) ≤ (2*‖v‖)^(m+1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (m+1)
  have hu : ‖(h : ℂ)^m*(value m (v/(h : ℂ))/(m.factorial : ℂ)*d)‖ ≤
      E*δ*‖v‖^m := by
    calc
      _ ≤ B*(|h|+‖v‖)^(m+1) := hp
      _ ≤ B*(2*‖v‖)^(m+1) := mul_le_mul_of_nonneg_left hpow hB
      _ = E*‖v‖*‖v‖^m := by dsimp [E]; rw [mul_pow,pow_succ]; ring
      _ ≤ E*δ*‖v‖^m := by gcongr
  have hmpos : 0 < ‖v‖^m := pow_pos hvpos m
  have hc := mul_le_mul_of_nonneg_right hcoef hmpos.le
  change k*‖v‖^m ≤ _ at hl
  have hpositive : 0 < k*‖v‖^m := mul_pos hk hmpos
  nlinarith

theorem actual_exact_cluster (m : ℕ) (t : ℝ) (z : ℂ)
    (hv : ∀ n < m, iteratedDeriv n (flow 1 t) z=0)
    (hD : iteratedDeriv m (flow 1 t) z ≠ 0) :
    ∃ δ > 0, ∀ᶠ h : ℝ in 𝓝[≠] 0, ∃ S : Finset ℂ, S.card=m ∧
      (∀ ζ : ℂ, ζ ∈ S ↔ ζ ∈ closedBall z δ ∧ flow 1 (t+h^2) ζ=0) ∧
      ∀ ζ ∈ S, deriv (flow 1 (t+h^2)) ζ ≠ 0 ∧ (z.im=0 → ζ.im=0) := by
  classical
  obtain ⟨δ,hδ,R,hR,hconf⟩ := actual_annular_confinement m t z hv hD
  let I := {a : ℂ // a ∈ RiemannQuadraticCluster.roots m}
  let : Fintype I := inferInstance
  choose r hr C hC hs using (fun a : I => actual_unique_simple_near_model_root
    m t z a hv hD ((RiemannQuadraticCluster.mem_roots m a).mp a.property))
  let W : ℝ → I → ℂ := fun h a =>
    if he : ∃ w, w ∈ closedBall (a : ℂ) (r a) ∧ flow 1 (t+h^2) (z+(h : ℂ)*w)=0
    then Classical.choose he else a
  let U : Set ℂ := ⋃ a : I, ball (a : ℂ) (r a)
  let K : Set ℂ := closedBall (0 : ℂ) R ∩ Uᶜ
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_ball)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_right hU.isClosed_compl
  have hmodel : ∀ w ∈ K, model m t z w ≠ 0 := by
    intro w hw hz
    have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hq : value m w=0 :=
      (div_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_right hD)).resolve_right hf
    let a : I := ⟨w,(RiemannQuadraticCluster.mem_roots m w).mpr hq⟩
    have hmem : w ∈ U := mem_iUnion.mpr ⟨a,mem_ball_self (hr a)⟩
    exact hw.2 hmem
  obtain ⟨ε,hε,hgap⟩ := hK.exists_forall_le'
    (model_differentiable m t z).continuous.norm.continuousOn
    (fun w hw => norm_pos_iff.mpr (hmodel w hw))
  have huniform := (Metric.tendstoUniformlyOn_iff.mp
    (RiemannQuadraticAllOrders.multiplicity_uniform_on_disk m t R z hv)) ε hε
  have hall := Filter.eventually_all.mpr hs
  have habs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hall,huniform,habs.eventually (Iio_mem_nhds hδ),self_mem_nhdsWithin,
    at_least_m_simple_zeros_near m t z hv hD δ hδ] with h hlocal hu hh hne hlow
  have hne' : h ≠ 0 := by simpa using hne
  have hc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne'
  let T : Finset ℂ := Finset.univ.image (fun a : I => z+(h : ℂ)*W h a)
  have hupper : ∀ ζ ∈ closedBall z δ, flow 1 (t+h^2) ζ=0 → ζ ∈ T := by
    intro ζ hball hz
    let w := (ζ-z)/(h : ℂ)
    have hwpoint : z+(h : ℂ)*w=ζ := by dsimp [w]; field_simp; ring
    have hδv : ‖ζ-z‖ ≤ δ := by simpa only [mem_closedBall,dist_eq_norm] using hball
    have hvconf := hconf h hne' hh.le (ζ-z) hδv (by simpa only [add_sub_cancel] using hz)
    have hwR : ‖w‖ ≤ R := by
      dsimp [w]
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
      exact ((div_lt_iff₀ (abs_pos.mpr hne')).mpr hvconf).le
    have hzero : flow 1 (t+h^2) (z+(h : ℂ)*w)=0 := by rwa [hwpoint]
    have hs0 : scaled m t z h w=0 := (scaled_eq_zero_iff m t z h hne' w).mpr hzero
    have hwU : w ∈ U := by
      by_contra hn
      have hwK : w ∈ K := ⟨mem_closedBall_zero_iff.mpr hwR,hn⟩
      have hd := hu w hwR
      change dist (model m t z w) (scaled m t z h w) < ε at hd
      rw [hs0,dist_zero_right] at hd
      linarith [hgap w hwK]
    obtain ⟨a,ha⟩ := mem_iUnion.mp hwU
    have hchosen : W h a ∈ closedBall (a : ℂ) (r a) ∧
        flow 1 (t+h^2) (z+(h : ℂ)*W h a)=0 := by
      have hex := (hlocal a).1.exists
      dsimp only [W]
      rw [dite_eq_left hex]
      exact Classical.choose_spec hex
    have heq : w=W h a := (hlocal a).1.unique ⟨ball_subset_closedBall ha,hzero⟩ hchosen
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_univ _,?_⟩
    rw [← heq,hwpoint]
  have hcardT : T.card ≤ m := by
    calc
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = Fintype.card I := Finset.card_univ
      _ = m := by simpa only [I,Fintype.card_coe] using RiemannQuadraticCluster.card_roots m
  obtain ⟨S,hcard,hS⟩ := hlow
  have hST : S ⊆ T := by
    intro ζ hζ
    exact hupper ζ (ball_subset_closedBall (hS ζ hζ).1) (hS ζ hζ).2.1
  have hEq : S=T := Finset.eq_of_subset_of_card_le hST (by rwa [hcard])
  refine ⟨S,hcard,?_,?_⟩
  · intro ζ
    constructor
    · intro hζ
      exact ⟨ball_subset_closedBall (hS ζ hζ).1,(hS ζ hζ).2.1⟩
    · rintro ⟨hball,hzero⟩
      rw [hEq]
      exact hupper ζ hball hzero
  · intro ζ hζ
    exact ⟨(hS ζ hζ).2.2.1,(hS ζ hζ).2.2.2⟩

theorem every_actual_zero_has_exact_simple_cluster (t : ℝ) (z : ℂ) (hz : flow 1 t z=0) :
    ∃ m : ℕ, 0 < m ∧ ∃ δ > 0, ∀ᶠ h : ℝ in 𝓝[≠] 0, ∃ S : Finset ℂ, S.card=m ∧
      (∀ ζ : ℂ, ζ ∈ S ↔ ζ ∈ closedBall z δ ∧ flow 1 (t+h^2) ζ=0) ∧
      ∀ ζ ∈ S, deriv (flow 1 (t+h^2)) ζ ≠ 0 ∧ (z.im=0 → ζ.im=0) := by
  obtain ⟨m,hm,hv,hD⟩ := actual_finite_multiplicity t z hz
  exact ⟨m,hm,actual_exact_cluster m t z hv hD⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticConfinement
