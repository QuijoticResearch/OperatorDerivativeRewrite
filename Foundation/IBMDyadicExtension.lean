import Foundation.IBMSmoothIncrementTails
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.Order.AtTopBotIxx

/-! Deterministic extension estimates for the existing IBM dyadic event.
No continuous modification is assumed in these estimates. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace OperatorDerivativeRewrite.Foundation.IBMDyadicExtension
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def index (l : ℕ) (x : UnitInterval) : ℕ := ⌊(2 : ℝ)^l * x.val⌋₊

def grid (a : ℝ) (l k : ℕ) : ℝ := a + (k : ℝ) / (2 : ℝ)^l

def rounded (G : ℝ → ℝ) (a : ℝ) (l : ℕ) (x : UnitInterval) : ℝ :=
  G (grid a l (index l x))

theorem index_le (l : ℕ) (x : UnitInterval) : index l x ≤ 2^l := by
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_of_le_one_right (by positivity) x.property.2

theorem index_refinement (l : ℕ) (x : UnitInterval) :
    index (l+1) x = 2 * index l x ∨ index (l+1) x = 2 * index l x + 1 := by
  have hdiv : index (l+1) x / 2 = index l x := by
    unfold index
    simpa only [pow_succ, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using
      Nat.mul_cast_floor_div_cancel (R := ℝ) (by decide : (2 : ℕ) ≠ 0)
        ((2 : ℝ)^l * x.val)
  have hmod := Nat.mod_lt (index (l+1) x) (by decide : 0 < 2)
  have hdecomp := Nat.mod_add_div (index (l+1) x) 2
  rw [hdiv] at hdecomp
  omega

theorem grid_refinement (a : ℝ) (l k : ℕ) : grid a (l+1) (2*k) = grid a l k := by
  unfold grid
  push_cast
  rw [pow_succ]
  field_simp

theorem rounded_step_le {G : ℝ → ℝ} {a : ℝ} {l : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ k : Fin (2^(l+1)),
      |G (grid a (l+1) (k.val+1)) - G (grid a (l+1) k.val)| ≤ δ)
    (x : UnitInterval) : dist (rounded G a l x) (rounded G a (l+1) x) ≤ δ := by
  rcases index_refinement l x with he | he
  · simp only [rounded, he, grid_refinement, dist_self]
    exact hδ
  · have hk : 2 * index l x < 2^(l+1) := by
      have hb := index_le (l+1) x
      rw [he] at hb
      omega
    have hh := h ⟨2 * index l x, hk⟩
    simpa only [rounded, he, grid_refinement, Real.dist_eq, abs_sub_comm] using hh

theorem rounded_cauchy {G : ℝ → ℝ} {a : ℝ}
    (h : ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) - G (grid a l k.val)| ≤ (3/4 : ℝ)^l)
    (x : UnitInterval) : CauchySeq (fun l => rounded G a l x) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hs : Summable (fun l => dist (rounded G a l x) (rounded G a (l+1) x)) := by
    rw [← summable_nat_add_iff N]
    apply Summable.of_nonneg_of_le (fun _ => dist_nonneg)
      (fun l => rounded_step_le (by positivity) (hN (l+N+1) (by omega)) x)
    have hg : Summable (fun l : ℕ => (3/4 : ℝ)^l) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (N+1)).mpr hg
  exact cauchySeq_of_summable_dist hs

def extension (G : ℝ → ℝ) (a : ℝ) (x : UnitInterval) : ℝ :=
  limsup (fun l => rounded G a l x) atTop

theorem extension_tendsto {G : ℝ → ℝ} {a : ℝ}
    (h : ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) - G (grid a l k.val)| ≤ (3/4 : ℝ)^l)
    (x : UnitInterval) :
    Tendsto (fun l => rounded G a l x) atTop (𝓝 (extension G a x)) := by
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (rounded_cauchy h x)
  simpa only [extension, hy.limsup_eq] using hy

/-- A uniform geometric tail bound, independent of the spatial point. -/
theorem extension_tail {G : ℝ → ℝ} {a : ℝ} {N l : ℕ}
    (h : ∀ m ≥ N, ∀ k : Fin (2^m),
      |G (grid a m (k.val+1)) - G (grid a m k.val)| ≤ (3/4 : ℝ)^m)
    (hl : N ≤ l) (x : UnitInterval) :
    dist (rounded G a l x) (extension G a x) ≤ 3 * (3/4 : ℝ)^l := by
  have he : ∀ᶠ m in atTop, ∀ k : Fin (2^m),
      |G (grid a m (k.val+1)) - G (grid a m k.val)| ≤ (3/4 : ℝ)^m :=
    eventually_atTop.mpr ⟨N, h⟩
  have ht : Tendsto (fun m => rounded G a (l+m) x) atTop (𝓝 (extension G a x)) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (extension_tendsto he x).comp (tendsto_add_atTop_nat l)
  have hb := dist_le_tsum_of_dist_le_of_tendsto₀
    (fun m : ℕ => (3/4 : ℝ)^(l+m+1))
    (fun m => rounded_step_le (by positivity) (h (l+m+1) (by omega)) x)
    (by
      have hg : Summable (fun m : ℕ => (3/4 : ℝ)^m) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (summable_nat_add_iff (l+1)).mpr hg) ht
  simp only [Nat.add_zero] at hb
  have hs : (∑' m : ℕ, (3/4 : ℝ)^(l+m+1)) = 3 * (3/4 : ℝ)^l := by
    simp_rw [pow_succ, pow_add, mul_assoc]
    rw [tsum_mul_left, tsum_mul_right,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  exact hb.trans_eq hs

theorem rounded_close {G : ℝ → ℝ} {a : ℝ} {l : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) - G (grid a l k.val)| ≤ δ)
    (x y : UnitInterval) (hxy : dist x y < 1 / (2 : ℝ)^l) :
    dist (rounded G a l x) (rounded G a l y) ≤ δ := by
  have hp : (0 : ℝ) < 2^l := by positivity
  have hab : |x.val-y.val| < 1 / (2 : ℝ)^l := hxy
  have hdiff := abs_lt.mp hab
  have hx : (0 : ℝ) ≤ 2^l * x.val := mul_nonneg hp.le x.property.1
  have hy : (0 : ℝ) ≤ 2^l * y.val := mul_nonneg hp.le y.property.1
  have hi : index l x ≤ index l y + 1 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt hx).mpr
    have hh := Nat.lt_floor_add_one ((2 : ℝ)^l * y.val)
    change 2^l * y.val < (index l y : ℝ) + 1 at hh
    push_cast
    have hh' := (mul_lt_mul_of_pos_left hdiff.2 hp)
    field_simp at hh'
    nlinarith
  have hj : index l y ≤ index l x + 1 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt hy).mpr
    have hh := Nat.lt_floor_add_one ((2 : ℝ)^l * x.val)
    change 2^l * x.val < (index l x : ℝ) + 1 at hh
    push_cast
    have hh' := (mul_lt_mul_of_pos_left hdiff.1 hp)
    field_simp at hh'
    nlinarith
  have hc : index l x = index l y ∨ index l y = index l x + 1 ∨
      index l x = index l y + 1 := by omega
  rcases hc with he | he | he
  · simp only [rounded, he, dist_self]
    exact hδ
  · have hk : index l x < 2^l := by have hb := index_le l y; omega
    simpa only [rounded, he, Real.dist_eq, abs_sub_comm] using h ⟨index l x, hk⟩
  · have hk : index l y < 2^l := by have hb := index_le l x; omega
    simpa only [rounded, he, Real.dist_eq] using h ⟨index l y, hk⟩

/-- The actual dyadic limit is continuous; the proof uses uniform tails and
adjacent-cell control, rather than an assumed continuity property. -/
theorem extension_continuous {G : ℝ → ℝ} {a : ℝ}
    (h : ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) - G (grid a l k.val)| ≤ (3/4 : ℝ)^l) :
    Continuous (extension G a) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  apply Metric.continuous_iff.mpr
  intro x ε hε
  have hz : Tendsto (fun l : ℕ => 7 * (3/4 : ℝ)^l) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3/4)
      (by norm_num : (3/4 : ℝ) < 1)).const_mul 7
  obtain ⟨l, hlN, hl⟩ := ((eventually_ge_atTop N).and
    (hz.eventually (eventually_lt_nhds hε))).exists
  refine ⟨1 / (2 : ℝ)^l, by positivity, ?_⟩
  intro y hy
  have hx := extension_tail hN hlN x
  have hy' := extension_tail hN hlN y
  have hc := rounded_close (by positivity) (hN l hlN) y x hy
  calc
    dist (extension G a y) (extension G a x) ≤
        dist (extension G a y) (rounded G a l y) +
        dist (rounded G a l y) (rounded G a l x) +
        dist (rounded G a l x) (extension G a x) := dist_triangle4 _ _ _ _
    _ ≤ 7 * (3/4 : ℝ)^l := by rw [dist_comm (extension G a y)]; linarith
    _ < ε := hl

open InfiniteGaussian IBMJointMollifierGaussian IBMSmoothIncrementTails

/-- Dyadic piecewise-linear interpolation of the actual node values. At the
right endpoint the interpolation coefficient is zero. -/
def linear (G : ℝ → ℝ) (a : ℝ) (l : ℕ) (x : UnitInterval) : ℝ :=
  rounded G a l x + ((2 : ℝ)^l * x.val - (index l x : ℝ)) *
    (G (grid a l (index l x+1)) - G (grid a l (index l x)))

theorem linear_rounded_le {G : ℝ → ℝ} {a : ℝ} {l : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) - G (grid a l k.val)| ≤ δ) (x : UnitInterval) :
    dist (linear G a l x) (rounded G a l x) ≤ δ := by
  have hp : (0 : ℝ) < 2^l := by positivity
  have hf := Nat.floor_le (mul_nonneg hp.le x.property.1)
  have hg := Nat.lt_floor_add_one ((2 : ℝ)^l * x.val)
  change (index l x : ℝ) ≤ (2 : ℝ)^l * x.val at hf
  change (2 : ℝ)^l * x.val < (index l x : ℝ)+1 at hg
  by_cases hk : index l x < 2^l
  · rw [linear, Real.dist_eq, add_sub_cancel_left, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ (2 : ℝ)^l*x.val-(index l x : ℝ))]
    calc
      _ ≤ 1 * |G (grid a l (index l x+1)) - G (grid a l (index l x))| := by
        gcongr; linarith
      _ ≤ δ := by simpa only [one_mul] using h ⟨index l x, hk⟩
  · have he : index l x = 2^l := le_antisymm (index_le l x) (by omega)
    have hx : x.val = 1 := by
      rw [he] at hf
      push_cast at hf
      nlinarith [x.property.2]
    simp [linear, hx, he, hδ]

theorem linear_tendstoUniformly {G : ℝ → ℝ} {a : ℝ}
    (h : ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) - G (grid a l k.val)| ≤ (3/4 : ℝ)^l) :
    TendstoUniformly (linear G a) (extension G a) atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hz : Tendsto (fun l : ℕ => 4 * (3/4 : ℝ)^l) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3/4)
      (by norm_num : (3/4 : ℝ) < 1)).const_mul 4
  filter_upwards [eventually_ge_atTop N, hz.eventually (eventually_lt_nhds hε)] with l hl he x
  have ht := extension_tail hN hl x
  have hp := linear_rounded_le (by positivity) (hN l hl) x
  calc
    dist (extension G a x) (linear G a l x) ≤
        dist (extension G a x) (rounded G a l x) +
        dist (rounded G a l x) (linear G a l x) := dist_triangle _ _ _
    _ ≤ 4 * (3/4 : ℝ)^l := by
      have ht' : dist (extension G a x) (rounded G a l x) ≤ 3 * (3/4 : ℝ)^l :=
        by simpa only [dist_comm] using ht
      have hp' : dist (rounded G a l x) (linear G a l x) ≤ (3/4 : ℝ)^l :=
        by simpa only [dist_comm] using hp
      linarith
    _ < ε := he

theorem gaussianTriple_linear_measurable (n : ℕ) (i : Fin 3) (z : ℤ)
    (l : ℕ) (x : UnitInterval) :
    Measurable (fun ω => linear (fun r => gaussianTriple n r i ω) z l x) := by
  apply Measurable.add
  · exact GaussianHilbertProcess.isonormal_measurable _
  · exact measurable_const.mul ((GaussianHilbertProcess.isonormal_measurable _).sub
      (GaussianHilbertProcess.isonormal_measurable _))

/-- The previously proved common event now gives actual convergence of every
rounded spatial sequence, simultaneously, including all uncountably many
points inside each unit interval. The quantifier over points is deterministic
inside the already constructed countable full-measure event. -/
theorem gaussianTriple_common_rounded_converges :
    ∀ᵐ ω ∂gaussianProduct, ∀ (n : ℕ) (i : Fin 3) (z : ℤ) (x : UnitInterval),
      ∃ y : ℝ, Tendsto (fun l => rounded (fun r => gaussianTriple n r i ω) z l x)
        atTop (𝓝 y) := by
  filter_upwards [gaussianTriple_common_dyadic_control] with ω hω
  intro n i z x
  apply cauchySeq_tendsto_of_complete
  apply rounded_cauchy
  filter_upwards [hω n i z] with l hl k
  exact (hl k).le

theorem grid_index_tendsto (a : ℝ) (x : UnitInterval) :
    Tendsto (fun l => grid a l (index l x)) atTop (𝓝 (a+x.val)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hz : Tendsto (fun l : ℕ => (1/2 : ℝ)^l) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply tendsto_const_nhds.squeeze hz (fun _ => dist_nonneg) (fun l => ?_)
  have hp : (0 : ℝ) < 2^l := by positivity
  have hf := Nat.floor_le (mul_nonneg hp.le x.property.1)
  have hg := Nat.lt_floor_add_one ((2 : ℝ)^l * x.val)
  change (index l x : ℝ) ≤ (2 : ℝ)^l * x.val at hf
  change (2 : ℝ)^l * x.val < (index l x : ℝ) + 1 at hg
  rw [grid, Real.dist_eq, abs_of_nonpos (by
    have hh := (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hf)
    linarith), one_div_pow]
  have hh : ((2 : ℝ)^l * x.val - (index l x : ℝ)) / (2 : ℝ)^l <
      1 / (2 : ℝ)^l :=
    (div_lt_div_iff_of_pos_right hp).mpr (by linarith)
  have he : (2 : ℝ)^l * x.val / (2 : ℝ)^l = x.val := by field_simp
  rw [sub_div, he] at hh
  linarith

def good (ω : SampleSpace) : Prop :=
  ∀ (n : ℕ) (i : Fin 3) (z : ℤ), ∃ N : ℕ, ∀ l ≥ N, ∀ k : Fin (2^l),
    |gaussianTriple n (grid z l (k.val+1)) i ω -
      gaussianTriple n (grid z l k.val) i ω| < (3/4 : ℝ)^l

theorem good_ae : ∀ᵐ ω ∂gaussianProduct, good ω := by
  filter_upwards [gaussianTriple_common_dyadic_control] with ω hω
  intro n i z
  exact eventually_atTop.mp (hω n i z)

theorem good_measurableSet : MeasurableSet {ω | good ω} := by
  unfold good
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.iInter; intro n
  apply MeasurableSet.iInter; intro i
  apply MeasurableSet.iInter; intro z
  apply MeasurableSet.iUnion; intro N
  apply MeasurableSet.iInter; intro l
  apply MeasurableSet.iInter; intro _hl
  apply MeasurableSet.iInter; intro k
  have hm1 : Measurable (gaussianTriple n (grid z l (k.val+1)) i) :=
    GaussianHilbertProcess.isonormal_measurable _
  have hm2 : Measurable (gaussianTriple n (grid z l k.val) i) :=
    GaussianHilbertProcess.isonormal_measurable _
  exact measurableSet_lt (continuous_abs.measurable.comp (hm1.sub hm2)) measurable_const

theorem local_extension_measurable (n : ℕ) (i : Fin 3) (z : ℤ) (x : UnitInterval) :
    Measurable (fun ω => extension (fun r => gaussianTriple n r i ω) z x) := by
  apply Measurable.limsup
  intro l
  exact GaussianHilbertProcess.isonormal_measurable _

def localPath (n : ℕ) (i : Fin 3) (z : ℤ) (ω : SampleSpace) : C(UnitInterval, ℝ) :=
  if h : good ω then
    ⟨extension (fun r => gaussianTriple n r i ω) z,
      extension_continuous (by
        obtain ⟨N, hN⟩ := h n i z
        exact eventually_atTop.mpr ⟨N, fun l hl k => (hN l hl k).le⟩)⟩
  else 0

theorem localPath_measurable (n : ℕ) (i : Fin 3) (z : ℤ) :
    Measurable (localPath n i z) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro x
  have he : (fun ω => localPath n i z ω x) =
      fun ω => if good ω then extension (fun r => gaussianTriple n r i ω) z x else 0 := by
    funext ω
    by_cases h : good ω <;> simp [localPath, h]
  rw [he]
  exact Measurable.ite good_measurableSet (local_extension_measurable n i z x) measurable_const

theorem localPath_ae_tendsto (n : ℕ) (i : Fin 3) (z : ℤ) (x : UnitInterval) :
    ∀ᵐ ω ∂gaussianProduct,
      Tendsto (fun l => rounded (fun r => gaussianTriple n r i ω) z l x)
        atTop (𝓝 (localPath n i z ω x)) := by
  filter_upwards [good_ae] with ω hω
  simp only [localPath, dite_eq_left hω, ContinuousMap.coe_mk]
  apply extension_tendsto
  obtain ⟨N, hN⟩ := hω n i z
  exact eventually_atTop.mpr ⟨N, fun l hl k => (hN l hl k).le⟩

theorem derivativeKernel_regular (n : ℕ) (i : Fin 3) :
    HasCompactSupport (derivativeKernel n i) ∧ ContDiff ℝ 1 (derivativeKernel n i) := by
  have hc := IBMMollifier.kernel_compactSupport n
  have h := IBMMollifier.kernel_smooth n
  have hd := (contDiff_infty_iff_deriv.mp h).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  unfold derivativeKernel
  split_ifs
  · exact ⟨hc, h.of_le (by norm_num)⟩
  · exact ⟨hc.deriv, hd.of_le (by norm_num)⟩
  · exact ⟨hc.deriv.deriv, hdd.of_le (by norm_num)⟩

/-- Each continuous local path modifies the original Gaussian coordinate
family. Equality is almost sure at each fixed coordinate, with no uncountable
intersection of coordinate equalities. -/
theorem localPath_coordinate_ae (n : ℕ) (i : Fin 3) (z : ℤ) (x : UnitInterval) :
    (fun ω => localPath n i z ω x) =ᵐ[gaussianProduct]
      gaussianTriple n ((z : ℝ)+x.val) i := by
  let F : ℕ → InfiniteGaussian.GaussianL2 := fun l =>
    IBMContinuousScenery.wholeLineScenery (derivativeKernel n i) (grid z l (index l x))
  let H : InfiniteGaussian.GaussianL2 :=
    IBMContinuousScenery.wholeLineScenery (derivativeKernel n i) ((z : ℝ)+x.val)
  have hr := derivativeKernel_regular n i
  have hc : Continuous (IBMContinuousScenery.wholeLineScenery (derivativeKernel n i)) :=
    continuous_iff_continuousAt.mpr fun r =>
      (IBMContinuousScenery.wholeLineScenery_hasDerivAt hr.1 hr.2 r).continuousAt
  have ht : Tendsto F atTop (𝓝 H) := hc.continuousAt.tendsto.comp (grid_index_tendsto z x)
  have hm := tendstoInMeasure_of_tendsto_Lp ht
  have he : ∀ r, (IBMContinuousScenery.wholeLineScenery (derivativeKernel n i) r :
      SampleSpace → ℝ) = gaussianTriple n r i := by
    intro r
    rw [IBMJointMollifierGaussian.wholeLineScenery_eq_sourceEmbedding]
    rfl
  have hm' : TendstoInMeasure gaussianProduct
      (fun l ω => rounded (fun r => gaussianTriple n r i ω) z l x)
      atTop (gaussianTriple n ((z : ℝ)+x.val) i) := by
    simpa only [F, H, he, rounded] using hm
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_ae
      (fun l => (GaussianHilbertProcess.isonormal_measurable _).aestronglyMeasurable)
      (localPath_ae_tendsto n i z x)) hm'

theorem localPath_jointly_measurable (n : ℕ) (i : Fin 3) (z : ℤ) :
    Measurable (fun p : SampleSpace × UnitInterval => localPath n i z p.1 p.2) :=
  continuous_eval.measurable.comp ((localPath_measurable n i z).comp measurable_fst
    |>.prodMk measurable_snd)

def zeroPoint : UnitInterval := ⟨0, by constructor <;> norm_num⟩
def onePoint : UnitInterval := ⟨1, by constructor <;> norm_num⟩

theorem rounded_zero (G : ℝ → ℝ) (a : ℝ) (l : ℕ) :
    rounded G a l zeroPoint = G a := by
  simp [rounded, index, zeroPoint, grid]

theorem rounded_one (G : ℝ → ℝ) (a : ℝ) (l : ℕ) :
    rounded G a l onePoint = G (a+1) := by
  have hi : index l onePoint = 2^l := by
    simp only [index, onePoint, mul_one]
    exact_mod_cast (Nat.floor_natCast (2^l) : ⌊((2^l : ℕ) : ℝ)⌋₊ = 2^l)
  simp only [rounded, hi, grid, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_self (by positivity : (2 : ℝ)^l ≠ 0)]

theorem localPath_zero (n : ℕ) (i : Fin 3) (z : ℤ) (ω : SampleSpace) :
    localPath n i z ω zeroPoint = if good ω then gaussianTriple n z i ω else 0 := by
  by_cases hg : good ω
  · simp only [localPath, dite_eq_left hg, ContinuousMap.coe_mk, ite_eq_left hg, extension]
    simp only [rounded_zero]
    exact tendsto_const_nhds.limsup_eq
  · simp [localPath, hg]

theorem localPath_one (n : ℕ) (i : Fin 3) (z : ℤ) (ω : SampleSpace) :
    localPath n i z ω onePoint = if good ω then gaussianTriple n ((z : ℝ)+1) i ω else 0 := by
  by_cases hg : good ω
  · simp only [localPath, dite_eq_left hg, ContinuousMap.coe_mk, ite_eq_left hg, extension]
    simp only [rounded_one]
    exact tendsto_const_nhds.limsup_eq
  · simp [localPath, hg]

/-- The neighboring interval constructions agree on their common endpoint
for every sample, including the zero path selected off the good event. -/
theorem localPath_neighbor (n : ℕ) (i : Fin 3) (z : ℤ) (ω : SampleSpace) :
    localPath n i z ω onePoint = localPath n i (z+1) ω zeroPoint := by
  rw [localPath_one, localPath_zero]
  push_cast
  rfl

def window (z : ℤ) : Set ℝ := Set.Icc (z : ℝ) ((z : ℝ)+1)

def chart (z : ℤ) (x : window z) : UnitInterval :=
  ⟨x.val-z, by constructor <;> linarith [x.property.1, x.property.2]⟩

theorem chart_continuous (z : ℤ) : Continuous (chart z) :=
  Continuous.subtype_mk (continuous_subtype_val.sub continuous_const) _

theorem windows_cover : (⋃ z : ℤ, window z) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro r
  apply Set.mem_iUnion.mpr
  exact ⟨⌊r⌋, Int.floor_le r, (Int.lt_floor_add_one r).le⟩

theorem windowPath_compatible (n : ℕ) (i : Fin 3) (ω : SampleSpace)
    (z w : ℤ) (r : ℝ) (hz : r ∈ window z) (hw : r ∈ window w) :
    localPath n i z ω (chart z ⟨r, hz⟩) =
      localPath n i w ω (chart w ⟨r, hw⟩) := by
  have ordered : ∀ z w : ℤ, ∀ hz : r ∈ window z, ∀ hw : r ∈ window w, z < w →
      localPath n i z ω (chart z ⟨r, hz⟩) =
        localPath n i w ω (chart w ⟨r, hw⟩) := by
    intro z w hz hw hzw
    have hstep : (z : ℝ)+1 ≤ (w : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hzw)
    have hr : r = (w : ℝ) := by linarith [hz.2, hw.1]
    have he : (z : ℝ)+1 = (w : ℝ) := by linarith [hz.2, hw.1]
    have hc1 : chart z ⟨r, hz⟩ = onePoint := by
      apply Subtype.ext
      change r-(z : ℝ) = 1
      linarith
    have hc0 : chart w ⟨r, hw⟩ = zeroPoint := by
      apply Subtype.ext
      change r-(w : ℝ) = 0
      linarith
    rw [hc1, hc0, localPath_one, localPath_zero, he]
  rcases lt_trichotomy z w with h | h | h
  · exact ordered z w hz hw h
  · subst w; rfl
  · exact (ordered w z hw hz h).symm

def field (n : ℕ) (i : Fin 3) (ω : SampleSpace) : ℝ → ℝ :=
  Set.liftCover window (fun z r => localPath n i z ω (chart z r))
    (windowPath_compatible n i ω) windows_cover

/-- Independence of which closed unit interval is used, including endpoints. -/
theorem field_on_window (n : ℕ) (i : Fin 3) (ω : SampleSpace) (z : ℤ)
    (r : ℝ) (hr : r ∈ window z) :
    field n i ω r = localPath n i z ω (chart z ⟨r, hr⟩) :=
  Set.liftCover_of_mem hr

theorem field_continuous (n : ℕ) (i : Fin 3) (ω : SampleSpace) :
    Continuous (field n i ω) := by
  have hu : Tendsto (fun z : ℤ => (z : ℝ)+1) atBot atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [((tendsto_intCast_atBot_iff.mpr tendsto_id) :
      Tendsto (fun z : ℤ => (z : ℝ)) atBot atBot).eventually
        (eventually_le_atBot (b-1))] with z hz
    linarith
  have hloc : LocallyFinite window :=
    locallyFinite_Icc_of_tendsto tendsto_intCast_atTop_atTop hu
  apply hloc.continuous windows_cover (fun _ => isClosed_Icc)
  intro z
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (Set.domRestrict (window z) (field n i ω)) =
      fun r => localPath n i z ω (chart z r) := by
    funext r
    exact field_on_window n i ω z r r.property
  rw [he]
  exact (localPath n i z ω).continuous.comp (chart_continuous z)

theorem field_coordinate_measurable (n : ℕ) (i : Fin 3) (r : ℝ) :
    Measurable (fun ω => field n i ω r) := by
  have hr : r ∈ window ⌊r⌋ := ⟨Int.floor_le r, (Int.lt_floor_add_one r).le⟩
  have he : (fun ω => field n i ω r) =
      fun ω => localPath n i ⌊r⌋ ω (chart ⌊r⌋ ⟨r, hr⟩) := by
    funext ω; exact field_on_window n i ω ⌊r⌋ r hr
  rw [he]
  exact (ContinuousMap.measurable_eval _).comp (localPath_measurable n i ⌊r⌋)

/-- An actual jointly measurable real random field on the original Gaussian
source, continuous for every sample after setting the exceptional paths to zero. -/
theorem field_jointly_measurable (n : ℕ) (i : Fin 3) :
    Measurable (fun p : ℝ × SampleSpace => field n i p.2 p.1) :=
  measurable_uncurry_of_continuous_of_measurable (field_continuous n i)
    (field_coordinate_measurable n i)

theorem field_coordinate_ae (n : ℕ) (i : Fin 3) (r : ℝ) :
    (fun ω => field n i ω r) =ᵐ[gaussianProduct] gaussianTriple n r i := by
  have hr : r ∈ window ⌊r⌋ := ⟨Int.floor_le r, (Int.lt_floor_add_one r).le⟩
  have he : (⌊r⌋ : ℝ) + (chart ⌊r⌋ ⟨r, hr⟩).val = r := by simp [chart]
  have h := localPath_coordinate_ae n i ⌊r⌋ (chart ⌊r⌋ ⟨r, hr⟩)
  rw [he] at h
  filter_upwards [h] with ω hω
  exact (field_on_window n i ω ⌊r⌋ r hr).trans hω

def path (n : ℕ) (i : Fin 3) (ω : SampleSpace) : C(ℝ, ℝ) :=
  ⟨field n i ω, field_continuous n i ω⟩

theorem path_measurable (n : ℕ) (i : Fin 3) : Measurable (path n i) :=
  ContinuousMap.measurable_iff_eval.mpr (field_coordinate_measurable n i)

/-- All finite families, including different mollifier scales, derivative
orders and spatial points, preserve the original joint Gaussian structure. -/
theorem field_isGaussianProcess : ProbabilityTheory.IsGaussianProcess
    (fun q : ℕ × Fin 3 × ℝ => fun ω => field q.1 q.2.1 ω q.2.2) gaussianProduct := by
  have h := GaussianHilbertProcess.isonormal_isGaussianProcess.comp_right
    (fun q : ℕ × Fin 3 × ℝ => wholeLineDirection (derivativeKernel q.1 q.2.1) q.2.2)
  apply h.congr
  intro q
  exact (field_coordinate_ae q.1 q.2.1 q.2.2).symm

end OperatorDerivativeRewrite.Foundation.IBMDyadicExtension
