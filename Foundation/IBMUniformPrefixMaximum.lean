import Foundation.IBMUniformPrefixQuartic

/-! Uniform-in-prefix actual IBM quartic variation. Positivity bridges finitely
many deterministic coarse prefixes to every prefix of the same uniform grid. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformPrefixMaximum
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformSubfamilyQuartic
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def width (N K : ℕ) : ℕ := N / K + 1
def node (N K j : ℕ) : ℕ := min (j * width N K) N

theorem node_le (N K j : ℕ) : node N K j ≤ N := Nat.min_le_right _ _

/-- Rounded blocks cover every prefix, including both endpoints. Their index
count is fixed by K, not by the increasing full-grid size N. -/
theorem cover (N K : ℕ) (hK : 0 < K) (m : ℕ) (hm : m ≤ N) :
    ∃ j < K, node N K j ≤ m ∧ m ≤ node N K (j + 1) ∧
      node N K (j + 1) ≤ node N K j + width N K := by
  let L := width N K
  have hL : 0 < L := Nat.zero_lt_succ _
  have hN : N < K * L := Nat.lt_mul_div_succ N hK
  have hj : m / L < K := (Nat.div_lt_iff_lt_mul hL).mpr (hm.trans_lt hN)
  have hl : m / L * L ≤ m := Nat.div_mul_le_self m L
  have hu : m < m / L * L + L := Nat.lt_div_mul_add hL
  have he : node N K (m/L) = m/L * L := min_eq_left (hl.trans hm)
  refine ⟨m/L, hj, ?_, ?_, ?_⟩
  · rw [he]; exact hl
  · change m ≤ min ((m/L+1)*L) N
    apply le_min _ hm
    nlinarith
  · rw [he]
    change min ((m/L+1)*L) N ≤ m/L*L+L
    exact (min_le_left _ _).trans_eq (by ring)

def cumulative (T : ℝ≥0) (n m : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range m, (ibmValue (grid (T/(n + 1)) (i + 1)) ω -
    ibmValue (grid (T/(n + 1)) i) ω)^4

theorem cumulative_mono (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    Monotone (fun m => cumulative T n m ω) := by
  intro m l hml
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hml)
    (fun _ _ _ => by positivity)

theorem error_eq {T : ℝ≥0} (hT : 0 < T) (n m : ℕ) (ω : JointSample) :
    IBMUniformPrefixQuartic.error T n m ω =
      cumulative T n m ω - (3 * (T : ℝ)/(n + 1)) * m := by
  unfold IBMUniformPrefixQuartic.error IBMUniformSubfamilyQuartic.quartic
  rw [sum_prefix hT]
  simp only [IBMUniformQuarticFamily.segment, Nat.cast_add, Nat.cast_one]
  unfold cumulative
  ring

theorem error_measurable (T : ℝ≥0) (n m : ℕ) :
    Measurable (IBMUniformPrefixQuartic.error T n m) :=
  (quartic_measurable _).sub measurable_const

def coarse (T : ℝ≥0) (n K : ℕ) (ω : JointSample) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
    (fun j => |IBMUniformPrefixQuartic.error T n (node (n + 1) K j) ω|)

def maximum (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  (Finset.range (n + 2)).sup' (Finset.nonempty_range_add_one)
    (fun m => |IBMUniformPrefixQuartic.error T n m ω|)

theorem maximum_nonneg (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    0 ≤ maximum T n ω :=
  (abs_nonneg _).trans (Finset.le_sup'
    (fun m => |IBMUniformPrefixQuartic.error T n m ω|) (b := 0) (by simp))

theorem maximum_measurable (T : ℝ≥0) (n : ℕ) : Measurable (maximum T n) := by
  apply Finset.measurable_range_sup''
  intro m hm
  exact continuous_abs.measurable.comp (error_measurable T n m)

theorem coarse_nonneg (T : ℝ≥0) (n K : ℕ) (ω : JointSample) :
    0 ≤ coarse T n K ω :=
  (abs_nonneg _).trans (Finset.le_sup'
    (fun j => |IBMUniformPrefixQuartic.error T n (node (n + 1) K j) ω|)
    (b := 0) (by simp))

/-- A deterministic squeeze for a nondecreasing cumulative mass, with a linear
target. No regularity of a random weight or stochastic independence is used. -/
theorem squeeze_prefix (Q : ℕ → ℝ) (hQ : Monotone Q) {d a : ℝ} (hd : 0 ≤ d)
    {l m u L : ℕ} (hlm : l ≤ m) (hmu : m ≤ u) (hul : u ≤ l + L)
    (hl : |Q l - d * l| ≤ a) (hu : |Q u - d * u| ≤ a) :
    |Q m - d * m| ≤ a+d*L := by
  have hl' := abs_le.mp hl
  have hu' := abs_le.mp hu
  have h1 := hQ hlm
  have h2 := hQ hmu
  have h3 : (u : ℝ) ≤ l + L := by exact_mod_cast hul
  have h4 : (l : ℝ) ≤ m := by exact_mod_cast hlm
  have h5 : (m : ℝ) ≤ u := by exact_mod_cast hmu
  have h6 := mul_le_mul_of_nonneg_left h3 hd
  have h7 := mul_le_mul_of_nonneg_left h4 hd
  have h8 := mul_le_mul_of_nonneg_left h5 hd
  apply abs_le.mpr
  constructor <;> nlinarith

theorem maximum_bound {T : ℝ≥0} (hT : 0 < T) (n K : ℕ) (hK : 0 < K)
    (ω : JointSample) :
    maximum T n ω ≤ coarse T n K ω + 3*(T : ℝ)/K + 3*(T : ℝ)/(n + 1) := by
  have hd : 0 ≤ 3*(T : ℝ)/(n + 1) := by positivity
  have hp : 0 < (n + 1 : ℝ) := by positivity
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hb : maximum T n ω ≤ coarse T n K ω +
      (3*(T : ℝ)/(n + 1)) * width (n + 1) K := by
    unfold maximum
    apply Finset.sup'_le
    intro m hm
    obtain ⟨j, hj, hl, hu, hw⟩ := cover (n + 1) K hK m (by
      have := Finset.mem_range.mp hm
      omega)
    have he (j : ℕ) (hj : j ≤ K) :
        |cumulative T n (node (n + 1) K j) ω -
          (3*(T : ℝ)/(n + 1)) * node (n + 1) K j| ≤ coarse T n K ω := by
      rw [← error_eq hT]
      exact Finset.le_sup'
        (fun j => |IBMUniformPrefixQuartic.error T n (node (n + 1) K j) ω|)
        (Finset.mem_range.mpr (by omega))
    rw [error_eq hT]
    exact squeeze_prefix _ (cumulative_mono T n ω) hd hl hu hw
      (he j (by omega)) (he (j + 1) (by omega))
  have hf : (width (n + 1) K : ℝ) ≤ (n + 1 : ℝ)/K + 1 := by
    unfold width
    push_cast
    have hf0 : (((n + 1)/K : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ)/(K : ℝ) := Nat.cast_div_le
    push_cast at hf0
    linarith
  calc
    maximum T n ω ≤ coarse T n K ω +
        (3*(T : ℝ)/(n + 1)) * ((n + 1 : ℝ)/K + 1) :=
      hb.trans (by gcongr)
    _ = _ := by field_simp; ring

theorem coarse_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) (K : ℕ) :
    TendstoInMeasure jointMeasure (fun n => coarse T n K) atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have hb (n : ℕ) : jointMeasure.real {ω | ε ≤ coarse T n K ω} ≤
      ∑ j ∈ Finset.range (K + 1),
        jointMeasure.real {ω | ε ≤ |IBMUniformPrefixQuartic.error T n (node (n + 1) K j) ω|} := by
    apply le_trans (measureReal_mono (μ := jointMeasure) (s₂ :=
      ⋃ j ∈ Finset.range (K + 1),
        {ω | ε ≤ |IBMUniformPrefixQuartic.error T n (node (n + 1) K j) ω|}) ?_
          (measure_ne_top _ _))
      (measureReal_biUnion_finset_le _ _)
    intro ω hω
    unfold coarse at hω
    obtain ⟨j, hj, he⟩ := (Finset.le_sup'_iff
      (s := Finset.range (K + 1)) Finset.nonempty_range_add_one
      (f := fun j => |IBMUniformPrefixQuartic.error T n (node (n + 1) K j) ω|)).mp hω
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, he⟩⟩
  have hs := tendsto_finsetSum (Finset.range (K + 1)) (fun j hj =>
    (tendstoInMeasure_iff_measureReal_norm.mp
      (IBMUniformPrefixQuartic.error_tendstoInMeasure hT
        (fun n => node (n + 1) K j) (fun n => node_le _ _ _))) ε hε)
  simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (coarse_nonneg _ _ _ _)]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [sub_zero, Real.norm_eq_abs, Finset.sum_const_zero] using hs

/-- Uniform convergence of the entire discrete cumulative quartic-variation
function, in probability under the original scenery-clock product law. -/
theorem maximum_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (maximum T) atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => 3*(T : ℝ)/(n + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have he : 0 < ε/4 := by positivity
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds he)).exists
  have hc := tendstoInMeasure_iff_measureReal_norm.mp
    (coarse_tendstoInMeasure hT (k + 1))
  have hb : ∀ᶠ n : ℕ in atTop,
      jointMeasure.real {ω | ε ≤ maximum T n ω} ≤
        jointMeasure.real {ω | ε/2 ≤ |coarse T n (k + 1) ω|} := by
    filter_upwards [ht.eventually (gt_mem_nhds he)] with n hn
    apply measureReal_mono (μ := jointMeasure) (h₂ := by finiteness)
    intro ω hω
    have h := maximum_bound hT n (k + 1) (by omega) ω
    simp only [Nat.cast_add, Nat.cast_one] at h
    have hc0 := le_abs_self (coarse T n (k + 1) ω)
    change ε ≤ maximum T n ω at hω
    change ε/2 ≤ |coarse T n (k + 1) ω|
    linarith
  simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (maximum_nonneg _ _ _)]
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hb
    (by simpa only [sub_zero, Real.norm_eq_abs] using hc (ε/2) (by positivity))

attribute [local irreducible] IBMUniformPrefixQuartic.error

theorem selected_measurable (T : ℝ≥0) (n : ℕ) (m : JointSample → ℕ)
    (hm : Measurable m) :
    Measurable (fun ω => IBMUniformPrefixQuartic.error T n (m ω) ω) := by
  have hp : Measurable (fun p : ℕ × JointSample =>
      IBMUniformPrefixQuartic.error T n p.1 p.2) :=
    measurable_from_prod_countable_right
      (f := fun p : ℕ × JointSample => IBMUniformPrefixQuartic.error T n p.1 p.2)
      (fun k => error_measurable T n k)
  exact hp.comp (hm.prodMk measurable_id)

/-- Uniform control permits sample-dependent prefix selection. Combined with
selected_measurable this is ordinary probability convergence for measurable
selectors; no stopping-time or adaptedness assertion is made. -/
theorem selected_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (m : ℕ → JointSample → ℕ) (hm : ∀ n ω, m n ω ≤ n + 1) :
    TendstoInMeasure jointMeasure
      (fun n ω => IBMUniformPrefixQuartic.error T n (m n ω) ω)
      atTop (fun _ => (0 : ℝ)) := by
  have h := tendstoInMeasure_iff_measureReal_norm.mp (maximum_tendstoInMeasure hT)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have hb (n : ℕ) : jointMeasure.real
      {ω | ε ≤ |IBMUniformPrefixQuartic.error T n (m n ω) ω|} ≤
      jointMeasure.real {ω | ε ≤ maximum T n ω} := by
    apply measureReal_mono (μ := jointMeasure) (h₂ := measure_ne_top _ _)
    intro ω hω
    change ε ≤ |IBMUniformPrefixQuartic.error T n (m n ω) ω| at hω
    exact hω.trans (Finset.le_sup'
      (fun k => |IBMUniformPrefixQuartic.error T n k ω|)
      (Finset.mem_range.mpr (by have := hm n ω; omega)))
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (maximum_nonneg _ _ _)] using h ε hε

end OperatorDerivativeRewrite.Foundation.IBMUniformPrefixMaximum
