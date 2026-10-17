import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Finset.Lattice.Fold

/-! Finite maxima preserve Lipschitz bounds but need not preserve differentiability. -/
noncomputable section
open Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.CorridorMaximumRegularity
set_option backward.isDefEq.respectTransparency false

def sectorLeft (t : ℝ) : ℝ := 1+t+t^2
def sectorRight (t : ℝ) : ℝ := 1-t+t^2
def total (t : ℝ) : ℝ := sectorLeft t+sectorRight t
def maximum (t : ℝ) : ℝ := max (sectorLeft t) (sectorRight t)
def concentration (t : ℝ) : ℝ := maximum t/total t

theorem sectorLeft_smooth : ContDiff ℝ ⊤ sectorLeft := by unfold sectorLeft; fun_prop
theorem sectorRight_smooth : ContDiff ℝ ⊤ sectorRight := by unfold sectorRight; fun_prop

theorem sectorLeft_pos (t : ℝ) : 0<sectorLeft t := by
  unfold sectorLeft
  nlinarith [sq_nonneg (t+1/2)]

theorem sectorRight_pos (t : ℝ) : 0<sectorRight t := by
  unfold sectorRight
  nlinarith [sq_nonneg (t-1/2)]

theorem total_formula (t : ℝ) : total t=2+2*t^2 := by
  unfold total sectorLeft sectorRight
  ring

theorem total_pos (t : ℝ) : 0<total t :=
  add_pos (sectorLeft_pos t) (sectorRight_pos t)

theorem total_smooth : ContDiff ℝ ⊤ total := sectorLeft_smooth.add sectorRight_smooth

theorem maximum_formula (t : ℝ) : maximum t=1+t^2+|t| := by
  by_cases ht : 0≤t
  · rw [abs_of_nonneg ht]
    unfold maximum sectorLeft sectorRight
    rw [max_eq_left (by linarith)]
    ring
  · rw [abs_of_neg (lt_of_not_ge ht)]
    unfold maximum sectorLeft sectorRight
    rw [max_eq_right (by linarith)]
    ring

theorem maximum_continuous : Continuous maximum :=
  sectorLeft_smooth.continuous.max sectorRight_smooth.continuous

theorem concentration_continuous : Continuous concentration :=
  maximum_continuous.div total_smooth.continuous (fun t => (total_pos t).ne')

theorem maximum_not_differentiable : ¬DifferentiableAt ℝ maximum 0 := by
  intro hd
  have hb : DifferentiableAt ℝ (fun t : ℝ => 1+t^2) 0 := by fun_prop
  have hh := hd.sub hb
  change DifferentiableAt ℝ (fun t => maximum t-(1+t^2)) 0 at hh
  have he : (fun t => maximum t-(1+t^2))=(abs : ℝ → ℝ) := by
    ext t; rw [maximum_formula]; ring
  rw [he] at hh
  exact not_differentiableAt_abs_zero hh

theorem concentration_not_differentiable : ¬DifferentiableAt ℝ concentration 0 := by
  intro hd
  have ht : DifferentiableAt ℝ total 0 := total_smooth.differentiable (by simp) 0
  have hh := ht.mul hd
  change DifferentiableAt ℝ (fun t => total t*concentration t) 0 at hh
  have he : (fun t => total t*concentration t)=maximum := by
    ext t
    unfold concentration
    field_simp [(total_pos t).ne']
  rw [he] at hh
  exact maximum_not_differentiable hh

theorem concentration_at_tie : concentration 0=1/2 := by
  norm_num [concentration, maximum, total, sectorLeft, sectorRight]

def finiteMaximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → ℝ → ℝ) (t : ℝ) : ℝ := s.sup' hs (fun i => e i t)

theorem finiteMaximum_shift_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → ℝ → ℝ) (t u a : ℝ) (he : ∀ i∈s, e i t-e i u≤a) :
    finiteMaximum s hs e t≤finiteMaximum s hs e u+a := by
  apply (Finset.sup'_le_iff hs _).mpr
  intro i hi
  have hm : e i u≤finiteMaximum s hs e u := Finset.le_sup' (fun i => e i u) hi
  linarith [he i hi]

theorem finiteMaximum_difference_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → ℝ → ℝ) (t u a : ℝ) (he : ∀ i∈s, |e i t-e i u|≤a) :
    |finiteMaximum s hs e t-finiteMaximum s hs e u|≤a := by
  have htu := finiteMaximum_shift_bound s hs e t u a
    (fun i hi => (le_abs_self _).trans (he i hi))
  have hut := finiteMaximum_shift_bound s hs e u t a
    (fun i hi => by have h := (abs_le.mp (he i hi)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem finiteMaximum_lipschitz {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → ℝ → ℝ) (K : ℝ≥0) (he : ∀ i∈s, LipschitzWith K (e i)) :
    LipschitzWith K (finiteMaximum s hs e) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  simp only [Real.dist_eq]
  exact finiteMaximum_difference_bound s hs e t u _
    (fun i hi => by simpa only [Real.dist_eq] using (he i hi).dist_le_mul t u)

theorem finiteMaximum_nonneg {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → ℝ → ℝ) (t : ℝ) (he : ∀ i∈s, 0≤e i t) :
    0≤finiteMaximum s hs e t := by
  obtain ⟨i, hi⟩ := hs
  exact (he i hi).trans (Finset.le_sup' (fun i => e i t) hi)

theorem finiteMaximum_le_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → ℝ → ℝ) (t : ℝ) (he : ∀ i∈s, 0≤e i t) :
    finiteMaximum s hs e t≤∑ i∈s, e i t := by
  apply (Finset.sup'_le_iff hs _).mpr
  intro i hi
  exact Finset.single_le_sum he hi

theorem ratio_difference_bound {m M e E a b d : ℝ}
    (hd : 0<d) (he : d≤e) (hE : d≤E) (hM : 0≤M) (hME : M≤E)
    (ha : 0≤a) (hb : 0≤b) (hm : |m-M|≤a) (heE : |e-E|≤b) :
    |m/e-M/E|≤(a+b)/d := by
  have hep : 0<e := hd.trans_le he
  have hEp : 0<E := hd.trans_le hE
  have hid : m/e-M/E=(m-M)/e+(M/E)*((E-e)/e) := by
    field_simp
    ring
  have hratio : 0≤M/E := div_nonneg hM hEp.le
  have hratio1 : M/E≤1 := (div_le_one hEp).mpr hME
  rw [hid]
  calc
    |(m-M)/e+(M/E)*((E-e)/e)| ≤ |(m-M)/e|+|(M/E)*((E-e)/e)| := abs_add_le _ _
    _ = |m-M|/e+(M/E)*(|E-e|/e) := by
      simp only [abs_mul, abs_div, abs_of_pos hep, abs_of_pos hEp, abs_of_nonneg hM]
    _ ≤ a/e+1*(b/e) := by
      gcongr
      simpa only [abs_sub_comm] using heE
    _ = (a+b)/e := by ring
    _ ≤ (a+b)/d := div_le_div_of_nonneg_left (add_nonneg ha hb) hd he

theorem threshold_persistence {f : ℝ → ℝ} {t t₀ threshold δ L : ℝ}
    (hi : f t₀≤threshold-δ) (hb : |f t-f t₀|≤L*|t-t₀|)
    (hs : L*|t-t₀|<δ) : f t<threshold := by
  have h := (le_abs_self (f t-f t₀)).trans hb
  linarith

theorem threshold_persistence_radius {f : ℝ → ℝ} {t t₀ threshold δ L : ℝ}
    (hL : 0≤L) (_hδ : 0<δ) (hi : f t₀≤threshold-δ)
    (hb : |f t-f t₀|≤L*|t-t₀|) (ht : |t-t₀|<δ/(L+1)) : f t<threshold := by
  apply threshold_persistence hi hb
  have hprod : |t-t₀| * (L+1)<δ := (lt_div_iff₀ (by linarith)).mp ht
  nlinarith [abs_nonneg (t-t₀)]

theorem finite_sum_difference_bound {ι : Type*} (s : Finset ι)
    (e : ι → ℝ → ℝ) (t u K : ℝ) (he : ∀ i∈s, |e i t-e i u|≤K*|t-u|) :
    |(∑ i∈s, e i t)-(∑ i∈s, e i u)|≤(s.card:ℝ)*K*|t-u| := by
  calc
    |(∑ i∈s, e i t)-(∑ i∈s, e i u)| = |∑ i∈s, (e i t-e i u)| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i∈s, |e i t-e i u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈s, K*|t-u| := Finset.sum_le_sum he
    _ = (s.card:ℝ)*K*|t-u| := by simp [mul_assoc]

theorem finite_concentration_difference_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → ℝ → ℝ) (t u K d : ℝ) (hK : 0≤K) (hd : 0<d)
    (het : d≤∑ i∈s, e i t) (heu : d≤∑ i∈s, e i u)
    (hn : ∀ i∈s, 0≤e i u) (he : ∀ i∈s, |e i t-e i u|≤K*|t-u|) :
    |finiteMaximum s hs e t/(∑ i∈s, e i t)-finiteMaximum s hs e u/(∑ i∈s, e i u)|≤
      (((s.card:ℝ)+1)*K/d)*|t-u| := by
  have h := ratio_difference_bound hd het heu
    (finiteMaximum_nonneg s hs e u hn) (finiteMaximum_le_sum s hs e u hn)
    (mul_nonneg hK (abs_nonneg _)) (by positivity)
    (finiteMaximum_difference_bound s hs e t u _ he) (finite_sum_difference_bound s e t u K he)
  calc
    _ ≤ (K*|t-u|+(s.card:ℝ)*K*|t-u|)/d := h
    _ = (((s.card:ℝ)+1)*K/d)*|t-u| := by ring

theorem finite_concentration_threshold_persistence {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → ℝ → ℝ) (t u K d threshold δ : ℝ) (hK : 0≤K) (hd : 0<d)
    (het : d≤∑ i∈s, e i t) (heu : d≤∑ i∈s, e i u)
    (hn : ∀ i∈s, 0≤e i u) (he : ∀ i∈s, |e i t-e i u|≤K*|t-u|)
    (hi : finiteMaximum s hs e u/(∑ i∈s, e i u)≤threshold-δ)
    (hstep : (((s.card:ℝ)+1)*K/d)*|t-u|<δ) :
    finiteMaximum s hs e t/(∑ i∈s, e i t)<threshold := by
  exact threshold_persistence
    (f := fun v => finiteMaximum s hs e v/(∑ i∈s, e i v))
    (t := t) (t₀ := u) (L := ((s.card:ℝ)+1)*K/d) hi
    (finite_concentration_difference_bound s hs e t u K d hK hd het heu hn he) hstep

theorem threshold_above_persistence {f : ℝ → ℝ} {t t₀ threshold δ L : ℝ}
    (hi : threshold+δ≤f t₀) (hb : |f t-f t₀|≤L*|t-t₀|)
    (hs : L*|t-t₀|<δ) : threshold<f t := by
  have h := (abs_le.mp hb).1
  linarith

end OperatorDerivativeRewrite.Foundation.CorridorMaximumRegularity
