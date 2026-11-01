import Foundation.FractionalWickCovariance
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! An ordinary finite signed covariance measure on a compact time square
is incompatible with the actual fBM diagonal increments when0<H<1/2.
This concerns the covariance differential, NOT the positive fBM path law. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalCovarianceMeasureObstruction

def grid (n i : ℕ) : ℝ := (i:ℝ)/(n+1:ℕ)
def square (n i : ℕ) : Set (ℝ × ℝ) :=
  Ioc (grid n i) (grid n (i+1)) ×ˢ Ioc (grid n i) (grid n (i+1))

theorem grid_step (n i : ℕ) : grid n (i+1)-grid n i=1/(n+1:ℕ) := by
  simp only [grid,Nat.cast_add,Nat.cast_one]
  ring

theorem grid_mono (n : ℕ) : Monotone (grid n) := by
  intro i j hij
  apply div_le_div_of_nonneg_right (by exact_mod_cast hij)
  positivity

theorem grid_bounds (n i : ℕ) (hi : i ≤ n+1) : 0 ≤ grid n i ∧ grid n i ≤ 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
    exact_mod_cast hi

theorem square_measurable (n i : ℕ) : MeasurableSet (square n i) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem squares_disjoint (n : ℕ) : ∀ i j : ℕ, i≠j → Disjoint (square n i) (square n j) := by
  intro i j hij
  apply disjoint_left.mpr
  intro w hi hj
  change (w.1 ∈ Ioc (grid n i) (grid n (i+1))) ∧ _ at hi
  change (w.1 ∈ Ioc (grid n j) (grid n (j+1))) ∧ _ at hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hh := grid_mono n (Nat.succ_le_of_lt h)
    linarith [hi.1.2,hj.1.1]
  · have hh := grid_mono n (Nat.succ_le_of_lt h)
    linarith [hj.1.2,hi.1.1]

def rectangleIncrement (H a b c d : ℝ) : ℝ :=
  FractionalSpectralGeometry.covariance H b d-FractionalSpectralGeometry.covariance H a d-
    FractionalSpectralGeometry.covariance H b c+FractionalSpectralGeometry.covariance H a c

theorem diagonal_increment (H : ℝ) (hH : 0 < H) (a b : ℝ) :
    rectangleIncrement H a b a b=|b-a|^(2*H) := by
  unfold rectangleIncrement FractionalSpectralGeometry.covariance
  simp only [sub_self,abs_zero,Real.zero_rpow (by linarith : 2*H ≠ 0)]
  rw [abs_sub_comm a b]
  ring

theorem grid_diagonal_increment (H : ℝ) (hH : 0 < H) (n i : ℕ) :
    rectangleIncrement H (grid n i) (grid n (i+1)) (grid n i) (grid n (i+1)) =
      (1/(n+1:ℕ):ℝ)^(2*H) := by
  rw [diagonal_increment H hH,grid_step,abs_of_nonneg (by positivity)]

theorem partition_sum (H A : ℝ) (n : ℕ) :
    (∑ _i ∈ Finset.range (n+1), A*(1/(n+1:ℕ):ℝ)^(2*H)) =
      A*((n+1:ℕ):ℝ)^(1-2*H) := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Real.rpow_sub hn,
    Real.rpow_one,one_div,Real.inv_rpow hn.le]
  ring

/-- Exact growing lower bound forced on ANY finite positive control measure. -/
theorem control_mass_lower (H A : ℝ) (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν]
    (hc : ∀ n i : ℕ, i<n+1 → A*(1/(n+1:ℕ):ℝ)^(2*H) ≤ ν.real (square n i)) (n : ℕ) :
    A*((n+1:ℕ):ℝ)^(1-2*H) ≤ ν.real univ := by
  have hs := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range (n+1)) => hc n i (Finset.mem_range.mp hi))
  rw [partition_sum] at hs
  exact hs.trans (sum_measureReal_le_measureReal_univ (fun i _ => square_measurable n i)
    (fun i _ j _ hij => squares_disjoint n i j hij))

theorem no_finite_control (H : ℝ) (hH : H<1/2) (A : ℝ) (hA : 0<A)
    (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν]
    (hc : ∀ n i : ℕ, i<n+1 → A*(1/(n+1:ℕ):ℝ)^(2*H) ≤ ν.real (square n i)) : False := by
  have ht : Tendsto (fun n : ℕ => A*((n+1:ℕ):ℝ)^(1-2*H)) atTop atTop := by
    apply Tendsto.const_mul_atTop hA
    exact (tendsto_rpow_atTop (by linarith : 0<1-2*H)).comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1))
  have he := (tendsto_atTop.1 ht (ν.real univ+1)).exists
  obtain ⟨n,hn⟩ := he
  linarith [control_mass_lower H A ν hc n]

/-- Only diagonal squares in[0,1]^2 are needed to exclude the signed measure. -/
theorem no_signed_diagonal (H : ℝ) (hH0 : 0<H) (hH : H<1/2) (A : ℝ) (hA : 0<A)
    (μ : SignedMeasure (ℝ × ℝ))
    (hc : ∀ a b : ℝ, 0≤a → a≤b → b≤1 →
      μ (Ioc a b ×ˢ Ioc a b)=A*rectangleIncrement H a b a b) : False := by
  letI : IsFiniteMeasure μ.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  apply no_finite_control H hH A hA μ.variation
  intro n i hi
  have hbounds := grid_bounds n i (by omega)
  have hbounds' := grid_bounds n (i+1) (by omega)
  have hm := hc (grid n i) (grid n (i+1)) hbounds.1 (grid_mono n (by omega)) hbounds'.2
  rw [grid_diagonal_increment H hH0] at hm
  have hn := VectorMeasure.norm_measure_le_variation (μ := μ) (E := square n i)
  change |μ (square n i)| ≤ μ.variation.real (square n i) at hn
  rw [show μ (square n i)=A*(1/(n+1:ℕ):ℝ)^(2*H) from hm,
    abs_of_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (by positivity) _))] at hn
  exact hn

theorem no_signed_covariance (H : ℝ) (hH0 : 0<H) (hH : H<1/2) (A : ℝ) (hA : 0<A)
    (μ : SignedMeasure (ℝ × ℝ))
    (hc : ∀ a b c d : ℝ, 0≤a → a≤b → b≤1 → 0≤c → c≤d → d≤1 →
      μ (Ioc a b ×ˢ Ioc c d)=A*rectangleIncrement H a b c d) : False := by
  apply no_signed_diagonal H hH0 hH A hA μ
  intro a b ha hab hb
  exact hc a b a b ha hab hb ha hab hb

/-- Compact-domain version: no assumption about mass outside the unit square. -/
theorem no_signed_unit_covariance (H : ℝ) (hH0 : 0<H) (hH : H<1/2) (A : ℝ) (hA : 0<A)
    (μ : SignedMeasure {q : ℝ × ℝ // q ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1})
    (hc : ∀ a b c d : ℝ, 0≤a → a≤b → b≤1 → 0≤c → c≤d → d≤1 →
      μ {q | q.val ∈ Ioc a b ×ˢ Ioc c d}=A*rectangleIncrement H a b c d) : False := by
  apply no_signed_covariance H hH0 hH A hA (μ.map Subtype.val)
  intro a b c d ha hab hb hc' hcd hd
  rw [VectorMeasure.map_apply μ measurable_subtype_coe (measurableSet_Ioc.prod measurableSet_Ioc)]
  exact hc a b c d ha hab hb hc' hcd hd

/-- Instantiation on the ACTUAL verified fractional Gaussian increment law. -/
theorem no_signed_actual_increment (H : ℝ) (hH0 : 0<H) (hH1 : H<1) (hH : H<1/2)
    (A : ℝ) (hA : 0<A) (μ : SignedMeasure (ℝ × ℝ))
    (hc : ∀ a b : ℝ≥0, a≤b → b≤1 → μ (Ioc (a:ℝ) (b:ℝ) ×ˢ Ioc (a:ℝ) (b:ℝ))=
      A*(∫ w,(FractionalGaussianProcess.process H hH0 hH1 b w-
        FractionalGaussianProcess.process H hH0 hH1 a w)^2 ∂InfiniteGaussian.gaussianProduct)) : False := by
  apply no_signed_diagonal H hH0 hH A hA μ
  intro a b ha hab hb
  have hnn : a.toNNReal≤b.toNNReal := Real.toNNReal_le_toNNReal hab
  have hbn : b.toNNReal≤1 := by simpa using Real.toNNReal_le_toNNReal hb
  have hm := hc a.toNNReal b.toNNReal hnn hbn
  rw [FractionalGaussianProcess.increment_secondMoment H hH0 hH1,
    Real.coe_toNNReal a ha,Real.coe_toNNReal b (ha.trans hab)] at hm
  rw [diagonal_increment H hH0]
  exact hm

/-- The mass lower bound is constant at the Brownian boundary H=1/2. -/
theorem half_partition_sum (A : ℝ) (n : ℕ) :
    (∑ _i ∈ Finset.range (n+1), A*(1/(n+1:ℕ):ℝ)^(2*(1/2:ℝ)))=A := by
  rw [partition_sum]
  norm_num

/-- A genuine finite diagonal measure realizes the Brownian boundary control. -/
theorem brownian_control_exists : ∃ ν : Measure (ℝ × ℝ), IsFiniteMeasure ν ∧
    ∀ n i : ℕ, i<n+1 → ν.real (square n i)=1/(n+1:ℕ) := by
  let ρ : Measure ℝ := volume.restrict (Ioc 0 1)
  letI : IsFiniteMeasure ρ := ⟨by simp [ρ]⟩
  let ν : Measure (ℝ × ℝ) := ρ.map (fun x : ℝ => (x,x))
  have hm : Measurable (fun x : ℝ => (x,x)) := measurable_id.prodMk measurable_id
  refine ⟨ν,inferInstance,?_⟩
  intro n i hi
  have ha := (grid_bounds n i (by omega)).1
  have hb := (grid_bounds n (i+1) (by omega)).2
  have hsub : Ioc (grid n i) (grid n (i+1)) ⊆ Ioc (0:ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_le_of_lt ha hx.1,hx.2.trans hb⟩
  have hp : (fun x : ℝ => (x,x)) ⁻¹' square n i=Ioc (grid n i) (grid n (i+1)) := by
    ext x
    simp [square]
  change ((ρ.map (fun x : ℝ => (x,x))) (square n i)).toReal = _
  rw [Measure.map_apply hm (square_measurable n i),hp]
  change ((volume.restrict (Ioc (0:ℝ) 1)) (Ioc (grid n i) (grid n (i+1)))).toReal = _
  rw [Measure.restrict_apply measurableSet_Ioc,inter_eq_left.mpr hsub]
  change volume.real (Ioc (grid n i) (grid n (i+1))) = _
  rw [Real.volume_real_Ioc,max_eq_left (sub_nonneg.mpr (grid_mono n (by omega)))]
  exact grid_step n i

end OperatorDerivativeRewrite.Foundation.FractionalCovarianceMeasureObstruction
