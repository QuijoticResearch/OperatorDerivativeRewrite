import Foundation.GaussianAngularSphere
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.CStarAlgebra.Unitary.Maps
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Measure

/-! The concrete Gaussian angular law is the tuple image of unit-quaternion Haar probability. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Quaternion
namespace OperatorDerivativeRewrite.Foundation.QuaternionAngularHaar
open GaussianAngularSphere
set_option backward.isDefEq.respectTransparency false

abbrev Group := ↥(unitary ℍ)
abbrev tuple : ℍ ≃ₗᵢ[ℝ] Space := Quaternion.linearIsometryEquivTuple

instance quaternionMeasurableSpace : MeasurableSpace ℍ := borel ℍ
instance quaternionBorelSpace : BorelSpace ℍ := ⟨rfl⟩

theorem mem_unitary_of_norm_one (q : ℍ) (hq : ‖q‖ = 1) : q ∈ unitary ℍ := by
  have hn : Quaternion.normSq q = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hq, one_mul]
  rw [Unitary.mem_iff]
  constructor <;> simp [Quaternion.star_mul_self, Quaternion.self_mul_star, hn]

instance group_compact : CompactSpace Group := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : ℍ) 1).of_isClosed_subset isClosed_unitary
  intro q hq
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (CStarRing.norm_of_mem_unitary hq).le

def rawDirection (x : Space) : ℍ :=
  if x = 0 then 1 else tuple.symm (NormedSpace.normalize x)

theorem rawDirection_mem (x : Space) : rawDirection x ∈ unitary ℍ := by
  by_cases hx : x = 0
  · simp [rawDirection, hx]
  · apply mem_unitary_of_norm_one
    simp only [rawDirection, if_neg hx, tuple.symm.norm_map, NormedSpace.norm_normalize hx]

def direction (x : Space) : Group := ⟨rawDirection x, rawDirection_mem x⟩

theorem direction_measurable : Measurable direction := by
  have hm : Measurable rawDirection :=
    Measurable.ite (measurableSet_singleton 0) measurable_const
      (tuple.symm.continuous.measurable.comp normalize_measurable)
  exact hm.subtype_mk

def embed (u : Group) : Space := tuple (u : ℍ)

theorem embed_continuous : Continuous embed :=
  tuple.continuous.comp continuous_subtype_val

theorem embed_norm (u : Group) : ‖embed u‖ = 1 := by
  rw [embed, tuple.norm_map, CStarRing.norm_coe_unitary]

theorem embed_injective : Function.Injective embed := by
  intro u v h
  exact Subtype.ext (tuple.injective h)

def rotation (u : Group) : Space ≃ₗᵢ[ℝ] Space :=
  (tuple.symm.trans (Unitary.mulLeft ℝ ℍ u)).trans tuple

theorem rotation_quaternion (u : Group) (x : Space) :
    tuple.symm (rotation u x) = (u : ℍ) * tuple.symm x := by
  change tuple.symm (tuple ((Unitary.mulLeft ℝ ℍ u) (tuple.symm x))) = _
  rw [tuple.symm_apply_apply, Unitary.mulLeft_apply]

theorem direction_rotation (u : Group) (x : Space) (hx : x ≠ 0) :
    direction (rotation u x) = u * direction x := by
  have hr : rotation u x ≠ 0 := by
    intro h
    apply hx
    apply (rotation u).injective
    simpa only [map_zero] using h
  apply Subtype.ext
  change rawDirection (rotation u x) = (u : ℍ) * rawDirection x
  rw [rawDirection, if_neg hr, rawDirection, if_neg hx, normalize_isometry]
  exact rotation_quaternion u (NormedSpace.normalize x)

def law : Measure Group := gaussian.map direction

instance law_probability : IsProbabilityMeasure law := by unfold law; infer_instance

instance law_leftInvariant : law.IsMulLeftInvariant where
  map_mul_left_eq_self u := by
    calc
      law.map (u * ·) = gaussian.map ((u * ·) ∘ direction) :=
        Measure.map_map (measurable_const_mul u) direction_measurable
      _ = gaussian.map (direction ∘ rotation u) := by
        apply Measure.map_congr
        filter_upwards [gaussian_ae_ne_zero] with x hx
        exact (direction_rotation u x hx).symm
      _ = (gaussian.map (rotation u)).map direction :=
        (Measure.map_map direction_measurable (rotation u).continuous.measurable).symm
      _ = law := by rw [stdGaussian_map]; rfl

instance law_isHaar : law.IsHaarMeasure := by
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior law univ isCompact_univ
  · simp
  · simp
  · simp

theorem law_eq_probability_haar (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] :
    law = ν :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure law ν

theorem embed_direction_ae : ∀ᵐ x ∂gaussian, embed (direction x) = NormedSpace.normalize x := by
  filter_upwards [gaussian_ae_ne_zero] with x hx
  change tuple (rawDirection x) = NormedSpace.normalize x
  rw [rawDirection, if_neg hx]
  exact tuple.apply_symm_apply _

theorem law_embed : law.map embed = angularLaw := by
  rw [law, Measure.map_map embed_continuous.measurable direction_measurable]
  exact Measure.map_congr embed_direction_ae

/-- The angular law is identified using Haar uniqueness, not merely matching moments. -/
theorem probability_haar_embed (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] :
    ν.map embed = angularLaw := by
  rw [← law_eq_probability_haar ν, law_embed]

def realCoordinate (u : Group) : ℝ := (u : ℍ).re

theorem realCoordinate_eq (u : Group) : realCoordinate u = coord 0 (embed u) := by
  rw [coord, NormedSpace.normalize_eq_self_of_norm_eq_one (embed_norm u)]
  rfl

theorem realCoordinate_measurable : Measurable realCoordinate := by
  have he : realCoordinate = coord 0 ∘ embed := funext realCoordinate_eq
  rw [he]
  exact (coord_measurable 0).comp embed_continuous.measurable

theorem realCoordinate_bound (u : Group) : |realCoordinate u| ≤ 1 := by
  rw [realCoordinate_eq]
  exact coord_bound 0 (embed u)

theorem weighted_realCoordinate (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (g : ℝ → ℝ) (hg : Measurable g) (t : ℝ) :
    BoundedExponentialTiltResponse.weighted ν realCoordinate (fun u => g (realCoordinate u)) t =
      BoundedExponentialTiltResponse.weighted angularLaw (coord 0) (fun x => g (coord 0 x)) t := by
  have hm : Measurable (fun x : Space => g (coord 0 x) * Real.exp (t * coord 0 x)) :=
    (hg.comp (coord_measurable 0)).mul ((measurable_const.mul (coord_measurable 0)).exp)
  have he := integral_map (μ := ν) embed_continuous.measurable.aemeasurable hm.aestronglyMeasurable
  rw [probability_haar_embed ν] at he
  change (∫ u, g (realCoordinate u) * Real.exp (t * realCoordinate u) ∂ν) =
    ∫ x, g (coord 0 x) * Real.exp (t * coord 0 x) ∂angularLaw
  simpa only [realCoordinate_eq] using he.symm

theorem partition_realCoordinate (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (t : ℝ) : BoundedExponentialTiltResponse.partition ν realCoordinate t =
      BoundedExponentialTiltResponse.partition angularLaw (coord 0) t :=
  weighted_realCoordinate ν (fun _ => 1) measurable_const t

theorem expectation_realCoordinate (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (g : ℝ → ℝ) (hg : Measurable g) (t : ℝ) :
    BoundedExponentialTiltResponse.expectation ν realCoordinate (fun u => g (realCoordinate u)) t =
      BoundedExponentialTiltResponse.expectation angularLaw (coord 0) (fun x => g (coord 0 x)) t := by
  unfold BoundedExponentialTiltResponse.expectation
  rw [weighted_realCoordinate ν g hg t, partition_realCoordinate ν t]

theorem haar_variance_eq (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] (t : ℝ) :
    BoundedExponentialTiltResponse.variance ν realCoordinate
      (fun u => realCoordinate u+realCoordinate u^2) t =
    BoundedExponentialTiltResponse.variance angularLaw (coord 0)
      (fun x => coord 0 x+coord 0 x^2) t := by
  unfold BoundedExponentialTiltResponse.variance
  rw [expectation_realCoordinate ν (fun r => (r+r^2)^2) (by fun_prop) t,
    expectation_realCoordinate ν (fun r => r+r^2) (by fun_prop) t]

theorem haar_variance_zero (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] :
    BoundedExponentialTiltResponse.variance ν realCoordinate
      (fun u => realCoordinate u+realCoordinate u^2) 0 = 5/16 := by
  rw [haar_variance_eq, angular_variance_zero]

theorem haar_variance_derivative (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] :
    HasDerivAt (BoundedExponentialTiltResponse.variance ν realCoordinate
      (fun u => realCoordinate u+realCoordinate u^2)) (1/8) 0 := by
  have he : BoundedExponentialTiltResponse.variance ν realCoordinate
      (fun u => realCoordinate u+realCoordinate u^2) =
      BoundedExponentialTiltResponse.variance angularLaw (coord 0)
        (fun x => coord 0 x+coord 0 x^2) := funext (haar_variance_eq ν)
  rw [he]
  exact angular_variance_derivative 0

theorem haar_variance_increases (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (ε : ℝ) (hε : 0 < ε) : ∃ t, 0 < t ∧ t < ε ∧
      BoundedExponentialTiltResponse.variance ν realCoordinate
        (fun u => realCoordinate u+realCoordinate u^2) 0 <
      BoundedExponentialTiltResponse.variance ν realCoordinate
        (fun u => realCoordinate u+realCoordinate u^2) t := by
  simpa only [haar_variance_eq] using angular_variance_increases 0 ε hε

theorem haar_variance_not_antitone (ν : Measure Group) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] :
    ¬ AntitoneOn (BoundedExponentialTiltResponse.variance ν realCoordinate
      (fun u => realCoordinate u+realCoordinate u^2)) (Ici 0) := by
  intro hanti
  obtain ⟨t, ht, _, hinc⟩ := haar_variance_increases ν 1 (by norm_num)
  have he := hanti (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht.le) ht.le
  exact (not_lt_of_ge he) hinc

end OperatorDerivativeRewrite.Foundation.QuaternionAngularHaar
