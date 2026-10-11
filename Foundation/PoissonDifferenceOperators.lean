import Foundation.PoissonDifferenceCore
import Foundation.AdjointClosure
import Foundation.LpProducts
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Module

/-! Finite-support Poisson difference and divergence as densely defined
partial Hilbert operators. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.PoissonDifferenceOperators
open PoissonDifferenceCore

variable (rate : ℝ≥0)

abbrev ScalarL2 := Lp ℝ 2 (poissonLaw rate)
abbrev FieldL2 := Lp ℝ 2 ((rate : ℝ≥0∞) • poissonLaw rate)

def scalarFinsupp (f : ℕ →₀ ℝ) : ScalarL2 rate :=
  (finsupp_memLp_two rate f).toLp fun n => f n

def fieldFinsupp (u : ℕ →₀ ℝ) : FieldL2 rate :=
  (finsupp_memLp_two_weighted rate u).toLp fun n => u n

theorem scalarFinsupp_coeFn (f : ℕ →₀ ℝ) :
    scalarFinsupp rate f =ᵐ[poissonLaw rate] fun n => f n := MemLp.coeFn_toLp _

theorem fieldFinsupp_coeFn (u : ℕ →₀ ℝ) :
    fieldFinsupp rate u =ᵐ[(rate : ℝ≥0∞) • poissonLaw rate] fun n => u n :=
  MemLp.coeFn_toLp _

def scalarEmbedding : (ℕ →₀ ℝ) →ₗ[ℝ] ScalarL2 rate where
  toFun := scalarFinsupp rate
  map_add' f g := by
    apply Lp.ext
    filter_upwards [scalarFinsupp_coeFn rate (f + g), scalarFinsupp_coeFn rate f,
      scalarFinsupp_coeFn rate g, Lp.coeFn_add (scalarFinsupp rate f)
      (scalarFinsupp rate g)] with n hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply, hf, hg, Finsupp.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [scalarFinsupp_coeFn rate (c • f), scalarFinsupp_coeFn rate f,
      Lp.coeFn_smul c (scalarFinsupp rate f)] with n hcf hf hs
    rw [hcf]
    simp only [RingHom.id_apply, hs, Pi.smul_apply, hf, Finsupp.smul_apply]

def fieldEmbedding : (ℕ →₀ ℝ) →ₗ[ℝ] FieldL2 rate where
  toFun := fieldFinsupp rate
  map_add' f g := by
    apply Lp.ext
    filter_upwards [fieldFinsupp_coeFn rate (f + g), fieldFinsupp_coeFn rate f,
      fieldFinsupp_coeFn rate g, Lp.coeFn_add (fieldFinsupp rate f)
      (fieldFinsupp rate g)] with n hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply, hf, hg, Finsupp.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [fieldFinsupp_coeFn rate (c • f), fieldFinsupp_coeFn rate f,
      Lp.coeFn_smul c (fieldFinsupp rate f)] with n hcf hf hs
    rw [hcf]
    simp only [RingHom.id_apply, hs, Pi.smul_apply, hf, Finsupp.smul_apply]

/-- Positive mass at each Poisson atom turns almost-everywhere equality into pointwise equality. -/
theorem ae_eq_implies_pointwise (hr : 0 < rate) {f g : ℕ → ℝ}
    (h : f =ᵐ[poissonLaw rate] g) (n : ℕ) : f n = g n := by
  by_contra hne
  have hnull : poissonLaw rate {n} = 0 := by
    apply measure_mono_null (t := {k | f k ≠ g k}) ?_ (ae_iff.mp h)
    intro k hk
    have hkn : k = n := Set.mem_singleton_iff.mp hk
    subst k
    exact hne
  have hpos : poissonLaw rate {n} ≠ 0 := by
    intro hz
    have hw : poissonWeight rate n = 0 := by simp [poissonWeight, measureReal_def, hz]
    exact (ne_of_gt (poisson_weight_pos rate hr n)) hw
  exact hpos hnull

/-- The scalar finite-support embedding is injective for positive rate. -/
theorem scalarEmbedding_injective (hr : 0 < rate) :
    Function.Injective (scalarEmbedding rate) := by
  intro f g h
  apply Finsupp.ext
  intro n
  change scalarFinsupp rate f = scalarFinsupp rate g at h
  have hae : (fun n => f n) =ᵐ[poissonLaw rate] (fun n => g n) :=
    (scalarFinsupp_coeFn rate f).symm.trans (by rw [h]; exact scalarFinsupp_coeFn rate g)
  exact ae_eq_implies_pointwise rate hr hae n
/-- The weighted field embedding is injective when the rate is positive. -/
theorem fieldEmbedding_injective (hr : 0 < rate) :
    Function.Injective (fieldEmbedding rate) := by
  intro u v h
  apply Finsupp.ext
  intro n
  change fieldFinsupp rate u = fieldFinsupp rate v at h
  have hae : (fun n => u n) =ᵐ[(rate : ℝ≥0∞) • poissonLaw rate] (fun n => v n) :=
    (fieldFinsupp_coeFn rate u).symm.trans (by rw [h]; exact fieldFinsupp_coeFn rate v)
  have hr0 : (rate : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  exact ae_eq_implies_pointwise rate hr
    ((Measure.ae_ennreal_smul_measure_iff hr0).mp hae) n

/-- Finite-support output for the actual forward difference. -/
def finsuppDifference (f : ℕ →₀ ℝ) : ℕ →₀ ℝ :=
  Finsupp.ofSupportFinite (forwardDifference f) (difference_hasFiniteSupport f)

@[simp] theorem finsuppDifference_apply (f : ℕ →₀ ℝ) (n : ℕ) :
    finsuppDifference f n = f (n + 1) - f n := by
  rfl

/-- Finite-support output for the actual Poisson divergence. -/
def finsuppDivergence (u : ℕ →₀ ℝ) : ℕ →₀ ℝ :=
  Finsupp.ofSupportFinite (poissonDivergenceExpr rate u)
    (divergence_hasFiniteSupport rate u)

@[simp] theorem finsuppDivergence_apply (u : ℕ →₀ ℝ) (n : ℕ) :
    finsuppDivergence rate u n = poissonDivergenceExpr rate u n := by
  rfl

/-- The pointwise Poisson difference is an actual linear map on finite-support functions. -/
def differenceFinsuppLinear : (ℕ →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) where
  toFun := finsuppDifference
  map_add' f g := by
    ext n
    simp only [finsuppDifference_apply, Finsupp.add_apply]
    ring
  map_smul' c f := by
    ext n
    simp only [finsuppDifference_apply, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The pointwise Poisson divergence is linear on finite-support fields. -/
def divergenceFinsuppLinear : (ℕ →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) where
  toFun := finsuppDivergence rate
  map_add' u v := by
    ext n
    cases n with
    | zero => simp [finsuppDivergence_apply, divergence_at_zero, Finsupp.add_apply]; ring
    | succ n => simp [finsuppDivergence_apply, divergence_at_succ, Finsupp.add_apply]; ring
  map_smul' c u := by
    ext n
    cases n with
    | zero => simp [finsuppDivergence_apply, divergence_at_zero, Finsupp.smul_apply]; ring
    | succ n => simp [finsuppDivergence_apply, divergence_at_succ, Finsupp.smul_apply]; ring

/-- Algebraic graph of the genuine Poisson difference in the two L² spaces. -/
def differenceGraph : Submodule ℝ (ScalarL2 rate × FieldL2 rate) :=
  LinearMap.range ((scalarEmbedding rate).prod
    ((fieldEmbedding rate).comp differenceFinsuppLinear))

/-- Algebraic graph of the genuine Poisson divergence. -/
def divergenceGraph : Submodule ℝ (FieldL2 rate × ScalarL2 rate) :=
  LinearMap.range ((fieldEmbedding rate).prod
    ((scalarEmbedding rate).comp (divergenceFinsuppLinear rate)))

theorem differenceGraph_vertical_zero (hr : 0 < rate)
    (z : ScalarL2 rate × FieldL2 rate) (hz : z ∈ differenceGraph rate)
    (hz0 : z.1 = 0) : z.2 = 0 := by
  obtain ⟨f, hf⟩ := hz
  subst z
  have hf0 : f = 0 := scalarEmbedding_injective rate hr (by simpa using hz0)
  change fieldEmbedding rate (differenceFinsuppLinear f) = 0
  rw [hf0, map_zero, map_zero]

theorem divergenceGraph_vertical_zero (hr : 0 < rate)
    (z : FieldL2 rate × ScalarL2 rate) (hz : z ∈ divergenceGraph rate)
    (hz0 : z.1 = 0) : z.2 = 0 := by
  obtain ⟨u, hu⟩ := hz
  subst z
  have hu0 : u = 0 := fieldEmbedding_injective rate hr (by simpa using hz0)
  change scalarEmbedding rate (divergenceFinsuppLinear rate u) = 0
  rw [hu0, map_zero, map_zero]

/-- The finite-support Poisson difference as a genuine partial Hilbert operator. -/
def coreDifference (_hr : 0 < rate) : ScalarL2 rate →ₗ.[ℝ] FieldL2 rate :=
  (differenceGraph rate).toLinearPMap

/-- The finite-support Poisson divergence as a genuine partial Hilbert operator. -/
def coreDivergence (_hr : 0 < rate) : FieldL2 rate →ₗ.[ℝ] ScalarL2 rate :=
  (divergenceGraph rate).toLinearPMap

theorem coreDifference_graph (hr : 0 < rate) :
    (coreDifference rate hr).graph = differenceGraph rate :=
  (differenceGraph rate).toLinearPMap_graph_eq (differenceGraph_vertical_zero rate hr)

theorem coreDivergence_graph (hr : 0 < rate) :
    (coreDivergence rate hr).graph = divergenceGraph rate :=
  (divergenceGraph rate).toLinearPMap_graph_eq (divergenceGraph_vertical_zero rate hr)

/-- Every finite-support scalar belongs to the core domain with its actual difference. -/
theorem coreDifference_finsupp_graph (hr : 0 < rate) (f : ℕ →₀ ℝ) :
    (scalarFinsupp rate f, fieldFinsupp rate (finsuppDifference f)) ∈
      (coreDifference rate hr).graph := by
  rw [coreDifference_graph]
  exact ⟨f, rfl⟩

/-- Every finite-support field belongs to the core domain with its actual divergence. -/
theorem coreDivergence_finsupp_graph (hr : 0 < rate) (u : ℕ →₀ ℝ) :
    (fieldFinsupp rate u, scalarFinsupp rate (finsuppDivergence rate u)) ∈
      (coreDivergence rate hr).graph := by
  rw [coreDivergence_graph]
  exact ⟨u, rfl⟩

/-- The core difference evaluates to the actual finite difference on every core scalar. -/
theorem coreDifference_finsupp_apply (hr : 0 < rate) (f : ℕ →₀ ℝ) :
    (coreDifference rate hr) ⟨scalarFinsupp rate f,
      LinearPMap.mem_domain_of_mem_graph (coreDifference_finsupp_graph rate hr f)⟩ =
        fieldFinsupp rate (finsuppDifference f) := by
  exact ((LinearPMap.image_iff (LinearPMap.mem_domain_of_mem_graph
    (coreDifference_finsupp_graph rate hr f))).2
      (coreDifference_finsupp_graph rate hr f)).symm

/-- The core divergence evaluates to the actual Poisson divergence on every core field. -/
theorem coreDivergence_finsupp_apply (hr : 0 < rate) (u : ℕ →₀ ℝ) :
    (coreDivergence rate hr) ⟨fieldFinsupp rate u,
      LinearPMap.mem_domain_of_mem_graph (coreDivergence_finsupp_graph rate hr u)⟩ =
        scalarFinsupp rate (finsuppDivergence rate u) := by
  exact ((LinearPMap.image_iff (LinearPMap.mem_domain_of_mem_graph
    (coreDivergence_finsupp_graph rate hr u))).2
      (coreDivergence_finsupp_graph rate hr u)).symm
/-- Scalar L² pairings of finite-support classes are genuine Poisson integrals. -/
theorem scalarFinsupp_inner (f g : ℕ →₀ ℝ) :
    inner ℝ (scalarFinsupp rate f) (scalarFinsupp rate g) =
      ∫ n, f n * g n ∂poissonLaw rate := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [scalarFinsupp_coeFn rate f, scalarFinsupp_coeFn rate g] with n hf hg
  rw [hf, hg]
  simp only [Real.inner_apply]

/-- The field inner product has the required rate weighting. -/
theorem fieldFinsupp_inner (f g : ℕ →₀ ℝ) :
    inner ℝ (fieldFinsupp rate f) (fieldFinsupp rate g) =
      (rate : ℝ) * ∫ n, f n * g n ∂poissonLaw rate := by
  rw [L2_inner_eq_integral]
  have hpoint :
      (fun n => inner ℝ ((fieldFinsupp rate f) n) ((fieldFinsupp rate g) n)) =ᵐ[
        (rate : ℝ≥0∞) • poissonLaw rate] (fun n => f n * g n) := by
    filter_upwards [fieldFinsupp_coeFn rate f, fieldFinsupp_coeFn rate g] with n hf hg
    rw [hf, hg]
    simp only [Real.inner_apply]
  rw [integral_congr_ae hpoint, integral_smul_measure]
  rfl

/-- The two actual core operators are formal adjoints, with the correct λ-weighted pairing. -/
theorem coreDifference_formalAdjoint (hr : 0 < rate) :
    (coreDifference rate hr).IsFormalAdjoint (coreDivergence rate hr) := by
  intro f u
  have hf := (coreDifference rate hr).mem_graph f
  have hu := (coreDivergence rate hr).mem_graph u
  rw [coreDifference_graph] at hf
  rw [coreDivergence_graph] at hu
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hu
  have hp1 := congrArg Prod.fst hp
  have hp2 := congrArg Prod.snd hp
  have hq1 := congrArg Prod.fst hq
  have hq2 := congrArg Prod.snd hq
  change scalarFinsupp rate p = (f : ScalarL2 rate) at hp1
  change fieldFinsupp rate (finsuppDifference p) = coreDifference rate hr f at hp2
  change fieldFinsupp rate q = (u : FieldL2 rate) at hq1
  change scalarFinsupp rate (finsuppDivergence rate q) = coreDivergence rate hr u at hq2
  rw [← hp1, ← hp2, ← hq1, ← hq2]
  rw [fieldFinsupp_inner, scalarFinsupp_inner]
  simpa only [finsuppDifference_apply, finsuppDivergence_apply, forwardDifference] using
    poisson_difference_ibp_finsupp rate p q

/-- Pairing with a coordinate indicator extracts the actual L² representative at that atom. -/
theorem scalar_inner_single (v : ScalarL2 rate) (n : ℕ) :
    inner ℝ (scalarFinsupp rate (Finsupp.single n 1)) v =
      poissonWeight rate n * v n := by
  rw [L2_inner_eq_integral]
  have hInt : Integrable (fun k => (Finsupp.single n (1 : ℝ)) k * v k)
      (poissonLaw rate) :=
    mul_L2_integrable (finsupp_memLp_two rate _) (Lp.memLp v)
  have he : (fun k => inner ℝ ((scalarFinsupp rate (Finsupp.single n 1)) k) (v k))
      =ᵐ[poissonLaw rate] (fun k => (Finsupp.single n (1 : ℝ)) k * v k) := by
    filter_upwards [scalarFinsupp_coeFn rate (Finsupp.single n 1)] with k hk
    rw [hk]
    simp only [Real.inner_apply]
  rw [integral_congr_ae he, integral_eq_weighted_tsum rate _ hInt]
  rw [tsum_eq_single n]
  · simp
  · intro k hkn
    simp [Finsupp.single_eq_of_ne hkn]

/-- Vanishing pairings against every finite-support scalar force an L² class to vanish. -/
theorem scalar_eq_zero_of_orthogonal (hr : 0 < rate) (v : ScalarL2 rate)
    (hv : ∀ f : ℕ →₀ ℝ, inner ℝ (scalarFinsupp rate f) v = 0) : v = 0 := by
  have hcoord (n : ℕ) : v n = 0 := by
    have hn := hv (Finsupp.single n 1)
    rw [scalar_inner_single] at hn
    have hw : poissonWeight rate n ≠ 0 := ne_of_gt (poisson_weight_pos rate hr n)
    exact (mul_eq_zero.mp hn).resolve_left hw
  apply Lp.ext
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := poissonLaw rate)] with n hz
  exact (hcoord n).trans hz.symm

/-- The finite-support scalar domain is dense in the actual Poisson L² space. -/
theorem scalarEmbedding_dense (hr : 0 < rate) :
    Dense ((scalarEmbedding rate).range : Set (ScalarL2 rate)) := by
  have hb : (scalarEmbedding rate).range.topologicalClosureᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro v hv
    apply scalar_eq_zero_of_orthogonal rate hr v
    intro f
    exact (scalarEmbedding rate).range.topologicalClosure.inner_right_of_mem_orthogonal
      ((scalarEmbedding rate).range.le_topologicalClosure ⟨f, rfl⟩) hv
  have ht := Submodule.orthogonal_eq_bot_iff.mp hb
  rw [dense_iff_closure_eq]
  change ((scalarEmbedding rate).range.topologicalClosure : Set (ScalarL2 rate)) = Set.univ
  rw [ht]
  rfl

/-- A weighted coordinate indicator extracts the field value with coefficient λ μ{n}. -/
theorem field_inner_single (hr : 0 < rate) (v : FieldL2 rate) (n : ℕ) :
    inner ℝ (fieldFinsupp rate (Finsupp.single n 1)) v =
      (rate : ℝ) * poissonWeight rate n * v n := by
  rw [L2_inner_eq_integral]
  have hr0 : (rate : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hIntW : Integrable (fun k => (Finsupp.single n (1 : ℝ)) k * v k)
      ((rate : ℝ≥0∞) • poissonLaw rate) :=
    mul_L2_integrable (finsupp_memLp_two_weighted rate _) (Lp.memLp v)
  have hInt : Integrable (fun k => (Finsupp.single n (1 : ℝ)) k * v k)
      (poissonLaw rate) :=
    (integrable_smul_measure hr0 (by finiteness)).mp hIntW
  have he : (fun k => inner ℝ ((fieldFinsupp rate (Finsupp.single n 1)) k) (v k))
      =ᵐ[(rate : ℝ≥0∞) • poissonLaw rate]
        (fun k => (Finsupp.single n (1 : ℝ)) k * v k) := by
    filter_upwards [fieldFinsupp_coeFn rate (Finsupp.single n 1)] with k hk
    rw [hk]
    simp only [Real.inner_apply]
  rw [integral_congr_ae he, integral_smul_measure,
    integral_eq_weighted_tsum rate _ hInt, tsum_eq_single n]
  · simp
    ring
  · intro k hkn
    simp [Finsupp.single_eq_of_ne hkn]

/-- Finite-support fields are dense in the rate-weighted Poisson L² space. -/
theorem fieldEmbedding_dense (hr : 0 < rate) :
    Dense ((fieldEmbedding rate).range : Set (FieldL2 rate)) := by
  have hb : (fieldEmbedding rate).range.topologicalClosureᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro v hv
    have hcoord (n : ℕ) : v n = 0 := by
      have hn := (fieldEmbedding rate).range.topologicalClosure.inner_right_of_mem_orthogonal
        ((fieldEmbedding rate).range.le_topologicalClosure
          ⟨Finsupp.single n 1, rfl⟩) hv
      change inner ℝ (fieldFinsupp rate (Finsupp.single n 1)) v = 0 at hn
      rw [field_inner_single rate hr] at hn
      have hrreal : (rate : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
      have hw : poissonWeight rate n ≠ 0 := ne_of_gt (poisson_weight_pos rate hr n)
      exact (mul_eq_zero.mp hn).resolve_left (mul_ne_zero hrreal hw)
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2)
      (μ := (rate : ℝ≥0∞) • poissonLaw rate)] with n hz
    exact (hcoord n).trans hz.symm
  have ht := Submodule.orthogonal_eq_bot_iff.mp hb
  rw [dense_iff_closure_eq]
  change ((fieldEmbedding rate).range.topologicalClosure : Set (FieldL2 rate)) = Set.univ
  rw [ht]
  rfl

/-- The core difference has a dense domain in scalar Poisson L². -/
theorem coreDifference_dense_domain (hr : 0 < rate) :
    Dense ((coreDifference rate hr).domain : Set (ScalarL2 rate)) := by
  apply (scalarEmbedding_dense rate hr).mono
  rintro x ⟨f, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (coreDifference_finsupp_graph rate hr f)

/-- The core divergence has a dense domain in weighted Poisson L². -/
theorem coreDivergence_dense_domain (hr : 0 < rate) :
    Dense ((coreDivergence rate hr).domain : Set (FieldL2 rate)) := by
  apply (fieldEmbedding_dense rate hr).mono
  rintro x ⟨u, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (coreDivergence_finsupp_graph rate hr u)

/-- The Poisson difference core is contained in the Hilbert adjoint of divergence. -/
theorem coreDifference_le_divergence_adjoint (hr : 0 < rate) :
    coreDifference rate hr ≤ (coreDivergence rate hr).adjoint :=
  (coreDifference_formalAdjoint rate hr).symm.le_adjoint
    (coreDivergence_dense_domain rate hr)

/-- The Poisson divergence core is contained in the Hilbert adjoint of difference. -/
theorem coreDivergence_le_difference_adjoint (hr : 0 < rate) :
    coreDivergence rate hr ≤ (coreDifference rate hr).adjoint :=
  (coreDifference_formalAdjoint rate hr).le_adjoint
    (coreDifference_dense_domain rate hr)

/-- Density and integration by parts imply genuine closability of the difference core. -/
theorem coreDifference_isClosable (hr : 0 < rate) :
    (coreDifference rate hr).IsClosable :=
  ((coreDivergence rate hr).adjoint_isClosed (coreDivergence_dense_domain rate hr)).isClosable
    |>.leIsClosable (coreDifference_le_divergence_adjoint rate hr)

/-- Density and integration by parts imply genuine closability of the divergence core. -/
theorem coreDivergence_isClosable (hr : 0 < rate) :
    (coreDivergence rate hr).IsClosable :=
  ((coreDifference rate hr).adjoint_isClosed (coreDifference_dense_domain rate hr)).isClosable
    |>.leIsClosable (coreDivergence_le_difference_adjoint rate hr)

end OperatorDerivativeRewrite.Foundation.PoissonDifferenceOperators
