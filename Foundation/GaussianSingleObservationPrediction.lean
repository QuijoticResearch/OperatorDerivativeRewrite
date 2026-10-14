import Foundation.GaussianWickConditionalProjection

/-! Density of actual one-direction Wick classes and sufficiency of the
linear Gaussian forecast for every terminal L2 observable. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianSingleObservationPrediction
open InfiniteGaussian GaussianTimeSpaceHermite GaussianConditionalGraph
open GaussianWickConditionalProjection GaussianWickPredictionBound

def algebraicSpan (τ : ℝ) : Submodule ℝ (MvPolynomial Unit ℝ) :=
  Submodule.span ℝ (Set.range (polynomial τ))

theorem X_mul_zero (τ : ℝ) : MvPolynomial.X ()*polynomial τ 0=polynomial τ 1 := by simp

theorem X_mul_succ (τ : ℝ) (n : ℕ) :
    MvPolynomial.X ()*polynomial τ (n+1)=polynomial τ (n+2)+((n+1 : ℝ)*τ) • polynomial τ n := by
  rw [polynomial_recursion,sub_add_cancel]

theorem X_mul_mem (τ : ℝ) (p : MvPolynomial Unit ℝ) (hp : p∈algebraicSpan τ) :
    MvPolynomial.X ()*p∈algebraicSpan τ := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n,rfl⟩ := hp
    have hm (i : ℕ) : polynomial τ i∈algebraicSpan τ := Submodule.subset_span ⟨i,rfl⟩
    cases n with
    | zero => rw [X_mul_zero]; exact hm 1
    | succ n =>
      rw [X_mul_succ]
      exact (algebraicSpan τ).add_mem (hm (n+2)) ((algebraicSpan τ).smul_mem _ (hm n))
  | zero => simp
  | add p q hp hq ihp ihq => rw [mul_add]; exact (algebraicSpan τ).add_mem ihp ihq
  | smul c p hp ih => rw [mul_smul_comm]; exact (algebraicSpan τ).smul_mem c ih

theorem algebraicSpan_eq_top (τ : ℝ) : algebraicSpan τ=⊤ := by
  have hAll (p : MvPolynomial Unit ℝ) : p∈algebraicSpan τ := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      have hm : polynomial τ 0∈algebraicSpan τ := Submodule.subset_span ⟨0,rfl⟩
      simpa only [polynomial_zero,Algebra.smul_def,mul_one,MvPolynomial.algebraMap_eq] using (algebraicSpan τ).smul_mem c hm
    | add p q hp hq => exact (algebraicSpan τ).add_mem hp hq
    | mul_X p i hp =>
      cases i
      rw [mul_comm]
      exact X_mul_mem τ p hp
  exact top_unique (fun p _ => hAll p)

def wickClass (u : CoefficientSpace) (n : ℕ) : GaussianL2 := wick u n

def wickSpan (u : CoefficientSpace) : Submodule ℝ GaussianL2 :=
  Submodule.span ℝ (Set.range (wickClass u))

def singleGenerated (u : CoefficientSpace) : Submodule ℝ GaussianL2 :=
  generated (fun _ : Unit => u)

theorem wickSpan_range (u : CoefficientSpace) :
    wickSpan u=(familyPolynomialEmbedding (fun _ : Unit => u)).range := by
  let L := familyPolynomialEmbedding (fun _ : Unit => u)
  have he : Set.range (wickClass u)=L '' Set.range (polynomial (‖u‖^2)) := by
    ext f
    constructor
    · rintro ⟨n,rfl⟩
      exact ⟨polynomial (‖u‖^2) n,⟨n,rfl⟩,rfl⟩
    · rintro ⟨p,⟨n,rfl⟩,rfl⟩
      exact ⟨n,rfl⟩
  rw [wickSpan,he,Submodule.span_image]
  change Submodule.map L (algebraicSpan (‖u‖^2))=L.range
  rw [algebraicSpan_eq_top,Submodule.map_top]

theorem wickSpan_closure (u : CoefficientSpace) :
    (wickSpan u).topologicalClosure=singleGenerated u := by
  rw [wickSpan_range]
  exact familyPolynomial_closure (fun _ : Unit => u)

theorem sourceProjection_single_mean {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    sourceProjection (fun _ : Unit => sourceProjection h u) u=sourceProjection h u := by
  let v := sourceProjection h u
  have hv : v∈sourceSpan h := (sourceSpan h).starProjection_apply_mem u
  have hs : sourceSpan (fun _ : Unit => v) ≤ sourceSpan h := by
    have hspan : Submodule.span ℝ (Set.range (fun _ : Unit => v)) ≤ sourceSpan h := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hv
    exact (Submodule.span ℝ (Set.range (fun _ : Unit => v))).topologicalClosure_minimal hspan
      (Submodule.isClosed_topologicalClosure _)
  have hm : v∈sourceSpan (fun _ : Unit => v) :=
    (Submodule.span ℝ (Set.range (fun _ : Unit => v))).le_topologicalClosure
      (Submodule.subset_span ⟨(),rfl⟩)
  have ho : u-v∈(sourceSpan h)ᗮ := (sourceSpan h).sub_starProjection_mem_orthogonal u
  exact (sourceSpan (fun _ : Unit => v)).eq_starProjection_of_mem_orthogonal hm
    (Submodule.orthogonal_le hs ho)

theorem conditional_singleObservation_sufficient {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (f : GaussianL2) (hf : f∈singleGenerated u) :
    conditionalProjection h f=conditionalProjection (fun _ : Unit => sourceProjection h u) f := by
  let L := conditionalProjection h-conditionalProjection (fun _ : Unit => sourceProjection h u)
  have hs : wickSpan u≤L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    change conditionalProjection h (wick u n)-
      conditionalProjection (fun _ : Unit => sourceProjection h u) (wick u n)=0
    rw [conditional_wick_projection,conditional_wick_projection,sourceProjection_single_mean,sub_self]
  have hc := (wickSpan u).topologicalClosure_minimal hs L.isClosed_ker
  rw [wickSpan_closure] at hc
  have he := hc hf
  change conditionalProjection h f-conditionalProjection (fun _ : Unit => sourceProjection h u) f=0 at he
  exact sub_eq_zero.mp he

theorem conditional_singleObservation_range {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (f : GaussianL2) (hf : f∈singleGenerated u) :
    conditionalProjection h f∈singleGenerated (sourceProjection h u) := by
  rw [conditional_singleObservation_sufficient h u f hf]
  exact (generated (fun _ : Unit => sourceProjection h u)).starProjection_apply_mem f

end OperatorDerivativeRewrite.Foundation.GaussianSingleObservationPrediction

