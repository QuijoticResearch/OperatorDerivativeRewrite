import Foundation.OneSidedBlockKernel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The actual 72-component incidence map has one gauge dimension and rank31. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedBlockRank
open OneSidedBlockIncidence OneSidedBlockKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

abbrev Interior := {e : EdgeData // e∈edges}
abbrev Inner := {p : FaceData // p∈innerFaces}
abbrev Upper := {p : EdgeData × Fin 4 // p∈upperFaces}
abbrev Field := Interior → ℝ
abbrev Curvature := (Inner → ℝ) × (Upper → ℝ)

def extend (f : Field) (e : EdgeData) : ℝ := if he : e∈edges then f ⟨e,he⟩ else 0

theorem extend_on (f : Field) (e : Interior) : extend f e=f e := by simp [extend,e.property]

theorem extend_add (f g : Field) (e : EdgeData) : extend (f+g) e=extend f e+extend g e := by
  by_cases he : e∈edges <;> simp [extend,he]

theorem extend_smul (c : ℝ) (f : Field) (e : EdgeData) : extend (c • f) e=c*extend f e := by
  by_cases he : e∈edges <;> simp [extend,he]

def incidence : Field →ₗ[ℝ] Curvature where
  toFun f := (fun p => realCurl (extend f) p,fun p => extend f p.1.1)
  map_add' f g := by
    apply Prod.ext <;> funext p
    · simp only [Prod.fst_add,Pi.add_apply,realCurl,extend_add]
      ring
    · simp [extend_add]
  map_smul' c f := by
    apply Prod.ext <;> funext p
    · change realCurl (extend (c • f)) p=c*realCurl (extend f) p
      simp only [realCurl,extend_smul]
      ring
    · simp [extend_smul,smul_eq_mul]

def gauge : Field := fun e => originField e

theorem incidence_zero_iff (f : Field) : incidence f=0 ↔ realEnergy (extend f)=0 := by
  constructor
  · intro h
    unfold realEnergy
    have hi : ∑ p∈innerFaces, (realCurl (extend f) p)^2=0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hz := congrArg (fun z : Curvature => z.1 ⟨p,hp⟩) h
      change realCurl (extend f) p=0 at hz
      rw [hz]
      norm_num
    have hu : ∑ p∈upperFaces, (extend f p.1)^2=0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hz := congrArg (fun z : Curvature => z.2 ⟨p,hp⟩) h
      change extend f p.1=0 at hz
      rw [hz]
      norm_num
    rw [hi,hu,add_zero]
  · intro h
    apply Prod.ext <;> funext p
    · exact inner_zero (extend f) h p p.property
    · exact upper_zero (extend f) h p p.property

theorem gauge_nonzero : gauge≠0 := by
  intro h
  have hv := congrFun h (⟨(origin,0),by decide⟩ : Interior)
  norm_num [gauge,originField,originStar] at hv

theorem gauge_incidence_zero : incidence gauge=0 := by
  apply (incidence_zero_iff gauge).mpr
  have he : ∀ e∈edges, extend gauge e=1*originField e := by
    intro e he
    simp [extend,gauge,he]
  rw [realEnergy_congr _ (fun e => 1*originField e) he]
  exact scalar_origin_zero 1

theorem kernel_span : LinearMap.ker incidence=Submodule.span ℝ ({gauge} : Set Field) := by
  apply le_antisymm
  · intro f hf
    have hz : realEnergy (extend f)=0 := (incidence_zero_iff f).mp hf
    have hc := kernel_classification (extend f) hz
    have he : f=extend f (origin,0) • gauge := by
      funext e
      have h := hc e e.property
      simpa [extend,gauge,e.property,smul_eq_mul] using h
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro f hf
    have he : f=gauge := Set.mem_singleton_iff.mp hf
    subst f
    exact gauge_incidence_zero

theorem interior_card : Fintype.card Interior=32 := by
  simpa only [Fintype.card_coe] using edges_card

theorem inner_card : Fintype.card Inner=24 := by
  simpa only [Fintype.card_coe] using innerFaces_card

theorem upper_card : Fintype.card Upper=48 := by
  simpa only [Fintype.card_coe] using upperFaces_card

theorem field_finrank : Module.finrank ℝ Field=32 := by
  rw [Module.finrank_pi,interior_card]

theorem curvature_finrank : Module.finrank ℝ Curvature=72 := by
  simp only [Curvature,Module.finrank_prod,Module.finrank_pi,inner_card,upper_card]

theorem kernel_finrank : Module.finrank ℝ (LinearMap.ker incidence)=1 := by
  rw [kernel_span]
  exact finrank_span_singleton gauge_nonzero

theorem incidence_rank : Module.finrank ℝ (LinearMap.range incidence)=31 := by
  have h := LinearMap.finrank_range_add_finrank_ker incidence
  rw [kernel_finrank,field_finrank] at h
  omega

def gaugePotential (v : Vertex) : ℝ := if v=origin then -1 else 0

def latticeGradient (phi : Vertex → ℝ) (e : EdgeData) : ℝ :=
  phi (shifted e.1 e.2)-phi e.1

theorem shifted_target_nonorigin : ∀ e∈edges, shifted e.1 e.2≠origin := by decide

theorem gauge_is_gradient (e : EdgeData) (he : e∈edges) :
    latticeGradient gaugePotential e=originField e := by
  have ht := shifted_target_nonorigin e he
  by_cases ho : e.1=origin
  · have ht' : shifted origin e.2≠origin := by simpa only [ho] using ht
    simp [latticeGradient,gaugePotential,ht',originField,originStar,ho]
  · simp [latticeGradient,gaugePotential,ht,originField,originStar,ho]

end OperatorDerivativeRewrite.Foundation.OneSidedBlockRank
