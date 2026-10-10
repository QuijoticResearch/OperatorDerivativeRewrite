import Foundation.OperatorDomains
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# A bounded multiplier algebra for the given divergence

A multiplier must preserve δ's domain and have a bounded commutator with δ.
These properties imply invariance of the actual adjoint domain. They are not a
Leibniz hypothesis for δ*. The resulting algebra is not asserted to be graph-dense.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Multiplication by an essentially bounded real function on L²(H). -/
def boundedMultiplier (f : Ω → ℝ) (hf : MemLp f ∞ μ) : Lp H 2 μ →L[ℝ] Lp H 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ lpSmul (r := 2) (hf.toLp f) u
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [lpSmul_coeFn (r := 2) (hf.toLp f) (u + v),
          lpSmul_coeFn (r := 2) (hf.toLp f) u, lpSmul_coeFn (r := 2) (hf.toLp f) v,
          Lp.coeFn_add u v, Lp.coeFn_add (lpSmul (r := 2) (hf.toLp f) u)
            (lpSmul (r := 2) (hf.toLp f) v)] with ω huv hu hv hadd hout
        rw [huv, hout]
        simp only [Pi.add_apply]
        rw [hu, hv, hadd]
        simp only [Pi.add_apply, smul_add]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [lpSmul_coeFn (r := 2) (hf.toLp f) (c • u),
          lpSmul_coeFn (r := 2) (hf.toLp f) u, Lp.coeFn_smul c u,
          Lp.coeFn_smul c (lpSmul (r := 2) (hf.toLp f) u)] with ω hcu hu hin hout
        simp only [RingHom.id_apply]
        rw [hcu, hout]
        simp only [Pi.smul_apply]
        rw [hu, hin]
        simp only [Pi.smul_apply]
        exact smul_comm _ _ _ }
    ‖hf.toLp f‖ (fun u ↦ lpSmul_norm_le (hf.toLp f) u)

theorem boundedMultiplier_coeFn (f : Ω → ℝ) (hf : MemLp f ∞ μ) (u : Lp H 2 μ) :
    boundedMultiplier f hf u =ᵐ[μ] fun ω ↦ f ω • u ω := by
  filter_upwards [lpSmul_coeFn (r := 2) (hf.toLp f) u, hf.coeFn_toLp] with ω hu hfω
  exact hu.trans (congrArg (fun c ↦ c • u ω) hfω)

theorem boundedMultiplier_add (f g : Ω → ℝ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    boundedMultiplier (H := H) (f + g) (hf.add hg) =
      boundedMultiplier f hf + boundedMultiplier g hg := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedMultiplier_coeFn (f + g) (hf.add hg) u,
    boundedMultiplier_coeFn f hf u, boundedMultiplier_coeFn g hg u,
    Lp.coeFn_add (boundedMultiplier f hf u) (boundedMultiplier g hg u)] with ω hsum hfω hgω hout
  simp only [add_apply, hout, hsum, hfω, hgω, Pi.add_apply, add_smul]

theorem boundedMultiplier_mul (f g : Ω → ℝ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    boundedMultiplier (H := H) (f * g) (mul_memLp hf hg) =
      (boundedMultiplier f hf).comp (boundedMultiplier g hg) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedMultiplier_coeFn (f * g) (mul_memLp hf hg) u,
    boundedMultiplier_coeFn f hf (boundedMultiplier g hg u),
    boundedMultiplier_coeFn g hg u] with ω hprod hfω hgω
  simp only [ContinuousLinearMap.comp_apply, hprod, hfω, hgω, Pi.mul_apply, mul_smul]

theorem boundedMultiplier_const (c : ℝ) :
    boundedMultiplier (fun _ : Ω ↦ c) (memLp_top_const c) =
      c • ContinuousLinearMap.id ℝ (Lp H 2 μ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedMultiplier_coeFn (fun _ : Ω ↦ c) (memLp_top_const c) u,
    Lp.coeFn_smul c u] with ω hc hcu
  exact hc.trans hcu.symm

theorem boundedMultiplier_symmetric (f : Ω → ℝ) (hf : MemLp f ∞ μ) (u v : Lp H 2 μ) :
    inner ℝ (boundedMultiplier f hf u) v = inner ℝ u (boundedMultiplier f hf v) :=
  L2_bounded_multiplier_selfadj (hf.toLp f) u v

/-- An admissible multiplier preserves the GIVEN divergence domain and has a bounded
commutator. R is δ's commutator, not a separately assigned derivative of f. -/
def IsDivergenceMultiplier (δ : Lp H 2 μ →ₗ.[ℝ] Lp ℝ 2 μ) (f : Ω → ℝ) : Prop :=
  ∃ hf : MemLp f ∞ μ, ∃ R : Lp H 2 μ →L[ℝ] Lp ℝ 2 μ,
    ∃ hdom : ∀ u : δ.domain, boundedMultiplier f hf (u : Lp H 2 μ) ∈ δ.domain,
      ∀ u : δ.domain, δ ⟨boundedMultiplier f hf u, hdom u⟩ =
        boundedMultiplier f hf (δ u) - R (u : Lp H 2 μ)

variable (δ : Lp H 2 μ →ₗ.[ℝ] Lp ℝ 2 μ)

/-- Constants are admissible by the linearity of δ. -/
theorem isDivergenceMultiplier_const (c : ℝ) : IsDivergenceMultiplier δ (fun _ ↦ c) := by
  let hf : MemLp (fun _ : Ω ↦ c) ∞ μ := memLp_top_const c
  have hdom : ∀ u : δ.domain, boundedMultiplier (fun _ ↦ c) hf (u : Lp H 2 μ) ∈ δ.domain := by
    intro u
    rw [boundedMultiplier_const]
    exact δ.domain.smul_mem c u.property
  refine ⟨hf, 0, hdom, fun u ↦ ?_⟩
  have heq : (⟨boundedMultiplier (fun _ ↦ c) hf u, hdom u⟩ : δ.domain) = c • u := by
    apply Subtype.ext
    simp [boundedMultiplier_const]
  rw [heq, δ.map_smul]
  simp [boundedMultiplier_const]

/-- Sums preserve admissibility, with commutator R_f + R_g. -/
theorem IsDivergenceMultiplier.add {f g : Ω → ℝ}
    (hf : IsDivergenceMultiplier δ f) (hg : IsDivergenceMultiplier δ g) :
    IsDivergenceMultiplier δ (f + g) := by
  obtain ⟨hf, Rf, hdf, hef⟩ := hf
  obtain ⟨hg, Rg, hdg, heg⟩ := hg
  have hdom : ∀ u : δ.domain, boundedMultiplier (f + g) (hf.add hg) (u : Lp H 2 μ) ∈ δ.domain := by
    intro u
    rw [boundedMultiplier_add f g hf hg, add_apply]
    exact δ.domain.add_mem (hdf u) (hdg u)
  refine ⟨hf.add hg, Rf + Rg, hdom, fun u ↦ ?_⟩
  have heq : (⟨boundedMultiplier (f + g) (hf.add hg) u, hdom u⟩ : δ.domain) =
      ⟨boundedMultiplier f hf u, hdf u⟩ + ⟨boundedMultiplier g hg u, hdg u⟩ := by
    apply Subtype.ext
    simp [boundedMultiplier_add f g hf hg]
  rw [heq, δ.map_add, hef, heg, boundedMultiplier_add f g hf hg]
  simp only [add_apply]
  abel

/-- Products preserve admissibility. The commutator is M_f R_g + R_f M_g.
This proves closure from δ's actual equations, rather than assuming closure of dom(δ*). -/
theorem IsDivergenceMultiplier.mul {f g : Ω → ℝ}
    (hf : IsDivergenceMultiplier δ f) (hg : IsDivergenceMultiplier δ g) :
    IsDivergenceMultiplier δ (f * g) := by
  obtain ⟨hf, Rf, hdf, hef⟩ := hf
  obtain ⟨hg, Rg, hdg, heg⟩ := hg
  let gu (u : δ.domain) : δ.domain := ⟨boundedMultiplier g hg u, hdg u⟩
  have hdom : ∀ u : δ.domain,
      boundedMultiplier (f * g) (mul_memLp hf hg) (u : Lp H 2 μ) ∈ δ.domain := by
    intro u
    rw [boundedMultiplier_mul f g hf hg, ContinuousLinearMap.comp_apply]
    exact hdf (gu u)
  refine ⟨mul_memLp hf hg, (boundedMultiplier f hf).comp Rg + Rf.comp (boundedMultiplier g hg),
    hdom, fun u ↦ ?_⟩
  have heq : (⟨boundedMultiplier (f * g) (mul_memLp hf hg) u, hdom u⟩ : δ.domain) =
      ⟨boundedMultiplier f hf (gu u), hdf (gu u)⟩ := by
    apply Subtype.ext
    simp [gu, boundedMultiplier_mul f g hf hg]
  rw [heq, hef, heg]
  simp only [boundedMultiplier_mul f g hf hg, ContinuousLinearMap.comp_apply,
    add_apply, map_sub, gu]
  abel

/-- The algebra of admissible bounded multipliers. No density is part of this definition. -/
def boundedMultiplierAlgebra : Subalgebra ℝ (Ω → ℝ) where
  carrier := {f | IsDivergenceMultiplier δ f}
  algebraMap_mem' := isDivergenceMultiplier_const δ
  add_mem' := IsDivergenceMultiplier.add δ
  mul_mem' := IsDivergenceMultiplier.mul δ

/-- For a bounded everywhere-defined δ every bounded multiplier is admissible.
No derivation property of δ* is used. -/
theorem isDivergenceMultiplier_bounded (A : Lp H 2 μ →L[ℝ] Lp ℝ 2 μ)
    (f : Ω → ℝ) (hf : MemLp f ∞ μ) : IsDivergenceMultiplier (A.toPMap ⊤) f := by
  have hdom : ∀ u : (A.toPMap ⊤).domain,
      boundedMultiplier f hf (u : Lp H 2 μ) ∈ (A.toPMap ⊤).domain := fun _ ↦ Submodule.mem_top
  refine ⟨hf, (boundedMultiplier f hf).comp A - A.comp (boundedMultiplier f hf), hdom, fun u ↦ ?_⟩
  change A (boundedMultiplier f hf (u : Lp H 2 μ)) =
    boundedMultiplier f hf (A (u : Lp H 2 μ)) -
    (((boundedMultiplier f hf).comp A - A.comp (boundedMultiplier f hf)) (u : Lp H 2 μ))
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  abel

/-- On a dense divergence domain, the bounded commutator is forced uniquely by δ. -/
theorem divergenceCommutator_unique (f : Ω → ℝ) (hf : MemLp f ∞ μ)
    (hδ : Dense (δ.domain : Set (Lp H 2 μ)))
    (hdom : ∀ u : δ.domain, boundedMultiplier f hf (u : Lp H 2 μ) ∈ δ.domain)
    (R S : Lp H 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : ∀ u : δ.domain, δ ⟨boundedMultiplier f hf u, hdom u⟩ =
      boundedMultiplier f hf (δ u) - R (u : Lp H 2 μ))
    (hS : ∀ u : δ.domain, δ ⟨boundedMultiplier f hf u, hdom u⟩ =
      boundedMultiplier f hf (δ u) - S (u : Lp H 2 μ)) : R = S := by
  apply DFunLike.ext'
  apply R.continuous.ext_on hδ S.continuous
  intro u hu
  have hsub := (hR ⟨u, hu⟩).symm.trans (hS ⟨u, hu⟩)
  apply neg_injective
  apply add_left_cancel (a := boundedMultiplier f hf (δ ⟨u, hu⟩))
  simpa only [sub_eq_add_neg] using hsub

/-- It suffices to check the divergence conditions on generators: all finite algebraic
combinations then belong to the verified multiplier algebra. -/
theorem adjoin_le_boundedMultiplierAlgebra (s : Set (Ω → ℝ))
    (hs : ∀ f ∈ s, IsDivergenceMultiplier δ f) :
    Algebra.adjoin ℝ s ≤ boundedMultiplierAlgebra δ := Algebra.adjoin_le hs
section Adjoint
variable [CompleteSpace H]

/-- Domain invariance for the ACTUAL adjoint follows from the divergence commutator.
The proof constructs a Riesz representer from δ*, the multiplier and R*, not a new derivative. -/
theorem IsDivergenceMultiplier.preserves_adjoint_domain {f : Ω → ℝ}
    (hf : MemLp f ∞ μ) (h : IsDivergenceMultiplier δ f)
    (hδ : Dense (δ.domain : Set (Lp H 2 μ))) (F : δ.adjoint.domain) :
    boundedMultiplier f hf (F : Lp ℝ 2 μ) ∈ δ.adjoint.domain := by
  obtain ⟨hf', R, hdom, hcomm⟩ := h
  apply δ.mem_adjoint_domain_of_exists
  refine ⟨boundedMultiplier f hf (δ.adjoint F) + R.adjoint (F : Lp ℝ 2 μ), fun u ↦ ?_⟩
  calc
    inner ℝ (boundedMultiplier f hf (δ.adjoint F) + R.adjoint (F : Lp ℝ 2 μ)) (u : Lp H 2 μ) =
        inner ℝ (δ.adjoint F) (boundedMultiplier f hf u) + inner ℝ (F : Lp ℝ 2 μ) (R u) := by
      rw [inner_add_left, boundedMultiplier_symmetric, R.adjoint_inner_left]
    _ = inner ℝ (F : Lp ℝ 2 μ) (δ ⟨boundedMultiplier f hf' u, hdom u⟩) +
        inner ℝ (F : Lp ℝ 2 μ) (R u) := by
      rw [δ.adjoint_isFormalAdjoint hδ F ⟨boundedMultiplier f hf' u, hdom u⟩]
    _ = inner ℝ (F : Lp ℝ 2 μ) (boundedMultiplier f hf (δ u)) := by
      rw [hcomm, inner_sub_right]
      ring
    _ = inner ℝ (boundedMultiplier f hf (F : Lp ℝ 2 μ)) (δ u) :=
      (boundedMultiplier_symmetric f hf (F : Lp ℝ 2 μ) (δ u)).symm

variable [IsFiniteMeasure μ]

/-- The canonical L² class of an essentially bounded function on a finite measure space. -/
def boundedToL2 (f : Ω → ℝ) (hf : MemLp f ∞ μ) : Lp ℝ 2 μ :=
  (hf.mono_exponent le_top).toLp f

theorem boundedToL2_coeFn (f : Ω → ℝ) (hf : MemLp f ∞ μ) :
    boundedToL2 f hf =ᵐ[μ] f := MemLp.coeFn_toLp _

/-- Products in the multiplier algebra have their genuine pointwise L² interpretation. -/
theorem boundedToL2_mul (f g : Ω → ℝ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    boundedToL2 (f * g) (mul_memLp hf hg) = boundedMultiplier f hf (boundedToL2 g hg) := by
  apply Lp.ext
  filter_upwards [boundedToL2_coeFn (f * g) (mul_memLp hf hg),
    boundedMultiplier_coeFn f hf (boundedToL2 g hg), boundedToL2_coeFn g hg] with ω hfg hfω hgω
  simp only [hfg, hfω, hgω, Pi.mul_apply, smul_eq_mul]

/-- Centeredness puts the constant one in the actual adjoint domain. -/
theorem one_mem_adjoint_domain
    (hcenter : ∀ u : δ.domain, (∫ ω, (δ u : Ω → ℝ) ω ∂μ) = 0) :
    boundedToL2 (fun _ ↦ (1 : ℝ)) (memLp_top_const 1) ∈ δ.adjoint.domain := by
  apply δ.mem_adjoint_domain_of_exists
  refine ⟨0, fun u ↦ ?_⟩
  have hi : inner ℝ (boundedToL2 (fun _ ↦ (1 : ℝ)) (memLp_top_const 1)) (δ u) = 0 := by
    rw [L2_inner_eq_integral]
    calc
      (∫ ω, inner ℝ (boundedToL2 (fun _ ↦ (1 : ℝ)) (memLp_top_const 1) ω) (δ u ω) ∂μ) =
          ∫ ω, δ u ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [boundedToL2_coeFn (fun _ ↦ (1 : ℝ)) (memLp_top_const 1)] with ω hω
        simp [hω]
      _ = 0 := hcenter u
  simpa only [inner_zero_left] using hi.symm

/-- Every admissible bounded function belongs to dom(δ*) for a centered densely defined δ. -/
theorem IsDivergenceMultiplier.mem_adjoint_domain {f : Ω → ℝ}
    (hf : MemLp f ∞ μ) (h : IsDivergenceMultiplier δ f)
    (hδ : Dense (δ.domain : Set (Lp H 2 μ)))
    (hcenter : ∀ u : δ.domain, (∫ ω, (δ u : Ω → ℝ) ω ∂μ) = 0) :
    boundedToL2 f hf ∈ δ.adjoint.domain := by
  have hone := one_mem_adjoint_domain δ hcenter
  have hprod := h.preserves_adjoint_domain δ hf hδ
    ⟨boundedToL2 (fun _ ↦ (1 : ℝ)) (memLp_top_const 1), hone⟩
  have heq : boundedToL2 f hf =
      boundedMultiplier f hf (boundedToL2 (fun _ ↦ (1 : ℝ)) (memLp_top_const 1)) := by
    have hm := boundedToL2_mul f (fun _ ↦ (1 : ℝ)) hf (memLp_top_const 1)
    have hfun : f * (fun _ : Ω ↦ (1 : ℝ)) = f := by funext ω; simp
    simpa only [hfun] using hm
  rw [heq]
  exact hprod

/-- Genuine product closure in the actual adjoint domain on the chosen multiplier algebra.
No Leibniz identity for δ* is a hypothesis or a conclusion. -/
theorem multiplierAlgebra_product_mem_adjoint_domain
    (hδ : Dense (δ.domain : Set (Lp H 2 μ)))
    (hcenter : ∀ u : δ.domain, (∫ ω, (δ u : Ω → ℝ) ω ∂μ) = 0)
    (f g : boundedMultiplierAlgebra δ) :
    ∃ hfg : MemLp ((f : Ω → ℝ) * (g : Ω → ℝ)) ∞ μ,
      boundedToL2 ((f : Ω → ℝ) * (g : Ω → ℝ)) hfg ∈ δ.adjoint.domain := by
  have h : IsDivergenceMultiplier δ ((f : Ω → ℝ) * (g : Ω → ℝ)) :=
    IsDivergenceMultiplier.mul δ f.property g.property
  obtain ⟨hfg, _, _, _⟩ := h
  exact ⟨hfg, IsDivergenceMultiplier.mem_adjoint_domain δ hfg
    (IsDivergenceMultiplier.mul δ f.property g.property) hδ hcenter⟩
/-- Product-domain closure for the algebraic test core generated by any admissible family.
Only the generators need commutator hypotheses; product membership is proved. -/
theorem generatedAlgebra_product_mem_adjoint_domain
    (hδ : Dense (δ.domain : Set (Lp H 2 μ)))
    (hcenter : ∀ u : δ.domain, (∫ ω, (δ u : Ω → ℝ) ω ∂μ) = 0)
    (s : Set (Ω → ℝ)) (hs : ∀ f ∈ s, IsDivergenceMultiplier δ f)
    (f g : Algebra.adjoin ℝ s) :
    ∃ hfg : MemLp ((f : Ω → ℝ) * (g : Ω → ℝ)) ∞ μ,
      boundedToL2 ((f : Ω → ℝ) * (g : Ω → ℝ)) hfg ∈ δ.adjoint.domain := by
  have hle := adjoin_le_boundedMultiplierAlgebra δ s hs
  exact multiplierAlgebra_product_mem_adjoint_domain δ hδ hcenter
    ⟨f, hle f.property⟩ ⟨g, hle g.property⟩
end Adjoint
end OperatorDerivativeRewrite.Foundation
