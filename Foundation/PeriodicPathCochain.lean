import Foundation.PeriodicCoarseCurl

/-! Coarse-edge path integration is a cochain map, distinct from face averaging. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicPathCochain
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def corner (q : CoarseVertex) : Vertex := fineVertex q 0

theorem corner_double_shift : ∀ (q : CoarseVertex) (i : Direction),
    shift (shift (corner q) i) i = corner (coarseShift q i) := by decide

theorem corner_edge_data : ∀ (q : CoarseVertex) (i : Direction),
    ¬ oddEdge (corner q, i) ∧ oddEdge (shift (corner q) i, i) ∧
      coarseBlock (shift (corner q) i) = q := by decide

def pathMap : (Edge → ℝ) →ₗ[ℝ] (CoarseEdge → ℝ) :=
  LinearMap.pi (fun e => (LinearMap.proj (corner e.1, e.2) : (Edge → ℝ) →ₗ[ℝ] ℝ) +
    LinearMap.proj (shift (corner e.1) e.2, e.2))

theorem pathMap_apply (f : Edge → ℝ) (e : CoarseEdge) :
    pathMap f e = f (corner e.1, e.2) + f (shift (corner e.1) e.2, e.2) := rfl

def samplePotential : (Vertex → ℝ) →ₗ[ℝ] (CoarseVertex → ℝ) :=
  LinearMap.pi (fun q => LinearMap.proj (corner q))

theorem pathMap_gradient (φ : Vertex → ℝ) :
    pathMap (gradientMap φ) = coarseGradient (samplePotential φ) := by
  funext e
  change (φ (shift (corner e.1) e.2) - φ (corner e.1)) +
    (φ (shift (shift (corner e.1) e.2) e.2) - φ (shift (corner e.1) e.2)) =
      φ (corner (coarseShift e.1 e.2)) - φ (corner e.1)
  rw [corner_double_shift]
  ring

theorem pathMap_comp_gradient :
    pathMap.comp gradientMap = coarseGradient.comp samplePotential := by
  apply LinearMap.ext
  exact pathMap_gradient

def refinedCurl (f : Edge → ℝ) (q : CoarseVertex) (i j : Direction) : ℝ :=
  curl f (corner q) i j + curl f (shift (corner q) i) i j +
    curl f (shift (corner q) j) i j + curl f (shift (shift (corner q) i) j) i j

theorem plaquette_Stokes (f : Edge → ℝ) (q : CoarseVertex) (i j : Direction) :
    coarseCurl (pathMap f) q i j = refinedCurl f q i j := by
  simp only [coarseCurl, pathMap_apply, refinedCurl, curl, ← corner_double_shift]
  simp only [shift_commute]
  ring

theorem pathMap_flatLift (c : CoarseEdge → ℝ) : pathMap (flatLift c) = c := by
  funext e
  rw [pathMap_apply, flatLift_apply, flatLift_apply]
  obtain ⟨he, ho, hb⟩ := corner_edge_data e.1 e.2
  simp [he, ho, hb]

theorem pathMap_normalizedLift (c : CoarseEdge → ℝ) :
    pathMap (normalizedLift c) = (1/8 : ℝ) • c := by
  rw [normalizedLift, LinearMap.smul_apply, map_smul, pathMap_flatLift]

theorem flatLift_Stokes (c : CoarseEdge → ℝ) (q : CoarseVertex) (i j : Direction) :
    refinedCurl (flatLift c) q i j = coarseCurl c q i j := by
  rw [← plaquette_Stokes, pathMap_flatLift]

theorem normalizedLift_Stokes (c : CoarseEdge → ℝ) (q : CoarseVertex) (i j : Direction) :
    refinedCurl (normalizedLift c) q i j = (1/8 : ℝ) * coarseCurl c q i j := by
  rw [← plaquette_Stokes, pathMap_normalizedLift]
  simp only [coarseCurl, Pi.smul_apply, smul_eq_mul]
  ring

end OperatorDerivativeRewrite.Foundation.PeriodicPathCochain
