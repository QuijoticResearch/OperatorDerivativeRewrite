import Foundation.HigherHeatFiniteHorizon

/-! Exact coordinate marginals of the constructed finite signed heat laws. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMarginals
open HigherHeatSignedLaws

def dropCoordinate {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) (j : Fin n) : ℝ :=
  x (i.succAbove j)

theorem dropCoordinate_measurable {n : ℕ} (i : Fin (n+1)) : Measurable (dropCoordinate i) := by
  apply Measurable.of_eval
  intro j
  exact measurable_pi_apply _

theorem dropCoordinate_law {n : ℕ} (m : ℕ) (hm : 0 < m)
    (t : Fin (n+1) → ℝ≥0) (ht : ∀ j, 0 < t j) (i : Fin (n+1)) :
    (incrementLaw m hm t ht).map (dropCoordinate i) =
      incrementLaw m hm (fun j : Fin n => t (i.succAbove j)) (fun j => ht _) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) i).symm
  have hd (z : ℝ × (Fin n → ℝ)) : dropCoordinate i (e.symm z) = z.2 := by
    funext j
    simp [dropCoordinate,e,MeasurableEquiv.piFinSuccAbove_symm_apply]
  have hprod (z : ℝ × (Fin n → ℝ)) :
      incrementDensity m hm t ht (e.symm z) = realKernel m hm (t i) (ht i) z.1 *
        incrementDensity m hm (fun j : Fin n => t (i.succAbove j)) (fun j => ht _) z.2 := by
    unfold incrementDensity
    rw [Fin.prod_univ_succAbove _ i]
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply]
  ext s hs
  rw [VectorMeasure.map_apply _ (dropCoordinate_measurable i) hs]
  rw [incrementLaw,withDensityᵥ_apply (incrementDensity_integrable m hm t ht)
    ((dropCoordinate_measurable i) hs)]
  rw [← he.setIntegral_preimage_emb e.symm.measurableEmbedding
    (incrementDensity m hm t ht) (dropCoordinate i ⁻¹' s)]
  have hset : e.symm ⁻¹' (dropCoordinate i ⁻¹' s) = Set.univ ×ˢ s := by
    ext z
    simp only [Set.mem_preimage,hd,Set.mem_prod,Set.mem_univ,true_and]
  rw [hset]
  change (∫ z in Set.univ ×ˢ s, incrementDensity m hm t ht (e.symm z)
    ∂((volume : Measure ℝ).prod (Measure.pi (fun _ : Fin n => volume)))) = _
  simp_rw [hprod]
  rw [setIntegral_prod_mul,Measure.restrict_univ,realKernel_integral,one_mul]
  exact (withDensityᵥ_apply
    (incrementDensity_integrable m hm (fun j : Fin n => t (i.succAbove j)) (fun j => ht _)) hs).symm

end OperatorDerivativeRewrite.Foundation.HigherHeatMarginals
