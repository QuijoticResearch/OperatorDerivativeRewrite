import Foundation.HigherHeatSpatialGenerator
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A genuine closed densely defined heat generator with its weighted domain. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatClosedGenerator
set_option backward.isDefEq.respectTransparency false
open HigherHeatL2 HigherHeatGenerator

def frequencyGraph (m : ℕ) : Submodule ℂ (H × H) where
  carrier := {z | target m z.1 =ᵐ[volume] z.2}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    change target m (0 : H) x = (0 : H) x
    simp only [target,hx,Pi.zero_apply,mul_zero]
  add_mem' := by
    intro z w hz hw
    filter_upwards [hz,hw,Lp.coeFn_add z.1 w.1,Lp.coeFn_add z.2 w.2] with x hz hw h1 h2
    change target m (z.1+w.1) x = (z.2+w.2) x
    change ((-weight m x : ℝ) : ℂ)*z.1 x=z.2 x at hz
    change ((-weight m x : ℝ) : ℂ)*w.1 x=w.2 x at hw
    simp only [target,h1,h2,Pi.add_apply,mul_add,hz,hw]
  smul_mem' := by
    intro c z hz
    filter_upwards [hz,Lp.coeFn_smul c z.1,Lp.coeFn_smul c z.2] with x hz h1 h2
    change target m (c • z.1) x = (c • z.2) x
    change ((-weight m x : ℝ) : ℂ)*z.1 x=z.2 x at hz
    simp only [target,h1,h2,Pi.smul_apply,smul_eq_mul]
    calc
      ((-weight m x : ℝ) : ℂ)*(c*z.1 x) = c*(((-weight m x : ℝ) : ℂ)*z.1 x) := by ring
      _ = c*z.2 x := by rw [hz]

theorem frequency_vertical_zero (m : ℕ) (z : H × H) (hz : z ∈ frequencyGraph m)
    (h0 : z.1=0) : z.2=0 := by
  apply Lp.ext
  filter_upwards [hz,Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx he
  change target m z.1 x=z.2 x at hx
  rw [h0] at hx
  simpa only [target,he,Pi.zero_apply,mul_zero] using hx.symm

theorem frequencyGraph_closed (m : ℕ) : IsClosed (frequencyGraph m : Set (H × H)) := by
  apply IsSeqClosed.isClosed
  intro z w hz hw
  obtain ⟨ns,hns,hn⟩ := (tendstoInMeasure_of_tendsto_Lp hw.fst_nhds).exists_seq_tendsto_ae
  obtain ⟨ms,hms,hm⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hw.snd_nhds.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂volume, ∀ n, target m (z n).1 x=(z n).2 x := ae_all_iff.mpr hz
  filter_upwards [hn,hm,hall] with x hn hm hall
  have hl := (hn.comp hms.tendsto_atTop).const_mul (((-weight m x : ℝ) : ℂ))
  have he (k : ℕ) : (((-weight m x : ℝ) : ℂ))*(z (ns (ms k))).1 x=(z (ns (ms k))).2 x := hall _
  have hl' : Tendsto (fun k => (z (ns (ms k))).2 x) atTop
      (𝓝 ((((-weight m x : ℝ) : ℂ)) * w.1 x)) := by simpa only [Function.comp_def,he] using hl
  exact tendsto_nhds_unique hl' hm

def fourierPair : (H × H) →L[ℂ] (H × H) :=
  ((fourierCLM ℂ H).comp (ContinuousLinearMap.fst ℂ H H)).prod
    ((fourierCLM ℂ H).comp (ContinuousLinearMap.snd ℂ H H))

def graph (m : ℕ) : Submodule ℂ (H × H) :=
  (frequencyGraph m).comap fourierPair.toLinearMap

theorem graph_iff (m : ℕ) (f g : H) : (f,g) ∈ graph m ↔
    target m (𝓕 f) =ᵐ[volume] (𝓕 g : H) := Iff.rfl

theorem vertical_zero (m : ℕ) (z : H × H) (hz : z ∈ graph m) (h0 : z.1=0) : z.2=0 := by
  have h := frequency_vertical_zero m (fourierPair z) hz (by
    change 𝓕 z.1=(0 : H)
    simp only [h0,FourierTransform.fourier_zero])
  change 𝓕 z.2=(0 : H) at h
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 z.2=𝓕 (0 : H)
  simpa only [FourierTransform.fourier_zero] using h

def operator (m : ℕ) : H →ₗ.[ℂ] H := (graph m).toLinearPMap

theorem operator_graph (m : ℕ) : (operator m).graph=graph m :=
  (graph m).toLinearPMap_graph_eq (vertical_zero m)

theorem graph_closed (m : ℕ) : IsClosed (graph m : Set (H × H)) :=
  (frequencyGraph_closed m).preimage fourierPair.continuous

theorem operator_closed (m : ℕ) : (operator m).IsClosed := by
  change IsClosed ((operator m).graph : Set (H × H))
  rw [operator_graph]
  exact graph_closed m

theorem domain_iff (m : ℕ) (f : H) : f ∈ (operator m).domain ↔
    MemLp (target m (𝓕 f)) 2 volume := by
  rw [LinearPMap.mem_domain_iff,operator_graph]
  constructor
  · rintro ⟨g,hg⟩
    exact (memLp_congr_ae ((graph_iff m f g).mp hg)).mpr (Lp.memLp (𝓕 g : H))
  · intro hf
    refine ⟨generator m f hf,?_⟩
    rw [graph_iff,generator,fourier_fourierInv_eq]
    exact hf.coeFn_toLp.symm

theorem domain_dense (m : ℕ) : Dense ((operator m).domain : Set H) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top
  apply hd.mono
  rintro f ⟨u,rfl⟩
  apply (domain_iff m _).mpr
  exact HigherHeatSpatialGenerator.in_domain m u

theorem generator_mem_graph (m : ℕ) (f : H) (hf : MemLp (target m (𝓕 f)) 2 volume) :
    (f,generator m f hf) ∈ (operator m).graph := by
  rw [operator_graph,graph_iff,generator,fourier_fourierInv_eq]
  exact hf.coeFn_toLp.symm

theorem graph_hasDerivWithinAt (m : ℕ) (f g : H) (hg : (f,g) ∈ (operator m).graph) :
    HasDerivWithinAt (fun t : ℝ => evolution m t.toNNReal f) g (Set.Ici 0) 0 := by
  have hmem : f ∈ (operator m).domain := LinearPMap.mem_domain_iff.mpr ⟨g,hg⟩
  have hf := (domain_iff m f).mp hmem
  have he : generator m f hf=g := by
    exact (operator m).mem_graph_snd_inj (generator_mem_graph m f hf) hg rfl
  rw [← he]
  exact HigherHeatGenerator.evolution_hasDerivWithinAt m f hf

end OperatorDerivativeRewrite.Foundation.HigherHeatClosedGenerator
