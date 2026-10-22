import Foundation.GaussianWeakVectorPrimitive

/-! The actual folded scenery section cannot have a common finite-energy
vector derivative whose scalar tests lie in the ORIGINAL 1D Gaussian graph.
Transport from the infinite-dimensional native clock graph remains separate. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockWeakGraphObstruction
open IBMClockSectionEnergyObstruction GaussianWeakVectorPrimitive
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem section_memLp (c : ℝ) :
    MemLp (fun x : ℝ => folded (c * x)) 2 GaussianCore.γ := by
  have hm : Continuous (fun x : ℝ => folded (c * x)) :=
    IBMContinuousScenery.sourceScenery_continuous.comp
      ((continuous_const.mul continuous_id).abs)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  have hi : Integrable (fun x : ℝ => x) GaussianCore.γ := by
    simpa only [Polynomial.eval_X] using
      (GaussianCore.polynomial_memLp (Polynomial.X : Polynomial ℝ) 1 (by norm_num)).integrable
        (by norm_num)
  have he (x : ℝ) : ‖folded (c * x)‖ ^ 2 = |c * x| := by
    simpa only [folded, abs_abs] using IBMRandomTimeHilbert.sourceScenery_norm_sq |c * x|
  simpa only [he] using (hi.const_mul c).abs

def sectionClass (c : ℝ) : Lp InfiniteGaussian.GaussianL2 2 GaussianCore.γ :=
  (section_memLp c).toLp _

theorem sectionClass_ae (c : ℝ) :
    sectionClass c =ᵐ[GaussianCore.γ] fun x => folded (c * x) :=
  (section_memLp c).coeFn_toLp

/-- There is no SINGLE square-integrable scenery-valued derivative realizing
all actual scalar closed Gaussian graphs of this section at positive scale. -/
theorem no_common_closed_derivative (c : ℝ) (hc : 0 < c) :
    ¬ ∃ g : Lp InfiniteGaussian.GaussianL2 2 GaussianCore.γ,
      ∀ e : InfiniteGaussian.GaussianL2,
        ((innerSL ℝ e).compLp (sectionClass c), (innerSL ℝ e).compLp g) ∈
          GaussianCore.closedDerivative.graph := by
  rintro ⟨g, hg⟩
  obtain ⟨v, hv⟩ := weak_graph_primitive (sectionClass c) g hg
    (a := 0) (b := 1) (by norm_num)
  have hvol : (volume : Measure ℝ) ≪ GaussianCore.γ :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
  have hr : sectionClass c =ᵐ[volume.restrict (Icc 0 1)] fun x => folded (c * x) :=
    ae_restrict_of_ae (hvol.ae_eq (sectionClass_ae c))
  have he := hr.symm.trans hv
  exact scaled_folded_no_ae_primitive (by norm_num) (by norm_num) hc (Lp.memLp g) v he

end OperatorDerivativeRewrite.Foundation.IBMClockWeakGraphObstruction
