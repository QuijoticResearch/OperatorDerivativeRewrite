import Foundation.GaussianSampleReflection
import Foundation.InfiniteGaussianOperators

/-! Reflection covariance of the ORIGINAL closed Gaussian derivative graph. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianDerivativeReflection
open InfiniteGaussian GaussianSampleReflection
set_option backward.isDefEq.respectTransparency false

def vectorReflection : GaussianVectorL2 →ₗᵢ[ℝ] GaussianVectorL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ reflect reflect_preserving

theorem vectorReflection_ae (g : GaussianVectorL2) :
    vectorReflection g =ᵐ[gaussianProduct] fun ω => g (reflect ω) :=
  Lp.coeFn_compMeasurePreserving g reflect_preserving

theorem cylinder_reflect_ae {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    (fun ω => isonormalCylinder h p (reflect ω)) =ᵐ[gaussianProduct]
      isonormalCylinder (fun i => -h i) p := by
  have hn (i : ι) : firstChaosEmbedding (-h i) =ᵐ[gaussianProduct]
      fun ω => -firstChaosEmbedding (h i) ω := by
    rw [map_neg]
    filter_upwards [Lp.coeFn_neg (firstChaosEmbedding (h i))] with ω hω
    exact hω
  filter_upwards [ae_all_iff.mpr (fun i => firstChaos_reflect_ae (h i)),ae_all_iff.mpr hn]
    with ω hr hn
  apply congrArg (fun x : ι → ℝ => MvPolynomial.eval x p)
  funext i
  exact (hr i).trans (hn i).symm

theorem cylinder_reflection {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    reflection (isonormalCylinderL2 h p) = isonormalCylinderL2 (fun i => -h i) p := by
  apply Lp.ext
  have ht := reflect_preserving.quasiMeasurePreserving.ae_eq_comp (isonormalCylinderL2_coeFn h p)
  exact (reflection_ae _).trans (ht.trans ((cylinder_reflect_ae h p).trans
    (isonormalCylinderL2_coeFn (fun i => -h i) p).symm))

theorem gradient_reflect_ae {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    isonormalCylinderGradient (fun i => -h i) p =ᵐ[gaussianProduct]
      fun ω => -isonormalCylinderGradient h p (reflect ω) := by
  filter_upwards [ae_all_iff.mpr (fun i => cylinder_reflect_ae h (MvPolynomial.pderiv i p))]
    with ω hr
  simp only [isonormalCylinderGradient,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hr i,smul_neg]

theorem gradient_reflection {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    isonormalCylinderGradientL2 (fun i => -h i) p =
      -vectorReflection (isonormalCylinderGradientL2 h p) := by
  apply Lp.ext
  have ht := reflect_preserving.quasiMeasurePreserving.ae_eq_comp
    (isonormalCylinderGradientL2_coeFn h p)
  filter_upwards [isonormalCylinderGradientL2_coeFn (fun i => -h i) p,
    gradient_reflect_ae h p,vectorReflection_ae (isonormalCylinderGradientL2 h p),ht,
    Lp.coeFn_neg (vectorReflection (isonormalCylinderGradientL2 h p))]
    with ω hg hr hv ht hn
  change isonormalCylinderGradientL2 h p (reflect ω) =
    isonormalCylinderGradient h p (reflect ω) at ht
  rw [hg,hr,hn,Pi.neg_apply,hv,ht]

theorem cylinder_graph {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    (isonormalCylinderL2 h p,isonormalCylinderGradientL2 h p) ∈ cylindricalDerivative.graph := by
  exact cylindricalDerivative.mem_graph_iff.mpr
    ⟨⟨_,isonormalCylinderL2_mem_core h p⟩,rfl,polynomialDerivative_on_cylinder h p⟩

theorem polynomial_graph (f : polynomialCylindricalDomain) :
    (reflection (f : GaussianL2),-vectorReflection (polynomialDerivative f))
      ∈ cylindricalDerivative.graph := by
  let r := polynomialRepresentation f
  have hg := cylinder_graph (fun i => -r.directions i) r.polynomial
  rw [← cylinder_reflection,gradient_reflection] at hg
  have hd : polynomialDerivative f = isonormalCylinderGradientL2 r.directions r.polynomial :=
    polynomialGradient_agrees f r.directions r.polynomial r.represents
  rw [r.represents,← hd] at hg
  exact hg

theorem closed_graph {f : GaussianL2} {g : GaussianVectorL2}
    (h : (f,g) ∈ closedCylindricalDerivative.graph) :
    (reflection f,-vectorReflection g) ∈ closedCylindricalDerivative.graph := by
  let S : Set (GaussianL2 × GaussianVectorL2) :=
    (fun z => (reflection z.1,-vectorReflection z.2)) ⁻¹'
      (closedCylindricalDerivative.graph : Set (GaussianL2 × GaussianVectorL2))
  have hS : IsClosed S := closedCylindricalDerivative_isClosed.preimage
    ((reflection.continuous.comp continuous_fst).prodMk
      ((vectorReflection.continuous.comp continuous_snd).neg))
  have hs : (cylindricalDerivative.graph : Set (GaussianL2 × GaussianVectorL2)) ⊆ S := by
    intro z hz
    obtain ⟨u,hu,hv⟩ := cylindricalDerivative.mem_graph_iff.mp hz
    change polynomialDerivative u = z.2 at hv
    have hh := polynomial_graph u
    rw [hu,hv] at hh
    exact LinearPMap.le_graph_of_le cylindricalDerivative.le_closure
      hh
  have hc := closure_minimal hs hS
  change (f,g) ∈ S
  apply hc
  rw [closedCylindricalDerivative_graph] at h
  exact h

end OperatorDerivativeRewrite.Foundation.GaussianDerivativeReflection
