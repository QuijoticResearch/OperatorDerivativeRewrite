import Foundation.FiniteGammaL2Algebra
import Mathlib.LinearAlgebra.Isomorphisms

/-! Concrete realization of the manuscript tensor form, with its probability normalization. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteGammaTensor
open FiniteGammaSeed
open scoped TensorProduct
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def singleForm (f u : Algebra) : Form :=
  WithLp.toLp 2 (fun p => u p.1 * beta f p.2)

theorem singleForm_apply (f u : Algebra) (p : State × Fin 2) :
    singleForm f u p = u p.1 * beta f p.2 := rfl

def bilinear : Algebra →ₗ[ℝ] Algebra →ₗ[ℝ] Form where
  toFun f :=
    { toFun := singleForm f
      map_add' := by
        intro u v
        apply PiLp.ext
        intro p
        simp only [singleForm_apply, PiLp.add_apply, Pi.add_apply]
        ring
      map_smul' := by
        intro r u
        apply PiLp.ext
        intro p
        simp only [singleForm_apply, PiLp.smul_apply, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        ring }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro u
    apply PiLp.ext
    intro p
    change u p.1 * beta (f + g) p.2 = u p.1 * beta f p.2 + u p.1 * beta g p.2
    rw [map_add, Pi.add_apply]
    ring
  map_smul' := by
    intro r f
    apply LinearMap.ext
    intro u
    apply PiLp.ext
    intro p
    change u p.1 * beta (r • f) p.2 = r * (u p.1 * beta f p.2)
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    ring

abbrev Tensor := FiniteGammaSeed.Algebra ⊗[ℝ] FiniteGammaSeed.Algebra

def tensorMap : Tensor →ₗ[ℝ] Form := TensorProduct.lift bilinear

theorem tensorMap_tmul (f u : Algebra) :
    tensorMap (f ⊗ₜ[ℝ] u) = singleForm f u := TensorProduct.lift.tmul _ _

def potential (i : Fin 2) : Algebra :=
  fun s => if s = (if i = 0 then State.x else State.y) then 1 else 0

theorem beta_potential (i j : Fin 2) : beta (potential i) j = if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [beta, potential]

def basisTensor (p : State × Fin 2) : Tensor :=
  potential p.2 ⊗ₜ[ℝ] (Pi.single p.1 1 : FiniteGammaSeed.Algebra)

theorem tensorMap_basis (p : State × Fin 2) :
    tensorMap (basisTensor p) = EuclideanSpace.single p (1 : ℝ) := by
  apply PiLp.ext
  intro q
  rw [basisTensor, tensorMap_tmul, singleForm_apply, beta_potential]
  simp only [PiLp.single_apply]
  by_cases hs : q.1 = p.1 <;> by_cases hi : q.2 = p.2 <;>
    simp [hs, hi, Prod.ext_iff]

def synthesis (v : Form) : Tensor := ∑ p, v p • basisTensor p

theorem tensorMap_synthesis (v : Form) : tensorMap (synthesis v) = v := by
  simp only [synthesis, map_sum, map_smul, tensorMap_basis]
  apply PiLp.ext
  intro q
  change (∑ p, v p • EuclideanSpace.single p (1 : ℝ)) q = v q
  change WithLp.ofLp (∑ p, v p • EuclideanSpace.single p (1 : ℝ)) q = v q
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    PiLp.ofLp_single, Pi.single_apply]
  simp

theorem tensorMap_surjective : Function.Surjective tensorMap :=
  fun v => ⟨synthesis v, tensorMap_synthesis v⟩

/-- The exact probability-weighted tensor pairing on pure tensors. -/
theorem pure_pairing (f u g v : Algebra) :
    (1/3 : ℝ) * inner ℝ (singleForm f u) (singleForm g v) =
      expect (fun s => u s * v s * gamma f g s) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  unfold expect gamma dotProduct
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  change (∑ i, inner ℝ (singleForm f u (s, i)) (singleForm g v (s, i))) =
    u s * v s * ∑ i, beta f i * beta g i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [singleForm_apply, RCLike.inner_apply, conj_trivial]
  ring

def quotientEquiv : (Tensor ⧸ LinearMap.ker tensorMap) ≃ₗ[ℝ] Form :=
  tensorMap.quotKerEquivOfSurjective tensorMap_surjective

end OperatorDerivativeRewrite.Foundation.FiniteGammaTensor
