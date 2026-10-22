import Foundation.IBMNativeProductOperators

/-! Actual square-integrable contractions for bounded native IBM gradient fields. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeContraction
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicChainRule IBMNativeFieldMultiplier
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def contract (v : JointVectorL2)
    (hv : MemLp (v : IBMSourceLaws.JointSample → CoefficientSpace)
      ∞ IBMSourceLaws.jointMeasure) (u : JointVectorL2) : JointL2 :=
  lpInner (r := 2) (hv.toLp v) u

theorem contract_ae (v : JointVectorL2)
    (hv : MemLp (v : IBMSourceLaws.JointSample → CoefficientSpace)
      ∞ IBMSourceLaws.jointMeasure) (u : JointVectorL2) :
    contract v hv u =ᵐ[IBMSourceLaws.jointMeasure] fun ω => inner ℝ (v ω) (u ω) := by
  filter_upwards [lpInner_coeFn (r := 2) (hv.toLp v) u,hv.coeFn_toLp] with ω hc hv
  exact hc.trans (congrArg (fun z : CoefficientSpace => inner ℝ z (u ω)) hv)

theorem contract_norm (v : JointVectorL2)
    (hv : MemLp (v : IBMSourceLaws.JointSample → CoefficientSpace)
      ∞ IBMSourceLaws.jointMeasure) (u : JointVectorL2) :
    ‖contract v hv u‖ ≤ ‖hv.toLp v‖ * ‖u‖ := lpInner_norm_le _ _

theorem contract_pairing (v : JointVectorL2)
    (hv : MemLp (v : IBMSourceLaws.JointSample → CoefficientSpace)
      ∞ IBMSourceLaws.jointMeasure) (u : JointVectorL2) (g : JointL2)
    (hg : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    inner ℝ (contract v hv u) g = inner ℝ (boundedMultiplier g hg u) v := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [contract_ae v hv u,boundedMultiplier_coeFn g hg u] with ω hc hm
  rw [hc,hm,Real.inner_apply,real_inner_smul_left,real_inner_comm (u ω) (v ω)]
  ring

def correction (V : JointFieldSpace)
    (hV : ∀ i : Fin 2, MemLp (coordinate i (V i) : IBMSourceLaws.JointSample → CoefficientSpace)
      ∞ IBMSourceLaws.jointMeasure) (u : JointFieldSpace) : JointL2 :=
  contract (coordinate 0 (V 0)) (hV 0) (coordinate 0 (u 0)) +
  contract (coordinate 1 (V 1)) (hV 1) (coordinate 1 (u 1))

theorem correction_ae (V : JointFieldSpace)
    (hV : ∀ i : Fin 2, MemLp (coordinate i (V i) : IBMSourceLaws.JointSample → CoefficientSpace)
      ∞ IBMSourceLaws.jointMeasure) (u : JointFieldSpace) :
    correction V hV u =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      inner ℝ (coordinate 0 (V 0) ω) (coordinate 0 (u 0) ω) +
      inner ℝ (coordinate 1 (V 1) ω) (coordinate 1 (u 1) ω) :=
  (Lp.coeFn_add _ _).trans ((contract_ae _ (hV 0) _).add (contract_ae _ (hV 1) _))

theorem channel_pairing (v u : FieldSpace) (i : Fin 2)
    (hv : MemLp (coordinate i v : IBMSourceLaws.JointSample → CoefficientSpace)
      ∞ IBMSourceLaws.jointMeasure) (g : JointL2)
    (hg : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    inner ℝ (contract (coordinate i v) hv (coordinate i u)) g =
      inner ℝ (channelMultiplier i g hg u) v := by
  calc
    _ = inner ℝ (boundedMultiplier g hg (coordinate i u)) (coordinate i v) :=
      contract_pairing _ hv _ g hg
    _ = inner ℝ (coordinate i (channelMultiplier i g hg u)) (coordinate i v) :=
      congrArg (fun z : JointVectorL2 => inner ℝ z (coordinate i v))
        (channel_coordinate i g hg u).symm
    _ = _ := (coordinate i).inner_map_map _ _

theorem correction_pairing (V : JointFieldSpace)
    (hV : ∀ i : Fin 2, MemLp (coordinate i (V i) : IBMSourceLaws.JointSample → CoefficientSpace)
      ∞ IBMSourceLaws.jointMeasure) (u : JointFieldSpace) (g : JointL2)
    (hg : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    inner ℝ (correction V hV u) g = inner ℝ (multiply g hg u) V := by
  calc
    _ = inner ℝ (contract (coordinate 0 (V 0)) (hV 0) (coordinate 0 (u 0))) g +
        inner ℝ (contract (coordinate 1 (V 1)) (hV 1) (coordinate 1 (u 1))) g :=
      inner_add_left _ _ _
    _ = inner ℝ (channelMultiplier 0 g hg (u 0)) (V 0) +
        inner ℝ (channelMultiplier 1 g hg (u 1)) (V 1) :=
      congrArg₂ (fun a b : ℝ => a+b) (channel_pairing _ _ 0 (hV 0) g hg)
        (channel_pairing _ _ 1 (hV 1) g hg)
    _ = _ := by simp only [PiLp.inner_apply,Fin.sum_univ_two,multiply_channel]

end OperatorDerivativeRewrite.Foundation.IBMNativeContraction
