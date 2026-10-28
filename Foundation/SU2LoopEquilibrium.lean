import Foundation.SU2InteractingLoopKernel
import Mathlib.Probability.Kernel.Composition.WithDensity

noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.MeasurableExponentialKernel
open OperatorDerivativeRewrite.Foundation.BoundedExponentialTiltResponse
open OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse
open OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel

namespace OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium

def globalPartition (r : ℝ) : ℝ :=
  BoundedExponentialTiltResponse.partition μ X r

def equilibriumDensity (r : ℝ) (C : SU2) : ℝ :=
  MeasurableExponentialKernel.partition law (interaction r) C / globalPartition r

def equilibriumLaw (r : ℝ) : Measure SU2 :=
  law.withDensity (fun C => ENNReal.ofReal (equilibriumDensity r C))

theorem globalPartition_pos (r : ℝ) : 0 < globalPartition r := by
  apply BoundedExponentialTiltResponse.partition_pos μ X
  · exact (halfTrace_measurable.comp measurable_fst).mul
      (halfTrace_measurable.comp measurable_snd)
  · intro p
    simpa [X, F, G] using
      (show |halfTrace p.1 * halfTrace p.2| ≤ 1 by
        rw [abs_mul]
        calc
          |halfTrace p.1| * |halfTrace p.2| ≤ 1 * 1 :=
            mul_le_mul (halfTrace_bound _) (halfTrace_bound _) (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num)

theorem equilibriumDensity_measurable (r : ℝ) :
    Measurable (equilibriumDensity r) := by
  exact (MeasurableExponentialKernel.partition_measurable law (interaction r)
    (interaction_measurable r)).div_const _

theorem detailed_balance_density (r : ℝ) (C D : SU2) :
    equilibriumDensity r C *
      MeasurableExponentialKernel.density law (interaction r) C D =
    equilibriumDensity r D *
      MeasurableExponentialKernel.density law (interaction r) D C := by
  have hc := MeasurableExponentialKernel.partition_positive law (interaction r) C
    (interaction_exp_integrable r C)
  have hd := MeasurableExponentialKernel.partition_positive law (interaction r) D
    (interaction_exp_integrable r D)
  unfold equilibriumDensity MeasurableExponentialKernel.density
  have he : interaction r C D = interaction r D C := by unfold interaction; ring
  rw [he]
  field_simp

theorem equilibrium_edge (r : ℝ) :
    equilibriumLaw r ⊗ₘ loopKernel r = coupledLaw r := by
  haveI : IsMarkovKernel ((Kernel.const SU2 law).withDensity
      (fun C D => ENNReal.ofReal (MeasurableExponentialKernel.density law (interaction r) C D))) := by
    change IsMarkovKernel (loopKernel r)
    exact loopKernel_markov r
  have hf : Measurable (fun C : SU2 => ENNReal.ofReal (equilibriumDensity r C)) :=
    (equilibriumDensity_measurable r).ennreal_ofReal
  have hg : Measurable (Function.uncurry (fun C D : SU2 =>
      ENNReal.ofReal (MeasurableExponentialKernel.density law (interaction r) C D))) :=
    (MeasurableExponentialKernel.density_measurable law (interaction r)
      (interaction_measurable r)).ennreal_ofReal
  change (law.withDensity _) ⊗ₘ
      ((Kernel.const SU2 law).withDensity _) = coupledLaw r
  rw [Measure.withDensity_compProd_withDensity hf hg, Measure.compProd_const]
  unfold coupledLaw BoundedExponentialTiltResponse.tiltedMeasure
  congr 1
  funext p
  have hZ : 0 < globalPartition r := globalPartition_pos r
  have hC := MeasurableExponentialKernel.partition_positive law (interaction r) p.1
    (interaction_exp_integrable r p.1)
  have hEq : 0 ≤ equilibriumDensity r p.1 := by
    exact div_nonneg hC.le hZ.le
  rw [← ENNReal.ofReal_mul hEq]
  congr 1
  unfold equilibriumDensity MeasurableExponentialKernel.density
  unfold BoundedExponentialTiltResponse.density globalPartition X F G interaction
  field_simp [hC.ne', hZ.ne']
  change 0 < MeasurableExponentialKernel.partition law
    (fun C D => r * halfTrace C * halfTrace D) p.1 at hC
  rw [div_mul_eq_div_div, div_self hC.ne']

theorem equilibriumLaw_eq_fst (r : ℝ) :
    equilibriumLaw r = (coupledLaw r).fst := by
  haveI : SFinite (equilibriumLaw r) := by
    unfold equilibriumLaw
    infer_instance
  haveI : IsMarkovKernel (loopKernel r) := loopKernel_markov r
  rw [← equilibrium_edge]
  exact (Measure.fst_compProd (equilibriumLaw r) (loopKernel r)).symm

theorem equilibriumLaw_probability (r : ℝ) :
    IsProbabilityMeasure (equilibriumLaw r) := by
  rw [equilibriumLaw_eq_fst]
  letI : IsProbabilityMeasure (coupledLaw r) := coupledLaw_probability r
  infer_instance

theorem coupledLaw_exchangeable (r : ℝ) :
    (coupledLaw r).map Prod.swap = coupledLaw r := by
  have hd : Measurable (fun p : SU2 × SU2 => ENNReal.ofReal
      (BoundedExponentialTiltResponse.density μ X r p)) :=
    ((measurable_const.mul
      ((halfTrace_measurable.comp measurable_fst).mul
        (halfTrace_measurable.comp measurable_snd))).exp.div_const _).ennreal_ofReal
  have hs : μ.map Prod.swap = μ := by
    unfold μ
    exact Measure.prod_swap
  apply Measure.ext
  intro s hset
  rw [Measure.map_apply measurable_swap hset, coupledLaw,
    BoundedExponentialTiltResponse.tiltedMeasure,
    withDensity_apply _ (measurable_swap hset), withDensity_apply _ hset]
  have he := setLIntegral_map (μ := μ) hset hd measurable_swap
  rw [hs] at he
  have hh : (fun p : SU2 × SU2 => ENNReal.ofReal
      (BoundedExponentialTiltResponse.density μ X r p)) =
      (fun p => ENNReal.ofReal
        (BoundedExponentialTiltResponse.density μ X r p.swap)) := by
    funext p
    simp [BoundedExponentialTiltResponse.density, X, F, G, mul_comm]
  conv_lhs => rw [hh]
  exact he.symm

theorem equilibriumLaw_stationary (r : ℝ) :
    loopKernel r ∘ₘ equilibriumLaw r = equilibriumLaw r := by
  haveI : SFinite (equilibriumLaw r) := by
    unfold equilibriumLaw
    infer_instance
  haveI : IsMarkovKernel (loopKernel r) := loopKernel_markov r
  rw [← Measure.snd_compProd]
  rw [equilibrium_edge]
  rw [← Measure.fst_map_swap, coupledLaw_exchangeable]
  exact (equilibriumLaw_eq_fst r).symm

end OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium
