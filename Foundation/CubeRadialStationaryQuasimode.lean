import Foundation.CubeFiniteGroundQuasimode

/-! Concrete mean-zero unit quasimodes of the actual stationary Wilson transfer. -/
noncomputable section
open MeasureTheory Filter Topology
namespace OperatorDerivativeRewrite.Foundation.CubeRadialStationaryQuasimode
open CubeGaussianRadialEigenvector CubeGaussianChannelGround CubeFiniteGroundQuasimode
open CubeSlabGround CubeChordOperator CubeGroundUnitary CubeHaarOperator CubeSlabL2
open CubeBoundaryChartL2

def chord (j : Fin 5) (t : ℝ) : ChordL2 := unit t (radialClass j)

theorem chord_orthogonal (j : Fin 5) (t : ℝ) :
    inner ℝ (chord j t) (chordGround (ground (1/t^2))) = 0 := unit_orthogonal _ _

theorem chord_norm (j : Fin 5) : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ‖chord j t‖ = 1 :=
  eventually_unit_norm _ (radial_ratio_bounds j).1 (radial_ratio_bounds j).2
    (radialClass j) (radialClass_nonzero j) (normalized_radial_eigenvector j)

theorem chord_error (j : Fin 5) :
    Tendsto (fun t : ℝ => ‖chordOperator (ground (1/t^2)) (chord j t)-
      (ratio j)^2 • chord j t‖) (𝓝[>] (0:ℝ)) (𝓝 0) :=
  unit_error_tendsto _ (radial_ratio_bounds j).1 (radial_ratio_bounds j).2
    (radialClass j) (radialClass_nonzero j) (normalized_radial_eigenvector j)

def haar (j : Fin 5) (t : ℝ) : HaarL2 := lift (chord j t)

theorem haar_norm (j : Fin 5) (t : ℝ) : ‖haar j t‖ = ‖chord j t‖ := lift_norm _

theorem haar_orthogonal (j : Fin 5) (t : ℝ) :
    inner ℝ (haar j t) (groundVector (ground (1/t^2))) = 0 :=
  (ground_complement_iff _ _).mpr (chord_orthogonal j t)

theorem haar_error_norm (j : Fin 5) (t : ℝ) :
    ‖haarOperator (ground (1/t^2)) (haar j t)-(ratio j)^2 • haar j t‖ =
      ‖chordOperator (ground (1/t^2)) (chord j t)-(ratio j)^2 • chord j t‖ := by
  rw [← lift_norm]
  simp only [map_sub,map_smul,intertwines,haar]

def native (j : Fin 5) (t : ℝ) : StateL2 (ground (1/t^2)) :=
  (unitary (ground (1/t^2))).symm (haar j t)

theorem native_norm (j : Fin 5) (t : ℝ) : ‖native j t‖ = ‖chord j t‖ := by
  rw [native,(unitary _).symm.norm_map,haar_norm]

theorem native_mean_zero (j : Fin 5) (t : ℝ) :
    (∫ U, native j t U ∂(ground (1/t^2)).stationary) = 0 := by
  apply (centered_iff _ _).mpr
  rw [native,(unitary _).apply_symm_apply]
  exact haar_orthogonal j t

theorem native_error_norm (j : Fin 5) (t : ℝ) :
    ‖operator (ground (1/t^2)) (native j t)-(ratio j)^2 • native j t‖ =
      ‖chordOperator (ground (1/t^2)) (chord j t)-(ratio j)^2 • chord j t‖ := by
  rw [← (unitary (ground (1/t^2))).norm_map]
  rw [map_sub,map_smul]
  have h : unitary (ground (1/t^2)) (operator (ground (1/t^2)) (native j t)) =
      haarOperator (ground (1/t^2)) (haar j t) := by
    rw [haarOperator_apply]
    rfl
  rw [h]
  simp only [native,(unitary _).apply_symm_apply]
  exact haar_error_norm j t

theorem native_error (j : Fin 5) :
    Tendsto (fun t : ℝ =>
      ‖operator (ground (1/t^2)) (native j t)-(ratio j)^2 • native j t‖)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  simpa only [native_error_norm] using chord_error j

theorem native_unit_mean_zero (j : Fin 5) :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ‖native j t‖ = 1 ∧
      (∫ U, native j t U ∂(ground (1/t^2)).stationary) = 0 := by
  filter_upwards [chord_norm j] with t ht
  exact ⟨(native_norm j t).trans ht,native_mean_zero j t⟩

theorem native_action_lower (j : Fin 5) (a : ℝ) (ha : a < (ratio j)^2) :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), a < ‖operator (ground (1/t^2)) (native j t)‖ := by
  have h := (native_error j).eventually
    (eventually_lt_nhds (sub_pos.mpr ha))
  filter_upwards [native_unit_mean_zero j,h] with t hn he
  have hb := norm_sub_norm_le ((ratio j)^2 • native j t)
    (operator (ground (1/t^2)) (native j t))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),hn.1,mul_one,
    norm_sub_rev] at hb
  linarith

theorem native_quasimode (j : Fin 5) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ∃ f : StateL2 (ground (1/t^2)),
      ‖f‖ = 1 ∧ (∫ U, f U ∂(ground (1/t^2)).stationary) = 0 ∧
        ‖operator (ground (1/t^2)) f-(ratio j)^2 • f‖ < ε := by
  filter_upwards [native_unit_mean_zero j,(native_error j).eventually
    (eventually_lt_nhds hε)] with t hn he
  exact ⟨native j t,hn.1,hn.2,he⟩

end OperatorDerivativeRewrite.Foundation.CubeRadialStationaryQuasimode
