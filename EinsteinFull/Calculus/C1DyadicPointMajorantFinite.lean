import EinsteinFull.Calculus.C1DyadicPointInitialization
import EinsteinFull.Calculus.C19FirstUnitGradientProjection

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c1_dyadic_actual_point_majorant_finite (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 1 ≤ T) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ‖ζ‖ ≤ 2 → ∀ growth : ℝ, 0 ≤ growth → let S : Set ℝ := {z | ∃ t : ℝ≥0, 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ T ∧ z = ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ / (Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)))}; S.Nonempty ∧ BddAbove S ∧ 0 ≤ sSup S ∧ sSup S ≤ C ∧ ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) ≤ T → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤ sSup S * (Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4))) := by
  obtain ⟨C, hC, hbound⟩ := c1_dyadic_bounded_time_point_decay
    (c19_dyadic_locality_input_of_forced_local hlocal) d hd D T hT
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth hgrowth
  dsimp only
  let w : ℝ≥0 → ℝ := fun t => Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) *
    ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4))
  have hw (t : ℝ≥0) (ht : 1 ≤ (t : ℝ)) :
      0 < w t ∧ (t : ℝ) ^ (-(1/2+(d : ℝ)/4)) ≤ w t := by
    have htpos : 0 < (t : ℝ) := by linarith
    have hp : 0 < (t : ℝ) ^ (-(1/2+(d : ℝ)/4)) := Real.rpow_pos_of_pos htpos _
    have hp2 : 0 ≤ ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4) := by positivity
    have he : 1 ≤ Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) := by
      apply Real.one_le_exp_iff.mpr
      positivity
    dsimp [w]
    constructor
    · positivity
    · nlinarith
  have hratio (t : ℝ≥0) (ht : 1 ≤ (t : ℝ)) (htT : (t : ℝ) ≤ T) :
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ / w t ≤ C := by
    apply (div_le_iff₀ (hw t ht).1).2
    have hb := hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht htT
    exact hb.trans (mul_le_mul_of_nonneg_left (hw t ht).2 (by linarith))
  let S : Set ℝ := {z | ∃ t : ℝ≥0, 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ T ∧
    z = ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ / w t}
  have hn : S.Nonempty := ⟨_, ⟨1, by norm_num, by simpa using hT, rfl⟩⟩
  have hb : BddAbove S := ⟨C, by rintro z ⟨t, ht, htT, rfl⟩; exact hratio t ht htT⟩
  change S.Nonempty ∧ BddAbove S ∧ 0 ≤ sSup S ∧ sSup S ≤ C ∧ _
  refine ⟨hn, hb, ?_, csSup_le hn (by rintro z ⟨t, ht, htT, rfl⟩; exact hratio t ht htT), ?_⟩
  · obtain ⟨z, ⟨t, ht, htT, rfl⟩⟩ := hn
    exact le_trans (div_nonneg (norm_nonneg _) (le_of_lt (hw t ht).1)) (le_csSup hb ⟨t, ht, htT, rfl⟩)
  · intro t ht htT
    have h := le_csSup hb (show ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ / w t ∈ S from ⟨t, ht, htT, rfl⟩)
    exact (div_le_iff₀ (hw t ht).1).1 h

end EinsteinFull.Blueprint
