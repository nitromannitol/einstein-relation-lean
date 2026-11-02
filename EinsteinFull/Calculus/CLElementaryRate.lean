import EinsteinFull.Calculus.CLForcedLLNV2
import EinsteinFull.Calculus.C12ElementaryExpansionRate
import EinsteinFull.Blueprint.Foundation.Proofs.D1PathwiseV2

/-! `t.main#elementary-rate`, `paper/main.tex:105–110`, from the full expansion.
On a smooth environment law every member of a signed physical family has a
velocity at every nonzero force (smooth-scope forced LLN), so a velocity at one
force extends to the velocity family the expansion consumes. -/

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- A velocity at one nonzero force extends to the whole signed family. -/
theorem clr_signed_physical_family_velocity_extension {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (X : DiffusionFamily d)
    (hX : IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q X)
    (lam : ℝ) (_hlam : lam ≠ 0) (v : Vec d)
    (hv : HasQuenchedVelocity Q.measure (originLaw (X lam)) v) :
    ∃ velocity : ℝ → Vec d, velocity lam = v ∧
      ∀ l : ℝ, l ≠ 0 → HasQuenchedVelocity Q.measure (originLaw (X l)) (velocity l) := by
  classical
  have hi : External.GantertSection7Support.firstCoordinateIndex hd = (⟨0, by omega⟩ : Fin d) :=
    Fin.ext rfl
  have hex : ∀ l : ℝ, l ≠ 0 → ∃ w, HasQuenchedVelocity Q.measure (originLaw (X l)) w := by
    intro l hl
    obtain ⟨w, hw, -⟩ := clr_physical_velocity_signed
      node_eq_u2E_reduced_u2D_generator_u23_pathwise_of_deps hd D Q hQ hl (originLaw (X l))
      (by rw [hi]; exact hX l)
    exact ⟨w, hw⟩
  refine ⟨fun l => if l = lam then v else if h : l = 0 then 0 else Classical.choose (hex l h),
    by simp, ?_⟩
  intro l hl
  by_cases heq : l = lam
  · subst heq
    simpa using hv
  · simp only [heq, ite_false, hl, dite_false]
    exact Classical.choose_spec (hex l hl)

/-- `t.main#elementary-rate` from the full expansion. -/
theorem node_t_u2E_main_u23_elementary_u2D_rate_of_deps
    (hexp : node_t_u3A_expansionStmt) : node_t_u2E_main_u23_elementary_u2D_rateStmt :=
  elementary_rate_of_expansion_and_velocity_extension
    (fun hd D Q hQ X hX lam hlam v hv =>
      clr_signed_physical_family_velocity_extension hd D Q hQ X hX lam hlam v hv) hexp

end EinsteinFull.Blueprint
