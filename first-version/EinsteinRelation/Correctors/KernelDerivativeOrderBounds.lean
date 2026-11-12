import EinsteinRelation.Correctors.RadialAverageMomentBounds

/-! # Uniformity over coordinate derivatives of a fixed order

Source: `paper/main.tex:1015–1018`. Only finitely many coordinate
sequences have a prescribed order. One constant controls all of them.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors.KernelCalculus

/-- One positive constant bounds the masses of all derivatives of a fixed
order of one profile (`paper/main.tex:1015–1018`). -/
theorem exists_integral_abs_coordinateIterate_order_bound {d : ℕ}
    (K : Vec d → ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ cs : List (Fin d), cs.length = n →
      (∫ x : Vec d, |coordinateIterate cs K x|) ≤ C := by
  classical
  let a : (Fin n → Fin d) → ℝ := fun σ => ∫ x : Vec d, |coordinateIterate (List.ofFn σ) K x|
  have ha (σ : Fin n → Fin d) : 0 ≤ a σ := integral_nonneg fun _ => abs_nonneg _
  refine ⟨1 + ∑ σ, a σ, by positivity, ?_⟩
  intro cs hcs
  subst n
  have hs := Finset.single_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (Fin cs.length → Fin d))) => ha σ)
    (Finset.mem_univ cs.get)
  have he : a cs.get = ∫ x : Vec d, |coordinateIterate cs K x| := by
    simp only [a, List.ofFn_get]
  rw [he] at hs
  linarith

end EinsteinRelation.Correctors.KernelCalculus
