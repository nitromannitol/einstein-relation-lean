import MarkovProcess.Path.DenseFiltration
import MarkovProcess.Path.StoppedValueMeasurability
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.PiSystem
import EinsteinRelation.Diffusion.Basic

/-!
# Countable π-systems generating the canonical path filtration at rational times

For every rational time `S`, a countable π-system containing `univ` and generating the canonical
σ-algebra `F_S` of the continuous-path coordinates up to time `S`.  It is obtained from a countable
generating set of the countable product of the rational-past coordinates
(`MarkovProcess.ContinuousPath.comap_densePastRestriction_eq_canonicalFiltration`).
-/

open MeasureTheory

namespace EinsteinFull
open EinsteinRelation

theorem countable_generatePiSystem {α : Type*} {g : Set (Set α)} (hg : g.Countable) :
    (generatePiSystem g).Countable := by
  refine ((Set.countable_ofPred_finite_subset hg).image (fun F : Set (Set α) => ⋂₀ F)).mono ?_
  intro s hs
  induction hs using generatePiSystem_induction with
  | base s hs => exact ⟨{s}, ⟨Set.finite_singleton _, Set.singleton_subset_iff.2 hs⟩, by simp⟩
  | inter u v hu hv huv ihu ihv =>
    obtain ⟨F, ⟨hF, hFg⟩, hFu⟩ := ihu
    obtain ⟨G, ⟨hG, hGg⟩, hGv⟩ := ihv
    refine ⟨F ∪ G, ⟨hF.union hG, Set.union_subset hFg hGg⟩, ?_⟩
    show ⋂₀ (F ∪ G) = u ∩ v
    rw [Set.sInter_union]
    exact congrArg₂ _ hFu hGv

theorem exists_cylinder_piSystem (d : ℕ) :
    ∃ cyl : MarkovProcess.DenseTime → Set (Set (Path d)),
      (∀ S, (cyl S).Countable) ∧ (∀ S, IsPiSystem (cyl S)) ∧ (∀ S, Set.univ ∈ cyl S) ∧
      ∀ S, MeasurableSpace.generateFrom (cyl S) =
        MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)
          (MarkovProcess.DenseTime.castOrderEmbedding S) := by
  let f : (S : MarkovProcess.DenseTime) → Path d → (Set.Iic S → Vec d) := fun S =>
    MarkovProcess.ContinuousPath.densePastRestriction (alpha := Vec d) S
  refine ⟨fun S => insert Set.univ
    {s | ∃ t ∈ generatePiSystem (MeasurableSpace.countableGeneratingSet (Set.Iic S → Vec d)),
      f S ⁻¹' t = s}, ?_, ?_, ?_, ?_⟩
  · intro S
    exact Set.Countable.insert _ ((countable_generatePiSystem
      MeasurableSpace.countable_countableGeneratingSet).image (fun t => f S ⁻¹' t))
  · intro S
    exact IsPiSystem.insert_univ ((isPiSystem_generatePiSystem _).comap (f S))
  · intro S
    exact Set.mem_insert _ _
  · intro S
    rw [MeasurableSpace.generateFrom_insert_univ]
    have h1 : {s | ∃ t ∈ generatePiSystem
        (MeasurableSpace.countableGeneratingSet (Set.Iic S → Vec d)), f S ⁻¹' t = s} =
        (fun t => f S ⁻¹' t) '' generatePiSystem
          (MeasurableSpace.countableGeneratingSet (Set.Iic S → Vec d)) := rfl
    rw [h1, ← MeasurableSpace.comap_generateFrom, generateFrom_generatePiSystem_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
    exact MarkovProcess.ContinuousPath.comap_densePastRestriction_eq_canonicalFiltration S

end EinsteinFull
