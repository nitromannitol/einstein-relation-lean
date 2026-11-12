import EinsteinRelation.External.GantertSection7Support
import Mathlib.Probability.Kernel.Composition.CompMap

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace EinsteinRelation.Probability

/-- Source `paper/main.tex:406–408`: conjugation by a measurable equivalence preserves a transition semigroup. -/
theorem conjugate_kernel_semigroup {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)]
    (hz : K 0 = Kernel.id) (ha : ∀ s t, K (s + t) = K t ∘ₖ K s) :
    let L : ℝ≥0 → Kernel α α := fun t => ((K t).comap e e.measurable).map e.symm
    L 0 = Kernel.id ∧ ∀ s t, L (s + t) = L t ∘ₖ L s := by
  intro L
  have h_symm_comp : Kernel.deterministic e.symm e.symm.measurable ∘ₖ Kernel.deterministic e e.measurable =
      Kernel.id := by
    calc
      Kernel.deterministic e.symm e.symm.measurable ∘ₖ Kernel.deterministic e e.measurable =
          Kernel.deterministic (e.symm ∘ e) (e.symm.measurable.comp e.measurable) := by
        rw [Kernel.deterministic_comp_deterministic e.measurable e.symm.measurable]
      _ = Kernel.id := by
        have h : e.symm ∘ e = id := funext fun x => e.symm_apply_apply x
        simp [h, Kernel.id]
  have h_comp_symm : Kernel.deterministic e e.measurable ∘ₖ Kernel.deterministic e.symm e.symm.measurable =
      Kernel.id := by
    calc
      Kernel.deterministic e e.measurable ∘ₖ Kernel.deterministic e.symm e.symm.measurable =
          Kernel.deterministic (e ∘ e.symm) (e.measurable.comp e.symm.measurable) := by
        rw [Kernel.deterministic_comp_deterministic e.symm.measurable e.measurable]
      _ = Kernel.id := by
        have h : e ∘ e.symm = id := funext fun x => e.apply_symm_apply x
        simp [h, Kernel.id]
  have hL0 : L 0 = Kernel.id := by
    dsimp [L]
    rw [hz]
    calc
      ((Kernel.id : Kernel α α).comap e e.measurable).map e.symm =
          (Kernel.deterministic e e.measurable).map e.symm := by
        simp [Kernel.id_comap]
      _ = Kernel.deterministic e.symm e.symm.measurable ∘ₖ Kernel.deterministic e e.measurable := by
        rw [← Kernel.deterministic_comp_eq_map e.symm.measurable (Kernel.deterministic e e.measurable)]
      _ = Kernel.id := h_symm_comp
  have hLs : ∀ s t, L (s + t) = L t ∘ₖ L s := by
    intro s t
    dsimp [L]
    rw [ha s t]
    have h_map_comp : ((K t ∘ₖ K s).comap e e.measurable).map e.symm =
        (Kernel.deterministic e.symm e.symm.measurable ∘ₖ K t ∘ₖ K s) ∘ₖ Kernel.deterministic e e.measurable := by
      calc
        ((K t ∘ₖ K s).comap e e.measurable).map e.symm =
            ((K t ∘ₖ K s) ∘ₖ Kernel.deterministic e e.measurable).map e.symm := by
          rw [Kernel.comp_deterministic_eq_comap]
        _ = ((K t ∘ₖ K s).map e.symm) ∘ₖ Kernel.deterministic e e.measurable := by
          rw [Kernel.map_comp]
        _ = (((K t).map e.symm) ∘ₖ K s) ∘ₖ Kernel.deterministic e e.measurable := by
          rw [Kernel.map_comp]
        _ = ((Kernel.deterministic e.symm e.symm.measurable ∘ₖ K t) ∘ₖ K s) ∘ₖ Kernel.deterministic e e.measurable := by
          rw [Kernel.deterministic_comp_eq_map e.symm.measurable (K t)]
        _ = (Kernel.deterministic e.symm e.symm.measurable ∘ₖ K t ∘ₖ K s) ∘ₖ Kernel.deterministic e e.measurable := by
          simp [Kernel.comp_assoc]
    have h_comp_map : (((K t).comap e e.measurable).map e.symm) ∘ₖ (((K s).comap e e.measurable).map e.symm) =
        (Kernel.deterministic e.symm e.symm.measurable ∘ₖ K t ∘ₖ K s) ∘ₖ Kernel.deterministic e e.measurable := by
      calc
        (((K t).comap e e.measurable).map e.symm) ∘ₖ (((K s).comap e e.measurable).map e.symm) =
            (Kernel.comap ((K t).map e.symm) e e.measurable) ∘ₖ (Kernel.comap ((K s).map e.symm) e e.measurable) := by
          rw [← Kernel.comap_map_comm (K t) e.measurable e.symm.measurable,
            ← Kernel.comap_map_comm (K s) e.measurable e.symm.measurable]
        _ = ((Kernel.deterministic e.symm e.symm.measurable ∘ₖ K t) ∘ₖ Kernel.deterministic e e.measurable) ∘ₖ
            ((Kernel.deterministic e.symm e.symm.measurable ∘ₖ K s) ∘ₖ Kernel.deterministic e e.measurable) := by
          simp [Kernel.deterministic_comp_eq_map e.symm.measurable (K t),
            Kernel.deterministic_comp_eq_map e.symm.measurable (K s),
            Kernel.comp_deterministic_eq_comap]
        _ = (Kernel.deterministic e.symm e.symm.measurable ∘ₖ K t ∘ₖ
            (Kernel.deterministic e e.measurable ∘ₖ Kernel.deterministic e.symm e.symm.measurable) ∘ₖ
            K s ∘ₖ Kernel.deterministic e e.measurable) := by
          simp [Kernel.comp_assoc]
        _ = (Kernel.deterministic e.symm e.symm.measurable ∘ₖ K t ∘ₖ Kernel.id ∘ₖ K s ∘ₖ Kernel.deterministic e e.measurable) := by
          rw [h_comp_symm]
        _ = (Kernel.deterministic e.symm e.symm.measurable ∘ₖ K t ∘ₖ K s ∘ₖ Kernel.deterministic e e.measurable) := by
          simp
        _ = (Kernel.deterministic e.symm e.symm.measurable ∘ₖ K t ∘ₖ K s) ∘ₖ Kernel.deterministic e e.measurable := by
          simp [Kernel.comp_assoc]
    rw [h_map_comp, h_comp_map]
  exact And.intro hL0 hLs

end EinsteinRelation.Probability
