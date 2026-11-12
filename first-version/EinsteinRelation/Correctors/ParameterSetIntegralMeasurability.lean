import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Measurability of restricted spatial averages

Source: `paper/main.tex:926–938`.
-/

open MeasureTheory
open Set

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:931–938`. A center integral is measurable for
an observation sigma algebra when only its contributing centers have a
jointly measurable version. -/
theorem measurable_setIntegral_of_measurable_subtype {X Ω E : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure X) [SFinite μ] {S : Set X} (hS : MeasurableSet S)
    (F : X → Ω → E)
    (hF : Measurable (fun p : S × Ω => F p.1.1 p.2)) :
    Measurable (fun ω => ∫ x in S, F x ω ∂μ) := by
  classical
  let G : X × Ω → E := fun p => if h : p.1 ∈ S then F p.1 p.2 else 0
  have hG_meas : Measurable G := by
    refine measurable_of_restrict_of_restrict_compl (hS.prod MeasurableSet.univ) ?_ ?_
    · -- G restricted to S ×ˢ Set.univ is measurable
      let ψ : (S ×ˢ Set.univ : Set (X × Ω)) → S × Ω := fun p =>
        (⟨p.1.1, (Set.mem_prod.1 p.2).1⟩, p.1.2)
      have hψ_meas : Measurable ψ := by
        refine Measurable.prodMk ?_ ?_
        · refine Measurable.subtype_mk ?_
          exact measurable_fst.comp measurable_subtype_coe
        · exact measurable_snd.comp measurable_subtype_coe
      have h_eq : (S ×ˢ Set.univ : Set (X × Ω)).restrict G =
          (fun p : S × Ω => F p.1.1 p.2) ∘ ψ := by
        ext p
        dsimp [G, Set.restrict, ψ]
        rcases Set.mem_prod.1 p.2 with ⟨hx, hω⟩
        simp [hx]
      rw [h_eq]
      exact hF.comp hψ_meas
    · -- G restricted to the complement is constant zero
      have h_eq : ((S ×ˢ Set.univ : Set (X × Ω))ᶜ).restrict G = fun _ => (0 : E) := by
        ext p
        dsimp [G, Set.restrict]
        by_cases hx : p.1.1 ∈ S
        · exfalso
          apply p.2
          exact Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩
        · simp [hx]
      rw [h_eq]
      exact measurable_const
  let f : Ω × X → E := fun p => G (p.2, p.1)
  have hf_meas : Measurable f := by
    exact hG_meas.comp measurable_swap
  have hf_strong : StronglyMeasurable f := hf_meas.stronglyMeasurable
  have h_int_strong : StronglyMeasurable (fun (ω : Ω) => ∫ x, f (ω, x) ∂μ) :=
    hf_strong.integral_prod_right' (ν := μ)
  have h_eq : (fun (ω : Ω) => ∫ x, f (ω, x) ∂μ) = (fun ω => ∫ x in S, F x ω ∂μ) := by
    ext ω
    dsimp [f, G]
    calc
      ∫ x, (if h : x ∈ S then F x ω else 0) ∂μ
          = ∫ x, S.indicator (fun x => F x ω) x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with x
        simp [Set.indicator]
      _ = ∫ x in S, F x ω ∂μ := by rw [integral_indicator hS]
  simpa [h_eq] using h_int_strong.measurable

end EinsteinRelation.Correctors
