import EinsteinRelation.Correctors.MeasurableWeakGradient
import EinsteinRelation.Correctors.SemigroupSpatialGradient
import EinsteinRelation.Correctors.ParabolicGradientRepresentative

/-! # A joint version of the supplied semigroup gradient

Source: `paper/main.tex:789–816,822–840`. The scalar source witness is
jointly measurable. Recovering spatial weak derivatives from that scalar
witness gives a jointly measurable version of its actual PDE gradient on
one event of coefficients, times and spatial points.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The scalar flow's actual Sobolev gradients admit a jointly measurable
version without an additional selection hypothesis.
Source: `paper/main.tex:789–816,822–840`. -/
theorem exists_measurable_semigroupGradient_version {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K))
    (g : Coefficient d K → Vec d → Vec d)
    (u : Coefficient d K → ℝ × Vec d → ℝ)
    (G : Coefficient d K → ℝ × Vec d → Vec d)
    (hum : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2))
    (hsol : ∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) :
    ∃ H : Coefficient d K → ℝ × Vec d → Vec d,
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2) ∧
      ∀ᵐ A ∂P, ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
        ((fun x => H A (t, x)) =ᵐ[volume] (fun x => G A (t, x))) ∧
        HasWeakGradient Set.univ (fun x => u A (t, x)) (fun x => H A (t, x)) := by
  let f : (Coefficient d K × ℝ) → Vec d → ℝ := fun z x => u z.1 (z.2, x)
  have hfm : Measurable (fun z : (Coefficient d K × ℝ) × Vec d => f z.1 z.2) :=
    hum.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  obtain ⟨H₀, hH₀m, hH₀G⟩ := exists_measurable_spatialGradient_recovery f hfm
  let H : Coefficient d K → ℝ × Vec d → Vec d := fun A z => H₀ (A, z.1) z.2
  refine ⟨H, ?_, ?_⟩
  · exact hH₀m.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  · filter_upwards [hsol] with A hA
    filter_upwards [semigroupSolution_weakGradient_positive_ae hA] with t ht
    have heq : (fun x => H A (t, x)) =ᵐ[volume] (fun x => G A (t, x)) :=
      hH₀G (A, t) (fun x => G A (t, x)) ht
    refine ⟨heq, ?_⟩
    apply hasWeakGradient_congr_ae isOpen_univ ht Filter.EventuallyEq.rfl
    simpa only [Measure.restrict_univ] using heq.symm

/-- Recover a joint gradient while retaining every positive-time energy
cylinder and the same scalar initial trace. Source: `paper/main.tex:789–816`. -/
theorem exists_measurable_semigroupGradient_solution {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K))
    (g : Coefficient d K → Vec d → Vec d)
    (u : Coefficient d K → ℝ × Vec d → ℝ)
    (G : Coefficient d K → ℝ × Vec d → Vec d)
    (hum : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2))
    (hsol : ∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) :
    ∃ H : Coefficient d K → ℝ × Vec d → Vec d,
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2) ∧
      (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (H A)) ∧
      ∀ᵐ A ∂P, ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
        ((fun x => H A (t, x)) =ᵐ[volume] (fun x => G A (t, x))) ∧
        HasWeakGradient Set.univ (fun x => u A (t, x)) (fun x => H A (t, x)) := by
  obtain ⟨H, hHm, hHG⟩ := exists_measurable_semigroupGradient_version P g u G hum hsol
  refine ⟨H, hHm, ?_, hHG⟩
  filter_upwards [hsol, hHG] with A hA heqA
  apply semigroupSolution_gradient_congr_ae hA
  intro a b R ha hab hR
  let μ : Measure ℝ := volume.restrict (Set.Ioo a b)
  let ν : Measure (Vec d) := volume.restrict (originBall d R)
  have hGm : AEStronglyMeasurable (G A) (μ.prod ν) := by
    simpa only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod] using
      (hA.2.1 a b R ha hab hR).2.1
  have hHmA : AEStronglyMeasurable (H A) (μ.prod ν) :=
    ((hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  have heq : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, G A (t, x) = H A (t, x) := by
    have hsub : Set.Ioo a b ⊆ Set.Ioi 0 := fun t ht => ha.trans ht.1
    filter_upwards [heqA.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))]
      with t ht
    exact (ht.1.symm).filter_mono (ae_mono (Measure.restrict_le_self))
  have hmk : hGm.mk (G A) =ᵐ[μ.prod ν] hHmA.mk (H A) := by
    apply (Measure.ae_prod_iff_ae_ae
      (hGm.stronglyMeasurable_mk.measurableSet_eq_fun hHmA.stronglyMeasurable_mk)).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hGm.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hHmA.ae_eq_mk, heq] with t htG htH ht
    filter_upwards [htG, htH, ht] with x hxG hxH hx
    exact hxG.symm.trans (hx.trans hxH)
  have hGH := hGm.ae_eq_mk.trans (hmk.trans hHmA.ae_eq_mk.symm)
  simpa only [μ, ν, Measure.prod_restrict, ← Measure.volume_eq_prod] using hGH

end EinsteinRelation.Correctors
