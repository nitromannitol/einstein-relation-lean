import EinsteinRelation.Correctors.SemigroupSpatialTranslation

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Joint measurability is preserved by the inverse coefficient translation
and the forward spatial translation. Source: `paper/main.tex:798–806`. -/
theorem measurable_semigroupFlow_spatial_reindex {d : ℕ} {K : ℝ}
    {E : Type*} [MeasurableSpace E]
    (u : Coefficient d K → ℝ × Vec d → E)
    (hum : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2))
    (v : Vec d) :
    Measurable (fun z : Coefficient d K × (ℝ × Vec d) =>
      u (translateCoefficient (-v) z.1) (z.2.1,v+z.2.2)) := by
  have hr : Measurable (fun z : Coefficient d K × (ℝ × Vec d) =>
      (translateCoefficient (-v) z.1,(z.2.1,v+z.2.2))) :=
    ((measurable_translateCoefficient (-v)).comp measurable_fst).prodMk
      (measurable_snd.fst.prodMk (measurable_const.add measurable_snd.snd))
  exact hum.comp hr

/-- Simultaneously translating the coefficient label and spatial point
retains the original coefficient in the equation. Source:
`paper/main.tex:798–806`. -/
theorem semigroupFlow_spatial_reindex_solution {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) (v : Vec d)
    (hP : MeasurePreserving (translateCoefficient (-v)) P P)
    (g : Coefficient d K → Vec d → Vec d)
    (u : Coefficient d K → ℝ × Vec d → ℝ)
    (G : Coefficient d K → ℝ × Vec d → Vec d)
    (hsol : ∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) :
    ∀ᵐ A ∂P, IsSemigroupSolution A
      (fun x => g (translateCoefficient (-v) A) (v+x))
      (fun z => u (translateCoefficient (-v) A) (z.1,v+z.2))
      (fun z => G (translateCoefficient (-v) A) (z.1,v+z.2)) := by
  filter_upwards [hP.quasiMeasurePreserving.ae hsol] with A hA
  have hcoeff : translateCoefficient v (translateCoefficient (-v) A) = A := by
    cases A
    simp only [translateCoefficient,neg_add_cancel_left]
  simpa only [hcoeff] using semigroupSolution_spatial_translation hA v

/-- The genuine prescribed-time weak gradients translate with the same
scalar flow. Source: `paper/main.tex:798–806`. -/
theorem semigroupFlow_spatial_reindex_gradient {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) (v : Vec d)
    (hP : MeasurePreserving (translateCoefficient (-v)) P P)
    (u : Coefficient d K → ℝ × Vec d → ℝ)
    (H : Coefficient d K → ℝ × Vec d → Vec d)
    (hH : ∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
      (fun x => u A (t,x)) (fun x => H A (t,x))) :
    ∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
      (fun x => u (translateCoefficient (-v) A) (t,v+x))
      (fun x => H (translateCoefficient (-v) A) (t,v+x)) := by
  filter_upwards [hP.quasiMeasurePreserving.ae hH] with A hA
  intro t ht
  exact EinsteinRelation.HasWeakGradient.translated (hA t ht) v

end EinsteinRelation.Correctors
