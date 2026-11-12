import EinsteinRelation.External.AKMLocalCorrectors

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Scalar moment estimates are preserved by a measure-preserving change
of the coefficient and a fixed spatial translation. Source:
`paper/main.tex:798–806`. -/
theorem semigroupFlow_scalar_moments_reindex {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {ρ : Coefficient d K → Coefficient d K}
    (hρ : MeasurePreserving ρ P P) (v : Vec d)
    (u : Coefficient d K → ℝ × Vec d → ℝ) (F : ℝ → ℝ)
    (hval : ∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
      MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
      eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
        ENNReal.ofReal (F m*t^(-(1 : ℝ)/2-(d : ℝ)/4))) :
    ∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
      MemLp (fun A => u (ρ A) (t,v+x)) (ENNReal.ofReal m) P ∧
      eLpNorm (fun A => u (ρ A) (t,v+x)) (ENNReal.ofReal m) P ≤
        ENNReal.ofReal (F m*t^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
  intro m hm t ht x
  have he := hval m hm t ht (v+x)
  exact ⟨he.1.comp_measurePreserving hρ,
    (eLpNorm_comp_measurePreserving he.1.aestronglyMeasurable hρ).le.trans he.2⟩

/-- A measurable local gradient RMS has exactly the same probability
moment after a measure-preserving coefficient reindexing. Source:
`paper/main.tex:798–806`. -/
theorem semigroupFlow_gradient_moments_reindex_iff {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {ρ : Coefficient d K → Coefficient d K}
    (hρ : MeasurePreserving ρ P P)
    (H : Coefficient d K → ℝ × Vec d → Vec d)
    (hHm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2))
    (v : Vec d) (t : ℝ) (p : ℝ≥0∞) (B : ℝ≥0∞) :
    (MemLp (fun A => vectorRms volume (originBall d 1)
        (fun x => H (ρ A) (t,v+x))) p P ∧
      eLpNorm (fun A => vectorRms volume (originBall d 1)
        (fun x => H (ρ A) (t,v+x))) p P ≤ B) ↔
    (MemLp (fun A => vectorRms volume (originBall d 1)
        (fun x => H A (t,v+x))) p P ∧
      eLpNorm (fun A => vectorRms volume (originBall d 1)
        (fun x => H A (t,v+x))) p P ≤ B) := by
  let f : Coefficient d K → ℝ := fun A =>
    vectorRms volume (originBall d 1) (fun x => H A (t,v+x))
  have hrep : Measurable (fun z : Coefficient d K × Vec d => H z.1 (t,v+z.2)) :=
    hHm.comp (measurable_fst.prodMk (measurable_const.prodMk
      (measurable_const.add measurable_snd)))
  have hsquare : Measurable (fun z : Coefficient d K × Vec d =>
      euclideanSq (H z.1 (t,v+z.2))) := by
    unfold euclideanSq dot
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp hrep).mul ((measurable_pi_apply j).comp hrep)
  have hf : Measurable f := by
    have hi := (hsquare.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (originBall d 1))).measurable
    simpa only [f,vectorRms,average_eq,measureReal_restrict_apply_univ,smul_eq_mul] using
      (measurable_const.mul hi).sqrt
  have hm : MemLp f p P ↔ MemLp (f ∘ ρ) p P := by
    have hfmap : AEStronglyMeasurable f (Measure.map ρ P) := by
      rw [hρ.map_eq]
      exact hf.aestronglyMeasurable
    have he := memLp_map_measure_iff (p := p) hfmap hρ.aemeasurable
    simpa only [hρ.map_eq] using he
  change (MemLp (f ∘ ρ) p P ∧ eLpNorm (f ∘ ρ) p P ≤ B) ↔
    (MemLp f p P ∧ eLpNorm f p P ≤ B)
  rw [eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hρ,← hm]

end EinsteinRelation.Correctors
