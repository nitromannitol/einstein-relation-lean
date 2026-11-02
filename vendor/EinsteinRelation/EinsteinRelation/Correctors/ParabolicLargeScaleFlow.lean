import EinsteinRelation.Correctors.ParabolicTimeTranslation
import EinsteinRelation.Correctors.LocalEnergyVolumeComparison
import Mathlib.MeasureTheory.Integral.Prod

/-! # Large-scale gradient comparison for the supplied parabolic flow

Source: `paper/main.tex:788–796`. AKM's backward-cylinder estimates apply
to the genuine positive-time flow. Time slices retain the almost-everywhere
qualifier of the literature input; no endpoint gradient is selected here.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The energy class of a weak cylinder supplies its spatial L² slices.
Source: `paper/main.tex:788–796,822–830`. -/
theorem parabolicSolution_gradient_slice_memLp {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G) :
    ∀ᵐ t ∂volume.restrict I,
      MemLp (fun x => euclideanNorm (G (t,x))) 2 (volume.restrict U) := by
  have hG : MemLp (fun z => euclideanNorm (G z)) 2
      ((volume.restrict I).prod (volume.restrict U)) := by
    simpa only [Measure.prod_restrict] using! hsol.2.2.1
  filter_upwards [hG.aestronglyMeasurable.prodMk_left, hG.integrable_sq.prod_right_ae]
    with t hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

/-- One random scale serves every positive-time flow and every cylinder
lying above time zero. The gradient comparison is evaluated on genuine
spatial slices of that flow. Source: `paper/main.tex:788–796`. -/
theorem parabolicLargeScale_semigroup_gradient (hAKM : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∃ X : Coefficient d K → ℝ, Measurable X ∧
        (∀ A, 1 ≤ X A) ∧ StretchedExponentialBound P s C X ∧
        ∀ᵐ A ∂P, ∀ (g : Vec d → Vec d) (u : ℝ × Vec d → ℝ)
          (G : ℝ × Vec d → Vec d), IsSemigroupSolution A g u G →
          ∀ R : ℝ, X A ≤ R → ∀ t : ℝ, R^2 < t →
            ∀ r : ℝ, X A ≤ r → r ≤ R / 2 →
              ∀ᵐ τ ∂volume.restrict (Set.Ioo (-(r^2)/4) 0),
                vectorRms volume (originBall d (r/2)) (fun x => G (τ+t,x)) ≤
                  C * vectorRms volume (cylinder d R) (fun z => G (z.1+t,z.2)) := by
  obtain ⟨C, hC, hreg⟩ := hAKM d hd K s hK hs hsd
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨X, hXm, hX, htail, hbound⟩ := hreg P hP
  refine ⟨X, hXm, hX, htail, ?_⟩
  filter_upwards [hbound] with A hA
  intro g u G hsol R hR t ht r hr hrR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one ((hX A).trans hR)
  exact hA R hR _ _ (semigroupSolution_backward_cylinder hsol hR0 ht) r hr hrR

/-- Restricting the spatial ball in a time-slice comparison costs exactly
its volume ratio. No unproved spatial integrability is added as a premise.
Source: `paper/main.tex:788–796`. -/
theorem parabolicSolution_gradient_slice_restrict {d : ℕ} {K C : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U V : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    (hVU : V ⊆ U) (hV : volume V ≠ 0) (hVfin : volume V ≠ ⊤)
    (hUfin : volume U ≠ ⊤)
    (hb : ∀ᵐ t ∂volume.restrict I, vectorRms volume U (fun x => G (t,x)) ≤ C) :
    ∀ᵐ t ∂volume.restrict I,
      vectorRms volume V (fun x => G (t,x)) ≤
        Real.sqrt ((volume U).toReal / (volume V).toReal) * C := by
  filter_upwards [parabolicSolution_gradient_slice_memLp hsol, hb] with t hG ht
  exact (vectorRms_mono_set_volume_ratio volume hVU hV hVfin hUfin _ hG).trans
    (mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _))

end EinsteinRelation.Correctors
