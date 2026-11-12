import EinsteinRelation.Diffusion.TranslatedRealization
import EinsteinRelation.Diffusion.RealizationUniquenessFromLocality
import EinsteinRelation.Diffusion.GMPFamily

/-!
# Spatial covariance of the reduced diffusion

Source `paper/main.tex:406–408`. The translated actual GMP realization
is identified with the given realization by the frozen stopped-locality
input on the whole space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Diffusion
open External.GantertSection7Support

/-- The actual reduced zero-potential coefficient pair commutes with
the physical spatial translation. -/
theorem zeroPotentialReducedPair_translate {d : ℕ} (a : Vec d) (ω : FieldPair d) :
    zeroPotentialReducedPair (translate a ω) = translate a (zeroPotentialReducedPair ω) := by
  unfold zeroPotentialReducedPair
  rw [reduce_translate]
  rfl

/-- Spatial covariance of actual reduced path laws on two regular
environments, derived from full realization transport and frozen locality. -/
theorem reduced_pathLaw_map_recenter_eq_of_realizations (hLoc : External.GMPKernelLocality)
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (ω : FieldPair d) (a : Vec d)
    (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
    (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair (translate a ω)))
    (r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
      (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
      (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair (translate a ω)) hω' lam h0 h1)
    (x : Vec d) :
    (r.pathLaw (a + x)).map (Regeneration.recenterPathEquiv a) = r'.pathLaw x := by
  let rt := translateRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
    (zeroPotentialReducedPair ω) hω lam h0 h1 r a
  have hωt : IsRegular (sourceReducedBound Λ₀) (translate a (zeroPotentialReducedPair ω)) :=
    (ActualImageLpStateTransport.isRegular_translate_iff a _).mpr hω
  let rs : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
      (one_le_sourceReducedBound hΛ₀) (translate a (zeroPotentialReducedPair ω)) hωt lam h0 h1 := by
    simpa only [zeroPotentialReducedPair_translate] using r'
  have heq := realization_pathLaw_eq_of_locality hLoc hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound hΛ₀) (translate a (zeroPotentialReducedPair ω)) hωt lam h0 h1 rt rs
  have h := congrArg (fun L : Kernel (Vec d) (Path d) => L x) heq
  simpa [rt, rs, translateRealization,
    Kernel.map_apply _ (Regeneration.recenterPathEquiv a).measurable, Kernel.comap_apply] using h


end EinsteinRelation.Diffusion
