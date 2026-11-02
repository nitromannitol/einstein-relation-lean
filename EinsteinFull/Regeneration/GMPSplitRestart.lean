import EinsteinFull.Regeneration.GMPSplitPathMarginal
import EinsteinFull.Regeneration.SplitDeterministicRestart

/-!
# Joint deterministic restart of the actual fixed-environment GMP splitting

The source process supplies the actual starting-position law. The entire
continuous future and all remaining coins restart together in this same
canonical coupling. Source minorization remains explicit; no identification
with the paper's weak process or force-uniform success constant is inferred.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
  (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (hminor : EinsteinFull.External.Source.GMP.HasSourceMinorization G.pathLaw Δ δ R i)

/-- Every bounded exact-past observation factors against the full future
path/coin law at the actual grid endpoint, for this same GMP split kernel. -/
theorem deterministicRestart_gmpContinuousSplitKernel (x : Vec d) (n : ℕ)
    (H Φ : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H)
    (hbH : BoundedRealTest H) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ z, H z * Φ (sampleTimeShift Δ z (n * Δ))
      ∂gmpContinuousSplitKernel G Δ hΔ δ R i hδ₀ hδ₁ hR hminor x) =
      ∫ z, H z * (∫ z', Φ z'
        ∂gmpContinuousSplitKernel G Δ hΔ δ R i hδ₀ hδ₁ hR hminor (z.1 (n * Δ)))
        ∂gmpContinuousSplitKernel G Δ hΔ δ R i hδ₀ hδ₁ hR hminor x := by
  letI := G.pathLaw_isMarkovKernel
  exact deterministicRestartAt_splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR
    (G.pathLaw.comap Prod.fst measurable_fst) (fun _ => hminor)
    (fun a => G.pathLaw_starts_at a.1) (x, ω) n H Φ hH hbH hΦ hbΦ

end EinsteinFull.Regeneration
