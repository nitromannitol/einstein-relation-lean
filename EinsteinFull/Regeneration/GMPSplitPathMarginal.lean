import EinsteinFull.Regeneration.SplitPathMarginal

/-!
# Continuous splitting of the actual fixed-environment GMP process

The GMP realization supplies its starting-position and complete-past Markov
laws. Under the actual source minorization, the canonical continuous splitting
therefore has the original whole-path marginal, the Bernoulli product coin
law and the literal finite-history fresh-bit identity. Identifying a paper law
with this source realization and proving its force-uniform minorization remain
separate obligations.
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

private def fixedGMPPathKernel : QuenchedPathLaws d :=
  G.pathLaw.comap Prod.fst measurable_fst

private instance isMarkovKernel_fixedGMPPathKernel : IsMarkovKernel (fixedGMPPathKernel G) := by
  letI := G.pathLaw_isMarkovKernel
  unfold fixedGMPPathKernel
  infer_instance

variable (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (hminor : EinsteinFull.External.Source.GMP.HasSourceMinorization G.pathLaw Δ δ R i)

/-- The canonical continuous path/coin kernel for the actual GMP realization
in its fixed environment, indexed by every spatial starting point. -/
def gmpContinuousSplitKernel : Kernel (Vec d) (CoupledSample d) :=
  (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR (fixedGMPPathKernel G)
    (fun _ => hminor)).comap (fun x => (x, ω)) (measurable_id.prodMk measurable_const)

instance isMarkovKernel_gmpContinuousSplitKernel :
    IsMarkovKernel (gmpContinuousSplitKernel G Δ hΔ δ R i hδ₀ hδ₁ hR hminor) := by
  have := isMarkovKernel_splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR
    (fixedGMPPathKernel G) (fun _ => hminor)
  exact Kernel.IsMarkovKernel.comap _ (measurable_id.prodMk measurable_const)

/-- Splitting and gluing the actual GMP process preserves its entire path
law at every spatial starting point. The process's restart law is proved,
not an extra premise of this specialization. -/
theorem map_gmpContinuousSplitKernel_path :
    (gmpContinuousSplitKernel G Δ hΔ δ R i hδ₀ hδ₁ hR hminor).map Prod.fst =
      G.pathLaw := by
  have hstart : ∀ a, ∀ᵐ γ ∂fixedGMPPathKernel G a, γ 0 = a.1 :=
    fun a => G.pathLaw_starts_at a.1
  have hslice : (fixedGMPPathKernel G).comap (fun x : Vec d => (x, ω))
      (measurable_id.prodMk measurable_const) = G.pathLaw := by
    ext x : 1
    rfl
  ext x : 1
  rw [Kernel.map_apply _ measurable_fst, gmpContinuousSplitKernel, Kernel.comap_apply]
  apply map_splitContinuousCouplingKernel_path Δ hΔ δ R i hδ₀ hδ₁ hR
    (fixedGMPPathKernel G) (fun _ => hminor) hstart (x, ω)
  intro n
  rw [hslice]
  exact gmpPathLaw_prefix_future_joint G ((n + 1 : ℕ) * Δ) x

/-- The full coin sequence in this same GMP coupling has the literal
Bernoulli product law, for every spatial starting point. -/
theorem map_gmpContinuousSplitKernel_coins :
    (gmpContinuousSplitKernel G Δ hΔ δ R i hδ₀ hδ₁ hR hminor).map Prod.snd =
      Kernel.const (Vec d) (Measure.infinitePi (fun _ : ℕ => splitCoinLaw δ)) := by
  rw [gmpContinuousSplitKernel, ← Kernel.comap_map_comm _
    (show Measurable (fun x : Vec d => (x, ω)) from
      measurable_id.prodMk measurable_const) measurable_snd,
    map_splitContinuousCouplingKernel_coin_product Δ δ R i hδ₀ hδ₁ hR
      (fixedGMPPathKernel G) (fun _ => hminor) hΔ]
  ext x : 1
  rfl

/-- Freshness against the actual closed path and previous-coin history holds
for this same GMP coupling at every deterministic grid time and spatial start. -/
theorem freshBits_gmpContinuousSplitKernel (x : Vec d) (n : ℕ)
    (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ
      (finiteHistorySigma Δ n) inferInstance H)
    (hb : BoundedRealTest H) :
    (∫ z, H z * (if z.2 n = true then (1 : ℝ) else 0)
      ∂gmpContinuousSplitKernel G Δ hΔ δ R i hδ₀ hδ₁ hR hminor x) =
        δ * ∫ z, H z ∂gmpContinuousSplitKernel G Δ hΔ δ R i hδ₀ hδ₁ hR hminor x := by
  exact freshBitsAt_splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR
    (fixedGMPPathKernel G) (fun _ => hminor) (fun a => G.pathLaw_starts_at a.1) (x, ω)
      n H hH hb

end EinsteinFull.Regeneration
