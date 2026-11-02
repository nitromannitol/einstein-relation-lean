import EinsteinRelation.Diffusion.StoppedPathLocality
import EinsteinRelation.Regeneration.RenewalCarriers

/-!
# Locality of the killed one-interval diffusion and bridge mixture

Source `paper/main.tex:377–381`. Equality of the GMP laws stopped on
leaving a locality region identifies the killed segments in a contained
coupling ball. The endpoint reweighting defining the actual bridge mixture
preserves this equality. No coupled half-space locality is assumed here.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

private theorem continuous_euclideanNorm_segment {d : ℕ} :
    Continuous (fun v : Vec d => euclideanNorm v) := by
  have hs : Continuous (fun v : Vec d => ∑ j, v j * v j) := by
    apply continuous_finset_sum
    intro j _
    exact (continuous_apply j).mul (continuous_apply j)
  exact Real.continuous_sqrt.comp hs

theorem isOpen_couplingRegion {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d) :
    IsOpen (couplingRegion i R x) :=
  isOpen_lt (continuous_euclideanNorm_segment.comp
    (continuous_id.sub continuous_const)) continuous_const

private theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (g : β → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hf]
  rfl

/-- Endpoint reweighting of two finite-horizon path laws depends only on
their stopped laws, including the endpoint law in the Radon–Nikodym denominator. -/
theorem map_endpoint_reweighted_eq_of_map_stopPathAt_eq {d : ℕ} (T : ℝ≥0)
    (μ ν : Measure (Path d)) (η : Measure (Vec d))
    (heq : μ.map (Diffusion.stopPathAt T) = ν.map (Diffusion.stopPathAt T)) :
    (μ.withDensity (fun γ => (η.rnDeriv (μ.map fun γ' => γ' T)) (γ T))).map
        (Diffusion.stopPathAt T) =
      (ν.withDensity (fun γ => (η.rnDeriv (ν.map fun γ' => γ' T)) (γ T))).map
        (Diffusion.stopPathAt T) := by
  have hT := (Diffusion.continuous_stopPathAt (d := d) T).measurable
  have heval : Measurable (fun γ : Path d => γ T) := (continuous_eval_const T).measurable
  have hend : μ.map (fun γ : Path d => γ T) = ν.map (fun γ : Path d => γ T) := by
    have h := congrArg (Measure.map (fun γ : Path d => γ T)) heq
    simpa only [Measure.map_map heval hT, Function.comp_def,
      Diffusion.stopPathAt, ContinuousMap.coe_mk, min_self] using h
  rw [← hend]
  let g : Path d → ℝ≥0∞ := fun γ => (η.rnDeriv (μ.map fun γ' => γ' T)) (γ T)
  have hg : Measurable g := (Measure.measurable_rnDeriv _ _).comp heval
  have hcomp : g ∘ Diffusion.stopPathAt T = g := by
    funext γ
    simp [g, Diffusion.stopPathAt]
  change (μ.withDensity g).map (Diffusion.stopPathAt T) =
    (ν.withDensity g).map (Diffusion.stopPathAt T)
  calc
    _ = (μ.map (Diffusion.stopPathAt T)).withDensity g := by
      simpa only [hcomp] using map_withDensity_comp μ (Diffusion.stopPathAt T) g hT hg
    _ = (ν.map (Diffusion.stopPathAt T)).withDensity g := by rw [heq]
    _ = _ := by
      simpa only [hcomp] using (map_withDensity_comp ν (Diffusion.stopPathAt T) g hT hg).symm

/-- The frozen GMP locality input identifies both actual one-interval
ingredients on the coupling ball. This is the diffusion-law part of Step 2. -/
theorem killedSegment_and_bridge_map_stop_eq_of_locality
    (hLoc : External.GMPKernelLocality) {d : ℕ} (hd : 2 ≤ d)
    (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀) (U : Set (Vec d)) (hU : IsOpen U)
    (ω ω' : FieldPair d) (hω : IsRegular Λ₀ ω) (hω' : IsRegular Λ₀ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam h0 h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω' hω' lam h0 h1)
    (P P' : QuenchedPathLaws d) (z : Vec d) (hz : z ∈ U)
    (hP : P (z, ω) = r.pathLaw z) (hP' : P' (z, ω') = r'.pathLaw z)
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hball : couplingRegion i R z ⊆ U) :
    (Renewal.killedSegmentLaw Δ R i P z ω).map (Diffusion.stopPathAt Δ) =
        (Renewal.killedSegmentLaw Δ R i P' z ω').map (Diffusion.stopPathAt Δ) ∧
      (Renewal.killedBridgeMixture Δ R i P z ω).map (Diffusion.stopPathAt Δ) =
        (Renewal.killedBridgeMixture Δ R i P' z ω').map (Diffusion.stopPathAt Δ) := by
  obtain ⟨hm, hstop⟩ := Diffusion.realization_map_localityStoppedPath_eq hLoc hd Λ₀ hΛ₀
    U hU ω ω' hω hω' lam h0 h1 heq r r' z hz
  have hsegment := Diffusion.map_restrict_stopPathAt_eq_of_stoppedLaw_eq U
    (couplingRegion i R z) hU (isOpen_couplingRegion i R z) hball Δ
    (r.pathLaw z) (r'.pathLaw z) hm hstop
  have hkill : (Renewal.killedSegmentLaw Δ R i P z ω).map (Diffusion.stopPathAt Δ) =
      (Renewal.killedSegmentLaw Δ R i P' z ω').map (Diffusion.stopPathAt Δ) := by
    simpa only [Renewal.killedSegmentLaw, hP, hP'] using hsegment
  exact ⟨hkill, map_endpoint_reweighted_eq_of_map_stopPathAt_eq Δ _ _ _ hkill⟩


end EinsteinRelation.Regeneration
