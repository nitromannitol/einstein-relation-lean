import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.Calculus.GeneratorMeasurability
import Mathlib.MeasureTheory.Measure.Prod

/-! # Spatial null sets along actual continuous diffusion paths

Source `paper/main.tex:61–80,194–217,240–255` and the weak diffusion construction
cited in GMP Section 7: a spatial representative is irrelevant to time integrals
only after positive-time endpoint absolute continuity is used with Fubini.
This module proves that measure-theoretic bridge for the actual Path carrier,
then consumes it in compensatedTest and physical environment differentiability.

Endpoint absolute continuity and probability are explicit INTERNAL inputs here.
No diffusion construction, weak generator identification, environmental renewal,
occupation estimate or external statement is assumed or proved by this module.
-/

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace EinsteinRelation

/-- A spatial Lebesgue null set is avoided for almost every positive time on almost every
actual continuous path, if every strictly positive one-time marginal is absolutely continuous.
The starting position is deliberately excluded; it need not have a density. -/
theorem ae_ae_path_avoids_null {d : ℕ} (P : Measure (Path d)) [SFinite P]
    (hP : ∀ t : ℝ≥0, 0 < t → P.map (pathPosition t) ≪ (volume : Measure (Vec d)))
    {N : Set (Vec d)} (hN : MeasurableSet N) (hnull : volume N = 0) :
    ∀ᵐ γ ∂P, ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), γ t.toNNReal ∉ N := by
  have heval : Measurable (fun z : ℝ × Path d => z.2 z.1.toNNReal) := by
    exact (continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp continuous_fst))).measurable
  apply (ae_ae_comm (hN.preimage heval).compl).mp
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
  have hn : ∀ᵐ x ∂P.map (pathPosition t.toNNReal), x ∉ N :=
    ae_iff.mpr (by simpa using hP t.toNNReal ht' hnull)
  exact ae_of_ae_map (measurable_pathPosition t.toNNReal).aemeasurable hn

/-- Transfer any spatial full-measure property to almost every positive path time.
A measurable null cover handles properties which are not themselves measurable. -/
theorem ae_ae_path_of_ae {d : ℕ} (P : Measure (Path d)) [SFinite P]
    (hP : ∀ t : ℝ≥0, 0 < t → P.map (pathPosition t) ≪ (volume : Measure (Vec d)))
    {p : Vec d → Prop} (hp : ∀ᵐ x ∂(volume : Measure (Vec d)), p x) :
    ∀ᵐ γ ∂P, ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), p (γ t.toNNReal) := by
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  filter_upwards [ae_ae_path_avoids_null P hP hN hnull] with γ hγ
  filter_upwards [hγ] with t ht
  by_contra hnot
  exact ht (hsub hnot)

/-- Spatial almost-everywhere changes of any real function are invisible at almost every
positive path time. No measurability of the two representatives is required: the exceptional
set is covered by a measurable spatial null set before applying Fubini. -/
theorem ae_ae_path_comp_congr {d : ℕ} (P : Measure (Path d)) [SFinite P]
    (hP : ∀ t : ℝ≥0, 0 < t → P.map (pathPosition t) ≪ (volume : Measure (Vec d)))
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume] g) :
    ∀ᵐ γ ∂P, (fun t : ℝ => f (γ t.toNNReal)) =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ => g (γ t.toNNReal)) := by
  exact ae_ae_path_of_ae P hP hfg

/-- Actual finite-time generator integrals and their interval integrability are invariant
under changes on spatial null sets. One path exceptional set works for EVERY terminal time. -/
theorem ae_path_intervalIntegral_comp_congr {d : ℕ} (P : Measure (Path d)) [SFinite P]
    (hP : ∀ t : ℝ≥0, 0 < t → P.map (pathPosition t) ≪ (volume : Measure (Vec d)))
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume] g) :
    ∀ᵐ γ ∂P, ∀ T : ℝ≥0,
      (∫ t in (0 : ℝ)..(T : ℝ), f (γ t.toNNReal)) =
        (∫ t in (0 : ℝ)..(T : ℝ), g (γ t.toNNReal)) ∧
      (IntervalIntegrable (fun t : ℝ => f (γ t.toNNReal)) volume 0 (T : ℝ) ↔
        IntervalIntegrable (fun t : ℝ => g (γ t.toNNReal)) volume 0 (T : ℝ)) := by
  filter_upwards [ae_ae_path_comp_congr P hP hfg] with γ hγ
  intro T
  have hT : (fun t : ℝ => f (γ t.toNNReal)) =ᵐ[volume.restrict (Set.uIoc 0 (T : ℝ))]
      (fun t : ℝ => g (γ t.toNNReal)) := by
    rw [Set.uIoc_of_le T.coe_nonneg]
    exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hγ
  exact ⟨intervalIntegral.integral_congr_ae_restrict hT, intervalIntegrable_congr_ae hT⟩

/-- Real consumer for the literal martingale-problem expression, using the source reduced
operator. The identification of a weak generator with this spatial representative remains
an internal prerequisite, rather than an external assumption about this paper's arguments. -/
theorem ae_compensatedTest_reducedGenerator_eq_of_ae {d : ℕ}
    (P : Measure (Path d)) [SFinite P]
    (hP : ∀ t : ℝ≥0, 0 < t → P.map (pathPosition t) ≪ (volume : Measure (Vec d)))
    (i : Fin d) (ω : FieldPair d) (lam : ℝ)
    (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    (hL : L f =ᵐ[volume] reducedGenerator i ω lam f) :
    ∀ᵐ γ ∂P, ∀ T : ℝ≥0,
      compensatedTest L f T γ = compensatedTest (reducedGenerator i ω lam) f T γ := by
  filter_upwards [ae_path_intervalIntegral_comp_congr P hP hL] with γ hγ
  intro T
  simp only [compensatedTest, (hγ T).1]

/-- Actual environment-law consumer: the Lipschitz reduction is differentiable along almost
every path at almost every positive time, for almost every physical environment. The density
and probability properties are explicit INTERNAL inputs until the cited diffusion is realized. -/
theorem EnvironmentLaw.ae_ae_ae_path_differentiableAt_reduction {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (P : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (P (0, ω)))
    (hdensity : ∀ᵐ ω ∂Q.measure, ∀ t : ℝ≥0, 0 < t →
      (P (0, ω)).map (pathPosition t) ≪ (volume : Measure (Vec d))) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂P (0, ω),
      ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        DifferentiableAt ℝ (clockDensity ω) (γ t.toNNReal) ∧
        DifferentiableAt ℝ (reducedCoefficient ω) (γ t.toNNReal) := by
  filter_upwards [Q.ae_ae_differentiableAt_reduction, hprob, hdensity] with ω hω hp hd
  letI : IsProbabilityMeasure (P (0, ω)) := hp
  exact ae_ae_path_of_ae (P (0, ω)) hd hω

end EinsteinRelation
