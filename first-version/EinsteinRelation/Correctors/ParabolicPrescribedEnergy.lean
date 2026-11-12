import EinsteinRelation.Correctors.ParabolicRegularizedEndpoint
import EinsteinRelation.Correctors.TemporalCurveEnergy
import EinsteinRelation.Correctors.TemporalTestPairingLimit
import EinsteinRelation.Correctors.CutoffEnergyRestriction
import EinsteinRelation.Correctors.GradientLimitRecovery

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A continuous actual parabolic solution has a genuine weak gradient at the
prescribed final time, controlled by its preceding cylinder energy. The proof
uses only temporal regularization and the symmetric autonomous weak equation.
Source: `paper/main.tex:798–806`; AKM Lemma 8.2, pp. 305–307. -/
theorem parabolicSolution_prescribed_gradient_energy {d : ℕ} {K c b : ℝ}
    (hK : 0 < K) (hc : 0 < c) (hcb : c < b)
    {A : Coefficient d K} {U V : Set (Vec d)} (hU : IsOpen U)
    (hVU : V ⊆ U) (hV : MeasurableSet V)
    [IsFiniteMeasure (volume.restrict U)] [IsFiniteMeasure (volume.restrict V)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ))
    (hsol : IsParabolicSolution A (Set.Ioo c b) U u G)
    (hub : MemLp (fun x => u (b,x)) 2 (volume.restrict V))
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) (hχb : ∀ x, |χ x| ≤ 1)
    (hχV : ∀ x ∈ V, χ x = 1)
    {L : ℝ} (hL : 0 ≤ L) (hχD : ∀ x, euclideanNorm (gradient χ x) ≤ L) :
    ∃ H : Vec d → Vec d, HasWeakGradient V (fun x => u (b,x)) H ∧
      MemLp (fun x => euclideanNorm (H x)) 2 (volume.restrict V) ∧
      (eLpNorm (fun x => euclideanNorm (H x)) 2 (volume.restrict V)).toReal ≤
        Real.sqrt d * Real.sqrt ((2*K/(b-c) + 2*K^2*L^2) *
          (∫ z in Set.Ioo c b ×ˢ U, euclideanSq (G z))) := by
  let a := (c+b)/2
  have hab : a < b := by dsimp only [a]; linarith
  have hca : c < a := by dsimp only [a]; linarith
  obtain ⟨ε,ρ,hε,hεb,hρ,hρc,hρ0,hρ1,hρs⟩ :=
    exists_one_sided_time_approximation (show 0 < (b-c)/4 by linarith)
  have hεa k : c+ε k ≤ a := by
    have he := (hεb k).2
    dsimp only [a]
    linarith
  choose g hgc hgrep hgw hge using fun k =>
    parabolicSolution_regularized_gradient_endpoint hK hab (hεa k) (le_refl b)
      hU hsol (hρ k) (hρc k) (hρs k) hχ hχb hL hχD
  let E := ∫ z in Set.Ioo c b ×ˢ U, euclideanSq (G z)
  let D := K/(b-a) + 2*K^2*L^2
  have hE : 0 ≤ E := integral_nonneg fun z => by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hba : 0 < b-a := sub_pos.mpr hab
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hp : volume.restrict (Set.Ioo c b ×ˢ U) =
      (volume.restrict (Set.Ioo c b)).prod (volume.restrict U) := by
    simp only [Measure.volume_eq_prod,Measure.prod_restrict]
  have hGenergy k : (∫ t in a..b, ‖g k t‖^2) ≤ E := by
    have hh i : MemLp (fun z => G z i) 2
        ((volume.restrict (Set.Ioo c b)).prod (volume.restrict U)) :=
      hp ▸ parabolicSolution_gradient_coordinate_memLp hsol i
    have he := temporal_gradient_curve_energy_le (volume.restrict U) hab.le hh
      (hρ k).continuous (hρc k) (hρ0 k) (hρ1 k) (g k) (hgrep k)
    simpa only [E,hp,euclideanSq,dot,← pow_two] using he
  have hbound k := cutoff_energy_restricted_L2_le hVU hV hχ hχb hχV (g k b)
    (Real.sqrt_nonneg (D*E)) (by
      rw [Real.sq_sqrt (mul_nonneg hD hE)]
      exact (hge k).trans (mul_le_mul_of_nonneg_left (hGenergy k) hD))
  have huV : MemLp u 2 (volume.restrict (Set.Ioo c b ×ˢ V)) :=
    hsol.1.mono_measure (Measure.restrict_mono_set volume
      (Set.prod_mono (Set.Subset.refl _) hVU))
  obtain ⟨H,hw,hHL,hHb⟩ := weakGradient_of_test_pairing_limit V hub
    (fun k x => ∫ s in Set.Ioo c b, ρ k (b-s) * u (s,x))
    (fun k x => (g k b x).ofLp)
    (fun k => hasWeakGradient_mono hVU (hgw k))
    (fun k => (hbound k).1) (Real.sqrt_nonneg (D*E)) (fun k => (hbound k).2)
    (fun i ψ hψ => temporal_test_pairing_tendsto hc hcb hu huV
      (fun k => (hρ k).continuous) hρc hρ0 hρ1 hε
      (fun k => ((hεb k).2).trans (by linarith)) hρs
      (isSpatialTest_coordinateDerivative hψ i))
  refine ⟨H,hw,hHL,?_⟩
  have hDeq : D = 2*K/(b-c) + 2*K^2*L^2 := by
    dsimp only [D,a]
    congr 1
    field_simp
    <;> ring
  simpa only [hDeq,E] using hHb

end EinsteinRelation.Correctors
