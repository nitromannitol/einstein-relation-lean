import EinsteinRelation.Correctors.TemporalL2Curves
import EinsteinRelation.Correctors.ParabolicTemporalFlux
import EinsteinRelation.Correctors.ParabolicTemporalWeakEquation
import EinsteinRelation.Calculus.WeakRepresentativeOperations

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Actual temporal regularization simultaneously realizes the scalar solution,
its gradient, and their differentiated autonomous weak equation in L².
Source: `paper/main.tex:798–806`. -/
theorem parabolicSolution_temporal_regularization {d : ℕ} {K a b : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) :
    ∃ f f' : ℝ → Lp ℝ 2 (volume.restrict U),
    ∃ g g' : ℝ → Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U),
      (∀ t, (f t : Vec d → ℝ) =ᵐ[volume.restrict U]
        fun x => ∫ s in Set.Ioo a b, ρ (t-s) * u (s,x)) ∧
      (∀ t i, (fun x => g t x i) =ᵐ[volume.restrict U]
        fun x => ∫ s in Set.Ioo a b, ρ (t-s) * G (s,x) i) ∧
      (∀ t, HasDerivAt f (f' t) t) ∧ (∀ t, HasDerivAt g (g' t) t) ∧
      (∀ t, HasWeakGradient U (f t) (fun x => (g t x).ofLp)) ∧
      (∀ t, HasWeakGradient U (f' t) (fun x => (g' t x).ofLp)) ∧
      (∀ t, tsupport (fun s => ρ (t-s)) ⊆ Set.Ioo a b →
        HasWeakDivergence U (fun x => (A x).mulVec (g t x).ofLp) (f' t)) := by
  let μ := volume.restrict (Set.Ioo a b)
  let ν := volume.restrict U
  have hp : volume.restrict (Set.Ioo a b ×ˢ U) = μ.prod ν := by
    simp only [μ,ν,Measure.volume_eq_prod,Measure.prod_restrict]
  have hu : MemLp u 2 (μ.prod ν) := hp ▸ hsol.1
  have hG i : MemLp (fun z => G z i) 2 (μ.prod ν) :=
    hp ▸ parabolicSolution_gradient_coordinate_memLp hsol i
  obtain ⟨f,f',hf,hf',hfd⟩ := exists_differentiable_temporal_L2_curve μ ν hu hρ hρc
  obtain ⟨g,g',hg,hg',hgd⟩ := exists_differentiable_temporal_vector_L2_curve μ ν hG hρ hρc
  have hc t : HasCompactSupport (fun s => ρ (t-s)) :=
    hρc.comp_homeomorph (Homeomorph.subLeft t)
  have hcd t : HasCompactSupport (fun s => deriv ρ (t-s)) :=
    hρc.deriv.comp_homeomorph (Homeomorph.subLeft t)
  refine ⟨f,f',g,g',hf,hg,hfd,hgd,?_,?_,?_⟩
  · intro t i
    exact (parabolicSolution_temporal_weakGradient hsol
      (hρ.continuous.comp (continuous_const.sub continuous_id)) (hc t) i).congr_ae
      (hf t).symm (hg t i).symm
  · intro t i
    exact (parabolicSolution_temporal_weakGradient hsol
      ((hρ.continuous_deriv (by norm_num)).comp (continuous_const.sub continuous_id))
      (hcd t) i).congr_ae (hf' t).symm (hg' t i).symm
  · intro t hs
    have hη : ContDiff ℝ (⊤ : ℕ∞) (fun s => ρ (t-s)) :=
      hρ.comp (contDiff_const.sub contDiff_id)
    have hder : deriv (fun s => ρ (t-s)) = fun s => -(deriv ρ (t-s)) := by
      funext s
      simpa only [mul_neg_one] using
        (((hρ.differentiable (by norm_num)).differentiableAt.hasDerivAt).comp s
          ((hasDerivAt_id s).const_sub t)).deriv
    have hw := parabolicSolution_temporal_weakDivergence hK hsol hη (hc t) hs
    have hflux := parabolicSolution_temporal_flux_commute hsol
      (hρ.continuous.comp (continuous_const.sub continuous_id)) (hc t)
    apply hw.congr_ae
    · filter_upwards [hflux,ae_all_iff.mpr (hg t)] with x hx hxg
      change (A x).mulVec (fun j => ∫ s in Set.Ioo a b, ρ (t-s) * G (s,x) j) =
        (fun j => ∫ s in Set.Ioo a b, ρ (t-s) * (A x).mulVec (G (s,x)) j) at hx
      rw [← hx]
      congr 1
      exact (funext hxg).symm
    · rw [hder]
      simp only [neg_mul,integral_neg,neg_neg]
      exact (hf' t).symm

end EinsteinRelation.Correctors
