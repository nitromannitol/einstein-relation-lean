import EinsteinRelation.Correctors.ParabolicTemporalRegularization
import EinsteinRelation.Correctors.RegularizedCoefficientEnergyEndpoint
import EinsteinRelation.Correctors.OneSidedTimeMollifier

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Actual one-sided temporal smoothing of a parabolic solution satisfies the
uniform local endpoint gradient energy estimate. Source: `paper/main.tex:798–806`. -/
theorem parabolicSolution_regularized_gradient_endpoint {d : ℕ} {K c e a b ε : ℝ}
    (hK : 0 < K) (hab : a < b) (ha : c+ε ≤ a) (hb : b ≤ e)
    {A : Coefficient d K} {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo c e) U u G)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ Set.Ioo 0 ε)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) (hχb : ∀ x, |χ x| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hχD : ∀ x, euclideanNorm (gradient χ x) ≤ L) :
    ∃ g : ℝ → Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U),
      Continuous g ∧
      (∀ t i, (fun x => g t x i) =ᵐ[volume.restrict U]
        fun x => ∫ s in Set.Ioo c e, ρ (t-s) * G (s,x) i) ∧
      HasWeakGradient U (fun x => ∫ s in Set.Ioo c e, ρ (b-s) * u (s,x))
        (fun x => (g b x).ofLp) ∧
      (∫ x in U, χ x^2 * euclideanSq (g b x).ofLp) ≤
        (K/(b-a) + 2*K^2*L^2) * (∫ t in a..b, ‖g t‖^2) := by
  obtain ⟨f,f',g,g',hf,hg,hfd,hgd,hw,hw',hdiv⟩ :=
    parabolicSolution_temporal_regularization hK hsol hρ hρc
  refine ⟨g,continuous_iff_continuousAt.mpr (fun t => (hgd t).continuousAt),hg,?_,?_⟩
  · intro i
    exact (hw b i).congr_ae (hf b) Filter.EventuallyEq.rfl
  · exact regularized_coefficient_gradient_endpoint_le hK hab A hU hχ hχb hL hχD
      g g' hgd (fun t => f' t) (fun t _ => Lp.memLp (f' t))
      (fun t _ => hw' t) (fun t ht => hdiv t
        (tsupport_time_kernel_subset hρs (ha.trans ht.1.le) (ht.2.le.trans hb)))

end EinsteinRelation.Correctors
