import EinsteinRelation.Correctors.AKMFiniteTimeDivergence

/-! # The initial trace of finite-time source fluxes

Source: `paper/main.tex:808–816`. The actual distributional initial datum
identifies the zero-time limit of the finite-time flux against every
compact spatial test. This limit does not assert convergence of the
integrated gradient itself at time zero.
-/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The finite-time coefficient flux has the actual scalar endpoint
pairings on the entire space. Source: `paper/main.tex:808–816`. -/
theorem akmLocal_semigroup_time_integral_flux_pairing {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest Set.univ ψ) :
    (∫ x, dot ((A x).mulVec (fun j => ∫ t in Set.Ioo a b, G (t,x) j))
      (gradient ψ x)) =
      (∫ x, u (a,x) * ψ x) - (∫ x, u (b,x) * ψ x) := by
  have he := (akmLocal_semigroup_time_integral_divergence hK hsol ha hab).2.2 ψ hψ
  have hui (t : ℝ) (ht : 0 < t) : Integrable (fun x => u (t,x) * ψ x) volume := by
    have hc : Continuous (fun x => u (t,x)) :=
      hsol.1.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨ht, Set.mem_univ _⟩)
    exact (hc.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  simp only [Measure.restrict_univ, sub_mul] at he
  rw [integral_sub (hui b (ha.trans hab)) (hui a ha)] at he
  linarith

/-- The literal finite-time source flux has the source's distributional
initial endpoint, without assuming a time-zero gradient or potential.
Source: `paper/main.tex:808–816`. -/
theorem akmLocal_semigroup_time_integral_flux_initial_trace {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {b : ℝ} (hb : 0 < b)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest Set.univ ψ) :
    Tendsto (fun a => ∫ x,
      dot ((A x).mulVec (fun j => ∫ t in Set.Ioo a b, G (t,x) j)) (gradient ψ x))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (-(∫ x, dot (g x) (gradient ψ x)) - (∫ x, u (b,x) * ψ x))) := by
  have hlim := (hsol.2.2 ψ hψ).sub_const (∫ x, u (b,x) * ψ x)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hb : ∀ᶠ a in 𝓝 (0 : ℝ), a < b).filter_mono nhdsWithin_le_nhds]
    with a ha hab
  exact (akmLocal_semigroup_time_integral_flux_pairing hK hsol ha hab hψ).symm

end EinsteinRelation.Correctors
