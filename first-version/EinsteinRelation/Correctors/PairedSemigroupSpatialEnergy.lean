import EinsteinRelation.Correctors.ParabolicSpatialEnergyPrimitive
import EinsteinRelation.Correctors.ParabolicWeightedEnergyContinuity

/-! # Endpoint energy identities for the actual paired semigroup

Source: `paper/main.tex:814–840`. The continuous scalar representatives
supply the energy continuity at every positive time. The endpoint identity
then follows from the weak equation, with no classical temporal derivative
or energy primitive assumed.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The literal weighted energy of two actual semigroup solutions is
continuous at every positive time. Source: `paper/main.tex:824–840`. -/
theorem paired_semigroupSolutions_continuous_spatial_energy
    {d : ℕ} {K : ℝ} {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hUc : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)]
    {ψ : Vec d → ℝ} (hψ : MemLp ψ ∞ (volume.restrict U)) :
    ContinuousOn (fun t => ∫ x in U, ψ x^2 * (u₁ (t,x) - u₂ (t,x))^2)
      (Set.Ioi 0) := by
  obtain ⟨v₁, hv₁, hr₁⟩ := semigroupSolution_exists_continuous_local_L2 h₁ hUc
  obtain ⟨v₂, hv₂, hr₂⟩ := semigroupSolution_exists_continuous_local_L2 h₂ hUc
  apply (continuousOn_weighted_square_integral_of_L2 hψ (hv₁.sub hv₂)).congr
  intro t ht
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (v₁ t) (v₂ t), hr₁ t ht, hr₂ t ht] with x hx hx₁ hx₂
  simp only [Pi.sub_apply, hx₁, hx₂] at hx
  rw [hx]

/-- On a positive-time window the paired weak PDE gives its actual
spatial energy primitive. Scalar continuity is derived from the semigroup
representatives, rather than assumed as an energy premise.
Source: `paper/main.tex:814–840`. -/
theorem paired_semigroupSolutions_spatial_energy_integral_eq_sub
    {d : ℕ} {K a b : ℝ} (hK : 0 < K) (ha : 0 < a) (hab : a < b)
    {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)] (hA : Set.EqOn A₁ A₂ U)
    (hp₁ : IsParabolicSolution A₁ (Set.Ioo a b) U u₁ G₁)
    (hp₂ : IsParabolicSolution A₂ (Set.Ioo a b) U u₂ G₂)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U) :
    (∫ t in a..b,
      -2 * ∫ x in U, dot ((A₁ x).mulVec (G₁ (t,x) - G₂ (t,x))) (fun j =>
        ψ x^2 * (G₁ (t,x) - G₂ (t,x)) j +
          2 * ψ x * (u₁ (t,x) - u₂ (t,x)) * coordinateDerivative j ψ x)) =
      (∫ x in U, ψ x^2 * (u₁ (b,x) - u₂ (b,x))^2) -
        (∫ x in U, ψ x^2 * (u₁ (a,x) - u₂ (a,x))^2) := by
  rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
  apply parabolicSolution_spatial_energy_integral_eq_sub hK hab hU
    (paired_parabolicSolution hK measurableSet_Ioo hU.measurableSet hA hp₁ hp₂)
    hψ hψc hψs
  exact (paired_semigroupSolutions_continuous_spatial_energy h₁ h₂ hUc
    (hψ.continuous.memLp_top_of_hasCompactSupport hψc _)).mono (by
      intro t ht
      exact ha.trans_le ht.1)

end EinsteinRelation.Correctors
