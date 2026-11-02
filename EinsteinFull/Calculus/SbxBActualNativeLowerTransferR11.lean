import EinsteinFull.Calculus.SbxBEveryStartNativeRowsR07

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP

/-- A pointwise native lower bound transfers to every endpoint event through
the actual killed row, with the endpoint and starting weights in their native order. -/
theorem b_actual_native_setwise_lower_of_pointwise
    (c m : ℝ) (hc : 0 < c) (hm : 0 < m)
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (y : Vec d) (hy : y ∈ sourceBall 0 R)
    (V : Set (Vec d)) (hV : MeasurableSet V) (hsub : V ⊆ sourceBall 0 R)
    (hlower : ∀ x ∈ V, c * Real.rpow (t : ℝ) (-(d : ℝ)/2) ≤ K t x y / ρ y)
    (hrho : ∀ x ∈ V, m ≤ ρ x) :
    ENNReal.ofReal (m * c * Real.rpow (t : ℝ) (-(d : ℝ)/2)) • volume.restrict V ≤
      gmpKilledEndpointKernel r (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t y := by
  rw [b_every_start_actual_killed_row_supplied_kernel r hκ hR hell hcoeff hK t ht y hy,
    ← withDensity_const, ← withDensity_indicator hV]
  apply withDensity_mono
  filter_upwards with x
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub hx)]
    apply ENNReal.ofReal_le_ofReal
    have hp : 0 ≤ c * Real.rpow (t : ℝ) (-(d : ℝ)/2) :=
      (mul_pos hc (Real.rpow_pos_of_pos ht _)).le
    have hmul := mul_le_mul (hrho x hx) (hlower x hx) hp (hm.le.trans (hrho x hx))
    calc
      m * c * Real.rpow (t : ℝ) (-(d : ℝ)/2) =
          m * (c * Real.rpow (t : ℝ) (-(d : ℝ)/2)) := by ring
      _ ≤ ρ x * (K t x y / ρ y) := hmul
      _ = (ρ x / ρ y) * K t x y := by ring
  · simp [hx]

end EinsteinFull

