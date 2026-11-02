import EinsteinFull.Calculus.SbxBActualNativeEvolutionR06
import EinsteinFull.Calculus.SbxBNativeSpectralCompactnessR06
import EinsteinFull.Calculus.SbxS10KernelRepresentativeR03

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace CompactlySupported

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat

noncomputable section

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
  {ω : FieldPair d} {hω : IsRegular L ω}
  {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}

/-- The actual killed row is the weighted spectral row at every interior
start and positive time. The spectral escape hypothesis concerns this spectrum. -/
theorem b_every_start_actual_killed_spectral_row
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (s : DirichletSpectralResolution ρ α R) (hs : Tendsto s.eigenvalue atTop atTop)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (y : Vec d) (hy : y ∈ sourceBall 0 R) :
    gmpKilledEndpointKernel r (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t y =
      (dirichletVolume ρ R).withDensity (fun x => ENNReal.ofReal
        (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
          s.eigenfunction n y * s.eigenfunction n x)) := by
  classical
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  choose u hu hv using fun n =>
    Calculus.c16_supplied_eigenfunction_dirichletEquation_all_dimensions hκ hR hell s n
  have hb (n : ℕ) : spectralHeatBasis s n = J (u n) := by
    have hs' : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) := by
      exact congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
    rw [hs']
    apply Lp.ext
    exact (s.square_integrable n).coeFn_toLp.trans (hu n).symm
  apply s10_actual_killed_row_eq_spectral_of_ae_operator_identification
    hd L hL ω hω lam h0 h1 r hκ hR hell s hs u hb hv t ht
  intro f F g hF hg
  exact b_actual_killed_l2_eq_spectral_on_compact_tests r hκ hR hell hcoeff s t f F g hF hg
  exact hy

/-- With the spectrum carried by the supplied source kernel, the actual
endpoint law has the source-normalized Lebesgue density at every interior start. -/
theorem b_every_start_actual_killed_row_of_supplied_spectral_kernel
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (hs : Tendsto (Classical.choose hK.2).eigenvalue atTop atTop)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (y : Vec d) (hy : y ∈ sourceBall 0 R) :
    gmpKilledEndpointKernel r (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t y =
      volume.withDensity ((sourceBall (0 : Vec d) R).indicator (fun x => ENNReal.ofReal
        ((ρ x / ρ y) * K (t : ℝ) x y))) := by
  classical
  let s := Classical.choose hK.2
  have hspec := Classical.choose_spec hK.2
  have hB : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  rw [withDensity_indicator hB]
  rw [b_every_start_actual_killed_spectral_row r hκ hR hell hcoeff s hs t ht y hy,
    s10_spectral_row_source_normalization hd hκ hR hell s hs t ht y hy]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet] with x hx
  have hswap : (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n y * s.eigenfunction n x) =
      ∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y :=
    tsum_congr (fun _ => by ring)
  rw [hswap, (hspec (t : ℝ) ht x hx y hy).2]

/-- Every compact continuous test has the action of the exact normalized
source row at every interior starting point. -/
theorem b_every_start_actual_killed_compact_test_action
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (hs : Tendsto (Classical.choose hK.2).eigenvalue atTop atTop)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (y : Vec d) (hy : y ∈ sourceBall 0 R)
    (f : Vec d →C_c ℝ) :
    (∫ x, f x ∂gmpKilledEndpointKernel r (sourceBall 0 R)
      (dirichletBall (d := d) R).isOpen t y) =
    ∫ x, f x ∂(volume.withDensity ((sourceBall (0 : Vec d) R).indicator
      (fun x => ENNReal.ofReal ((ρ x / ρ y) * K (t : ℝ) x y))) : Measure (Vec d)) := by
  rw [b_every_start_actual_killed_row_of_supplied_spectral_kernel
    r hκ hR hell hcoeff hK hs t ht y hy]


/-- The compact-test action as an ordinary Lebesgue integral on the ball. -/
theorem b_every_start_actual_killed_compact_test_lebesgue_action
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (hs : Tendsto (Classical.choose hK.2).eigenvalue atTop atTop)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (y : Vec d) (hy : y ∈ sourceBall 0 R)
    (f : Vec d →C_c ℝ) :
    (∫ x, f x ∂gmpKilledEndpointKernel r (sourceBall 0 R)
      (dirichletBall (d := d) R).isOpen t y) =
    ∫ x in sourceBall (0 : Vec d) R, ((ρ x / ρ y) * K (t : ℝ) x y) * f x := by
  have hB : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hk : ContinuousOn (fun x => K (t : ℝ) x y) (sourceBall (0 : Vec d) R) := by
    apply ((hK.1 y hy).1).comp (continuous_const.prodMk continuous_id).continuousOn
    intro x hx
    exact ⟨ht, subset_closure hx⟩
  have hm : AEMeasurable (fun x => (ρ x / ρ y) * K (t : ℝ) x y)
      (volume.restrict (sourceBall (0 : Vec d) R)) :=
    (hell.1.aemeasurable.div_const (ρ y)).mul (hk.aemeasurable hB)
  rw [b_every_start_actual_killed_row_of_supplied_spectral_kernel
    r hκ hR hell hcoeff hK hs t ht y hy, withDensity_indicator hB,
    integral_withDensity_eq_integral_toReal_smul₀ hm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hB] with x hx
  have hnonneg : 0 ≤ (ρ x / ρ y) * K (t : ℝ) x y :=
    mul_nonneg (div_nonneg (hκ.le.trans (hell.2.2 x).1)
      (hκ.le.trans (hell.2.2 y).1)) ((hK.1 y hy).2.1 (t : ℝ) ht x hx)
  simp only [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]


/-- One jointly continuous spectral representative works at all positive times
and every interior start. -/
theorem b_every_start_actual_killed_joint_spectral_rows
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (s : DirichletSpectralResolution ρ α R) (hs : Tendsto s.eigenvalue atTop atTop) :
    ContinuousOn (fun z : ℝ × Vec d × Vec d =>
      ∑' n, Real.exp (-s.eigenvalue n * z.1) *
        s.eigenfunction n z.2.1 * s.eigenfunction n z.2.2)
      {z | 0 < z.1 ∧ z.2.1 ∈ sourceBall 0 R ∧ z.2.2 ∈ sourceBall 0 R} ∧
    ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ y ∈ sourceBall 0 R,
      gmpKilledEndpointKernel r (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t y =
        (dirichletVolume ρ R).withDensity (fun x => ENNReal.ofReal
          (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
            s.eigenfunction n y * s.eigenfunction n x)) := by
  refine ⟨spectral_heat_continuousOn hd hκ hell hR s hs, ?_⟩
  intro t ht y hy
  exact b_every_start_actual_killed_spectral_row r hκ hR hell hcoeff s hs t ht y hy


/-- The actual endpoint rows for a supplied native kernel, with spectral
escape proved from ellipticity for its chosen resolution. -/
theorem b_every_start_actual_killed_row_supplied_kernel
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G) :
    ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ y ∈ sourceBall 0 R,
      gmpKilledEndpointKernel r (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t y =
        volume.withDensity ((sourceBall (0 : Vec d) R).indicator (fun x => ENNReal.ofReal
          ((ρ x / ρ y) * K (t : ℝ) x y))) := by
  intro t ht y hy
  exact b_every_start_actual_killed_row_of_supplied_spectral_kernel r hκ hR hell hcoeff hK
    (Calculus.br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell (Classical.choose hK.2))
    t ht y hy

/-- Compact continuous tests act by the supplied native kernel's exact
Lebesgue endpoint density, with no spectral-growth premise. -/
theorem b_every_start_actual_killed_supplied_kernel_test_action
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (y : Vec d) (hy : y ∈ sourceBall 0 R)
    (f : Vec d →C_c ℝ) :
    (∫ x, f x ∂gmpKilledEndpointKernel r (sourceBall 0 R)
      (dirichletBall (d := d) R).isOpen t y) =
    ∫ x in sourceBall (0 : Vec d) R, ((ρ x / ρ y) * K (t : ℝ) x y) * f x := by
  exact b_every_start_actual_killed_compact_test_lebesgue_action r hκ hR hell hcoeff hK
    (Calculus.br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell (Classical.choose hK.2))
    t ht y hy f

#print axioms b_every_start_actual_killed_spectral_row
#print axioms b_every_start_actual_killed_row_of_supplied_spectral_kernel
#print axioms b_every_start_actual_killed_compact_test_action
#print axioms b_every_start_actual_killed_compact_test_lebesgue_action
#print axioms b_every_start_actual_killed_joint_spectral_rows
#print axioms b_every_start_actual_killed_row_supplied_kernel
#print axioms b_every_start_actual_killed_supplied_kernel_test_action

end
end EinsteinFull
