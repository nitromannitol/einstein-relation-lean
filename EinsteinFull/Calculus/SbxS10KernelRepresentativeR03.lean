import EinsteinFull.Calculus.SunaS6KilledEveryStartLocality
import EinsteinFull.Calculus.SbxS4KilledSpectralR01
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3UniformCrossHeat
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

open MeasureTheory Filter ProbabilityTheory EinsteinRelation.Diffusion
open EinsteinRelation EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS2Boundary
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped NNReal ENNReal Topology CompactlySupported InnerProductSpace

namespace EinsteinFull

/-- Positive-time killed endpoint tests of the actual realization are continuous
at every interior starting point. The proof uses its actual short-time exit bound. -/
theorem s10_actual_killed_test_continuousOn
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : BoundedContinuousFunction (Vec d) ℝ) :
    ContinuousOn (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) U := by
  apply s6_supplied_killed_endpoint_continuousOn_of_uniform_exit hd L hL ω hω
    lam h0 h1 G U hU t f
  exact fun x hx ε hε =>
    s1_supplied_killed_exit_probability_locally_uniform hd L hL ω hω lam h0 h1
      G U hU x hx ε hε

/-- An equality of the physical and native spectral L² evolutions on a given
bounded continuous datum implies equality of their test actions at every interior
start. The only identification premise is the L² representative equality; no
pointwise kernel identity or killed-row continuity is assumed. -/
theorem s10_killed_test_eq_spectral_of_ae_operator_identification
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (hs : Tendsto s.eigenvalue atTop atTop)
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (f : BoundedContinuousFunction (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (g : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (hg : (g : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] f)
    (hop : (fun x => gmpKilledL2Operator G (sourceBall 0 R)
      (dirichletBall (d := d) R).isOpen t F x) =ᵐ[dirichletVolume ρ R]
      (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t g x)) :
    ∀ x ∈ sourceBall 0 R,
      (∫ y, f y ∂gmpKilledEndpointKernel G (sourceBall 0 R)
        (dirichletBall (d := d) R).isOpen t x) =
      ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R := by
  let U := sourceBall (0 : Vec d) R
  let hU : IsOpen U := (dirichletBall (d := d) R).isOpen
  have hac : dirichletVolume ρ R ≪ physicalReversibleMeasure ω hd lam := by
    apply (withDensity_absolutelyContinuous _ _).trans
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (Blueprint.gmpVolume_absolutelyContinuous_physical hd ω lam)
  have hactual := (hac.ae_eq (gmpKilledL2_ae_eq G U hU t F))
  have hrow := hac (ae_ae_gmpKilledEndpointKernel_of_ae G U hU t hf)
  have hspec := spectral_heat_operator_ae_kernel_action hd hκ hell hR s t ht g
  have heq : ∀ᵐ x ∂dirichletVolume ρ R,
      (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =
      ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R := by
    filter_upwards [hactual, hrow, hop, hspec] with x ha hr ho hs'
    have hi : (∫ y, F y ∂gmpKilledEndpointKernel G U hU t x) =
        ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x := integral_congr_ae hr
    have hj : (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * g y ∂dirichletVolume ρ R) =
        ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [hg] with y hy
      rw [hy]
    exact hi.symm.trans (ha.symm.trans (ho.trans (hs'.trans hj)))
  have hc : ContinuousOn (fun x =>
      (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) -
      ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R) U := by
    apply (s10_actual_killed_test_continuousOn hd L hL ω hω lam h0 h1 G U hU t f).sub
    apply (spectral_heat_action_continuousOn hd hκ hell hR s hs t ht g).congr
    intro x hx
    apply integral_congr_ae
    filter_upwards [hg] with y hy
    rw [hy]
  have hb := dirichletVolume_continuousOn_ae_bounds hκ hell R hc
    (heq.mono fun x hx => by rw [hx, sub_self])
    (heq.mono fun x hx => by rw [hx, sub_self])
  intro x hx
  have hx' := hb x hx
  exact sub_eq_zero.mp (le_antisymm hx'.2 hx'.1)

/-- At a fixed positive time, the actual killed rows have one jointly measurable
reversible density. Its source normalization uses the density at the starting
point, and represents the actual Lebesgue endpoint law at every start. -/
theorem s10_actual_killed_joint_source_normalization
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t) :
    ∃ k : Vec d → Vec d → ℝ,
      Measurable (Function.uncurry k) ∧
      (∀ y x, 0 ≤ k y x) ∧
      (∀ y, gmpKilledEndpointKernel G U hU t y =
        (physicalReversibleMeasure ω hd lam).withDensity
          (fun x => ENNReal.ofReal (k y x))) ∧
      ∀ y, gmpKilledEndpointKernel G U hU t y =
        volume.withDensity (fun x => ENNReal.ofReal
          ((s4PhysicalRho hd ω lam x / s4PhysicalRho hd ω lam y) *
            (s4PhysicalRho hd ω lam y * k y x))) := by
  obtain ⟨k, hk, hn, hr, _⟩ :=
    s4_actual_killed_joint_reversible_density_balance G U hU t ht
  refine ⟨k, hk, hn, hr, ?_⟩
  intro y
  rw [hr y]
  exact s4_reversible_kernel_density_transfer hd ω lam y (k y)
    (hk.comp (measurable_const.prodMk measurable_id))

/-- If the actual killed evolution and a variational Dirichlet spectrum agree
on compactly supported test data in their respective L² realizations, then the
spectral density represents the actual killed row at every interior start. -/
theorem s10_actual_killed_row_eq_spectral_of_ae_operator_identification
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (hop : ∀ (f : Vec d →C_c ℝ)
      (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
      (g : Lp ℝ 2 (dirichletVolume ρ R)),
      (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f →
      (g : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] f →
      (fun x => gmpKilledL2Operator G (sourceBall 0 R)
        (dirichletBall (d := d) R).isOpen t F x) =ᵐ[dirichletVolume ρ R]
      (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t g x)) :
    ∀ x ∈ sourceBall 0 R,
      gmpKilledEndpointKernel G (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t x =
      (dirichletVolume ρ R).withDensity (fun y => ENNReal.ofReal
        (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
          s.eigenfunction n x * s.eigenfunction n y)) := by
  intro x hx
  let row : Vec d → ℝ := fun y => ∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
    s.eigenfunction n x * s.eigenfunction n y
  let ν := dirichletVolume ρ R
  letI : IsFiniteMeasure ν :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hr : MemLp row 2 ν := spectral_heat_row_memLp hd hκ hell hR s t ht x hx
  have hi : Integrable row ν := hr.integrable (by norm_num)
  letI : IsFiniteMeasure (ν.withDensity (fun y => ENNReal.ofReal (row y))) :=
    isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  letI := isFiniteKernel_gmpKilledEndpointKernel G (sourceBall 0 R)
    (dirichletBall (d := d) R).isOpen t
  have hn : ∀ᵐ y ∂ν, 0 ≤ row y := by
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)] with y hy
    exact (spectral_heat_kernel_nonneg_of_variational hd hκ hell R hR s hs u hb hv).2
      t ht x hx y hy
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf : MemLp (f : Vec d → ℝ) 2 (physicalReversibleMeasure ω hd lam) :=
    Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f f.continuous f.hasCompactSupport
  have hg : MemLp (f : Vec d → ℝ) 2 ν :=
    (f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport ν).mono_exponent le_top
  have ha := s10_killed_test_eq_spectral_of_ae_operator_identification hd L hL ω hω
    lam h0 h1 G hκ hR hell s hs t ht f.toBoundedContinuousFunction
      (hf.toLp f) (hg.toLp f) hf.coeFn_toLp hg.coeFn_toLp
      (hop f (hf.toLp f) (hg.toLp f) hf.coeFn_toLp hg.coeFn_toLp) x hx
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hr.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ y, row y * f y ∂ν := ha
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hn] with y hy
      simp [ENNReal.toReal_ofReal hy, smul_eq_mul]

/-- The same spectral series is jointly continuous at positive time and
represents every actual interior-start row, provided the two L² evolutions
agree on compactly supported data at every positive time. -/
theorem s10_actual_killed_jointly_continuous_spectral_representative_of_ae_operator_identification
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (hop : ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ (f : Vec d →C_c ℝ)
      (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
      (g : Lp ℝ 2 (dirichletVolume ρ R)),
      (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f →
      (g : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] f →
      (fun x => gmpKilledL2Operator G (sourceBall 0 R)
        (dirichletBall (d := d) R).isOpen t F x) =ᵐ[dirichletVolume ρ R]
      (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t g x)) :
    ContinuousOn (fun z : ℝ × Vec d × Vec d =>
      ∑' n, Real.exp (-s.eigenvalue n * z.1) *
        s.eigenfunction n z.2.1 * s.eigenfunction n z.2.2)
      {z | 0 < z.1 ∧ z.2.1 ∈ sourceBall 0 R ∧ z.2.2 ∈ sourceBall 0 R} ∧
    ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
      gmpKilledEndpointKernel G (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t x =
      (dirichletVolume ρ R).withDensity (fun y => ENNReal.ofReal
        (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
          s.eigenfunction n x * s.eigenfunction n y)) := by
  refine ⟨spectral_heat_continuousOn hd hκ hell hR s hs, ?_⟩
  intro t ht
  exact s10_actual_killed_row_eq_spectral_of_ae_operator_identification
    hd L hL ω hω lam h0 h1 G hκ hR hell s hs u hb hv t ht (hop t ht)

/-- Source normalization of the native spectral row. The endpoint density is
with respect to Lebesgue measure restricted to the ball. -/
theorem s10_spectral_row_source_normalization
    {d : ℕ} (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (hs : Tendsto s.eigenvalue atTop atTop)
    (t : ℝ) (ht : 0 < t) (y : Vec d) (hy : y ∈ sourceBall 0 R) :
    (dirichletVolume ρ R).withDensity (fun x => ENNReal.ofReal
      (∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n y * s.eigenfunction n x)) =
    (volume.restrict (sourceBall 0 R)).withDensity (fun x => ENNReal.ofReal
      ((ρ x / ρ y) * (ρ y * (∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n y * s.eigenfunction n x)))) := by
  let k : Vec d → ℝ := fun x => ∑' n, Real.exp (-s.eigenvalue n * t) *
    s.eigenfunction n y * s.eigenfunction n x
  have hk : ContinuousOn k (sourceBall 0 R) := by
    apply (spectral_heat_continuousOn hd hκ hell hR s hs).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
    intro x hx
    exact ⟨ht, hy, hx⟩
  have hkm : AEMeasurable k (volume.restrict (sourceBall 0 R)) :=
    hk.aemeasurable (dirichletBall (d := d) R).isOpen.measurableSet
  change ((volume.restrict (sourceBall 0 R)).withDensity
    (fun x => ENNReal.ofReal (ρ x))).withDensity (fun x => ENNReal.ofReal (k x)) = _
  rw [← withDensity_mul₀ hell.1.aemeasurable.ennreal_ofReal hkm.ennreal_ofReal]
  apply congrArg (Measure.withDensity (volume.restrict (sourceBall 0 R)))
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (le_trans hκ.le (hell.2.2 x).1)]
  congr 1
  have hyρ : ρ y ≠ 0 := (lt_of_lt_of_le hκ (hell.2.2 y).1).ne'
  field_simp
  simp only [k, neg_mul]

/-- The actual killed endpoint row has the source-normalized spectral density
at every interior start, under the L² evolution identification. -/
theorem s10_actual_killed_row_source_normalization_of_ae_operator_identification
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (hop : ∀ (f : Vec d →C_c ℝ)
      (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
      (g : Lp ℝ 2 (dirichletVolume ρ R)),
      (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f →
      (g : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] f →
      (fun x => gmpKilledL2Operator G (sourceBall 0 R)
        (dirichletBall (d := d) R).isOpen t F x) =ᵐ[dirichletVolume ρ R]
      (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t g x)) :
    ∀ y ∈ sourceBall 0 R,
      gmpKilledEndpointKernel G (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t y =
      (volume.restrict (sourceBall 0 R)).withDensity (fun x => ENNReal.ofReal
        ((ρ x / ρ y) * (ρ y * (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
          s.eigenfunction n y * s.eigenfunction n x)))) := by
  intro y hy
  rw [s10_actual_killed_row_eq_spectral_of_ae_operator_identification
    hd L hL ω hω lam h0 h1 G hκ hR hell s hs u hb hv t ht hop y hy]
  exact s10_spectral_row_source_normalization hd hκ hR hell s hs t ht y hy

/-- The source-normalized native heat kernel is continuous up to the
boundary in the endpoint variable for every fixed interior source. -/
theorem s10_spectral_source_kernel_continuousOn
    {d : ℕ} (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (hs : Tendsto s.eigenvalue atTop atTop)
    (y : Vec d) (hy : y ∈ sourceBall 0 R) :
    ContinuousOn (fun z : ℝ × Vec d => ρ y *
      (∑' n, Real.exp (-s.eigenvalue n * z.1) *
        s.eigenfunction n y * s.eigenfunction n z.2))
      (Set.Ioi 0 ×ˢ closure (sourceBall 0 R)) := by
  apply (continuousOn_const.mul
    (spectral_heat_row_continuousOn_closedBall hd hκ hell hR s hs y hy)).congr
  intro z hz
  change ρ y * (∑' n, Real.exp (-s.eigenvalue n * z.1) *
    s.eigenfunction n y * s.eigenfunction n z.2) =
    ρ y * (∑' n, Real.exp (-s.eigenvalue n * z.1) *
      s.eigenfunction n z.2 * s.eigenfunction n y)
  congr 1
  apply tsum_congr
  intro n
  ring

end EinsteinFull
