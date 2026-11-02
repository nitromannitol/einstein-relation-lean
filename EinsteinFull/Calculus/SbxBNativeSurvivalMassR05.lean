import EinsteinFull.Calculus.C16TubeCutoffQuantitativeTrace
import EinsteinFull.Calculus.C12TubeGaussianAssembly
import EinsteinFull.Calculus.C12TubeGaussianIntegratedTail
import EllipticRegularity.Parabolic.LocalMax.Cutoff

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

private theorem b_sourceBall_eq_euclideanBall {d : ℕ} (x : Vec d) {r : ℝ} (hr : 0 < r) :
    sourceBall x r = PDE.euclideanBall x r := by
  ext y
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
  rfl

/-- An interior cutoff, including its Euclidean gradient bound at the actual scale. -/
theorem b_interior_ball_cutoff {d : ℕ} (x : Vec d) {r R : ℝ} (hr : 0 < r)
    (hinside : sourceBall x (2 * r) ⊆ sourceBall 0 R) :
    ∃ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ ∧
      tsupport φ ⊆ sourceBall x (2 * r) ∧
      (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧
      (∀ y ∈ sourceBall x r, φ y = 1) ∧
      (∀ y, euclideanSq (fun i => fderiv ℝ φ y (unitVector i)) ≤ 1024 / r ^ 2) := by
  have hrr : r < 2 * r := by linarith
  let φ := PDE.canonicalBallCutoff x r (2 * r)
  have hs : tsupport φ ⊆ sourceBall x (2 * r) := by
    rw [b_sourceBall_eq_euclideanBall x (by positivity)]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer hr.le hrr
  refine ⟨φ, ⟨PDE.canonicalBallCutoff_smooth x hr.le hrr,
    PDE.canonicalBallCutoff_hasCompactSupport hr.le hrr, hs.trans hinside⟩,
    hs, ?_, ?_, ?_⟩
  · intro y
    exact ⟨PDE.canonicalBallCutoff_nonneg x r (2 * r) y,
      PDE.canonicalBallCutoff_le_one x r (2 * r) y⟩
  · intro y hy
    rw [b_sourceBall_eq_euclideanBall x hr] at hy
    exact PDE.canonicalBallCutoff_eq_one_on_inner hr.le hrr hy
  · intro y
    have hb := PDE.canonicalBallCutoff_gradient_bound (x₀ := x) hr.le hrr y
    have hs' := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) hb 2
    rw [PDE.vecEuclideanNorm_sq, div_pow] at hs'
    norm_num only at hs'
    have hdiff : 2 * r - r = r := by ring
    rw [hdiff] at hs'
    simpa only [PDE.vecNormSq, PDE.vecDot, euclideanSq, dot,
      PDE.classicalGradient_apply, PDE.basisVec, unitVector] using hs'

/-- The native density normalization cancels against the weighted measure. -/
theorem b_native_weighted_row_eq_mass {d : ℕ} {κ R : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (t : ℝ) (x : Vec d) :
    (∫ y, K t x y / ρ y ∂dirichletVolume ρ R) =
      ∫ y in sourceBall 0 R, K t x y := by
  change (∫ y, K t x y / ρ y ∂(volume.restrict
    (sourceBall (0 : Vec d) R)).withDensity (fun y => ENNReal.ofReal (ρ y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (hκ.le.trans (hell.2.2 y).1), smul_eq_mul]
  have hr : ρ y ≠ 0 := ne_of_gt (hκ.trans_le (hell.2.2 y).1)
  field_simp

/-- Weighted and Lebesgue forms also agree when a cutoff is inserted. -/
theorem b_native_weighted_cutoff_eq {d : ℕ} {κ R : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (φ : Vec d → ℝ) (t : ℝ) (x : Vec d) :
    (∫ y, (K t x y / ρ y) * φ y ∂dirichletVolume ρ R) =
      ∫ y in sourceBall 0 R, K t x y * φ y := by
  change (∫ y, (K t x y / ρ y) * φ y ∂(volume.restrict
    (sourceBall (0 : Vec d) R)).withDensity (fun y => ENNReal.ofReal (ρ y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (hκ.le.trans (hell.2.2 y).1), smul_eq_mul]
  have hr : ρ y ≠ 0 := ne_of_gt (hκ.trans_le (hell.2.2 y).1)
  field_simp

/-- The action of a cutoff bounded by one is bounded by the same native row mass. -/
theorem b_native_cutoff_le_row_mass {d : ℕ} (hd : 2 ≤ d) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφupper : ∀ y, φ y ≤ 1) (t : ℝ) (ht : 0 < t)
    (x : Vec d) (hx : x ∈ sourceBall 0 R) :
    (∫ y in sourceBall 0 R, K t x y * φ y) ≤
      ∫ y in sourceBall 0 R, K t x y := by
  obtain ⟨s, hs⟩ := hK.2
  have : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hball : ∀ᵐ y ∂dirichletVolume ρ R, y ∈ sourceBall (0 : Vec d) R :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)
  have heq : (fun y => ∑' n, Real.exp (-s.eigenvalue n*t) *
      s.eigenfunction n x * s.eigenfunction n y) =ᵐ[dirichletVolume ρ R]
      (fun y => K t x y / ρ y) := by
    filter_upwards [hball] with y hy
    rw [(hs t ht x hx y hy).2]
    have hr : ρ y ≠ 0 := ne_of_gt (hκ.trans_le (hell.2.2 y).1)
    field_simp
    simp only [mul_comm t (s.eigenvalue _)]
  have hrow : MemLp (fun y => K t x y / ρ y) 2 (dirichletVolume ρ R) :=
    (spectral_heat_row_memLp hd hκ hell hR s t ht x hx).ae_eq heq
  have hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  have hcomp : (∫ y, (K t x y / ρ y) * φ y ∂dirichletVolume ρ R) ≤
      ∫ y, K t x y / ρ y ∂dirichletVolume ρ R := by
    apply integral_mono_ae (hrow.integrable_mul hp) (hrow.integrable (by norm_num))
    filter_upwards [hball] with y hy
    have hk : 0 ≤ K t x y / ρ y := div_nonneg ((hK.1 y hy).2.1 t ht x hx)
      (hκ.le.trans (hell.2.2 y).1)
    change (K t x y / ρ y) * φ y ≤ K t x y / ρ y
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hφupper y) hk
  rw [b_native_weighted_cutoff_eq hκ hell K φ t x,
    b_native_weighted_row_eq_mass hκ hell K t x] at hcomp
  exact hcomp

/-- Ellipticity and the Euclidean cutoff bound control the actual Dirichlet energy. -/
theorem b_interior_cutoff_energy_bound {d : ℕ} {κ R r : ℝ} (hκ : 0 < κ)
    (hR : 0 < R) (hr : 0 < r) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (x : Vec d) (φ : Vec d → ℝ)
    (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hs : tsupport φ ⊆ sourceBall x (2 * r))
    (hinside : sourceBall x (2 * r) ⊆ sourceBall 0 R)
    (hg : ∀ y, euclideanSq (fun i => fderiv ℝ φ y (unitVector i)) ≤ 1024 / r ^ 2) :
    (∫ y in sourceBall 0 R,
      dot ((α y).mulVec (fun i => fderiv ℝ φ y (unitVector i)))
        (fun i => fderiv ℝ φ y (unitVector i))) ≤
      (κ⁻¹ * (1024 / r ^ 2)) * (volume (sourceBall x (2 * r))).toReal := by
  let S := sourceBall x (2 * r)
  let v : Vec d → Vec d := fun y i => fderiv ℝ φ y (unitVector i)
  let E : Vec d → ℝ := fun y => dot ((α y).mulVec (v y)) (v y)
  let M : ℝ := κ⁻¹ * (1024 / r ^ 2)
  have hSfin : volume S ≠ ⊤ := by
    dsimp [S]
    rw [b_sourceBall_eq_euclideanBall x (by positivity)]
    exact PDE.volume_euclideanBall_ne_top x (by positivity)
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSfin
  have hSM : MeasurableSet (sourceBall (0 : Vec d) R) := by
    rw [b_sourceBall_eq_euclideanBall 0 hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hEmeas : Measurable E := by
    have hv (i : Fin d) : Measurable (fun y => v y i) :=
      ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
    have ha (i j : Fin d) : Measurable (fun y => α y i j) := by
      letI : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
      letI : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
      exact (((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
        hell.2.1)
    change Measurable (fun y => ∑ i : Fin d, (∑ j : Fin d, α y i j * v y j) * v y i)
    exact Finset.measurable_sum _ fun i _ =>
      (Finset.measurable_sum _ fun j _ => (ha i j).mul (hv j)).mul (hv i)
  have hpoint (y : Vec d) : 0 ≤ E y ∧ E y ≤ M := by
    have hsq : 0 ≤ euclideanSq (v y) := by
      simp only [euclideanSq, dot]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v y i)
    have hq := (hell.2.2 y).2.2.2 (v y)
    change κ * euclideanSq (v y) ≤ dotProduct (v y) ((α y).mulVec (v y)) ∧
      dotProduct (v y) ((α y).mulVec (v y)) ≤ κ⁻¹ * euclideanSq (v y) at hq
    rw [dotProduct_comm] at hq
    change κ * euclideanSq (v y) ≤ E y ∧ E y ≤ κ⁻¹ * euclideanSq (v y) at hq
    refine ⟨(mul_nonneg hκ.le hsq).trans hq.1, ?_⟩
    exact hq.2.trans (mul_le_mul_of_nonneg_left (hg y) (inv_nonneg.mpr hκ.le))
  have hint : Integrable E (volume.restrict S) := by
    apply (integrable_const M).mono' hEmeas.aestronglyMeasurable
    filter_upwards [] with y
    change ‖E y‖ ≤ M
    rw [Real.norm_eq_abs, abs_of_nonneg (hpoint y).1]
    exact (hpoint y).2
  have heq : (∫ y in sourceBall 0 R, E y) = ∫ y in S, E y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSM hinside
    intro y hy
    have hn : y ∉ tsupport φ := fun h => hy.2 (hs h)
    simp [E, v, fderiv_of_notMem_tsupport ℝ hn, dot]
  change (∫ y in sourceBall 0 R, E y) ≤ M * (volume S).toReal
  rw [heq]
  calc
    _ ≤ ∫ _y in S, M := integral_mono_ae hint (integrable_const M)
      (ae_of_all _ fun y => (hpoint y).2)
    _ = _ := by simp [integral_const, Measure.real, smul_eq_mul, mul_comm]

/-- A cutoff chosen from geometry alone has a uniform native spectral trace bound. -/
theorem b_native_interior_cutoff_trace {d : ℕ} {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (x : Vec d)
    (hinside : sourceBall x (2 * r) ⊆ sourceBall 0 R) :
    ∃ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ ∧
      tsupport φ ⊆ sourceBall x (2 * r) ∧
      (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧
      (∀ y ∈ sourceBall x r, φ y = 1) ∧
      ∀ (κ : ℝ), 0 < κ → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G → ∀ t : ℝ, 0 < t →
      (∫ z in sourceBall 0 R,
        ρ z * ((∫ y in sourceBall 0 R, K t z y * φ y) - φ z) ^ 2) ≤
        t * (κ⁻¹ * (1024 / r ^ 2)) * (volume (sourceBall x (2 * r))).toReal := by
  obtain ⟨φ, hφ, hs, hb, hp, hg⟩ := b_interior_ball_cutoff x hr hinside
  refine ⟨φ, hφ, hs, hb, hp, ?_⟩
  intro κ hκ ρ α hell K G hK t ht
  have he := b_interior_cutoff_energy_bound hκ hR hr ρ α hell x φ hφ hs hinside hg
  calc
    _ ≤ t * ∫ z in sourceBall 0 R,
        dot ((α z).mulVec (fun i => fderiv ℝ φ z (unitVector i)))
          (fun i => fderiv ℝ φ z (unitVector i)) :=
        c16_native_cutoff_quantitative_L2_trace hκ hR ρ α hell K G hK φ hφ t ht
    _ ≤ t * ((κ⁻¹ * (1024 / r ^ 2)) * (volume (sourceBall x (2 * r))).toReal) :=
      mul_le_mul_of_nonneg_left he ht.le
    _ = _ := by ring

/-- Chebyshev's inequality for the supplied native spectral cutoff action. -/
theorem b_native_cutoff_error_level {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ) (ht : 0 < t) (ε : ℝ) :
    ε * (dirichletVolume ρ R).real
      {x | ε ≤ ((∫ y in sourceBall 0 R, K t x y * φ y) - φ x) ^ 2} ≤
      t * ∫ x in sourceBall 0 R,
        dot ((α x).mulVec (fun i => fderiv ℝ φ x (unitVector i)))
          (fun i => fderiv ℝ φ x (unitVector i)) := by
  let τ : ℝ≥0 := ⟨t, ht.le⟩
  obtain ⟨s, haction⟩ := c16_supplied_kernel_heat_action_all_dimensions hκ hR hell K G hK φ hφ τ ht
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let f := Blueprint.TubeProbability.SpectralHeat.heatOperator
    (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) τ (hp.toLp φ)
  let e : Vec d → ℝ := fun x => (∫ y in sourceBall 0 R, K t x y * φ y) - φ x
  have hae : ((f - hp.toLp φ : Lp ℝ 2 (dirichletVolume ρ R)) : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] e := by
    filter_upwards [Lp.coeFn_sub f (hp.toLp φ), haction, hp.coeFn_toLp] with x hx hy hz
    rw [hx]
    change f x - (hp.toLp φ) x = _
    rw [hy, hz]
    rfl
  have he : MemLp e 2 (dirichletVolume ρ R) := (Lp.memLp (f - hp.toLp φ)).ae_eq hae
  have hint : Integrable (fun x => (e x)^2) (dirichletVolume ρ R) := by
    simpa only [Real.norm_eq_abs, sq_abs] using he.integrable_norm_pow (by decide : 2 ≠ 0)
  have heq : (∫ x, (e x)^2 ∂dirichletVolume ρ R) =
      ∫ x in sourceBall 0 R, ρ x * (e x)^2 := by
    have h1 : (∫ x, (e x)^2 ∂dirichletVolume ρ R) = ‖f - hp.toLp φ‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hx]
    have h2 := Blueprint.TubeProbability.DimensionLift.dirichletVolume_inner_eq_native
      hκ hell R (f - hp.toLp φ) (f - hp.toLp φ) _ _ hae hae
    rw [real_inner_self_eq_norm_sq] at h2
    rw [h1, h2]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  calc
    _ ≤ ∫ x, (e x)^2 ∂dirichletVolume ρ R :=
      mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => sq_nonneg (e x)) hint ε
    _ = ∫ x in sourceBall 0 R, ρ x * (e x)^2 := heq
    _ ≤ _ := c16_native_cutoff_quantitative_L2_trace hκ hR ρ α hell K G hK φ hφ t ht

/-- Quantitative weighted volume of starting points with native row mass at most one half. -/
theorem b_native_interior_bad_mass_measure {d : ℕ} (hd : 2 ≤ d) {κ R r : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hr : 0 < r)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (x : Vec d) (hinside : sourceBall x (2 * r) ⊆ sourceBall 0 R)
    (t : ℝ) (ht : 0 < t) :
    (dirichletVolume ρ R).real
      {z | z ∈ sourceBall x r ∧ (∫ y in sourceBall 0 R, K t z y) ≤ (1/2 : ℝ)} ≤
      4 * t * (κ⁻¹ * (1024 / r ^ 2)) * (volume (sourceBall x (2 * r))).toReal := by
  obtain ⟨φ, hφ, hs, hb, hp, hg⟩ := b_interior_ball_cutoff x hr hinside
  have he := b_interior_cutoff_energy_bound hκ hR hr ρ α hell x φ hφ hs hinside hg
  let A : Set (Vec d) :=
    {z | z ∈ sourceBall x r ∧ (∫ y in sourceBall 0 R, K t z y) ≤ (1/2 : ℝ)}
  let B : Set (Vec d) :=
    {z | (1/4 : ℝ) ≤ ((∫ y in sourceBall 0 R, K t z y * φ y) - φ z) ^ 2}
  have hinner : sourceBall x r ⊆ sourceBall x (2 * r) := by
    intro z hz
    change euclideanNorm (z - x) < r at hz
    change euclideanNorm (z - x) < 2 * r
    linarith
  have hAB : A ⊆ B := by
    intro z hz
    have hzR : z ∈ sourceBall 0 R := hinside (hinner hz.1)
    have hcomp := b_native_cutoff_le_row_mass hd hκ hR hell K G hK φ hφ
      (fun y => (hb y).2) t ht z hzR
    have hplateau := hp z hz.1
    dsimp [A] at hz
    dsimp [B]
    nlinarith [sq_nonneg ((∫ y in sourceBall 0 R, K t z y * φ y) - φ z + 1/2)]
  have : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hm : (dirichletVolume ρ R).real A ≤ (dirichletVolume ρ R).real B :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hAB)
  have hlevel := b_native_cutoff_error_level hκ hR ρ α hell K G hK φ hφ t ht (1/4)
  change (1/4 : ℝ) * (dirichletVolume ρ R).real B ≤ _ at hlevel
  have hbound : (1/4 : ℝ) * (dirichletVolume ρ R).real A ≤
      t * ((κ⁻¹ * (1024 / r ^ 2)) * (volume (sourceBall x (2 * r))).toReal) := by
    calc
      _ ≤ (1/4 : ℝ) * (dirichletVolume ρ R).real B :=
        mul_le_mul_of_nonneg_left hm (by norm_num)
      _ ≤ _ := hlevel
      _ ≤ _ := mul_le_mul_of_nonneg_left he ht.le
  change (dirichletVolume ρ R).real A ≤ _
  nlinarith

/-- At a uniform diffusive time scale, every admissible interior ball contains
a starting point whose actual native spectral row has mass greater than one half. -/
theorem b_native_interior_exists_good_start (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ), 0 < R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
    ∀ (x : Vec d) (r : ℝ), 0 < r → sourceBall x (2 * r) ⊆ sourceBall 0 R →
    ∀ t : ℝ, 0 < t → t ≤ δ * r ^ 2 →
      ∃ z ∈ sourceBall x r, (1/2 : ℝ) < ∫ y in sourceBall 0 R, K t z y := by
  let δ : ℝ := κ ^ 2 / (8192 * (2 : ℝ) ^ d)
  have htwo : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro R hR ρ α hell K G hK x r hr hinside t ht htbound
  have hinner : sourceBall x r ⊆ sourceBall 0 R := by
    apply Set.Subset.trans ?_ hinside
    intro z hz
    change euclideanNorm (z - x) < r at hz
    change euclideanNorm (z - x) < 2 * r
    linarith
  have hmeas : MeasurableSet (sourceBall x r) := by
    rw [b_sourceBall_eq_euclideanBall x hr]
    exact (PDE.isOpen_euclideanBall x r).measurableSet
  have hvolpos : 0 < (volume (sourceBall x r)).toReal := by
    rw [b_sourceBall_eq_euclideanBall x hr]
    exact PDE.volume_euclideanBall_toReal_pos x hr
  have hvol : (volume (sourceBall x (2 * r))).toReal =
      (2 : ℝ) ^ d * (volume (sourceBall x r)).toReal := by
    rw [b_sourceBall_eq_euclideanBall x (by positivity : 0 < 2 * r),
      b_sourceBall_eq_euclideanBall x hr,
      PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos x (by positivity : 0 < 2 * r),
      PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos x hr, mul_pow]
    ring
  have hweighted : κ * (volume (sourceBall x r)).toReal ≤
      (dirichletVolume ρ R).real (sourceBall x r) := by
    exact dirichletVolume_real_lower ρ R hR κ⁻¹ κ hκ.le
      (fun y _ => (hell.2.2 y).2.1) (fun y _ => (hell.2.2 y).1)
      (sourceBall x r) hmeas hinner
  have hbad := b_native_interior_bad_mass_measure hd hκ hR hr ρ α hell K G hK
    x hinside t ht
  have htime : 4 * t * (κ⁻¹ * (1024 / r ^ 2)) *
      (volume (sourceBall x (2 * r))).toReal ≤
      (κ / 2) * (volume (sourceBall x r)).toReal := by
    calc
      _ ≤ 4 * (δ * r ^ 2) * (κ⁻¹ * (1024 / r ^ 2)) *
          (volume (sourceBall x (2 * r))).toReal := by
        gcongr
      _ = _ := by
        rw [hvol]
        dsimp [δ]
        field_simp
        <;> ring
  by_contra hnone
  push_neg at hnone
  have hbadset : {z | z ∈ sourceBall x r ∧
      (∫ y in sourceBall 0 R, K t z y) ≤ (1/2 : ℝ)} = sourceBall x r := by
    ext z
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, hnone z hz⟩⟩
  rw [hbadset] at hbad
  nlinarith [mul_pos hκ hvolpos]


/-- The actual native kernel has a radius-uniform Gaussian bound on the mass
    ending outside a ball. The estimate concerns the endpoint, not killing. -/
theorem b_native_exterior_endpoint_mass {d : ℕ} (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
    ∀ (t : ℝ), 0 < t → ∀ x ∈ sourceBall 0 R, ∀ (r : ℝ), 0 < r →
      (∫ y in sourceBall (0 : Vec d) R \ sourceBall x r, K t x y) ≤
        C * Real.exp (-r ^ 2 / (C * t)) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := c12_spectral_gaussian_envelope_pointwise hd hκ
  let p : ℝ := -(d : ℝ) / 2
  let Q : ℝ := B / 2
  let P : ℝ := κ⁻¹ * (A * ((1 / 2 : ℝ) ^ p) / κ)
  let M : ℝ := P * (Real.pi * (2 * Q)) ^ ((d : ℝ) / 2)
  let C : ℝ := 2 * Q + M + 1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hCQ : 2 * Q ≤ C := by dsimp [C]; linarith
  have hCM : M ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α hell K G hK t ht x hx r hr
  let S : Set (Vec d) := sourceBall (0 : Vec d) R \ sourceBall x r
  have hS : MeasurableSet S := by
    apply (dirichletBall (d := d) R).isOpen.measurableSet.diff
    rw [b_sourceBall_eq_euclideanBall x hr]
    exact (PDE.isOpen_euclideanBall x r).measurableSet
  have hρ (y : Vec d) : 0 < ρ y := hκ.trans_le (hell.2.2 y).1
  obtain ⟨s, hs⟩ := hK.2
  have : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hball : ∀ᵐ y ∂dirichletVolume ρ R, y ∈ sourceBall (0 : Vec d) R :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)
  have heq : (fun y => ∑' n, Real.exp (-s.eigenvalue n*t) *
      s.eigenfunction n x * s.eigenfunction n y) =ᵐ[dirichletVolume ρ R]
      (fun y => K t x y / ρ y) := by
    filter_upwards [hball] with y hy
    rw [(hs t ht x hx y hy).2]
    field_simp [ne_of_gt (hρ y)]
    simp only [mul_comm t (s.eigenvalue _)]
  have hrow : MemLp (fun y => K t x y / ρ y) 2 (dirichletVolume ρ R) :=
    (spectral_heat_row_memLp hd hκ hell hR s t ht x hx).ae_eq heq
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    change volume.restrict (sourceBall (0 : Vec d) R) ≪
      (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun y => ENNReal.ofReal (ρ y))
    apply withDensity_absolutelyContinuous' hell.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun y => ne_of_gt (ENNReal.ofReal_pos.mpr (hρ y))
  have hkmeas : AEStronglyMeasurable (K t x) (volume.restrict S) := by
    have hm := (hrow.aestronglyMeasurable.mono_ac hac).mul hell.1.aestronglyMeasurable
    have hm' : AEStronglyMeasurable (K t x)
        (volume.restrict (sourceBall (0 : Vec d) R)) := by
      apply hm.congr
      filter_upwards [] with y
      exact div_mul_cancel₀ (K t x y) (ne_of_gt (hρ y))
    exact hm'.mono_measure (Measure.restrict_mono_set volume
      (Set.sdiff_subset : S ⊆ sourceBall (0 : Vec d) R))
  have hh := hbound hR hell K G hK (t / 2) (by positivity) x hx
  have htime : t / 2 + t / 2 = t := by ring
  have hrpow : (t / 2) ^ p = (1 / 2 : ℝ) ^ p * t ^ p := by
    have he : t / 2 = (1 / 2 : ℝ) * t := by ring
    rw [he, Real.mul_rpow (by norm_num) ht.le]
  have hden : B * (t / 2) = Q * t := by dsimp [Q]; ring
  have hgauss : ∀ y ∈ sourceBall (0 : Vec d) R,
      K t x y ≤ P * t ^ p * Real.exp (-(euclideanNorm (x - y)) ^ 2 / (Q * t)) := by
    intro y hy
    have hy' := hh y hy
    rw [htime, show (t / 2) ^ (-(d : ℝ) / 2) = (t / 2) ^ p by rfl,
      hrpow, hden] at hy'
    dsimp [P]
    convert hy' using 1
    all_goals ring
  let D : ℝ := P * t ^ p * Real.exp (-r ^ 2 / (2 * Q * t))
  let H : Vec d → ℝ := fun y => Real.exp (-(euclideanSq (y - x)) / (2 * Q * t))
  have hH : Integrable H (volume.restrict S) :=
    ((c12_translated_gaussian_euclidean (d := d) (show 0 < 2 * Q * t by positivity) x).1).mono_measure
      Measure.restrict_le_self
  have hmajor : Integrable (fun y => D * H y) (volume.restrict S) := hH.const_mul D
  have hp : ∀ᵐ y ∂volume.restrict S, 0 ≤ K t x y ∧ K t x y ≤ D * H y := by
    filter_upwards [ae_restrict_mem hS] with y hy
    have he := c12_gaussian_exterior_exponent_bound hQ ht hr x y hy.2
    have hc : 0 ≤ P * t ^ p := mul_nonneg hP.le (Real.rpow_nonneg ht.le _)
    refine ⟨(hK.1 y hy.1).2.1 t ht x hx, ?_⟩
    calc
      K t x y ≤ P * t ^ p * Real.exp (-(euclideanNorm (x - y)) ^ 2 / (Q * t)) :=
        hgauss y hy.1
      _ ≤ P * t ^ p * (Real.exp (-r ^ 2 / (2 * Q * t)) * H y) :=
        mul_le_mul_of_nonneg_left he hc
      _ = D * H y := by dsimp [D]; ring
  have hki : Integrable (K t x) (volume.restrict S) := by
    refine Integrable.mono' hmajor hkmeas ?_
    filter_upwards [hp] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2
  have hmexp : Real.exp (-r ^ 2 / (2 * Q * t)) ≤ Real.exp (-r ^ 2 / (C * t)) := by
    apply Real.exp_le_exp.mpr
    have hden' : 2 * Q * t ≤ C * t := mul_le_mul_of_nonneg_right hCQ ht.le
    have hp1 : 0 < 2 * Q * t := by positivity
    have hp2 : 0 < C * t := by positivity
    rw [div_le_div_iff₀ hp1 hp2]
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith
  calc
    (∫ y in S, K t x y) ≤ ∫ y in S, D * H y :=
      integral_mono_ae hki hmajor (hp.mono fun _ hy => hy.2)
    _ = D * (∫ y in S, H y) := integral_const_mul _ _
    _ ≤ M * Real.exp (-r ^ 2 / (2 * Q * t)) := by
      have hz := c12_restricted_gaussian_scaled_mass_bound d hQ ht x S
      have hz' := mul_le_mul_of_nonneg_left hz
        (mul_nonneg hP.le (Real.exp_pos (-r ^ 2 / (2 * Q * t))).le)
      dsimp [D, M, H, p] at *
      nlinarith
    _ ≤ C * Real.exp (-r ^ 2 / (C * t)) :=
      mul_le_mul hCM hmexp (Real.exp_pos _).le (le_trans hM hCM)

#print axioms b_native_exterior_endpoint_mass

end EinsteinFull.Calculus
