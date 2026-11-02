import EinsteinRelation.Regeneration.HalfSpaces
import EinsteinFull.Calculus.C5TubeSignedPowerDomination
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3TubeProbability
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Average
import EllipticRegularity.Parabolic.LocalMax.Cutoff
import EllipticRegularity.Parabolic.LocalMax.EnergyPointwise
import EinsteinFull.Calculus.ParabolicBridgeCoeff
import EinsteinFull.Calculus.C13TubeNativeCutoffProduct
import EinsteinFull.Calculus.C9TubeWeightedZeroPast

open EinsteinRelation MeasureTheory
open PDE.Parabolic.LocalMax
open EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- Each coordinate of the actual elliptic flux is square integrable. -/
theorem c5_weighted_caloric_flux_memLp {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) :
    ∀ i : Fin d, MemLp (fun z => ((α z.2).mulVec (G z)) i) 2
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hα : IsElliptic κ⁻¹ α := by
    intro x
    simpa only [inv_inv] using (h.2.2 x).2.2
  have hαtop (i j : Fin d) : MemLp (fun z : ℝ × Vec d => α z.2 i j) ∞ μ := by
    let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
    let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
    have hm : Measurable (fun z : ℝ × Vec d => α z.2 i j) :=
      ((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
        (h.2.1.comp measurable_snd)
    apply memLp_top_of_bound hm.aestronglyMeasurable κ⁻¹
    apply ae_of_all
    intro z
    have he := PiLp.norm_apply_le
      (WithLp.toLp 2 ((α z.2).mulVec (unitVector j)) : EuclideanSpace ℝ (Fin d)) i
    have hn := Correctors.isElliptic_mulVec_euclideanNorm_le (inv_pos.mpr hκ)
      hα z.2 (unitVector j)
    rw [TimeChange.euclideanNorm_eq_norm_toLp] at hn
    have hv : ((α z.2).mulVec (unitVector j)) i = α z.2 i j := by
      change dotProduct (fun k => α z.2 i k) (Pi.single j 1) = _
      rw [dotProduct_single, mul_one]
    have hw : euclideanNorm (unitVector j) = 1 := by
      simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
    simpa only [PiLp.toLp_apply, hv, Real.norm_eq_abs, hw, mul_one] using he.trans hn
  have hG : MemLp G 2 μ := by
    apply hu.2.2.1.mono' hu.2.1
    exact Filter.Eventually.of_forall (fun z => by
      apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
      intro i
      exact EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm (G z) i)
  have hg : ∀ i, MemLp (fun z => G z i) 2 μ := memLp_pi_iff.mp hG
  intro i
  simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply] using
    memLp_finsetSum Finset.univ (fun j _ => (hαtop i j).mul (hg j))

/-- The mass and flux of a weighted caloric function are square integrable,
so its literal weighted mass and coefficient energy are integrable. -/
theorem c5_weighted_caloric_mass_flux_energy_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) :
    Integrable (fun z => ρ z.2 * u z ^ 2) (volume.restrict (I ×ˢ U)) ∧
      Integrable (fun z => dot ((α z.2).mulVec (G z)) (G z))
        (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hρ : MemLp (fun z : ℝ × Vec d => ρ z.2) ∞ μ := by
    apply memLp_top_of_bound (h.1.comp measurable_snd).aestronglyMeasurable κ⁻¹
    exact ae_of_all μ (fun z => by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans (h.2.2 z.2).1)] using
        (h.2.2 z.2).2.1)
  have hflux := c5_weighted_caloric_flux_memLp hκ h hu
  have hG : MemLp G 2 μ := by
    apply hu.2.2.1.mono' hu.2.1
    exact Filter.Eventually.of_forall (fun z => by
      apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
      intro i
      exact EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm (G z) i)
  have hg : ∀ i, MemLp (fun z => G z i) 2 μ := memLp_pi_iff.mp hG
  refine ⟨hu.1.integrable_sq.mul_of_top_right hρ, ?_⟩
  change Integrable (fun z => ∑ i : Fin d, ((α z.2).mulVec (G z)) i * G z i) μ
  exact integrable_finsetSum Finset.univ (fun i _ => (hflux i).integrable_mul (hg i))

/-- A smooth spatially compact cutoff for the fixed nested cylinders, with
explicit bounds on its time and Euclidean spatial derivatives. -/
theorem c5_fixed_cylinder_cutoff (d : ℕ) :
    ∃ (η : PDE.Vec d × ℝ → ℝ) (B : ℝ) (K : Set (PDE.Vec d)),
      0 ≤ B ∧ ContDiff ℝ (⊤ : ℕ∞) η ∧ IsCompact K ∧ K ⊆ sourceBall 0 1 ∧
      (∀ z, 0 ≤ η z ∧ η z ≤ 1) ∧
      (∀ x ∈ sourceBall 0 (1/2), ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4), η (x, t) = 1) ∧
      (∀ x t, t ≤ (-3/8 : ℝ) → η (x, t) = 0) ∧
      (∀ x ∉ K, ∀ t, η (x, t) = 0) ∧
      (∀ z, |PDE.parTimeDeriv η z| ≤ 8 * B) ∧
      (∀ z, PDE.vecNormSq (PDE.parSpaceGrad η z) ≤ 4096) := by
  obtain ⟨B, hB0, hB⟩ := PDE.Parabolic.LocalMax.exists_abs_deriv_smoothTransition_le
  let η := PDE.Parabolic.LocalMax.cylCutoff (d := d) (1/2) 1 (-1/2) (-1/4)
  let K := tsupport (PDE.canonicalBallCutoff (0 : PDE.Vec d) (1/2) 1)
  refine ⟨η, B, K, hB0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PDE.Parabolic.LocalMax.cylCutoff_contDiff (by norm_num) (by norm_num) _ _
  · exact PDE.canonicalBallCutoff_hasCompactSupport (by norm_num) (by norm_num)
  · rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1)]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer (by norm_num) (by norm_num)
  · intro z
    exact ⟨PDE.Parabolic.LocalMax.cylCutoff_nonneg _ _ _ _ z,
      PDE.Parabolic.LocalMax.cylCutoff_le_one _ _ _ _ z⟩
  · intro x hx t ht
    apply PDE.Parabolic.LocalMax.cylCutoff_eq_one (by norm_num) (by norm_num) (by norm_num)
    · rw [EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1/2)]
      exact hx
    · linarith [ht.1]
  · intro x t ht
    apply PDE.Parabolic.LocalMax.cylCutoff_eq_zero_of_le (by norm_num)
    norm_num at ht ⊢
    exact ht
  · intro x hx t
    exact PDE.Parabolic.LocalMax.cylCutoff_eq_zero_of_notMem hx t
  · intro z
    have hb := PDE.Parabolic.LocalMax.abs_parTimeDeriv_cylCutoff_le hB
      (r := (1/2 : ℝ)) (ρ := 1) (T := -1/2) (T' := -1/4)
      (by norm_num) (by norm_num) (by norm_num) z
    convert hb using 1 <;> norm_num <;> ring
  · intro z
    have hb := PDE.Parabolic.LocalMax.vecNormSq_parSpaceGrad_cylCutoff_le
      (r := (1/2 : ℝ)) (ρ := 1) (by norm_num) (by norm_num) (-1/2) (-1/4) z
    convert hb using 1 <;> norm_num

/-- Every spatial slice of a smooth cutoff supported in a common compact set
is an admissible spatial test, with the literal space-time gradient. -/
theorem c5_cutoff_spatial_slice_test {d : ℕ} {U K : Set (Vec d)}
    {η : Vec d × ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hηK : ∀ x ∉ K, ∀ t, η (x, t) = 0) (t : ℝ) :
    IsSpatialTest U (fun x => η (x, t)) ∧
      (∀ x i, fderiv ℝ (fun y => η (y, t)) x (unitVector i) =
        PDE.parSpaceGrad η (x, t) i) := by
  have hsupp : Function.support (fun x => η (x, t)) ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (hηK x hxK t)
  have htsupp : tsupport (fun x => η (x, t)) ⊆ K :=
    closure_minimal hsupp hK.isClosed
  refine ⟨⟨hη.comp (contDiff_id.prodMk contDiff_const),
    hK.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hKU⟩, ?_⟩
  intro x i
  rw [EinsteinFull.Blueprint.TubeProbability.DimensionLift.spatial_slice_fderiv
    (hη.differentiable (by simp))]
  rfl

/-- Multiplying the actual mass and coefficient energy by a bounded smooth
cutoff preserves integrability on the caloric cylinder. -/
theorem c5_weighted_caloric_cutoff_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ}
    (hη : Continuous η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1) :
    Integrable (fun z => η (z.2, z.1) ^ 2 * (ρ z.2 * u z ^ 2))
        (volume.restrict (I ×ˢ U)) ∧
      Integrable (fun z => η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z))
        (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hηtop : MemLp (fun z : ℝ × Vec d => η (z.2, z.1) ^ 2) ∞ μ := by
    apply memLp_top_of_bound ((hη.comp (continuous_snd.prodMk continuous_fst)).pow 2).aestronglyMeasurable 1
    exact ae_of_all μ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change η (z.2, z.1) ^ 2 ≤ 1
      exact (sq_le_one_iff₀ (hη0 _)).2 (hη1 _))
  obtain ⟨hmass, henergy⟩ := c5_weighted_caloric_mass_flux_energy_integrable hκ h hu
  constructor
  · convert hmass.mul_of_top_right hηtop using 1
  · convert henergy.mul_of_top_right hηtop using 1

/-- The cutoff energy dominates the actual coefficient energy on the inner
cylinder, since the cutoff is one there and ellipticity makes energy nonnegative. -/
theorem c5_inner_energy_le_cutoff_energy {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    {η : Vec d × ℝ → ℝ} (hη : Continuous η) (hη0 : ∀ z, 0 ≤ η z)
    (hη1 : ∀ z, η z ≤ 1)
    (hone : ∀ x ∈ sourceBall 0 (1/2), ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4), η (x, t) = 1) :
    (∫ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2),
      dot ((α z.2).mulVec (G z)) (G z)) ≤
    ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z) := by
  let small : Set (ℝ × Vec d) := Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2)
  let large : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1
  have hsub : small ⊆ large := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    change euclideanNorm (x - 0) < 1/2 at hx
    change euclideanNorm (x - 0) < 1
    linarith
  have hsmall : MeasurableSet small := by
    apply measurableSet_Ioo.prod
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1/2)]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hpos (z : ℝ × Vec d) : 0 ≤ dot ((α z.2).mulVec (G z)) (G z) := by
    have hc := (h.2.2 z.2).2.2.2 (G z) |>.1
    have he : 0 ≤ κ * euclideanSq (G z) := mul_nonneg hκ.le (PDE.vecNormSq_nonneg _)
    have := he.trans hc
    simpa only [dot, mul_comm] using this
  have hint := (c5_weighted_caloric_cutoff_integrable hκ h hu hη hη0 hη1).2
  calc
    (∫ z in small, dot ((α z.2).mulVec (G z)) (G z)) =
        ∫ z in small, η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z) := by
      apply setIntegral_congr_fun hsmall
      intro z hz
      change dot ((α z.2).mulVec (G z)) (G z) =
        η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z)
      rw [hone z.2 hz.2 z.1 hz.1]
      simp
    _ ≤ ∫ z in large, η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z) := by
      exact integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (ae_of_all _ fun z => mul_nonneg (sq_nonneg _) (hpos z)) hint

/-- The time derivative of a bounded cutoff contributes at most its uniform
bound times the actual weighted mass, including for signed solutions. -/
theorem c5_weighted_cutoff_time_term_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ} {M : ℝ}
    (hη : Continuous η) (hηt : Continuous (PDE.parTimeDeriv η))
    (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    (ht : ∀ z, |PDE.parTimeDeriv η z| ≤ M) :
    Integrable (fun z => η (z.2, z.1) * PDE.parTimeDeriv η (z.2, z.1) *
      (ρ z.2 * u z ^ 2)) (volume.restrict (I ×ˢ U)) ∧
    (∫ z in I ×ˢ U, |η (z.2, z.1) * PDE.parTimeDeriv η (z.2, z.1) *
      (ρ z.2 * u z ^ 2)|) ≤ M * ∫ z in I ×ˢ U, ρ z.2 * u z ^ 2 := by
  let μ := volume.restrict (I ×ˢ U)
  have hm := (c5_weighted_caloric_mass_flux_energy_integrable hκ h hu).1
  have htop : MemLp (fun z : ℝ × Vec d => η (z.2, z.1) *
      PDE.parTimeDeriv η (z.2, z.1)) ∞ μ := by
    apply memLp_top_of_bound
      (((hη.mul hηt).comp (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable) M
    apply ae_of_all
    intro z
    change |η (z.2, z.1) * PDE.parTimeDeriv η (z.2, z.1)| ≤ M
    rw [abs_mul, abs_of_nonneg (hη0 _)]
    calc η (z.2, z.1) * |PDE.parTimeDeriv η (z.2, z.1)| ≤
        1 * M := mul_le_mul (hη1 _) (ht _) (abs_nonneg _) (by norm_num)
      _ = M := one_mul _
  have hi : Integrable (fun z => η (z.2, z.1) * PDE.parTimeDeriv η (z.2, z.1) *
      (ρ z.2 * u z ^ 2)) μ := by
    convert hm.mul_of_top_right htop using 1 <;> ring
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono_ae hi.abs (hm.const_mul M)
  apply ae_of_all
  intro z
  have hr : 0 ≤ ρ z.2 * u z ^ 2 :=
    mul_nonneg (hκ.le.trans (h.2.2 z.2).1) (sq_nonneg _)
  change |η (z.2, z.1) * PDE.parTimeDeriv η (z.2, z.1) * (ρ z.2 * u z ^ 2)| ≤ M * (ρ z.2 * u z ^ 2)
  rw [abs_mul, abs_mul, abs_of_nonneg (hη0 _), abs_of_nonneg hr]
  calc η (z.2, z.1) * |PDE.parTimeDeriv η (z.2, z.1)| * (ρ z.2 * u z ^ 2) ≤
      (1 * M) * (ρ z.2 * u z ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hη1 _) (ht _) (abs_nonneg _) (by norm_num)) hr
    _ = M * (ρ z.2 * u z ^ 2) := by ring

/-- The signed spatial cutoff cross term is integrable on the original
weighted caloric cylinder. -/
theorem c5_weighted_cutoff_spatial_cross_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ} {L : ℝ}
    (hη : ContDiff ℝ 1 η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    (hgrad : ∀ z i, |PDE.parSpaceGrad η z i| ≤ L) :
    Integrable (fun z => η (z.2, z.1) * u z *
      dot ((α z.2).mulVec (G z)) (PDE.parSpaceGrad η (z.2, z.1)))
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have htop (i : Fin d) : MemLp (fun z : ℝ × Vec d =>
      η (z.2, z.1) * PDE.parSpaceGrad η (z.2, z.1) i) ∞ μ := by
    have hc : Continuous (fun z => PDE.parSpaceGrad η z i) := by
      exact (hη.continuous_fderiv (by norm_num)).clm_apply continuous_const
    apply memLp_top_of_bound
      (((hη.continuous.mul hc).comp (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable) L
    apply ae_of_all
    intro z
    change |η (z.2, z.1) * PDE.parSpaceGrad η (z.2, z.1) i| ≤ L
    rw [abs_mul, abs_of_nonneg (hη0 _)]
    calc η (z.2, z.1) * |PDE.parSpaceGrad η (z.2, z.1) i| ≤ 1 * L :=
      mul_le_mul (hη1 _) (hgrad _ _) (abs_nonneg _) (by norm_num)
      _ = L := one_mul _
  have hflux := c5_weighted_caloric_flux_memLp hκ h hu
  have hprod (i : Fin d) : MemLp (fun z : ℝ × Vec d =>
      η (z.2, z.1) * PDE.parSpaceGrad η (z.2, z.1) i * u z) 2 μ :=
    (htop i).mul hu.1
  have hterm (i : Fin d) : Integrable (fun z : ℝ × Vec d =>
      (η (z.2, z.1) * PDE.parSpaceGrad η (z.2, z.1) i * u z) *
        ((α z.2).mulVec (G z)) i) μ :=
    (hprod i).integrable_mul (hflux i)
  have hs := integrable_finsetSum Finset.univ (fun i _ => hterm i)
  convert hs using 1
  funext z
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The spatial cutoff error is controlled by the actual weighted mass and
the lower bound on the clock density. -/
theorem c5_weighted_cutoff_spatial_mass_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ} {L : ℝ}
    (hη : ContDiff ℝ 1 η) (hL : 0 ≤ L)
    (hgrad : ∀ z, PDE.vecNormSq (PDE.parSpaceGrad η z) ≤ L) :
    Integrable (fun z => u z ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (z.2, z.1)))
      (volume.restrict (I ×ˢ U)) ∧
    (∫ z in I ×ˢ U, u z ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (z.2, z.1))) ≤
      (L * κ⁻¹) * ∫ z in I ×ˢ U, ρ z.2 * u z ^ 2 := by
  let μ := volume.restrict (I ×ˢ U)
  have hc : Continuous (fun z => PDE.vecNormSq (PDE.parSpaceGrad η z)) := by
    have heq : (fun z => PDE.vecNormSq (PDE.parSpaceGrad η z)) =
        fun z => ∑ i, PDE.parSpaceGrad η z i ^ 2 :=
      funext fun z => PDE.vecNormSq_eq_sum_sq _
    rw [heq]
    exact continuous_finsetSum _ fun i _ =>
      ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2
  have htop : MemLp (fun z : ℝ × Vec d => PDE.vecNormSq
      (PDE.parSpaceGrad η (z.2, z.1))) ∞ μ := by
    apply memLp_top_of_bound ((hc.comp (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable) L
    apply ae_of_all
    intro z
    change |PDE.vecNormSq (PDE.parSpaceGrad η (z.2, z.1))| ≤ L
    rw [abs_of_nonneg (PDE.vecNormSq_nonneg _)]
    exact hgrad _
  have hi : Integrable (fun z => u z ^ 2 * PDE.vecNormSq
      (PDE.parSpaceGrad η (z.2, z.1))) μ := by
    convert hu.1.integrable_sq.mul_of_top_right htop using 1
    funext z
    exact mul_comm _ _
  have hm := (c5_weighted_caloric_mass_flux_energy_integrable hκ h hu).1
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono_ae hi (hm.const_mul (L * κ⁻¹))
  apply ae_of_all
  intro z
  change u z ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (z.2, z.1)) ≤
    (L * κ⁻¹) * (ρ z.2 * u z ^ 2)
  have hsq := sq_nonneg (u z)
  have hr := mul_le_mul_of_nonneg_right (h.2.2 z.2).1 hsq
  have hr' := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hκ.le)
  have hinv : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ.ne'
  have hu' : u z ^ 2 ≤ κ⁻¹ * (ρ z.2 * u z ^ 2) := by nlinarith [hinv]
  calc u z ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (z.2, z.1)) ≤ u z ^ 2 * L :=
      mul_le_mul_of_nonneg_left (hgrad _) hsq
    _ ≤ (L * κ⁻¹) * (ρ z.2 * u z ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hu' hL]

/-- A Euclidean bound on the cutoff gradient makes the actual mixed spatial
flux term integrable for every weighted caloric solution. -/
theorem c5_weighted_cutoff_spatial_cross_integrable_of_norm_bound
    {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ} {R : ℝ}
    (hη : ContDiff ℝ 1 η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    (hR : 0 ≤ R) (hgrad : ∀ z, PDE.vecNormSq (PDE.parSpaceGrad η z) ≤ R ^ 2) :
    Integrable (fun z => η (z.2, z.1) * u z *
      dot ((α z.2).mulVec (G z)) (PDE.parSpaceGrad η (z.2, z.1)))
      (volume.restrict (I ×ˢ U)) := by
  apply c5_weighted_cutoff_spatial_cross_integrable hκ h hu hη hη0 hη1 (L := R)
  intro z i
  have hc := EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm
    (PDE.parSpaceGrad η z) i
  have hn : euclideanNorm (PDE.parSpaceGrad η z) ≤ R := by
    change Real.sqrt (PDE.vecNormSq (PDE.parSpaceGrad η z)) ≤ R
    have hs := Real.sqrt_le_sqrt (hgrad z)
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hR] using hs
  exact hc.trans hn

/-- The actual weighted mass and elliptic energy have integrable spatial
slices at almost every time, with nonnegative slice integrals. -/
theorem c5_weighted_caloric_mass_energy_slices {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) :
    ∀ᵐ t ∂volume.restrict I,
      Integrable (fun x => ρ x * u (t, x) ^ 2) (volume.restrict U) ∧
      Integrable (fun x => dot ((α x).mulVec (G (t, x))) (G (t, x))) (volume.restrict U) ∧
      0 ≤ (∫ x in U, ρ x * u (t, x) ^ 2) ∧
      0 ≤ (∫ x in U, dot ((α x).mulVec (G (t, x))) (G (t, x))) := by
  obtain ⟨hm, he⟩ := c5_weighted_caloric_mass_flux_energy_integrable hκ h hu
  have hm' : Integrable (fun z => ρ z.2 * u z ^ 2)
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hm
  have he' : Integrable (fun z => dot ((α z.2).mulVec (G z)) (G z))
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact he
  filter_upwards [hm'.prod_right_ae, he'.prod_right_ae] with t hmt het
  refine ⟨hmt, het, ?_, ?_⟩
  · apply integral_nonneg
    intro x
    exact mul_nonneg (hκ.le.trans (h.2.2 x).1) (sq_nonneg _)
  · apply integral_nonneg
    intro x
    change 0 ≤ dot ((α x).mulVec (G (t, x))) (G (t, x))
    have he0 : 0 ≤ κ * euclideanSq (G (t, x)) :=
      mul_nonneg hκ.le (PDE.vecNormSq_nonneg _)
    have he1 := (h.2.2 x).2.2.2 (G (t, x)) |>.1
    have := he0.trans he1
    simpa only [dot, mul_comm] using this

/-- The squared cutoff is a spatial test on every time slice, with the
product-rule gradient needed for testing the signed caloric equation. -/
theorem c5_squared_cutoff_spatial_slice_test {d : ℕ} {U K : Set (Vec d)}
    {η : Vec d × ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hηK : ∀ x ∉ K, ∀ t, η (x, t) = 0) (t : ℝ) :
    IsSpatialTest U (fun x => η (x, t) ^ 2) ∧
      (∀ x i, fderiv ℝ (fun y => η (y, t) ^ 2) x (unitVector i) =
        2 * η (x, t) * PDE.parSpaceGrad η (x, t) i) := by
  have hs := c5_cutoff_spatial_slice_test (hη.pow 2) hK hKU
    (fun x hx t => by simp [hηK x hx t]) t
  refine ⟨hs.1, ?_⟩
  intro x i
  rw [hs.2 x i]
  change fderiv ℝ (fun z => η z ^ 2) (x, t) (PDE.basisVec i, 0) =
    2 * η (x, t) * fderiv ℝ η (x, t) (PDE.basisVec i, 0)
  have hd := hη.differentiable (by simp) (x, t)
  simp only [pow_two]
  change fderiv ℝ (η * η) (x, t) (PDE.basisVec i, 0) = _
  rw [fderiv_mul hd hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The flux cross term is controlled by the actual symmetric coefficient's
quadratic form and its upper ellipticity bound. -/
theorem c5_weighted_flux_cross_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (x e p : Vec d) :
    dot ((α x).mulVec e) p ^ 2 ≤
      κ⁻¹ * dot e ((α x).mulVec e) * euclideanSq p := by
  have hk : κ ≤ κ⁻¹ := (h.2.2 x).1.trans (h.2.2 x).2.1
  have hkone : κ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hk hκ.le
    have hi : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
    nlinarith [sq_nonneg (κ - 1)]
  have hΛ : 1 ≤ κ⁻¹ := (one_le_inv₀ hκ).2 hkone
  have hS : EinsteinFull.S5Elliptic (α x) κ⁻¹ := by
    refine ⟨hΛ, ?_, ?_, ?_⟩
    · intro j k
      have hs := congrFun (congrFun (h.2.2 x).2.2.1 j) k
      simpa [Matrix.transpose_apply] using hs.symm
    · intro v
      simpa only [inv_inv, EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot,
        PDE.vecNormSq, PDE.vecDot, PDE.matVecMul, Matrix.mulVec, dotProduct,
        euclideanSq, dot, pow_two] using (h.2.2 x).2.2.2 v |>.1
    · intro v
      simpa only [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot,
        PDE.vecNormSq, PDE.vecDot, PDE.matVecMul, Matrix.mulVec, dotProduct,
        euclideanSq, dot, pow_two] using (h.2.2 x).2.2.2 v |>.2
  have hcs := EinsteinFull.s5Bil_sq_le hS p e
  have hu := hS.upper p
  have hq := EinsteinFull.s5Bil_self_nonneg hS e
  have hh := mul_le_mul_of_nonneg_right hu hq
  have hp := hcs.trans hh
  have hcross : dot ((α x).mulVec e) p = EinsteinFull.s5Bil (α x) p e := by
    rw [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot, PDE.vecDot_comm]
    rfl
  rw [hcross]
  simp only [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot,
    PDE.vecNormSq, PDE.vecDot, PDE.matVecMul, Matrix.mulVec, dotProduct,
    euclideanSq, dot, pow_two] at hp ⊢
  convert hp using 1 <;> ring

/-- Young absorption of the signed solution's literal elliptic flux term. -/
theorem c5_weighted_signed_cutoff_cross_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (x e p : Vec d) (u η : ℝ) :
    |u * (2 * η * dot ((α x).mulVec e) p)| ≤
      (1 / 2 : ℝ) * dot e ((α x).mulVec e) * η ^ 2 +
        2 * κ⁻¹ * u ^ 2 * euclideanSq p := by
  have hq : 0 ≤ dot e ((α x).mulVec e) := by
    have he := (h.2.2 x).2.2.2 e |>.1
    have hn : 0 ≤ euclideanSq e := PDE.vecNormSq_nonneg e
    change κ * euclideanSq e ≤ dot e ((α x).mulVec e) at he
    exact (mul_nonneg hκ.le hn).trans he
  have hp : 0 ≤ euclideanSq p := PDE.vecNormSq_nonneg p
  have hc := c5_weighted_flux_cross_bound hκ h x e p
  have hy := PDE.Parabolic.LocalMax.abs_young_le
    (F0 := u ^ 2) (F1 := u) (F2 := 1) (K := 1) (L := κ⁻¹)
    (Q := dot e ((α x).mulVec e)) (N := euclideanSq p) (η := η) (χ := 1)
    (P := dot ((α x).mulVec e) p)
    (sq_nonneg u) (by norm_num) (by norm_num) (inv_nonneg.mpr hκ.le)
    hq hp (by norm_num) (by simp) hc
  simpa only [mul_one, one_mul] using hy

/-- The integrated signed flux error is absorbed by half the cutoff energy,
with the remainder controlled by the actual weighted mass. -/
theorem c5_weighted_cutoff_cross_integral_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ} {R : ℝ}
    (hη : ContDiff ℝ 1 η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    (hR : 0 ≤ R) (hgrad : ∀ z, PDE.vecNormSq (PDE.parSpaceGrad η z) ≤ R ^ 2) :
    (∫ z in I ×ˢ U, |2 * η (z.2, z.1) * u z *
      dot ((α z.2).mulVec (G z)) (PDE.parSpaceGrad η (z.2, z.1))|) ≤
    (1 / 2 : ℝ) * (∫ z in I ×ˢ U,
      η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z)) +
      (2 * κ⁻¹ * (R ^ 2 * κ⁻¹)) * ∫ z in I ×ˢ U, ρ z.2 * u z ^ 2 := by
  let μ := volume.restrict (I ×ˢ U)
  have hcross := c5_weighted_cutoff_spatial_cross_integrable_of_norm_bound
    hκ h hu hη hη0 hη1 hR hgrad
  have hi : Integrable (fun z => 2 * η (z.2, z.1) * u z *
      dot ((α z.2).mulVec (G z)) (PDE.parSpaceGrad η (z.2, z.1))) μ := by
    convert hcross.const_mul 2 using 1 <;> ring
  have he := (c5_weighted_caloric_cutoff_integrable hκ h hu hη.continuous hη0 hη1).2
  obtain ⟨hs, hsbound⟩ := c5_weighted_cutoff_spatial_mass_bound hκ h hu hη
    (sq_nonneg R) hgrad
  have hpoint : ∀ z : ℝ × Vec d,
      |2 * η (z.2, z.1) * u z *
        dot ((α z.2).mulVec (G z)) (PDE.parSpaceGrad η (z.2, z.1))| ≤
      (1 / 2 : ℝ) * (η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z)) +
        (2 * κ⁻¹) * (u z ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (z.2, z.1))) := by
    intro z
    have hh := c5_weighted_signed_cutoff_cross_bound hκ h z.2 (G z)
      (PDE.parSpaceGrad η (z.2, z.1)) (u z) (η (z.2, z.1))
    have hd : dot (G z) ((α z.2).mulVec (G z)) =
        dot ((α z.2).mulVec (G z)) (G z) := by
      simp only [dot, mul_comm]
    rw [hd] at hh
    convert hh using 1 <;> simp only [PDE.vecNormSq_eq_sum_sq, euclideanSq, dot, pow_two] <;> ring
  calc
    _ ≤ ∫ z in I ×ˢ U, ((1 / 2 : ℝ) *
        (η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z)) +
        (2 * κ⁻¹) * (u z ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (z.2, z.1)))) :=
      integral_mono_ae hi.abs ((he.const_mul _).add (hs.const_mul _)) (ae_of_all μ hpoint)
    _ = (1 / 2 : ℝ) * (∫ z in I ×ˢ U,
          η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z)) +
        (2 * κ⁻¹) * ∫ z in I ×ˢ U,
          u z ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (z.2, z.1)) := by
      rw [integral_add (he.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hsbound (by positivity : 0 ≤ 2 * κ⁻¹)
      nlinarith


/-- The squared, time-dependent cutoff times the signed solution is an
admissible spatial Sobolev test on almost every time slice. -/
theorem c5_signed_squared_cutoff_sobolev_slices {d : ℕ} {I : Set ℝ}
    {U K : Set (Vec d)} (hU : IsOpen U) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hK : IsCompact K) (hKU : K ⊆ U)
    (hηK : ∀ x ∉ K, ∀ t, η (x, t) = 0) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => η (x, t) ^ 2 * u (t, x))
        (fun x => η (x, t) ^ 2 • G (t, x) +
          u (t, x) • (fun j => 2 * η (x, t) * PDE.parSpaceGrad η (x, t) j)) ∧
      MemLp (fun x => η (x, t) ^ 2 * u (t, x)) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm (η (x, t) ^ 2 • G (t, x) +
        u (t, x) • (fun j => 2 * η (x, t) * PDE.parSpaceGrad η (x, t) j)))
        2 (volume.restrict U) := by
  have hu' : MemLp u 2 ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hu.1
  have hG' : MemLp (fun z => euclideanNorm (G z)) 2
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hu.2.2.1
  filter_upwards [c9_memLp_prod_right_ae _ _ _ hu',
    c9_memLp_prod_right_ae _ _ _ hG', hu.2.2.2.1] with t hut hGt hwt
  obtain ⟨htest, hderiv⟩ := c5_squared_cutoff_spatial_slice_test hη hK hKU hηK t
  have hp := EinsteinFull.c13_native_cutoff_weak_gradient hU _ _ hwt hut hGt _ htest
  simpa only [hderiv] using hp


/-- All terms in the signed cutoff energy calculation have integrable spatial
slices, including the actual density in the time term. -/
theorem c5_weighted_cutoff_energy_integrable_slices {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ} {M R : ℝ}
    (hη : ContDiff ℝ 1 η) (hηt : Continuous (PDE.parTimeDeriv η))
    (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    (_hM : 0 ≤ M) (ht : ∀ z, |PDE.parTimeDeriv η z| ≤ M)
    (hR : 0 ≤ R) (hgrad : ∀ z, PDE.vecNormSq (PDE.parSpaceGrad η z) ≤ R ^ 2) :
    ∀ᵐ t ∂volume.restrict I,
      Integrable (fun x => η (x, t) ^ 2 * (ρ x * u (t, x) ^ 2)) (volume.restrict U) ∧
      Integrable (fun x => η (x, t) ^ 2 * dot ((α x).mulVec (G (t, x))) (G (t, x)))
        (volume.restrict U) ∧
      Integrable (fun x => η (x, t) * PDE.parTimeDeriv η (x, t) *
        (ρ x * u (t, x) ^ 2)) (volume.restrict U) ∧
      Integrable (fun x => η (x, t) * u (t, x) *
        dot ((α x).mulVec (G (t, x))) (PDE.parSpaceGrad η (x, t))) (volume.restrict U) := by
  obtain ⟨hm, he⟩ := c5_weighted_caloric_cutoff_integrable hκ h hu hη.continuous hη0 hη1
  have ht' := (c5_weighted_cutoff_time_term_bound hκ h hu hη.continuous hηt
    hη0 hη1 ht).1
  have hx := c5_weighted_cutoff_spatial_cross_integrable_of_norm_bound hκ h hu hη
    hη0 hη1 hR hgrad
  have hp : (volume.restrict I).prod (volume.restrict U) =
      volume.restrict (I ×ˢ U) := by rw [Measure.prod_restrict]; rfl
  rw [← hp] at hm he ht' hx
  filter_upwards [hm.prod_right_ae, he.prod_right_ae, ht'.prod_right_ae,
    hx.prod_right_ae] with t hmt het htt hxt
  exact ⟨hmt, het, htt, hxt⟩

/-- On almost every time slice, the signed spatial cross term is absorbed by
half the cutoff energy and the actual density-weighted mass. -/
theorem c5_weighted_cutoff_cross_slice_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ} {R : ℝ}
    (hη : ContDiff ℝ 1 η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    (hR : 0 ≤ R) (hgrad : ∀ z, PDE.vecNormSq (PDE.parSpaceGrad η z) ≤ R ^ 2) :
    ∀ᵐ t ∂volume.restrict I,
      (∫ x in U, |2 * η (x, t) * u (t, x) *
        dot ((α x).mulVec (G (t, x))) (PDE.parSpaceGrad η (x, t))|) ≤
      (1 / 2 : ℝ) * (∫ x in U, η (x, t) ^ 2 *
        dot ((α x).mulVec (G (t, x))) (G (t, x))) +
      (2 * κ⁻¹ * (R ^ 2 * κ⁻¹)) * ∫ x in U, ρ x * u (t, x) ^ 2 := by
  have hm := (c5_weighted_caloric_mass_flux_energy_integrable hκ h hu).1
  have he := (c5_weighted_caloric_cutoff_integrable hκ h hu hη.continuous hη0 hη1).2
  have hx := c5_weighted_cutoff_spatial_cross_integrable_of_norm_bound hκ h hu hη
    hη0 hη1 hR hgrad
  have hs := (c5_weighted_cutoff_spatial_mass_bound hκ h hu hη (sq_nonneg R) hgrad).1
  have hp : (volume.restrict I).prod (volume.restrict U) =
      volume.restrict (I ×ˢ U) := by rw [Measure.prod_restrict]; rfl
  rw [← hp] at hm he hx hs
  filter_upwards [hm.prod_right_ae, he.prod_right_ae, hx.prod_right_ae,
    hs.prod_right_ae] with t hmt het hxt hst
  have hpoint (x : Vec d) :
      |2 * η (x, t) * u (t, x) *
        dot ((α x).mulVec (G (t, x))) (PDE.parSpaceGrad η (x, t))| ≤
      (1 / 2 : ℝ) * (η (x, t) ^ 2 * dot ((α x).mulVec (G (t, x))) (G (t, x))) +
      (2 * κ⁻¹) * (u (t, x) ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (x, t))) := by
    have hh := c5_weighted_signed_cutoff_cross_bound hκ h x (G (t, x))
      (PDE.parSpaceGrad η (x, t)) (u (t, x)) (η (x, t))
    have hd : dot (G (t, x)) ((α x).mulVec (G (t, x))) =
        dot ((α x).mulVec (G (t, x))) (G (t, x)) := by simp only [dot, mul_comm]
    rw [hd] at hh
    convert hh using 1 <;> simp only [PDE.vecNormSq_eq_sum_sq, euclideanSq, dot, pow_two] <;> ring
  have hmpt (x : Vec d) : u (t, x) ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (x, t)) ≤
      (R ^ 2 * κ⁻¹) * (ρ x * u (t, x) ^ 2) := by
    have hsq := sq_nonneg (u (t, x))
    have hr := mul_le_mul_of_nonneg_right (h.2.2 x).1 hsq
    have hr' := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hκ.le)
    have hinv : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ.ne'
    have hu' : u (t, x) ^ 2 ≤ κ⁻¹ * (ρ x * u (t, x) ^ 2) := by nlinarith [hinv]
    have hh := mul_le_mul_of_nonneg_left (hgrad (x, t)) hsq
    have hk := mul_le_mul_of_nonneg_left hu' (sq_nonneg R)
    nlinarith
  have hsm : (∫ x in U, u (t, x) ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (x, t))) ≤
      (R ^ 2 * κ⁻¹) * ∫ x in U, ρ x * u (t, x) ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono_ae hst (hmt.const_mul _) (ae_of_all _ hmpt)
  have hcross : Integrable (fun x => 2 * η (x, t) * u (t, x) *
      dot ((α x).mulVec (G (t, x))) (PDE.parSpaceGrad η (x, t))) (volume.restrict U) := by
    convert hxt.const_mul 2 using 1 <;> ring
  calc
    _ ≤ ∫ x in U, ((1 / 2 : ℝ) * (η (x, t) ^ 2 *
        dot ((α x).mulVec (G (t, x))) (G (t, x))) +
      (2 * κ⁻¹) * (u (t, x) ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (x, t)))) :=
      integral_mono_ae hcross.abs ((het.const_mul _).add (hst.const_mul _)) (ae_of_all _ hpoint)
    _ = (1 / 2 : ℝ) * (∫ x in U, η (x, t) ^ 2 *
          dot ((α x).mulVec (G (t, x))) (G (t, x))) +
        (2 * κ⁻¹) * ∫ x in U, u (t, x) ^ 2 * PDE.vecNormSq (PDE.parSpaceGrad η (x, t)) := by
      rw [integral_add (het.const_mul _) (hst.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hsm (by positivity : 0 ≤ 2 * κ⁻¹)
      nlinarith

/-- The inner-cylinder energy is dominated by cutoff energy on the interior
time cylinder ending at any later terminal slice. -/
theorem c5_inner_energy_le_interior_cutoff_energy {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    {T : ℝ} (hT : (1/4 : ℝ) ≤ T) (hT1 : T ≤ 1)
    {η : Vec d × ℝ → ℝ} (hη : Continuous η) (hη0 : ∀ z, 0 ≤ η z)
    (hη1 : ∀ z, η z ≤ 1)
    (hone : ∀ x ∈ sourceBall 0 (1/2), ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4), η (x, t) = 1) :
    (∫ z in Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2),
      dot ((α z.2).mulVec (G z)) (G z)) ≤
    ∫ z in Set.Ioo (-1/2 : ℝ) T ×ˢ sourceBall 0 1,
      η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z) := by
  let small : Set (ℝ × Vec d) := Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2)
  let middle : Set (ℝ × Vec d) := Set.Ioo (-1/2 : ℝ) T ×ˢ sourceBall 0 1
  let large : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1
  have hsub : small ⊆ middle := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2, hT]⟩, ?_⟩
    change euclideanNorm (x - 0) < 1/2 at hx
    change euclideanNorm (x - 0) < 1
    linarith
  have hmid : middle ⊆ large := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2, hT1]⟩, hx⟩
  have hsmall : MeasurableSet small := by
    apply measurableSet_Ioo.prod
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1/2)]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hpos (z : ℝ × Vec d) : 0 ≤ dot ((α z.2).mulVec (G z)) (G z) := by
    have hc := (h.2.2 z.2).2.2.2 (G z) |>.1
    have he : 0 ≤ κ * euclideanSq (G z) := mul_nonneg hκ.le (PDE.vecNormSq_nonneg _)
    have := he.trans hc
    simpa only [dot, mul_comm] using this
  have hint := (c5_weighted_caloric_cutoff_integrable hκ h hu hη hη0 hη1).2
  have hintmid : Integrable (fun z : ℝ × Vec d => η (z.2, z.1) ^ 2 *
      dot ((α z.2).mulVec (G z)) (G z)) (volume.restrict middle) :=
    hint.mono_measure (Measure.restrict_mono hmid le_rfl)
  calc
    (∫ z in small, dot ((α z.2).mulVec (G z)) (G z)) =
        ∫ z in small, η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z) := by
      apply setIntegral_congr_fun hsmall
      intro z hz
      change dot ((α z.2).mulVec (G z)) (G z) =
        η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z)
      rw [hone z.2 hz.2 z.1 hz.1]
      simp
    _ ≤ ∫ z in middle, η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z) := by
      exact integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (ae_of_all _ fun z => mul_nonneg (sq_nonneg _) (hpos z)) hintmid

/-- The signed cross term absorbs into cutoff energy on any subinterval of
 the caloric time domain, with the mass restricted to that same interval. -/
theorem c5_weighted_cutoff_cross_subinterval_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I J : Set ℝ} {U : Set (Vec d)} (hJI : J ⊆ I)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ} {R : ℝ}
    (hη : ContDiff ℝ 1 η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    (hR : 0 ≤ R) (hgrad : ∀ z, PDE.vecNormSq (PDE.parSpaceGrad η z) ≤ R ^ 2) :
    (∫ z in J ×ˢ U, |2 * η (z.2, z.1) * u z *
      dot ((α z.2).mulVec (G z)) (PDE.parSpaceGrad η (z.2, z.1))|) ≤
    (1 / 2 : ℝ) * (∫ z in J ×ˢ U,
      η (z.2, z.1) ^ 2 * dot ((α z.2).mulVec (G z)) (G z)) +
    (2 * κ⁻¹ * (R ^ 2 * κ⁻¹)) * ∫ z in J ×ˢ U, ρ z.2 * u z ^ 2 := by
  have hm := (c5_weighted_caloric_mass_flux_energy_integrable hκ h hu).1
  have he := (c5_weighted_caloric_cutoff_integrable hκ h hu hη.continuous hη0 hη1).2
  have hx := c5_weighted_cutoff_spatial_cross_integrable_of_norm_bound hκ h hu hη
    hη0 hη1 hR hgrad
  have hmeas : volume.restrict (J ×ˢ U) ≤ volume.restrict (I ×ˢ U) :=
    Measure.restrict_mono (Set.prod_mono hJI (Set.Subset.refl U)) le_rfl
  have hm' := hm.mono_measure hmeas
  have he' := he.mono_measure hmeas
  have hx' := ((hx.const_mul 2).mono_measure hmeas).abs
  have hx'' : Integrable (fun z => |2 * η (z.2, z.1) * u z *
      dot ((α z.2).mulVec (G z)) (PDE.parSpaceGrad η (z.2, z.1))|)
      (volume.restrict (J ×ˢ U)) := by
    convert hx' using 1 <;> ring
  have hp : (volume.restrict J).prod (volume.restrict U) =
      volume.restrict (J ×ˢ U) := by rw [Measure.prod_restrict]; rfl
  rw [← hp] at hm' he' hx''
  have hs := ae_restrict_of_ae_restrict_of_subset hJI
    (c5_weighted_cutoff_cross_slice_bound hκ h hu hη hη0 hη1 hR hgrad)
  have hi := integral_mono_ae hx''.integral_prod_left
    ((he'.integral_prod_left.const_mul (1/2 : ℝ)).add
      (hm'.integral_prod_left.const_mul (2 * κ⁻¹ * (R ^ 2 * κ⁻¹)))) hs
  simp only [Pi.add_apply] at hi
  rw [integral_add (he'.integral_prod_left.const_mul (1/2 : ℝ))
    (hm'.integral_prod_left.const_mul (2 * κ⁻¹ * (R ^ 2 * κ⁻¹))),
    integral_const_mul, integral_const_mul] at hi
  rw [← integral_prod _ hx'', ← integral_prod _ he', ← integral_prod _ hm'] at hi
  simpa only [hp] using hi

/-- The time-cutoff contribution on a subinterval is controlled by the
weighted mass on the original caloric cylinder. -/
theorem c5_weighted_cutoff_time_subinterval_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I J : Set ℝ} {U : Set (Vec d)} (hJI : J ⊆ I)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {η : Vec d × ℝ → ℝ} {M : ℝ}
    (hη : Continuous η) (hηt : Continuous (PDE.parTimeDeriv η))
    (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    (_hM : 0 ≤ M) (ht : ∀ z, |PDE.parTimeDeriv η z| ≤ M) :
    (∫ z in J ×ˢ U, |η (z.2, z.1) * PDE.parTimeDeriv η (z.2, z.1) *
      (ρ z.2 * u z ^ 2)|) ≤ M * ∫ z in I ×ˢ U, ρ z.2 * u z ^ 2 := by
  obtain ⟨hi, hb⟩ := c5_weighted_cutoff_time_term_bound hκ h hu hη hηt hη0 hη1 ht
  exact (integral_mono_measure
    (Measure.restrict_mono (Set.prod_mono hJI (Set.Subset.refl U)) le_rfl)
    (ae_of_all _ fun z => abs_nonneg _) hi.abs).trans hb

/-- A cutoff which vanishes at the initial time has zero weighted initial mass. -/
theorem c5_weighted_cutoff_initial_mass_zero {d : ℕ}
    {ρ : Vec d → ℝ} {u : ℝ × Vec d → ℝ} {η : Vec d × ℝ → ℝ}
    {U : Set (Vec d)} {t : ℝ} (hzero : ∀ x, η (x, t) = 0) :
    (∫ x in U, η (x, t) ^ 2 * (ρ x * u (t, x) ^ 2)) = 0 := by
  have hz : (fun x => η (x, t) ^ 2 * (ρ x * u (t, x) ^ 2)) = 0 := by
    funext x
    simp [hzero x]
  rw [hz]
  simp

/-- Choose two good times on opposite sides of the inner cylinder, with the
first in the region where the fixed cutoff vanishes. -/
theorem c5_exists_good_cutoff_times {p : ℝ → Prop}
    (hp : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1), p t) :
    ∃ s ∈ Set.Ioo (-1/2 : ℝ) (-3/8), ∃ T ∈ Set.Ioo (1/4 : ℝ) (1/2), p s ∧ p T := by
  have hs : Set.Ioo (-1/2 : ℝ) (-3/8) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hT : Set.Ioo (1/4 : ℝ) (1/2) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsm : volume (Set.Ioo (-1/2 : ℝ) (-3/8)) ≠ 0 := by
    norm_num [Real.volume_Ioo, ENNReal.ofReal_eq_zero]
  have hTm : volume (Set.Ioo (1/4 : ℝ) (1/2)) ≠ 0 := by
    norm_num [Real.volume_Ioo, ENNReal.ofReal_eq_zero]
  obtain ⟨s, hs', hps⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hsm
    (ae_restrict_of_ae_restrict_of_subset hs hp)
  obtain ⟨T, hT', hpT⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hTm
    (ae_restrict_of_ae_restrict_of_subset hT hp)
  exact ⟨s, hs', T, hT', hps, hpT⟩

/-- Moving the lower time endpoint through a region where the cutoff vanishes
leaves the cutoff energy unchanged. -/
theorem c5_cutoff_energy_shift_initial_time {d : ℕ}
    {a s T : ℝ} (has : a ≤ s) {U : Set (Vec d)} (hU : MeasurableSet U)
    {η : Vec d × ℝ → ℝ} (hzero : ∀ x t, t ≤ s → η (x, t) = 0)
    (F : ℝ × Vec d → ℝ) :
    (∫ z in Set.Ioo a T ×ˢ U, η (z.2, z.1) ^ 2 * F z) =
      ∫ z in Set.Ioo s T ×ˢ U, η (z.2, z.1) ^ 2 * F z := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Ioo.prod hU)
  · rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨lt_of_le_of_lt has ht.1, ht.2⟩, hx⟩
  · rintro ⟨t, x⟩ ⟨⟨ht, hx⟩, hn⟩
    have hts : t ≤ s := by
      by_contra h
      have hst : s < t := lt_of_not_ge h
      exact hn ⟨⟨hst, ht.2⟩, hx⟩
    simp [hzero x t hts]

/-- Select an early time at which an integrable energy is at most its
    average, while retaining an arbitrary almost-everywhere condition. -/
theorem c5_exists_early_energy_le_average (E : ℝ → ℝ) (P : ℝ → Prop)
    (hE : IntegrableOn E (Set.Ioo (-1 : ℝ) (-1/2)))
    (hP : ∀ᵐ s ∂volume.restrict (Set.Ioo (-1 : ℝ) (-1/2)), P s) :
    ∃ s ∈ Set.Ioo (-1 : ℝ) (-1/2), P s ∧
      E s ≤ 2 * ∫ q in Set.Ioo (-1 : ℝ) (-1/2), E q := by
  classical
  let I : Set ℝ := Set.Ioo (-1 : ℝ) (-1/2)
  let μ : Measure ℝ := volume.restrict I
  have hμ : μ ≠ 0 := by
    apply Measure.measure_univ_ne_zero.mp
    norm_num [μ, I, Real.volume_Ioo]
  have hgood : ∀ᵐ s ∂μ, s ∈ I ∧ P s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hP] with s hs hp
    exact ⟨hs, hp⟩
  have hnull : μ {s | ¬(s ∈ I ∧ P s)} = 0 := ae_iff.mp hgood
  obtain ⟨s, hs, hle⟩ := exists_notMem_null_le_average hμ hE hnull
  have hs' : s ∈ I ∧ P s := by simpa only [Set.mem_setOf_eq, not_not] using hs
  have havg : (⨍ q in I, E q) = 2 * ∫ q in I, E q := by
    rw [setAverage_eq]
    norm_num [I, Measure.real, Real.volume_Ioo]
  refine ⟨s, hs'.1, hs'.2, ?_⟩
  simpa only [μ, havg] using hle

/-- Select a time in any nonempty bounded interval at which an integrable
energy does not exceed its average, while retaining an a.e. condition. -/
theorem c5_exists_interval_energy_le_average {a b : ℝ} (hab : a < b)
    (E : ℝ → ℝ) (P : ℝ → Prop)
    (hE : IntegrableOn E (Set.Ioo a b))
    (hP : ∀ᵐ s ∂volume.restrict (Set.Ioo a b), P s) :
    ∃ s ∈ Set.Ioo a b, P s ∧
      E s ≤ (b - a)⁻¹ * ∫ q in Set.Ioo a b, E q := by
  classical
  let I : Set ℝ := Set.Ioo a b
  let μ : Measure ℝ := volume.restrict I
  have hμ : μ ≠ 0 := by
    apply Measure.measure_univ_ne_zero.mp
    simp only [μ, I, Measure.restrict_apply_univ, Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hgood : ∀ᵐ s ∂μ, s ∈ I ∧ P s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hP] with s hs hp
    exact ⟨hs, hp⟩
  have hnull : μ {s | ¬(s ∈ I ∧ P s)} = 0 := ae_iff.mp hgood
  obtain ⟨s, hs, hle⟩ := exists_notMem_null_le_average hμ hE hnull
  have hs' : s ∈ I ∧ P s := by simpa only [Set.mem_setOf_eq, not_not] using hs
  have havg : (⨍ q in I, E q) = (b - a)⁻¹ * ∫ q in I, E q := by
    rw [setAverage_eq]
    simp only [I, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), smul_eq_mul]
  exact ⟨s, hs'.1, hs'.2, by simpa only [μ, havg] using hle⟩

/-- An early average bound and a forward increment bound control the
    essential supremum of a later energy representative. -/
theorem c5_later_energy_essSup_le_of_early_average
    (E F : ℝ → ℝ) (M A : ℝ)
    (hE : IntegrableOn E (Set.Ioo (-1 : ℝ) (-1/2)))
    (havg : (∫ q in Set.Ioo (-1 : ℝ) (-1/2), E q) ≤ M)
    (hincr : ∀ s ∈ Set.Ioo (-1 : ℝ) (-1/2),
      ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4), E t ≤ E s + A * M)
    (hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4)), F t ≤ E t) :
    essSup (fun t => ENNReal.ofReal (F t))
      (volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4))) ≤
      ENNReal.ofReal ((2 + A) * M) := by
  obtain ⟨s, hs, _, hsel⟩ :=
    c5_exists_early_energy_le_average E (fun _ => True) hE (ae_of_all _ fun _ => trivial)
  letI : (ae (volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4)))).NeBot :=
    ae_restrict_neBot.mpr (by norm_num [Real.volume_Ioo])
  apply essSup_le_of_ae_le _ ?_ (Filter.isCoboundedUnder_le_of_le _ (x := 0) (fun _ => bot_le))
  filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with t ht hti
  apply ENNReal.ofReal_le_ofReal
  have hi := hincr s hs t hti
  nlinarith


/-- An interval-average bound and a pointwise increment bound control the
essential supremum on another nonempty interval. -/
theorem c5_interval_energy_essSup_le_of_average
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (E F : ℝ → ℝ) (M A : ℝ)
    (hE : IntegrableOn E (Set.Ioo a b))
    (havg : (∫ q in Set.Ioo a b, E q) ≤ M)
    (hincr : ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo c d, E t ≤ E s + A * M)
    (hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo c d), F t ≤ E t) :
    essSup (fun t => ENNReal.ofReal (F t)) (volume.restrict (Set.Ioo c d)) ≤
      ENNReal.ofReal (((b - a)⁻¹ + A) * M) := by
  obtain ⟨s, hs, _, hsel⟩ :=
    c5_exists_interval_energy_le_average hab E (fun _ => True) hE
      (ae_of_all _ fun _ => trivial)
  have havg' := mul_le_mul_of_nonneg_left havg (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  letI : (ae (volume.restrict (Set.Ioo c d))).NeBot :=
    ae_restrict_neBot.mpr (by
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd)).ne')
  apply essSup_le_of_ae_le _ ?_ (Filter.isCoboundedUnder_le_of_le _ (x := 0) (fun _ => bot_le))
  filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with t ht hti
  apply ENNReal.ofReal_le_ofReal
  have hi := hincr s hs t hti
  nlinarith

/-- A common initial time selected by an interval average controls both the
later energy and the dissipation in a forward energy inequality. -/
theorem c5_interval_energy_and_dissipation_of_average
    {a b c d : ℝ} (hab : a < b)
    (E : ℝ → ℝ) (D F : ℝ → ℝ → ℝ) (P : ℝ → Prop) (M A : ℝ)
    (hA : 0 ≤ A)
    (hE : IntegrableOn E (Set.Ioo a b))
    (hP : ∀ᵐ s ∂volume.restrict (Set.Ioo a b), P s)
    (havg : (∫ q in Set.Ioo a b, E q) ≤ M)
    (henergy : ∀ s ∈ Set.Ioo a b, P s → ∀ t ∈ Set.Ioo c d,
      E t + (1/2 : ℝ) * D s t ≤ E s + A * F s t)
    (hforce : ∀ s ∈ Set.Ioo a b, P s → ∀ t ∈ Set.Ioo c d, F s t ≤ M)
    (hnonneg : ∀ s ∈ Set.Ioo a b, P s → ∀ t ∈ Set.Ioo c d,
      0 ≤ E t ∧ 0 ≤ D s t) :
    ∃ s ∈ Set.Ioo a b, P s ∧ ∀ t ∈ Set.Ioo c d,
      E t ≤ ((b-a)⁻¹ + A) * M ∧
      D s t ≤ 2 * (((b-a)⁻¹ + A) * M) := by
  obtain ⟨s, hs, hp, hsel⟩ := c5_exists_interval_energy_le_average hab E P hE hP
  have havg' := mul_le_mul_of_nonneg_left havg (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  refine ⟨s, hs, hp, ?_⟩
  intro t ht
  have he := henergy s hs hp t ht
  have hf := mul_le_mul_of_nonneg_left (hforce s hs hp t ht) hA
  obtain ⟨het, hdt⟩ := hnonneg s hs hp t ht
  constructor <;> nlinarith

/-- Both signed truncations are bounded uniformly by the regularized moment. -/
theorem c5_symmetric_truncated_power_le_regularized {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s) ≤
      2 * Real.rpow (|s| + ε) p := by
  have hpos := c5_all_real_truncated_power_le_abs hp hε n s
  have hneg := c5_all_real_truncated_power_le_abs hp hε n (-s)
  simp only [abs_neg] at hneg
  linarith

/-- The baseline removed from the symmetric energy is controlled by the same
regularized moment. -/
theorem c5_symmetric_truncated_power_baseline_le_regularized {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    2 * powF p ε (n : ℝ) 0 ≤ 2 * Real.rpow (|s| + ε) p := by
  have hbase := c5_all_real_truncated_power_le_abs hp hε n 0
  simp only [abs_zero, zero_add] at hbase
  have hmono := Real.rpow_le_rpow hε.le (show ε ≤ |s| + ε by linarith [abs_nonneg s])
    (by linarith : 0 ≤ p)
  change Real.rpow ε p ≤ Real.rpow (|s| + ε) p at hmono
  linarith

end EinsteinFull.Calculus
