import EinsteinFull.Calculus.C8TubeWeightedParabolicSobolev
import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2
import PDEFoundation.Measure.BallVolume
import PDEFoundation.Monotonicity.Core.RellichSphere
import PDEFoundation.Sobolev.OneDimensional.WeakPrimitiveRepresentation
import EllipticRegularity.Parabolic.WeakHarnack.WeightedPoincareCutoff

open MeasureTheory Filter EinsteinRelation EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The source ball agrees with the library's Euclidean ball at positive radius. -/
theorem c8_sourceBall_eq_euclideanBall {d : ℕ} (x : Vec d) {r : ℝ} (hr : 0 < r) :
    sourceBall x r = PDE.euclideanBall x r := by
  ext y
  change Real.sqrt (EinsteinRelation.euclideanSq (y - x)) < r ↔
    PDE.vecNormSq (y - x) < r ^ 2
  rw [Real.sqrt_lt' hr]
  rfl

/-- A fixed smooth cutoff is supported strictly inside the source ball. -/
theorem c8_radial_cutoff_properties (d : ℕ) :
    let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
    ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ sourceBall (0 : Vec d) 1 ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ PDE.euclideanBall (0 : Vec d) (3 / 4), χ x = 1) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x v : Vec d,
        |fderiv ℝ χ x v| ≤ C * PDE.vecEuclideanNorm v := by
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  have hsupport : tsupport χ ⊆ PDE.euclideanClosedBall (0 : Vec d) (7 / 8) := by
    apply closure_minimal _ (PDE.isClosed_euclideanClosedBall 0 (7 / 8))
    intro x hx
    by_contra hxc
    have hxo : x ∉ PDE.euclideanBall (0 : Vec d) (7 / 8) := by
      intro hxball
      exact hxc (PDE.euclideanBall_subset_euclideanClosedBall (0 : Vec d) (7 / 8) hxball)
    exact hx (PDE.Parabolic.WeakHarnack.radialCutoff_eq_zero hxo)
  have hcompact : HasCompactSupport χ :=
    (PDE.isCompact_euclideanClosedBall (0 : Vec d) (by norm_num)).of_isClosed_subset
      (isClosed_tsupport χ) hsupport
  refine ⟨PDE.Parabolic.WeakHarnack.radialCutoff_contDiff d, hcompact, ?_, ?_, ?_,
    PDE.Parabolic.WeakHarnack.radialCutoff_fderiv_bound d⟩
  · rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact hsupport.trans (PDE.euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num))
  · intro x
    exact ⟨PDE.Parabolic.WeakHarnack.radialCutoff_nonneg x,
      PDE.Parabolic.WeakHarnack.radialCutoff_le_one x⟩
  · intro x hx
    exact PDE.Parabolic.WeakHarnack.radialCutoff_eq_one hx

/-- The cutoff has uniformly positive mass against every admissible density. -/
theorem c8_radial_cutoff_density_mass {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal ≤
      ∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x := by
  let B := sourceBall (0 : Vec d) 1
  let A := PDE.euclideanBall (0 : Vec d) (3 / 4)
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  have hAB : A ⊆ B := by
    dsimp [A, B]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.euclideanBall_mono (by norm_num) (by norm_num)
  have hfinite : IsFiniteMeasure (volume.restrict B) := by
    apply isFiniteMeasure_restrict.mpr
    dsimp [B]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  have hpoint (x : Vec d) : 0 ≤ ρ x * χ x ∧ ρ x * χ x ≤ κ⁻¹ := by
    have hρ := (hell.2.2 x)
    have hχ := (c8_radial_cutoff_properties d).2.2.2.1 x
    constructor
    · exact mul_nonneg (le_trans hκ.le hρ.1) hχ.1
    · calc
        ρ x * χ x ≤ ρ x * 1 := mul_le_mul_of_nonneg_left hχ.2 (le_trans hκ.le hρ.1)
        _ ≤ κ⁻¹ := by simpa using hρ.2.1
  have hi : IntegrableOn (fun x => ρ x * χ x) B := by
    apply (integrable_const κ⁻¹).mono'
      ((hell.1.mul (c8_radial_cutoff_properties d).1.continuous.measurable).aestronglyMeasurable)
    filter_upwards [] with x
    change |ρ x * χ x| ≤ κ⁻¹
    rw [abs_of_nonneg (hpoint x).1]
    exact (hpoint x).2
  have hfiniteA : IsFiniteMeasure (volume.restrict A) := by
    apply isFiniteMeasure_restrict.mpr
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  have hsmall : κ * (volume A).toReal ≤ ∫ x in A, ρ x * χ x := by
    have hm : (∫ _x in A, κ) ≤ ∫ x in A, ρ x * χ x := by
      apply setIntegral_mono_on (integrable_const κ) (hi.mono_set hAB)
        (PDE.isOpen_euclideanBall 0 (3 / 4)).measurableSet
      intro x hx
      have hχ : χ x = 1 := (c8_radial_cutoff_properties d).2.2.2.2.1 x hx
      simpa [hχ] using (hell.2.2 x).1
    simpa [setIntegral_const, smul_eq_mul, Measure.real, mul_comm] using hm
  calc
    κ * (volume A).toReal ≤ ∫ x in A, ρ x * χ x := hsmall
    _ ≤ ∫ x in B, ρ x * χ x :=
      setIntegral_mono_set hi (ae_of_all _ fun x => (hpoint x).1)
        (ae_of_all _ fun x hx => hAB hx)

/-- In particular the cutoff's density mass is strictly positive. -/
theorem c8_radial_cutoff_density_mass_pos {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    0 < ∫ x in sourceBall (0 : Vec d) 1,
      ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x :=
  lt_of_lt_of_le (mul_pos hκ (PDE.volume_euclideanBall_toReal_pos 0 (by norm_num)))
    (c8_radial_cutoff_density_mass hκ hell)

/-- On a finite nonzero measure space the mean minimizes squared deviation. -/
theorem c8_integral_sq_sub_mean_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : (μ Set.univ).toReal ≠ 0)
    {f : X → ℝ} (hf : MemLp f 2 μ) (a : ℝ) :
    (∫ x, (f x - (μ Set.univ).toReal⁻¹ * ∫ y, f y ∂μ) ^ 2 ∂μ) ≤
      ∫ x, (f x - a) ^ 2 ∂μ := by
  let c := (μ Set.univ).toReal⁻¹ * ∫ y, f y ∂μ
  have hc : ∫ x, (f x - c) * (1 : ℝ) ∂μ = 0 := by
    simp only [mul_one]
    rw [integral_sub (hf.integrable one_le_two) (integrable_const c), integral_const]
    simp only [smul_eq_mul, Measure.real]
    dsimp [c]
    field_simp
    ring
  have h := PDE.Parabolic.WeakHarnack.weighted_sq_sub_eq (μ := μ)
    (ρ := fun _ => (1 : ℝ)) hf measurable_const (fun _ => zero_le_one)
    (fun _ => le_rfl) a hc
  have hnonneg : 0 ≤ (c - a) ^ 2 * ∫ _ : X, (1 : ℝ) ∂μ := by positivity
  simp only [mul_one] at h
  dsimp only [c] at hnonneg h
  linarith

/-- Spatial oscillation about the ball average is controlled on almost every slice. -/
theorem c8_native_ae_slice_poincare {d : ℕ} {I : Set ℝ}
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (I ×ˢ sourceBall 0 1)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (I ×ˢ sourceBall 0 1)))
    (hw : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient (sourceBall 0 1) (fun x => u (t, x)) (fun x => G (t, x))) :
    ∀ᵐ t ∂volume.restrict I,
      (∫ x in sourceBall 0 1, (u (t,x) - PDE.integralAverage (sourceBall 0 1)
        (fun x => u (t,x))) ^ 2) ≤
      ((2 : ℝ) ^ d * 2) ^ 2 * ∫ x in sourceBall 0 1, euclideanSq (G (t,x)) := by
  have hb : sourceBall (0 : Vec d) 1 = PDE.euclideanBall 0 1 :=
    c8_sourceBall_eq_euclideanBall 0 (by norm_num)
  have hopen : IsOpen (sourceBall (0 : Vec d) 1) := by
    rw [hb]
    exact PDE.isOpen_euclideanBall 0 1
  filter_upwards [c8_native_ae_slice_h1 hopen u G hu hG hw] with t ht
  obtain ⟨v, hv, hg⟩ := ht
  have h := PDE.centeredPoincare_sq_on_boundedConvexSubdomain v
    (by rw [hb]; exact PDE.isOpenBoundedConvexDomain_euclideanBall 0 (by norm_num))
    (Set.Subset.rfl)
    (by rw [hb]; simpa using PDE.hasEuclideanDiameterLE_euclideanBall (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
    (by norm_num) (by rw [hb]; exact PDE.euclideanBall_nonempty 0 (by norm_num))
  simpa only [hv, hg, PDE.vecNormSq, PDE.vecDot, euclideanSq, dot] using h

/-- Separated tests give the literal weighted mass and flux identity. -/
theorem c8_caloric_separated_test {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) {θ : ℝ → ℝ} {χ : Vec d → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hcθ : HasCompactSupport θ) (hcχ : HasCompactSupport χ)
    (hsθ : tsupport θ ⊆ interior I) (hsχ : tsupport χ ⊆ U) :
    (∫ z in I ×ˢ U,
      -(ρ z.2 * u z) * (deriv θ z.1 * χ z.2) +
        dot ((α z.2).mulVec (G z)) (fun j => θ z.1 * fderiv ℝ χ z.2 (unitVector j))) = 0 := by
  let ψ : ℝ × Vec d → ℝ := fun z => θ z.1 * χ z.2
  have hs : tsupport ψ ⊆ tsupport θ ×ˢ tsupport χ := by
    show closure _ ⊆ closure (Function.support θ) ×ˢ closure (Function.support χ)
    rw [← closure_prod_eq]
    apply closure_mono
    intro z hz
    change θ z.1 * χ z.2 ≠ 0 at hz
    simp only [ne_eq, mul_eq_zero, not_or] at hz
    exact ⟨hz.1, hz.2⟩
  have hc : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset (hcθ.prod hcχ) (isClosed_tsupport ψ) hs
  have hd (z : ℝ × Vec d) : HasFDerivAt ψ
      (χ z.2 • (deriv θ z.1 • ContinuousLinearMap.fst ℝ ℝ (Vec d)) +
        θ z.1 • (fderiv ℝ χ z.2).comp (ContinuousLinearMap.snd ℝ ℝ (Vec d))) z := by
    have h1 := ((hθ.differentiable (by norm_num) z.1).hasDerivAt).hasFDerivAt.comp z
      (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := Vec d) (p := z))
    have h2 := ((hχ.differentiable (by norm_num) z.2).hasFDerivAt).comp z
      (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := Vec d) (p := z))
    exact h1.mul h2 |>.congr_fderiv (ContinuousLinearMap.ext fun v => by simp [mul_comm, add_comm])
  have ht := hu.2.2.2.2 ψ ((hθ.comp contDiff_fst).mul (hχ.comp contDiff_snd)) hc
    (hs.trans (Set.prod_mono hsθ hsχ))
  convert ht using 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [(hd z).fderiv]
  simp [mul_comm]

/-- Each coordinate of the actual elliptic flux is square integrable. -/
theorem c8_weighted_caloric_flux_memLp {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
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
      change ‖G z i‖ ≤ euclideanNorm (G z)
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (G z)) i))
  have hg : ∀ i, MemLp (fun z => G z i) 2 μ := memLp_pi_iff.mp hG
  intro i
  simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply] using
    memLp_finsetSum Finset.univ (fun j _ => (hαtop i j).mul (hg j))

/-- The cutoff-weighted mass and cutoff flux are square integrable on the cylinder. -/
theorem c8_caloric_cutoff_mass_flux_memLp {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) :
    let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
    MemLp (fun z => ρ z.2 * u z * χ z.2) 2 (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => dot ((α z.2).mulVec (G z))
      (fun j => fderiv ℝ χ z.2 (unitVector j))) 2 (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  have hρ : MemLp (fun z : ℝ × Vec d => ρ z.2) ∞ μ := by
    apply memLp_top_of_bound (hell.1.comp measurable_snd).aestronglyMeasurable κ⁻¹
    exact ae_of_all μ (fun z => by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans (hell.2.2 z.2).1)] using
        (hell.2.2 z.2).2.1)
  have hχ : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ μ := by
    apply memLp_top_of_bound
      ((c8_radial_cutoff_properties d).1.continuous.measurable.comp measurable_snd).aestronglyMeasurable 1
    exact ae_of_all μ (fun z => by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg ((c8_radial_cutoff_properties d).2.2.2.1 z.2).1] using
        ((c8_radial_cutoff_properties d).2.2.2.1 z.2).2)
  obtain ⟨C, hC, hbound⟩ := (c8_radial_cutoff_properties d).2.2.2.2.2
  have hd (i : Fin d) : MemLp (fun z : ℝ × Vec d => fderiv ℝ χ z.2 (unitVector i)) ∞ μ := by
    apply memLp_top_of_bound
      ((((c8_radial_cutoff_properties d).1.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.comp
        measurable_snd).aestronglyMeasurable C
    apply ae_of_all
    intro z
    have hv : PDE.vecEuclideanNorm (unitVector i) = 1 := by
      simpa [PDE.basisVec, unitVector] using PDE.vecEuclideanNorm_basisVec i
    simpa only [Function.comp_apply, Real.norm_eq_abs, hv, mul_one] using hbound z.2 (unitVector i)
  refine ⟨?_, ?_⟩
  · have hm : MemLp (fun z : ℝ × Vec d => u z * ρ z.2) 2 μ := hu.1.mul hρ
    have hp : MemLp (fun z : ℝ × Vec d => (u z * ρ z.2) * χ z.2) 2 μ := hm.mul hχ
    convert hp using 1 <;> funext z <;> simp [χ, mul_comm (ρ z.2) (u z)]
  · change MemLp (fun z => ∑ i : Fin d, ((α z.2).mulVec (G z)) i *
      fderiv ℝ χ z.2 (unitVector i)) 2 μ
    exact memLp_finsetSum Finset.univ (fun i _ => (c8_weighted_caloric_flux_memLp hκ hell hu i).mul (hd i))

/-- Cutoff mass and flux have integrable temporal pairings, with Fubini identities. -/
theorem c8_caloric_cutoff_pairing_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G) :
    let I := Set.Ioo (-1 : ℝ) 1
    let U := sourceBall (0 : Vec d) 1
    let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
    let M := fun z : ℝ × Vec d => ρ z.2 * u z * χ z.2
    let F := fun z : ℝ × Vec d => dot ((α z.2).mulVec (G z))
      (fun j => fderiv ℝ χ z.2 (unitVector j))
    IntegrableOn (fun t => ∫ x in U, M (t, x)) I ∧
    IntegrableOn (fun t => ∫ x in U, F (t, x)) I ∧
    (∫ t in I, ∫ x in U, M (t, x)) = ∫ z in I ×ˢ U, M z ∧
    (∫ t in I, ∫ x in U, F (t, x)) = ∫ z in I ×ˢ U, F z := by
  let I := Set.Ioo (-1 : ℝ) 1
  let U := sourceBall (0 : Vec d) 1
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  let M := fun z : ℝ × Vec d => ρ z.2 * u z * χ z.2
  let F := fun z : ℝ × Vec d => dot ((α z.2).mulVec (G z))
    (fun j => fderiv ℝ χ z.2 (unitVector j))
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    dsimp [U]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
  letI : IsFiniteMeasure (volume.restrict (I ×ˢ U)) := by
    have hf : IsFiniteMeasure ((volume.restrict I).prod (volume.restrict U)) := inferInstance
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hf
    exact hf
  obtain ⟨hM, hF⟩ := c8_caloric_cutoff_mass_flux_memLp hκ hell hu
  have hMi : Integrable M (volume.restrict (I ×ˢ U)) := hM.integrable (by norm_num)
  have hFi : Integrable F (volume.restrict (I ×ˢ U)) := hF.integrable (by norm_num)
  have hMp : Integrable M ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hMi
  have hFp : Integrable F ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hFi
  refine ⟨hMp.integral_prod_left, hFp.integral_prod_left, ?_, ?_⟩
  · simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using (integral_prod M hMp).symm
  · simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using (integral_prod F hFp).symm

/-- Testing caloricity against a separated cutoff gives the one-dimensional mass identity. -/
theorem c8_caloric_cutoff_time_test {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hcθ : HasCompactSupport θ)
    (hsθ : tsupport θ ⊆ Set.Ioo (-1) 1) :
    let I := Set.Ioo (-1 : ℝ) 1
    let U := sourceBall (0 : Vec d) 1
    let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
    (∫ t in I, -(∫ x in U, ρ x * u (t, x) * χ x) * deriv θ t +
      (∫ x in U, dot ((α x).mulVec (G (t, x)))
        (fun j => fderiv ℝ χ x (unitVector j))) * θ t) = 0 := by
  let I := Set.Ioo (-1 : ℝ) 1
  let U := sourceBall (0 : Vec d) 1
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  let M := fun z : ℝ × Vec d => ρ z.2 * u z * χ z.2
  let F := fun z : ℝ × Vec d => dot ((α z.2).mulVec (G z))
    (fun j => fderiv ℝ χ z.2 (unitVector j))
  let μ := volume.restrict (I ×ˢ U)
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    dsimp [U]; rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
  letI : IsFiniteMeasure μ := by
    have hf : IsFiniteMeasure ((volume.restrict I).prod (volume.restrict U)) := inferInstance
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hf
    exact hf
  obtain ⟨hM, hF⟩ := c8_caloric_cutoff_mass_flux_memLp hκ hell hu
  have hMi : Integrable M μ := hM.integrable (by norm_num)
  have hFi : Integrable F μ := hF.integrable (by norm_num)
  obtain ⟨B, hB⟩ := hθ.continuous.bounded_above_of_compact_support hcθ
  obtain ⟨D, hD⟩ := (hθ.continuous_deriv (by simp)).bounded_above_of_compact_support hcθ.deriv
  have ht : MemLp (fun z : ℝ × Vec d => θ z.1) ∞ μ := by
    apply memLp_top_of_bound (hθ.continuous.measurable.comp measurable_fst).aestronglyMeasurable B
    exact ae_of_all μ (fun z => by simpa only [Function.comp_apply] using hB z.1)
  have hd : MemLp (fun z : ℝ × Vec d => deriv θ z.1) ∞ μ := by
    apply memLp_top_of_bound ((hθ.continuous_deriv (by simp)).measurable.comp measurable_fst).aestronglyMeasurable D
    exact ae_of_all μ (fun z => by simpa only [Function.comp_apply] using hD z.1)
  have hp : Integrable (fun z : ℝ × Vec d => -(M z * deriv θ z.1)) μ := by
    convert (hMi.mul_of_top_right hd).neg using 1 <;> ext z <;> simp [Pi.mul_apply, mul_comm]
  have hq : Integrable (fun z : ℝ × Vec d => F z * θ z.1) μ := by
    convert hFi.mul_of_top_right ht using 1 <;> ext z <;> simp [Pi.mul_apply, mul_comm]
  have hpq : Integrable (fun z : ℝ × Vec d => -(M z * deriv θ z.1) + F z * θ z.1)
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hp.add hq
  have heq (z : ℝ × Vec d) :
      -(ρ z.2 * u z) * (deriv θ z.1 * χ z.2) +
        dot ((α z.2).mulVec (G z)) (fun j => θ z.1 * fderiv ℝ χ z.2 (unitVector j)) =
        -(M z * deriv θ z.1) + F z * θ z.1 := by
    dsimp [M, F, dot]
    rw [Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  have hw := c8_caloric_separated_test hu hθ (c8_radial_cutoff_properties d).1 hcθ
    (c8_radial_cutoff_properties d).2.1 (by simpa only [interior_Ioo] using hsθ)
    (c8_radial_cutoff_properties d).2.2.1
  have hz : (∫ z in I ×ˢ U, -(M z * deriv θ z.1) + F z * θ z.1) = 0 := by
    convert hw using 1
    apply integral_congr_ae
    exact ae_of_all _ fun z => (heq z).symm
  have hiter := (integral_prod _ hpq).symm
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hiter
  rw [hz] at hiter
  convert hiter using 1
  apply integral_congr_ae
  filter_upwards [((by simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hp :
    Integrable _ ((volume.restrict I).prod (volume.restrict U))).prod_right_ae),
    ((by simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hq :
    Integrable _ ((volume.restrict I).prod (volume.restrict U))).prod_right_ae)] with t hpt hqt
  rw [integral_add hpt hqt, integral_neg, integral_mul_const, integral_mul_const]
  simp [U, χ, M, F, neg_mul]

/-- The cutoff mass has the negative coefficient-flux pairing as its weak time derivative. -/
theorem c8_caloric_cutoff_hasWeakDeriv {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G) :
    let U := sourceBall (0 : Vec d) 1
    let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
    PDE.HasWeakDerivOnIoo (-1) 1
      (fun t => ∫ x in U, ρ x * u (t, x) * χ x)
      (fun t => -(∫ x in U, dot ((α x).mulVec (G (t, x)))
        (fun j => fderiv ℝ χ x (unitVector j)))) := by
  let U := sourceBall (0 : Vec d) 1
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  let M : ℝ → ℝ := fun t => ∫ x in U, ρ x * u (t, x) * χ x
  let F : ℝ → ℝ := fun t => ∫ x in U, dot ((α x).mulVec (G (t, x)))
    (fun j => fderiv ℝ χ x (unitVector j))
  change PDE.HasWeakDerivOnIoo (-1) 1 M (fun t => -F t)
  unfold PDE.HasWeakDerivOnIoo PDE.HasWeakPartialDerivOn
  intro φ hφ hcompact hsupport
  let θ := PDE.scalarPullbackOne φ
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := PDE.ContDiff.scalarPullbackOne hφ
  have hcθ : HasCompactSupport θ := by
    change HasCompactSupport (φ ∘ PDE.scalarToVecOneContinuousLinearEquiv.toHomeomorph)
    exact hcompact.comp_homeomorph _
  have hsθ : tsupport θ ⊆ Set.Ioo (-1) 1 :=
    PDE.tsupport_scalarPullbackOne_subset_Ioo hsupport
  have hi := c8_caloric_cutoff_time_test hκ hell hu hθ hcθ hsθ
  change (∫ t in Set.Ioo (-1 : ℝ) 1, -M t * deriv θ t + F t * θ t) = 0 at hi
  obtain ⟨hM, hF, _, _⟩ := c8_caloric_cutoff_pairing_integrable hκ hell hu
  change IntegrableOn M (Set.Ioo (-1) 1) at hM
  change IntegrableOn F (Set.Ioo (-1) 1) at hF
  obtain ⟨B, hB⟩ := hθ.continuous.bounded_above_of_compact_support hcθ
  obtain ⟨D, hD⟩ := (hθ.continuous_deriv (by simp)).bounded_above_of_compact_support hcθ.deriv
  have ht : MemLp θ ∞ (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
    memLp_top_of_bound hθ.continuous.aestronglyMeasurable B (ae_of_all _ hB)
  have hd : MemLp (deriv θ) ∞ (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
    memLp_top_of_bound (hθ.continuous_deriv (by simp)).aestronglyMeasurable D (ae_of_all _ hD)
  have hm : IntegrableOn (fun t => -M t * deriv θ t) (Set.Ioo (-1 : ℝ) 1) := by
    have he : (-(deriv θ * M)) = (fun t => -M t * deriv θ t) := by
      funext t
      simp [Pi.mul_apply, mul_comm]
    rw [← he]
    exact (hM.mul_of_top_right hd).neg
  have hf : IntegrableOn (fun t => F t * θ t) (Set.Ioo (-1 : ℝ) 1) := by
    have he : (θ * F) = (fun t => F t * θ t) := by
      funext t
      simp [Pi.mul_apply, mul_comm]
    rw [← he]
    exact hF.mul_of_top_right ht
  have heq : (∫ t in Set.Ioo (-1 : ℝ) 1, M t * deriv θ t) =
      ∫ t in Set.Ioo (-1 : ℝ) 1, F t * θ t := by
    rw [integral_add hm hf] at hi
    have hm' : (∫ t in Set.Ioo (-1 : ℝ) 1, -M t * deriv θ t) =
        -(∫ t in Set.Ioo (-1 : ℝ) 1, M t * deriv θ t) := by
      simp only [neg_mul, integral_neg]
    rw [hm'] at hi
    linarith
  have hleft : (fun x => PDE.liftOneDimensional M x *
      (fderiv ℝ φ x) (PDE.basisVec (0 : Fin 1))) =
      PDE.liftOneDimensional (fun t => M t * deriv θ t) := by
    funext x
    simp only [PDE.liftOneDimensional]
    rw [show deriv θ (PDE.vecOneCoordinate x) =
      (fderiv ℝ φ (PDE.scalarToVecOne (PDE.vecOneCoordinate x)))
        (PDE.basisVec (0 : Fin 1)) from
      PDE.deriv_scalarPullbackOne_eq_native_directional (hφ.of_le (by simp)) _]
    rw [PDE.scalarToVecOne_vecOneCoordinate]
  have hright : (fun x => PDE.liftOneDimensional (fun t => -F t) x * φ x) =
      PDE.liftOneDimensional (fun t => -(F t * θ t)) := by
    funext x
    simp only [PDE.liftOneDimensional, θ, PDE.scalarPullbackOne]
    rw [PDE.scalarToVecOne_vecOneCoordinate]
    simp only [neg_mul]
  rw [hleft, hright, PDE.setIntegral_axisBox_one_eq_setIntegral_Ioo,
    PDE.setIntegral_axisBox_one_eq_setIntegral_Ioo, integral_neg, neg_neg]
  exact heq

/-- Integration over a finite spatial measure preserves time-space square integrability. -/
theorem c8_spatial_integral_memLp {d : ℕ} {μ : Measure ℝ} {ν : Measure (Vec d)}
    [SFinite μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {f : ℝ × Vec d → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun t => ∫ x, f (t, x) ∂ν) 2 μ := by
  have hfi : Integrable f (μ.prod ν) := hf.integrable (by norm_num)
  have hpair : Integrable (fun t => ∫ x, f (t, x) ∂ν) μ := hfi.integral_prod_left
  have hsq : Integrable (fun z => f z ^ 2) (μ.prod ν) := hf.integrable_sq
  let S : ℝ → ℝ := fun t => ∫ x, f (t, x) ^ 2 ∂ν
  have hS : Integrable S μ := hsq.integral_prod_left
  let N : ℝ → ℝ := fun t => Real.sqrt (S t)
  have hNmeas : AEStronglyMeasurable N μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hS.aestronglyMeasurable
  have hSnonneg (t : ℝ) : 0 ≤ S t := integral_nonneg fun x => sq_nonneg _
  have hNsq (t : ℝ) : N t ^ 2 = S t := by
    simp [N, Real.sq_sqrt (hSnonneg t)]
  have hN : MemLp N 2 μ := (memLp_two_iff_integrable_sq hNmeas).2
    (hS.congr (Filter.Eventually.of_forall fun t => (hNsq t).symm))
  have hone : MemLp (fun _ : Vec d => (1 : ℝ)) 2 ν := memLp_const 1
  have hbound : ∀ᵐ t ∂μ, ‖∫ x, f (t, x) ∂ν‖ ≤ ‖hone.toLp _‖ * ‖N t‖ := by
    filter_upwards [hfi.prod_right_ae, hsq.prod_right_ae] with t ht htsq
    have ht2 : MemLp (fun x => f (t, x)) 2 ν :=
      (memLp_two_iff_integrable_sq ht.aestronglyMeasurable).2 htsq
    let ft := ht2.toLp (fun x => f (t, x))
    have hinner : (∫ x, f (t, x) ∂ν) = inner ℝ ft (hone.toLp _) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ht2.coeFn_toLp, hone.coeFn_toLp] with x hx hy
      rw [hx, hy]
      simp
    have hnorm : ‖ft‖ = N t := by
      change ‖ht2.toLp (fun x => f (t, x))‖ = N t
      rw [Lp.norm_toLp]
      have hs := PDE.toReal_eLpNorm_two_sq_eq_integral_sq ht2
      have hn : 0 ≤ (eLpNorm (fun x => f (t, x)) 2 ν).toReal := ENNReal.toReal_nonneg
      dsimp [N, S]
      symm
      rw [Real.sqrt_eq_iff_eq_sq (integral_nonneg fun x => sq_nonneg _) hn]
      exact hs.symm
    rw [Real.norm_eq_abs, hinner]
    calc
      |inner ℝ ft (hone.toLp _)| ≤ ‖ft‖ * ‖hone.toLp _‖ := abs_real_inner_le_norm _ _
      _ = ‖hone.toLp _‖ * ‖N t‖ := by
        rw [hnorm, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        ring
  exact hN.of_le_mul (c := ‖hone.toLp _‖) hpair.aestronglyMeasurable hbound

/-- The literal cutoff mass and flux pairings are square-integrable in time. -/
theorem c8_caloric_cutoff_pairing_memLp {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G) :
    let I := Set.Ioo (-1 : ℝ) 1
    let U := sourceBall (0 : Vec d) 1
    let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
    MemLp (fun t => ∫ x in U, ρ x * u (t, x) * χ x) 2 (volume.restrict I) ∧
    MemLp (fun t => ∫ x in U, dot ((α x).mulVec (G (t, x)))
      (fun j => fderiv ℝ χ x (unitVector j))) 2 (volume.restrict I) := by
  let I := Set.Ioo (-1 : ℝ) 1
  let U := sourceBall (0 : Vec d) 1
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    dsimp [U]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
  obtain ⟨hM, hF⟩ := c8_caloric_cutoff_mass_flux_memLp hκ hell hu
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hM hF
  exact ⟨c8_spatial_integral_memLp hM, c8_spatial_integral_memLp hF⟩

/-- The cutoff mass admits a continuous representative controlled by the flux. -/
theorem c8_caloric_cutoff_mass_representative {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G) :
    let U := sourceBall (0 : Vec d) 1
    let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
    let M := fun t => ∫ x in U, ρ x * u (t, x) * χ x
    let F := fun t => ∫ x in U, dot ((α x).mulVec (G (t, x)))
      (fun j => fderiv ℝ χ x (unitVector j))
    ∃ v : ℝ → ℝ, ContinuousOn v (Set.Icc (-1) 1) ∧
      M =ᵐ[volume.restrict (Set.Ioo (-1) 1)] v ∧
      ∀ s ∈ Set.Icc (-1) 1, ∀ t ∈ Set.Icc (-1) 1, s ≤ t →
        |v t - v s| ^ 2 ≤ (t - s) * ∫ x in Set.Icc s t, |F x| ^ (2 : ℝ) := by
  obtain ⟨hM, hF⟩ := c8_caloric_cutoff_pairing_memLp hκ hell hu
  have hFc := hF.neg
  rw [restrict_Ioo_eq_restrict_Icc] at hFc
  obtain ⟨v, hv, hmv, hinc⟩ :=
    PDE.exists_continuousOn_representative_with_sq_increment_le
      (a := -1) (b := 1) (by norm_num) hM hFc
      (c8_caloric_cutoff_hasWeakDeriv hκ hell hu)
  refine ⟨v, hv, hmv, ?_⟩
  intro s hs t ht hst
  simpa only [Pi.neg_apply, abs_neg] using hinc s hs t ht hst

/-- The cutoff flux has a coefficient-uniform pointwise gradient bound. -/
theorem c8_caloric_cutoff_flux_pointwise (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (x v : Vec d),
      |dot ((α x).mulVec v) (fun j =>
        fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector j))| ≤
        B * euclideanNorm v := by
  obtain ⟨C, hC, hbound⟩ := (c8_radial_cutoff_properties d).2.2.2.2.2
  refine ⟨(d : ℝ) * κ⁻¹ * C, by positivity, ?_⟩
  intro ρ α hell x v
  have hα : IsElliptic κ⁻¹ α := by
    intro y
    simpa only [inv_inv] using (hell.2.2 y).2.2
  have hnorm := Correctors.isElliptic_mulVec_euclideanNorm_le (inv_pos.mpr hκ) hα x v
  have hcoord (i : Fin d) : |((α x).mulVec v) i| ≤ κ⁻¹ * euclideanNorm v := by
    have hp := PiLp.norm_apply_le (WithLp.toLp 2 ((α x).mulVec v) : EuclideanSpace ℝ (Fin d)) i
    rw [TimeChange.euclideanNorm_eq_norm_toLp] at hnorm
    exact (by simpa only [PiLp.toLp_apply, Real.norm_eq_abs] using hp.trans hnorm)
  have hderiv (i : Fin d) :
      |fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector i)| ≤ C := by
    have hv : PDE.vecEuclideanNorm (unitVector i) = 1 := by
      simpa [PDE.basisVec, unitVector] using PDE.vecEuclideanNorm_basisVec i
    simpa only [hv, mul_one] using hbound x (unitVector i)
  have hN : 0 ≤ κ⁻¹ * euclideanNorm v :=
    mul_nonneg (inv_nonneg.mpr hκ.le) (Real.sqrt_nonneg _)
  change |∑ i : Fin d, ((α x).mulVec v) i *
    fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector i)| ≤ _
  calc
    _ ≤ ∑ i : Fin d, |((α x).mulVec v) i *
        fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (κ⁻¹ * euclideanNorm v) * C := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hcoord i) (hderiv i) (abs_nonneg _) hN
    _ = (d : ℝ) * κ⁻¹ * C * euclideanNorm v := by simp; ring

/-- The space-time cutoff-flux energy is controlled by the actual gradient energy. -/
theorem c8_caloric_cutoff_flux_energy (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      let Q := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1
      (∫ z in Q, |dot ((α z.2).mulVec (G z)) (fun j =>
        fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) z.2 (unitVector j))| ^ 2) ≤
      B * ∫ z in Q, euclideanNorm (G z) ^ 2 := by
  obtain ⟨A, hA, hpoint⟩ := c8_caloric_cutoff_flux_pointwise d hκ
  refine ⟨A ^ 2, sq_nonneg _, ?_⟩
  intro ρ α hell u G hu
  let Q := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1
  let F := fun z : ℝ × Vec d => dot ((α z.2).mulVec (G z)) (fun j =>
    fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) z.2 (unitVector j))
  have hF : MemLp F 2 (volume.restrict Q) := (c8_caloric_cutoff_mass_flux_memLp hκ hell hu).2
  have hleft : Integrable (fun z => |F z| ^ 2) (volume.restrict Q) := by
    simpa only [sq_abs] using hF.integrable_sq
  have hright : Integrable (fun z => A ^ 2 * euclideanNorm (G z) ^ 2)
      (volume.restrict Q) := hu.2.2.1.integrable_sq.const_mul _
  change (∫ z in Q, |F z| ^ 2) ≤ A ^ 2 * ∫ z in Q, euclideanNorm (G z) ^ 2
  rw [← integral_const_mul]
  apply integral_mono_ae hleft hright
  filter_upwards [] with z
  have hp := hpoint ρ α hell z.2 (G z)
  have hn : 0 ≤ A * euclideanNorm (G z) := mul_nonneg hA (Real.sqrt_nonneg _)
  have habs : 0 ≤ |F z| := abs_nonneg _
  change |F z| ≤ A * euclideanNorm (G z) at hp
  nlinarith [sq_nonneg (A * euclideanNorm (G z) - |F z|)]

/-- A finite spatial integral satisfies the square-integrated Cauchy--Schwarz bound. -/
theorem c8_spatial_integral_sq_le {d : ℕ} {μ : Measure ℝ} {ν : Measure (Vec d)}
    [SFinite μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {f : ℝ × Vec d → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    (∫ t, (∫ x, f (t, x) ∂ν) ^ 2 ∂μ) ≤
      (ν Set.univ).toReal * ∫ z, f z ^ 2 ∂(μ.prod ν) := by
  have hfi : Integrable f (μ.prod ν) := hf.integrable (by norm_num)
  have hsq : Integrable (fun z => f z ^ 2) (μ.prod ν) := hf.integrable_sq
  have hpair := c8_spatial_integral_memLp hf
  have hS := hsq.integral_prod_left
  have hC : Integrable (fun _ : Vec d => (1 : ℝ) ^ 2) ν := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Vec d => (1 : ℝ)) ν)
  have hpt : ∀ᵐ t ∂μ, (∫ x, f (t, x) ∂ν) ^ 2 ≤
      (ν Set.univ).toReal * ∫ x, f (t, x) ^ 2 ∂ν := by
    filter_upwards [hfi.prod_right_ae, hsq.prod_right_ae] with t ht htsq
    have hm : Integrable (fun x => (1 : ℝ) * f (t, x)) ν := by simpa using ht
    have hc := PDE.integral_mul_sq_le hC htsq hm
    simpa only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one, measureReal_def] using hc
  calc
    (∫ t, (∫ x, f (t, x) ∂ν) ^ 2 ∂μ) ≤
        ∫ t, (ν Set.univ).toReal * (∫ x, f (t, x) ^ 2 ∂ν) ∂μ :=
      integral_mono_ae hpair.integrable_sq (hS.const_mul _) hpt
    _ = (ν Set.univ).toReal * ∫ z, f z ^ 2 ∂(μ.prod ν) := by
      rw [integral_const_mul, integral_prod _ hsq]

/-- The temporal cutoff-flux pairing is bounded by the space-time gradient energy. -/
theorem c8_caloric_cutoff_pairing_energy (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      let I := Set.Ioo (-1 : ℝ) 1
      let U := sourceBall (0 : Vec d) 1
      let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
      (∫ t in I, |∫ x in U, dot ((α x).mulVec (G (t, x)))
        (fun j => fderiv ℝ χ x (unitVector j))| ^ 2) ≤
      B * ∫ z in I ×ˢ U, euclideanNorm (G z) ^ 2 := by
  let I := Set.Ioo (-1 : ℝ) 1
  let U := sourceBall (0 : Vec d) 1
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    dsimp [U]; rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
  obtain ⟨A, hA, henergy⟩ := c8_caloric_cutoff_flux_energy d hκ
  refine ⟨(volume U).toReal * A, mul_nonneg ENNReal.toReal_nonneg hA, ?_⟩
  intro ρ α hell u G hu
  let F := fun z : ℝ × Vec d => dot ((α z.2).mulVec (G z)) (fun j =>
    fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) z.2 (unitVector j))
  have hF : MemLp F 2 ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (c8_caloric_cutoff_mass_flux_memLp hκ hell hu).2
  have hpair := c8_spatial_integral_sq_le hF
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hpair
  have he := henergy ρ α hell u G hu
  change (∫ z in I ×ˢ U, |F z| ^ 2) ≤ A * ∫ z in I ×ˢ U, euclideanNorm (G z) ^ 2 at he
  simp only [sq_abs] at he ⊢
  simp only [Measure.restrict_apply_univ] at hpair
  apply hpair.trans
  calc
    (volume U).toReal * (∫ z in I ×ˢ U, F z ^ 2) ≤
        (volume U).toReal * (A * ∫ z in I ×ˢ U, euclideanNorm (G z) ^ 2) :=
      mul_le_mul_of_nonneg_left he ENNReal.toReal_nonneg
    _ = ((volume U).toReal * A) * ∫ z in I ×ˢ U, euclideanNorm (G z) ^ 2 := by ring


/-- A cutoff-mass representative has uniformly controlled temporal increments. -/
theorem c8_caloric_cutoff_mass_increment (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      let U := sourceBall (0 : Vec d) 1
      let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
      let M := fun t => ∫ x in U, ρ x * u (t, x) * χ x
      ∃ v : ℝ → ℝ, ContinuousOn v (Set.Icc (-1) 1) ∧
        M =ᵐ[volume.restrict (Set.Ioo (-1) 1)] v ∧
        ∀ s ∈ Set.Icc (-1) 1, ∀ t ∈ Set.Icc (-1) 1,
          |v t - v s| ^ 2 ≤ B * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ U,
            euclideanNorm (G z) ^ 2 := by
  obtain ⟨A, hA, henergy⟩ := c8_caloric_cutoff_pairing_energy d hκ
  refine ⟨2 * A, by positivity, ?_⟩
  intro ρ α hell u G hu
  let U := sourceBall (0 : Vec d) 1
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  let F := fun t => ∫ x in U, dot ((α x).mulVec (G (t, x)))
    (fun j => fderiv ℝ χ x (unitVector j))
  obtain ⟨v, hv, hmv, hinc⟩ := c8_caloric_cutoff_mass_representative hκ hell hu
  refine ⟨v, hv, hmv, ?_⟩
  have hF := (c8_caloric_cutoff_pairing_memLp hκ hell hu).2
  have hsq : IntegrableOn (fun t => |F t| ^ (2 : ℝ)) (Set.Icc (-1) 1) := by
    unfold IntegrableOn
    rw [← restrict_Ioo_eq_restrict_Icc]
    simpa only [Real.rpow_two, sq_abs] using hF.integrable_sq
  have hwhole : 0 ≤ ∫ t in Set.Icc (-1 : ℝ) 1, |F t| ^ (2 : ℝ) :=
    integral_nonneg fun t => Real.rpow_nonneg (abs_nonneg _) _
  have hbound (s t : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
      (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hst : s ≤ t) :
      |v t - v s| ^ 2 ≤ 2 * ∫ x in Set.Icc (-1 : ℝ) 1, |F x| ^ (2 : ℝ) := by
    have hsub : Set.Icc s t ⊆ Set.Icc (-1 : ℝ) 1 := Set.Icc_subset_Icc hs.1 ht.2
    have hlocal := setIntegral_mono_set hsq
      (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg (F x)) _) (ae_of_all _ fun _ hx => hsub hx)
    have hlocalnonneg : 0 ≤ ∫ x in Set.Icc s t, |F x| ^ (2 : ℝ) :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    have hlen : t - s ≤ 2 := by linarith [hs.1, ht.2]
    exact (hinc s hs t ht hst).trans (by nlinarith)
  intro s hs t ht
  have hp : |v t - v s| ^ 2 ≤ 2 * ∫ x in Set.Icc (-1 : ℝ) 1, |F x| ^ (2 : ℝ) := by
    rcases le_total s t with hst | hts
    · exact hbound s t hs ht hst
    · simpa only [abs_sub_comm] using hbound t s ht hs hts
  have he := henergy ρ α hell u G hu
  change (∫ t in Set.Ioo (-1 : ℝ) 1, |F t| ^ 2) ≤
    A * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ U, euclideanNorm (G z) ^ 2 at he
  rw [← restrict_Ioo_eq_restrict_Icc] at hp
  simp only [Real.rpow_two] at hp
  nlinarith

/-- The density-weighted cutoff mean has uniformly controlled temporal increments. -/
theorem c8_caloric_cutoff_mean_increment (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      let U := sourceBall (0 : Vec d) 1
      let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
      let D := ∫ x in U, ρ x * χ x
      let M := fun t => D⁻¹ * ∫ x in U, ρ x * u (t, x) * χ x
      ∃ v : ℝ → ℝ, ContinuousOn v (Set.Icc (-1) 1) ∧
        M =ᵐ[volume.restrict (Set.Ioo (-1) 1)] v ∧
        ∀ s ∈ Set.Icc (-1) 1, ∀ t ∈ Set.Icc (-1) 1,
          |v t - v s| ^ 2 ≤ B * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ U,
            euclideanNorm (G z) ^ 2 := by
  let δ := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
  have hδ : 0 < δ := mul_pos hκ (PDE.volume_euclideanBall_toReal_pos 0 (by norm_num))
  obtain ⟨A, hA, hinc⟩ := c8_caloric_cutoff_mass_increment d hκ
  refine ⟨δ⁻¹ ^ 2 * A, mul_nonneg (sq_nonneg _) hA, ?_⟩
  intro ρ α hell u G hu
  let U := sourceBall (0 : Vec d) 1
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  let D := ∫ x in U, ρ x * χ x
  have hD : δ ≤ D := c8_radial_cutoff_density_mass hκ hell
  have hDpos : 0 < D := lt_of_lt_of_le hδ hD
  have hinv : D⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ hDpos hδ).2 hD
  have hinv0 : 0 ≤ D⁻¹ := inv_nonneg.mpr hDpos.le
  obtain ⟨v, hv, hmv, hvinc⟩ := hinc ρ α hell u G hu
  refine ⟨fun t => D⁻¹ * v t, continuousOn_const.mul hv, ?_, ?_⟩
  · filter_upwards [hmv] with t ht
    exact congrArg (fun x : ℝ => D⁻¹ * x) ht
  · intro s hs t ht
    have he : 0 ≤ ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ U, euclideanNorm (G z) ^ 2 :=
      integral_nonneg fun z => sq_nonneg _
    have hV := hvinc s hs t ht
    have hsq : D⁻¹ ^ 2 ≤ δ⁻¹ ^ 2 := by nlinarith [sq_nonneg (δ⁻¹ - D⁻¹)]
    have hdiff : D⁻¹ * v t - D⁻¹ * v s = D⁻¹ * (v t - v s) := by ring
    rw [hdiff, abs_mul, abs_of_nonneg hinv0, mul_pow]
    calc
      D⁻¹ ^ 2 * |v t - v s| ^ 2 ≤ D⁻¹ ^ 2 * (A * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ U,
          euclideanNorm (G z) ^ 2) := mul_le_mul_of_nonneg_left hV (sq_nonneg _)
      _ ≤ δ⁻¹ ^ 2 * (A * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ U,
          euclideanNorm (G z) ^ 2) := mul_le_mul_of_nonneg_right hsq (mul_nonneg hA he)
      _ = δ⁻¹ ^ 2 * A * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ U,
          euclideanNorm (G z) ^ 2 := by ring

/-- Compare an L² function with its weighted mean using an arbitrary center. -/
theorem c8_integral_sq_sub_weighted_mean_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f w : X → ℝ}
    (hf : MemLp f 2 μ) (hw : MemLp w 2 μ)
    (hD : (∫ x, w x ∂μ) ≠ 0) (a : ℝ) :
    let D := ∫ x, w x ∂μ
    let c := D⁻¹ * ∫ x, f x * w x ∂μ
    (∫ x, (f x - c) ^ 2 ∂μ) ≤
      (2 + 2 * (μ Set.univ).toReal * D⁻¹ ^ 2 * ∫ x, w x ^ 2 ∂μ) *
        ∫ x, (f x - a) ^ 2 ∂μ := by
  let D := ∫ x, w x ∂μ
  let c := D⁻¹ * ∫ x, f x * w x ∂μ
  have hsub : MemLp (fun x => f x - a) 2 μ := hf.sub (memLp_const a)
  have hprod : Integrable (fun x => (f x - a) * w x) μ := hsub.integrable_mul hw
  have hfw : Integrable (fun x => f x * w x) μ := hf.integrable_mul hw
  have hwa : Integrable (fun x => a * w x) μ := (hw.integrable one_le_two).const_mul a
  have hidentity : ∫ x, (f x - a) * w x ∂μ = D * (c - a) := by
    have heq : (fun x => (f x - a) * w x) =
        (fun x => f x * w x - a * w x) := by funext x; ring
    rw [heq, integral_sub hfw hwa, integral_const_mul]
    dsimp [c, D]
    field_simp
  have hcauchy := PDE.integral_mul_sq_le hsub.integrable_sq hw.integrable_sq hprod
  rw [hidentity, mul_pow] at hcauchy
  have hshift : (c - a) ^ 2 ≤ D⁻¹ ^ 2 *
      ((∫ x, (f x - a) ^ 2 ∂μ) * ∫ x, w x ^ 2 ∂μ) := by
    have h := mul_le_mul_of_nonneg_left hcauchy (sq_nonneg D⁻¹)
    have hcancel : D⁻¹ ^ 2 * D ^ 2 = 1 := by field_simp [show D ≠ 0 from hD]
    nlinarith [hcancel]
  have hleft : Integrable (fun x => (f x - c) ^ 2) μ :=
    (hf.sub (memLp_const c)).integrable_sq
  have hright : Integrable (fun x => 2 * (f x - a) ^ 2 + 2 * (c - a) ^ 2) μ :=
    (hsub.integrable_sq.const_mul 2).add (integrable_const _)
  have hpoint : ∀ x, (f x - c) ^ 2 ≤ 2 * (f x - a) ^ 2 + 2 * (c - a) ^ 2 := by
    intro x
    nlinarith [sq_nonneg (f x - a + (c - a))]
  have hvar : 0 ≤ ∫ x, (f x - a) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hwint : 0 ≤ ∫ x, w x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  calc
    (∫ x, (f x - c) ^ 2 ∂μ) ≤
        ∫ x, (2 * (f x - a) ^ 2 + 2 * (c - a) ^ 2) ∂μ :=
      integral_mono_ae hleft hright (ae_of_all _ hpoint)
    _ = 2 * (∫ x, (f x - a) ^ 2 ∂μ) +
        (μ Set.univ).toReal * (2 * (c - a) ^ 2) := by
      rw [integral_add (hsub.integrable_sq.const_mul 2) (integrable_const _),
        integral_const_mul, integral_const]
      simp only [smul_eq_mul, measureReal_def]
    _ ≤ (2 + 2 * (μ Set.univ).toReal * D⁻¹ ^ 2 * ∫ x, w x ^ 2 ∂μ) *
        ∫ x, (f x - a) ^ 2 ∂μ := by
      calc
        _ ≤ 2 * (∫ x, (f x - a) ^ 2 ∂μ) +
            (2 * (μ Set.univ).toReal) * (D⁻¹ ^ 2 *
              ((∫ x, (f x - a) ^ 2 ∂μ) * ∫ x, w x ^ 2 ∂μ)) := by
          have hμ : 0 ≤ 2 * (μ Set.univ).toReal := by positivity
          have h := mul_le_mul_of_nonneg_left hshift hμ
          nlinarith
        _ = _ := by ring

/-- The cutoff weight is square integrable and uniformly bounded in energy. -/
theorem c8_radial_cutoff_weight_sq_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    let U := sourceBall (0 : Vec d) 1
    let w := fun x => ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
    MemLp w 2 (volume.restrict U) ∧
      (∫ x in U, w x ^ 2) ≤ (volume U).toReal * κ⁻¹ ^ 2 := by
  let U := sourceBall (0 : Vec d) 1
  let w := fun x => ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
  haveI : IsFiniteMeasure (volume.restrict U) := by
    apply isFiniteMeasure_restrict.mpr
    dsimp [U]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  have hw (x : Vec d) : 0 ≤ w x ∧ w x ≤ κ⁻¹ := by
    have hρ := hell.2.2 x
    have hχ := (c8_radial_cutoff_properties d).2.2.2.1 x
    constructor
    · exact mul_nonneg (hκ.le.trans hρ.1) hχ.1
    · calc
        w x ≤ ρ x * 1 := mul_le_mul_of_nonneg_left hχ.2 (hκ.le.trans hρ.1)
        _ ≤ κ⁻¹ := by simpa using hρ.2.1
  have hm : Measurable w := hell.1.mul (c8_radial_cutoff_properties d).1.continuous.measurable
  have htop : MemLp w ∞ (volume.restrict U) := by
    apply memLp_top_of_bound hm.aestronglyMeasurable κ⁻¹
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hw x).1] using (hw x).2)
  have htwo : MemLp w 2 (volume.restrict U) := htop.mono_exponent (by simp)
  refine ⟨htwo, ?_⟩
  have h := integral_mono_ae htwo.integrable_sq (integrable_const (κ⁻¹ ^ 2))
    (ae_of_all (volume.restrict U) fun x => by nlinarith [(hw x).1, (hw x).2, inv_nonneg.mpr hκ.le])
  simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] using h

/-- The cutoff-weighted mean is uniformly comparable to any spatial center. -/
theorem c8_cutoff_mean_variance_le (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (f : Vec d → ℝ),
      MemLp f 2 (volume.restrict (sourceBall 0 1)) → ∀ a : ℝ,
      let U := sourceBall (0 : Vec d) 1
      let w := fun x => ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
      let D := ∫ x in U, w x
      (∫ x in U, (f x - D⁻¹ * ∫ y in U, f y * w y) ^ 2) ≤
        C * ∫ x in U, (f x - a) ^ 2 := by
  let U := sourceBall (0 : Vec d) 1
  let V := (volume U).toReal
  let δ := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
  have hδ : 0 < δ := mul_pos hκ (PDE.volume_euclideanBall_toReal_pos 0 (by norm_num))
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let C := 2 + 2 * V * δ⁻¹ ^ 2 * (V * κ⁻¹ ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ρ α hell f hf a
  let w := fun x => ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
  let D := ∫ x in U, w x
  haveI : IsFiniteMeasure (volume.restrict U) := by
    apply isFiniteMeasure_restrict.mpr
    dsimp [U]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  have hD : δ ≤ D := c8_radial_cutoff_density_mass hκ hell
  have hDp : 0 < D := lt_of_lt_of_le hδ hD
  have hinv : D⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ hDp hδ).2 hD
  have hinv0 : 0 ≤ D⁻¹ := inv_nonneg.mpr hDp.le
  have hsq : D⁻¹ ^ 2 ≤ δ⁻¹ ^ 2 := by nlinarith [sq_nonneg (δ⁻¹ - D⁻¹)]
  obtain ⟨hw, hwbound⟩ := c8_radial_cutoff_weight_sq_bound hκ hell
  have hw0 : 0 ≤ ∫ x in U, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hvar : 0 ≤ ∫ x in U, (f x - a) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hc : 2 + 2 * V * D⁻¹ ^ 2 * (∫ x in U, w x ^ 2) ≤ C := by
    dsimp [C]
    have h1 := mul_le_mul_of_nonneg_right hsq hw0
    have h2 := mul_le_mul_of_nonneg_left hwbound (sq_nonneg δ⁻¹)
    nlinarith [mul_le_mul_of_nonneg_left (le_trans h1 h2) (show 0 ≤ 2 * V by positivity)]
  have h := c8_integral_sq_sub_weighted_mean_le (volume.restrict U) hf hw hDp.ne' a
  simp only [Measure.restrict_apply_univ] at h
  exact h.trans (mul_le_mul_of_nonneg_right hc hvar)

/-- The actual weighted cutoff mean controls spatial oscillation on almost every slice. -/
theorem c8_native_ae_cutoff_mean_poincare (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      let U := sourceBall (0 : Vec d) 1
      let w := fun x => ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
      let D := ∫ x in U, w x
      ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        (∫ x in U, (u (t,x) - D⁻¹ * ∫ y in U, u (t,y) * w y) ^ 2) ≤
          C * ∫ x in U, euclideanSq (G (t,x)) := by
  obtain ⟨A, hA, hcmp⟩ := c8_cutoff_mean_variance_le d hκ
  refine ⟨A * ((2 : ℝ) ^ d * 2) ^ 2, mul_nonneg hA (sq_nonneg _), ?_⟩
  intro ρ α hell u G hu
  have hU : IsOpen (sourceBall (0 : Vec d) 1) := by
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.isOpen_euclideanBall 0 1
  filter_upwards [c8_native_ae_slice_memLp hU.measurableSet u hu.1,
    c8_native_ae_slice_poincare u G hu.1 hu.2.2.1 hu.2.2.2.1] with t ht hp
  have h := hcmp ρ α hell (fun x => u (t,x)) ht
    (PDE.integralAverage (sourceBall 0 1) (fun x => u (t,x)))
  calc
    _ ≤ A * (∫ x in sourceBall (0 : Vec d) 1,
        (u (t,x) - PDE.integralAverage (sourceBall 0 1) (fun x => u (t,x))) ^ 2) := h
    _ ≤ A * (((2 : ℝ) ^ d * 2) ^ 2 * ∫ x in sourceBall (0 : Vec d) 1,
        euclideanSq (G (t,x))) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

/-- Integrating the native slice estimate controls the spacetime cutoff variance. -/
theorem c8_native_integrated_cutoff_mean_poincare (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      let I := Set.Ioo (-1 : ℝ) 1
      let U := sourceBall (0 : Vec d) 1
      let D := ∫ x in U, ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
      let M := fun t => D⁻¹ * ∫ x in U, ρ x * u (t,x) * PDE.Parabolic.WeakHarnack.radialCutoff d x
      (∫ z in I ×ˢ U, (u z - M z.1) ^ 2) ≤
        C * ∫ z in I ×ˢ U, euclideanNorm (G z) ^ 2 := by
  obtain ⟨C, hC, hs⟩ := c8_native_ae_cutoff_mean_poincare d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hu
  let I := Set.Ioo (-1 : ℝ) 1
  let U := sourceBall (0 : Vec d) 1
  let D := ∫ x in U, ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
  let M := fun t => D⁻¹ * ∫ x in U, ρ x * u (t,x) * PDE.Parabolic.WeakHarnack.radialCutoff d x
  let μ := volume.restrict I
  let ν := volume.restrict U
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by
    dsimp [U]; rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
  have hprod : volume.restrict (I ×ˢ U) = μ.prod ν := by
    dsimp [μ, ν]; rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hM : MemLp M 2 μ := (c8_caloric_cutoff_pairing_memLp hκ hell hu).1.const_mul D⁻¹
  have hu' : MemLp u 2 (μ.prod ν) := by rw [← hprod]; exact hu.1
  have hdiff : MemLp (fun z : ℝ × Vec d => u z - M z.1) 2 (μ.prod ν) :=
    hu'.sub (hM.comp_fst ν)
  have hgrad : Integrable (fun z : ℝ × Vec d => euclideanNorm (G z) ^ 2) (μ.prod ν) := by
    apply MemLp.integrable_sq
    rw [← hprod]
    exact hu.2.2.1
  have hsq (x : Vec d) : euclideanSq x = euclideanNorm x ^ 2 := by
    unfold euclideanNorm
    rw [Real.sq_sqrt]
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hslice := hs ρ α hell u G hu
  have hpoint : ∀ᵐ t ∂μ,
      (∫ x, (u (t,x) - M t) ^ 2 ∂ν) ≤
        C * ∫ x, euclideanNorm (G (t,x)) ^ 2 ∂ν := by
    filter_upwards [hslice] with t ht
    simpa only [M, D, U, ν, mul_assoc, mul_comm, mul_left_comm, hsq] using ht
  have hint := integral_mono_ae hdiff.integrable_sq.integral_prod_left
    (hgrad.integral_prod_left.const_mul C) hpoint
  rw [integral_const_mul] at hint
  have hfub := integral_prod (fun z : ℝ × Vec d => (u z - M z.1) ^ 2) hdiff.integrable_sq
  change (∫ z, (u z - M z.1) ^ 2 ∂(μ.prod ν)) =
    ∫ t, ∫ x, (u (t,x) - M t) ^ 2 ∂ν ∂μ at hfub
  have hgub := integral_prod (fun z : ℝ × Vec d => euclideanNorm (G z) ^ 2) hgrad
  rw [← hfub, ← hgub] at hint
  change (∫ z in I ×ˢ U, (u z - M z.1) ^ 2) ≤
    C * ∫ z in I ×ˢ U, euclideanNorm (G z) ^ 2
  rw [hprod]
  exact hint

/-- The cutoff mean varies in time by at most the total gradient energy. -/
theorem c8_caloric_cutoff_mean_time_variance (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      let I := Set.Ioo (-1 : ℝ) 1
      let U := sourceBall (0 : Vec d) 1
      let D := ∫ x in U, ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
      let M := fun t => D⁻¹ * ∫ x in U, ρ x * u (t,x) * PDE.Parabolic.WeakHarnack.radialCutoff d x
      ∃ a : ℝ, (∫ t in I, (M t - a) ^ 2) ≤
        B * ∫ z in I ×ˢ U, euclideanNorm (G z) ^ 2 := by
  obtain ⟨B, hB, hinc⟩ := c8_caloric_cutoff_mean_increment d hκ
  refine ⟨2 * B, by positivity, ?_⟩
  intro ρ α hell u G hu
  let I := Set.Ioo (-1 : ℝ) 1
  let U := sourceBall (0 : Vec d) 1
  let D := ∫ x in U, ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
  let M := fun t => D⁻¹ * ∫ x in U, ρ x * u (t,x) * PDE.Parabolic.WeakHarnack.radialCutoff d x
  let E := ∫ z in I ×ˢ U, euclideanNorm (G z) ^ 2
  obtain ⟨v, hv, hmv, hvi⟩ := hinc ρ α hell u G hu
  have hM : MemLp M 2 (volume.restrict I) :=
    (c8_caloric_cutoff_pairing_memLp hκ hell hu).1.const_mul D⁻¹
  refine ⟨v 0, ?_⟩
  have hp : ∀ᵐ t ∂volume.restrict I, (M t - v 0) ^ 2 ≤ B * E := by
    filter_upwards [hmv, ae_restrict_mem measurableSet_Ioo] with t ht hti
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨hti.1.le, hti.2.le⟩
    have h := hvi 0 (by norm_num) t ht'
    change M t = v t at ht
    rw [ht]
    simpa only [sq_abs, E, I, U] using h
  have h := integral_mono_ae (hM.sub (memLp_const (v 0))).integrable_sq
    (integrable_const (B * E)) hp
  change (∫ t in I, (M t - v 0) ^ 2) ≤ (2 * B) * E
  calc
    _ ≤ ∫ _t in I, B * E := h
    _ = _ := by simp [I, integral_const, Measure.real, Real.volume_Ioo]; ring

/-- Native weighted caloric functions satisfy the parabolic Poincaré inequality. -/
theorem c8_native_weighted_parabolic_poincare (d : ℕ)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    let Q : Set (ℝ × Vec d) := Set.Ioo (-1) 1 ×ˢ sourceBall 0 1
    let m : ℝ := (volume Q).toReal⁻¹ * ∫ z in Q, u z
    (∫ z in Q, |u z - m|^2) ≤ C * ∫ z in Q, euclideanNorm (G z)^2 := by
  obtain ⟨A, hA, hsp⟩ := c8_native_integrated_cutoff_mean_poincare d hκ
  obtain ⟨B, hB, htime⟩ := c8_caloric_cutoff_mean_time_variance d hκ
  let I := Set.Ioo (-1 : ℝ) 1
  let U := sourceBall (0 : Vec d) 1
  let V := (volume U).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨2 * A + 2 * V * B + 1, by positivity, ?_⟩
  intro ρ α hell u G hu
  let Q := I ×ˢ U
  let μ := volume.restrict I
  let ν := volume.restrict U
  let D := ∫ x in U, ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x
  let M := fun t => D⁻¹ * ∫ x in U, ρ x * u (t,x) * PDE.Parabolic.WeakHarnack.radialCutoff d x
  let E := ∫ z in Q, euclideanNorm (G z) ^ 2
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by simp [μ, I])
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by
    dsimp [U]; rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
  have hprod : volume.restrict Q = μ.prod ν := by
    dsimp [Q, μ, ν]; rw [Measure.volume_eq_prod, Measure.prod_restrict]
  haveI : IsFiniteMeasure (volume.restrict Q) := by rw [hprod]; infer_instance
  have hQ : (volume.restrict Q Set.univ).toReal ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    have hv : 0 < (volume U).toReal := by
      dsimp [U]; rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
      exact PDE.volume_euclideanBall_toReal_pos 0 (by norm_num)
    have hq : (volume Q).toReal = 2 * (volume U).toReal := by
      dsimp [Q, I]
      rw [Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul]
      simp [Real.volume_Ioo]
      norm_num
    rw [hq]; positivity
  have hM : MemLp M 2 μ := (c8_caloric_cutoff_pairing_memLp hκ hell hu).1.const_mul D⁻¹
  obtain ⟨a, ha⟩ := htime ρ α hell u G hu
  have hsp' := hsp ρ α hell u G hu
  change (∫ z in Q, (u z - M z.1) ^ 2) ≤ A * E at hsp'
  change (∫ t in I, (M t - a) ^ 2) ≤ B * E at ha
  have hu' : MemLp u 2 (μ.prod ν) := by rw [← hprod]; exact hu.1
  have hdif : MemLp (fun z : ℝ × Vec d => u z - M z.1) 2 (μ.prod ν) := hu'.sub (hM.comp_fst ν)
  have ht : MemLp (fun z : ℝ × Vec d => M z.1 - a) 2 (μ.prod ν) :=
    (hM.sub (memLp_const a)).comp_fst ν
  have hleft : Integrable (fun z : ℝ × Vec d => (u z - a) ^ 2) (μ.prod ν) :=
    (hu'.sub (memLp_const a)).integrable_sq
  have hright := (hdif.integrable_sq.const_mul 2).add (ht.integrable_sq.const_mul 2)
  have hpoint : ∀ z : ℝ × Vec d, (u z - a) ^ 2 ≤
      2 * (u z - M z.1) ^ 2 + 2 * (M z.1 - a) ^ 2 := by
    intro z
    nlinarith [sq_nonneg (u z - M z.1 - (M z.1 - a))]
  have hsums := integral_mono_ae hleft hright (ae_of_all _ hpoint)
  change (∫ z : ℝ × Vec d, (u z - a) ^ 2 ∂(μ.prod ν)) ≤
    ∫ z : ℝ × Vec d, (2 * (u z - M z.1) ^ 2 + 2 * (M z.1 - a) ^ 2) ∂(μ.prod ν) at hsums
  rw [integral_add (hdif.integrable_sq.const_mul 2) (ht.integrable_sq.const_mul 2),
    integral_const_mul, integral_const_mul] at hsums
  have hfub := integral_prod (fun z : ℝ × Vec d => (M z.1 - a) ^ 2) ht.integrable_sq
  have htemp : (∫ z : ℝ × Vec d, (M z.1 - a) ^ 2 ∂(μ.prod ν)) =
      V * ∫ t in I, (M t - a) ^ 2 := by
    rw [hfub]
    simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
    rw [integral_const_mul]
    simp only [V, μ, ν, Measure.restrict_apply_univ]
  have he : 0 ≤ E := integral_nonneg fun z => sq_nonneg _
  have hcenter : (∫ z in Q, (u z - a) ^ 2) ≤ (2 * A + 2 * V * B + 1) * E := by
    rw [hprod] at hsp' ⊢
    rw [htemp] at hsums
    nlinarith [mul_le_mul_of_nonneg_left ha hV]
  have hm := c8_integral_sq_sub_mean_le (volume.restrict Q) hQ hu.1 a
  change (∫ z in Q, |u z - (volume Q).toReal⁻¹ * ∫ z in Q, u z| ^ 2) ≤
    (2 * A + 2 * V * B + 1) * E
  simpa only [Measure.restrict_apply_univ, sq_abs] using hm.trans hcenter

end EinsteinFull.Calculus
