import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3UniformCrossHeat
import PDEFoundation.Analysis.Inequalities.Nash.Main

open MeasureTheory PDE EinsteinFull.External.Source.GMP
open EinsteinRelation
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- The completed Dirichlet graph gives an actual global H¹ representative,
with the literal value and gradient zero extensions. -/
noncomputable def dirichletHilbertGlobalH1 {d : ℕ} (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) : PDE.H1Function (Set.univ : Set (PDE.Vec d)) where
  toFun := dirichletHilbertZeroExtension R hR u
  grad := dirichletHilbertZeroExtensionGrad R hR u
  memL2 := by
    change MemLp _ 2 (volume.restrict Set.univ)
    simpa only [Measure.restrict_univ] using
      (dirichletHilbert_global_zeroExtension R hR u).1
  gradMemL2 := by
    intro i
    change MemLp _ 2 (volume.restrict Set.univ)
    simpa only [Measure.restrict_univ] using
      (dirichletHilbert_global_zeroExtension R hR u).2.1 i
  hasWeakGradient := by
    intro i φ hφ hc hs
    have hw := ((dirichletHilbert_global_zeroExtension R hR u).2.2 i).2.2 φ
      ⟨hφ, hc, hs⟩
    simpa only [coordinateDerivative, unitVector, PDE.basisVec] using hw

/-- The global representative is integrable because its support is in a finite ball. -/
theorem dirichletHilbertGlobalH1_integrable {d : ℕ} (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    Integrable (dirichletHilbertGlobalH1 R hR u).toFun volume := by
  let B := sourceBall (0 : PDE.Vec d) R
  have hB : MeasurableSet B := (dirichletBall (d := d) R).isOpen.measurableSet
  have hfin : volume B ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (sourceBall_subset_cube R hR))
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hfin
  have hm := ((dirichletHilbert_global_zeroExtension R hR u).1.restrict B).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi := (integrable_indicator_iff hB).2 hm
  simpa only [dirichletHilbertGlobalH1, dirichletHilbertZeroExtension,
    Set.indicator_indicator, B, Set.inter_self] using hi

/-- The library Nash inequality applied to the actual global Dirichlet extension.
The constant is chosen independently of the ball and the function. -/
theorem dirichletHilbert_global_nash {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (u : DirichletHilbertSpace (d := d) R hR),
      (∫ x, (dirichletHilbertGlobalH1 R hR u).toFun x ^ 2) ≤
        C * (∫ x, PDE.vecEuclideanNorm ((dirichletHilbertGlobalH1 R hR u).grad x) ^ 2) ^
          ((d : ℝ) / (d + 2)) *
        (∫ x, |(dirichletHilbertGlobalH1 R hR u).toFun x|) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := PDE.Nash.exists_nash_constant_full d (by omega)
  exact ⟨C, hC, fun R hR u => hN _ (dirichletHilbertGlobalH1_integrable R hR u)⟩

/-- Nash on the native ball coordinates, with a dimension-only constant. -/
theorem dirichletHilbert_ball_nash {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (u : DirichletHilbertSpace (d := d) R hR),
      (∫ x in sourceBall (0 : PDE.Vec d) R, (u.val none x) ^ 2) ≤
        C * (∫ x in sourceBall (0 : PDE.Vec d) R,
          PDE.vecEuclideanNorm (fun i => u.val (some i) x) ^ 2) ^ ((d : ℝ) / (d + 2)) *
        (∫ x in sourceBall (0 : PDE.Vec d) R, |u.val none x|) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := dirichletHilbert_global_nash hd
  refine ⟨C, hC, ?_⟩
  intro R hR u
  let B := sourceBall (0 : PDE.Vec d) R
  have hB : MeasurableSet B := (dirichletBall (d := d) R).isOpen.measurableSet
  have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 := PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
  have hval : (fun x => (dirichletHilbertGlobalH1 R hR u).toFun x ^ 2) =
      B.indicator (fun x => (u.val none x) ^ 2) := by
    funext x
    by_cases hx : x ∈ B <;> simp [dirichletHilbertGlobalH1, dirichletHilbertZeroExtension, B, hx]
  have hgrad : (fun x => PDE.vecEuclideanNorm ((dirichletHilbertGlobalH1 R hR u).grad x) ^ 2) =
      B.indicator (fun x => PDE.vecEuclideanNorm (fun i => u.val (some i) x) ^ 2) := by
    funext x
    by_cases hx : x ∈ B <;> simp [dirichletHilbertGlobalH1, dirichletHilbertZeroExtensionGrad, B, hx, hz]
  have habs : (fun x => |(dirichletHilbertGlobalH1 R hR u).toFun x|) =
      B.indicator (fun x => |u.val none x|) := by
    funext x
    by_cases hx : x ∈ B <;> simp [dirichletHilbertGlobalH1, dirichletHilbertZeroExtension, B, hx]
  have hn := hN R hR u
  rw [hval, hgrad, habs, integral_indicator hB, integral_indicator hB, integral_indicator hB] at hn
  exact hn

/-- Value and gradient coordinates of the native graph are L² on the ball. -/
theorem dirichletHilbert_ball_memLp {d : ℕ} (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    MemLp (fun x => u.val none x) 2 (volume.restrict (sourceBall 0 R)) ∧
      ∀ i, MemLp (fun x => u.val (some i) x) 2 (volume.restrict (sourceBall 0 R)) := by
  let B := sourceBall (0 : PDE.Vec d) R
  have hB : MeasurableSet B := (dirichletBall (d := d) R).isOpen.measurableSet
  constructor
  · apply (memLp_indicator_iff_restrict hB).mp
    exact (dirichletHilbert_global_zeroExtension R hR u).1
  · intro i
    apply (memLp_indicator_iff_restrict hB).mp
    have hg := (dirichletHilbert_global_zeroExtension R hR u).2.1 i
    have heq : (fun x => dirichletHilbertZeroExtensionGrad R hR u x i) =
        B.indicator (fun x => u.val (some i) x) := by
      funext x
      by_cases hx : x ∈ B <;> simp [dirichletHilbertZeroExtensionGrad, B, hx]
    rw [← heq]
    exact hg

/-- The two mass integrands and the native Dirichlet energy are integrable. -/
theorem dirichletHilbert_weighted_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    Integrable (fun x => ρ x * (u.val none x) ^ 2) (volume.restrict (sourceBall 0 R)) ∧
    Integrable (fun x => ρ x * |u.val none x|) (volume.restrict (sourceBall 0 R)) ∧
    Integrable (fun x => dot ((α x).mulVec (fun i => u.val (some i) x))
      (fun i => u.val (some i) x)) (volume.restrict (sourceBall 0 R)) := by
  let B := sourceBall (0 : PDE.Vec d) R
  have hfin : volume B ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (sourceBall_subset_cube R hR))
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hfin
  obtain ⟨hu, hg⟩ := dirichletHilbert_ball_memLp R hR u
  have hρ := (uniformlyElliptic_coefficients_memLp_top hκ h (volume.restrict B)).1
  have hflux := (uniformlyElliptic_flux_mass_memLp hκ h (volume.restrict B) hu hg).1
  refine ⟨hu.integrable_sq.mul_of_top_right hρ, ?_, ?_⟩
  · exact (hu.integrable (by norm_num)).abs.mul_of_top_right hρ
  · change Integrable (fun x => ∑ i : Fin d, ((α x).mulVec (fun i => u.val (some i) x)) i *
      u.val (some i) x) (volume.restrict B)
    exact integrable_finsetSum Finset.univ (fun i _ => (hflux i).integrable_mul (hg i))

/-- Ellipticity compares the native unweighted norms to the weighted mass and energy. -/
theorem dirichletHilbert_weighted_comparisons {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    (∫ x in sourceBall 0 R, ρ x * (u.val none x) ^ 2) ≤
      κ⁻¹ * (∫ x in sourceBall 0 R, (u.val none x) ^ 2) ∧
    κ * (∫ x in sourceBall 0 R, |u.val none x|) ≤
      (∫ x in sourceBall 0 R, ρ x * |u.val none x|) ∧
    κ * (∫ x in sourceBall 0 R, PDE.vecEuclideanNorm (fun i => u.val (some i) x) ^ 2) ≤
      (∫ x in sourceBall 0 R, dot ((α x).mulVec (fun i => u.val (some i) x))
        (fun i => u.val (some i) x)) := by
  let B := sourceBall (0 : PDE.Vec d) R
  have hfin : volume B ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (sourceBall_subset_cube R hR))
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hfin
  obtain ⟨hu, hg⟩ := dirichletHilbert_ball_memLp R hR u
  obtain ⟨hmass, hl1, henergy⟩ := dirichletHilbert_weighted_integrable hκ h R hR u
  have hs : Integrable (fun x => PDE.vecEuclideanNorm (fun i => u.val (some i) x) ^ 2)
      (volume.restrict B) := by
    simp_rw [PDE.vecEuclideanNorm_sq, PDE.vecNormSq_eq_sum_sq]
    exact integrable_finsetSum Finset.univ (fun i _ => (hg i).integrable_sq)
  refine ⟨?_, ?_, ?_⟩
  · have hh := integral_mono hmass (hu.integrable_sq.const_mul κ⁻¹)
      (fun x => mul_le_mul_of_nonneg_right ((h.2.2 x).2.1) (sq_nonneg _))
    simpa only [integral_const_mul] using hh
  · have hh := integral_mono ((hu.integrable (by norm_num)).abs.const_mul κ) hl1
      (fun x => mul_le_mul_of_nonneg_right ((h.2.2 x).1) (abs_nonneg _))
    simpa only [integral_const_mul] using hh
  · have hh := integral_mono (hs.const_mul κ) henergy (fun x => by
      have he := ((h.2.2 x).2.2.2 (fun i => u.val (some i) x)).1
      rw [PDE.vecEuclideanNorm_sq, PDE.vecNormSq, PDE.vecDot]
      change κ * (∑ i, u.val (some i) x * u.val (some i) x) ≤ _
      change κ * (∑ i, u.val (some i) x * u.val (some i) x) ≤
        dotProduct (fun i => u.val (some i) x) ((α x).mulVec (fun i => u.val (some i) x)) at he
      rw [dotProduct_comm] at he
      simpa only [dot, dotProduct] using he)
    simpa only [integral_const_mul] using hh

/-- Quantitative Nash inequality for the native weighted Dirichlet energy.
The constant depends only on the dimension and ellipticity parameter. -/
theorem dirichletHilbert_weighted_nash {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d),
      IsUniformlyElliptic κ ρ α → ∀ u : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall 0 R, ρ x * (u.val none x) ^ 2) ≤
        C * (∫ x in sourceBall 0 R,
          dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => u.val (some i) x)) ^ ((d : ℝ) / (d + 2)) *
          (∫ x in sourceBall 0 R, ρ x * |u.val none x|) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := dirichletHilbert_ball_nash hd
  let p : ℝ := (d : ℝ) / (d + 2)
  let q : ℝ := (4 : ℝ) / (d + 2)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  refine ⟨κ⁻¹ * C * (κ⁻¹ ^ p) * (κ⁻¹ ^ q), by positivity, ?_⟩
  intro R hR ρ α hell u
  let X : ℝ := ∫ x in sourceBall 0 R, (u.val none x) ^ 2
  let G : ℝ := ∫ x in sourceBall 0 R, PDE.vecEuclideanNorm (fun i => u.val (some i) x) ^ 2
  let L : ℝ := ∫ x in sourceBall 0 R, |u.val none x|
  let E : ℝ := ∫ x in sourceBall 0 R, dot ((α x).mulVec (fun i => u.val (some i) x))
    (fun i => u.val (some i) x)
  let W : ℝ := ∫ x in sourceBall 0 R, ρ x * |u.val none x|
  have hG : 0 ≤ G := integral_nonneg fun x => sq_nonneg _
  have hL : 0 ≤ L := integral_nonneg fun x => abs_nonneg _
  obtain ⟨hM, hW, hE⟩ := dirichletHilbert_weighted_comparisons hκ hell R hR u
  change κ * L ≤ W at hW
  change κ * G ≤ E at hE
  have hE0 : 0 ≤ E := (mul_nonneg hκ.le hG).trans hE
  have hW0 : 0 ≤ W := (mul_nonneg hκ.le hL).trans hW
  have hG' : G ≤ κ⁻¹ * E := by
    have hh := (le_div_iff₀ hκ).2 (by simpa [mul_comm] using hE)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hL' : L ≤ κ⁻¹ * W := by
    have hh := (le_div_iff₀ hκ).2 (by simpa [mul_comm] using hW)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hgp : G ^ p ≤ κ⁻¹ ^ p * E ^ p := by
    exact (Real.rpow_le_rpow hG hG' hp).trans_eq (Real.mul_rpow (inv_nonneg.mpr hκ.le) hE0)
  have hlq : L ^ q ≤ κ⁻¹ ^ q * W ^ q := by
    exact (Real.rpow_le_rpow hL hL' hq).trans_eq (Real.mul_rpow (inv_nonneg.mpr hκ.le) hW0)
  have hn : X ≤ C * G ^ p * L ^ q := hN R hR u
  have hm : (∫ x in sourceBall 0 R, ρ x * (u.val none x) ^ 2) ≤ κ⁻¹ * X := hM
  calc
    _ ≤ κ⁻¹ * X := hm
    _ ≤ κ⁻¹ * (C * G ^ p * L ^ q) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hκ.le)
    _ ≤ κ⁻¹ * (C * (κ⁻¹ ^ p * E ^ p) * (κ⁻¹ ^ q * W ^ q)) := by
      gcongr
    _ = _ := by ring

#print axioms dirichletHilbert_weighted_nash

end EinsteinFull.Calculus
