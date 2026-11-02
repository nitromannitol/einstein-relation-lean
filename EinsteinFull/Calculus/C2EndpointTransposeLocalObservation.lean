import EinsteinFull.Calculus.C8EndpointTransposeProjection
import EllipticRegularity.Parabolic.NashLower.Restrict
import EllipticRegularity.Parabolic.SliceEstimate.WeakC1
import PDEFoundation.Sobolev.OneDimensional.ContinuousWeakIncrement
import PDEFoundation.Sobolev.OneDimensional.SmoothTransport

/-! Conservative real lifts for the short-time transpose endpoint.
The endpoint localization theorem still requires the actual residual and its
Gaussian comparison; the lemmas here keep the transpose force in the flux. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

/-- The transpose lift keeps the complex force in the physical flux.
The two equal auxiliary diagonal entries cancel on the harmonic exponential. -/
def shortTimeTransposeLiftMatrix {d : ℕ} (A : PDE.Mat d) (i : Fin d)
    (ζ : ℂ) (M : ℝ) : PDE.Mat (d + 2) :=
  (shortTimeComplexLiftMatrix A i (-ζ) M).transpose

/-- Transposing the real lift preserves its uniform ellipticity constants. -/
theorem short_time_transpose_lift_uniform_ellipticity {d : ℕ}
    (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 < L ∧ ∀ (A : PDE.Mat d), S5Elliptic A Λ →
      ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
      PDE.IsEllipticMatrix (Λ⁻¹ / 4) L
        (shortTimeTransposeLiftMatrix A i ζ (4 * Λ ^ 3 * (B ^ 2 + 1))) := by
  obtain ⟨L, hL, hmatrix⟩ := short_time_complex_lift_uniform_ellipticity Λ B hΛ hB
  refine ⟨L, hL, fun A hA i ζ hζ => ?_⟩
  exact PDE.isEllipticMatrix_transpose (hmatrix A hA i (-ζ) (by simpa only [norm_neg] using hζ))

/-- The physical rows are exactly the conservative transpose flux; no
derivative of a coefficient or replacement forward equation is used. -/
theorem short_time_transpose_lift_flux {d : ℕ} (A : PDE.Mat d) (i : Fin d)
    (ζ e u : ℂ) (M : ℝ) (D : Fin d → ℂ) :
    PDE.matVecMul (shortTimeTransposeLiftMatrix A i ζ M)
      (Fin.addCases (fun j => (e * D j).re) ![(e * u).re, -(e * u).im]) =
    Fin.addCases
      (fun j => (e * ((1 / 2 : ℂ) * ∑ k, (A k j : ℂ) * D k -
        ζ * (A j i : ℂ) * u)).re)
      ![M * (e * u).re, -M * (e * u).im] := by
  have hsum (C : Fin d → ℝ) :
      (∑ k, C k * (e * D k).re) = (e * ∑ k, (C k : ℂ) * D k).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  ext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [PDE.matVecMul, shortTimeTransposeLiftMatrix, Matrix.transpose_apply,
      shortTimeComplexLiftMatrix, Fin.addCases_left, Fin.addCases_right,
      Fin.sum_univ_add, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
      Complex.neg_re, Complex.neg_im, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hm : (∑ k, A k j / 2 * (e * D k).re) =
        (1 / 2 : ℝ) * (e * ∑ k, (A k j : ℂ) * D k).re := by
      rw [← hsum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hm]
    simp only [mul_sub, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    norm_num
    ring
  · fin_cases j <;>
      simp [PDE.matVecMul, shortTimeTransposeLiftMatrix, Matrix.transpose_apply,
        shortTimeComplexLiftMatrix, Fin.sum_univ_add]
    ring

/-- The conservative complex weak equation becomes a homogeneous real
parabolic weak equation under the transpose lift. -/
theorem short_time_transpose_lift_isParabolicWeakSolution {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {I : Set ℝ}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hI : MeasurableSet I)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (A : PDE.Vec d → PDE.Mat d) (i : Fin d)
    (u : PDE.Vec d × ℝ → ℂ) (D : Fin d → PDE.Vec d × ℝ → ℂ)
    (ζ : ℂ) (M : ℝ)
    (hu : IntegrableOn u (U ×ˢ I))
    (hP : ∀ j, IntegrableOn
      (fun z => (1 / 2 : ℂ) * ∑ k, (A z.1 k j : ℂ) * D k z -
        ζ * (A z.1 j i : ℂ) * u z) (U ×ˢ I))
    (hweak : ∀ ψ : PDE.ParTestFunction U (interior I), ∀ e : ℂ,
      (∫ z in U ×ˢ I,
        -((e * u z).re * PDE.parTimeDeriv ψ.toFun z) +
          ∑ j, (e * ((1 / 2 : ℂ) * ∑ k, (A z.1 k j : ℂ) * D k z -
            ζ * (A z.1 j i : ℂ) * u z)).re * PDE.parSpaceGrad ψ.toFun z j) = 0)
    (w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) I)
    (hw : ∀ z, w.toFun z = (Complex.exp
      ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re)
    (hD : ∀ z j, w.grad z (Fin.castAdd 2 j) = (Complex.exp
      ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        D j ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re)
    (h0 : ∀ z, w.grad z (Fin.natAdd d (0 : Fin 2)) = w.toFun z)
    (h1 : ∀ z, w.grad z (Fin.natAdd d (1 : Fin 2)) = -(Complex.exp
      ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).im) :
    PDE.IsParabolicWeakSolution
      (fun z => shortTimeTransposeLiftMatrix (A (PDE.vecAppendEquiv d 2 z.1).1) i ζ M)
      (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) I w := by
  intro φ
  let P : Fin d → PDE.Vec d × ℝ → ℂ := fun j z =>
    (1 / 2 : ℂ) * ∑ k, (A z.1 k j : ℂ) * D k z - ζ * (A z.1 j i : ℂ) * u z
  have heq : PDE.parWeakIntegrand
      (fun z => shortTimeTransposeLiftMatrix (A (PDE.vecAppendEquiv d 2 z.1).1) i ζ M)
      w φ.toFun = shortTimeComplexLiftWeakIntegrand u (fun _ => 0) P 0 M φ.toFun := by
    funext z
    have hgrad : w.grad z = Fin.addCases
        (fun j => (Complex.exp
          ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
            D j ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re)
        ![w.toFun z, -(Complex.exp
          ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
            u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).im] := by
      ext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.addCases_left] using hD z j
      · fin_cases j <;> simp [h0 z, h1 z]
    simp only [PDE.parWeakIntegrand, hgrad, hw z, short_time_transpose_lift_flux,
      shortTimeComplexLiftWeakIntegrand, Complex.zero_re, Complex.zero_im,
      zero_mul, zero_add, zero_sub, neg_mul, P]
  rw [heq]
  apply short_time_complex_lift_weak_integral hU hV hI hVfinite r hr u
    (fun _ => 0) P 0 M hu (integrableOn_zero) hP ?_ φ
  intro ψ e
  simpa only [zero_mul, Complex.zero_re, mul_zero, sub_zero] using hweak ψ e

/-- The time normalization of the conservative lift has lower ellipticity one,
with constants independent of the physical field and signed complex force. -/
theorem short_time_transpose_lift_normalized_ellipticity {d : ℕ}
    (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (A : PDE.Mat d), S5Elliptic A Λ →
      ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
      PDE.IsEllipticMatrix 1 L
        ((4 * Λ) • shortTimeTransposeLiftMatrix A i ζ (4 * Λ ^ 3 * (B ^ 2 + 1))) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  obtain ⟨L, _, hmatrix⟩ := short_time_transpose_lift_uniform_ellipticity Λ B hΛ hB
  refine ⟨max 1 (4 * Λ * L), le_max_left _ _, fun A hA i ζ hζ => ?_⟩
  have hm := PDE.isEllipticMatrix_smul (by positivity : 0 < 4 * Λ)
    (hmatrix A hA i ζ hζ)
  have hl : 4 * Λ * (Λ⁻¹ / 4) = 1 := by field_simp
  rw [hl] at hm
  exact hm.mono zero_lt_one le_rfl (le_max_right _ _)

/-- Continuity of the actual coefficient field also controls the entries of
the transposed lift. -/
theorem short_time_continuous_transpose_lift_entry_continuous {d : ℕ}
    (A : EinsteinRelation.CoefficientField d) (i : Fin d) (ζ : ℂ) (M κ : ℝ)
    (j k : Fin (d + 2)) :
    Continuous (fun z : PDE.Vec (d + 2) × ℝ =>
      (κ • shortTimeTransposeLiftMatrix (A ((PDE.vecAppendEquiv d 2 z.1).1))
        i ζ M) j k) := by
  exact short_time_continuous_lift_entry_continuous A i (-ζ) M κ k j

/-- The signed local maximum estimate applies to the conservative transpose
lift. The constant precedes the field, force and weak solution. -/
theorem short_time_continuous_transpose_lift_local_max {d : ℕ}
    (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : EinsteinRelation.CoefficientField d),
    (∀ z ∈ PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1 ×ˢ Set.Ioc (-1 : ℝ) 0,
      S5Elliptic (A ((PDE.vecAppendEquiv d 2 z.1).1)) Λ) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ w : PDE.ParH1Function (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1) (Set.Ioc (-1 : ℝ) 0),
    PDE.IsParabolicWeakSolution
      (fun z => (4 * Λ) • shortTimeTransposeLiftMatrix
        (A ((PDE.vecAppendEquiv d 2 z.1).1)) i ζ (4 * Λ ^ 3 * (B ^ 2 + 1)))
      (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1) (Set.Ioc (-1 : ℝ) 0) w →
    essSup (fun z => ENNReal.ofReal |w.toFun z|)
      (volume.restrict (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
      ENNReal.ofReal C * (∫⁻ z in EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (1 / 2) (-3 / 4),
        ENNReal.ofReal |w.toFun z| ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
  obtain ⟨L, hL, hmatrix⟩ := short_time_transpose_lift_normalized_ellipticity Λ B hΛ hB
  obtain ⟨C₀, hC₀, hstep⟩ := EinsteinFull.SignedLocalMax.power_step_S (d + 2) (by omega)
  obtain ⟨C, hC, hmax⟩ :=
    EinsteinFull.SignedLocalMax.signed_local_max_L2 (d + 2) (by omega) hC₀ hstep L hL
  refine ⟨C, hC, fun A hA i ζ hζ w hw => hmax _ ?_ w hw⟩
  refine ⟨fun j k => ?_, ?_⟩
  · exact (short_time_continuous_transpose_lift_entry_continuous A i ζ
      (4 * Λ ^ 3 * (B ^ 2 + 1)) (4 * Λ) j k).measurable.aemeasurable
  · filter_upwards [ae_restrict_mem
      ((PDE.isOpen_euclideanBall (0 : PDE.Vec (d + 2)) 1).measurableSet.prod measurableSet_Ioc)]
        with z hz
    exact hmatrix _ (hA z hz) i ζ hζ

/-- The conservative transpose local maximum after the physical space and time
normalization. The solution and its actual physical residual remain identical
through both changes of variables. -/
theorem short_time_transpose_normalized_lift_local_max {d : ℕ}
    (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : EinsteinRelation.CoefficientField d),
    (∀ x, S5Elliptic (A x) Λ) → ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (X : ℝ × Vec d → ℂ)
      (w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹'
        (PDE.euclideanBall (0 : PDE.Vec d) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec 2) 1))
        (Icc (-1 : ℝ) 1)),
    (∀ z, w.toFun z = (Complex.exp
      ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).re) →
    (∀ M : ℝ, PDE.IsParabolicWeakSolution
      (fun z => shortTimeTransposeLiftMatrix (A (PDE.vecAppendEquiv d 2 z.1).1) i ζ M)
      (PDE.vecAppendEquiv d 2 ⁻¹'
        (PDE.euclideanBall (0 : PDE.Vec d) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec 2) 1))
      (Icc (-1 : ℝ) 1) w) →
    ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ T : ℝ,
      -1 ≤ T - 4 * Λ * q ^ 2 → T ≤ 1 →
      let v : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
        (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
          q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
            X (T + 4 * Λ * q ^ 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re
      MemLp v 2 (volume.restrict
        (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1 ×ˢ Ioc (-1 : ℝ) 0)) ∧
      essSup (fun z => ENNReal.ofReal |v z|)
        (volume.restrict (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
        ENNReal.ofReal C *
          (∫⁻ z in EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (1 / 2) (-3 / 4),
            ENNReal.ofReal |v z| ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
  obtain ⟨L, hL, hmatrix⟩ := short_time_transpose_lift_normalized_ellipticity Λ B hΛ hB
  obtain ⟨C₀, hC₀, hstep⟩ := EinsteinFull.SignedLocalMax.power_step_S (d + 2) (by omega)
  obtain ⟨C, hC, hmax⟩ :=
    EinsteinFull.SignedLocalMax.signed_local_max_L2 (d + 2) (by omega) hC₀ hstep L hL
  refine ⟨C, hC, ?_⟩
  intro A hA i ζ hζ X w hw hweak q hq hq1 T hT₀ hT₁
  let E := PDE.vecAppendEquiv d 2 ⁻¹'
    (PDE.euclideanBall (0 : PDE.Vec d) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec 2) 1)
  have hqE : PDE.euclideanBall (0 : PDE.Vec (d + 2)) q ⊆ E :=
    (PDE.euclideanBall_mono hq.le hq1).trans
      (PDE.euclideanBall_subset_preimage_vecAppendEquiv_prod d 2 zero_lt_one)
  let wq := PDE.Parabolic.NashLower.restrictParH1 hqE (Subset.rfl : Icc (-1 : ℝ) 1 ⊆ _) w
  let M := 4 * Λ ^ 3 * (B ^ 2 + 1)
  let a : PDE.ParCoeffField (d + 2) := fun z =>
    shortTimeTransposeLiftMatrix (A (PDE.vecAppendEquiv d 2 z.1).1) i ζ M
  have hwq : PDE.IsParabolicWeakSolution a _ _ wq :=
    PDE.Parabolic.NashLower.isParabolicWeakSolution_restrict hqE Subset.rfl (hweak M)
  let r := Real.sqrt (4 * Λ)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 4 * Λ := Real.sq_sqrt (by positivity)
  let J : Set ℝ := Ioc (-(q ^ 2)) 0
  have hJI : PDE.Parabolic.Rescale.timeMap T r '' J ⊆ Icc (-1 : ℝ) 1 := by
    rintro _ ⟨s, hs, rfl⟩
    change -1 ≤ T + r ^ 2 * s ∧ T + r ^ 2 * s ≤ 1
    rw [hr2]
    have hlo := mul_le_mul_of_nonneg_left hs.1.le (by positivity : 0 ≤ 4 * Λ)
    have hhi := mul_le_mul_of_nonneg_left hs.2 (by positivity : 0 ≤ 4 * Λ)
    constructor <;> linarith only [hlo, hhi, hT₀, hT₁]
  let wt := shortTimeParabolicTimeRescale T hr hJI wq
  have hwt : PDE.IsParabolicWeakSolution
      (fun z => r ^ 2 • a (shortTimeParabolicTimeHomeomorph (d + 2) T hr z))
      (PDE.euclideanBall (0 : PDE.Vec (d + 2)) q) J wt :=
    short_time_time_rescale_isParabolicWeakSolution T hr
      (PDE.isOpen_euclideanBall _ _).measurableSet measurableSet_Icc hJI a wq hwq
  have hqJ : Ioc (0 - q ^ 2) 0 ⊆ J := by simp only [zero_sub]; exact Subset.rfl
  let wn := PDE.Parabolic.Rescale.rescaleParH1 (0 : PDE.Vec (d + 2)) hq 0 hqJ wt
  let an : PDE.ParCoeffField (d + 2) := fun z =>
    r ^ 2 • a (shortTimeParabolicTimeHomeomorph (d + 2) T hr
      (PDE.Parabolic.Rescale.cylMap 0 q 0 z))
  have hwn : PDE.IsParabolicWeakSolution an _ _ wn :=
    PDE.Parabolic.Rescale.isParabolicWeakSolution_rescale
      (fun z => r ^ 2 • a (shortTimeParabolicTimeHomeomorph (d + 2) T hr z)) 0 hq 0
      measurableSet_Ioc hqJ wt hwt
  have hean : an = fun z => (4 * Λ) • shortTimeTransposeLiftMatrix
      (A (q • (PDE.vecAppendEquiv d 2 z.1).1)) i ζ M := by
    funext z
    simp [an, a, shortTimeParabolicTimeHomeomorph, PDE.Parabolic.Rescale.cylMap,
      PDE.Parabolic.Rescale.spaceMap_apply, hr2, map_smul]
  have hcoeff : PDE.IsParabolicCoeff 1 L an
      (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1) (Ioc (-1 : ℝ) 0) := by
    rw [hean]
    refine ⟨fun j k => ?_, ?_⟩
    · have hentry := short_time_continuous_transpose_lift_entry_continuous A i ζ M (4 * Λ) j k
      have hmap : Continuous (fun z : PDE.Vec (d + 2) × ℝ => (q • z.1, z.2)) :=
        (continuous_fst.const_smul q).prodMk continuous_snd
      simpa only [Function.comp_def, map_smul, ContinuousLinearEquiv.coe_coe, Prod.smul_fst] using
        (hentry.comp hmap).measurable.aemeasurable
    · exact Filter.Eventually.of_forall fun z => hmatrix _ (hA _) i ζ hζ
  have hbound := hmax an hcoeff wn hwn
  have hewn : wn.toFun = fun z : PDE.Vec (d + 2) × ℝ =>
      (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
        q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          X (T + 4 * Λ * q ^ 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re := by
    funext z
    change w.toFun _ = _
    rw [hw]
    simp [shortTimeParabolicTimeHomeomorph, PDE.Parabolic.Rescale.cylMap,
      PDE.Parabolic.Rescale.spaceMap_apply, PDE.Parabolic.Rescale.timeMap, hr2, map_smul, mul_assoc]
  exact ⟨by simpa only [hewn] using wn.memL2, by simpa only [hewn] using hbound⟩

/-- The actual stationary transpose primitive is strongly continuous in every
Gaussian L2 norm, on an event chosen before all widths and short times. -/
theorem short_time_stationary_transpose_primitive_gaussian_strong_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (F U : ℝ × FieldPair d → ℂ)
    (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g)
    (hprim : ∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ L : ℝ, 0 < L →
      (∀ t ∈ Icc (0 : ℝ) 1,
        MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) *
          F (t, translate x ω)) 2 volume) ∧
      ∀ a ∈ Icc (0 : ℝ) 1,
        Tendsto (fun t => ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - F (a, translate x ω)‖ ^ 2)
          (𝓝[Icc (0 : ℝ) 1] a) (𝓝 0) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    integrable_sq_joint_l2_representative
      ((((hPdag.continuous_apply hP g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hU heU
  filter_upwards [ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) 1 zero_le_one U hU hI,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) f] with ω hω hfω
  intro L hL
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / L) : ℂ)
  let D : ℝ × Vec d → ℂ := fun p => w p.2 * U (p.1, translate p.2 ω)
  have hw : Measurable w := by
    dsimp only [w, euclideanSq, dot]
    fun_prop
  have hD : Measurable D :=
    (hw.comp measurable_snd).mul (hU.comp (measurable_fst.prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk measurable_const))))
  have hi : Integrable (fun p => ‖D p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
    (hω L hL).norm.integrable_sq
  obtain ⟨hm, hc⟩ := short_time_local_primitive_continuous volume hD hi
  have he (t : ℝ) (x : Vec d) :
      w x * F (t, translate x ω) = w x * f (translate x ω) +
        ∫ s in Icc (0 : ℝ) t, D (s, x) := by
    dsimp only [D]
    rw [hprim, mul_add, integral_const_mul]
  refine ⟨?_, ?_⟩
  · intro t ht
    exact ((hfω L hL).add (hm t ht)).ae_eq
      (ae_of_all _ fun x => (he t x).symm)
  · intro a ha
    convert hc a ha using 1
    funext t
    apply integral_congr_ae
    filter_upwards with x
    have heq : w x * (F (t, translate x ω) - F (a, translate x ω)) =
        (∫ s in Icc (0 : ℝ) t, D (s, x)) -
          (∫ s in Icc (0 : ℝ) a, D (s, x)) := by
      rw [mul_sub, he, he, add_sub_add_left_eq_sub]
    rw [← heq, norm_mul, mul_pow]
    simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The SAME stationary-minus-physical transpose residual has continuous
Gaussian energy. The event precedes the physical semigroup and every width. -/
theorem short_time_stationary_physical_transpose_gaussian_energy_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (F U : ℝ × FieldPair d → ℂ)
    (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g)
    (hprim : ∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ L : ℝ, 0 < L →
      ∀ (a : Vec d → Mat d)
        (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup a i ζ Pr Tr →
      ∀ (fr : Lp ℂ 2 (volume : Measure (Vec d))) (V : ℝ × Vec d → ℂ),
      (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) →
      ContinuousOn (fun t : ℝ => ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖F (t, translate x ω) - V (t, x)‖ ^ 2) (Icc (0 : ℝ) 1) := by
  filter_upwards [short_time_stationary_transpose_primitive_gaussian_strong_continuous
    hd Q hP hPdag f g F U hU heU hprim] with ω hω
  intro L hL a Pr Tr hPr fr V heV
  obtain ⟨hFm, hFc⟩ := hω L hL
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / L) : ℂ)
  let H : Icc (0 : ℝ) 1 → Lp ℂ 2 (volume : Measure (Vec d)) := fun t =>
    (hFm t t.property).toLp (fun x => w x * F (t, translate x ω))
  have hH : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun s : Icc (0 : ℝ) 1 => fun x => w x * F (s, translate x ω))
      (fun s => hFm s s.property) _ (hFm t t.property)).mpr
    have hc := (tendsto_nhdsWithin_iff_subtype t.property _ _).mp (hFc t t.property)
    have hc' : Tendsto (fun s : Icc (0 : ℝ) 1 => ∫ x,
        ‖w x * F (s, translate x ω) - w x * F (t, translate x ω)‖ ^ 2)
        (𝓝 t) (𝓝 0) := by
      convert hc using 1
      funext s
      apply integral_congr_ae
      filter_upwards with x
      rw [← mul_sub, norm_mul, mul_pow]
      simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he := PDE.tendsto_eLpNorm_two_zero_of_tendsto_integral_sq
      (fun s : Icc (0 : ℝ) 1 => ((hFm s s.property).sub (hFm t t.property)).norm) hc'
    convert he using 1
    funext s
    exact (eLpNorm_norm _ ((hFm s s.property).sub (hFm t t.property)).aestronglyMeasurable).symm
  let W : Lp ℂ 2 (volume : Measure (Vec d)) → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun u => (short_time_gaussian_weight_memLp L hL u).toLp (fun x => w x * u x)
  have hW : Continuous W := (short_time_gaussian_weight_lipschitz L hL).continuous
  have hR : Continuous (fun t : Icc (0 : ℝ) 1 => H t - W (Tr t.val.toNNReal fr)) :=
    hH.sub (hW.comp (((hPr.2.2.1 fr).comp continuous_real_toNNReal).comp
      continuous_subtype_val))
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hR.norm.pow 2 using 1
  funext t
  let G : Vec d → ℂ := fun x => w x * F (t, translate x ω) - w x * (Tr t.val.toNNReal fr) x
  have hmG : MemLp G 2 volume := (hFm t t.property).sub
    (short_time_gaussian_weight_memLp L hL (Tr t.val.toNNReal fr))
  have heG : H t - W (Tr t.val.toNNReal fr) = hmG.toLp G :=
    ((hFm t t.property).toLp_sub
      (short_time_gaussian_weight_memLp L hL (Tr t.val.toNNReal fr))).symm
  change (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
    ‖F (t, translate x ω) - V (t, x)‖ ^ 2) = ‖H t - W (Tr t.val.toNNReal fr)‖ ^ 2
  rw [heG, short_time_complex_L2_sq hmG]
  apply integral_congr_ae
  filter_upwards [heV t] with x hx
  dsimp only [G]
  rw [← hx, ← mul_sub, norm_mul, mul_pow]
  simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Gaussian energy finiteness and continuity for the actual transpose residual,
on the same event for every width and physical transpose semigroup. -/
theorem short_time_stationary_physical_transpose_gaussian_lintegral_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (F U : ℝ × FieldPair d → ℂ)
    (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g)
    (hprim : ∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ L : ℝ, 0 < L →
      ∀ (a : Vec d → Mat d)
        (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup a i ζ Pr Tr →
      ∀ (fr : Lp ℂ 2 (volume : Measure (Vec d))) (V : ℝ × Vec d → ℂ),
      (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2) volume ∧
        (∫⁻ x, ENNReal.ofReal (Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2)) =
          ENNReal.ofReal (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
            ‖F (t, translate x ω) - V (t, x)‖ ^ 2)) ∧
      ContinuousOn (fun t : ℝ => ∫⁻ x,
        ENNReal.ofReal (Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2)) (Icc (0 : ℝ) 1) := by
  filter_upwards [short_time_stationary_transpose_primitive_gaussian_strong_continuous
    hd Q hP hPdag f g F U hU heU hprim,
    short_time_stationary_physical_transpose_gaussian_energy_continuous
      hd Q hP hPdag f g F U hU heU hprim] with ω hω hcω
  intro L hL a Pr Tr hPr fr V heV
  have hi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖F (t, translate x ω) - V (t, x)‖ ^ 2) volume := by
    have hm := ((hω L hL).1 t ht).sub
      (short_time_gaussian_weight_memLp L hL (Tr t.toNNReal fr))
    apply hm.norm.integrable_sq.congr
    filter_upwards [heV t] with x hx
    change ‖(Real.exp (-euclideanSq x / L) : ℂ) * F (t, translate x ω) -
      (Real.exp (-euclideanSq x / L) : ℂ) * (Tr t.toNNReal fr) x‖ ^ 2 = _
    rw [← hx, ← mul_sub, norm_mul, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (-euclideanSq x / L) ^ 2 *
        ‖F (t, translate x ω) - V (t, x)‖ ^ 2)) =
        ENNReal.ofReal (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal (hi t ht)
      (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))).symm
  refine ⟨fun t ht => ⟨hi t ht, he t ht⟩, ?_⟩
  exact (ENNReal.continuous_ofReal.comp_continuousOn
    (hcω L hL a Pr Tr hPr fr V heV)).congr he

/-- The fixed Gaussian is below the comparison Gaussian throughout short time.
The wider L² weight supplies the integrability needed by the real integral. -/
theorem short_time_fixed_gaussian_energy_le_moving {d : ℕ} {L t : ℝ}
    (hL : 0 < L) (ht : t ∈ Icc (0 : ℝ) 1) (Y : Vec d → ℂ)
    (hY : Measurable Y)
    (hY2 : MemLp (fun x => (Real.exp (-euclideanSq x / (2 * L)) : ℂ) * Y x)
      2 volume) :
    (∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖Y x‖ ^ 2) ≤
      ∫ x, Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2 * ‖Y x‖ ^ 2 := by
  have hw (l : ℝ) : Measurable (fun x : Vec d =>
      (Real.exp (-euclideanSq x / l) : ℂ) * Y x) := by
    have hm : Measurable (fun x : Vec d => (Real.exp (-euclideanSq x / l) : ℂ)) := by
      dsimp only [euclideanSq, dot]
      fun_prop
    exact hm.mul hY
  have hden : 0 < L * (2 - t) := mul_pos hL (by linarith only [ht.2])
  have he (x : Vec d) :
      Real.exp (-euclideanSq x / L) ≤
        Real.exp (-euclideanSq x / (L * (2 - t))) ∧
      Real.exp (-euclideanSq x / (L * (2 - t))) ≤
        Real.exp (-euclideanSq x / (2 * L)) := by
    constructor <;> apply Real.exp_le_exp.mpr
    · apply (div_le_div_iff₀ hL hden).2
      nlinarith only [mul_nonneg (euclideanSq_nonneg_coords x)
        (mul_nonneg hL.le (sub_nonneg.mpr ht.2))]
    · apply (div_le_div_iff₀ hden (by positivity : 0 < 2 * L)).2
      nlinarith only [mul_nonneg (euclideanSq_nonneg_coords x) (mul_nonneg hL.le ht.1)]
  have hm : MemLp (fun x => (Real.exp (-euclideanSq x / (L * (2 - t))) : ℂ) * Y x)
      2 volume := by
    apply hY2.of_le (hw _).aestronglyMeasurable
    filter_upwards with x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (he x).2 (norm_nonneg _)
  have hi : Integrable (fun x =>
      Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2 * ‖Y x‖ ^ 2) volume := by
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hm.norm.integrable_sq
  apply integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) hi
  filter_upwards with x
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Real.exp_nonneg _) (he x).1 2) (sq_nonneg _)

/-- The actual transpose comparison holds on one event for every short time,
with the fixed Gaussian needed by the local maximum estimate. The conservative
comparison constants and retained datum are unchanged. -/
theorem short_time_transpose_drift_fixed_gaussian_comparison_common_event
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B)
    (g : Lp ℂ 2 (reducedLaw Q)) (F U : ℝ × FieldPair d → ℂ)
    (hF : Measurable F) (hU : Measurable U)
    (heF : ∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal (β i))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g)
    (hprim : ∀ s ω, F (s, ω) = (β i) ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    let M := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
    let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) + 1
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ b : Vec d → Mat d, (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      (∀ᵐ x ∂volume, S5Elliptic (b x) Λ) →
      ∀ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup b i ζ Pr Tr →
      ∀ (fr : Lp ℂ 2 (volume : Measure (Vec d))) (V : ℝ × Vec d → ℂ),
      (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) →
      ∀ ρ L : ℝ, 64 * Λ ^ 3 ≤ L →
        (∀ x, euclideanSq x < ρ ^ 2 → b x = ω.1 x) →
        (∀ᵐ x ∂volume, euclideanSq x < ρ ^ 2 → (β i) (translate x ω) = fr x) →
      ∀ t ∈ Icc (0 : ℝ) 1,
      Real.exp (-γ * t) *
        (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2) ≤
      Real.exp (-ρ ^ 2 / (2 * L)) *
        (2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) + 2 * ‖fr‖ ^ 2) +
        Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
          (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
            2 * d * B ^ 2 * (2 * Λ) ^ 2 * t) *
          (Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * t) * ‖fr‖ ^ 2) := by
  intro Λ M γ
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hrat := ae_all_iff.mpr fun r : ℚ =>
    ae_all_iff.mpr fun hr0 : 0 ≤ (r : ℝ) =>
      ae_all_iff.mpr fun hr1 : (r : ℝ) ≤ 1 =>
        short_time_transpose_drift_gaussian_comparison hd D Q hQ β hβ i hP hPdag B hζ
          (r : ℝ).toNNReal (by simpa only [Real.coe_toNNReal _ hr0] using hr1)
  have hsp := ae_all_iff.mpr fun r : ℚ =>
    ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
      (hF.comp (measurable_const.prodMk measurable_id))
      (Lp.stronglyMeasurable (Pdag (r : ℝ).toNNReal (β i))).measurable (heF r)
  filter_upwards [hrat, hsp,
    short_time_stationary_physical_transpose_gaussian_energy_continuous
      hd Q hP hPdag (β i) g F U hU heU hprim,
    short_time_stationary_transpose_primitive_gaussian_strong_continuous
      hd Q hP hPdag (β i) g F U hU heU hprim] with ω hratω hspω hcont hmem
  intro b hb hbe Pr Tr hPr fr V heV ρ L hscale hinterior hinitial
  have hL : 0 < L := (by positivity : 0 < 64 * Λ ^ 3).trans_le hscale
  let H : ℝ → ℝ := fun t => ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
    ‖F (t, translate x ω) - V (t, x)‖ ^ 2
  let R : ℝ → ℝ := fun t =>
    Real.exp (-ρ ^ 2 / (2 * L)) *
      (2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) + 2 * ‖fr‖ ^ 2) +
      Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
        (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
          2 * d * B ^ 2 * (2 * Λ) ^ 2 * t) *
        (Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * t) * ‖fr‖ ^ 2)
  let E : ℝ → ℝ := fun t => Real.exp (-γ * t) * H t - R t
  have hH : ContinuousOn H (Icc (0 : ℝ) 1) := hcont L hL b Pr Tr hPr fr V heV
  have hR : Continuous R := by dsimp only [R]; fun_prop
  have hE : ContinuousOn E (Icc (0 : ℝ) 1) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hH
      |>.sub hR.continuousOn
  have hbound (r : ℚ) (hr0 : 0 ≤ (r : ℝ)) (hr1 : (r : ℝ) ≤ 1) : E r ≤ 0 := by
    have hr : (r : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hr0, hr1⟩
    let Y : Vec d → ℂ := fun x => F ((r : ℝ), translate x ω) - (Tr (r : ℝ).toNNReal fr) x
    have hY : Measurable Y := (hF.comp (measurable_const.prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const)))).sub (Lp.stronglyMeasurable _).measurable
    have hY2 : MemLp (fun x => (Real.exp (-euclideanSq x / (2 * L)) : ℂ) * Y x)
        2 volume := by
      convert ((hmem (2 * L) (by positivity)).1 r hr).sub
        (short_time_gaussian_weight_memLp (2 * L) (by positivity) (Tr (r : ℝ).toNNReal fr)) using 1
      funext x
      exact mul_sub _ _ _
    have hmoving := short_time_fixed_gaussian_energy_le_moving hL hr Y hY hY2
    have heq : Y =ᵐ[volume] (fun x =>
        (Pdag (r : ℝ).toNNReal (β i)) (translate x ω) - (Tr (r : ℝ).toNNReal fr) x) := by
      filter_upwards [hspω r] with x hx
      exact congrArg (fun z => z - (Tr (r : ℝ).toNNReal fr) x) hx
    have hcomparison := hratω r hr0 hr1 b hb hbe Pr Tr hPr fr ρ L hscale hinterior hinitial
    rw [Real.coe_toNNReal _ hr0] at hcomparison
    have hfixed : H r ≤ ∫ x, Real.exp (-euclideanSq x / (L * (2 - (r : ℝ)))) ^ 2 *
        ‖(Pdag (r : ℝ).toNNReal (β i)) (translate x ω) - (Tr (r : ℝ).toNNReal fr) x‖ ^ 2 := by
      calc
        H r = ∫ x, Real.exp (-euclideanSq x / L) ^ 2 * ‖Y x‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [heV r] with x hx
          simp only [Y, hx]
        _ ≤ ∫ x, Real.exp (-euclideanSq x / (L * (2 - (r : ℝ)))) ^ 2 * ‖Y x‖ ^ 2 := hmoving
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [heq] with x hx
          rw [hx]
    exact sub_nonpos.mpr ((mul_le_mul_of_nonneg_left hfixed (Real.exp_nonneg _)).trans hcomparison)
  let S : Set ℝ := Ioo (0 : ℝ) 1 ∩ Set.range ((↑) : ℚ → ℝ)
  have hS : closure S ⊆ Icc (0 : ℝ) 1 :=
    closure_minimal (fun _ hx => ⟨hx.1.1.le, hx.1.2.le⟩) isClosed_Icc
  have hI : Icc (0 : ℝ) 1 ⊆ closure S := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact closure_minimal
      (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo) isClosed_closure
  intro t ht
  have he : E t ≤ 0 := le_on_closure (s := S) (by
    rintro x ⟨hx, r, rfl⟩
    exact hbound r hx.1.le hx.2.le) (hE.mono hS) continuousOn_const (hI ht)
  exact sub_nonpos.mp he


/-- A fixed polynomial loss can be absorbed into half the Gaussian exponent,
with a constant depending only on the degree and the Gaussian scale. -/
theorem short_time_polynomial_gaussian_absorption (d : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      (1 + (2 * ρ) ^ d) * Real.exp (-(2 * a) * ρ ^ 2) ≤
        C * Real.exp (-a * ρ ^ 2) := by
  let C := 1 + (2 / a) ^ d * (d.factorial : ℝ)
  have hf : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro ρ hρ
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have harg : 0 ≤ a * ρ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have hp : (2 * ρ) ^ d ≤ (2 / a) ^ d * (a * ρ ^ 2) ^ d := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have he : 2 / a * (a * ρ ^ 2) = 2 * ρ ^ 2 := by field_simp
    rw [he]
    nlinarith
  have he : (a * ρ ^ 2) ^ d ≤ (d.factorial : ℝ) * Real.exp (a * ρ ^ 2) := by
    exact (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (a * ρ ^ 2) harg d) |>.trans_eq (mul_comm _ _)
  have hpoly : 1 + (2 * ρ) ^ d ≤ C * Real.exp (a * ρ ^ 2) := by
    have hpow := hp.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (2 / a) ^ d))
    have hone : 1 ≤ Real.exp (a * ρ ^ 2) := Real.one_le_exp_iff.mpr harg
    dsimp only [C]
    nlinarith only [hpow, hone]
  calc
    _ ≤ (C * Real.exp (a * ρ ^ 2)) * Real.exp (-(2 * a) * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The conservative transpose comparison loses only a polynomial factor in
the physical initial datum. Absorbing it gives constants before the radius,
time, and residual energy. The comparison radius is one quarter of the
cutoff radius, leaving a fixed interior region for the local maximum. -/
theorem short_time_transpose_gaussian_comparison_decay
    (d : ℕ) (Λ B M N L : ℝ) (hΛ : 0 < Λ) (hL : 0 < L) :
    let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) + 1
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ ρ t E n : ℝ,
      1 ≤ ρ → t ∈ Icc (0 : ℝ) 1 → 0 ≤ n → n ≤ N ^ 2 * (2 * ρ) ^ d →
      Real.exp (-γ * t) * E ≤
        Real.exp (-(ρ / 4) ^ 2 / (2 * L)) *
          (2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) + 2 * n) +
        Real.exp (-(ρ / 4) ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
          (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
            2 * d * B ^ 2 * (2 * Λ) ^ 2 * t) *
          (Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * t) * n) →
      E ≤ K * Real.exp (-c * ρ ^ 2) := by
  intro γ
  let a := 1 / (64 * L)
  let I := ∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))
  let H := 2 * (4 * Λ + 16 / L)
  let J := 2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
    2 * d * B ^ 2 * (2 * Λ) ^ 2
  let δ := 2 * ((d : ℝ) * Λ ^ 3 * B ^ 2)
  let A := 2 * M ^ 2 * I + (2 + H * J * Real.exp δ) * N ^ 2
  have ha : 0 < a := by dsimp only [a]; positivity
  obtain ⟨C, hC, habs⟩ := short_time_polynomial_gaussian_absorption d a ha
  have hI : 0 ≤ I := integral_nonneg fun _ => Real.exp_nonneg _
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨Real.exp γ * (A + 1) * C, a, by positivity, ha, ?_⟩
  intro ρ t E n hρ ht hn hnorm hcomp
  have ht0 : 0 ≤ t := ht.1
  let p := (2 * ρ) ^ d
  let e := Real.exp (-(2 * a) * ρ ^ 2)
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have he : 0 ≤ e := Real.exp_nonneg _
  have heq : -(ρ / 4) ^ 2 / (2 * L) = -(2 * a) * ρ ^ 2 := by dsimp only [a]; ring
  have htail : Real.exp (-(ρ / 4) ^ 2 / L) ≤ e := by
    apply Real.exp_le_exp.mpr
    rw [← heq]
    have hnonpos : -(ρ / 4) ^ 2 / (2 * L) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    have heq' : -(ρ / 4) ^ 2 / L = 2 * (-(ρ / 4) ^ 2 / (2 * L)) := by ring
    rw [heq']; linarith
  have htime : 2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
      2 * d * B ^ 2 * (2 * Λ) ^ 2 * t ≤ J := by
    dsimp only [J]
    have hm := mul_le_of_le_one_right
      (show 0 ≤ 2 * (d : ℝ) * B ^ 2 * (2 * Λ) ^ 2 by positivity) ht.2
    linarith only [hm]
  have hexp : Real.exp (δ * t) ≤ Real.exp δ :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_right hδ ht.2)
  have hsource : Real.exp (-(ρ / 4) ^ 2 / L) * H *
      (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
        2 * d * B ^ 2 * (2 * Λ) ^ 2 * t) * (Real.exp (δ * t) * n) ≤
      e * H * J * (Real.exp δ * (N ^ 2 * p)) := by
    apply mul_le_mul
    · exact mul_le_mul (mul_le_mul_of_nonneg_right htail hH) htime
        (by positivity) (mul_nonneg he hH)
    · exact mul_le_mul hexp hnorm hn (Real.exp_nonneg _)
    · positivity
    · positivity
  have hweighted : Real.exp (-γ * t) * E ≤ e * A * (1 + p) := by
    have hfirst : e * (2 * M ^ 2 * I + 2 * n) ≤
        e * (2 * M ^ 2 * I + 2 * (N ^ 2 * p)) := by gcongr
    rw [heq] at hcomp
    have hsum := hcomp.trans (add_le_add hfirst hsource)
    refine hsum.trans ?_
    have hconst : 0 ≤ 2 * M ^ 2 * I := by positivity
    have hcoef : 0 ≤ (2 + H * J * Real.exp δ) * N ^ 2 := by positivity
    dsimp only [A]
    nlinarith only [mul_nonneg he hconst, mul_nonneg he hcoef,
      mul_nonneg (mul_nonneg he hconst) hp, mul_nonneg he hp]
  calc
    E = Real.exp (γ * t) * (Real.exp (-γ * t) * E) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [neg_mul, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (γ * t) * (e * A * (1 + p)) :=
      mul_le_mul_of_nonneg_left hweighted (Real.exp_nonneg _)
    _ ≤ Real.exp γ * (e * A * (1 + p)) :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_of_le_one_right hγ ht.2)) (by positivity)
    _ = Real.exp γ * A * ((1 + p) * e) := by ring
    _ ≤ Real.exp γ * A * (C * Real.exp (-a * ρ ^ 2)) :=
      mul_le_mul_of_nonneg_left (habs ρ hρ) (by positivity)
    _ ≤ Real.exp γ * (A + 1) * (C * Real.exp (-a * ρ ^ 2)) := by gcongr; linarith
    _ = _ := by ring


/-- The retained coefficients are a convex combination with the identity,
so they preserve the actual ellipticity constant. -/
theorem short_time_retained_cutoff_elliptic {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) (x : Vec d) {Λ : ℝ} (hA : S5Elliptic (ω.1 x) Λ)
    (hχ0 : 0 ≤ χ x) (hχ1 : χ x ≤ 1) :
    S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ := by
  have hform (ξ : Fin d → ℝ) :
      s5Bil ((ForcedLocality.retainedPair χ ω).1 x) ξ ξ =
        χ x * s5Bil (ω.1 x) ξ ξ + (1 - χ x) * ∑ j, ξ j ^ 2 := by
    change (∑ j, ∑ k, ξ j *
      (χ x * ω.1 x j k + (1 - χ x) * (1 : Mat d) j k) * ξ k) = _
    simp only [mul_add, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
      mul_ite, ite_mul, mul_zero, zero_mul, mul_one]
    unfold s5Bil
    simp only [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
  refine ⟨hA.one_le, ?_, ?_, ?_⟩
  · intro j k
    change χ x * ω.1 x j k + (1 - χ x) * (1 : Mat d) j k =
      χ x * ω.1 x k j + (1 - χ x) * (1 : Mat d) k j
    rw [hA.symm j k]
    simp only [Matrix.one_apply, eq_comm]
  · intro ξ
    rw [hform]
    have hs : 0 ≤ ∑ j, ξ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hl := mul_le_mul_of_nonneg_left (hA.lower ξ) hχ0
    have hi := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hA.one_le) hs
    have he := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hχ1)
    linarith only [hl, he]
  · intro ξ
    rw [hform]
    have hs : 0 ≤ ∑ j, ξ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hu := mul_le_mul_of_nonneg_left (hA.upper ξ) hχ0
    have hi := mul_le_mul_of_nonneg_right hA.one_le hs
    have he := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hχ1)
    linarith only [hu, he]


/-- Uniform Gaussian decay for the actual retained transpose drift on one
sample event for all short times. The cutoff derivative is included in the
initial datum and its polynomial radius loss is absorbed into the Gaussian. -/
theorem short_time_transpose_actual_gaussian_decay_common_event
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B Cχ : ℝ) (hCχ : 0 ≤ Cχ) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    ∃ L K c : ℝ, 64 * Λ ^ 3 ≤ L ∧ 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P Pdag →
    ∀ (g : Lp ℂ 2 (reducedLaw Q)) (F U : ℝ × FieldPair d → ℂ),
      Measurable F → Measurable U →
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal (β i)) →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g) →
      (∀ s ω, F (s, ω) = (β i) ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) →
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (χ : C(Vec d, ℝ)), ContDiff ℝ (⊤ : ℕ∞) χ →
      ∀ ρ : ℝ, 1 ≤ ρ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) →
      (∀ j x, |coordinateDerivative j χ x| ≤ Cχ / ρ) →
      (∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
        (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
          (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
            (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      ∀ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
      ∀ V : ℝ × Vec d → ℂ,
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2) ≤
          K * Real.exp (-c * ρ ^ 2) := by
  intro Λ
  let L := 64 * Λ ^ 3 + 1
  let M := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
  let N := M + (1 / 2 : ℝ) * d * (Λ + 1) * Cχ
  have hΛ1 : 1 ≤ Λ := by
    have he : 1 ≤ Real.exp (2 * D.ellipticity) :=
      Real.one_le_exp_iff.mpr (by linarith [D.one_le_ellipticity])
    exact (one_mul (1 : ℝ)).symm.trans_le
      (mul_le_mul he D.one_le_ellipticity zero_le_one (Real.exp_nonneg _))
  have hΛ : 0 < Λ := zero_lt_one.trans_le hΛ1
  have hL : 0 < L := by dsimp only [L]; positivity
  obtain ⟨K, c, hK, hc, hdecay⟩ :=
    short_time_transpose_gaussian_comparison_decay d Λ B M N L hΛ hL
  have hscale : 64 * Λ ^ 3 ≤ L := by dsimp only [L]; linarith
  refine ⟨L, K, c, hscale, hL, hK, hc, ?_⟩
  intro Q hQ β hβ i ζ hζ P Pdag hP hPdag g F U hF hU heF heU hprim
  filter_upwards [short_time_transpose_drift_fixed_gaussian_comparison_common_event
    hd D Q hQ β hβ i hP hPdag B hζ g F U hF hU heF heU hprim,
    short_time_transpose_actual_retained_drift_norm_sq hβ i,
    short_time_transpose_drift_spatial_identification hβ i,
    c4_ae_reduced_physical_elliptic Q] with ω hcompare hnorm hbi hA
  intro χ hχ ρ hρ hχb hχzero hχder hin fr hfr Pr Tr hPr V heV t ht
  have hret (x : Vec d) : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    short_time_retained_cutoff_elliptic χ ω x (s5Elliptic_of_isElliptic hΛ1 hA x)
      (hχb x).1 (hχb x).2
  have hb (j k : Fin d) :
      MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume := by
    apply memLp_top_of_bound
      (Complex.continuous_ofReal.comp
        ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k)).aestronglyMeasurable Λ
    exact ae_of_all _ fun x => by
      change ‖(((ForcedLocality.retainedPair χ ω).1 x j k : ℝ) : ℂ)‖ ≤ Λ
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hret x).entry_abs_le j k
  let O : Set (Vec d) := {x | euclideanNorm x < ρ / 4}
  have hO : IsOpen O := isOpen_lt (by unfold euclideanNorm euclideanSq dot; fun_prop) continuous_const
  have hχO : ∀ x ∈ O, χ x = 1 := fun x hx => hin x hx.le
  have hinside (x : Vec d) (hx : euclideanSq x < (ρ / 4) ^ 2) : x ∈ O := by
    change Real.sqrt (euclideanSq x) < ρ / 4
    exact (Real.sqrt_lt (euclideanSq_nonneg_coords x) (by linarith : 0 ≤ ρ / 4)).2 hx
  have hcoeff (x : Vec d) (hx : euclideanSq x < (ρ / 4) ^ 2) :
      (ForcedLocality.retainedPair χ ω).1 x = ω.1 x :=
    (ForcedLocality.retainedPair_eq_at χ ω (hχO x (hinside x hx))).1
  have hinitial : ∀ᵐ x ∂volume, euclideanSq x < (ρ / 4) ^ 2 →
      (β i) (translate x ω) = fr x := by
    filter_upwards [hbi, hfr] with x hbx hfrx
    intro hx
    rw [hbx, hfrx]
    exact congrArg (fun z : ℝ => (z : ℂ))
      (ForcedLocality.retainedPair_drift χ ω hO hχO (hinside x hx) i).symm
  apply hdecay ρ t _ (‖fr‖ ^ 2) hρ ht (sq_nonneg _)
    (hnorm χ hχ Cχ ρ hCχ hρ hχb hχzero hχder fr hfr)
  exact hcompare (ForcedLocality.retainedPair χ ω).1 hb (ae_of_all _ hret)
    Pr Tr hPr fr V heV (ρ / 4) L hscale hcoeff hinitial t ht


/-- Gaussian spacetime decay for any measurable representative of the actual
transpose orbit. Stationary spacetime congruence lets the local maximum use
the same residual already supplied by the conservative retained equation. -/
theorem short_time_transpose_actual_gaussian_spacetime_decay
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B Cχ : ℝ) (hCχ : 0 ≤ Cχ) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    ∃ L K c : ℝ, 64 * Λ ^ 3 ≤ L ∧ 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P Pdag →
    ∀ (g : Lp ℂ 2 (reducedLaw Q)), IsComplexTransposeGeneratorPair Q i ζ (β i) g →
    ∀ F : ℝ × FieldPair d → ℂ, Measurable F →
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal (β i)) →
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (χ : C(Vec d, ℝ)), ContDiff ℝ (⊤ : ℕ∞) χ →
      ∀ ρ : ℝ, 1 ≤ ρ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) →
      (∀ j x, |coordinateDerivative j χ x| ≤ Cχ / ρ) →
      (∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
        (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
          (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
            (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      ∀ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
      ∀ V : ℝ × Vec d → ℂ, Measurable V →
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) →
        (∫⁻ z in Icc (0 : ℝ) 1 ×ˢ (univ : Set (Vec d)),
          ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) ^ 2 *
            ‖F (z.1, translate z.2 ω) - V z‖ ^ 2)) ≤
              ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2)) := by
  intro Λ
  obtain ⟨L, K, c, hscale, hL, hK, hc, hcommon⟩ :=
    short_time_transpose_actual_gaussian_decay_common_event d hd D B Cχ hCχ
  refine ⟨L, K, c, hscale, hL, hK, hc, ?_⟩
  intro Q hQ β hβ i ζ hζ P Pdag hP hPdag g hfg F hF heF
  obtain ⟨F₀, U, hF₀, hU, heF₀, heU, hprim⟩ :=
    short_time_stationary_transpose_joint_primitive hP hPdag hfg
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hcong : ∀ᵐ ω ∂reducedLaw Q,
      (fun z : ℝ × Vec d => F (z.1, translate z.2 ω)) =ᵐ[
        (volume.restrict (Icc (0 : ℝ) 1)).prod volume]
      (fun z => F₀ (z.1, translate z.2 ω)) := by
    have hm : Measurable (fun q : (ℝ × Vec d) × FieldPair d =>
        (q.1.1, translate q.1.2 q.2)) :=
      measurable_fst.fst.prodMk (Probability.continuous_translate.measurable.comp
        (measurable_fst.snd.prodMk measurable_snd))
    apply (Measure.ae_ae_comm
      (μ := (volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure (Vec d)))
      (ν := reducedLaw Q)
      (p := fun z ω => F (z.1, translate z.2 ω) = F₀ (z.1, translate z.2 ω))
      (measurableSet_eq_fun (hF.comp hm) (hF₀.comp hm))).mp
    exact ae_of_all _ fun z =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) z.2).quasiMeasurePreserving.ae
        ((heF z.1).trans (heF₀ z.1).symm)
  filter_upwards [hcommon Q hQ β hβ i ζ hζ P Pdag hP hPdag
    g F₀ U hF₀ hU heF₀ heU hprim, hcong,
    short_time_stationary_transpose_primitive_gaussian_strong_continuous
      hd Q hP hPdag (β i) g F₀ U hU heU hprim] with ω hbound heω hmem
  intro χ hχ ρ hρ hχb hχzero hχder hin fr hfr Pr Tr hPr V hV heV
  let H : ℝ × Vec d → ℝ := fun z => Real.exp (-euclideanSq z.2 / L) ^ 2 *
    ‖F₀ (z.1, translate z.2 ω) - V z‖ ^ 2
  have hshift : Measurable (fun z : ℝ × Vec d => (z.1, translate z.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hw : Measurable (fun z : ℝ × Vec d => Real.exp (-euclideanSq z.2 / L) ^ 2) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  have hH : Measurable H := hw.mul (((hF₀.comp hshift).sub hV).norm.pow_const 2)
  have hhi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Integrable (fun x => H (t, x)) volume := by
    have hm := ((hmem L hL).1 t ht).sub
      (short_time_gaussian_weight_memLp L hL (Tr t.toNNReal fr))
    apply hm.norm.integrable_sq.congr
    filter_upwards [heV t] with x hx
    change ‖(Real.exp (-euclideanSq x / L) : ℂ) * F₀ (t, translate x ω) -
      (Real.exp (-euclideanSq x / L) : ℂ) * (Tr t.toNNReal fr) x‖ ^ 2 = H (t, x)
    dsimp only [H]
    rw [← hx, ← mul_sub, norm_mul, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have henergy : (∫⁻ z in Icc (0 : ℝ) 1 ×ˢ (univ : Set (Vec d)),
      ENNReal.ofReal (H z)) ≤ ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2)) := by
    rw [Measure.volume_eq_prod, setLIntegral_prod
      (fun z : ℝ × Vec d => ENNReal.ofReal (H z)) hH.ennreal_ofReal.aemeasurable,
      Measure.restrict_univ]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [← ofReal_integral_eq_lintegral_ofReal (hhi t ht)
          (ae_of_all _ fun x => by dsimp only [H]; positivity)]
        exact ENNReal.ofReal_le_ofReal
          (hbound χ hχ ρ hρ hχb hχzero hχder hin fr hfr Pr Tr hPr V heV t ht)
      _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ,
        Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  have heω' : (fun z : ℝ × Vec d => F (z.1, translate z.2 ω)) =ᵐ[
      volume.restrict (Icc (0 : ℝ) 1 ×ˢ (univ : Set (Vec d)))]
      (fun z => F₀ (z.1, translate z.2 ω)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    exact heω
  refine (lintegral_congr_ae ?_).trans_le henergy
  filter_upwards [heω'] with z hz
  dsimp only [H]
  rw [hz]

/- The C¹ test extension follows the checked forward argument in C7:6325–6553.
Only the test-class approximation is reused; the transpose flux below is literal. -/
open PDE PDE.Parabolic.Energy Metric in
private theorem transpose_C1_test_approximation {d : ℕ} {φ : EinsteinRelation.Vec d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    {K : Set (EinsteinRelation.Vec d)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hδK : cthickening δ (tsupport φ) ⊆ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : EinsteinRelation.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ K ∧ (∀ x, |φ x - ψ x| ≤ ε) ∧
      ∀ j x, |coordinateDerivative j φ x - coordinateDerivative j ψ x| ≤ ε := by
  let Dφ : Fin d → EinsteinRelation.Vec d → ℝ := fun j x => fderiv ℝ φ x (basisVec j)
  have hDc (j : Fin d) : Continuous (Dφ j) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDzero (j : Fin d) (x : EinsteinRelation.Vec d) (hx : x ∉ tsupport φ) : Dφ j x = 0 := by
    simp [Dφ, fderiv_of_notMem_tsupport ℝ hx]
  have hDcs (j : Fin d) : HasCompactSupport (Dφ j) := by
    refine HasCompactSupport.of_support_subset_isCompact hφc.isCompact ?_
    intro x hx
    by_contra h
    exact hx (hDzero j x h)
  obtain ⟨a₀, ha₀, hclose₀⟩ :=
    exists_forall_dist_wholeSpaceMollify_le hφ.continuous hφc hε
  have hex (j : Fin d) := exists_forall_dist_wholeSpaceMollify_le (hDc j) (hDcs j) hε
  choose a₁ ha₁ hclose₁ using hex
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      0 < a ∧ a ≤ δ ∧ a ≤ a₀ ∧ ∀ j, a ≤ a₁ j := by
    have hall : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ j, a ≤ a₁ j := by
      rw [eventually_all]
      intro j
      filter_upwards [Ioc_mem_nhdsGT (ha₁ j)] with a ha using ha.2
    filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT hδ,
      Ioc_mem_nhdsGT ha₀, hall] with a ha hδa h₀a h₁a
    exact ⟨ha, hδa.2, h₀a.2, h₁a⟩
  obtain ⟨a, ha, haδ, haa₀, haa₁⟩ := hev.exists
  let ψ := wholeSpaceMollify a φ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := moll_contDiff ha hφ.continuous.locallyIntegrable
  have hsupp : Function.support ψ ⊆ cthickening a (tsupport φ) :=
    PDE.Ch4Infra.support_wholeSpaceMollify_subset_cthickening ha
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (hφc.isCompact.cthickening (r := a)) hsupp
  have hψK : tsupport ψ ⊆ K :=
    closure_minimal (hsupp.trans ((cthickening_mono haδ _).trans hδK)) hK.isClosed
  refine ⟨ψ, hψ, hψc, hψK, ?_, ?_⟩
  · intro x
    have hb := hclose₀ a ha haa₀ x
    rwa [Real.dist_eq, abs_sub_comm] at hb
  · intro j x
    have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
    have hd : fderiv ℝ ψ x (basisVec j) = wholeSpaceMollify a (Dφ j) x :=
      congrFun (euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
        (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha)
        (contDiff_scaledConvexApproxKernel hρ _) hφ.continuous.locallyIntegrable
        (HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := j) hφ)) x
    have hb := hclose₁ j a ha (haa₁ j) x
    rw [Real.dist_eq, abs_sub_comm] at hb
    rw [← hd] at hb
    simpa only [coordinateDerivative, unitVector, basisVec, Dφ] using hb

private theorem transpose_weak_divergence_C1 {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {F : Vec d → Vec d} {g : Vec d → ℝ} (hw : HasWeakDivergence U F g)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ interior U) :
    (∫ x in U, dot (F x) (gradient φ x)) = -(∫ x in U, g x * φ x) := by
  obtain ⟨δ, hδ, hδU⟩ := hφc.isCompact.exists_cthickening_subset_open isOpen_interior hφU
  let K := Metric.cthickening δ (tsupport φ)
  have hK : IsCompact K := hφc.isCompact.cthickening
  have hKU : K ⊆ U := hδU.trans interior_subset
  have hφK : tsupport φ ⊆ K := Metric.self_subset_cthickening _
  have hF (j : Fin d) : Integrable (fun x => F x j) (volume.restrict K) :=
    (hw.1 j).integrableOn_compact_subset hKU hK
  have hg : Integrable g (volume.restrict K) :=
    hw.2.1.integrableOn_compact_subset hKU hK
  have hbd {f q : Vec d → ℝ} (hf : Integrable f (volume.restrict K))
      (hq : Continuous q) (hqc : HasCompactSupport q) :
      Integrable (fun x => f x * q x) (volume.restrict K) := by
    obtain ⟨C, hC⟩ := hq.bounded_above_of_compact_support hqc
    exact hf.mul_bdd hq.aestronglyMeasurable (c := C) (Eventually.of_forall hC)
  have hder {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q)
      (j : Fin d) : Continuous (coordinateDerivative j q) ∧
      HasCompactSupport (coordinateDerivative j q) := by
    refine ⟨(hq.continuous_fderiv one_ne_zero).clm_apply continuous_const, ?_⟩
    refine HasCompactSupport.of_support_subset_isCompact hqc.isCompact ?_
    intro x hx
    by_contra h
    exact hx (by simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ h])
  have hcut {q : Vec d → ℝ} (hqK : tsupport q ⊆ K) :
      (∫ x in U, dot (F x) (gradient q x)) =
        ∫ x in K, dot (F x) (gradient q x) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hKU
    intro x hx
    have hxq : x ∉ tsupport q := fun h => hx.2 (hqK h)
    simp [dot, gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxq]
  have hcutg {q : Vec d → ℝ} (hqK : tsupport q ⊆ K) :
      (∫ x in U, g x * q x) = ∫ x in K, g x * q x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hKU
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx.2 (hqK h)), mul_zero]
  have hsum {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q) :
      (∫ x in K, dot (F x) (gradient q x)) =
        ∑ j, ∫ x in K, F x j * coordinateDerivative j q x := by
    exact integral_finsetSum _ (fun j _ => hbd (hF j) (hder hq hqc j).1
      (hder hq hqc j).2)
  let E := (∫ x in K, dot (F x) (gradient φ x)) + ∫ x in K, g x * φ x
  let C := (∑ j, ∫ x in K, |F x j|) + ∫ x in K, |g x|
  have hmain (ε : ℝ) (hε : 0 < ε) : |E| ≤ ε * C := by
    obtain ⟨ψ, hψ, hψc, hψK, hclose, hDclose⟩ :=
      transpose_C1_test_approximation hφ hφc hK hδ (Subset.refl K) hε
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
    have hid := hw.2.2 ψ ⟨hψ, hψc, hψK.trans hKU⟩
    rw [hcut hψK, hcutg hψK] at hid
    have hdiff : E = (∑ j, ∫ x in K, F x j *
        (coordinateDerivative j φ x - coordinateDerivative j ψ x)) +
        ∫ x in K, g x * (φ x - ψ x) := by
      simp_rw [mul_sub]
      rw [integral_sub (hbd hg hφ.continuous hφc) (hbd hg hψ.continuous hψc)]
      have hj (j : Fin d) := integral_sub
        (hbd (hF j) (hder hφ hφc j).1 (hder hφ hφc j).2)
        (hbd (hF j) (hder hψ1 hψc j).1 (hder hψ1 hψc j).2)
      simp_rw [hj]
      rw [Finset.sum_sub_distrib, ← hsum hφ hφc, ← hsum hψ1 hψc]
      dsimp [E]
      linarith
    have hb {f q : Vec d → ℝ} (hf : Integrable f (volume.restrict K))
        (hq : ∀ x, |q x| ≤ ε) :
        |∫ x in K, f x * q x| ≤ ε * ∫ x in K, |f x| := by
      calc
        |∫ x in K, f x * q x| ≤ ∫ x in K, |f x * q x| :=
          abs_integral_le_integral_abs
        _ ≤ ∫ x in K, ε * |f x| := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (hf.abs.const_mul ε) (Eventually.of_forall ?_)
          intro x
          change |f x * q x| ≤ ε * |f x|
          rw [abs_mul]
          nlinarith [hq x, abs_nonneg (f x)]
        _ = ε * ∫ x in K, |f x| := integral_const_mul _ _
    rw [hdiff]
    calc
      _ ≤ |∑ j, ∫ x in K, F x j *
          (coordinateDerivative j φ x - coordinateDerivative j ψ x)| +
          |∫ x in K, g x * (φ x - ψ x)| := abs_add_le _ _
      _ ≤ (∑ j, |∫ x in K, F x j *
          (coordinateDerivative j φ x - coordinateDerivative j ψ x)|) +
          |∫ x in K, g x * (φ x - ψ x)| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
      _ ≤ (∑ j, ε * ∫ x in K, |F x j|) + ε * ∫ x in K, |g x| :=
        add_le_add (Finset.sum_le_sum fun j _ => hb (hF j) (hDclose j)) (hb hg hclose)
      _ = ε * C := by rw [← Finset.mul_sum]; dsimp [C]; ring
  have hC : 0 ≤ C := add_nonneg
    (Finset.sum_nonneg fun j _ => integral_nonneg fun x => abs_nonneg _)
    (integral_nonneg fun x => abs_nonneg _)
  have hE : E = 0 := by
    by_contra hne
    have hpos := abs_pos.mpr hne
    have hb := hmain (|E| / (2 * (C + 1))) (by positivity)
    have hh : |E| / (2 * (C + 1)) * C < |E| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [hcut hφK, hcutg hφK]
  dsimp [E] at hE
  linarith

private theorem transpose_spacetime_weak_equation_C1 {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u v b : ℝ × Vec d → ℝ)
    (F : ℝ × Vec d → Vec d)
    (htime : ∀ᵐ x ∂volume.restrict U, ∀ ψ : ℝ → ℝ,
      ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
      (∫ s in (-1 : ℝ)..1, deriv ψ s * u (s, x) + ψ s * v (s, x)) = 0)
    (hspace : ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
      HasWeakDivergence U (fun x => F (s, x)) (fun x => v (s, x) - b (s, x)))
    (φ : ℝ × Vec d → ℝ)
    (hφt : ∀ x, ContDiff ℝ 1 (fun s => φ (s, x)))
    (hφl : ∀ x, φ (-1, x) = 0) (hφr : ∀ x, φ (1, x) = 0)
    (hφx : ∀ s, ContDiff ℝ 1 (fun x => φ (s, x)) ∧
      HasCompactSupport (fun x => φ (s, x)) ∧ tsupport (fun x => φ (s, x)) ⊆ interior U)
    (hu : Integrable (fun p : ℝ × Vec d =>
      deriv (fun s => φ (s, p.2)) p.1 * u p)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hv : Integrable (fun p : ℝ × Vec d => φ p * v p)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hF : Integrable (fun p : ℝ × Vec d =>
      dot (F p) (gradient (fun x => φ (p.1, x)) p.2))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hb : Integrable (fun p : ℝ × Vec d => φ p * b p)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U))) :
    (∫ p : ℝ × Vec d,
      deriv (fun s => φ (s, p.2)) p.1 * u p -
        dot (F p) (gradient (fun x => φ (p.1, x)) p.2) + φ p * b p
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) = 0 := by
  have ht : (∫ p : ℝ × Vec d,
      deriv (fun s => φ (s, p.2)) p.1 * u p + φ p * v p
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) = 0 := by
    have hp := integral_prod_symm _ (hu.add hv)
    simp only [Pi.add_apply] at hp
    rw [hp]
    apply integral_eq_zero_of_ae
    filter_upwards [htime] with x hx
    have he := hx (fun s => φ (s, x)) (hφt x) (hφl x) (hφr x)
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc] at he
    exact he
  have hs : (∫ p : ℝ × Vec d,
      dot (F p) (gradient (fun x => φ (p.1, x)) p.2)
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) =
      -(∫ p : ℝ × Vec d, φ p * v p - φ p * b p
        ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) := by
    have hp := integral_prod _ (hv.sub hb)
    simp only [Pi.sub_apply] at hp
    rw [integral_prod _ hF, hp, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hspace] with s hs
    have he := transpose_weak_divergence_C1 hU hs
      (hφx s).1 (hφx s).2.1 (hφx s).2.2
    rw [he]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hsum := integral_add (hu.sub hF) hb
  have hdiff := integral_sub hu hF
  have htv := integral_add hu hv
  have hvb := integral_sub hv hb
  simp only [Pi.sub_apply] at hsum hdiff htv hvb
  rw [hsum, hdiff]
  rw [htv] at ht
  rw [hvb] at hs
  linarith

/-- The actual conservative transpose equation admits compactly supported
`C¹` spacetime tests. Both the coefficient orientation and the signed force
remain inside the divergence. -/
theorem short_time_transpose_conservative_C1_weak_equation {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (A : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ) (X Y : ℝ × Vec d → ℂ)
    (J : ℝ → Vec d → Fin d → ℂ)
    (htime : ∀ᵐ x ∂volume.restrict U, ∀ L : ℂ →L[ℝ] ℝ,
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
        (∫ s in (-1 : ℝ)..1,
          deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0)
    (hspace : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence U
        (fun x j => L ((∑ k, (A x j k : ℂ) * J s x k) -
          2 * ζ * (A x j i : ℂ) * X (s, x)))
        (fun x => L (2 * Y (s, x))))
    (φ : ℝ × Vec d → ℝ)
    (hφt : ∀ x, ContDiff ℝ 1 (fun s => φ (s, x)))
    (hφl : ∀ x, φ (-1, x) = 0) (hφr : ∀ x, φ (1, x) = 0)
    (hφx : ∀ s, ContDiff ℝ 1 (fun x => φ (s, x)) ∧
      HasCompactSupport (fun x => φ (s, x)) ∧
      tsupport (fun x => φ (s, x)) ⊆ interior U)
    (L : ℂ →L[ℝ] ℝ)
    (hu : Integrable (fun p : ℝ × Vec d =>
      deriv (fun s => φ (s, p.2)) p.1 * L (X p))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hv : Integrable (fun p : ℝ × Vec d => φ p * L (Y p))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hF : Integrable (fun p : ℝ × Vec d =>
      dot (fun j => L ((1 / 2 : ℂ) * ∑ k, (A p.2 j k : ℂ) * J p.1 p.2 k -
        ζ * (A p.2 j i : ℂ) * X p)) (gradient (fun x => φ (p.1, x)) p.2))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U))) :
    (∫ p : ℝ × Vec d,
      deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
        dot (fun j => L ((1 / 2 : ℂ) * ∑ k, (A p.2 j k : ℂ) * J p.1 p.2 k -
          ζ * (A p.2 j i : ℂ) * X p)) (gradient (fun x => φ (p.1, x)) p.2)
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) = 0 := by
  have hhalf (z : ℂ) : L ((1 / 2 : ℂ) * z) = (1 / 2 : ℝ) * L z := by
    rw [show (1 / 2 : ℂ) * z = (1 / 2 : ℝ) • z by simp, map_smul]
    rfl
  have hspace' : ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
      HasWeakDivergence U
        (fun x j => L ((1 / 2 : ℂ) * ∑ k, (A x j k : ℂ) * J s x k -
          ζ * (A x j i : ℂ) * X (s, x))) (fun x => L (Y (s, x)) - 0) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hspace] with s hs
    have hh := hs ((1 / 2 : ℝ) • L)
    have hflux : (fun x j => ((1 / 2 : ℝ) • L)
        ((∑ k, (A x j k : ℂ) * J s x k) - 2 * ζ * (A x j i : ℂ) * X (s, x))) =
        (fun x j => L ((1 / 2 : ℂ) * ∑ k, (A x j k : ℂ) * J s x k -
          ζ * (A x j i : ℂ) * X (s, x))) := by
      funext x j
      change (1 / 2 : ℝ) * L _ = _
      rw [← hhalf]
      congr 1
      ring
    have hsource : (fun x => ((1 / 2 : ℝ) • L) (2 * Y (s, x))) =
        (fun x => L (Y (s, x)) - 0) := by
      funext x
      change (1 / 2 : ℝ) * L (2 * Y (s, x)) = _
      rw [show (2 : ℂ) * Y (s, x) = (2 : ℝ) • Y (s, x) by simp, map_smul]
      simp
    rw [hflux, hsource] at hh
    exact hh
  have hw := transpose_spacetime_weak_equation_C1 U hU (fun p => L (X p))
    (fun p => L (Y p)) 0
    (fun p j => L ((1 / 2 : ℂ) * ∑ k, (A p.2 j k : ℂ) * J p.1 p.2 k -
      ζ * (A p.2 j i : ℂ) * X p))
    (htime.mono fun x hx => hx L) hspace' φ hφt hφl hφr hφx hu hv hF
    (by simp only [Pi.zero_apply, mul_zero]; exact integrable_zero _ _ _)
  simpa only [Pi.zero_apply, mul_zero, add_zero] using hw

/-- The same actual retained transpose residual has its spatial weak gradients,
spacetime `L²` bound and conservative equation for `C¹` tests on each plateau.
All conclusions use the representatives selected by the actual C8 equation. -/
theorem short_time_transpose_actual_retained_C1_equation
    {d : ℕ} (S : StructuralData d)
    (Q : EnvironmentLaw d S.ellipticity S.dependenceRange)
    (hQ : HasSmoothBounds S Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) :
    ∃ F : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal (β i)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (complexTransposeGradientOrbit Q Pdag (β i) s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ j k, MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ᵐ x ∂volume, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (((1 / 2 : ℝ) * ∑ j, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      ∃ V X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        Measurable V ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Tr s.toNNReal fr) (H s)) ∧
        ∀ O K : Set (Vec d), IsOpen O → (∀ x ∈ O, χ x = 1) →
          IsCompact K → K ⊆ O →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          let J := fun s x k => (Ioc (0 : ℝ) 1).indicator
            (fun r => D k (r, translate x ω) - H r k x) s
          (∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
            HasWeakGradient (interior K) (fun x => (X (s, x)).re)
              (fun x k => (J s x k).re) ∧
            HasWeakGradient (interior K) (fun x => (X (s, x)).im)
              (fun x k => (J s x k).im)) ∧
          ∀ φ : ℝ × Vec d → ℝ,
            (∀ x, ContDiff ℝ 1 (fun s => φ (s, x))) →
            (∀ x, φ (-1, x) = 0) → (∀ x, φ (1, x) = 0) →
            (∀ s, ContDiff ℝ 1 (fun x => φ (s, x)) ∧
              HasCompactSupport (fun x => φ (s, x)) ∧
              tsupport (fun x => φ (s, x)) ⊆ interior K) →
            ∀ L : ℂ →L[ℝ] ℝ,
            Integrable (fun p : ℝ × Vec d =>
              deriv (fun s => φ (s, p.2)) p.1 * L (X p))
              ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict (interior K))) →
            Integrable (fun p : ℝ × Vec d => φ p * L (Y p))
              ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict (interior K))) →
            Integrable (fun p : ℝ × Vec d =>
              dot (fun j => L ((1 / 2 : ℂ) * ∑ k, (ω.1 p.2 j k : ℂ) * J p.1 p.2 k -
                ζ * (ω.1 p.2 j i : ℂ) * X p)) (gradient (fun x => φ (p.1, x)) p.2))
              ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict (interior K))) →
            (∫ p : ℝ × Vec d,
              deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
                dot (fun j => L ((1 / 2 : ℂ) * ∑ k, (ω.1 p.2 j k : ℂ) * J p.1 p.2 k -
                  ζ * (ω.1 p.2 j i : ℂ) * X p)) (gradient (fun x => φ (p.1, x)) p.2)
              ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict (interior K))) = 0 := by
  obtain ⟨F, D, hF, hD, heF, heD, hactual⟩ :=
    short_time_transpose_actual_retained_zero_extension_equation S Q hQ β hβ i hP hPdag
  refine ⟨F, D, hF, hD, heF, heD, ?_⟩
  filter_upwards [hactual,
    short_time_transpose_coherent_residual_spacetime_memLp Q hP hPdag (β i) F hF heF]
    with ω hactualω hmemω
  intro χ hχ hc ha Λ hΛ hA Pr Tr hPr fr hfr
  obtain ⟨V, X, Y, H, hV, hX, hY, heV, hX0, hHc, hH, hlocal⟩ :=
    hactualω χ hχ hc ha Λ hΛ hA Pr Tr hPr fr hfr
  refine ⟨V, X, Y, H, hV, hX, hY, heV, hX0, hHc, hH, ?_⟩
  intro O K hO hχO hK hKO
  obtain ⟨heX, htime, hgrad, hdiv⟩ := hlocal O K hO hχO hK hKO
  refine ⟨heX, htime, hmemω _ Pr Tr hPr fr V X hV hX heV hX0 K hK heX, hgrad, ?_⟩
  intro φ hφt hφl hφr hφx L hu hv hflux
  apply short_time_transpose_conservative_C1_weak_equation (interior K)
    isOpen_interior.measurableSet ω.1 i ζ X Y _ ?_ hdiv φ hφt hφl hφr ?_ L hu hv hflux
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset interior_subset htime] with x hx
    exact fun L => (hx L).2
  · simpa only [interior_interior] using hφx

/-- The prescribed continuous physical gradient has a jointly measurable
representative with square integrable norm on every compact time interval.
Gradient uniqueness identifies the C8 representative with the same `H`. -/
theorem short_time_transpose_joint_representative_of_physical_gradient
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hHc : ∀ j, Continuous (fun s => H s j))
    (hH : ∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal f) (H s)) :
    ∃ W : Fin d → ℝ × Vec d → ℂ,
      (∀ j, Measurable (W j)) ∧
      (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
      ∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
        ((volume.restrict (Icc l r)).prod volume) := by
  obtain ⟨G, W, hG, _, hW, heW, _⟩ :=
    short_time_physical_transpose_joint_gradient ha hΛ hA hP hfg
  have heGH (s : ℝ) : G s = H s :=
    physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ (hG s) (hH s)
  have heH (j : Fin d) (s : ℝ) : (fun x => W j (s, x)) =ᵐ[volume] H s j := by
    simpa only [heGH s] using heW j s
  refine ⟨W, hW, heH, ?_⟩
  intro j l r
  exact short_time_joint_sq_integrable
    (((hHc j).norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc l r) isCompact_Icc) (hW j) (heH j)

/-- Joint representatives of the actual transpose orbit, generator orbit and
gradient have square integrable translates on every compact spatial set, on
one sample event. No retained evolution is reselected. -/
theorem short_time_transpose_orbit_representatives_local_sq_integrable
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (F U : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hF : Measurable F) (hU : Measurable U) (hD : ∀ j, Measurable (D j))
    (heF : ∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
      (complexTransposeGradientOrbit Q Pdag f s) j) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
      Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
      ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hfi := short_time_joint_sq_integrable
    ((((hPdag.continuous_apply hP f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact (μ := volume) (K := Icc (0 : ℝ) 1)
        isCompact_Icc) hF heF
  have hui := short_time_joint_sq_integrable
    ((((hPdag.continuous_apply hP g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact (μ := volume) (K := Icc (0 : ℝ) 1)
        isCompact_Icc) hU heU
  obtain ⟨G, hG, _⟩ := hPdag.existsUnique_continuous_gradient_orbit hP hfg
  have hdi (j : Fin d) : Integrable (fun p => ‖D j p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) := by
    apply short_time_joint_sq_integrable
      (u := fun s => (complexTransposeGradientOrbit Q Pdag f s) j) _ (hD j) (heD j)
    let C : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) →L[ℂ]
        Lp ℂ 2 (reducedLaw Q) := PiLp.proj 2 _ j
    have hj : Continuous (fun s : ℝ => (G s.toNNReal) j) :=
      C.continuous.comp (hG.2.comp continuous_real_toNNReal)
    have hi := (hj.norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (0 : ℝ) 1) isCompact_Icc
    change Integrable (fun s : ℝ => ‖(G s.toNNReal) j‖ ^ 2)
      (volume.restrict (Icc (0 : ℝ) 1)) at hi
    rw [← restrict_Ioc_eq_restrict_Icc] at hi ⊢
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [complexTransposeGradientOrbit_eq hs.1 (hG.1 s.toNNReal)]
  have hfLoc := ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hfi.ofReal
  have huLoc := ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hui.ofReal
  have hdLoc := ae_all_iff.mpr (fun j =>
    ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
      (reducedLaw_stationary Q) (hdi j).ofReal)
  filter_upwards [hfLoc, huLoc, hdLoc] with ω hfω huω hdω
  intro K hK
  refine ⟨(Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hfω K hK).swap,
    (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (huω K hK).swap, ?_⟩
  intro j
  exact (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hdω j K hK).swap

/-- Time zero extension preserves the local spacetime square-integrability
needed by the retained conservative equation. -/
private theorem transpose_zero_extension_memLp {d : ℕ} (K : Set (Vec d))
    (u : ℝ × Vec d → ℂ)
    (hu : MemLp u 2 ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) :
    MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
      (fun s => u (s, p.2)) p.1) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) := by
  let S : Set (ℝ × Vec d) := Prod.fst ⁻¹' Ioc (0 : ℝ) 1
  have hS : MeasurableSet S := measurableSet_Ioc.preimage measurable_fst
  have hm : (((volume.restrict (Icc (-1 : ℝ) 1)).prod
      (volume.restrict K)).restrict S) ≤
      (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K) := by
    rw [Measure.prod_restrict, Measure.restrict_restrict hS, Measure.prod_restrict]
    apply Measure.restrict_mono_set
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2.2⟩
  change MemLp (S.indicator u) 2 _
  exact (memLp_indicator_iff_restrict hS).mpr (hu.mono_measure hm)

/-- A stationary representative and the same chosen physical representative
have an `L²` zero-extended difference. This applies separately to the forcing
and to each coordinate of the retained gradient. -/
theorem short_time_transpose_difference_zero_extension_memLp {d : ℕ}
    (ω : FieldPair d) (K : Set (Vec d))
    (U : ℝ × FieldPair d → ℂ) (Z : ℝ × Vec d → ℂ)
    (hU : Measurable U) (hZ : Measurable Z)
    (hu : Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)))
    (hz : Integrable (fun p => ‖Z p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume)) :
    MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
      (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) := by
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hum := (memLp_two_iff_integrable_sq_norm
    (hU.comp hshift).aestronglyMeasurable).mpr hu
  have hzm := (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).mpr hz
  apply transpose_zero_extension_memLp K (fun p => U (p.1, translate p.2 ω) - Z p)
  exact hum.sub (hzm.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self))

/-- Compact-region spacetime `L²` bounds discharge all three integrability
requirements of the conservative transpose `C¹` identity. -/
theorem short_time_transpose_C1_test_integrable {d : ℕ}
    {K U : Set (Vec d)} (hK : IsCompact K) (hUK : U ⊆ K)
    (A : Vec d → Mat d) (hA : Continuous A) (i : Fin d) (ζ : ℂ)
    (X Y : ℝ × Vec d → ℂ) (J : ℝ → Vec d → Fin d → ℂ)
    (hX : MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hY : MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hJ : ∀ j, MemLp (fun p : ℝ × Vec d => J p.1 p.2 j) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (φ : ℝ × Vec d → ℝ) (hφ : Continuous φ)
    (hdt : Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1))
    (hdx : ∀ j, Continuous (fun p : ℝ × Vec d =>
      gradient (fun x => φ (p.1, x)) p.2 j)) (L : ℂ →L[ℝ] ℝ) :
    Integrable (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1 * L (X p))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) ∧
    Integrable (fun p : ℝ × Vec d => φ p * L (Y p))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) ∧
    Integrable (fun p : ℝ × Vec d =>
      dot (fun j => L ((1 / 2 : ℂ) * ∑ k, (A p.2 j k : ℂ) * J p.1 p.2 k -
        ζ * (A p.2 j i : ℂ) * X p)) (gradient (fun x => φ (p.1, x)) p.2))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) := by
  let μ := (volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hm : (volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U) ≤ μ :=
    Measure.prod_mono le_rfl (Measure.restrict_mono_set volume hUK)
  have hmul {u v : ℝ × Vec d → ℂ} (hu : Continuous u) (hv : Integrable v μ) :
      Integrable (fun p => u p * v p) μ := by
    dsimp only [μ] at hv ⊢
    rw [Measure.prod_restrict] at hv ⊢
    exact IntegrableOn.continuousOn_mul hu.continuousOn hv (isCompact_Icc.prod hK)
  have hmulR {u v : ℝ × Vec d → ℝ} (hu : Continuous u) (hv : Integrable v μ) :
      Integrable (fun p => u p * v p) μ := by
    dsimp only [μ] at hv ⊢
    rw [Measure.prod_restrict] at hv ⊢
    exact IntegrableOn.continuousOn_mul hu.continuousOn hv (isCompact_Icc.prod hK)
  have hX1 : Integrable X μ := hX.integrable (by norm_num)
  have ha (j k : Fin d) : Continuous (fun p : ℝ × Vec d => (A p.2 j k : ℂ)) :=
    Complex.continuous_ofReal.comp ((hA.matrix_elem j k).comp continuous_snd)
  have hf (j : Fin d) : Integrable (fun p : ℝ × Vec d =>
      L ((1 / 2 : ℂ) * ∑ k, (A p.2 j k : ℂ) * J p.1 p.2 k -
        ζ * (A p.2 j i : ℂ) * X p)) μ := by
    have hd := ((integrable_finsetSum Finset.univ fun k _ =>
      hmul (ha j k) ((hJ k).integrable (by norm_num))).const_mul (1 / 2 : ℂ)).sub
      ((hmul (ha j i) hX1).const_mul ζ)
    simpa only [Pi.sub_apply, mul_assoc] using L.integrable_comp hd
  refine ⟨(hmulR hdt (L.integrable_comp hX1)).mono_measure hm,
    (hmulR hφ (L.integrable_comp (hY.integrable (by norm_num)))).mono_measure hm, ?_⟩
  have hfull : Integrable (fun p : ℝ × Vec d =>
      dot (fun j => L ((1 / 2 : ℂ) * ∑ k, (A p.2 j k : ℂ) * J p.1 p.2 k -
        ζ * (A p.2 j i : ℂ) * X p)) (gradient (fun x => φ (p.1, x)) p.2)) μ := by
    change Integrable (fun p : ℝ × Vec d =>
      ∑ j, L ((1 / 2 : ℂ) * ∑ k, (A p.2 j k : ℂ) * J p.1 p.2 k -
        ζ * (A p.2 j i : ℂ) * X p) * gradient (fun x => φ (p.1, x)) p.2 j) μ
    exact integrable_finsetSum Finset.univ fun j _ => by
      simpa only [mul_comm] using hmulR (hdx j) (hf j)
  exact hfull.mono_measure hm

/-- The same coherent forcing and gradient acquire compact spacetime `L²`
bounds after zero extension. The prescribed physical gradient `H` is retained. -/
theorem short_time_transpose_coherent_forcing_gradient_memLp {d : ℕ}
    (ω : FieldPair d) (U : ℝ × FieldPair d → ℂ)
    (D : Fin d → ℝ × FieldPair d → ℂ)
    (hU : Measurable U) (hD : ∀ j, Measurable (D j))
    (hu : ∀ K : Set (Vec d), IsCompact K →
      Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)))
    (hd : ∀ (K : Set (Vec d)), IsCompact K → ∀ j,
      Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)))
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (Z Y : ℝ × Vec d → ℂ) (hZ : Measurable Z)
    (heZ : ∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pdag s.toNNReal g)
    (heY : ∀ p : ℝ × Vec d, Y p = (Ioc (0 : ℝ) 1).indicator
      (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1)
    (H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hHc : ∀ j, Continuous (fun s => H s j))
    (hH : ∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal f) (H s)) :
    ∃ W : Fin d → ℝ × Vec d → ℂ,
      (∀ j, Measurable (W j)) ∧
      (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
      (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
        ((volume.restrict (Icc l r)).prod volume)) ∧
      ∀ K : Set (Vec d), IsCompact K →
        MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
          (fun s => D j (s, translate p.2 ω) - W j (s, p.2)) p.1) 2
          ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) := by
  obtain ⟨W, hW, heW, hw⟩ :=
    short_time_transpose_joint_representative_of_physical_gradient ha hΛ hA hP hfg H hHc hH
  have hz : Integrable (fun p => ‖Z p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
    short_time_joint_sq_integrable
      ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        (μ := volume) (K := Icc (0 : ℝ) 1) isCompact_Icc) hZ heZ
  refine ⟨W, hW, heW, hw, ?_⟩
  intro K hK
  constructor
  · have hy := short_time_transpose_difference_zero_extension_memLp ω K U Z hU hZ (hu K hK) hz
    exact MemLp.ae_eq (ae_of_all _ fun p => (heY p).symm) hy
  · intro j
    exact short_time_transpose_difference_zero_extension_memLp ω K (D j) (W j)
      (hD j) (hW j) (hd K hK j) (hw j 0 1)

/-- Spacetime `L²` bounds give the conservative `C¹` equation without any
additional test-integrability assumptions. -/
theorem short_time_transpose_conservative_C1_weak_equation_of_memLp {d : ℕ}
    (U K : Set (Vec d)) (hU : MeasurableSet U) (hK : IsCompact K)
    (hUK : U ⊆ K) (A : Vec d → Mat d) (hA : Continuous A)
    (i : Fin d) (ζ : ℂ) (X Y : ℝ × Vec d → ℂ)
    (J : ℝ → Vec d → Fin d → ℂ)
    (hX : MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hY : MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hJ : ∀ j, MemLp (fun p : ℝ × Vec d => J p.1 p.2 j) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (htime : ∀ᵐ x ∂volume.restrict U, ∀ L : ℂ →L[ℝ] ℝ,
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
        (∫ s in (-1 : ℝ)..1,
          deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0)
    (hspace : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence U
        (fun x j => L ((∑ k, (A x j k : ℂ) * J s x k) -
          2 * ζ * (A x j i : ℂ) * X (s, x)))
        (fun x => L (2 * Y (s, x))))
    (φ : ℝ × Vec d → ℝ)
    (hφt : ∀ x, ContDiff ℝ 1 (fun s => φ (s, x)))
    (hφl : ∀ x, φ (-1, x) = 0) (hφr : ∀ x, φ (1, x) = 0)
    (hφx : ∀ s, ContDiff ℝ 1 (fun x => φ (s, x)) ∧
      HasCompactSupport (fun x => φ (s, x)) ∧
      tsupport (fun x => φ (s, x)) ⊆ interior U)
    (L : ℂ →L[ℝ] ℝ)
    (hφ : Continuous φ)
    (hdt : Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1))
    (hdx : ∀ j, Continuous (fun p : ℝ × Vec d =>
      gradient (fun x => φ (p.1, x)) p.2 j)) :
    (∫ p : ℝ × Vec d,
      deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
        dot (fun j => L ((1 / 2 : ℂ) * ∑ k, (A p.2 j k : ℂ) * J p.1 p.2 k -
          ζ * (A p.2 j i : ℂ) * X p)) (gradient (fun x => φ (p.1, x)) p.2)
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) = 0 := by
  obtain ⟨hu, hv, hf⟩ := short_time_transpose_C1_test_integrable hK hUK A hA i ζ
    X Y J hX hY hJ φ hφ hdt hdx L
  exact short_time_transpose_conservative_C1_weak_equation U hU A i ζ X Y J
    htime hspace φ hφt hφl hφr hφx L hu hv hf

/-- The conservative transpose residual satisfies the smooth parabolic test
identity; compact spacetime `L²` bounds supply every required integral. -/
theorem short_time_transpose_conservative_parabolic_test {d : ℕ}
    (K U : Set (Vec d)) (hK : IsCompact K) (hU : IsOpen U)
    (hUK : U ⊆ K) (A : Vec d → Mat d) (hA : Continuous A)
    (i : Fin d) (ζ : ℂ) (X Y : ℝ × Vec d → ℂ)
    (J : ℝ → Vec d → Fin d → ℂ)
    (hX : MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hY : MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hJ : ∀ j, MemLp (fun p : ℝ × Vec d => J p.1 p.2 j) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (htime : ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
        (∫ s in (-1 : ℝ)..1,
          deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0)
    (hspace : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence K
        (fun x j => L ((∑ k, (A x j k : ℂ) * J s x k) -
          2 * ζ * (A x j i : ℂ) * X (s, x)))
        (fun x => L (2 * Y (s, x))))
    (ψ : PDE.ParTestFunction U (interior (Icc (-1 : ℝ) 1))) (e : ℂ) :
    (∫ z in U ×ˢ Icc (-1 : ℝ) 1,
      -((e * X (z.2, z.1)).re * PDE.parTimeDeriv ψ.toFun z) +
        (∑ j, (e * ((1 / 2 : ℂ) * ∑ k, (A z.1 j k : ℂ) * J z.2 z.1 k -
          ζ * (A z.1 j i : ℂ) * X (z.2, z.1))).re * PDE.parSpaceGrad ψ.toFun z j)) = 0 := by
  let P : Fin d → ℝ × Vec d → ℂ := fun j p =>
    (1 / 2 : ℂ) * ∑ k, (A p.2 j k : ℂ) * J p.1 p.2 k -
      ζ * (A p.2 j i : ℂ) * X p
  let φ : ℝ × Vec d → ℝ := fun p => ψ.toFun (p.2, p.1)
  have ht (s : ℝ) (x : Vec d) :
      deriv (fun t => φ (t, x)) s = PDE.parTimeDeriv ψ.toFun (x, s) := by
    exact (((ψ.contDiff.differentiable (by norm_num)) (x, s)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s x).prodMk (hasDerivAt_id s))).deriv
  have hx (s : ℝ) (x : Vec d) (j : Fin d) :
      gradient (fun y => φ (s, y)) x j = PDE.parSpaceGrad ψ.toFun (x, s) j := by
    have hd := ((ψ.contDiff.differentiable (by norm_num)) (x, s)).hasFDerivAt
    have he := hd.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const s x))
    change HasFDerivAt (fun y => ψ.toFun (y, s)) _ x at he
    change fderiv ℝ (fun y => ψ.toFun (y, s)) x (unitVector j) = _
    rw [he.fderiv]
    rfl
  have hφc : Continuous φ := ψ.contDiff.continuous.comp continuous_swap
  have hdt : Continuous (fun p : ℝ × Vec d => deriv (fun s => φ (s, p.2)) p.1) := by
    simp_rw [ht]
    exact ((ψ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      continuous_swap
  have hdx (j : Fin d) : Continuous (fun p : ℝ × Vec d =>
      gradient (fun x => φ (p.1, x)) p.2 j) := by
    simp_rw [hx]
    exact ((ψ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      continuous_swap
  have hφt (x : Vec d) : ContDiff ℝ 1 (fun s => φ (s, x)) :=
    ψ.contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hend (s : ℝ) (hs : s ∉ interior (Icc (-1 : ℝ) 1)) (x : Vec d) : φ (s, x) = 0 := by
    change ψ.toFun (x, s) = 0
    exact image_eq_zero_of_notMem_tsupport (fun hz => hs (ψ.tsupport_subset hz).2)
  have hφx (s : ℝ) : ContDiff ℝ 1 (fun x => φ (s, x)) ∧
      HasCompactSupport (fun x => φ (s, x)) ∧
      tsupport (fun x => φ (s, x)) ⊆ interior K := by
    refine ⟨ψ.contDiff.comp (contDiff_id.prodMk contDiff_const), ?_, ?_⟩
    · apply ψ.hasCompactSupport.comp_isClosedEmbedding
      refine ⟨isEmbedding_prodMkLeft s, ?_⟩
      convert isClosed_eq (continuous_snd : Continuous (Prod.snd : Vec d × ℝ → ℝ))
        (continuous_const : Continuous (fun _ : Vec d × ℝ => s)) using 1
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        rfl
      · intro hz
        exact ⟨z.1, Prod.ext rfl hz.symm⟩
    · intro x hx'
      exact (hU.subset_interior_iff.mpr hUK) ((ψ.tsupport_subset
        (tsupport_comp_subset_preimage ψ.toFun (continuous_id.prodMk continuous_const) hx')).1)
  let L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ e)
  have hw := short_time_transpose_conservative_C1_weak_equation_of_memLp
    K K hK.measurableSet hK subset_rfl A hA i ζ X Y J hX hY hJ htime hspace
    φ hφt (hend (-1) (by simp)) (hend 1 (by simp)) hφx L hφc hdt hdx
  change (∫ p : ℝ × Vec d,
    deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
      dot (fun j => L (P j p)) (gradient (fun x => φ (p.1, x)) p.2)
    ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) = 0 at hw
  let f : Vec d × ℝ → ℝ := fun z =>
    -((e * X (z.2, z.1)).re * PDE.parTimeDeriv ψ.toFun z) +
      (∑ j, (e * P j (z.2, z.1)).re * PDE.parSpaceGrad ψ.toFun z j)
  have hform : (fun p : ℝ × Vec d =>
      deriv (fun s => φ (s, p.2)) p.1 * L (X p) -
        dot (fun j => L (P j p)) (gradient (fun x => φ (p.1, x)) p.2)) = fun p => -f p.swap := by
    funext p
    simp only [ht, dot, hx]
    dsimp [f, L, φ, Prod.swap]
    ring
  rw [hform, integral_neg, integral_prod_swap] at hw
  have hzK : (∫ z in K ×ˢ Icc (-1 : ℝ) 1, f z) = 0 := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    linarith
  have hoff (z : Vec d × ℝ) (hz : z.1 ∉ U) : f z = 0 := by
    have hs : z ∉ tsupport ψ.toFun := fun hz' => hz (ψ.tsupport_subset hz').1
    have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hs
    simp [f, PDE.parTimeDeriv, PDE.parSpaceGrad, hd]
  have heq : (∫ z in K ×ˢ Icc (-1 : ℝ) 1, f z) =
      ∫ z in U ×ˢ Icc (-1 : ℝ) 1, f z := by
    calc
      _ = ∫ z in K ×ˢ Icc (-1 : ℝ) 1, (U ×ˢ Icc (-1 : ℝ) 1).indicator f z := by
        apply setIntegral_congr_fun (hK.measurableSet.prod measurableSet_Icc)
        intro z hz
        by_cases ha : z.1 ∈ U
        · simp [ha, hz.2]
        · simp [ha, hoff z ha]
      _ = ∫ z in (K ×ˢ Icc (-1 : ℝ) 1) ∩ (U ×ˢ Icc (-1 : ℝ) 1), f z :=
        setIntegral_indicator (hU.measurableSet.prod measurableSet_Icc)
      _ = _ := by rw [inter_eq_right.mpr (prod_mono hUK subset_rfl)]
  exact heq ▸ hzK


private theorem transpose_time_weak_derivative
    {v g : ℝ → ℝ}
    (hv : ContinuousOn v (Icc (-1 : ℝ) 1))
    (hg : MemLp g 2 (volume.restrict (Icc (-1 : ℝ) 1)))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
      (∫ t in (-1 : ℝ)..1, deriv ψ t * v t + ψ t * g t) = 0) :
    PDE.HasWeakDerivOnIoo (-1) 1 v g := by
  unfold PDE.HasWeakDerivOnIoo
  intro φ hφ hφc hφs
  let ψ : ℝ → ℝ := PDE.scalarPullbackOne φ
  have hψ : ContDiff ℝ 1 ψ := PDE.ContDiff.scalarPullbackOne (hφ.of_le (by simp))
  have hs : tsupport ψ ⊆ Ioo (-1 : ℝ) 1 :=
    PDE.tsupport_scalarPullbackOne_subset_Ioo hφs
  have hψa : ψ (-1) = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; have := (hs h).1; linarith)
  have hψb : ψ 1 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; have := (hs h).2; linarith)
  have hi₁ : IntegrableOn (fun t => deriv ψ t * v t) (Icc (-1 : ℝ) 1) :=
    ((hψ.continuous_deriv (by norm_num)).continuousOn.mul hv).integrableOn_Icc
  have hi₂ : IntegrableOn (fun t => ψ t * g t) (Icc (-1 : ℝ) 1) :=
    IntegrableOn.continuousOn_mul hψ.continuous.continuousOn
      (hg.integrable (by norm_num) : IntegrableOn g (Icc (-1 : ℝ) 1) volume) isCompact_Icc
  have he := hweak ψ hψ hψa hψb
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc, integral_add hi₁ hi₂] at he
  rw [PDE.setIntegral_oneDimensionalAxisBox_eq_scalarPullbackOne,
    PDE.setIntegral_oneDimensionalAxisBox_eq_scalarPullbackOne]
  have hleft :
      (fun t => PDE.scalarPullbackOne
        (fun x => PDE.liftOneDimensional v x *
          (fderiv ℝ φ x) (PDE.basisVec (0 : Fin 1))) t) =
      (fun t => v t * deriv ψ t) := by
    funext t
    simp only [PDE.scalarPullbackOne, PDE.liftOneDimensional,
      PDE.vecOneCoordinate_scalarToVecOne]
    rw [← PDE.deriv_scalarPullbackOne_eq_native_directional (hφ.of_le (by simp))]
  have hright :
      (fun t => PDE.scalarPullbackOne
        (fun x => PDE.liftOneDimensional g x * φ x) t) =
      (fun t => g t * ψ t) := by
    funext t
    simp only [PDE.scalarPullbackOne, PDE.liftOneDimensional,
      PDE.vecOneCoordinate_scalarToVecOne, ψ]
  change (∫ t in Ioo (-1 : ℝ) 1,
      PDE.scalarPullbackOne (fun x => PDE.liftOneDimensional v x *
        (fderiv ℝ φ x) (PDE.basisVec (0 : Fin 1))) t) =
    -(∫ t in Ioo (-1 : ℝ) 1,
      PDE.scalarPullbackOne (fun x => PDE.liftOneDimensional g x * φ x) t)
  rw [hleft, hright, Measure.restrict_congr_set Ioo_ae_eq_Icc]
  simpa only [mul_comm] using (eq_neg_iff_add_eq_zero.mpr he)

/-- A complex residual with the actual weak time identity and zero initial
trace is the literal primitive of its already chosen time derivative. -/
private theorem transpose_zero_extended_primitive_identity
    {v g : ℝ → ℂ}
    (hv : MemLp v 2 (volume.restrict (Icc (-1 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Icc (-1 : ℝ) 1)))
    (hv0 : v 0 = 0)
    (hweak : ∀ L : ℂ →L[ℝ] ℝ,
      AbsolutelyContinuousOnInterval (fun s => L (v s)) (-1) 1 ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
        (∫ t in (-1 : ℝ)..1, deriv ψ t * L (v t) + ψ t * L (g t)) = 0) :
    ∀ t ∈ Icc (-1 : ℝ) 1, v t = ∫ s in (0 : ℝ)..t, g s := by
  intro t ht
  have he (L : ℂ →L[ℝ] ℝ) : L (v t) = L (∫ s in (0 : ℝ)..t, g s) := by
    have hLv : MemLp (fun s => L (v s)) 2 (volume.restrict (Icc (-1 : ℝ) 1)) :=
      L.comp_memLp' hv
    have hLg : MemLp (fun s => L (g s)) 2 (volume.restrict (Icc (-1 : ℝ) 1)) :=
      L.comp_memLp' hg
    have hcv : ContinuousOn (fun s => L (v s)) (Icc (-1 : ℝ) 1) := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using (hweak L).1.continuousOn
    have hw := transpose_time_weak_derivative hcv hLg (hweak L).2
    have hi := PDE.ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
      (by norm_num : (-1 : ℝ) < 1) hcv
      (hLv.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl))
      hLg hw (s := 0) (by norm_num) ht
    have hgi : IntervalIntegrable g volume 0 t :=
      MeasureTheory.IntegrableOn.intervalIntegrable (MeasureTheory.IntegrableOn.mono_set
        (hg.integrable (by norm_num) : IntegrableOn g (Icc (-1 : ℝ) 1) volume)
        (uIcc_subset_Icc (by norm_num) ht))
    rw [hv0, map_zero, sub_zero, L.intervalIntegral_comp_comm hgi] at hi
    exact hi
  apply Complex.ext
  · exact he Complex.reCLM
  · exact he Complex.imCLM


/-- The already chosen zero-extended residual is strongly continuous locally
in spatial `L²` at every time in `[-1,1]`, including zero and both endpoints.
Its spacetime derivative and weak time identity determine the same slices. -/
theorem short_time_transpose_zero_extended_local_strong_continuous
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [SFinite μ]
    {X Y : ℝ × S → ℂ} (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod μ))
    (hY2 : MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod μ))
    (hX0 : ∀ t : ℝ, t ≤ 0 → ∀ x, X (t, x) = 0)
    (hweak : ∀ᵐ x ∂μ, ∀ L : ℂ →L[ℝ] ℝ,
      AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
        (∫ t in (-1 : ℝ)..1,
          deriv ψ t * L (X (t, x)) + ψ t * L (Y (t, x))) = 0) :
    (∀ t ∈ Icc (-1 : ℝ) 1, MemLp (fun x => X (t, x)) 2 μ) ∧
    ∀ a ∈ Icc (-1 : ℝ) 1,
      Tendsto (fun t => ∫ x, ‖X (t, x) - X (a, x)‖ ^ 2 ∂μ)
        (𝓝[Icc (-1 : ℝ) 1] a) (𝓝 0) := by
  have hXI := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX2
  have hYI := (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mp hY2
  have hprim : ∀ᵐ x ∂μ, ∀ t ∈ Icc (-1 : ℝ) 1,
      X (t, x) = ∫ s in (0 : ℝ)..t, Y (s, x) := by
    filter_upwards [hXI.prod_left_ae, hYI.prod_left_ae, hweak] with x hx hy hw
    apply transpose_zero_extended_primitive_identity
      ((memLp_two_iff_integrable_sq_norm
        (hX.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx)
      ((memLp_two_iff_integrable_sq_norm
        (hY.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hy)
      (hX0 0 le_rfl x) hw
  have hYpos : Integrable (fun p => ‖Y p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod μ) :=
    hYI.mono_measure (Measure.prod_mono
      (Measure.restrict_mono (Icc_subset_Icc (by norm_num) le_rfl) le_rfl) le_rfl)
  obtain ⟨hmem, hcont⟩ := short_time_local_primitive_continuous μ hY hYpos
  have hclamp (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      max 0 t ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le (by norm_num) ht.2⟩
  have he (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      (fun x => X (t, x)) =ᵐ[μ]
        (fun x => ∫ s in Icc (0 : ℝ) (max 0 t), Y (s, x)) := by
    filter_upwards [hprim] with x hx
    by_cases ht0 : 0 ≤ t
    · rw [max_eq_right ht0, hx t ht, intervalIntegral.integral_of_le ht0,
        integral_Icc_eq_integral_Ioc]
    · rw [hX0 t (le_of_not_ge ht0) x, max_eq_left (le_of_not_ge ht0)]
      simp
  refine ⟨fun t ht => (hmem _ (hclamp t ht)).ae_eq (he t ht).symm, ?_⟩
  intro a ha
  have hm : MapsTo (fun t : ℝ => max 0 t) (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) :=
    fun t ht => hclamp t ht
  have hc : Tendsto (fun t : ℝ => max 0 t)
      (𝓝[Icc (-1 : ℝ) 1] a) (𝓝[Icc (0 : ℝ) 1] (max 0 a)) :=
    (continuous_const.max continuous_id).continuousWithinAt.tendsto_nhdsWithin hm
  have htend := (hcont _ (hclamp a ha)).comp hc
  apply htend.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  apply integral_congr_ae
  filter_upwards [he t ht, he a ha] with x hx ha'
  rw [hx, ha']


/-- Replacing the supplied physical gradient by its joint representative on
an open plateau preserves both spatial equations of the same residual. The
compact restriction is taken only after that replacement. -/
theorem short_time_transpose_joint_residual_spatial_equations {d : ℕ}
    (O K : Set (Vec d)) (hO : IsOpen O) (hKO : K ⊆ O)
    (A : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (F V X Y : ℝ × Vec d → ℂ) (D W : Fin d → ℝ × Vec d → ℂ)
    (v : ℝ → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (heV : ∀ s, (fun x => V (s, x)) =ᵐ[volume] v s)
    (heW : ∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j)
    (hH : ∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (v s) (H s))
    (hX0 : ∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0)
    (hY0 : ∀ s : ℝ, s ≤ 0 → ∀ x, Y (s, x) = 0)
    (heX : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (fun x => X (s, x)) =ᵐ[volume.restrict K]
        (fun x => F (s, x) - V (s, x)))
    (hgrad : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakGradient univ (fun x => L (F (s, x)))
        (fun x j => L (D j (s, x))))
    (hdiv : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence O
        (fun x j => L ((∑ k, (A x j k : ℂ) * (D k (s, x) - H s k x)) -
          2 * ζ * (A x j i : ℂ) * (F (s, x) - V (s, x))))
        (fun x => L (2 * Y (s, x)))) :
    let J := fun s x j => (Ioc (0 : ℝ) 1).indicator
      (fun t => D j (t, x) - W j (t, x)) s
    (∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
      HasWeakGradient K (fun x => (X (s, x)).re) (fun x j => (J s x j).re) ∧
      HasWeakGradient K (fun x => (X (s, x)).im) (fun x j => (J s x j).im)) ∧
    ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence K
        (fun x j => L ((∑ k, (A x j k : ℂ) * J s x k) -
          2 * ζ * (A x j i : ℂ) * X (s, x)))
        (fun x => L (2 * Y (s, x))) := by
  intro J
  have hphys (s : ℝ) :
      HasWeakGradient univ (fun x => (V (s, x)).re) (fun x j => (W j (s, x)).re) ∧
      HasWeakGradient univ (fun x => (V (s, x)).im) (fun x j => (W j (s, x)).im) := by
    have he : ∀ᵐ x ∂volume.restrict (univ : Set (Vec d)),
        V (s, x) = v s x ∧ ∀ j, W j (s, x) = H s j x := by
      rw [Measure.restrict_univ]
      filter_upwards [heV s, ae_all_iff.mpr (fun j => heW j s)] with x hx hw
      exact ⟨hx, hw⟩
    constructor
    · apply Correctors.hasWeakGradient_congr_ae isOpen_univ (hH s).1
      · exact he.mono fun x hx => congrArg Complex.re hx.1.symm
      · exact he.mono fun x hx => funext fun j => congrArg Complex.re (hx.2 j).symm
    · apply Correctors.hasWeakGradient_congr_ae isOpen_univ (hH s).2
      · exact he.mono fun x hx => congrArg Complex.im hx.1.symm
      · exact he.mono fun x hx => funext fun j => congrArg Complex.im (hx.2 j).symm
  have hg (L : ℂ →L[ℝ] ℝ)
      (hv : ∀ s, HasWeakGradient univ (fun x => L (V (s, x)))
        (fun x j => L (W j (s, x)))) :
      ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
        HasWeakGradient K (fun x => L (X (s, x)))
          (fun x j => L (J s x j)) := by
    have hz := short_time_zero_extension_spatial_gradient K
      (fun p => L (X p)) (fun p => L (F p - V p))
      (fun s x j => L (D j (s, x) - W j (s, x)))
      (fun s hs x => by rw [hX0 s hs x, map_zero])
      (fun s hs hs1 => (heX s hs hs1).symm.mono fun x hx => congrArg L hx) ?_
    · simpa only [J, Set.indicator, apply_ite L, map_zero] using hz
    · filter_upwards [hgrad] with s hs
      intro j
      simpa only [map_sub] using HasWeakPartialDerivative.restrict_subset
        (subset_univ K) MeasurableSet.univ
        (Correctors.hasWeakPartialDerivative_sub (hs L j) (hv s j))
  refine ⟨?_, ?_⟩
  · filter_upwards [hg Complex.reCLM (fun s => (hphys s).1),
      hg Complex.imCLM (fun s => (hphys s).2)] with s hr hi
    exact ⟨hr, hi⟩
  apply short_time_transpose_zero_extension_spatial_divergence A i ζ K X Y
    (fun p => F p - V p) (fun s x j => D j (s, x) - W j (s, x))
    hX0 hY0 (fun s hs hs1 => (heX s hs hs1).symm)
  filter_upwards [hdiv] with s hs
  intro L
  have he : ∀ᵐ x ∂volume.restrict O, ∀ j, W j (s, x) = H s j x :=
    ae_restrict_of_ae (ae_all_iff.mpr (fun j => heW j s))
  have hd : HasWeakDivergence O
      (fun x j => L ((∑ k, (A x j k : ℂ) * (D k (s, x) - W k (s, x))) -
        2 * ζ * (A x j i : ℂ) * (F (s, x) - V (s, x))))
      (fun x => L (2 * Y (s, x))) := by
    apply Correctors.hasWeakDivergence_congr_ae hO (hs L)
    · exact he.mono fun x hx => by simp only [hx]
    · exact Filter.EventuallyEq.rfl
  exact HasWeakDivergence.restrict_subset hKO hO.measurableSet hd

private theorem transpose_residual_memLp_space_time {d : ℕ} {K : Set (Vec d)}
    {X : ℝ × Vec d → ℂ}
    (hX : MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K))) :
    MemLp (fun p : Vec d × ℝ => X (p.2, p.1)) 2
      (volume.restrict (K ×ˢ Icc (-1 : ℝ) 1)) := by
  have hs := hX.comp_measurePreserving
    (Measure.measurePreserving_swap
      (μ := volume.restrict K) (ν := volume.restrict (Icc (-1 : ℝ) 1)))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact hs

private theorem transpose_residual_weak_gradient_pde {d : ℕ} {K : Set (Vec d)}
    {v : Vec d → ℝ} {J : Vec d → Vec d} (h : HasWeakGradient K v J) :
    PDE.HasWeakGradientOn K v J := by
  intro j φ hφ hφc hφK
  simpa only [coordinateDerivative, unitVector, PDE.basisVec] using
    (h j).2.2 φ ⟨hφ, hφc, hφK⟩

/-- The same conservative residual, with its actual time equation and local
`L²` bounds, has a literal exponential parabolic lift. Symmetry converts the
row flux in its spatial equation to the transpose lift's column flux. -/
theorem short_time_transpose_residual_parabolic_lift {d : ℕ}
    (K U : Set (Vec d)) (hK : IsCompact K) (hU : IsOpen U) (hUK : U ⊆ K)
    (V : Set (PDE.Vec 2)) (hV : IsOpen V) (hVfinite : volume V < ⊤)
    (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (A : Vec d → Mat d) (hA : Continuous A) (hAsym : ∀ x j k, A x j k = A x k j)
    (i : Fin d) (ζ : ℂ) (X Y : ℝ × Vec d → ℂ)
    (J : ℝ → Vec d → Fin d → ℂ) (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hY2 : MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hJ2 : ∀ j, MemLp (fun p : ℝ × Vec d => J p.1 p.2 j) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
    (hX0 : ∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0)
    (htime : ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
      AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
        (∫ s in (-1 : ℝ)..1,
          deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0)
    (hgrad : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
      HasWeakGradient K (fun x => (X (s, x)).re) (fun x j => (J s x j).re) ∧
      HasWeakGradient K (fun x => (X (s, x)).im) (fun x j => (J s x j).im))
    (hspace : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence K
        (fun x j => L ((∑ k, (A x j k : ℂ) * J s x k) -
          2 * ζ * (A x j i : ℂ) * X (s, x)))
        (fun x => L (2 * Y (s, x)))) :
    ∃ w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V))
        (Icc (-1 : ℝ) 1),
      (∀ z, w.toFun z = (Complex.exp
        ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).re) ∧
      (∀ z j, w.grad z (Fin.castAdd 2 j) = (Complex.exp
        ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          J z.2 (PDE.vecAppendEquiv d 2 z.1).1 j).re) ∧
      (∀ z, w.grad z (Fin.natAdd d (0 : Fin 2)) = w.toFun z) ∧
      (∀ z, w.grad z (Fin.natAdd d (1 : Fin 2)) = -(Complex.exp
        ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          X (z.2, (PDE.vecAppendEquiv d 2 z.1).1)).im) ∧
      ∀ M : ℝ, PDE.IsParabolicWeakSolution
        (fun z => shortTimeTransposeLiftMatrix (A (PDE.vecAppendEquiv d 2 z.1).1) i ζ M)
        (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) (Icc (-1 : ℝ) 1) w := by
  obtain ⟨hslice, hcont⟩ := short_time_transpose_zero_extended_local_strong_continuous
    (volume.restrict K) hX hY hX2 hY2 hX0 htime
  have hm : (volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U) ≤
      (volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono_set volume hUK)
  have hweak : ∀ᵐ t ∂volume.restrict (Icc (-1 : ℝ) 1),
      PDE.HasWeakGradientOn U (fun x => (X (t, x)).re) (fun x j => (J t x j).re) ∧
      PDE.HasWeakGradientOn U (fun x => (X (t, x)).im) (fun x j => (J t x j).im) := by
    have hg : ∀ᵐ t ∂volume.restrict (Icc (-1 : ℝ) 1),
        HasWeakGradient K (fun x => (X (t, x)).re) (fun x j => (J t x j).re) ∧
        HasWeakGradient K (fun x => (X (t, x)).im) (fun x j => (J t x j).im) := by
      rwa [restrict_Ioo_eq_restrict_Icc] at hgrad
    filter_upwards [hg] with t ht
    exact ⟨(transpose_residual_weak_gradient_pde ht.1).restrict hU hUK,
      (transpose_residual_weak_gradient_pde ht.2).restrict hU hUK⟩
  obtain ⟨w, hw, hD, h0, h1⟩ := short_time_complex_lift_ParH1
    hU hV measurableSet_Icc hVfinite r hr
    (fun p => X (p.2, p.1)) (fun j p => J p.2 p.1 j)
    (transpose_residual_memLp_space_time (hX2.mono_measure hm))
    (fun j => transpose_residual_memLp_space_time ((hJ2 j).mono_measure hm)) hweak
    (fun t ht L _ hLU => (hslice t ht).mono_measure
      (Measure.restrict_mono_set volume (hLU.trans hUK))) (by
      intro t ht L _ hLU
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hcont t ht)
      · exact Eventually.of_forall fun s => integral_nonneg (fun x => sq_nonneg _)
      · filter_upwards [eventually_mem_nhdsWithin] with s hs
        exact setIntegral_mono_set (((hslice s hs).sub (hslice t ht)).norm.integrable_sq)
          (ae_of_all _ (fun x => sq_nonneg _)) (Eventually.of_forall (hLU.trans hUK)))
  refine ⟨w, hw, hD, h0, h1, ?_⟩
  intro M
  let μ := (volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hu : Integrable X μ := hX2.integrable (by norm_num)
  have hmul {f g : ℝ × Vec d → ℂ} (hf : Continuous f) (hg : Integrable g μ) :
      Integrable (fun p => f p * g p) μ := by
    dsimp only [μ] at hg ⊢
    rw [Measure.prod_restrict] at hg ⊢
    exact IntegrableOn.continuousOn_mul hf.continuousOn hg (isCompact_Icc.prod hK)
  have ha (j k : Fin d) : Continuous (fun p : ℝ × Vec d => (A p.2 j k : ℂ)) :=
    Complex.continuous_ofReal.comp ((hA.matrix_elem j k).comp continuous_snd)
  have hp (j : Fin d) : Integrable (fun p : ℝ × Vec d =>
      (1 / 2 : ℂ) * ∑ k, (A p.2 k j : ℂ) * J p.1 p.2 k -
        ζ * (A p.2 j i : ℂ) * X p) μ := by
    apply Integrable.congr
      (((integrable_finsetSum Finset.univ fun k _ =>
        hmul (ha k j) ((hJ2 k).integrable (by norm_num))).const_mul (1 / 2 : ℂ)).sub
          ((hmul (ha j i) hu).const_mul ζ))
    exact ae_of_all _ fun p => by simp only [Pi.sub_apply, mul_assoc]
  have hswap {f : ℝ × Vec d → ℂ} (hf : Integrable f μ) :
      IntegrableOn (fun z : Vec d × ℝ => f (z.2, z.1))
        (U ×ˢ Icc (-1 : ℝ) 1) := by
    change Integrable (fun z : Vec d × ℝ => f (z.2, z.1))
      (volume.restrict (U ×ˢ Icc (-1 : ℝ) 1))
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.measurePreserving_swap
      (μ := volume.restrict U) (ν := volume.restrict (Icc (-1 : ℝ) 1))).integrable_comp_of_integrable
        (hf.mono_measure hm)
  apply short_time_transpose_lift_isParabolicWeakSolution hU.measurableSet hV.measurableSet
    measurableSet_Icc hVfinite r hr A i (fun p => X (p.2, p.1))
    (fun j p => J p.2 p.1 j) ζ M (hswap hu) (fun j => hswap (hp j)) ?_ w hw hD h0 h1
  intro ψ e
  have ht : ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
      ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → φ (-1) = 0 → φ 1 = 0 →
        (∫ s in (-1 : ℝ)..1,
          deriv φ s * L (X (s, x)) + φ s * L (Y (s, x))) = 0 :=
    htime.mono fun x hx L => (hx L).2
  have he := short_time_transpose_conservative_parabolic_test
    K U hK hU hUK A hA i ζ X Y J hX2 hY2 hJ2 ht hspace ψ e
  convert he using 1
  congr 1
  funext z
  congr 2
  funext j
  rw [show (∑ k, (A z.1 j k : ℂ) * J z.2 z.1 k) =
      ∑ k, (A z.1 k j : ℂ) * J z.2 z.1 k from
    Finset.sum_congr rfl (fun k _ => by rw [hAsym z.1 j k])]

/-- The normalized maximum of the actual conservative residual is controlled
by the Gaussian energy of its matching uncut residual. -/
theorem short_time_transpose_residual_normalized_gaussian_max {d : ℕ}
    (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
    ∀ (K : Set (Vec d)) (_ : IsCompact K)
      (_ : PDE.euclideanBall (0 : PDE.Vec d) 1 ⊆ K)
      (A : EinsteinRelation.CoefficientField d) (_ : Continuous A)
      (_ : ∀ x, S5Elliptic (A x) Λ) (i : Fin d) (ζ : ℂ) (_ : ‖ζ‖ ≤ B)
      (X Y Z : ℝ × Vec d → ℂ) (J : ℝ → Vec d → Fin d → ℂ)
      (_ : Measurable X) (_ : Measurable Y) (_ : Measurable Z)
      (_ : MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
      (_ : MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
      (_ : ∀ j, MemLp (fun p : ℝ × Vec d => J p.1 p.2 j) 2
        ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)))
      (_ : ∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0)
      (_ : ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
        AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
        ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
          (∫ s in (-1 : ℝ)..1,
            deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0)
      (_ : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
        HasWeakGradient K (fun x => (X (s, x)).re) (fun x j => (J s x j).re) ∧
        HasWeakGradient K (fun x => (X (s, x)).im) (fun x j => (J s x j).im))
      (_ : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
        HasWeakDivergence K
          (fun x j => L ((∑ k, (A x j k : ℂ) * J s x k) -
            2 * ζ * (A x j i : ℂ) * X (s, x)))
          (fun x => L (2 * Y (s, x))))
      (_ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        (fun x => X (s, x)) =ᵐ[volume.restrict K] (fun x => Z (s, x)))
      (q : ℝ) (_ : 0 < q) (_ : q ≤ 1) (T : ℝ)
      (_ : -1 ≤ T - 4 * Λ * q ^ 2) (_ : T ≤ 1) (L : ℝ) (_ : 0 < L),
      let v : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
        (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
          q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
            X (T + 4 * Λ * q ^ 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re
      MemLp v 2 (volume.restrict
        (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1 ×ˢ Ioc (-1 : ℝ) 0)) ∧
      essSup (fun z => ENNReal.ofReal |v z|)
        (volume.restrict (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
        ENNReal.ofReal C₀ *
          (ENNReal.ofReal (C₁ * Real.exp (2 * q ^ 2 / L) / q ^ (d + 2)) *
            ∫⁻ z in Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec d)),
              ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) * ‖Z z‖ ^ 2)) ^ (2 : ℝ)⁻¹ := by
  obtain ⟨C₀, hC₀, hmax⟩ := short_time_transpose_normalized_lift_local_max Λ B hΛ hB
  obtain ⟨C₁, hC₁, henergy⟩ := short_time_normalized_lift_local_residual_gaussian_energy d
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro K hK hball A hA hEll i ζ hζ X Y Z J hX hY hZ hX2 hY2 hJ2 hX0 htime hgrad hspace hmatch q hq hq1 T hT₀ hT₁ L hL
  have hVfinite : volume (PDE.euclideanBall (0 : PDE.Vec 2) 1) < ⊤ :=
    lt_top_iff_ne_top.mpr (PDE.volume_euclideanBall_ne_top _ (by norm_num))
  have hr : ∀ y ∈ PDE.euclideanBall (0 : PDE.Vec 2) 1, y 0 ≤ 1 := by
    intro y hy
    have hy' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1)).1 hy
    have hc := PDE.abs_apply_le_vecEuclideanNorm y (0 : Fin 2)
    simp only [sub_zero] at hy'
    exact (le_abs_self _).trans (hc.trans hy'.le)
  obtain ⟨w, hw, _, _, _, hweak⟩ := short_time_transpose_residual_parabolic_lift
    K (PDE.euclideanBall (0 : PDE.Vec d) 1) hK (PDE.isOpen_euclideanBall _ _) hball
    (PDE.euclideanBall (0 : PDE.Vec 2) 1) (PDE.isOpen_euclideanBall _ _) hVfinite 1 hr
    A hA (fun x j k => (hEll x).symm j k) i ζ X Y J hX hY hX2 hY2 hJ2 hX0 htime hgrad hspace
  obtain ⟨hv, hm⟩ := hmax A hEll i ζ hζ X w hw hweak q hq hq1 T hT₀ hT₁
  refine ⟨hv, ?_⟩
  have hslab : MemLp X 2 (volume.restrict
      (Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hX2
    exact hX2.mono_measure (Measure.restrict_mono_set _
      (prod_mono (Icc_subset_Icc hT₀ hT₁)
        ((PDE.euclideanBall_mono hq.le hq1).trans hball)))
  have hlocal : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (fun x => X (s, x)) =ᵐ[volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) q)]
        (fun x => Z (s, x)) := by
    intro s hs hs1
    exact ae_restrict_of_ae_restrict_of_subset
      ((PDE.euclideanBall_mono hq.le hq1).trans hball) (hmatch s hs hs1)
  have he := henergy Λ q T L hΛ hq hq1 hT₁ hL 1 (by simp) X Z hX hZ hX0 hlocal hslab
  simp only [mul_one] at he
  exact hm.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow he (by positivity)))

/-- Two non-collinear phases of the real exponential lift control the full
complex value. This is the scalar step in recovering both residual components. -/
private theorem short_time_transpose_complex_norm_le_of_two_phases (z : ℂ) {θ L : ℝ}
    (hθ : 0 < Real.sin θ) (h₀ : |z.re| ≤ L)
    (h₁ : |(Complex.exp ⟨0, θ⟩ * z).re| ≤ L) :
    ‖z‖ ≤ (1 + 2 / Real.sin θ) * L := by
  have he : Real.sin θ * z.im =
      Real.cos θ * z.re - (Complex.exp ⟨0, θ⟩ * z).re := by
    simp only [Complex.mul_re, Complex.exp_re, Complex.exp_im,
      Real.exp_zero, one_mul]
    ring
  have hi : Real.sin θ * |z.im| ≤ 2 * L := by
    calc
      Real.sin θ * |z.im| = |Real.sin θ * z.im| := by
        rw [abs_mul, abs_of_pos hθ]
      _ = |Real.cos θ * z.re - (Complex.exp ⟨0, θ⟩ * z).re| := congrArg abs he
      _ ≤ |Real.cos θ * z.re| + |(Complex.exp ⟨0, θ⟩ * z).re| := abs_sub _ _
      _ ≤ |z.re| + L := add_le_add (by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ)) h₁
      _ ≤ 2 * L := by linarith only [h₀]
  have him : |z.im| ≤ 2 * L / Real.sin θ :=
    (le_div_iff₀ hθ).2 (by simpa only [mul_comm] using hi)
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ L + 2 * L / Real.sin θ := add_le_add h₀ him
    _ = (1 + 2 / Real.sin θ) * L := by ring

/-- The auxiliary exponential is continuous, so its almost-everywhere bound
controls both non-collinear phases at every auxiliary point. -/
private theorem short_time_transpose_complex_norm_le_of_auxiliary_ae_bound
    (z : ℂ) {q r L : ℝ} (hr : 0 < r)
    (hθ : 0 < Real.sin (q * (r / 2)))
    (h : ∀ᵐ y ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec 2) r),
      |(Complex.exp ⟨q * y 0, q * y 1⟩ * z).re| ≤ L) :
    ‖z‖ ≤ (1 + 2 / Real.sin (q * (r / 2))) * L := by
  have hc : Continuous (fun y : PDE.Vec 2 =>
      |(Complex.exp ⟨q * y 0, q * y 1⟩ * z).re|) := by
    simpa only [Complex.mul_re, Complex.exp_re, Complex.exp_im] using
      (show Continuous (fun y : PDE.Vec 2 =>
        |Real.exp (q * y 0) * Real.cos (q * y 1) * z.re -
          Real.exp (q * y 0) * Real.sin (q * y 1) * z.im|) by fun_prop)
  have hp := PDE.Parabolic.Moser.continuousOn_le_of_ae_restrict_le
    (PDE.isOpen_euclideanBall (0 : PDE.Vec 2) r) hc.continuousOn h
  have hzero : (0 : PDE.Vec 2) ∈ PDE.euclideanBall (0 : PDE.Vec 2) r := by
    change PDE.vecNormSq ((0 : PDE.Vec 2) - 0) < r ^ 2
    simpa only [sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero] using sq_pos_of_pos hr
  have hphase : (![0, r / 2] : PDE.Vec 2) ∈
      PDE.euclideanBall (0 : PDE.Vec 2) r := by
    change PDE.vecNormSq ((![0, r / 2] : PDE.Vec 2) - 0) < r ^ 2
    simp only [sub_zero, PDE.vecNormSq, PDE.vecDot, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add]
    nlinarith only [sq_pos_of_pos hr]
  apply short_time_transpose_complex_norm_le_of_two_phases z hθ
  · have hzero' := hp 0 hzero
    simpa only [Pi.zero_apply, mul_zero, Complex.mul_re, Complex.exp_re,
      Complex.exp_im, Real.exp_zero, Real.cos_zero, Real.sin_zero,
      one_mul, zero_mul, sub_zero] using hzero'
  · simpa using hp (![0, r / 2] : PDE.Vec 2) hphase

/-- Splitting off the two lift coordinates commutes with retaining the time
coordinate, including all restricted product measures. -/
private theorem short_time_transpose_lift_spacetime_measurePreserving {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {I : Set ℝ}
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    MeasurePreserving
      (fun z : PDE.Vec (d + 2) × ℝ =>
        (((PDE.vecAppendEquiv d 2 z.1).1, z.2),
          (PDE.vecAppendEquiv d 2 z.1).2))
      (volume.restrict ((PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ×ˢ I))
      ((volume.restrict (U ×ˢ I)).prod (volume.restrict V)) := by
  let μ := (volume : Measure (PDE.Vec d)).restrict U
  let ν := (volume : Measure (PDE.Vec 2)).restrict V
  let τ := (volume : Measure ℝ).restrict I
  have hs := (PDE.measurePreserving_vecAppendEquiv_restrict d 2 hU hV).prod
    (MeasurePreserving.id τ)
  have ha := measurePreserving_prodAssoc μ ν τ
  have hb := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := τ))
  have hc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ τ ν)
  have h := hc.comp (hb.comp (ha.comp hs))
  simpa [μ, ν, τ, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Function.comp_def, MeasurableEquiv.prodAssoc] using h

/-- An almost-everywhere bound for the real lift controls both components of
its physical residual on the half-radius physical cylinder. -/
private theorem short_time_transpose_complex_bound_of_lift_ae {d : ℕ}
    {Z : PDE.Vec d × ℝ → ℂ} (hZ : Measurable Z)
    {R q L : ℝ} (hR : 0 < R)
    (hθ : 0 < Real.sin (q * ((R / 2) / 2))) {I : Set ℝ}
    (h : ∀ᵐ z ∂volume.restrict
        (PDE.euclideanBall (0 : PDE.Vec (d + 2)) R ×ˢ I),
      |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
          q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          Z ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re| ≤ L) :
    ∀ᵐ z ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (R / 2) ×ˢ I),
      ‖Z z‖ ≤ (1 + 2 / Real.sin (q * ((R / 2) / 2))) * L := by
  let U := PDE.euclideanBall (0 : PDE.Vec d) (R / 2)
  let V := PDE.euclideanBall (0 : PDE.Vec 2) (R / 2)
  have hs := short_time_transpose_lift_spacetime_measurePreserving (U := U) (V := V) (I := I)
    (PDE.isOpen_euclideanBall _ _).measurableSet
    (PDE.isOpen_euclideanBall _ _).measurableSet
  have hsmall := h.filter_mono (ae_mono (Measure.restrict_mono_set _
    (prod_mono (PDE.preimage_vecAppendEquiv_prod_halfBall_subset_euclideanBall d 2 hR)
      Subset.rfl)))
  have hm : Measurable (fun z : (PDE.Vec d × ℝ) × PDE.Vec 2 =>
      |(Complex.exp ⟨q * z.2 0, q * z.2 1⟩ * Z z.1).re|) := by
    simpa only [Complex.mul_re, Complex.exp_re, Complex.exp_im] using
      (show Measurable (fun z : (PDE.Vec d × ℝ) × PDE.Vec 2 =>
        |Real.exp (q * z.2 0) * Real.cos (q * z.2 1) * (Z z.1).re -
          Real.exp (q * z.2 0) * Real.sin (q * z.2 1) * (Z z.1).im|) by fun_prop)
  have hp : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)).prod (volume.restrict V),
      |(Complex.exp ⟨q * z.2 0, q * z.2 1⟩ * Z z.1).re| ≤ L := by
    rw [← hs.map_eq]
    exact (ae_map_iff hs.measurable.aemeasurable
      (measurableSet_le hm measurable_const)).2 hsmall
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with z hz
  exact short_time_transpose_complex_norm_le_of_auxiliary_ae_bound (Z z) (half_pos hR) hθ hz

/-- The Moser essential maximum bounds the full complex residual on the
physical cylinder, with the exact two-phase factor. -/
theorem short_time_transpose_complex_bound_of_lift_essSup {d : ℕ}
    {Z : PDE.Vec d × ℝ → ℂ} (hZ : Measurable Z)
    {R q L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hθ : 0 < Real.sin (q * ((R / 2) / 2))) {I : Set ℝ}
    (h : essSup (fun z : PDE.Vec (d + 2) × ℝ =>
        ENNReal.ofReal |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
          q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          Z ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re|)
        (volume.restrict (PDE.euclideanBall (0 : PDE.Vec (d + 2)) R ×ˢ I)) ≤
        ENNReal.ofReal L) :
    ∀ᵐ z ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (R / 2) ×ˢ I),
      ‖Z z‖ ≤ (1 + 2 / Real.sin (q * ((R / 2) / 2))) * L := by
  apply short_time_transpose_complex_bound_of_lift_ae hZ hR hθ
  filter_upwards [ENNReal.ae_le_essSup (fun z : PDE.Vec (d + 2) × ℝ =>
    ENNReal.ofReal |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
      q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
      Z ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re|)] with z hz
  exact (ENNReal.ofReal_le_ofReal_iff hL).1 (hz.trans h)


/-- Quantitative two-phase recovery with an explicit scale-dependent factor. -/
theorem short_time_transpose_complex_bound_of_lift_essSup_quantitative {d : ℕ}
    {Z : PDE.Vec d × ℝ → ℂ} (hZ : Measurable Z)
    {R q L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hq : 0 < q) (hphase : q * R ≤ 2 * Real.pi) {I : Set ℝ}
    (h : essSup (fun z : PDE.Vec (d + 2) × ℝ =>
        ENNReal.ofReal |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
          q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          Z ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re|)
        (volume.restrict (PDE.euclideanBall (0 : PDE.Vec (d + 2)) R ×ˢ I)) ≤
        ENNReal.ofReal L) :
    ∀ᵐ z ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (R / 2) ×ˢ I),
      ‖Z z‖ ≤ (1 + 4 * Real.pi / (q * R)) * L := by
  have hqr : 0 < q * R := mul_pos hq hR
  have ht : 0 < q * ((R / 2) / 2) := by positivity
  have htupper : q * ((R / 2) / 2) ≤ Real.pi / 2 := by linarith
  have hsin := Real.mul_le_sin ht.le htupper
  have hsinpos : 0 < Real.sin (q * ((R / 2) / 2)) :=
    lt_of_lt_of_le (mul_pos (div_pos (by norm_num) Real.pi_pos) ht) hsin
  have hfactor : 2 / Real.sin (q * ((R / 2) / 2)) ≤ 4 * Real.pi / (q * R) := by
    apply (div_le_div_iff₀ hsinpos hqr).2
    have hh := mul_le_mul_of_nonneg_left hsin (show 0 ≤ 4 * Real.pi by positivity)
    have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp at hh
    have heq : q * R / 2 ^ (2 : ℕ) = q * (R / 2 / 2) := by ring
    rw [heq] at hh
    nlinarith only [hh]
  filter_upwards [short_time_transpose_complex_bound_of_lift_essSup hZ hR hL hsinpos h] with z hz
  exact hz.trans (mul_le_mul_of_nonneg_right (add_le_add_right hfactor 1) hL)


end EinsteinFull.Blueprint
