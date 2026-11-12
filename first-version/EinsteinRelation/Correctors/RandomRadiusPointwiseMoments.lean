import EinsteinRelation.Correctors.AKMRandomRadiusTail
import EinsteinRelation.Correctors.RandomRadiusCutoffMoments
import EinsteinRelation.Correctors.PoweredBadRadiusMoments

/-! The good-radius and bad-radius moment assembly in
`paper/main.tex:852–861`, without an independence assumption. -/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM

/-- An energy estimate on the good event and higher moments on the bad
event give the same sharp polynomial rate; `paper/main.tex:852–861`.
This internal lemma works for any normed observable, including a Euclidean
gradient difference. -/
theorem randomRadius_pointwise_moment_le
    {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
    (P : Measure Ω) {X E G : Ω → ℝ} {F : Ω → V}
    {m R a C A M N : ℝ} (hm : 1 ≤ m) (hR : 0 < R) (ha : 0 < a)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hX : ∀ ω, 0 ≤ X ω) (hE : ∀ᵐ ω ∂P, 0 ≤ E ω)
    (hG : ∀ᵐ ω ∂P, 0 ≤ G ω) (hF : AEStronglyMeasurable F P)
    (hXLp : MemLp (fun ω => (X ω)^a) (ENNReal.ofReal (2*m)) P)
    (hELp : MemLp E (ENNReal.ofReal (2*m)) P)
    (hGLp : MemLp G (ENNReal.ofReal (2*m)) P)
    (hXA : eLpNorm (fun ω => (X ω)^a) (ENNReal.ofReal (2*m)) P ≤ ENNReal.ofReal A)
    (hEM : eLpNorm E (ENNReal.ofReal (2*m)) P ≤ ENNReal.ofReal (M*R^(-a)))
    (hGN : eLpNorm G (ENNReal.ofReal (2*m)) P ≤ ENNReal.ofReal N)
    (hgood : ∀ᵐ ω ∂P, X ω ≤ R → ‖F ω‖ ≤ C*(X ω)^a*E ω)
    (hbad : ∀ᵐ ω ∂P, R < X ω → ‖F ω‖ ≤ G ω) :
    MemLp F (ENNReal.ofReal m) P ∧
      eLpNorm F (ENNReal.ofReal m) P ≤ ENNReal.ofReal (A*(C*M+N)*R^(-a)) := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  haveI := holderTriple_double_ofReal hm0
  let U := fun ω => (X ω)^a * E ω
  let W := fun ω => (X ω)^a * G ω
  have hU : MemLp U (ENNReal.ofReal m) P := hELp.mul' hXLp
  have hW : MemLp W (ENNReal.ofReal m) P := hGLp.mul' hXLp
  let Y := fun ω => C*U ω + R^(-a)*W ω
  have hY : MemLp Y (ENNReal.ofReal m) P := (hU.const_mul C).add (hW.const_mul (R^(-a)))
  have hdom : ∀ᵐ ω ∂P, ‖F ω‖ ≤ ‖Y ω‖ := by
    filter_upwards [hE, hG, hgood, hbad] with ω he hg hgo hba
    have hx : 0 ≤ (X ω)^a := Real.rpow_nonneg (hX ω) _
    have hr : 0 ≤ R^(-a) := Real.rpow_nonneg hR.le _
    have hy : 0 ≤ Y ω := add_nonneg (mul_nonneg hC (mul_nonneg hx he))
      (mul_nonneg hr (mul_nonneg hx hg))
    rw [Real.norm_of_nonneg hy]
    by_cases hω : X ω ≤ R
    · exact (hgo hω).trans (by dsimp only [Y,U,W]; nlinarith only [mul_nonneg hr (mul_nonneg hx hg)])
    · have hω' : R < X ω := lt_of_not_ge hω
      have hpow := Real.rpow_le_rpow hR.le hω'.le ha.le
      have hunit : 1 ≤ R^(-a)*(X ω)^a := by
        rw [Real.rpow_neg hR.le]
        calc
          1 = (R^a)⁻¹ * R^a := (inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hR a))).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr (Real.rpow_nonneg hR.le a))
      exact (hba hω').trans (by
        dsimp only [Y,U,W]
        nlinarith only [mul_le_mul_of_nonneg_right hunit hg, mul_nonneg hC (mul_nonneg hx he)])
  have hUn : eLpNorm U (ENNReal.ofReal m) P ≤ ENNReal.ofReal (A*(M*R^(-a))) := by
    refine (eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ) (E := ℝ)
      (p := ENNReal.ofReal (2*m)) (q := ENNReal.ofReal (2*m))
      (f := E) (φ := fun ω => (X ω)^a) hELp.1 hXLp.1).trans ?_
    exact (mul_le_mul' hXA hEM).trans_eq (ENNReal.ofReal_mul hA).symm
  have hWn : eLpNorm W (ENNReal.ofReal m) P ≤ ENNReal.ofReal (A*N) := by
    refine (eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ) (E := ℝ)
      (p := ENNReal.ofReal (2*m)) (q := ENNReal.ofReal (2*m))
      (f := G) (φ := fun ω => (X ω)^a) hGLp.1 hXLp.1).trans ?_
    exact (mul_le_mul' hXA hGN).trans_eq (ENNReal.ofReal_mul hA).symm
  have hp : 1 ≤ ENNReal.ofReal m := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hm
  refine ⟨hY.of_le hF hdom, (eLpNorm_mono_ae hdom).trans ?_⟩
  calc
    eLpNorm Y (ENNReal.ofReal m) P ≤
        eLpNorm (fun ω => C*U ω) (ENNReal.ofReal m) P +
          eLpNorm (fun ω => R^(-a)*W ω) (ENNReal.ofReal m) P :=
      eLpNorm_add_le (hU.1.const_mul C) (hW.1.const_mul (R^(-a))) hp
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (A*(M*R^(-a))) +
        ENNReal.ofReal (R^(-a)) * ENNReal.ofReal (A*N) := by
      have hcu := eLpNorm_const_smul_le (μ := P) (p := ENNReal.ofReal m) (c := C) (f := U)
      have hrw := eLpNorm_const_smul_le (μ := P) (p := ENNReal.ofReal m) (c := R^(-a)) (f := W)
      rw [Real.enorm_of_nonneg hC] at hcu
      rw [Real.enorm_of_nonneg (Real.rpow_nonneg hR.le _)] at hrw
      exact add_le_add (hcu.trans (mul_le_mul_right hUn _))
        (hrw.trans (mul_le_mul_right hWn _))
    _ = _ := by
      rw [← ENNReal.ofReal_mul hC,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end EinsteinRelation.Correctors

/-! # From paired energy to pointwise moments

Source: `paper/main.tex:853–862`. The good event uses a deterministic
large-scale gradient estimate. The bad event uses higher gradient moments
and moments of the same random radius. No independence is used.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- The good/bad radius split used for the paired point gradient. The
three higher moments are on one and the same probability space.
Source: `paper/main.tex:853–862`. -/
theorem eLpNorm_pointwise_of_good_bad_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Z A : Ω → ℝ} (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    {m R a C : ℝ} (hm : 1 ≤ m) (hR : 0 < R) (ha : 0 < a) (hC : 0 ≤ C)
    (hXLp : MemLp (fun ω => (X ω)^a) (ENNReal.ofReal (2*m)) P)
    (hZLp : MemLp Z (ENNReal.ofReal (2*m)) P)
    (hALp : MemLp A (ENNReal.ofReal (2*m)) P)
    (hgood : ∀ᵐ ω ∂P, X ω ≤ R → ‖Z ω‖ ≤ C * (X ω)^a * ‖A ω‖) :
    MemLp Z (ENNReal.ofReal m) P ∧
      eLpNorm Z (ENNReal.ofReal m) P ≤
        ENNReal.ofReal C * (eLpNorm (fun ω => (X ω)^a) (ENNReal.ofReal (2*m)) P *
          eLpNorm A (ENNReal.ofReal (2*m)) P) +
        ENNReal.ofReal (R^(-a)) *
          (eLpNorm (fun ω => (X ω)^a) (ENNReal.ofReal (2*m)) P *
            eLpNorm Z (ENNReal.ofReal (2*m)) P) := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  haveI := holderTriple_double_ofReal hm0
  have hp : 1 ≤ ENNReal.ofReal m := ENNReal.one_le_ofReal.mpr hm
  let S := {ω | X ω ≤ R}
  have hS : MeasurableSet S := measurableSet_le hXm measurable_const
  have hprod : MemLp (fun ω => (X ω)^a * A ω) (ENNReal.ofReal m) P := hALp.mul' hXLp
  have hdom : ∀ᵐ ω ∂P, ‖S.indicator Z ω‖ ≤ C * ‖(X ω)^a * A ω‖ := by
    filter_upwards [hgood] with ω hω
    by_cases hmem : ω ∈ S
    · rw [Set.indicator_of_mem hmem, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (hX ω) a)]
      simpa only [mul_assoc] using hω hmem
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      exact mul_nonneg hC (norm_nonneg _)
  have hgoodLp := hprod.of_le_mul (hZLp.1.indicator hS) hdom
  have hgoodNorm : eLpNorm (S.indicator Z) (ENNReal.ofReal m) P ≤
      ENNReal.ofReal C * (eLpNorm (fun ω => (X ω)^a) (ENNReal.ofReal (2*m)) P *
        eLpNorm A (ENNReal.ofReal (2*m)) P) := by
    exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _).trans
      (mul_le_mul_right (eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ) (E := ℝ)
        (p := ENNReal.ofReal (2*m)) (q := ENNReal.ofReal (2*m))
        (r := ENNReal.ofReal m) (f := A) (φ := fun ω => (X ω)^a) hALp.1 hXLp.1) _)
  obtain ⟨hbadLp, hbadNorm⟩ := powered_badRadius_eLpNorm_le hXm hX hm0 hR ha hXLp hZLp
  have hsplit : Z = S.indicator Z + {ω | R < X ω}.indicator Z := by
    funext ω
    by_cases h : X ω ≤ R
    · simp [S, h, not_lt.mpr h]
    · simp [S, h, lt_of_not_ge h]
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hgoodLp.add hbadLp
  · calc
      eLpNorm Z (ENNReal.ofReal m) P =
          eLpNorm (S.indicator Z + {ω | R < X ω}.indicator Z) (ENNReal.ofReal m) P := by
            rw [← hsplit]
      _ ≤ _ := (eLpNorm_add_le hgoodLp.1 hbadLp.1 hp).trans
        (add_le_add hgoodNorm hbadNorm)

/-- Higher paired energy moments with decay `R^(-a)` and bounded higher
pointwise moments imply the same decay at a point. The constant is
independent of `R`. Source: `paper/main.tex:853–862`. -/
theorem eLpNorm_pointwise_decay_of_good_bad_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Z A : Ω → ℝ} (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    {m R a C D B H : ℝ} (hm : 1 ≤ m) (hR : 0 < R) (ha : 0 < a)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hXLp : MemLp (fun ω => (X ω)^a) (ENNReal.ofReal (2*m)) P)
    (hZLp : MemLp Z (ENNReal.ofReal (2*m)) P)
    (hALp : MemLp A (ENNReal.ofReal (2*m)) P)
    (hgood : ∀ᵐ ω ∂P, X ω ≤ R → ‖Z ω‖ ≤ C * (X ω)^a * ‖A ω‖)
    (hXmBound : eLpNorm (fun ω => (X ω)^a) (ENNReal.ofReal (2*m)) P ≤ ENNReal.ofReal D)
    (hZmBound : eLpNorm Z (ENNReal.ofReal (2*m)) P ≤ ENNReal.ofReal B)
    (hAmBound : eLpNorm A (ENNReal.ofReal (2*m)) P ≤ ENNReal.ofReal (H * R^(-a))) :
    MemLp Z (ENNReal.ofReal m) P ∧
      eLpNorm Z (ENNReal.ofReal m) P ≤ ENNReal.ofReal (D * (C * H + B) * R^(-a)) := by
  obtain ⟨hLp, hnorm⟩ := eLpNorm_pointwise_of_good_bad_radius hXm hX hm hR ha hC
    hXLp hZLp hALp hgood
  refine ⟨hLp, hnorm.trans ?_⟩
  calc
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal D * ENNReal.ofReal (H * R^(-a))) +
        ENNReal.ofReal (R^(-a)) * (ENNReal.ofReal D * ENNReal.ofReal B) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul hC,
        ← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The cited stretched-exponential radius bound supplies the higher
radius moment used in the pointwise good/bad split. There is no additional
polynomial-tail hypothesis. Source: `paper/main.tex:853–862`. -/
theorem eLpNorm_pointwise_decay_of_stretchedExponential_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Z A : Ω → ℝ} (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    {m R a C B H s θ : ℝ} (hm : 1 ≤ m) (hR : 0 < R) (ha : 0 < a)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hH : 0 ≤ H) (hs : 0 < s) (hθ : 0 < θ)
    (hradius : External.AKM.StretchedExponentialBound P s θ X)
    (hZLp : MemLp Z (ENNReal.ofReal (2*m)) P)
    (hALp : MemLp A (ENNReal.ofReal (2*m)) P)
    (hgood : ∀ᵐ ω ∂P, X ω ≤ R → ‖Z ω‖ ≤ C * (X ω)^a * ‖A ω‖)
    (hZmBound : eLpNorm Z (ENNReal.ofReal (2*m)) P ≤ ENNReal.ofReal B)
    (hAmBound : eLpNorm A (ENNReal.ofReal (2*m)) P ≤ ENNReal.ofReal (H * R^(-a))) :
    let D := (2 * ((2*m)/(s/a))^((2*m)/(s/a)))^(1/(2*m)) * θ^a
    MemLp Z (ENNReal.ofReal m) P ∧
      eLpNorm Z (ENNReal.ofReal m) P ≤ ENNReal.ofReal (D * (C * H + B) * R^(-a)) := by
  obtain ⟨hXLp, hXmBound⟩ := radius_rpow_moments_of_stretchedExponential P
    hXm hX hs hθ ha (show 0 < 2*m by linarith) hradius
  exact eLpNorm_pointwise_decay_of_good_bad_radius hXm hX hm hR ha hC
    (by positivity) hB hH hXLp hZLp hALp hgood hXmBound hZmBound hAmBound

end EinsteinRelation.Correctors
