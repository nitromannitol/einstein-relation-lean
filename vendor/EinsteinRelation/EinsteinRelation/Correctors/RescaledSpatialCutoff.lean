import EinsteinRelation.Correctors.PrescribedBallCutoff

namespace EinsteinRelation.Correctors
open External.AKM

/-- Rescaling a fixed Euclidean cutoff retains its plateau and gradient scale.
Source: `paper/main.tex:818–824`. -/
theorem rescale_reference_spatial_cutoff
    {d : ℕ} {χ : Vec d → ℝ} {D R : ℝ} (hR : 0 < R)
    (hχ : IsSpatialTest (originBall d 2) χ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ1 : ∀ x ∈ originBall d 1, χ x = 1)
    (hD : ∀ x, euclideanSq (gradient χ x) ≤ D^2) :
    IsSpatialTest (originBall d (4*R)) (fun x => χ ((2*R)⁻¹ • x)) ∧
      (∀ x, 0 ≤ χ ((2*R)⁻¹ • x) ∧ χ ((2*R)⁻¹ • x) ≤ 1) ∧
      (∀ x ∈ originBall d (2*R), χ ((2*R)⁻¹ • x) = 1) ∧
      ∀ x, euclideanSq (gradient (fun y => χ ((2*R)⁻¹ • y)) x) ≤ (D/R)^2 := by
  have h2R : 0 < 2*R := by positivity
  have hinv : 0 < (2*R)⁻¹ := inv_pos.mpr h2R
  let S : Vec d ≃ₜ Vec d := Homeomorph.smul (Units.mk0 ((2*R)⁻¹) hinv.ne')
  have hS (x : Vec d) : S x = (2*R)⁻¹ • x := rfl
  have hnorm (x : Vec d) : euclideanNorm ((2*R)⁻¹ • x) = (2*R)⁻¹ * euclideanNorm x :=
    Environment.AKMTestIntegralSupport.euclideanNorm_smul _ hinv.le x
  have htest : IsSpatialTest (originBall d (4*R)) (fun x => χ ((2*R)⁻¹ • x)) := by
    refine ⟨hχ.1.comp (contDiff_id.const_smul _), hχ.2.1.comp_homeomorph S, ?_⟩
    intro x hx
    have heq := tsupport_comp_eq_preimage χ S
    have hmem : (2*R)⁻¹ • x ∈ tsupport χ := (Set.ext_iff.mp heq x).mp hx
    have hsmall : (2*R)⁻¹ * euclideanNorm x < 2 := by
      have hh : euclideanNorm ((2*R)⁻¹ • x) < 2 := hχ.2.2 hmem
      rwa [hnorm] at hh
    change euclideanNorm x < 4*R
    have hmul := (mul_lt_mul_iff_right₀ h2R).mpr hsmall
    have hcancel : (2*R) * ((2*R)⁻¹ * euclideanNorm x) = euclideanNorm x := by
      field_simp
    rw [hcancel] at hmul
    linarith
  refine ⟨htest, fun x => hχb _, ?_, ?_⟩
  · intro x hx
    apply hχ1
    change euclideanNorm ((2*R)⁻¹ • x) < 1
    rw [hnorm]
    have hm := mul_lt_mul_of_pos_left hx hinv
    simpa only [inv_mul_cancel₀ h2R.ne'] using hm
  · intro x
    have hd : HasFDerivAt (fun y => χ ((2*R)⁻¹ • y))
        ((2*R)⁻¹ • fderiv ℝ χ ((2*R)⁻¹ • x)) x := by
      have hh := (hχ.1.differentiable (by simp) ((2*R)⁻¹ • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul ((2*R)⁻¹))
      convert! hh using 1
      ext v
      simp
    have hg : gradient (fun y => χ ((2*R)⁻¹ • y)) x =
        (2*R)⁻¹ • gradient χ ((2*R)⁻¹ • x) := by
      ext j
      change fderiv ℝ (fun y => χ ((2*R)⁻¹ • y)) x (unitVector j) = _
      rw [hd.fderiv]
      rfl
    rw [hg, Environment.AKMTestIntegralSupport.euclideanSq_smul]
    calc
      _ ≤ ((2*R)⁻¹)^2 * D^2 := mul_le_mul_of_nonneg_left (hD _) (sq_nonneg _)
      _ = (D/R)^2 / 4 := by field_simp; ring
      _ ≤ (D/R)^2 := by nlinarith [sq_nonneg (D/R)]

end EinsteinRelation.Correctors
