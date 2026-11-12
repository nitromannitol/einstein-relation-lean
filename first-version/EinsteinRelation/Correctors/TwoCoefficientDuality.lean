import EinsteinRelation.Correctors.ParabolicDualityTesting

/-! # Forward/backward testing for two coefficients

Source: `paper/main.tex:777–784,842`; the duality argument in the proof of
AKM Proposition E.1, p. 510. When the forward and backward solutions have
different coefficients, the interior fluxes no longer cancel. Their
difference is retained as an explicit integrand.
-/

open MeasureTheory
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The interior terms of forward/backward energy testing split into the
coefficient-difference pairing and the cutoff flux. -/
theorem parabolic_two_coefficient_duality_split {d : ℕ} {K : ℝ}
    (A B : Coefficient d K) (x : Vec d) (u v r c : ℝ) (G H D : Vec d) :
    dot ((A x).mulVec G)
        (fun j => (r*c)^2 * H j + 2*(r*c)*v*(r*D j)) +
      dot (-((B x).mulVec H))
        (fun j => (r*c)^2 * G j + 2*(r*c)*u*(r*D j)) =
      (r*c)^2 * (dot ((A x).mulVec G) H - dot ((B x).mulVec H) G) +
        2*r^2*c * dot (fun j => v*((A x).mulVec G) j-u*((B x).mulVec H) j) D := by
  dsimp only [dot]
  simp_rw [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp
  ring

/-- Compact forward/backward weak testing of a forward solution with
coefficient `A` against a backward solution with coefficient `B`. The
coefficient-difference pairing `(A G)·Z - (B Z)·G` remains.
Source: `paper/main.tex:777–784,842`; AKM Proposition E.1 proof, p. 510. -/
theorem parabolicSolutions_two_coefficient_cutoff_pairing {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A B : Coefficient d K} {a b T R : ℝ}
    (_hab : a < b) (_hR : 0 < R)
    {u v : ℝ × Vec d → ℝ} {G H : ℝ × Vec d → Vec d}
    (hu : IsParabolicSolution A (Set.Ioo a b) (originBall d R) u G)
    (hv : IsParabolicSolution B (Set.Ioo (T-b) (T-a)) (originBall d R) v H)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Set.Ioo a b)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d R) χ) :
    Integrable (fun z : ℝ × Vec d =>
      u z * v (T-z.1,z.2) * deriv η z.1 * χ z.2^2)
        (volume.restrict (Set.Ioo a b ×ˢ originBall d R)) ∧
    Integrable (fun z : ℝ × Vec d => η z.1 * χ z.2 *
      dot (fun j => v (T-z.1,z.2) * ((A z.2).mulVec (G z)) j -
        u z * ((B z.2).mulVec (H (T-z.1,z.2))) j) (gradient χ z.2))
        (volume.restrict (Set.Ioo a b ×ˢ originBall d R)) ∧
    Integrable (fun z : ℝ × Vec d => η z.1 * χ z.2^2 *
      (dot ((A z.2).mulVec (G z)) (H (T-z.1,z.2)) -
        dot ((B z.2).mulVec (H (T-z.1,z.2))) (G z)))
        (volume.restrict (Set.Ioo a b ×ˢ originBall d R)) ∧
    (∫ z in Set.Ioo a b ×ˢ originBall d R,
      u z * v (T-z.1,z.2) * deriv η z.1 * χ z.2^2) =
      2 * (∫ z in Set.Ioo a b ×ˢ originBall d R, η z.1 * χ z.2 *
        dot (fun j => v (T-z.1,z.2) * ((A z.2).mulVec (G z)) j -
          u z * ((B z.2).mulVec (H (T-z.1,z.2))) j) (gradient χ z.2)) +
      ∫ z in Set.Ioo a b ×ˢ originBall d R, η z.1 * χ z.2^2 *
        (dot ((A z.2).mulVec (G z)) (H (T-z.1,z.2)) -
          dot ((B z.2).mulVec (H (T-z.1,z.2))) (G z)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ originBall d R)
  let w : ℝ × Vec d → ℝ := fun z => v (T-z.1,z.2)
  let Z : ℝ × Vec d → Vec d := fun z => H (T-z.1,z.2)
  let D : ℝ × Vec d → ℝ := fun z =>
    dot (fun j => w z * ((A z.2).mulVec (G z)) j - u z * ((B z.2).mulVec (Z z)) j)
      (gradient χ z.2)
  let E : ℝ × Vec d → ℝ := fun z =>
    dot ((A z.2).mulVec (G z)) (Z z) - dot ((B z.2).mulVec (Z z)) (G z)
  let L : (ℝ → ℝ) → ℝ × Vec d → ℝ := fun ρ z =>
    u z * w z * (2*ρ z.1*deriv ρ z.1) * χ z.2^2
  let Bf : (ℝ → ℝ) → ℝ × Vec d → ℝ := fun ρ z => ρ z.1^2 * χ z.2 * D z
  let Ef : (ℝ → ℝ) → ℝ × Vec d → ℝ := fun ρ z => ρ z.1^2 * χ z.2^2 * E z
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).norm
  have hU : IsOpen (originBall d R) := isOpen_lt hnorm continuous_const
  have huf := parabolicFluxSolution_of_parabolicSolution hK hu
  have hvf := parabolicFluxSolution_of_backward_parabolicSolution hK hv
  have hEi : Integrable E μ := by
    have h1 : Integrable (fun z => dot ((A z.2).mulVec (G z)) (Z z)) μ := by
      simpa only [dot] using integrable_finset_sum Finset.univ fun j _ =>
        (huf.flux_memLp j).integrable_mul (hvf.gradient_memLp j)
    have h2 : Integrable (fun z => dot (-((B z.2).mulVec (Z z))) (G z)) μ := by
      simpa only [dot] using integrable_finset_sum Finset.univ fun j _ =>
        (hvf.flux_memLp j).integrable_mul (huf.gradient_memLp j)
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [E, dot, Pi.add_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    ring
  have hsquare {ρ : ℝ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
      (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ Set.Ioo a b) :
      Integrable (L ρ) μ ∧ Integrable (Bf ρ) μ ∧ Integrable (Ef ρ) μ ∧
        (∫ z, L ρ z ∂μ) = 2 * (∫ z, Bf ρ z ∂μ) + ∫ z, Ef ρ z ∂μ := by
    let ζ : ℝ × Vec d → ℝ := fun z => ρ z.1 * χ z.2
    have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ :=
      (hρ.comp contDiff_fst).mul (hχ.1.comp contDiff_snd)
    have hζsupport : tsupport ζ ⊆ tsupport ρ ×ˢ tsupport χ := by
      apply closure_minimal ?_ ((isClosed_tsupport ρ).prod (isClosed_tsupport χ))
      intro z hz
      exact ⟨subset_tsupport ρ (fun he => hz (by simp only [ζ, he, zero_mul])),
        subset_tsupport χ (fun he => hz (by simp only [ζ, he, mul_zero]))⟩
    have hζc : HasCompactSupport ζ :=
      (hρc.prod hχ.2.1).of_isClosed_subset (isClosed_tsupport _) hζsupport
    have hζs : tsupport ζ ⊆ interior (Set.Ioo a b) ×ˢ originBall d R := by
      rw [interior_Ioo]
      exact hζsupport.trans (Set.prod_mono hρs hχ.2.2)
    have hDt (z : ℝ × Vec d) : fderiv ℝ ζ z (1,0) = deriv ρ z.1 * χ z.2 := by
      simpa only [mul_one, map_zero, mul_zero, add_zero] using
        parabolic_tensor_cutoff_derivative hρ hχ.1 z (1,0)
    have hDx (z : ℝ × Vec d) (j : Fin d) :
        fderiv ℝ ζ z (0,unitVector j) = ρ z.1 * gradient χ z.2 j := by
      simpa only [mul_zero, zero_mul, zero_add, gradient, coordinateDerivative] using
        parabolic_tensor_cutoff_derivative hρ hχ.1 z (0,unitVector j)
    have hE := huf.bilinear_energy_identity measurableSet_Ioo hU hvf hζ hζc hζs
    have hx (z : ℝ × Vec d) :
        dot ((A z.2).mulVec (G z))
          (fun j => ζ z^2 * Z z j + 2*ζ z*w z*fderiv ℝ ζ z (0,unitVector j)) +
        dot (-((B z.2).mulVec (Z z)))
          (fun j => ζ z^2 * G z j + 2*ζ z*u z*fderiv ℝ ζ z (0,unitVector j)) =
        Ef ρ z + 2 * Bf ρ z := by
      simp_rw [hDx]
      convert parabolic_two_coefficient_duality_split A B z.2 (u z) (w z)
        (ρ z.1) (χ z.2) (G z) (Z z) (gradient χ z.2) using 1
      dsimp [ζ, Bf, Ef, D, E]
      ring
    have hζm : MemLp ζ ⊤ μ := hζ.continuous.memLp_top_of_hasCompactSupport hζc _
    have hEf : Integrable (Ef ρ) μ := by
      obtain ⟨M, hM⟩ := hζc.exists_bound_of_continuous hζ.continuous
      have hi := hEi.bdd_mul (c := M^2)
        (((hζ.continuous.pow 2).aestronglyMeasurable))
        (Filter.Eventually.of_forall fun z => by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hM z) 2)
      refine hi.congr (Filter.Eventually.of_forall fun z => ?_)
      dsimp [Ef, ζ]
      ring
    have hBi : Integrable (Bf ρ) μ := by
      have hi : Integrable (fun z => 2 * Bf ρ z) μ := by
        refine (hE.1.sub hEf).congr (Filter.Eventually.of_forall fun z => ?_)
        have hz := hx z
        simp only [Pi.sub_apply] at hz ⊢
        linarith only [hz]
      convert hi.const_mul (1/2 : ℝ) using 1
      ext z
      dsimp
      ring
    have hDtm : MemLp (fun z => fderiv ℝ ζ z (1,0)) ⊤ μ :=
      ((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous
        |>.memLp_top_of_hasCompactSupport (hζc.fderiv_apply ℝ (1,0)) _
    have huζ : MemLp (fun z => u z * ζ z) 2 μ := hζm.mul' huf.scalar_memLp
    have hwD : MemLp (fun z => w z * fderiv ℝ ζ z (1,0)) 2 μ :=
      hDtm.mul' hvf.scalar_memLp
    have ht (z : ℝ × Vec d) :
        (u z * ζ z) * (w z * fderiv ℝ ζ z (1,0)) = L ρ z / 2 := by
      rw [hDt]
      dsimp [ζ, L]
      ring
    have hLi : Integrable (L ρ) μ := by
      convert ((huζ.integrable_mul hwD).const_mul 2) using 1
      ext z
      change L ρ z = 2 * ((u z * ζ z) * (w z * fderiv ℝ ζ z (1,0)))
      rw [ht]
      ring
    refine ⟨hLi, hBi, hEf, ?_⟩
    have heq := (integral_congr_ae (Filter.Eventually.of_forall hx)).symm.trans hE.2
    change (∫ z, (Ef ρ z + 2 * Bf ρ z) ∂μ) =
      2 * ∫ z, u z * w z * ζ z * fderiv ℝ ζ z (1,0) ∂μ at heq
    rw [integral_add hEf (hBi.const_mul 2), integral_const_mul] at heq
    have heqT (z : ℝ × Vec d) :
        u z * w z * ζ z * fderiv ℝ ζ z (1,0) = L ρ z / 2 := by
      rw [← ht]
      ring
    simp_rw [heqT] at heq
    rw [integral_div] at heq
    linarith only [heq]
  obtain ⟨ρ, σ, hρ, hρc, hρs, hσ, hσc, hσs, heq⟩ :=
    compact_time_test_difference_squares hη hηc hηs
  obtain ⟨hLρ, hBρ, hEρ, hρeq⟩ := hsquare hρ hρc hρs
  obtain ⟨hLσ, hBσ, hEσ, hσeq⟩ := hsquare hσ hσc hσs
  have hL (z : ℝ × Vec d) :
      u z * w z * deriv η z.1 * χ z.2^2 = L ρ z - L σ z := by
    rw [(heq z.1).2]
    dsimp [L]
    ring
  have hB (z : ℝ × Vec d) : η z.1 * χ z.2 * D z = Bf ρ z - Bf σ z := by
    rw [(heq z.1).1]
    dsimp [Bf]
    ring
  have hEe (z : ℝ × Vec d) : η z.1 * χ z.2^2 * E z = Ef ρ z - Ef σ z := by
    rw [(heq z.1).1]
    dsimp [Ef]
    ring
  refine ⟨(hLρ.sub hLσ).congr (Filter.Eventually.of_forall fun z => (hL z).symm),
    (hBρ.sub hBσ).congr (Filter.Eventually.of_forall fun z => (hB z).symm),
    (hEρ.sub hEσ).congr (Filter.Eventually.of_forall fun z => (hEe z).symm), ?_⟩
  change (∫ z, u z*w z*deriv η z.1*χ z.2^2 ∂μ) =
    2 * (∫ z, η z.1*χ z.2*D z ∂μ) + ∫ z, η z.1*χ z.2^2*E z ∂μ
  simp_rw [hL, hB, hEe]
  rw [integral_sub hLρ hLσ, integral_sub hBρ hBσ, integral_sub hEρ hEσ, hρeq, hσeq]
  ring

end EinsteinRelation.Correctors
