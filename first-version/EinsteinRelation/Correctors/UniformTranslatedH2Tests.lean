import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Uniform normalized norms of translated smooth tests

Source: `paper/main.tex:948–955`. A fixed compact smooth mollifier and its
first two coordinate derivatives are globally bounded. Their translates
therefore have a common normalized `H²` bound on any fixed finite-volume
domain, without a restriction on the translation.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM

/-- A global scalar bound controls the normalized spatial RMS, also on a
null-volume domain. Source: `paper/main.tex:948–955`. -/
theorem scalarRms_le_of_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (U : Set X) (hU : ν U ≠ ⊤) {C : ℝ} (hC : 0 ≤ C)
    {f : X → ℝ} (hb : ∀ x, |f x| ≤ C) : scalarRms ν U f ≤ C := by
  let μ := ν.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU
  by_cases hzero : μ = 0
  · change Real.sqrt (average μ (fun x => f x ^ 2)) ≤ C
    simpa only [hzero, average_zero_measure, Real.sqrt_zero] using hC
  letI : NeZero μ := ⟨hzero⟩
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hC, ?_⟩
  change (∫ x, f x ^ 2 ∂(μ Set.univ)⁻¹ • μ) ≤ C ^ 2
  calc
    _ ≤ ∫ _ : X, C ^ 2 ∂(μ Set.univ)⁻¹ • μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (integrable_const _) (Filter.Eventually.of_forall ?_)
      intro x
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hC).mpr (hb x)
    _ = C ^ 2 := by simp

/-- Translation preserves the literal coordinate derivative, even at points
where a function is not differentiable. Source: `paper/main.tex:948–955`. -/
theorem coordinateDerivative_comp_sub {d : ℕ} (f : Vec d → ℝ)
    (a : Vec d) (j : Fin d) :
    coordinateDerivative j (fun x => f (x-a)) = fun x => coordinateDerivative j f (x-a) := by
  funext x
  simp only [coordinateDerivative, fderiv_comp_sub]

/-- All translates of one compact smooth test have a common positive
normalized `H²` bound on a fixed finite-volume domain. The constant is
chosen before the translation. Source: `paper/main.tex:948–955`. -/
theorem exists_uniform_h2TestNorm_comp_sub_bound {d : ℕ}
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) (U : Set (Vec d)) (hU : volume U ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Vec d, h2TestNorm U (fun x => ζ (x-a)) ≤ C := by
  have hD {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin d) :
      ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j f) :=
    ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const
  obtain ⟨B₀, hB₀⟩ := hc.exists_bound_of_continuous hζ.continuous
  choose B₁ hB₁ using fun j : Fin d =>
    (hc.fderiv_apply ℝ (unitVector j)).exists_bound_of_continuous
      (hD hζ j).continuous
  choose B₂ hB₂ using fun j k : Fin d =>
    ((hc.fderiv_apply ℝ (unitVector j)).fderiv_apply ℝ (unitVector k)).exists_bound_of_continuous
      (hD (hD hζ j) k).continuous
  have hB₀nonneg : 0 ≤ B₀ := (norm_nonneg (ζ 0)).trans (hB₀ 0)
  have hB₁nonneg (j : Fin d) : 0 ≤ B₁ j := (norm_nonneg _).trans (hB₁ j 0)
  have hB₂nonneg (j k : Fin d) : 0 ≤ B₂ j k := (norm_nonneg _).trans (hB₂ j k 0)
  let M : ℝ := (volume U).toReal ^ (-(2 : ℝ) / d) * B₀ +
    (volume U).toReal ^ (-(1 : ℝ) / d) * ∑ j, B₁ j +
      ∑ j, ∑ k ∈ Finset.univ.filter (j ≤ ·), B₂ j k
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro a
  apply le_trans (b := M)
  · simp only [h2TestNorm, coordinateDerivative_comp_sub, M]
    apply add_le_add
    · apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (ENNReal.toReal_nonneg) _)
        exact scalarRms_le_of_abs_le volume U hU hB₀nonneg (fun x => hB₀ (x-a))
      · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (ENNReal.toReal_nonneg) _)
        apply Finset.sum_le_sum
        intro j _
        exact scalarRms_le_of_abs_le volume U hU (hB₁nonneg j) (fun x => hB₁ j (x-a))
    · apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact scalarRms_le_of_abs_le volume U hU (hB₂nonneg j k) (fun x => hB₂ j k (x-a))
  · exact (le_abs_self M).trans (le_add_of_nonneg_right zero_le_one)

/-- Translates by at most one half preserve unit-ball test admissibility
for a test supported in the half ball. Source: `paper/main.tex:948–955`. -/
theorem isSpatialTest_comp_sub_of_half_ball {d : ℕ} {ζ : Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hsupp : tsupport ζ ⊆ originBall d (1/2))
    {a : Vec d} (ha : euclideanNorm a ≤ 1/2) :
    IsSpatialTest (originBall d 1) (fun x => ζ (x-a)) := by
  refine ⟨hζ.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
  · simpa only [Function.comp_def, sub_eq_add_neg] using
      hc.comp_homeomorph (Homeomorph.addRight (-a))
  · intro x hx
    have hx' : x-a ∈ tsupport ζ :=
      tsupport_comp_subset_preimage ζ (continuous_id.sub continuous_const) hx
    have hsmall := hsupp hx'
    change euclideanNorm (x-a) < 1/2 at hsmall
    change euclideanNorm x < 1
    have htri := TimeChange.euclideanNorm_add_le (x-a) a
    rw [sub_add_cancel] at htri
    linarith

end EinsteinRelation.Correctors
