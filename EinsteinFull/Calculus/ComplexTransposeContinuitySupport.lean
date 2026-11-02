import EinsteinFull.Calculus.ComplexTransposeSupport

/-!
# Strong continuity of the actual bilinear transpose

A Hilbert adjoint contraction estimate gives strong continuity at zero from
forward strong continuity. Contractive semigroup increments extend it to every
time; the proved exponential scalar shift treats all complex forces.
-/

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull

variable {α : Type*} [MeasurableSpace α]

/-- Bilinear transposition is complex linear in the bounded operator. -/
theorem complexL2Transpose_smul (μ : Measure α) (c : ℂ)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    complexL2Transpose μ (c • A) = c • complexL2Transpose μ A := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [complexL2Transpose, map_smulₛₗ, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, starRingEnd_self_apply]

/-- A contraction adjoint's squared increment is controlled by the forward increment. -/
theorem norm_complexL2Adjoint_sub_sq_le (μ : Measure α)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hA : ‖A‖ ≤ 1) (f : Lp ℂ 2 μ) :
    ‖ContinuousLinearMap.adjoint A f - f‖ ^ 2 ≤ 2 * ‖f‖ * ‖A f - f‖ := by
  have hb : ‖ContinuousLinearMap.adjoint A f‖ ≤ ‖f‖ := by
    have hn := (ContinuousLinearMap.adjoint A).le_opNorm f
    rw [ContinuousLinearMap.adjoint.norm_map] at hn
    exact hn.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (norm_nonneg f))
  have hi := re_inner_le_norm (𝕜 := ℂ) f (f - A f)
  rw [inner_sub_right, inner_self_eq_norm_sq_to_K] at hi
  change ((‖f‖ : ℂ)^2 - inner ℂ f (A f)).re ≤ ‖f‖ * ‖f - A f‖ at hi
  rw [Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re, norm_sub_rev f (A f)] at hi
  rw [norm_sub_sq (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_left]
  change ‖ContinuousLinearMap.adjoint A f‖^2 - 2 * (inner ℂ f (A f)).re + ‖f‖^2 ≤ _
  nlinarith only [hi, hb, norm_nonneg f, norm_nonneg (ContinuousLinearMap.adjoint A f)]

private theorem continuousAt_adjoint_zero (μ : Measure α)
    (P : ℝ≥0 → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (h0 : P 0 = ContinuousLinearMap.id ℂ _) (hc : ∀ f, Continuous (fun t => P t f))
    (hb : ∀ t, ‖P t‖ ≤ 1) (f : Lp ℂ 2 μ) :
    ContinuousAt (fun t => ContinuousLinearMap.adjoint (P t) f) 0 := by
  have hf : Tendsto (fun t => 2 * ‖f‖ * ‖P t f - f‖) (𝓝 0) (𝓝 0) := by
    have h := (((hc f).tendsto 0).sub_const f).norm.const_mul (2 * ‖f‖)
    simpa only [h0, ContinuousLinearMap.id_apply, sub_self, norm_zero, mul_zero] using h
  have hs := squeeze_zero (fun t => sq_nonneg ‖ContinuousLinearMap.adjoint (P t) f-f‖)
    (fun t => norm_complexL2Adjoint_sub_sq_le μ (P t) (hb t) f) hf
  have hn := hs.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  have hz := tendsto_iff_norm_sub_tendsto_zero.mpr hn
  change Tendsto _ (𝓝 0) (𝓝 _)
  simpa only [h0, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] using hz

private theorem contraction_increment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : ℝ≥0 → E →L[ℂ] E)
    (ha : ∀ s t, T (s+t) = (T s).comp (T t)) (hb : ∀ t, ‖T t‖ ≤ 1)
    (f : E) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖T t f - T s f‖ ≤ ‖T (t-s) f - f‖ := by
  have he : T t f - T s f = T s (T (t-s) f-f) := by
    rw [map_sub, ← ContinuousLinearMap.comp_apply, ← ha, add_tsub_cancel_of_le hst]
  rw [he]
  exact ((T s).le_opNorm _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb s) (norm_nonneg _))

/-- A strongly continuous complex L2 contraction semigroup has a strongly continuous transpose. -/
theorem continuous_complexL2Transpose_apply_of_contractive (μ : Measure α)
    (P : ℝ≥0 → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (h0 : P 0 = ContinuousLinearMap.id ℂ _)
    (ha : ∀ s t, P (s+t) = (P s).comp (P t))
    (hc : ∀ f, Continuous (fun t => P t f)) (hb : ∀ t, ‖P t‖ ≤ 1)
    (f : Lp ℂ 2 μ) : Continuous (fun t => complexL2Transpose μ (P t) f) := by
  let T := fun t => complexL2Transpose μ (P t)
  have hT0 : T 0 = ContinuousLinearMap.id ℂ _ := by
    simp only [T, h0, complexL2Transpose_id]
  have hTa (s t : ℝ≥0) : T (s+t) = (T s).comp (T t) := by
    dsimp only [T]
    rw [add_comm s t, ha, complexL2Transpose_comp]
  have hTb (t : ℝ≥0) : ‖T t‖ ≤ 1 := by
    change ‖complexL2Transpose μ (P t)‖ ≤ 1
    rw [norm_complexL2Transpose]
    exact hb t
  have hTc : ContinuousAt (fun t => T t f) 0 :=
    (complexL2Conjugation μ).continuous.continuousAt.comp
      (continuousAt_adjoint_zero μ P h0 hc hb (complexL2Conjugation μ f))
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hTc ε hε
  refine ⟨δ, hδ, fun s hs => ?_⟩
  change dist (T s f) (T t f) < ε
  rcases le_total s t with hst | hts
  · have he : dist (t-s) 0 = dist s t := by
      rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_sub hst, NNReal.coe_zero, sub_zero,
        abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst)),
        abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ t from hst)), neg_sub]
    have hh := hd (he ▸ hs)
    rw [hT0, ContinuousLinearMap.id_apply, dist_eq_norm] at hh
    rw [dist_eq_norm, norm_sub_rev]
    exact (contraction_increment T hTa hTb f s t hst).trans_lt hh
  · have he : dist (s-t) 0 = dist s t := by
      rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_sub hts, NNReal.coe_zero, sub_zero,
        abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ s from hts))]
    have hh := hd (he ▸ hs)
    rw [hT0, ContinuousLinearMap.id_apply, dist_eq_norm] at hh
    rw [dist_eq_norm]
    exact (contraction_increment T hTa hTb f t s hts).trans_lt hh

open EinsteinRelation

/-- The actual bilinear transpose of the forced evolution is strongly continuous on all L2. -/
theorem continuous_complexL2Transpose_forcedComplexEvolution_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t => complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q i ζ t) f) := by
  have hs := continuous_complexL2Transpose_apply_of_contractive (reducedLaw Q)
    (shiftedForcedComplexEvolution Q i ζ) (shiftedForcedComplexEvolution_zero Q i ζ)
    (shiftedForcedComplexEvolution_add Q i ζ)
    (continuous_shiftedForcedComplexEvolution_apply Q i ζ)
    (norm_shiftedForcedComplexEvolution_le Q i ζ) f
  have he := (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp ((continuous_const (y := complexForceShift d Λ₀ ζ)).fun_mul NNReal.continuous_coe))).fun_smul hs
  simpa only [forcedComplexEvolution, complexL2Transpose_smul,
    ContinuousLinearMap.smul_apply, Function.comp_def] using! he

/-- Every family in the full frozen transpose predicate has strongly continuous orbits. -/
theorem IsComplexTransposeSemigroup.continuous_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexTransposeSemigroup Q P R)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t => R t f) := by
  rw [hR.eq_complexL2Transpose, hP.eq_forcedComplexEvolution]
  exact continuous_complexL2Transpose_forcedComplexEvolution_apply Q i ζ f

end EinsteinFull
