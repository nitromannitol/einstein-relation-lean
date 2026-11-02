import EinsteinFull.Work.W2.CorrectorCorrelationSupport
import EinsteinFull.Calculus.ComplexEvolutionGeneratorSupport

/-!
# Undamped correlations of the actual unforced stationary evolution

Symmetry is passed from the actual resolvent to its bounded Yosida generators,
then their exponentials, and finally their strong limit.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors

private def conjugateLp {d : ℕ} (μ : Measure (FieldPair d)) :
    Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.conjCLE.toContinuousLinearMap.compLpL 2 μ

private theorem conjugateLp_apply {d : ℕ} (μ : Measure (FieldPair d)) (f : Lp ℂ 2 μ) :
    conjugateLp μ f = star f := by
  apply Lp.ext
  filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f,
    Lp.coeFn_star f] with ω ha hb
  change (star f) ω = star (f ω) at hb
  simpa only [conjugateLp, Complex.conjCLE_apply, Complex.star_def, hb] using! ha

private theorem star_sub_lp {d : ℕ} (μ : Measure (FieldPair d)) (f g : Lp ℂ 2 μ) :
    star (f - g) = star f - star g := by
  simp only [← conjugateLp_apply μ, map_sub]

private theorem star_real_smul_lp {d : ℕ} (μ : Measure (FieldPair d))
    (c : ℝ) (f : Lp ℂ 2 μ) : star (c • f) = c • star f := by
  simp only [← conjugateLp_apply μ, map_smul]

private theorem star_complex_real_smul_lp {d : ℕ} (μ : Measure (FieldPair d))
    (c : ℝ) (f : Lp ℂ 2 μ) : star ((c : ℂ) • f) = (c : ℂ) • star f := by
  simpa only [Complex.coe_smul] using! star_real_smul_lp μ c f

/-- Conjugation preserves the actual full unforced weak generator graph. -/
theorem IsComplexGeneratorPair.unforced_star {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i 0 f g) :
    IsComplexGeneratorPair Q i 0 (star f) (star g) := by
  obtain ⟨G, hG, hw⟩ := hfg
  refine ⟨fun j => star (G j), fun j => (hG j).star, ?_⟩
  intro v V hV
  have h := congrArg (starRingEnd ℂ)
    (hw (star v) (fun j => star (V j)) (fun j => (hV j).star))
  simp only [zero_mul, add_zero] at h ⊢
  have hm : (∫ ω, (star g) ω * v ω ∂reducedLaw Q) =
      (starRingEnd ℂ) (∫ ω, g ω * (star v) ω ∂reducedLaw Q) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star g, Lp.coeFn_star v] with ω hg hv
    change (star g) ω = star (g ω) at hg
    change (star v) ω = star (v ω) at hv
    simp only [hg, hv, map_mul, starRingEnd_apply, star_star]
  rw [hm, h, map_mul]
  have he : (starRingEnd ℂ) (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω *
      (star (V j)) ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * (star (G k)) ω * V j ω ∂reducedLaw Q := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (G j)),
      ae_all_iff.mpr (fun j => Lp.coeFn_star (V j))] with ω hGω hVω
    have hc (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
    change (∀ j, (star (G j)) ω = star (G j ω)) at hGω
    change (∀ j, (star (V j)) ω = star (V j ω)) at hVω
    simp only [map_sum, map_mul, hGω, hVω, starRingEnd_apply, hc, star_star]
  rw [show (starRingEnd ℂ) (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω *
    (star (V j)) ω ∂reducedLaw Q) = _ from he]
  congr 1
  norm_num [map_ofNat]

/-- The actual unforced positive resolvent commutes with conjugation. -/
theorem unforcedComplexResolvent_star {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    unforcedComplexResolvent Q i s hs (star f) = star (unforcedComplexResolvent Q i s hs f) := by
  apply IsComplexGeneratorPair.unforced_resolvent_unique hs
    (unforcedComplexResolvent_spec Q i s hs (star f))
  convert! (unforcedComplexResolvent_spec Q i s hs f).unforced_star using 1
  simp only [star_sub_lp, star_complex_real_smul_lp, star_real_smul_lp]

private theorem exp_apply_star {d : ℕ} (μ : Measure (FieldPair d))
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : ∀ f, A (star f) = star (A f)) (f : Lp ℂ 2 μ) :
    NormedSpace.exp A (star f) = star (NormedSpace.exp A f) := by
  have hp (m : ℕ) (u : Lp ℂ 2 μ) : (A ^ m) (star u) = star ((A ^ m) u) := by
    induction m with
    | zero => rfl
    | succ m hm =>
      simp only [pow_succ', ContinuousLinearMap.mul_apply, hm, hA]
  let E (u : Lp ℂ 2 μ) := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) u).restrictScalars ℝ
  have hs (u : Lp ℂ 2 μ) := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map
    (E u) (E u).continuous
  have hc := (hs f).map (conjugateLp μ) (conjugateLp μ).continuous
  have he : HasSum (fun m : ℕ => (m.factorial⁻¹ : ℝ) • (A ^ m) (star f))
      (star (NormedSpace.exp A f)) := by
    have hc' : HasSum (fun m : ℕ => conjugateLp μ ((m.factorial⁻¹ : ℝ) • (A ^ m) f))
        (conjugateLp μ (NormedSpace.exp A f)) := hc
    simpa only [map_smul, conjugateLp_apply, ← hp] using! hc'
  exact (hs (star f)).unique he

/-- The actual bounded unforced Yosida generators commute with conjugation. -/
theorem unforcedComplexYosida_star {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    unforcedComplexYosida Q i n (star f) = star (unforcedComplexYosida Q i n f) := by
  simp only [unforcedComplexYosida, unforcedComplexResolventApproximation,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, unforcedComplexResolvent_star,
    star_sub_lp, star_complex_real_smul_lp, star_real_smul_lp]

/-- Real-time Yosida evolutions commute with conjugation on the actual L2 space. -/
theorem unforcedComplexYosidaEvolution_star {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (n : ℕ) (t : ℝ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    unforcedComplexYosidaEvolution Q i n t (star f) =
      star (unforcedComplexYosidaEvolution Q i n t f) := by
  apply exp_apply_star
  intro u
  simp only [ContinuousLinearMap.smul_apply, unforcedComplexYosida_star,
    star_real_smul_lp]

/-- The actual bounded unforced Yosida generators are self-adjoint. -/
theorem unforcedComplexYosida_isSelfAdjoint {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (n : ℕ) :
    IsSelfAdjoint (unforcedComplexYosida Q i n) := by
  unfold unforcedComplexYosida unforcedComplexResolventApproximation
  have hc : IsSelfAdjoint (((n : ℝ) + 1 : ℝ) : ℂ) := by
    exact Complex.conj_ofReal _
  exact hc.smul ((hc.smul (unforcedComplexResolvent_isSymmetric Q i ((n : ℝ) + 1)
    (by positivity)).isSelfAdjoint).sub (IsSelfAdjoint.one (R := Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))))

/-- Every real-time bounded unforced Yosida evolution is self-adjoint. -/
theorem unforcedComplexYosidaEvolution_isSelfAdjoint {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (n : ℕ) (t : ℝ) :
    IsSelfAdjoint (unforcedComplexYosidaEvolution Q i n t) := by
  change IsSelfAdjoint (NormedSpace.exp ((t : ℂ) • unforcedComplexYosida Q i n))
  exact ((show IsSelfAdjoint (t : ℂ) from Complex.conj_ofReal t).smul
    (unforcedComplexYosida_isSelfAdjoint Q i n)).exp

/-- Symmetry survives the actual strong unforced Yosida limit. -/
theorem unforcedComplexEvolution_isSymmetric {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (t : ℝ≥0) :
    (unforcedComplexEvolution Q i t).IsSymmetric := by
  intro f g
  have hf := (tendsto_unforcedComplexYosidaEvolution Q i t f).inner
    (tendsto_const_nhds (x := g)) (𝕜 := ℂ)
  have hg := (tendsto_const_nhds (x := f)).inner
    (tendsto_unforcedComplexYosidaEvolution Q i t g) (𝕜 := ℂ)
  exact tendsto_nhds_unique hf (hg.congr fun n =>
    ((unforcedComplexYosidaEvolution_isSelfAdjoint Q i n t).isSymmetric f g).symm)

/-- Every actual full unforced semigroup is self-adjoint. -/
theorem IsComplexEnvironmentSemigroup.unforced_isSymmetric
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) :
    (P t).IsSymmetric := by
  rw [hP.unique (isComplexEnvironmentSemigroup_unforcedComplexEvolution Q i)]
  exact unforcedComplexEvolution_isSymmetric Q i t

/-- Every actual unforced semigroup commutes with conjugation. -/
theorem IsComplexEnvironmentSemigroup.unforced_star
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) : P t (star f) = star (P t f) := by
  rw [hP.unique (isComplexEnvironmentSemigroup_unforcedComplexEvolution Q i)]
  exact tendsto_nhds_unique (tendsto_unforcedComplexYosidaEvolution Q i t (star f))
    (by
      have h := ((conjugateLp (reducedLaw Q)).continuous.tendsto _).comp
        (tendsto_unforcedComplexYosidaEvolution Q i t f)
      simpa only [Function.comp_def, conjugateLp_apply,
        ← unforcedComplexYosidaEvolution_star] using! h)

/-- Literal half-time Hermitian pairing, for all actual complex L2 data. -/
theorem IsComplexEnvironmentSemigroup.unforced_half_time_inner
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    inner ℂ g (P t f) = inner ℂ (P (t / 2) g) (P (t / 2) f) := by
  calc
    _ = inner ℂ g (P (t / 2) (P (t / 2) f)) := by
      rw [← ContinuousLinearMap.comp_apply, ← hP.2.1, add_halves]
    _ = _ := (hP.unforced_isSymmetric (t / 2) g (P (t / 2) f)).symm

/-- The actual drift representatives are real almost everywhere. -/
theorem IsReducedDriftObservation.conj_ae {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q, star (β j ω) = β j ω := by
  filter_upwards [hβ j] with ω hω
  rw [hω]
  exact Complex.conj_ofReal _

/-- The actual drift L2 classes are fixed by conjugation. -/
theorem IsReducedDriftObservation.star_eq {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) : star (β j) = β j := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (β j), hβ.conj_ae j] with ω hs hβω
  change (star (β j)) ω = star (β j ω) at hs
  exact hs.trans hβω

/-- Actual evolved drift representatives remain real almost everywhere at each time. -/
theorem IsReducedDriftObservation.semigroup_conj_ae {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) :
    ∀ᵐ ω ∂reducedLaw Q, star (P t (β j) ω) = P t (β j) ω := by
  have he : star (P t (β j)) = P t (β j) := by
    rw [← hP.unforced_star, hβ.star_eq]
  filter_upwards [Lp.coeFn_star (P t (β j))] with ω hω
  change (star (P t (β j))) ω = star (P t (β j) ω) at hω
  rw [he] at hω
  exact hω.symm

/-- The literal drift correlation is the Hermitian L2 pairing. -/
theorem IsReducedDriftObservation.correlation_eq_inner {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, β j ω * f ω ∂reducedLaw Q) = inner ℂ (β j) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hβ.conj_ae j] with ω hω
  simp only [RCLike.inner_apply, starRingEnd_apply, hω, mul_comm]

/-- The actual drift correlation is its exact half-time Hermitian pairing. -/
theorem IsReducedDriftObservation.correlation_half_time {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) :
    (∫ ω, β j ω * P t (β k) ω ∂reducedLaw Q) =
      inner ℂ (P (t / 2) (β j)) (P (t / 2) (β k)) := by
  rw [hβ.correlation_eq_inner, hP.unforced_half_time_inner]

/-- The half-time pairing is literally the bilinear expectation of the real evolved drifts. -/
theorem IsReducedDriftObservation.correlation_half_time_integral
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) :
    (∫ ω, β j ω * P t (β k) ω ∂reducedLaw Q) =
      ∫ ω, P (t / 2) (β j) ω * P (t / 2) (β k) ω ∂reducedLaw Q := by
  rw [hβ.correlation_half_time i j k hP, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hβ.semigroup_conj_ae i j hP (t / 2)] with ω hω
  simp only [RCLike.inner_apply, starRingEnd_apply, hω, mul_comm]

/-- Each actual cross correlation is real, with its representatives qualified almost everywhere. -/
theorem IsReducedDriftObservation.correlation_im_eq_zero
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) :
    (∫ ω, β j ω * P t (β k) ω ∂reducedLaw Q).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [hβ.conj_ae j, hβ.semigroup_conj_ae i k hP t] with ω hβω hPω
  simp only [map_mul, starRingEnd_apply, hβω, hPω]

/-- Each actual diagonal drift correlation is a nonnegative real squared L2 norm. -/
theorem IsReducedDriftObservation.diagonal_correlation_eq_norm_sq
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) :
    (∫ ω, β j ω * P t (β j) ω ∂reducedLaw Q) =
      (‖P (t / 2) (β j)‖ ^ 2 : ℝ) := by
  rw [hβ.correlation_half_time i j j hP, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- The real part of each actual diagonal correlation is nonnegative at every time. -/
theorem IsReducedDriftObservation.diagonal_correlation_nonneg
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) :
    0 ≤ (∫ ω, β j ω * P t (β j) ω ∂reducedLaw Q).re := by
  rw [hβ.diagonal_correlation_eq_norm_sq i j hP, Complex.ofReal_re]
  exact sq_nonneg _

section TimeIntegrability
variable {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)

include hβ hP

private theorem integrable_laplace_half_norm_sq (j : Fin d) (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) *
      ‖P (t.toNNReal / 2) (β j)‖ ^ 2) (Ioi 0) := by
  have hi := (hP.integrable_laplace_correlation s hs (β j) (β j)).re
  change IntegrableOn (fun t : ℝ => ((Real.exp (-s * t) : ℂ) *
    ∫ ω, β j ω * P t.toNNReal (β j) ω ∂reducedLaw Q).re) (Ioi 0) at hi
  simpa only [hβ.diagonal_correlation_eq_norm_sq i j hP, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using! hi

private theorem tendsto_integral_laplace_half_norm_sq (j : Fin d) :
    Tendsto (fun n : ℕ => ∫ t in Ioi (0 : ℝ),
      Real.exp (-(1 / ((n : ℝ) + 1)) * t) * ‖P (t.toNNReal / 2) (β j)‖ ^ 2)
      atTop (𝓝 ((1 / 2 : ℝ) * inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q j)))) := by
  have hl := (Complex.continuous_re.tendsto _).comp
    (hβ.tendsto_laplace_correlation i j j hP
      (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  simp_rw [hβ.diagonal_correlation_eq_norm_sq i j hP,
    ← Complex.ofReal_mul, integral_complex_ofReal] at hl
  simpa using! hl

/-- The actual nonnegative diagonal drift correlation is time integrable, by Fatou. -/
theorem IsReducedDriftObservation.integrable_diagonal_half_norm_sq (j : Fin d) :
    IntegrableOn (fun t : ℝ => ‖P (t.toNNReal / 2) (β j)‖ ^ 2) (Ioi 0) := by
  let F : ℕ → ℝ → ℝ := fun n t => Real.exp (-(1 / ((n : ℝ) + 1)) * t) *
    ‖P (t.toNNReal / 2) (β j)‖ ^ 2
  have hFi (n : ℕ) : IntegrableOn (F n) (Ioi 0) :=
    integrable_laplace_half_norm_sq hβ i hP j _ (by positivity)
  have hFn (n : ℕ) (t : ℝ) : 0 ≤ F n t :=
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hl := ENNReal.tendsto_ofReal (tendsto_integral_laplace_half_norm_sq hβ i hP j)
  have hln : Tendsto (fun n => ∫⁻ t, ‖F n t‖ₑ ∂volume.restrict (Ioi 0)) atTop
      (𝓝 (ENNReal.ofReal ((1 / 2 : ℝ) * inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q j))))) := by
    convert! hl using 1
    ext n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hFi n)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun t => Real.norm_of_nonneg (hFn n t)
  apply integrable_of_tendsto (G := F) _ (fun n => (hFi n).aestronglyMeasurable)
    (hln.liminf_eq.trans_ne ENNReal.ofReal_ne_top)
  apply Eventually.of_forall
  intro t
  have he := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg.mul_const t).rexp
  simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul] using!
    he.mul_const (‖P (t.toNNReal / 2) (β j)‖ ^ 2)

/-- Half-time Cauchy–Schwarz bounds every actual cross correlation by the two diagonals. -/
theorem IsReducedDriftObservation.norm_correlation_le_half_norm_sq (j k : Fin d)
    (t : ℝ≥0) :
    ‖∫ ω, β j ω * P t (β k) ω ∂reducedLaw Q‖ ≤
      (‖P (t / 2) (β j)‖ ^ 2 + ‖P (t / 2) (β k)‖ ^ 2) / 2 := by
  rw [hβ.correlation_half_time i j k hP]
  have hc := norm_inner_le_norm (𝕜 := ℂ) (P (t / 2) (β j)) (P (t / 2) (β k))
  have hs := sq_nonneg (‖P (t / 2) (β j)‖ - ‖P (t / 2) (β k)‖)
  nlinarith only [hc, hs]

/-- The literal actual cross correlation is continuous in time, including zero. -/
theorem IsReducedDriftObservation.continuous_correlation (j k : Fin d) :
    Continuous (fun t : ℝ => ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q) := by
  simp_rw [hβ.correlation_eq_inner]
  exact continuous_const.inner ((hP.2.2.1 (β k)).comp continuous_real_toNNReal)

/-- Every undamped actual drift correlation is absolutely integrable over positive time. -/
theorem IsReducedDriftObservation.integrable_correlation (j k : Fin d) :
    IntegrableOn (fun t : ℝ => ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q)
      (Ioi 0) := by
  apply (((hβ.integrable_diagonal_half_norm_sq i hP j).add
    (hβ.integrable_diagonal_half_norm_sq i hP k)).div_const 2).mono'
      (hβ.continuous_correlation i hP j k).aestronglyMeasurable
  exact Eventually.of_forall fun t => hβ.norm_correlation_le_half_norm_sq i hP j k t.toNNReal

/-- Dominated convergence removes positive Laplace damping from the actual time integral. -/
theorem IsReducedDriftObservation.tendsto_laplace_correlation_integral (j k : Fin d)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (s : ι → ℝ) (hs : ∀ n, 0 < s n) (ht : Tendsto s l (𝓝 0)) :
    Tendsto (fun n => ∫ t in Ioi (0 : ℝ), (Real.exp (-s n * t) : ℂ) *
      ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q)
      l (𝓝 (∫ t in Ioi (0 : ℝ), ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => ‖∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q‖)
    (Eventually.of_forall fun n =>
      (hP.integrable_laplace_correlation (s n) (hs n) (β k) (β j)).aestronglyMeasurable)
    ?_ (hβ.integrable_correlation i hP j k).norm ?_
  · apply Eventually.of_forall
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hs n).le) ht0.le))
  · apply Eventually.of_forall
    intro t
    have he := Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((ht.neg.mul_const t).rexp)
    simpa only [Function.comp_apply, neg_zero, zero_mul, Real.exp_zero,
      Complex.ofReal_one, one_mul] using!
      he.mul_const (∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q)

/-- The undamped actual drift correlation integral is exactly half the canonical energy. -/
theorem IsReducedDriftObservation.integral_correlation_eq_corrector_energy (j k : Fin d) :
    (∫ t in Ioi (0 : ℝ), ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q) =
      (1 / 2 : ℂ) * (inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q k)) : ℝ) := by
  exact tendsto_nhds_unique
    (hβ.tendsto_laplace_correlation_integral i hP j k
      (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat)
    (hβ.tendsto_laplace_correlation i j k hP
      (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat)

/-- Adding the time-zero endpoint does not affect absolute integrability. -/
theorem IsReducedDriftObservation.integrable_correlation_Ici (j k : Fin d) :
    IntegrableOn (fun t : ℝ => ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q)
      (Ici 0) :=
  (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (hβ.integrable_correlation i hP j k)

/-- The endpoint-inclusive correlation integral has the same canonical half energy. -/
theorem IsReducedDriftObservation.integral_correlation_Ici_eq_corrector_energy
    (j k : Fin d) :
    (∫ t in Ici (0 : ℝ), ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q) =
      (1 / 2 : ℂ) * (inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q k)) : ℝ) := by
  rw [integral_Ici_eq_integral_Ioi, hβ.integral_correlation_eq_corrector_energy i hP]

/-- Absolute integrability of the frozen zero-force velocity correlation. -/
theorem IsReducedDriftObservation.integrable_velocityCorrelation (j k : Fin d)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) :
    IntegrableOn (fun t : ℝ => velocityCorrelation Q j k 0 P β a t.toNNReal) (Ioi 0) := by
  simp_rw [velocityCorrelation_zero_eq]
  exact hβ.integrable_correlation i hP j k

/-- The frozen undamped velocity correlation integrates to the literal anisotropic half energy. -/
theorem IsReducedDriftObservation.integral_velocityCorrelation_eq_corrector_energy
    (j k : Fin d) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∫ t in Ioi (0 : ℝ), velocityCorrelation Q j k 0 P β a t.toNNReal) =
      (1 / 2 : ℂ) * (∫ ω, ∑ a, ∑ b,
        ω.1 0 a b * correctorGradient Q k ω b * correctorGradient Q j ω a
        ∂reducedLaw Q : ℝ) := by
  simp_rw [velocityCorrelation_zero_eq, corrector_energy_eq_inner]
  exact hβ.integral_correlation_eq_corrector_energy i hP j k

/-- The actual unweighted linear velocity coefficient is the actual homogenized coefficient. -/
theorem IsReducedDriftObservation.linear_coefficient_eq_homogenizedCoefficient
    (j k : Fin d) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, ω.1 0 j k ∂reducedLaw Q : ℝ) -
      (2 : ℂ) * (∫ t in Ioi (0 : ℝ), velocityCorrelation Q j k 0 P β a t.toNNReal) =
      (homogenizedCoefficient Q j k : ℂ) := by
  rw [hβ.integral_velocityCorrelation_eq_corrector_energy i hP j k a,
    homogenizedCoefficient_eq_mean_sub_corrector_energy, corrector_energy_eq_inner]
  push_cast
  ring

end TimeIntegrability
end EinsteinFull
