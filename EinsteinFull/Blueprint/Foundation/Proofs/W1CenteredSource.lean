import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_centered_u2D_source
import EinsteinFull.Blueprint.Foundation.node_e_u3A_lp_u2D_growth
import EinsteinFull.Calculus.ComplexCenteringSourceSupport
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import EinsteinFull.Calculus.LocalEnergyDomainSupport
import EinsteinFull.Calculus.ComplexTransposeGradientTimeSupport
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinRelation.Correctors.ScalarSetAverageMoments

/-!
# Support for the centered-source reduction

The gradient is the actual positive-time horizontal gradient. Centering either
side of the forward evolution preserves it. The structural constant is chosen
before the environment, force, datum and time. The actual transpose energy
estimate and closed generator graph give positive-time full-domain membership
for arbitrary L2 data. Adding the literal source primitive then restores the
homogeneous generator equation. Together with restart and stationary moment
averaging, this proves the exact centered-source reduction from finite-p growth.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The first gradient and source-integrability clauses of the centered-source
contract, with a single structural constant and an actual continuous gradient.
No finite-moment or smoothness premise is needed for these clauses. -/
theorem centered_source_exists_gradient (d : ℕ) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d) (ζ : ℂ)
        (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q i ζ P →
        ∀ f : Lp ℂ 2 (reducedLaw Q),
          letI := reducedLaw_probability Q
          let u := fun r : ℝ =>
            centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))
          ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
            ContinuousOn G (Ioi 0) ∧
            (∀ r : ℝ, 0 < r →
              HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
                (u r) (G r) ∧
              ‖G r‖ ≤ C / Real.sqrt r * Real.exp (C * ‖ζ‖ ^ 2 * r) * ‖f‖) ∧
            (let c := fun r : ℝ => ζ * (∫ ω,
                ∑ j : Fin d, (ω.1 0 j i : ℂ) * G r j ω ∂reducedLaw Q)
             ∀ t : ℝ, 0 < t → IntegrableOn c (Icc (t / 4) t)) := by
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  let A := 2 * Real.sqrt K
  let B := 65 * (K * ((d : ℝ) * K) ^ 2)
  let C := A + B + 1
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans D.one_le_ellipticity)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hAC : A ≤ C := by dsimp only [C]; linarith only [hB]
  have hBC : B ≤ C := by dsimp only [C]; linarith only [hA]
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro Q i ζ P hP f
  letI := reducedLaw_probability Q
  dsimp only
  refine ⟨hP.gradientOrbit f, hP.continuousOn_gradientOrbit f, ?_, ?_⟩
  · intro r hr
    constructor
    · rw [hP.centered_apply]
      exact hP.centered_gradientOrbit_spec f hr
    · have hb := hP.norm_gradientOrbit_le f hr le_rfl
      have he : 65 * complexForceShift d D.ellipticity ζ * r = B * ‖ζ‖ ^ 2 * r := by
        dsimp only [complexForceShift, B, K]
        ring
      rw [he] at hb
      have hexp : Real.exp (B * ‖ζ‖ ^ 2 * r) ≤ Real.exp (C * ‖ζ‖ ^ 2 * r) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBC (sq_nonneg _)) hr.le)
      calc
        ‖hP.gradientOrbit f r‖ ≤
            A / Real.sqrt r * Real.exp (B * ‖ζ‖ ^ 2 * r) * ‖f‖ := by
          convert hb using 1
          dsimp only [A, K]
          ring
        _ ≤ C / Real.sqrt r * Real.exp (C * ‖ζ‖ ^ 2 * r) * ‖f‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (div_le_div_of_nonneg_right hAC (Real.sqrt_nonneg _))
              hexp (Real.exp_pos _).le (by positivity)) (norm_nonneg _)
  · intro t ht
    exact (hP.integrableOn_centeringSource f t.toNNReal).mono_set
      (by intro r hr; exact ⟨(by linarith [hr.1]), hr.2.trans (Real.le_coe_toNNReal t)⟩)

/-- The exact graph dependency supplies the finite moment required at t/8.
The bilinear transpose is constructed from the actual forward operators. -/
theorem centered_source_memLp_of_lp_growth
    (hLp : node_e_u3A_lp_u2D_growthStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d) {p : ℝ} (hp : 2 ≤ p)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q))
    (t : ℝ) :
    MemLp (centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f)))
      (ENNReal.ofReal p) (reducedLaw Q) := by
  obtain ⟨C, _, hC⟩ := hLp d D.ellipticity D.dependenceRange p hd hp
  exact (hC Q i ζ P (fun s => complexL2Transpose (reducedLaw Q) (P s)) hP
    (isComplexTransposeSemigroup_complexL2Transpose Q P)).1 (t / 8).toNNReal f hf |>.2.2.1

/-- The actual coefficient-column source is continuous at positive times. -/
theorem continuousOn_centered_source
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ContinuousOn (hP.centeringSource f) (Ioi 0) := by
  letI := reducedLaw_probability Q
  have he : hP.centeringSource f = fun r =>
      ζ * (∫ ω, complexForceDrift Q i (hP.gradientOrbit f r) ω ∂reducedLaw Q) := by
    funext r
    rw [IsComplexEnvironmentSemigroup.centeringSource,
      integral_congr_ae (complexForceDrift_coe Q i (hP.gradientOrbit f r))]
  rw [he]
  exact continuousOn_const.mul ((continuous_complexL2_integral (reducedLaw Q)).comp_continuousOn
    ((complexForceDrift Q i).continuous.comp_continuousOn
      (hP.continuousOn_gradientOrbit f)))

/-- The literal time primitive has the actual source as its derivative on all
positive times, including times before the lower endpoint t/4. -/
theorem hasDerivAt_centered_source_primitive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    HasDerivAt (fun s => ∫ v in (t / 4)..s, hP.centeringSource f v)
      (hP.centeringSource f r) r := by
  have hc := continuousOn_centered_source hP f
  have hcr := hc.continuousAt (isOpen_Ioi.mem_nhds hr)
  have hi : IntervalIntegrable (hP.centeringSource f) volume (t / 4) r :=
    (hc.mono (by
      intro v hv
      exact lt_of_lt_of_le (lt_min (by linarith) hr) hv.1)).intervalIntegrable
  exact intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hc r hr) hcr

/-- The literal twice-centered orbit restarts at any nonnegative time. -/
theorem centered_source_restart
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {a r : ℝ} (ha : 0 ≤ a) (har : a ≤ r) :
    centeredComplexLp Q (P (r - a).toNNReal
      (centeredComplexLp Q (P a.toNNReal (centeredComplexLp Q f)))) =
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) := by
  rw [hP.centered_apply, ← ContinuousLinearMap.comp_apply, ← hP.2.1]
  have he : (r - a).toNNReal + a.toNNReal = r.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ ha,
      Real.coe_toNNReal _ (sub_nonneg.mpr har), Real.coe_toNNReal _ (ha.trans har)]
    ring
  rw [he]

/-- Uniqueness identifies the actual Euclidean gradient after restarting the
centered orbit. No representative or gradient regularity premise is introduced. -/
theorem centered_source_gradient_restart
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {a r : ℝ} (ha : 0 ≤ a) (har : a < r) :
    hP.gradientOrbit
      (centeredComplexLp Q (P a.toNNReal (centeredComplexLp Q f))) (r - a) =
        hP.gradientOrbit f r := by
  have hg := hP.centered_gradientOrbit_spec
    (centeredComplexLp Q (P a.toNNReal (centeredComplexLp Q f))) (sub_pos.mpr har)
  have he := centered_source_restart hP f ha har.le
  rw [he, hP.centered_apply] at hg
  exact WithLp.ofLp_injective 2
    (hg.unique (hP.centered_gradientOrbit_spec f (ha.trans_lt har)))

private theorem norm_mean_le_l2 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ ω, f ω ∂reducedLaw Q‖ ≤ ‖f‖ := by
  letI := reducedLaw_probability Q
  apply (norm_integral_le_integral_norm _).trans
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- The actual column mean is bounded by the Euclidean horizontal gradient. -/
theorem centered_source_norm_le_gradient
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (r : ℝ) :
    ‖hP.centeringSource f r‖ ≤
      ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * ‖hP.gradientOrbit f r‖ := by
  rw [IsComplexEnvironmentSemigroup.centeringSource,
    integral_congr_ae (complexForceDrift_coe Q i (hP.gradientOrbit f r)).symm, norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_mean_le_l2 Q _) (norm_nonneg ζ)).trans
    (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (norm_complexForceDrift_apply_le Q i (hP.gradientOrbit f r)) (norm_nonneg ζ))

private theorem inv_sqrt_window {t r : ℝ} (ht : 0 < t)
    (hr : r ∈ Icc (t / 4) t) :
    1 / Real.sqrt (r - t / 8) ≤ 3 / Real.sqrt t := by
  have hs : 0 < r - t / 8 := by linarith [hr.1]
  have hsq := Real.sq_sqrt hs.le
  have htq := Real.sq_sqrt ht.le
  have hroot : Real.sqrt t ≤ 3 * Real.sqrt (r - t / 8) := by
    nlinarith [Real.sqrt_nonneg t, Real.sqrt_nonneg (r - t / 8), hr.1]
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hs) (Real.sqrt_pos.mpr ht)).mpr
  simpa only [one_mul] using hroot

/-- The source estimate on the literal window [t/4,t] uses the actual centered
input at t/8. Its constant precedes the law, complex force and datum. -/
theorem centered_source_window_bound (d : ℕ) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d) (ζ : ℂ)
        (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        ∀ hP : IsComplexEnvironmentSemigroup Q i ζ P,
        ∀ (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ), 0 < t →
        ∀ r ∈ Icc (t / 4) t,
          ‖hP.centeringSource f r‖ ≤
            C * ‖ζ‖ / Real.sqrt t * Real.exp (C * ‖ζ‖ ^ 2 * t) *
              ‖centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f))‖ := by
  obtain ⟨A, hA, hgrad⟩ := centered_source_exists_gradient d D
  let B := (d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le
      (zero_le_one.trans D.one_le_ellipticity))
  let C := A + 3 * B * A + 1
  have hAC : A ≤ C := by
    have hpos : 0 ≤ 3 * B * A := by positivity
    dsimp only [C]
    linarith
  have hBC : 3 * B * A ≤ C := by dsimp only [C]; linarith
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro Q i ζ P hP f t ht r hr
  let v := centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f))
  have hs : 0 < r - t / 8 := by linarith [hr.1]
  obtain ⟨G, _, hG, _⟩ := hgrad Q i ζ P hP v
  have hGr := hG (r - t / 8) hs
  dsimp only at hGr
  have heG : G (r - t / 8) = hP.gradientOrbit v (r - t / 8) := by
    apply WithLp.ofLp_injective 2
    rw [hP.centered_apply] at hGr
    exact hGr.1.unique (hP.centered_gradientOrbit_spec v hs)
  have hb := hGr.2
  rw [heG, centered_source_gradient_restart hP f (by linarith : 0 ≤ t / 8)
    (by linarith [hr.1] : t / 8 < r)] at hb
  have htime : r - t / 8 ≤ t := by linarith [hr.2]
  have hexp : Real.exp (A * ‖ζ‖ ^ 2 * (r - t / 8)) ≤
      Real.exp (C * ‖ζ‖ ^ 2 * t) := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left htime (mul_nonneg hA.le (sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAC (sq_nonneg _)) ht.le)
  have hden : A / Real.sqrt (r - t / 8) ≤ 3 * A / Real.sqrt t := by
    have h := mul_le_mul_of_nonneg_left (inv_sqrt_window ht hr) hA.le
    convert h using 1 <;> ring
  have hbound : ‖hP.gradientOrbit f r‖ ≤
      (3 * A / Real.sqrt t) * Real.exp (C * ‖ζ‖ ^ 2 * t) * ‖v‖ :=
    hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hden hexp (Real.exp_pos _).le (by positivity)) (norm_nonneg _))
  calc
    ‖hP.centeringSource f r‖ ≤ ‖ζ‖ * B * ‖hP.gradientOrbit f r‖ :=
      centered_source_norm_le_gradient hP f r
    _ ≤ ‖ζ‖ * B * ((3 * A / Real.sqrt t) * Real.exp (C * ‖ζ‖ ^ 2 * t) * ‖v‖) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg (norm_nonneg _) hB)
    _ = (3 * B * A) * ‖ζ‖ / Real.sqrt t * Real.exp (C * ‖ζ‖ ^ 2 * t) * ‖v‖ := by ring
    _ ≤ C * ‖ζ‖ / Real.sqrt t * Real.exp (C * ‖ζ‖ ^ 2 * t) * ‖v‖ := by
      gcongr

/-- The zero extension of the actual gradient makes its source zero at all
nonpositive times; this is an identity of the actual mean, not representatives. -/
theorem centered_source_eq_zero_of_nonpos
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {r : ℝ} (hr : r ≤ 0) : hP.centeringSource f r = 0 := by
  apply norm_le_zero_iff.mp
  simpa only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_neg (not_lt.mpr hr),
    norm_zero, mul_zero] using centered_source_norm_le_gradient hP f r

/-- The literal source primitive is continuous on the entire real time axis,
including zero, since the inverse-square-root singularity is integrable. -/
theorem continuous_centered_source_primitive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) (a : ℝ) :
    Continuous (fun r => ∫ v in a..r, hP.centeringSource f v) := by
  apply intervalIntegral.continuous_primitive
  intro b c
  have hn : IntegrableOn (hP.centeringSource f) (Iic (0 : ℝ)) :=
    integrableOn_zero.congr_fun
      (fun r hr => (centered_source_eq_zero_of_nonpos hP f hr).symm) measurableSet_Iic
  have hp := hP.integrableOn_centeringSource f (max b c).toNNReal
  have hi := integrableOn_union.mpr ⟨hn, hp⟩
  apply (hi.mono_set ?_).intervalIntegrable
  intro r hr
  by_cases h : r ≤ 0
  · exact Or.inl h
  · exact Or.inr ⟨(not_le.mp h).le, hr.2.trans (Real.le_coe_toNNReal _)⟩

/-- A single jointly strongly measurable field represents the corrected orbit
at EVERY real time, with equality a.e. in the actual reduced law at each time. -/
theorem centered_source_joint_representative
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) :
    letI := reducedLaw_probability Q
    let w := fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
        Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ U : ℝ × FieldPair d → ℂ,
      StronglyMeasurable U ∧ ∀ r, (fun ω => U (r, ω)) =ᵐ[reducedLaw Q] w r := by
  letI := reducedLaw_probability Q
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hc := (Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (continuous_centered_source_primitive hP f (t / 4))
  obtain ⟨U, hU, heU⟩ := StronglyMeasurable.exists_joint_l2_representative
    (hu.add hc).stronglyMeasurable
  exact ⟨U, hU.stronglyMeasurable, heU⟩

/-- The literal primitive has the expected square-root-time bound throughout
[t/4,t], using the input at t/8 and the same source-bound constant. -/
theorem centered_source_primitive_window_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hb : ∀ r ∈ Icc (t / 4) t,
      ‖hP.centeringSource f r‖ ≤ C * ‖ζ‖ / Real.sqrt t *
        Real.exp (C * ‖ζ‖ ^ 2 * t) *
          ‖centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f))‖)
    {r : ℝ} (hr : r ∈ Icc (t / 4) t) :
    ‖∫ v in (t / 4)..r, hP.centeringSource f v‖ ≤
      C * ‖ζ‖ * Real.sqrt t * Real.exp (C * ‖ζ‖ ^ 2 * t) *
        ‖centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f))‖ := by
  let B := C * ‖ζ‖ / Real.sqrt t * Real.exp (C * ‖ζ‖ ^ 2 * t) *
    ‖centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f))‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hi : ‖∫ v in (t / 4)..r, hP.centeringSource f v‖ ≤ B * |r - t / 4| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => by
      rw [uIoc_of_le hr.1] at hv
      exact hb v ⟨hv.1.le, hv.2.trans hr.2⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hr.1)] at hi
  have hlen : r - t / 4 ≤ t := by linarith [hr.2]
  apply hi.trans ((mul_le_mul_of_nonneg_left hlen hB).trans_eq ?_)
  dsimp only [B]
  have hs := Real.sq_sqrt ht.le
  have hn : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have he : t / Real.sqrt t = Real.sqrt t := by
    apply (div_eq_iff hn).2
    nlinarith only [hs]
  calc
    _ = (C * ‖ζ‖ * Real.exp (C * ‖ζ‖ ^ 2 * t) *
        ‖centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f))‖) *
          (t / Real.sqrt t) := by ring
    _ = _ := by rw [he]; ring

/-- Successive normalized finite-volume RMS averages inherit uniform probability
moments. This applies directly to the nested space-time average in the target. -/
theorem centered_source_double_average
    {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {S : Set X} {T : Set Y} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ∞) (hT0 : ν T ≠ 0) (hTfin : ν T ≠ ∞)
    {p B : ℝ} (hp : 2 ≤ p) (hB : 0 ≤ B)
    (F : Ω × (X × Y) → ℝ) (hF : Measurable F)
    (hb : ∀ r ∈ S, ∀ y ∈ T,
      MemLp (fun ω => F (ω, (r, y))) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => F (ω, (r, y))) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal B) :
    MemLp (fun ω => Real.sqrt (⨍ r in S, ⨍ y in T, F (ω, (r, y)) ^ 2 ∂ν ∂μ))
        (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => Real.sqrt (⨍ r in S, ⨍ y in T, F (ω, (r, y)) ^ 2 ∂ν ∂μ))
        (ENNReal.ofReal p) Q ≤ ENNReal.ofReal B := by
  let g : Ω × X → ℝ := fun z => Real.sqrt (⨍ y in T, F (z.1, (z.2, y)) ^ 2 ∂ν)
  have hFm : Measurable (fun z : (Ω × X) × Y => F (z.1.1, (z.1.2, z.2))) :=
    hF.comp ((measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hg : Measurable g := by
    simp only [g, setAverage_eq']
    exact (hFm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.sqrt
  have hgm (r : X) (hr : r ∈ S) :
      MemLp (fun ω => g (ω, r)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => g (ω, r)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal B := by
    exact Correctors.scalarL2_setAverage_moment_le Q ν hT hT0 hTfin hp hB
      (fun z => F (z.1, (r, z.2)))
      (hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))) (hb r hr)
  have h := Correctors.scalarL2_setAverage_moment_le Q μ hS hS0 hSfin hp hB g hg hgm
  have he (ω : Ω) (r : X) : g (ω, r) ^ 2 = ⨍ y in T, F (ω, (r, y)) ^ 2 ∂ν := by
    apply Real.sq_sqrt
    exact integral_nonneg fun y => sq_nonneg _
  simpa only [he] using h

/-- Translation invariance and the actual joint representative give the literal
normalized space-time RMS estimate from bounds on its time slices. The center
and positive Euclidean radius are arbitrary. -/
theorem centered_source_local_average_of_slices
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p B t : ℝ} (hp : 2 ≤ p) (hB : 0 ≤ B) (ht : 0 < t)
    (U : ℝ × FieldPair d → ℂ) (hU : StronglyMeasurable U)
    (hslices : ∀ r ∈ Icc (t / 4) t,
      MemLp (fun ω => U (r, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => U (r, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal B)
    (x : Vec d) (ρ : ℝ) (hρ : 0 < ρ) :
    let N := fun ω : FieldPair d => Real.sqrt
      (⨍ r in Icc (t / 4) t,
        ⨍ y in {y : Vec d | euclideanNorm (y - x) < ρ}, ‖U (r, translate y ω)‖ ^ 2)
    MemLp N (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm N (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal B := by
  letI := reducedLaw_probability Q
  have hT : MeasurableSet {y : Vec d | euclideanNorm (y - x) < ρ} := by
    apply IsOpen.measurableSet
    unfold euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hvol := ENNReal.toReal_pos_iff.mp (localSpatialEnergy_window_volume x ρ hρ)
  have htime : volume (Icc (t / 4) t) ≠ 0 := by
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  let F : FieldPair d × (ℝ × Vec d) → ℝ := fun z => ‖U (z.2.1, translate z.2.2 z.1)‖
  have hF : Measurable F := hU.measurable.norm.comp
    (measurable_snd.fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.snd.prodMk measurable_fst)))
  apply centered_source_double_average (reducedLaw Q) volume volume measurableSet_Icc hT
    htime (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hvol.1.ne' hvol.2.ne hp hB F hF
  intro r hr y _hy
  have h := hslices r hr
  have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) y
  refine ⟨(h.1.comp_measurePreserving hm).norm, ?_⟩
  change eLpNorm (fun ω => ‖U (r, translate y ω)‖) _ _ ≤ _
  have hUm : AEStronglyMeasurable (fun ω => U (r, translate y ω)) (reducedLaw Q) :=
    (h.1.comp_measurePreserving hm).aestronglyMeasurable
  rw [eLpNorm_norm _ hUm]
  exact (eLpNorm_comp_measurePreserving h.1.aestronglyMeasurable hm).trans_le h.2

/-- The restarted finite-p estimate and the actual source bound control every
corrected time slice. Cp is chosen before the law, force, datum and time. -/
theorem centered_source_window_lp_bound
    (hLp : node_e_u3A_lp_u2D_growthStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d) {p C : ℝ} (hp : 2 ≤ p) (hC : 0 < C) :
    ∃ Cp : ℝ, 0 < Cp ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d) (ζ : ℂ)
        (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
        (hP : IsComplexEnvironmentSemigroup Q i ζ P)
        (f : Lp ℂ 2 (reducedLaw Q)),
        MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
        ∀ t : ℝ, 0 < t →
        (∀ r ∈ Icc (t / 4) t,
          ‖hP.centeringSource f r‖ ≤ C * ‖ζ‖ / Real.sqrt t *
            Real.exp (C * ‖ζ‖ ^ 2 * t) *
              ‖centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f))‖) →
        ∀ r ∈ Icc (t / 4) t,
        let w := centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
          Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
        MemLp w (ENNReal.ofReal p) (reducedLaw Q) ∧
          eLpNorm w (ENNReal.ofReal p) (reducedLaw Q) ≤
            ENNReal.ofReal (Cp * (1 + ‖ζ‖ * Real.sqrt t) *
              Real.exp (Cp * ‖ζ‖ ^ 2 * t)) *
            eLpNorm (centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f)))
              (ENNReal.ofReal p) (reducedLaw Q) := by
  obtain ⟨A, hA, hgrowth⟩ := hLp d D.ellipticity D.dependenceRange p hd hp
  let Cp := A + C + 2
  have hCp : 0 < Cp := by dsimp only [Cp]; positivity
  have hACp : A ≤ Cp := by dsimp only [Cp]; linarith
  have hCCp : C ≤ Cp := by dsimp only [Cp]; linarith
  have h2Cp : 2 ≤ Cp := by dsimp only [Cp]; linarith
  refine ⟨Cp, hCp, ?_⟩
  intro Q i ζ P hP f hf t ht hb r hr
  letI := reducedLaw_probability Q
  let v := centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f))
  let u := centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))
  let c := ∫ s in (t / 4)..r, hP.centeringSource f s
  have hv : MemLp v (ENNReal.ofReal p) (reducedLaw Q) :=
    centered_source_memLp_of_lp_growth hLp hd D hp Q i ζ P hP f hf t
  have hs : 0 ≤ r - t / 8 := by linarith [hr.1]
  have hg := (hgrowth Q i ζ P (fun s => complexL2Transpose (reducedLaw Q) (P s))
    hP (isComplexTransposeSemigroup_complexL2Transpose Q P)).1 (r - t / 8).toNNReal v hv
  have he := centered_source_restart hP f (by linarith : 0 ≤ t / 8)
    (by linarith [hr.1] : t / 8 ≤ r)
  have hu : MemLp u (ENNReal.ofReal p) (reducedLaw Q) := by
    have heS : centeredComplexLp Q (P (r - t / 8).toNNReal (centeredComplexLp Q v)) = u := by
      rw [hP.centered_apply]
      exact he
    simpa only [heS] using hg.2.2.1
  have hub : eLpNorm u (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal (2 * Real.exp (A * ‖ζ‖ ^ 2 * (r - t / 8))) *
        eLpNorm v (ENNReal.ofReal p) (reducedLaw Q) := by
    have heS : centeredComplexLp Q (P (r - t / 8).toNNReal (centeredComplexLp Q v)) = u := by
      rw [hP.centered_apply]
      exact he
    simpa only [heS, Real.coe_toNNReal _ hs] using hg.2.2.2.2.2
  have hc : MemLp (Lp.const 2 (reducedLaw Q) c) (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_const c).ae_eq (Lp.coeFn_const 2 (reducedLaw Q) c).symm
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
  have hvnorm : ENNReal.ofReal ‖v‖ ≤ eLpNorm v (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v)]
    exact eLpNorm_le_eLpNorm_of_exponent_le
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp))
  let B := C * ‖ζ‖ * Real.sqrt t * Real.exp (C * ‖ζ‖ ^ 2 * t)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcb : eLpNorm (Lp.const 2 (reducedLaw Q) c) (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal B * eLpNorm v (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [eLpNorm_congr_ae (Lp.coeFn_const 2 (reducedLaw Q) c)]
    change eLpNorm (fun _ : FieldPair d => c) _ _ ≤ _
    rw [eLpNorm_const c (ne_zero_of_lt (lt_of_lt_of_le zero_lt_one hp1))
      (IsProbabilityMeasure.ne_zero (reducedLaw Q))]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, ← ofReal_norm_eq_enorm]
    apply (ENNReal.ofReal_le_ofReal (centered_source_primitive_window_bound hP f ht hC.le hb hr)).trans
    rw [ENNReal.ofReal_mul hB]
    simpa only [mul_comm] using mul_le_mul_left hvnorm (ENNReal.ofReal B)
  have hexpA : Real.exp (A * ‖ζ‖ ^ 2 * (r - t / 8)) ≤ Real.exp (Cp * ‖ζ‖ ^ 2 * t) := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (by linarith [hr.2] : r - t / 8 ≤ t)
      (by positivity : 0 ≤ A * ‖ζ‖ ^ 2)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hACp (sq_nonneg _)) ht.le)
  have hexpC : Real.exp (C * ‖ζ‖ ^ 2 * t) ≤ Real.exp (Cp * ‖ζ‖ ^ 2 * t) := by
    apply Real.exp_le_exp.mpr
    gcongr
  have htotal : 2 * Real.exp (A * ‖ζ‖ ^ 2 * (r - t / 8)) + B ≤
      Cp * (1 + ‖ζ‖ * Real.sqrt t) * Real.exp (Cp * ‖ζ‖ ^ 2 * t) := by
    calc
      _ ≤ 2 * Real.exp (Cp * ‖ζ‖ ^ 2 * t) +
          C * ‖ζ‖ * Real.sqrt t * Real.exp (Cp * ‖ζ‖ ^ 2 * t) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hexpA (by norm_num))
          (mul_le_mul_of_nonneg_left hexpC (by positivity))
      _ ≤ Cp * Real.exp (Cp * ‖ζ‖ ^ 2 * t) +
          Cp * ‖ζ‖ * Real.sqrt t * Real.exp (Cp * ‖ζ‖ ^ 2 * t) := by gcongr
      _ = _ := by ring
  have headd := Lp.coeFn_add u (Lp.const 2 (reducedLaw Q) c)
  refine ⟨(hu.add hc).ae_eq headd.symm, ?_⟩
  calc
    _ ≤ eLpNorm u (ENNReal.ofReal p) (reducedLaw Q) +
        eLpNorm (Lp.const 2 (reducedLaw Q) c) (ENNReal.ofReal p) (reducedLaw Q) := by
      rw [eLpNorm_congr_ae headd]
      exact eLpNorm_add_le hp1
    _ ≤ (ENNReal.ofReal (2 * Real.exp (A * ‖ζ‖ ^ 2 * (r - t / 8))) + ENNReal.ofReal B) *
        eLpNorm v (ENNReal.ofReal p) (reducedLaw Q) := by
      simpa only [add_mul] using add_le_add hub hcb
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add (by positivity) hB]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal htotal) _

/-- The full normalized local space-time moment and representative clauses,
with both constants chosen in the source order and no extra graph premise.
The homogeneous generator equation is a separate remaining obligation. -/
theorem centered_source_exists_moment_representative
    (hLp : node_e_u3A_lp_u2D_growthStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 2 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d) (ζ : ℂ)
        (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
        (hP : IsComplexEnvironmentSemigroup Q i ζ P)
        (f : Lp ℂ 2 (reducedLaw Q)),
        MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
        ∀ t : ℝ, 0 < t →
        letI := reducedLaw_probability Q
        let u := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))
        let w := fun r : ℝ => u r +
          Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
        (∀ r ∈ Icc (t / 4) t,
          ‖hP.centeringSource f r‖ ≤ C * ‖ζ‖ / Real.sqrt t *
            Real.exp (C * ‖ζ‖ ^ 2 * t) * ‖u (t / 8)‖) ∧
        ∃ U : ℝ × FieldPair d → ℂ,
          StronglyMeasurable U ∧
          (∀ r : ℝ, (fun ω => U (r, ω)) =ᵐ[reducedLaw Q] w r) ∧
          ∀ (x : Vec d) (ρ : ℝ), 0 < ρ →
            let N := fun ω : FieldPair d => Real.sqrt
              (⨍ r in Icc (t / 4) t,
                ⨍ y in {y : Vec d | euclideanNorm (y - x) < ρ}, ‖U (r, translate y ω)‖ ^ 2)
            MemLp N (ENNReal.ofReal p) (reducedLaw Q) ∧
              eLpNorm N (ENNReal.ofReal p) (reducedLaw Q) ≤
                ENNReal.ofReal (Cp * (1 + ‖ζ‖ * Real.sqrt t) *
                  Real.exp (Cp * ‖ζ‖ ^ 2 * t)) *
                eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) := by
  obtain ⟨C, hC, hsource⟩ := centered_source_window_bound d D
  refine ⟨C, hC, ?_⟩
  intro p hp
  obtain ⟨Cp, hCp, hwindow⟩ := centered_source_window_lp_bound hLp hd D hp hC
  refine ⟨Cp, hCp, ?_⟩
  intro Q i ζ P hP f hf t ht
  letI := reducedLaw_probability Q
  have hb := hsource Q i ζ P hP f t ht
  refine ⟨hb, ?_⟩
  obtain ⟨U, hU, heU⟩ := centered_source_joint_representative hP f t
  refine ⟨U, hU, heU, ?_⟩
  intro x ρ hρ
  let v := centeredComplexLp Q (P (t / 8).toNNReal (centeredComplexLp Q f))
  let A := Cp * (1 + ‖ζ‖ * Real.sqrt t) * Real.exp (Cp * ‖ζ‖ ^ 2 * t)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hv := centered_source_memLp_of_lp_growth hLp hd D hp Q i ζ P hP f hf t
  have hfinite : eLpNorm v (ENNReal.ofReal p) (reducedLaw Q) ≠ ∞ := hv.eLpNorm_ne_top
  have he : ENNReal.ofReal (A * (eLpNorm v (ENNReal.ofReal p) (reducedLaw Q)).toReal) =
      ENNReal.ofReal A * eLpNorm v (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_toReal hfinite]
  have hslices (r : ℝ) (hr : r ∈ Icc (t / 4) t) :
      MemLp (fun ω => U (r, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => U (r, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (A * (eLpNorm v (ENNReal.ofReal p) (reducedLaw Q)).toReal) := by
    have hw := hwindow Q i ζ P hP f hf t ht hb r hr
    exact ⟨hw.1.ae_eq (heU r).symm, by rw [eLpNorm_congr_ae (heU r), he]; exact hw.2⟩
  have h := centered_source_local_average_of_slices Q hp
    (mul_nonneg hA ENNReal.toReal_nonneg) ht U hU hslices x ρ hρ
  simpa only [he] using h

/-- A time-integrated transpose gradient estimate supplies a good testing time. -/
theorem centered_source_transpose_good_time
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) {t : ℝ} (ht : 0 < t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ h : Lp ℂ 2 (reducedLaw Q),
      ∃ s ∈ Ioc (0 : ℝ) (t / 2),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (T s.toNNReal h) (complexTransposeGradientOrbit Q T h s) ∧
        ‖complexTransposeGradientOrbit Q T h s‖ ≤ L * ‖h‖ := by
  let a := t / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  let E := 2 * (Real.exp (2 * Λ) * Λ) * Real.exp (2 * complexForceShift d Λ ζ * a)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)))
      (Real.exp_pos _).le
  let L := Real.sqrt (a⁻¹ * E)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  refine ⟨L, hL, ?_⟩
  intro h
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) a)
  have hm : μ ≠ 0 := by
    apply (Measure.measure_univ_ne_zero).mp
    simp only [μ, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact (ENNReal.ofReal_pos.mpr ha).ne'
  letI : IsFiniteMeasure μ := ⟨by
    simp only [μ, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_lt_top⟩
  have he := hT.gradientOrbit_horizon_energy hP h ⟨a, ha.le⟩
  have hi : Integrable (fun s => ‖complexTransposeGradientOrbit Q T h s‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm he.1.aestronglyMeasurable).mp he.1
  let good := fun s => s ∈ Ioc (0 : ℝ) a ∧
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (T s.toNNReal h) (complexTransposeGradientOrbit Q T h s)
  have hg : ∀ᵐ s ∂μ, good s :=
    (ae_restrict_mem measurableSet_Ioc).and he.2.1
  obtain ⟨s, hs, hb⟩ := exists_notMem_null_le_average hm hi (show μ {s | ¬good s} = 0 from hg)
  have hsg : good s := not_not.mp hs
  have hmean : (⨍ s, ‖complexTransposeGradientOrbit Q T h s‖ ^ 2 ∂μ) ≤
      (a⁻¹ * E) * ‖h‖ ^ 2 := by
    rw [average_eq]
    have hv : μ.real Set.univ = a := by
      simp only [Measure.real, μ, Measure.restrict_apply_univ, Real.volume_Ioc,
        sub_zero, ENNReal.toReal_ofReal ha.le]
    rw [hv]
    have hb : (∫ s in (0 : ℝ)..a, ‖complexTransposeGradientOrbit Q T h s‖ ^ 2) ≤ E * ‖h‖ ^ 2 := he.2.2
    simp only [smul_eq_mul]
    rw [intervalIntegral.integral_of_le ha.le] at hb
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ha.le)).trans_eq (by ring)
  refine ⟨s, hsg.1, hsg.2, ?_⟩
  have hsq : L ^ 2 = a⁻¹ * E := Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr ha.le) hE)
  have hbound := hb.trans hmean
  nlinarith only [hbound, hsq, norm_nonneg (complexTransposeGradientOrbit Q T h s),
    norm_nonneg h, mul_nonneg hL (norm_nonneg h)]

private theorem source_pairing_norm {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (f g : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ ω, f ω * g ω ∂reducedLaw Q‖ ≤ ‖f‖ * ‖g‖ := by
  rw [← inner_complexL2Conjugation_eq_integral_mul]
  simpa only [norm_complexL2Conjugation] using
    norm_inner_le_norm (complexL2Conjugation (reducedLaw Q) f) g

/-- The actual principal form is bounded on Euclidean L2 gradients. -/
theorem centered_source_principal_norm
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (G H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :
    ‖∫ ω, ∑ j : Fin d, ∑ k : Fin d,
        (ω.1 0 j k : ℂ) * G k ω * H j ω ∂reducedLaw Q‖ ≤
      (d : ℝ) ^ 2 * (Real.exp (2 * Λ) * Λ) * ‖G‖ * ‖H‖ := by
  let K := Real.exp (2 * Λ) * Λ
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter)
  have hi (j k : Fin d) : Integrable
      (fun ω => (ω.1 0 j k : ℂ) * G k ω * H j ω) (reducedLaw Q) := by
    apply ((Lp.memLp (complexCoefficientMul Q j k (G k))).integrable_mul (Lp.memLp (H j))).congr
    filter_upwards [complexCoefficientMul_coe Q j k (G k)] with ω hω
    simp only [Pi.mul_apply, hω]
  have hb (j k : Fin d) :
      ‖∫ ω, (ω.1 0 j k : ℂ) * G k ω * H j ω ∂reducedLaw Q‖ ≤ K * ‖G‖ * ‖H‖ := by
    have he : (∫ ω, (ω.1 0 j k : ℂ) * G k ω * H j ω ∂reducedLaw Q) =
        ∫ ω, (complexCoefficientMul Q j k (G k)) ω * H j ω ∂reducedLaw Q := by
      apply integral_congr_ae
      filter_upwards [complexCoefficientMul_coe Q j k (G k)] with ω hω
      rw [hω]
    rw [he]
    exact (source_pairing_norm Q _ _).trans
      (mul_le_mul ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (norm_complexCoefficientMul_le Q j k) (PiLp.norm_apply_le G k)
          (norm_nonneg _) hK)) (PiLp.norm_apply_le H j) (norm_nonneg _) (by positivity))
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hi j k))]
  simp_rw [integral_finset_sum _ (fun k _ => hi _ k)]
  calc
    _ ≤ ∑ j : Fin d, ∑ k : Fin d,
        ‖∫ ω, (ω.1 0 j k : ℂ) * G k ω * H j ω ∂reducedLaw Q‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
    _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, K * ‖G‖ * ‖H‖ :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hb j k))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Full-generator testing uses the actual weak form and Euclidean gradients. -/
theorem centered_source_generator_pairing_bound
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {f g v : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    (G H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H) :
    ‖∫ ω, g ω * v ω ∂reducedLaw Q‖ ≤
      ((d : ℝ) ^ 2 * (Real.exp (2 * Λ) * Λ) +
        ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ) * Λ))) * ‖G‖ * (‖H‖ + ‖v‖) := by
  obtain ⟨G₀, hG₀, hw⟩ := hfg
  have he := hG₀.unique hG
  rw [he] at hw
  rw [hw v H hH]
  have hf := source_pairing_norm Q (complexForceDrift Q i G) v
  rw [integral_complexForceDrift_mul] at hf
  have hf' := hf.trans (mul_le_mul_of_nonneg_right
    (norm_complexForceDrift_apply_le Q i G) (norm_nonneg _))
  have hp := centered_source_principal_norm Q G H
  have hn : ‖-(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  have hcoeff : 0 ≤ Real.exp (2 * Λ) * Λ :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  calc
    _ ≤ ‖-(1 / 2 : ℂ)‖ *
        ‖∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * H j ω ∂reducedLaw Q‖ +
        ‖ζ‖ * ‖∫ ω, (∑ j, (ω.1 0 j i : ℂ) * G j ω) * v ω ∂reducedLaw Q‖ := by
      simpa only [norm_mul] using norm_add_le
        (-(1 / 2 : ℂ) * (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * H j ω ∂reducedLaw Q))
        (ζ * (∫ ω, (∑ j, (ω.1 0 j i : ℂ) * G j ω) * v ω ∂reducedLaw Q))
    _ ≤ (d : ℝ) ^ 2 * (Real.exp (2 * Λ) * Λ) * ‖G‖ * ‖H‖ +
        ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ) * Λ) * ‖G‖ * ‖v‖) := by
      exact add_le_add ((mul_le_of_le_one_left (norm_nonneg _) hn).trans hp)
        (mul_le_mul_of_nonneg_left hf' (norm_nonneg _))
    _ ≤ _ := by
      have h1 : 0 ≤ (d : ℝ) ^ 2 * (Real.exp (2 * Λ) * Λ) * ‖G‖ * ‖v‖ := by positivity
      have h2 : 0 ≤ ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) * ‖G‖ * ‖H‖ := by positivity
      nlinarith only [h1, h2]


/-- At each positive time the forward generator output is bounded by the
initial L2 datum, initially on the full generator domain. -/
theorem centered_source_generator_output_bound
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) {t : ℝ} (ht : 0 < t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f g : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q i ζ f g → ‖P t.toNNReal g‖ ≤ B * ‖f‖ := by
  let T := fun s => complexL2Transpose (reducedLaw Q) (P s)
  have hT : IsComplexTransposeSemigroup Q P T := isComplexTransposeSemigroup_complexL2Transpose Q P
  obtain ⟨L, hL, hgood⟩ := centered_source_transpose_good_time hP hT ht
  let K := Real.exp (2 * Λ) * Λ
  let F := 2 * Real.sqrt K * Real.exp (65 * complexForceShift d Λ ζ * t) *
    (Real.sqrt (t / 2))⁻¹
  let M := Real.exp (complexForceShift d Λ ζ * t)
  let A := (d : ℝ) ^ 2 * K + ‖ζ‖ * ((d : ℝ) * K)
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A * F * (L + M), by positivity, ?_⟩
  intro f g hfg
  let z := P t.toNNReal g
  let h := complexL2Conjugation (reducedLaw Q) z
  obtain ⟨s, hs, hH, hbH⟩ := hgood h
  have ha : 0 < t - s := by linarith [hs.2]
  have heP : P s.toNNReal (P (t - s).toNNReal g) = z := by
    rw [← ContinuousLinearMap.comp_apply, ← hP.2.1]
    apply congrArg (fun a : ℝ≥0 => P a g)
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal s hs.1.le,
      Real.coe_toNNReal (t - s) ha.le, Real.coe_toNNReal t ht.le]
    ring
  have hepair : ‖∫ ω, z ω * h ω ∂reducedLaw Q‖ = ‖z‖ ^ 2 := by
    rw [← inner_complexL2Conjugation_eq_integral_mul]
    change ‖inner ℂ h h‖ = _
    rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq, norm_complexL2Conjugation]
  have he : (∫ ω, z ω * h ω ∂reducedLaw Q) =
      ∫ ω, P (t - s).toNNReal g ω * T s.toNNReal h ω ∂reducedLaw Q := by
    rw [← heP]
    exact hT s.toNNReal _ h
  have hbG : ‖hP.gradientOrbit f (t - s)‖ ≤ F * ‖f‖ := by
    have hb := hP.norm_gradientOrbit_le f ha (by linarith [hs.1] : t - s ≤ t)
    have hi : (Real.sqrt (t - s))⁻¹ ≤ (Real.sqrt (t / 2))⁻¹ :=
      inv_le_inv₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr (by positivity)) |>.mpr
        (Real.sqrt_le_sqrt (by linarith [hs.2]))
    have hc : 0 ≤ 2 * Real.sqrt K * Real.exp (65 * complexForceShift d Λ ζ * t) * ‖f‖ := by positivity
    have hh := mul_le_mul_of_nonneg_left hi hc
    apply hb.trans
    convert hh using 1
    dsimp only [F, K]
    ring
  have hbT : ‖T s.toNNReal h‖ ≤ M * ‖h‖ := by
    apply ((T s.toNNReal).le_opNorm h).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (hT.norm_le hP s.toNNReal).trans
    rw [Real.coe_toNNReal s hs.1.le]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hs.2])
      (complexForceShift_nonneg Q ζ))
  have hb := centered_source_generator_pairing_bound (hP.map_generator hfg (t - s).toNNReal)
    (hP.gradientOrbit f (t - s)) (complexTransposeGradientOrbit Q T h s)
    (hP.gradientOrbit_spec f ha) hH
  have hfinal : ‖z‖ ^ 2 ≤ (A * F * (L + M) * ‖f‖) * ‖z‖ := by
    rw [← hepair, he]
    calc
      _ ≤ A * ‖hP.gradientOrbit f (t - s)‖ *
          (‖complexTransposeGradientOrbit Q T h s‖ + ‖T s.toNNReal h‖) := hb
      _ ≤ A * (F * ‖f‖) * (L * ‖h‖ + M * ‖h‖) := by gcongr
      _ = _ := by rw [norm_complexL2Conjugation]; ring
  by_cases hz : ‖z‖ = 0
  · change ‖z‖ ≤ _
    rw [hz]
    positivity
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (mul_le_mul_iff_left₀ hzpos).mp (by nlinarith only [hfinal])


private theorem centered_source_cauchy_control
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {u : ℕ → E} {v : ℕ → F} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ n m, ‖v n - v m‖ ≤ B * ‖u n - u m‖) (hu : CauchySeq u) :
    CauchySeq v := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hpos : 0 < B + 1 := by linarith only [hB]
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu
    (ε / (B + 1)) (div_pos hε hpos)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hgap := hN n hn m hm
  rw [dist_eq_norm] at hgap ⊢
  calc
    _ ≤ B * ‖u n - u m‖ := hb n m
    _ ≤ (B + 1) * ‖u n - u m‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < ε := (lt_div_iff₀' hpos).mp hgap

private theorem centered_source_graph_limit
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {u v : ℕ → Lp ℂ 2 (reducedLaw Q)} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hu : Tendsto u atTop (𝓝 f)) (hv : Tendsto v atTop (𝓝 g))
    (hp : ∀ n, IsComplexGeneratorPair Q i ζ (u n) (v n)) :
    IsComplexGeneratorPair Q i ζ f g := by
  apply (isClosed_complexGenerator_graph Q i ζ).mem_of_tendsto
    (f := fun n : ℕ => (u n, v n)) (x := (f, g)) (b := atTop)
  · exact hu.prodMk_nhds hv
  · exact Eventually.of_forall hp

private theorem centered_source_graph_difference
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {u v : ℕ → Lp ℂ 2 (reducedLaw Q)}
    (hv : ∀ n, IsComplexGeneratorPair Q i ζ (u n) (v n)) (n m : ℕ) :
    IsComplexGeneratorPair Q i ζ (u n - u m) (v n - v m) := by
  simpa only [neg_one_smul, ← sub_eq_add_neg] using (hv n).add ((hv m).smul (-1))

private theorem centered_source_domain_of_approximation
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ f g, IsComplexGeneratorPair Q i ζ f g → ‖P t.toNNReal g‖ ≤ B * ‖f‖)
    (u v : ℕ → Lp ℂ 2 (reducedLaw Q)) (hu : Tendsto u atTop (𝓝 f))
    (hv : ∀ n, IsComplexGeneratorPair Q i ζ (u n) (v n)) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ (P t.toNNReal f) g := by
  have hcontrol (n m : ℕ) : ‖P t.toNNReal (v n) - P t.toNNReal (v m)‖ ≤ B * ‖u n - u m‖ := by
    have hd := centered_source_graph_difference hv n m
    simpa only [map_sub] using hb (u n - u m) (v n - v m) hd
  have hc : CauchySeq (fun n => P t.toNNReal (v n)) :=
    centered_source_cauchy_control hB hcontrol hu.cauchySeq
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨g, ?_⟩
  exact centered_source_graph_limit (((P t.toNNReal).continuous.tendsto f).comp hu) hg
    (fun n => hP.map_generator (hv n) t.toNNReal)

/-- Closedness and actual resolvent approximation upgrade positive-time
smoothing to membership in the entire forced generator domain. -/
theorem centered_source_positive_generator_domain
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t : ℝ} (ht : 0 < t) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ (P t.toNNReal f) g := by
  obtain ⟨B, hB, hb⟩ := centered_source_generator_output_bound hP ht
  exact centered_source_domain_of_approximation hP f t B hB hb
    (fun n => forcedComplexResolventApproximation Q i ζ n f)
    (fun n => forcedComplexYosida Q i ζ n f + (complexForceShift d Λ ζ : ℂ) •
      forcedComplexResolventApproximation Q i ζ n f)
    (tendsto_forcedComplexResolventApproximation Q i ζ f)
    (fun n => forcedComplexYosida_graph Q i ζ n f)

/-- The actual forward orbit is strongly differentiable and in the full
 generator graph at every positive time for arbitrary L2 initial data. -/
theorem centered_source_positive_hasDerivAt
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t : ℝ} (ht : 0 < t) :
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      HasDerivAt (fun s : ℝ => P s.toNNReal f) g t ∧
      IsComplexGeneratorPair Q i ζ (P t.toNNReal f) g := by
  let a := t / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hta : 0 < t - a := by dsimp only [a]; linarith only [ht]
  obtain ⟨g, hg⟩ := centered_source_positive_generator_domain hP f ha
  have hd := centeredEquations_forward_hasDerivAt hP hg (t - a).toNNReal
    (by rwa [Real.coe_toNNReal (t - a) hta.le])
  rw [Real.coe_toNNReal (t - a) hta.le] at hd
  have hder := hd.scomp t ((hasDerivAt_id t).sub_const a)
  simp only [id_eq, one_smul] at hder
  have he (s : ℝ) (hs : a ≤ s) : P (s - a).toNNReal (P a.toNNReal f) = P s.toNNReal f := by
    rw [← ContinuousLinearMap.comp_apply, ← hP.2.1]
    apply congrArg (fun r : ℝ≥0 => P r f)
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal (s - a) (sub_nonneg.mpr hs),
      Real.coe_toNNReal a ha.le, Real.coe_toNNReal s (ha.le.trans hs)]
    ring
  refine ⟨P (t - a).toNNReal g, ?_, ?_⟩
  · apply hder.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (show a < t by dsimp only [a]; linarith only [ht])] with s hs
    exact (he s hs.le).symm
  · simpa only [he t (by dsimp only [a]; linarith only [ht])] using
      hP.map_generator hg (t - a).toNNReal


/-- Adding the literal source primitive restores the homogeneous full
 generator equation at every positive time for arbitrary initial L2 data. -/
theorem centered_source_corrected_equation
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t : ℝ} (ht : 0 < t) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∀ r : ℝ, 0 < r → ∃ V : Lp ℂ 2 (reducedLaw Q),
      HasDerivAt w V r ∧ IsComplexGeneratorPair Q i ζ (w r) V := by
  letI := reducedLaw_probability Q
  dsimp only
  intro r hr
  obtain ⟨V, hd, hg⟩ := centered_source_positive_hasDerivAt hP f hr
  obtain ⟨G, hG, hm⟩ := hg.integral_eq
  have heG := hG.unique (hP.gradientOrbit_spec f hr)
  have hmean : (∫ ω, V ω ∂reducedLaw Q) = hP.centeringSource f r := by
    rw [heG] at hm
    exact hm
  have hcenter := ((centeredComplexLpCLM Q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r hd
  have hprimitive := ((Lp.constL 2 (reducedLaw Q) ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r
    (hasDerivAt_centered_source_primitive hP f ht hr)
  have hsum := hcenter.add hprimitive
  change HasDerivAt (fun s : ℝ => centeredComplexLpCLM Q (P s.toNNReal f) +
    Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v))
    (centeredComplexLpCLM Q V + Lp.const 2 (reducedLaw Q) (hP.centeringSource f r)) r at hsum
  have hcancel : centeredComplexLpCLM Q V + Lp.const 2 (reducedLaw Q) (hP.centeringSource f r) = V := by
    rw [centeredComplexLpCLM_apply, centeredComplexLp, hmean, sub_add_cancel]
  refine ⟨V, ?_, ?_⟩
  · rw [hcancel] at hsum
    simpa only [centeredComplexLpCLM_apply, hP.centered_apply] using hsum
  · have hconst := isComplexGeneratorPair_const Q i ζ
      ((∫ v in (t / 4)..r, hP.centeringSource f v) -
        (∫ ω, P r.toNNReal f ω ∂reducedLaw Q))
    have he : centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
        Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v) =
        P r.toNNReal f + Lp.const 2 (reducedLaw Q)
          ((∫ v in (t / 4)..r, hP.centeringSource f v) -
            (∫ ω, P r.toNNReal f ω ∂reducedLaw Q)) := by
      rw [hP.centered_apply, centeredComplexLp]
      change _ = P r.toNNReal f + (Lp.constL 2 (reducedLaw Q) ℂ) (_ - _)
      rw [map_sub]
      change _ = P r.toNNReal f +
        (Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v) -
          Lp.const 2 (reducedLaw Q) (∫ ω, P r.toNNReal f ω ∂reducedLaw Q))
      abel
    rw [he]
    simpa only [add_zero] using hg.add hconst

/-- The reviewed centered-source contract follows from its sole finite-p
 growth graph dependency, on the actual stationary complex evolution. -/
theorem node_l_u3A_forced_u2D_local_u23_centered_u2D_source_of_deps
    (hLp : node_e_u3A_lp_u2D_growthStmt) :
    node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt := by
  intro d hd D
  obtain ⟨A, hA, hgradient⟩ := centered_source_exists_gradient d D
  obtain ⟨B, hB, hmoment⟩ := centered_source_exists_moment_representative hLp hd D
  let C := A + B + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ C := by dsimp only [C]; linarith only [hB]
  have hBC : B ≤ C := by dsimp only [C]; linarith only [hA]
  refine ⟨C, hC, ?_⟩
  intro p hp
  obtain ⟨Cp, hCp, hmoment⟩ := hmoment p hp
  refine ⟨Cp, hCp, ?_⟩
  intro Q _hQ ζ P hP f hf
  letI := reducedLaw_probability Q
  dsimp only
  obtain ⟨G, _hGc, hG, _hci⟩ := hgradient Q ⟨0, by omega⟩ ζ P hP f
  dsimp only at hG
  have hGe (r : ℝ) (hr : 0 < r) : G r = hP.gradientOrbit f r := by
    apply WithLp.ofLp_injective 2
    apply (hG r hr).1.unique
    rw [hP.centered_apply]
    exact hP.centered_gradientOrbit_spec f hr
  refine ⟨hP.gradientOrbit f, ?_, ?_⟩
  · intro r hr
    refine ⟨?_, ?_⟩
    · rw [hP.centered_apply]
      exact hP.centered_gradientOrbit_spec f hr
    · have hb := (hG r hr).2
      rw [hGe r hr] at hb
      apply hb.trans
      gcongr
  · intro t ht
    have hm := hmoment Q ⟨0, by omega⟩ ζ P hP f hf t ht
    refine ⟨centered_source_memLp_of_lp_growth hLp hd D hp Q ⟨0, by omega⟩ ζ P hP f hf t,
      ?_, ?_, centered_source_corrected_equation hP f ht, hm.2⟩
    · change IntegrableOn (hP.centeringSource f) (Icc (t / 4) t)
      exact (hP.integrableOn_centeringSource f ⟨t, ht.le⟩).mono_set
        (fun r hr => ⟨by linarith only [hr.1, ht], hr.2⟩)
    · intro r hr
      apply (hm.1 r hr).trans
      gcongr

end EinsteinFull.Blueprint
