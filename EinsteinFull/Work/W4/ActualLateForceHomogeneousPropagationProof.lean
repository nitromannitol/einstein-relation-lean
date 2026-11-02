import EinsteinFull.Calculus.ComplexMildDuhamelSupport
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport
import EinsteinFull.Frozen.IndexedEndpoint

/-!
# Actual late-interval endpoint evolution

All endpoints restart exactly at an arbitrary nonnegative time. Replacing the
force on the remaining interval costs an explicit square-root-time factor on
the actual early datum. This does not supply Gaussian averaging, scalar decay,
or the quantitative conclusions of Propositions 6.2 and Lemma 6.4.
-/

open MeasureTheory
open scoped NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
  {P Pdag R Rdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- A law-independent bound for the actual centering operator. -/
theorem norm_centeredComplexLpCLM_le_two (Q : EnvironmentLaw d Λ r) :
    ‖centeredComplexLpCLM Q‖ ≤ 2 := by
  letI := reducedLaw_probability Q
  apply (centeredComplexLpCLM Q).opNorm_le_bound (by norm_num)
  intro f
  have hc (c : ℂ) : ‖Lp.const 2 (reducedLaw Q) c‖ = ‖c‖ := by
    rw [Lp.norm_const' 2 (reducedLaw Q) c (by norm_num) (by norm_num), probReal_univ, Real.one_rpow, mul_one]
  have hi : (∫ ω, Lp.const 2 (reducedLaw Q) (1 : ℂ) ω * f ω ∂reducedLaw Q) =
      ∫ ω, f ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, one_mul]
  have hb := norm_inner_le_norm (𝕜 := ℂ)
    (complexL2Conjugation (reducedLaw Q) (Lp.const 2 (reducedLaw Q) 1)) f
  rw [inner_complexL2Conjugation_eq_integral_mul, hi,
    norm_complexL2Conjugation, hc, norm_one, one_mul] at hb
  rw [centeredComplexLpCLM_apply]
  change ‖f - Lp.const 2 (reducedLaw Q) (∫ ω, f ω ∂reducedLaw Q)‖ ≤ _
  exact (norm_sub_le _ _).trans (by rw [hc]; linarith only [hb])

/-- The actual remaining-interval evolution: projected forward evolution for
velocity and clock, and the bilinear transpose for the transpose endpoint. -/
def lateEndpointEvolution (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  match ν with
  | .inr true => Pdag t
  | _ => (centeredComplexLpCLM Q).comp (P t)

/-- Every centered forward orbit restarts on its actual centered early datum. -/
theorem IsComplexEnvironmentSemigroup.centered_orbit_add
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (s t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q (P (s + t) f) =
      centeredComplexLp Q (P t (centeredComplexLp Q (P s f))) := by
  rw [hP.centered_apply, add_comm s t, hP.2.1, ContinuousLinearMap.comp_apply]

/-- Exact restart for the actual forward velocity, including the affine
signed-force coefficient observation and the centering after evolution. -/
theorem IsComplexEnvironmentSemigroup.velocityEndpoint_add
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d) (s t : ℝ≥0) :
    velocityEndpoint Q i j ζ P β a (s + t) =
      centeredComplexLp Q (P t (velocityEndpoint Q i j ζ P β a s)) :=
  hP.centered_orbit_add s t (β j + ζ • a i j)

/-- The clock restarts with its external signed complex force retained. -/
theorem IsComplexEnvironmentSemigroup.clockEndpoint_add
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (s t : ℝ≥0) :
    clockEndpoint Q ζ P μ (s + t) =
      centeredComplexLp Q (P t (clockEndpoint Q ζ P μ s)) := by
  unfold clockEndpoint
  rw [hP.centered_orbit_add, map_smul]
  simpa only [centeredComplexLpCLM_apply] using
    ((centeredComplexLpCLM Q).map_smul ζ (P t (centeredComplexLp Q (P s μ)))).symm

/-- The transpose endpoint restarts without imposing any artificial centering
or identifying the transpose with the forward generator at negative force. -/
theorem IsComplexTransposeSemigroup.transposeEndpoint_add
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (s t : ℝ≥0) :
    transposeEndpoint Q i Pdag β (s + t) =
      Pdag t (transposeEndpoint Q i Pdag β s) := by
  rw [hPdag.eq_complexL2Transpose]
  unfold transposeEndpoint
  dsimp only
  rw [hP.2.1, complexL2Transpose_comp, ContinuousLinearMap.comp_apply]

/-- A single exact restart identity for all literal frozen endpoint indices. -/
theorem IsComplexEnvironmentSemigroup.indexedEndpoint_add
    (hd : 2 ≤ d) (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ν : EndpointIndex d) (s t : ℝ≥0) :
    indexedEndpoint hd Q ν ζ P Pdag β a μ (s + t) =
      lateEndpointEvolution Q ν P Pdag t
        (indexedEndpoint hd Q ν ζ P Pdag β a μ s) := by
  rcases ν with j | b
  · simpa only [indexedEndpoint, lateEndpointEvolution, ContinuousLinearMap.comp_apply,
      centeredComplexLpCLM_apply] using hP.velocityEndpoint_add β a j s t
  · cases b
    · simpa only [indexedEndpoint, lateEndpointEvolution, ContinuousLinearMap.comp_apply,
        centeredComplexLpCLM_apply] using hP.clockEndpoint_add μ s t
    · exact hPdag.transposeEndpoint_add hP β s t

/-- The explicit all-L2 Duhamel factor, with structural parameters only. -/
def lateForceReplacementFactor (d : ℕ) (Λ : ℝ) (ζ : ℂ) (t : ℝ≥0) : ℝ :=
  4 * ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) *
    Real.sqrt (Real.exp (2 * Λ) * Λ) * Real.sqrt (t : ℝ) *
      Real.exp (65 * complexForceShift d Λ ζ * t)

/-- Bilinear transposition transfers the genuine force perturbation bound to
every transpose datum. In particular, no negative-force forward identification
or assumed transpose regularity is required. -/
theorem IsComplexTransposeSemigroup.norm_sub_unforced_apply_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (hRdag : IsComplexTransposeSemigroup Q R Rdag)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖Pdag t f - Rdag t f‖ ≤ lateForceReplacementFactor d Λ ζ t * ‖f‖ := by
  rw [hPdag.eq_complexL2Transpose, hRdag.eq_complexL2Transpose]
  have he : complexL2Transpose (reducedLaw Q) (P t) -
      complexL2Transpose (reducedLaw Q) (R t) =
      complexL2Transpose (reducedLaw Q) (P t - R t) :=
    ((complexL2TransposeCLM (reducedLaw Q)).map_sub (P t) (R t)).symm
  change ‖(complexL2Transpose (reducedLaw Q) (P t) -
    complexL2Transpose (reducedLaw Q) (R t)) f‖ ≤ _
  rw [he]
  exact ((complexL2Transpose (reducedLaw Q) (P t - R t)).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right
      ((norm_complexL2Transpose (reducedLaw Q) _).le.trans
        (hP.opNorm_sub_unforced_le hR t)) (norm_nonneg f))

/-- Actual late evolution admits force replacement on every early datum.
The numerical projection bound is uniform over all reduced laws. -/
theorem IsComplexEnvironmentSemigroup.lateEndpointEvolution_force_replacement_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (hRdag : IsComplexTransposeSemigroup Q R Rdag)
    (ν : EndpointIndex d) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖lateEndpointEvolution Q ν P Pdag t f - lateEndpointEvolution Q ν R Rdag t f‖ ≤
      2 * lateForceReplacementFactor d Λ ζ t * ‖f‖ := by
  have hΛ : 0 ≤ Λ := zero_le_one.trans Q.ellipticity_parameter
  have hB : 0 ≤ lateForceReplacementFactor d Λ ζ t := by
    unfold lateForceReplacementFactor
    positivity
  have hfwd : ‖(centeredComplexLpCLM Q) (P t f) -
      (centeredComplexLpCLM Q) (R t f)‖ ≤
      2 * lateForceReplacementFactor d Λ ζ t * ‖f‖ := by
    rw [← map_sub]
    exact ((centeredComplexLpCLM Q).le_opNorm _).trans (by
      calc
        _ ≤ ‖centeredComplexLpCLM Q‖ * (lateForceReplacementFactor d Λ ζ t * ‖f‖) :=
          mul_le_mul_of_nonneg_left (hP.norm_sub_unforced_mild_le hR f t) (norm_nonneg _)
        _ ≤ 2 * lateForceReplacementFactor d Λ ζ t * ‖f‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (norm_centeredComplexLpCLM_le_two Q) (mul_nonneg hB (norm_nonneg f)))
  rcases ν with j | b
  · exact hfwd
  · cases b
    · exact hfwd
    · exact (hPdag.norm_sub_unforced_apply_le hP hR hRdag t f).trans (by
        calc
          _ = 1 * (lateForceReplacementFactor d Λ ζ t * ‖f‖) := (one_mul _).symm
          _ ≤ 2 *
              (lateForceReplacementFactor d Λ ζ t * ‖f‖) :=
            mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (mul_nonneg hB (norm_nonneg f))
          _ = _ := (mul_assoc _ _ _).symm)

/-- Force replacement on the actual remaining interval for all frozen endpoints.
The early datum is still at force ζ: no early flux replacement or scalar decay
estimate is hidden in this unconditional bound. -/
theorem IsComplexEnvironmentSemigroup.indexedEndpoint_late_force_replacement_le
    (hd : 2 ≤ d) (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hR : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 R)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (hRdag : IsComplexTransposeSemigroup Q R Rdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ν : EndpointIndex d) (s t : ℝ≥0) :
    ‖indexedEndpoint hd Q ν ζ P Pdag β a μ (s + t) -
        lateEndpointEvolution Q ν R Rdag t
          (indexedEndpoint hd Q ν ζ P Pdag β a μ s)‖ ≤
      2 * lateForceReplacementFactor d Λ ζ t *
        ‖indexedEndpoint hd Q ν ζ P Pdag β a μ s‖ := by
  rw [hP.indexedEndpoint_add hd hPdag β a μ ν s t]
  exact hP.lateEndpointEvolution_force_replacement_le hR hPdag hRdag ν t _

/-- Exact late-interval forward Duhamel term with centering and the early
centered datum. The signed complex force remains outside the Bochner integral. -/
theorem IsComplexEnvironmentSemigroup.centered_late_duhamel
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    (s t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q (P (s + t) f) -
        centeredComplexLp Q (R t (centeredComplexLp Q (P s f))) =
      ζ • centeredComplexLp Q
        (∫ u in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t - u))
          (complexForceDrift Q i (hP.gradientOrbit (centeredComplexLp Q (P s f)) u))) := by
  rw [hP.centered_orbit_add]
  simp_rw [← centeredComplexLpCLM_apply]
  rw [← map_sub, ← hP.integral_mild_force_drift hR, map_smul]

/-- The constructed physical evolution supplies every semigroup and transpose
premise internally. This is an all-environment force replacement estimate on
actual endpoints, without decay or homogenization assumptions. -/
theorem forcedComplexEvolution_indexedEndpoint_late_force_replacement_le
    (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ r) (ζ : ℂ)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ν : EndpointIndex d) (s t : ℝ≥0) :
    let first : Fin d := ⟨0, by omega⟩
    let P := forcedComplexEvolution Q first ζ
    let Pdag := fun u => complexL2Transpose (reducedLaw Q) (P u)
    let R := forcedComplexEvolution Q first 0
    let Rdag := fun u => complexL2Transpose (reducedLaw Q) (R u)
    ‖indexedEndpoint hd Q ν ζ P Pdag β a μ (s + t) -
        lateEndpointEvolution Q ν R Rdag t
          (indexedEndpoint hd Q ν ζ P Pdag β a μ s)‖ ≤
      2 * lateForceReplacementFactor d Λ ζ t *
        ‖indexedEndpoint hd Q ν ζ P Pdag β a μ s‖ := by
  dsimp only
  exact (isComplexEnvironmentSemigroup_forcedComplexEvolution Q ⟨0, by omega⟩ ζ).indexedEndpoint_late_force_replacement_le hd
      (isComplexEnvironmentSemigroup_forcedComplexEvolution Q ⟨0, by omega⟩ 0)
      (isComplexTransposeSemigroup_complexL2Transpose Q _)
      (isComplexTransposeSemigroup_complexL2Transpose Q _) β a μ ν s t

end EinsteinFull
