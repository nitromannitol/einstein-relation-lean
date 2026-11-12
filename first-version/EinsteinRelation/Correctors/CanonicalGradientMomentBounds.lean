import EinsteinRelation.Mobility.VelocityResolventRate
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Uniform norm bounds from Lemma 5.1

Source: `paper/main.tex:710–719,1077–1082`. The power-moment statement
of Lemma 5.1 supplies a norm constant before the environment law.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Lemma 5.1 as an explicit uniform `L^m` norm bound for the actual
canonical gradient at the origin (`paper/main.tex:710–719`). -/
theorem exists_canonicalGradient_moment_bound (H51 : CorrectorGradientMoments)
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) {m : ℝ} (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d),
      eLpNorm (fun ω => euclideanNorm
        (StationarySpatialRealization.spatialRealization (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          ((0 : Vec d), ω)).ofLp) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := H51 d hd Λ₀ r₀ m hm
  have hm0 : 0 < m := by linarith
  let D : ℝ≥0∞ := (ENNReal.ofReal C) ^ (1 / m)
  have hDt : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  refine ⟨D.toReal, ENNReal.toReal_nonneg, fun Q i => ?_⟩
  rw [ENNReal.ofReal_toReal hDt]
  rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.mpr hm0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hm0.le]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  convert hC Q i using 1
  apply lintegral_congr
  intro ω
  have hn : 0 ≤ euclideanNorm
      (StationarySpatialRealization.spatialRealization (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ((0 : Vec d), ω)).ofLp :=
    Real.sqrt_nonneg _
  rw [Real.enorm_of_nonneg hn, ENNReal.ofReal_rpow_of_nonneg hn hm0.le]

/-- The local gradient inherits a uniform norm bound from its canonical
counterpart and the refined error (`paper/main.tex:1077–1082`). -/
theorem eLpNorm_localGradient_le_of_error
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 1 ≤ r)
    {G V : Ω → Vec d} (hG : Measurable G) (hV : Measurable V)
    (hGb : eLpNorm (fun ω => euclideanNorm (G ω)) p μ ≤ ENNReal.ofReal A)
    (hVb : eLpNorm (fun ω => euclideanNorm (V ω - G ω)) p μ ≤ ENNReal.ofReal (B * r⁻¹)) :
    eLpNorm (fun ω => euclideanNorm (V ω)) p μ ≤ ENNReal.ofReal (A + B) := by
  have hn : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  calc
    _ ≤ eLpNorm (fun ω => euclideanNorm (G ω) + euclideanNorm (V ω - G ω)) p μ := by
      apply eLpNorm_mono_real
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ euclideanNorm (V ω) from Real.sqrt_nonneg _)]
      have he : G ω + (V ω - G ω) = V ω := by abel
      simpa only [he] using TimeChange.euclideanNorm_add_le (G ω) (V ω - G ω)
    _ ≤ eLpNorm (fun ω => euclideanNorm (G ω)) p μ +
        eLpNorm (fun ω => euclideanNorm (V ω - G ω)) p μ :=
      eLpNorm_add_le (hn.measurable.comp hG).aestronglyMeasurable
        (hn.measurable.comp (hV.sub hG)).aestronglyMeasurable hp
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal (B * r⁻¹) := add_le_add hGb hVb
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal B := by
      gcongr
      exact mul_le_of_le_one_right hB (inv_le_one_of_one_le₀ hr)
    _ = _ := (ENNReal.ofReal_add hA hB).symm

end EinsteinRelation.Correctors
