import EinsteinRelation.Correctors.StationaryScalarBallMoments

/-!
# Stationary flux-corrector moments on local balls

Source: `paper/main.tex:724-731`. In dimensions greater than two, the
stationary representative supplied by (6.14) has all radius-four L²
moments, uniformly over centers. All tensor norms are Frobenius norms.
-/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A nonnegative stationary density with a finite cell integral transfers
its root-integral moments to any radius-four ball. -/
theorem stationary_root_integral_ball_four_moment_le {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (hP : LawHypotheses P)
    (F : Coefficient d K → Vec d → ℝ)
    (hF : Measurable (Function.uncurry F)) (hpos : ∀ a x, 0 ≤ F a x)
    (hs : ScalarStationary P F)
    (hi : ∀ᵐ a ∂P, Integrable (F a) (volume.restrict (unitCell d)))
    (p : ℝ) (hp : 2 ≤ p) (B : ℝ≥0∞)
    (hb : (∫⁻ a, ENNReal.ofReal ((Real.sqrt
      (∫ x in unitCell d, F a x ∂volume)) ^ p) ∂P) ≤ B) (z : Vec d) :
    (∫⁻ a, ENNReal.ofReal ((Real.sqrt
      (∫ x in ball z 4, F a x ∂volume)) ^ p) ∂P) ≤
      ((11 ^ d : ℕ) : ℝ≥0∞) ^ (p / 2 - 1) * (((11 ^ d : ℕ) : ℝ≥0∞) * B) := by
  have heq (a : Coefficient d K) (μ : Measure (Vec d)) :
      ENNReal.ofReal ((Real.sqrt (∫ x, F a x ∂μ)) ^ p) =
        ENNReal.ofReal (∫ x, F a x ∂μ) ^ (p / 2) := by
    have hn : 0 ≤ ∫ x, F a x ∂μ := integral_nonneg fun x => hpos a x
    rw [ENNReal.ofReal_rpow_of_nonneg hn (by positivity),
      Real.rpow_div_two_eq_sqrt _ hn]
  let G := fun a x => ENNReal.ofReal (F a x)
  have hG : Measurable (Function.uncurry G) := hF.ennreal_ofReal
  have hGs : ∀ k : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G a (x + latticeShift k) = G (translateCoefficient (latticeShift k) a) x := by
    intro k
    filter_upwards [hs k] with a ha
    exact ha.mono fun x hx => congrArg ENNReal.ofReal hx
  have hcell : (∫⁻ a, (∫⁻ x in unitCell d, G a x ∂volume) ^ (p / 2) ∂P) ≤ B := by
    apply le_trans (le_of_eq ?_) hb
    apply lintegral_congr_ae
    filter_upwards [hi] with a ha
    rw [heq, ofReal_integral_eq_lintegral_ofReal ha (ae_of_all _ (hpos a))]
  apply le_trans ?_ (stationary_ball_four_lintegral_moment_le hP G hG hGs
    (p / 2) (by linarith) B hcell z)
  apply lintegral_mono
  intro a
  dsimp only
  rw [heq]
  by_cases hi' : Integrable (F a) (volume.restrict (ball z 4))
  · rw [ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ (hpos a))]
  · rw [integral_undef hi', ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (by linarith : 0 < p / 2)]
    exact bot_le

/-- The passed stationary source estimate (6.14) gives a flux potential
with all radius-four L² moments, uniformly over the ball center. -/
theorem akm_stationary_flux_ball_four_moments (h614 : FluxStationaryEstimate)
    (d : ℕ) (hd : 2 < d) (K p : ℝ) (hK : 1 < K) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
      ∀ (e : Vec d), euclideanNorm e = 1 → ∀ (φ : Corrector P e)
        (S : FluxCorrector φ), ∃ T : FluxCorrector φ,
          (∀ᵐ a ∂P, ∀ j k, T.grad a j k =ᵐ[volume] S.grad a j k) ∧
          (∀ j k, ScalarStationary P (fun a x => T.potential a x j k)) ∧
          (∀ j k, (∫ a, ⨍ x in unitCell d, T.potential a x j k ∂volume ∂P) = 0) ∧
          ∀ z : Vec d, (∫⁻ a, ENNReal.ofReal ((Real.sqrt
            (∫ x in ball z 4, frobeniusNorm (T.potential a x) ^ 2 ∂volume)) ^ p)
            ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀, hest⟩ := akm_stationary_flux_cell_moments h614 d hd K p hK
    (by linarith)
  let N : ℕ := 11 ^ d
  let C : ℝ := (N : ℝ) ^ (p / 2 - 1) * ((N : ℝ) * C₀)
  have hN : 0 < (N : ℝ) := by dsimp [N]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCeq : ENNReal.ofReal C = (N : ℝ≥0∞) ^ (p / 2 - 1) *
      ((N : ℝ≥0∞) * ENNReal.ofReal C₀) := by
    dsimp only [C]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (N : ℝ) ^ (p / 2 - 1)),
      ← ENNReal.ofReal_rpow_of_nonneg hN.le (by linarith : 0 ≤ p / 2 - 1),
      ENNReal.ofReal_mul hN.le]
    simp
  refine ⟨C, hC, ?_⟩
  intro P hP e he φ S
  obtain ⟨T, hg, hs, hz, hb⟩ := hest P hP e he φ S
  refine ⟨T, hg, hs, hz, ?_⟩
  let F := fun a x => frobeniusNorm (T.potential a x) ^ 2
  have hnorm (a : Coefficient d K) (x : Vec d) :
      F a x = ∑ j : Fin d, ∑ k : Fin d, (T.potential a x j k) ^ 2 := by
    dsimp [F, frobeniusNorm]
    rw [Real.sq_sqrt (frobeniusSq_nonneg _)]
    simp only [frobeniusSq, pow_two]
  have hF : Measurable (Function.uncurry F) := by
    simp_rw [Function.uncurry_def, hnorm]
    exact Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
      (((continuous_apply k).comp (continuous_apply j)).measurable.comp
        T.measurable_potential).pow_const 2
  have hFs : ScalarStationary P F := by
    intro z
    have h := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hs j k z
    filter_upwards [h] with a ha
    have hax := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => ha j k
    filter_upwards [hax] with x hx
    simp only [hnorm, hx]
  have hi : ∀ᵐ a ∂P, Integrable (F a) (volume.restrict (unitCell d)) := by
    filter_upwards [T.locally_square_integrable] with a ha
    simp only [show F a = (fun x => ∑ j : Fin d, ∑ k : Fin d, (T.potential a x j k) ^ 2)
      from funext (hnorm a)]
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
      (memLp_unitCell_of_euclidean_balls _ fun R hR => (ha R hR j k).1).integrable_sq
  have hb' : (∫⁻ a, ENNReal.ofReal ((Real.sqrt
      (∫ x in unitCell d, F a x ∂volume)) ^ p) ∂P) ≤ ENNReal.ofReal C₀ := by
    simpa only [average_eq, measureReal_def, Measure.restrict_apply_univ,
      volume_akm_unitCell, ENNReal.toReal_one, inv_one, one_smul] using hb
  intro z
  rw [hCeq]
  exact stationary_root_integral_ball_four_moment_le hP F hF
    (fun a x => sq_nonneg _) hFs hi p hp (ENNReal.ofReal C₀) hb' z

end EinsteinRelation.Correctors
