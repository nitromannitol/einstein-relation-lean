import EinsteinRelation.Correctors.StationaryCellCovers
import EinsteinRelation.Correctors.SpatialBallLocalL2
import EinsteinRelation.Correctors.AKMStationaryCellMoments
import EinsteinRelation.Correctors.StationaryWeightedIntegrals

/-!
# Stationary scalar cell moments on arbitrary local balls

Source: `paper/main.tex:724-731,735-739`. A finite lattice-cell cover
transfers the high-dimensional scalar source estimate to the actual
local L² norm on a radius-four ball at any center. The weak corrector's
local L² membership makes the cell Bochner integrals genuine integrals.
No spatial Lᵖ upgrade is asserted here.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A raw scalar potential locally in L² on all origin balls is in L²
on the centered unit cell. -/
theorem memLp_unitCell_of_euclidean_balls {d : ℕ} (u : Vec d → ℝ)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) :
    MemLp u 2 (volume.restrict (unitCell d)) := by
  apply (memLp_on_compacts_of_euclidean_balls u hu
    (Metric.closedBall 0 1) (isCompact_closedBall _ _)).mono_measure
  apply Measure.restrict_mono_set
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  rw [Real.norm_eq_abs, abs_le]
  have hj := hx j (Set.mem_univ j)
  constructor <;> linarith [hj.1, hj.2]

private theorem ofReal_sqrt_integral_sq_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (p : ℝ) (hp : 0 ≤ p) :
    ENNReal.ofReal ((Real.sqrt (∫ x, |u x| ^ 2 ∂μ)) ^ p) =
      (ENNReal.ofReal (∫ x, |u x| ^ 2 ∂μ)) ^ (p / 2) := by
  have hn : 0 ≤ ∫ x, |u x| ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  rw [ENNReal.ofReal_rpow_of_nonneg hn (by positivity),
    Real.rpow_div_two_eq_sqrt _ hn]

/-- Stationary scalar cell L² moments control local L² moments uniformly
over the ball center. Only the cell needs an explicit integrability
hypothesis for this inequality. -/
theorem stationary_scalar_ball_four_L2_moment_le {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (hP : LawHypotheses P)
    (u : Coefficient d K → Vec d → ℝ)
    (hu : Measurable (Function.uncurry u)) (hs : ScalarStationary P u)
    (hL2 : ∀ᵐ a ∂P, MemLp (u a) 2 (volume.restrict (unitCell d)))
    (p : ℝ) (hp : 2 ≤ p) (B : ℝ≥0∞)
    (hb : (∫⁻ a, ENNReal.ofReal ((Real.sqrt
      (∫ x in unitCell d, |u a x| ^ 2 ∂volume)) ^ p) ∂P) ≤ B)
    (z : Vec d) :
    (∫⁻ a, ENNReal.ofReal ((Real.sqrt
      (∫ x in ball z 4, |u a x| ^ 2 ∂volume)) ^ p) ∂P) ≤
      ((11 ^ d : ℕ) : ℝ≥0∞) ^ (p / 2 - 1) * (((11 ^ d : ℕ) : ℝ≥0∞) * B) := by
  have hp0 : 0 < p := by linarith
  let F (a : Coefficient d K) (x : Vec d) := ENNReal.ofReal (|u a x| ^ 2)
  have hF : Measurable (Function.uncurry F) := ((continuous_abs.measurable.comp hu).pow_const 2).ennreal_ofReal
  have hFs : ∀ k : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      F a (x + latticeShift k) = F (translateCoefficient (latticeShift k) a) x := by
    intro k
    filter_upwards [hs k] with a ha
    filter_upwards [ha] with x hx
    simp only [F, hx]
  have hcell : (∫⁻ a, (∫⁻ x in unitCell d, F a x ∂volume) ^ (p / 2) ∂P) ≤ B := by
    calc
      _ = ∫⁻ a, ENNReal.ofReal ((Real.sqrt
          (∫ x in unitCell d, |u a x| ^ 2 ∂volume)) ^ p) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hL2] with a ha
        have hi : Integrable (fun x => |u a x| ^ 2)
            (volume.restrict (unitCell d)) := by simpa only [sq_abs] using ha.integrable_sq
        rw [ofReal_sqrt_integral_sq_rpow _ _ p hp0.le,
          ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
      _ ≤ B := hb
  apply le_trans ?_ (stationary_ball_four_lintegral_moment_le hP F hF hFs
    (p / 2) (by linarith) B hcell z)
  apply lintegral_mono
  intro a
  dsimp only
  rw [ofReal_sqrt_integral_sq_rpow _ _ p hp0.le]
  by_cases hi : Integrable (fun x => |u a x| ^ 2) (volume.restrict (ball z 4))
  · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
  · rw [integral_undef hi, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (by positivity : 0 < p / 2)]
    exact bot_le

/-- The passed AKM (4.5) estimate gives an actual stationary scalar
representative with all radius-four L² moments, uniformly in the center.
The constant precedes the law, the direction, and the original corrector. -/
theorem akm_stationary_scalar_ball_four_moments (h45 : ScalarStationaryEstimate)
    (d : ℕ) (hd : 2 < d) (K p : ℝ) (hK : 1 < K) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
      ∀ (e : Vec d), euclideanNorm e < 1 → ∀ (φ : Corrector P e),
        ∃ ψ : Corrector P e,
          Measurable (fun q : Coefficient d K × Vec d => ψ.potential q.1 q.2) ∧
          (∀ᵐ a ∂P, ψ.grad a =ᵐ[volume] φ.grad a) ∧
          ScalarStationary P ψ.potential ∧
          ∀ z : Vec d, (∫⁻ a, ENNReal.ofReal ((Real.sqrt
            (∫ x in ball z 4, |ψ.potential a x| ^ 2 ∂volume)) ^ p) ∂P) ≤
              ENNReal.ofReal C := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C₀, hC₀, hest⟩ := akm_stationary_scalar_cell_moments h45 d hd K p hK hp0
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
  intro P hP e he φ
  obtain ⟨ψ, hm, hg, hs, _, hb⟩ := hest P hP e he φ
  refine ⟨ψ, hm, hg, hs, ?_⟩
  have hcell : ∀ᵐ a ∂P, MemLp (ψ.potential a) 2 (volume.restrict (unitCell d)) := by
    filter_upwards [ψ.locally_square_integrable] with a ha
    exact memLp_unitCell_of_euclidean_balls _ fun R hR => (ha R hR).1
  have hb' : (∫⁻ a, ENNReal.ofReal ((Real.sqrt
      (∫ x in unitCell d, |ψ.potential a x| ^ 2 ∂volume)) ^ p) ∂P) ≤ ENNReal.ofReal C₀ := by
    simpa only [average_eq, measureReal_def, Measure.restrict_apply_univ,
      volume_akm_unitCell, ENNReal.toReal_one, inv_one, one_smul] using hb
  intro z
  rw [hCeq]
  exact stationary_scalar_ball_four_L2_moment_le hP ψ.potential hm hs hcell p hp
    (ENNReal.ofReal C₀) hb' z

end EinsteinRelation.Correctors

