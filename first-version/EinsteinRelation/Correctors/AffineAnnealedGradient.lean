import EinsteinRelation.Correctors.GTAffineLocalGradient
import EinsteinRelation.Correctors.AffineProbabilityMoment
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger
/-- Source: `paper/main.tex:727-731`. Scalar local oscillation moments
control the actual affine gradient on the interior unit ball. -/
theorem affine_annealed_local_gradient_moment_of_GT
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) (hd : 2 ≤ d) (lam Λ K α p : ℝ)
    (hlam : 0 < lam) (hΛ : 0 < Λ) (hK : 0 < K)
    (hα : 0 < α) (hα1 : α < 1) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (a : Ω → Vec d → Mat d)
      (u : Ω → Vec d → ℝ) (g : Ω → Vec d → Vec d) (c : Ω → ℝ)
      (i : Fin d) (B : ℝ),
      (∀ᵐ ω ∂P, EllipticBound (ball 0 4) (a ω) lam Λ ∧
        (∀ j k, HolderBound (ball 0 4) α (fun x => a ω x j k) K) ∧
        MemLp (fun x => u ω x - c ω) 2 (volume.restrict (ball 0 4)) ∧
        WeakSolution (ball 0 4) (a ω)
          (fun x => x i + u ω x - c ω) (fun x => unitVector i + g ω x)) →
      (∫⁻ ω, ENNReal.ofReal ((Real.sqrt
        (∫ x in ball 0 4, |u ω x - c ω| ^ 2 ∂volume)) ^ p) ∂P) ≤ ENNReal.ofReal B →
      (∫⁻ ω, ∫⁻ x in ball (0 : Vec d) 1,
        ENNReal.ofReal ((euclideanNorm (unitVector i + g ω x)) ^ p) ∂volume ∂P) ≤
          volume (ball (0 : Vec d) 1) * ENNReal.ofReal (C * (max B 0 + 1)) := by
  obtain ⟨A, hA, hlocal⟩ := scalar_corrector_affine_local_gradient_bound_of_GT
    h817 h832 h836 d hd lam Λ K α hlam hΛ hK hα hα1
  refine ⟨A ^ p * 2 ^ p, by positivity, ?_⟩
  intro Ω _ P _ a u g c i B hweak hB
  let S : Ω → ℝ := fun ω => Real.sqrt
    (∫ x in ball 0 4, |u ω x - c ω| ^ 2 ∂volume)
  have hS : ∀ ω, 0 ≤ S ω := fun _ => Real.sqrt_nonneg _
  have hAp : 0 ≤ A ^ p := Real.rpow_nonneg hA.le _
  have h2p : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
  have hmax : 0 ≤ max B 0 := le_max_right _ _
  have hprob := lintegral_nonneg_affine_rpow_le P S hA.le hA.le hp hS
    (hB.trans (ENNReal.ofReal_le_ofReal (le_max_left B 0)))
  have hmoment : (∫⁻ ω, ENNReal.ofReal ((A * (1 + S ω)) ^ p) ∂P) ≤
      ENNReal.ofReal (A ^ p * 2 ^ p * (max B 0 + 1)) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal ((A * S ω + A) ^ p) ∂P := by
        apply lintegral_congr
        intro ω
        congr 2
        ring
      _ ≤ _ := hprob
      _ = _ := by
        rw [← ENNReal.ofReal_mul hAp,
          ← ENNReal.ofReal_add (mul_nonneg hAp hmax) hAp,
          ← ENNReal.ofReal_mul h2p]
        congr 1
        ring
  have hvol : volume (ball (0 : Vec d) 1) ≠ ⊤ :=
    (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d 1 (by norm_num))).2.ne
  calc
    _ ≤ ∫⁻ ω, volume (ball (0 : Vec d) 1) *
        ENNReal.ofReal ((A * (1 + S ω)) ^ p) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hweak] with ω hw
      calc
        _ ≤ ∫⁻ _ in ball (0 : Vec d) 1,
            ENNReal.ofReal ((A * (1 + S ω)) ^ p) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [hlocal (a ω) hw.1 hw.2.1 (u ω) (g ω) i (c ω)
            hw.2.2.1 hw.2.2.2] with x hx
          exact ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow (Real.sqrt_nonneg _) hx hp.le)
        _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    _ = volume (ball (0 : Vec d) 1) *
        (∫⁻ ω, ENNReal.ofReal ((A * (1 + S ω)) ^ p) ∂P) := by
      rw [lintegral_const_mul' _ _ hvol]
    _ ≤ _ := mul_le_mul_right hmoment _

end EinsteinRelation.Correctors
