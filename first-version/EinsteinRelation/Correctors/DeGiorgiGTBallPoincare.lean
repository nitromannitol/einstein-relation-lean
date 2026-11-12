import Mathlib
import EinsteinRelation.External.GilbargTrudinger
import EinsteinRelation.Correctors.DeGiorgiBallPreimage
import EinsteinRelation.Correctors.DeGiorgiBallPoincare
import EinsteinRelation.Correctors.DeGiorgiSobolevWitness
import EinsteinRelation.Correctors.PoincareLeftSideTransport
import EinsteinRelation.Correctors.PoincareRightSideTransport
open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-! # Gilbarg–Trudinger ball Poincaré estimate from the De Giorgi ball inequality

The coordinate ball `External.AKM.ball y R` is the preimage of the Euclidean ball
`Metric.ball (toLp y) R` under `WithLp.ofLp`. The De Giorgi Poincaré inequality on Euclidean
balls, applied to the Euclidean witness of a repository weak gradient, transports back to the
coordinate ball with the same constant `DeGiorgi.C_poinc_val d`.
-/

/-- The De Giorgi Poincaré inequality for a `W^{1,2}` witness on a set `Ω` that equals the
Euclidean ball `Metric.ball x₀ R`. -/
private lemma poincare_of_set_eq {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R) (hΩ : Ω = Metric.ball x₀ R)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u Ω) :
    eLpNorm (fun x => u x - ⨍ y in Ω, u y ∂volume) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (DeGiorgi.C_poinc_val d * R) *
        eLpNorm (fun x => ‖hw.weakGrad x‖) 2 (volume.restrict Ω) := by
  subst hΩ
  exact poincare_ball_W1p hR hw

/-- The `L²` oscillation of a weak gradient on a coordinate ball is bounded by
`C_poinc_val d * R` times the `L²` norm of the gradient. -/
private lemma ballPoincare_of_hasWeakGradient {d : ℕ} [NeZero d] {y : Vec d} {R : ℝ}
    (hR : 0 < R) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (External.AKM.ball y R)))
    (hg : MemLp g 2 (volume.restrict (External.AKM.ball y R)))
    (h : HasWeakGradient (External.AKM.ball y R) u g) :
    Real.sqrt (∫ x in External.AKM.ball y R,
        |u x - ⨍ z in External.AKM.ball y R, u z ∂volume| ^ 2 ∂volume) ≤
      DeGiorgi.C_poinc_val d * R *
        Real.sqrt (∫ x in External.AKM.ball y R, euclideanSq (g x) ∂volume) := by
  have hU : volume (External.AKM.ball y R) ≠ ∞ := by
    have he : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
      (MeasurableEquiv.toLp 2 (Vec d)).symm.measurableEmbedding
    rw [← (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage_emb he
      (External.AKM.ball y R), preimage_ofLp_ball]
    exact measure_ball_lt_top.ne
  obtain ⟨hw, hwG⟩ := exists_memW1pWitness_of_hasWeakGradient hu hg h
  have hP := poincare_of_set_eq hR (preimage_ofLp_ball y R) hw
  rw [hwG, eLpNorm_sub_setAverage_comp_ofLp hU hu, eLpNorm_norm_toLp_comp_ofLp hg] at hP
  have hC : 0 < DeGiorgi.C_poinc_val d :=
    DeGiorgi.C_poinc_val_pos (Nat.pos_of_ne_zero (NeZero.ne d))
  have hnn : 0 ≤ DeGiorgi.C_poinc_val d * R *
      Real.sqrt (∫ x in External.AKM.ball y R, euclideanSq (g x) ∂volume) :=
    mul_nonneg (mul_nonneg hC.le hR.le) (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_mul (mul_nonneg hC.le hR.le)] at hP
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 hP

/-- The Gilbarg–Trudinger ball Poincaré estimate, with constant `DeGiorgi.C_poinc_val d`
for every dimension `d ≥ 2`. -/
theorem ballPoincareEstimate_of_deGiorgi :
    External.GilbargTrudinger.BallPoincareEstimate := by
  unfold External.GilbargTrudinger.BallPoincareEstimate
  intro d hd
  haveI : NeZero d := ⟨by omega⟩
  exact ⟨DeGiorgi.C_poinc_val d, DeGiorgi.C_poinc_val_pos (by omega),
    fun y R hR u g hu hg h => ballPoincare_of_hasWeakGradient hR hu hg h⟩

end EinsteinRelation.Correctors
