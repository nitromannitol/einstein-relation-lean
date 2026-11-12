import Mathlib
import EinsteinRelation.Environment.Basic
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Transport of the Euclidean `L²` norm of a right-hand side

The coordinate map `WithLp.ofLp` carries Lebesgue measure on the Euclidean space to Lebesgue
measure on the coordinate space, so `L²` norms on a set and on its Euclidean preimage agree.
For a coordinate-valued `g`, the Euclidean norm of `g` is in `L²` exactly when `g` is, and its
`L²` norm is the square root of the integral of `euclideanSq ∘ g`.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- The squared norm of a vector transported to the Euclidean space is `euclideanSq`. -/
private lemma norm_toLp_sq_eq {d : ℕ} (v : Vec d) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 = euclideanSq v := by
  have hsq : 0 ≤ euclideanSq v := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  rw [← TimeChange.euclideanNorm_eq_norm_toLp]
  unfold euclideanNorm
  exact Real.sq_sqrt hsq

/-- For a real function in `L²`, the `L²` norm is the square root of the integral of the square. -/
private lemma eLpNorm_two_eq_ofReal_sqrt_integral_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by
  have e : ∫ x, ‖f x‖ ^ (2 : ℝ≥0∞).toReal ∂μ = ∫ x, f x ^ 2 ∂μ :=
    integral_congr_ae (ae_of_all _ fun x => by
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])
  have hexp : ((2 : ℝ≥0∞).toReal)⁻¹ = 1 / (2 : ℝ) := by norm_num
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, e, hexp,
    Real.sqrt_eq_rpow]

/-- The `L²` norm of `G ∘ WithLp.ofLp` on the Euclidean preimage of `U` is the `L²` norm of `G`
on `U`, because `WithLp.ofLp` pushes the restricted measure forward to the restricted measure. -/
private lemma eLpNorm_comp_ofLp_restrict {d : ℕ} {U : Set (Vec d)} {G : Vec d → ℝ}
    (hG : AEStronglyMeasurable G (volume.restrict U)) :
    eLpNorm (fun x : EuclideanSpace ℝ (Fin d) => G (WithLp.ofLp x)) 2
        (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U)) =
      eLpNorm G 2 (volume.restrict U) := by
  have he : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
    (MeasurableEquiv.toLp 2 (Vec d)).symm.measurableEmbedding
  have hmap : Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d)
      (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U)) =
        volume.restrict U :=
    ((PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage_emb he U).map_eq
  have hG' : AEStronglyMeasurable G
      (Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d)
        (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U))) := by
    rw [hmap]
    exact hG
  have key : eLpNorm G 2 (Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d)
        (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U))) =
      eLpNorm (fun x : EuclideanSpace ℝ (Fin d) => G (WithLp.ofLp x)) 2
        (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U)) :=
    eLpNorm_map_measure hG' he.measurable.aemeasurable
  rw [hmap] at key
  exact key.symm

/-- Transport of an `L²` norm to the Euclidean preimage, for the right-hand side `g`.
The Euclidean norm of the transported vector is the square root of `euclideanSq`. -/
theorem eLpNorm_norm_toLp_comp_ofLp {d : ℕ} {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemLp g 2 (volume.restrict U)) :
    eLpNorm (fun x : EuclideanSpace ℝ (Fin d) =>
        ‖(WithLp.toLp 2 (g (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin d))‖) 2
        (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U)) =
      ENNReal.ofReal (Real.sqrt (∫ x in U, euclideanSq (g x) ∂volume)) := by
  have hE : MemLp (fun y : Vec d => (WithLp.toLp 2 (g y) : EuclideanSpace ℝ (Fin d)))
      2 (volume.restrict U) := by
    refine memLp_piLp_iff.mpr fun i => ?_
    exact memLp_pi_iff.mp hg i
  have hG : MemLp (fun y : Vec d => ‖(WithLp.toLp 2 (g y) : EuclideanSpace ℝ (Fin d))‖)
      2 (volume.restrict U) :=
    hE.norm
  have hint : ∫ x, ‖(WithLp.toLp 2 (g x) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ∂(volume.restrict U) =
      ∫ x in U, euclideanSq (g x) ∂volume :=
    integral_congr_ae (ae_of_all _ fun x => norm_toLp_sq_eq (g x))
  refine (eLpNorm_comp_ofLp_restrict hG.aestronglyMeasurable).trans ?_
  rw [eLpNorm_two_eq_ofReal_sqrt_integral_sq hG, hint]

end EinsteinRelation.Correctors
