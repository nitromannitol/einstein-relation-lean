import Mathlib
import EinsteinRelation.Environment.Basic

/-! # Transport of the left side of the Poincaré inequality to the Euclidean space

The coordinate map `WithLp.ofLp` carries Lebesgue measure on the Euclidean space to Lebesgue
measure on the coordinate space and maps the restricted measure on a Euclidean preimage onto
the restricted measure on the set. Consequently the `L²` norm of `u ∘ ofLp` minus its average
over the preimage is the `L²` norm of `u` minus its average over the set.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

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

/-- The `L²` norm of the Euclidean-coordinate function `u ∘ WithLp.ofLp` minus its average over
the Euclidean preimage of `U` equals the `L²` norm of `u` minus its average over `U`, for a set
`U` of finite Lebesgue measure. The average over the preimage is the average over `U`, and the
square root of the integral of the squared deviation is taken over `U`. -/
theorem eLpNorm_sub_setAverage_comp_ofLp {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hU : volume U ≠ ∞) (hu : MemLp u 2 (volume.restrict U)) :
    eLpNorm (fun x : EuclideanSpace ℝ (Fin d) => u (WithLp.ofLp x) -
        ⨍ y in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U, u (WithLp.ofLp y))
        2 (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U)) =
      ENNReal.ofReal (Real.sqrt (∫ x in U, |u x - ⨍ z in U, u z ∂volume| ^ 2 ∂volume)) := by
  have he : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
    (MeasurableEquiv.toLp 2 (Vec d)).symm.measurableEmbedding
  have hvol : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) volume volume :=
    PiLp.volume_preserving_ofLp (Fin d)
  have hfin : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU
  have hmeas : volume.real ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U) =
      volume.real U := by
    rw [measureReal_def, measureReal_def, hvol.measure_preimage_emb he U]
  have havg : ⨍ y in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U, u (WithLp.ofLp y) =
      ⨍ z in U, u z := by
    rw [setAverage_eq, setAverage_eq, hmeas, hvol.setIntegral_preimage_emb he u U]
  rw [havg]
  have hG : MemLp (fun z => u z - ⨍ w in U, u w) 2 (volume.restrict U) :=
    hu.sub (memLp_const (⨍ w in U, u w))
  have hres : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d)
      (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U))
      (volume.restrict U) :=
    hvol.restrict_preimage_emb he U
  refine (eLpNorm_comp_measurePreserving hG.aestronglyMeasurable hres).trans ?_
  rw [eLpNorm_two_eq_ofReal_sqrt_integral_sq hG]
  simp only [sq_abs]

end EinsteinRelation.Correctors
