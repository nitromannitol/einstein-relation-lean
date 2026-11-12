import EinsteinRelation.Correctors.ParabolicLargeScaleFlow
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # Spatial gradient integrability on an entire time tail

Source: `paper/main.tex:800–808`. Exhaustion by bounded positive-time
cylinders derives the time-slice energy membership from the semigroup
solution itself, with no additional decay or regularity hypothesis.
-/

open MeasureTheory Set

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual semigroup energy class supplies spatial `L²` slices on
the whole positive tail. Source: `paper/main.tex:800–808`. -/
theorem semigroupSolution_gradient_tail_slice_memLp
    {d : ℕ} {K : ℝ} {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) (hG : Measurable G)
    {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) :
    ∀ᵐ t ∂volume.restrict (Ioi T), MemLp (fun x => G (t,x)) 2
      (volume.restrict (originBall d ρ)) := by
  have hslice (n : ℕ) : ∀ᵐ t ∂volume,
      t ∈ Ioo (T/2) (T+(n : ℝ)+1) →
        MemLp (fun x => euclideanNorm (G (t,x))) 2 (volume.restrict (originBall d ρ)) := by
    apply (ae_restrict_iff' measurableSet_Ioo).mp
    exact parabolicSolution_gradient_slice_memLp
      (hsol.2.1 (T/2) (T+(n : ℝ)+1) ρ (by linarith)
        (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hρ)
  have hnorm : ∀ᵐ t ∂volume.restrict (Ioi T),
      MemLp (fun x => euclideanNorm (G (t,x))) 2 (volume.restrict (originBall d ρ)) := by
    filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr hslice),
      ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht htT
    obtain ⟨n,hn⟩ := exists_nat_gt t
    exact ht n ⟨by have : T < t := htT; linarith, by linarith⟩
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  filter_upwards [hnorm] with t ht
  have hjm : AEStronglyMeasurable (fun x => J (G (t,x)))
      (volume.restrict (originBall d ρ)) :=
    (J.continuous.measurable.comp
      (hG.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have hj : MemLp (fun x => J (G (t,x))) 2 (volume.restrict (originBall d ρ)) :=
    ht.mono' hjm (ae_of_all _ fun x => by
      change ‖WithLp.toLp 2 (G (t,x))‖ ≤ euclideanNorm (G (t,x))
      rw [TimeChange.euclideanNorm_eq_norm_toLp])
  have hv := J.symm.toContinuousLinearMap.comp_memLp' hj
  simpa only [Function.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using hv

end EinsteinRelation.Correctors
