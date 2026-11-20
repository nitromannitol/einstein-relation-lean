import EinsteinFull.Homogenization.SourceGradientBlockStationarity
import EinsteinFull.Homogenization.SourceGradientVectorVariance

/-!
# Optimizer gradient deviations and variance

The mean-square deviation of a vector from a deterministic loading is bounded
by its variance and the deviation of its mean, as used in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- For a square-integrable finite vector, the expected squared deviation
from a deterministic vector is bounded by twice its variance plus twice the
squared deviation of its mean. -/
theorem integrable_and_integral_vecNormSq_sub_le_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (F : Ω → Vec d) (hF : ∀ i, MemLp (fun a => F a i) 2 P) (b : Vec d) :
    (∀ i, Integrable (fun a => F a i) P) ∧
    Integrable (fun a => vecNormSq (F a - b)) P ∧
    (∫ a, vecNormSq (F a - b) ∂P) ≤
      2 * (∑ i : Fin d, ProbabilityTheory.variance (fun a => F a i) P) +
      2 * vecNormSq ((fun i => ∫ a, F a i ∂P) - b) := by
  classical
  let m : Vec d := fun i => ∫ a, F a i ∂P
  have hmean := integrable_and_integral_vecNormSq_sub_mean_eq_sum_variance P F hF
  change (∀ i, Integrable (fun a => F a i) P) ∧
    Integrable (fun a => vecNormSq (F a - m)) P ∧
    (∫ a, vecNormSq (F a - m) ∂P) = _ at hmean
  have hsub : Integrable (fun a => vecNormSq (F a - b)) P := by
    have hi (i : Fin d) : Integrable (fun a => (F a i - b i) ^ 2) P :=
      ((hF i).sub (memLp_const (b i))).integrable_sq
    have hs := integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => hi i)
    simpa only [vecNormSq, vecDot, Pi.sub_apply, sq] using hs
  refine ⟨hmean.1, hsub, ?_⟩
  have hpoint (a : Ω) : vecNormSq (F a - b) ≤
      2 * vecNormSq (F a - m) + 2 * vecNormSq (m - b) := by
    have h := vecNormSq_add_le (F a - m) (m - b)
    simpa only [sub_add_sub_cancel, mul_add] using h
  calc
    _ ≤ ∫ a, 2 * vecNormSq (F a - m) + 2 * vecNormSq (m - b) ∂P :=
      integral_mono hsub ((hmean.2.1.const_mul 2).add (integrable_const _)) hpoint
    _ = 2 * (∫ a, vecNormSq (F a - m) ∂P) + 2 * vecNormSq (m - b) := by
      rw [integral_add (hmean.2.1.const_mul 2) (integrable_const _), integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
    _ = _ := by rw [hmean.2.2]

end EinsteinFull.Homogenization
