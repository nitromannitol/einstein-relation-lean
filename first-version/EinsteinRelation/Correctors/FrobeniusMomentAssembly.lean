import EinsteinRelation.Correctors.FrobeniusPowerBound
import EinsteinRelation.Environment.MatrixNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Entrywise assembly of the flux moment in `paper/main.tex:714-716`. -/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- Entrywise stochastic or spatial moments control the Euclidean tensor
moment, with the dimension factor required by the power mean inequality. -/
theorem lintegral_frobeniusNorm_rpow_le_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ} (hd : 0 < d)
    (A : Ω → Mat d) (hA : Measurable A) (m : ℝ) (hm : 2 ≤ m) :
    (∫⁻ ω, ENNReal.ofReal (frobeniusNorm (A ω) ^ m) ∂μ) ≤
      ENNReal.ofReal ((d : ℝ) ^ (m - 2)) *
        ∑ j : Fin d, ∑ k : Fin d,
          ∫⁻ ω, ENNReal.ofReal (|A ω j k| ^ m) ∂μ := by
  have hn : 0 ≤ (d : ℝ) ^ (m - 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmeas (j k : Fin d) :
      Measurable (fun ω => ENNReal.ofReal (|A ω j k| ^ m)) := by
    have hec : Continuous (fun M : Mat d => M j k) :=
      (continuous_apply k).comp (continuous_apply j)
    have he : Measurable (fun ω => A ω j k) :=
      hec.measurable.comp hA
    exact ((Real.continuous_rpow_const (by linarith : 0 ≤ m)).measurable.comp
      (continuous_abs.measurable.comp he)).ennreal_ofReal
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((d : ℝ) ^ (m - 2) *
        ∑ j : Fin d, ∑ k : Fin d, |A ω j k| ^ m) ∂μ :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
        (frobeniusNorm_rpow_le_sum hd (A ω) m hm)
    _ = ∫⁻ ω, ENNReal.ofReal ((d : ℝ) ^ (m - 2)) *
        ∑ j : Fin d, ∑ k : Fin d, ENNReal.ofReal (|A ω j k| ^ m) ∂μ := by
      congr 1
      funext ω
      rw [ENNReal.ofReal_mul hn]
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
        Finset.sum_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _)]
      congr 1
      funext j
      exact ENNReal.ofReal_sum_of_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _
    _ = ENNReal.ofReal ((d : ℝ) ^ (m - 2)) *
        ∫⁻ ω, ∑ j : Fin d, ∑ k : Fin d,
          ENNReal.ofReal (|A ω j k| ^ m) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      congr 1
      rw [lintegral_finset_sum Finset.univ (fun j _ =>
        Finset.measurable_sum _ (fun k _ => hmeas j k))]
      apply Finset.sum_congr rfl
      intro j _
      exact lintegral_finset_sum Finset.univ (fun k _ => hmeas j k)

end EinsteinRelation.Correctors

