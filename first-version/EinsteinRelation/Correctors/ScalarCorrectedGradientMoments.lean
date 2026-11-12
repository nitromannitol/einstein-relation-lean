import EinsteinRelation.Correctors.ScalarCorrectedFunctionMoments

/-! # Coordinate moments of the corrected gradient

Source: `paper/main.tex:1077–1082`. The weak gradient used by the generator
identity is bounded using the two actual correction sums.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Each corrected gradient coordinate has a scale-independent moment
when `a ≤ 3r` (`paper/main.tex:1077–1082`). -/
theorem scalarCorrected_gradient_coordinate_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} {p r a A B : ℝ} (hp : 1 ≤ p) (hr : 1 ≤ r) (ha : 0 ≤ a)
    (har : a ≤ 3 * r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (Du : Ω → Vec d) (phi : Fin d → Ω → ℝ)
    (Dphi DDu : Fin d → Ω → Vec d)
    (hDu : Measurable Du)
    (hphi : ∀ j, Measurable (phi j)) (hDphi : ∀ j, Measurable (Dphi j))
    (hDDu : ∀ j, Measurable (DDu j))
    (hDub : ∀ i, eLpNorm (fun ω => Du ω i) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal B)
    (hphib : ∀ j, eLpNorm (phi j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A * a))
    (hDphib : ∀ j i, eLpNorm (fun ω => Dphi j ω i) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal A)
    (hDDub : ∀ j i, eLpNorm (fun ω => DDu j ω i) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (B / r)) :
    ∀ i, eLpNorm (fun ω => (Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • DDu j ω)) i)
      (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal (B + 4 * (d : ℝ) * A * B) := by
  intro i
  have hDum (j : Fin d) : Measurable (fun ω => Du ω j) := (measurable_pi_apply j).comp hDu
  have hDpm (j : Fin d) : Measurable (fun ω => Dphi j ω i) := (measurable_pi_apply i).comp (hDphi j)
  have hDDm (j : Fin d) : Measurable (fun ω => DDu j ω i) := (measurable_pi_apply i).comp (hDDu j)
  have hs := scalarCorrected_gradient_sums_moment μ hp hr ha har hA hB
    (fun j ω => Du ω j) (fun j ω => Dphi j ω i) phi (fun j ω => DDu j ω i)
    hDum hDpm hphi hDDm hDub (fun j => hDphib j i) hphib (fun j => hDDub j i)
  have hm : Measurable (fun ω => (∑ j, Du ω j * Dphi j ω i) + ∑ j, phi j ω * DDu j ω i) :=
    (Finset.measurable_sum _ fun j _ => (hDum j).mul (hDpm j)).add
      (Finset.measurable_sum _ fun j _ => (hphi j).mul (hDDm j))
  have heq : (fun ω => (Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • DDu j ω)) i) =
      fun ω => Du ω i + ((∑ j, Du ω j * Dphi j ω i) + ∑ j, phi j ω * DDu j ω i) := by
    funext ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [heq]
  apply (eLpNorm_add_le (hDum i).aestronglyMeasurable hm.aestronglyMeasurable
    (ENNReal.one_le_ofReal.mpr (by linarith))).trans
  have hqq : ENNReal.ofReal (2 * p) ≤ ENNReal.ofReal (4 * p) := ENNReal.ofReal_le_ofReal (by linarith)
  have hb := (eLpNorm_le_eLpNorm_of_exponent_le hqq (hDum i).aestronglyMeasurable).trans (hDub i)
  exact (add_le_add hb hs).trans_eq (ENNReal.ofReal_add hB (by positivity)).symm

end EinsteinRelation.Correctors
