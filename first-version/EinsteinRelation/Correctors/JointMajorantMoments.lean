import EinsteinRelation.Correctors.TwoMajorantMoments
import EinsteinRelation.Correctors.AffineProbabilityMoment
open MeasureTheory
namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:727-745`. Two measurable local amplitudes
and the deterministic source term have a uniform annealed moment. -/
theorem lintegral_one_add_two_majorants_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : Ω → ℝ) (K p B D : ℝ) (hK : 0 ≤ K) (hp : 0 < p)
    (ha : ∀ ω, 0 ≤ a ω) (hb : ∀ ω, 0 ≤ b ω)
    (ham : AEMeasurable a P) (hbm : AEMeasurable b P)
    (hB : (∫⁻ ω, ENNReal.ofReal (a ω ^ p) ∂P) ≤ ENNReal.ofReal B)
    (hD : (∫⁻ ω, ENNReal.ofReal (b ω ^ p) ∂P) ≤ ENNReal.ofReal D) :
    (∫⁻ ω, ENNReal.ofReal ((K * (1 + a ω + b ω)) ^ p) ∂P) ≤
      ENNReal.ofReal (2 ^ p * K ^ p * (2 ^ p * (max B 0 + max D 0) + 1)) := by
  have hs := lintegral_rpow_le_of_two_majorants P (fun ω => a ω + b ω)
    a b 1 p B D (by norm_num) hp.le ha hb ham hbm
    (ae_of_all _ fun ω => ⟨add_nonneg (ha ω) (hb ω), by simp⟩) hB hD
  simp only [Real.one_rpow, one_mul] at hs
  have h := lintegral_nonneg_affine_rpow_le P (fun ω => a ω + b ω)
    hK hK hp (fun ω => add_nonneg (ha ω) (hb ω)) hs
  have hconst :
      ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal (K ^ p) * ENNReal.ofReal (2 ^ p * (max B 0 + max D 0)) +
          ENNReal.ofReal (K ^ p)) =
      ENNReal.ofReal (2 ^ p * K ^ p * (2 ^ p * (max B 0 + max D 0) + 1)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hK _),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hconst] at h
  convert h using 1
  congr 1
  funext ω
  congr 1
  congr 1
  ring
end EinsteinRelation.Correctors
