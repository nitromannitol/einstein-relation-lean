import EinsteinRelation.Correctors.PrescribedTimeGradientRecovery
import EinsteinRelation.Correctors.EuclideanRmsNorm

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- Recover a genuine gradient of the scalar limit from uniform actual gradient
energies. Source: `paper/main.tex:798–806`; removal of temporal smoothing. -/
theorem weakGradient_of_test_pairing_limit {d : ℕ}
    (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)]
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (v : ℕ → Vec d → ℝ) (G : ℕ → Vec d → Vec d)
    (hw : ∀ k, HasWeakGradient U (v k) (G k))
    (hG : ∀ k, MemLp (fun x => euclideanNorm (G k x)) 2 (volume.restrict U))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k, (eLpNorm (fun x => euclideanNorm (G k x)) 2
      (volume.restrict U)).toReal ≤ B)
    (hlim : ∀ i ψ, IsSpatialTest U ψ →
      Tendsto (fun k => ∫ x in U, v k x * coordinateDerivative i ψ x)
        atTop (𝓝 (∫ x in U, u x * coordinateDerivative i ψ x))) :
    ∃ H : Vec d → Vec d, HasWeakGradient U u H ∧
      MemLp (fun x => euclideanNorm (H x)) 2 (volume.restrict U) ∧
      (eLpNorm (fun x => euclideanNorm (H x)) 2 (volume.restrict U)).toReal ≤
        Real.sqrt d * B := by
  have htest i ψ (hψ : IsSpatialTest U ψ) :
      |∫ x in U, u x * coordinateDerivative i ψ x| ≤
        B * (eLpNorm ψ 2 (volume.restrict U)).toReal := by
    apply le_of_tendsto (hlim i ψ hψ).abs
    apply Eventually.of_forall
    intro k
    have he := weakGradient_test_bound_vectorRms (hw k) (hG k) i hψ
    rw [← eLpNorm_euclideanNorm_toReal_eq_volume_mul_rms volume U (G k) (hG k)] at he
    exact he.trans (mul_le_mul_of_nonneg_right (hb k) ENNReal.toReal_nonneg)
  choose g hg hwg using fun i =>
    exists_L2_weakPartialDerivative_of_test_bound U i hu hB (htest i)
  exact exists_weakGradient_of_L2_partials U u g hB hg hwg

end EinsteinRelation.Correctors
