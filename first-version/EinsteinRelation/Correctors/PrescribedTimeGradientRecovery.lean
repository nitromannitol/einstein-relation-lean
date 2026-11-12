import EinsteinRelation.Correctors.PrescribedTimeTestBounds
import EinsteinRelation.Correctors.PrescribedTimePartialRiesz
import EinsteinRelation.Correctors.PrescribedTimeGradientAssembly
import EinsteinRelation.Correctors.WeakGradientRmsTestBounds

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Compact derivative test bounds recover a genuine weak gradient at either
endpoint. Source: `paper/main.tex:798–806`. -/
theorem continuous_flow_exists_weakGradient_of_ae_test_bounds {d : ℕ}
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} (hu : ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ))
    {a b B : ℝ} (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (hus : ∀ t ∈ Set.Icc a b, MemLp (fun x => u (t,x)) 2 (volume.restrict U))
    (hb : ∀ i : Fin d, ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        |∫ x in U, u (t,x) * coordinateDerivative i ψ x| ≤
          B * (eLpNorm ψ 2 (volume.restrict U)).toReal) :
    ∀ t ∈ Set.Icc a b, ∃ G : Vec d → Vec d,
      HasWeakGradient U (fun x => u (t,x)) G ∧
      MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U) ∧
      (eLpNorm (fun x => euclideanNorm (G x)) 2 (volume.restrict U)).toReal ≤
        Real.sqrt d * B := by
  intro t ht
  have htest := fun i => continuous_flow_test_bound_on_closed_interval i hu ha hab
    (hb i) t ht
  choose g hg hw using fun i =>
    exists_L2_weakPartialDerivative_of_test_bound U i (hus t ht) hB (htest i)
  exact exists_weakGradient_of_L2_partials U (fun x => u (t,x)) g hB hg hw

/-- A uniform a.e. local gradient energy bound persists as a genuine weak
gradient at every time in the closed interval. Source: `paper/main.tex:798–806`. -/
theorem continuous_flow_exists_weakGradient_of_ae_rms_bound {d : ℕ}
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ))
    {a b B : ℝ} (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (hus : ∀ t ∈ Set.Icc a b, MemLp (fun x => u (t,x)) 2 (volume.restrict U))
    (hw : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient U (fun x => u (t,x)) (fun x => G (t,x)))
    (hG : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      MemLp (fun x => euclideanNorm (G (t,x))) 2 (volume.restrict U))
    (hb : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      vectorRms volume U (fun x => G (t,x)) ≤ B) :
    ∀ t ∈ Set.Icc a b, ∃ H : Vec d → Vec d,
      HasWeakGradient U (fun x => u (t,x)) H ∧
      MemLp (fun x => euclideanNorm (H x)) 2 (volume.restrict U) ∧
      (eLpNorm (fun x => euclideanNorm (H x)) 2 (volume.restrict U)).toReal ≤
        Real.sqrt d * (Real.sqrt ((volume U).toReal) * B) := by
  apply continuous_flow_exists_weakGradient_of_ae_test_bounds hu ha hab
    (mul_nonneg (Real.sqrt_nonneg _) hB) hus
  intro i ψ hψ
  filter_upwards [hw,hG,hb] with s hsw hsG hsb
  exact (weakGradient_test_bound_vectorRms hsw hsG i hψ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsb (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg)

end EinsteinRelation.Correctors
