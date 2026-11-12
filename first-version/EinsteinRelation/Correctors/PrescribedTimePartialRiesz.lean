import EinsteinRelation.Correctors.BoundedFunctionalRiesz
import EinsteinRelation.Correctors.SpatialTestLinearMaps

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Bounded distributional derivative pairings have an actual L² representative.
Source: `paper/main.tex:798–806`; prescribed-time weak gradient recovery. -/
theorem exists_L2_weakPartialDerivative_of_test_bound {d : ℕ}
    (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)] (i : Fin d)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict U))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      |∫ x in U, u x * coordinateDerivative i ψ x| ≤
        B * (eLpNorm ψ 2 (volume.restrict U)).toReal) :
    ∃ g : Lp ℝ 2 (volume.restrict U), ‖g‖ ≤ B ∧
      HasWeakPartialDerivative U i u g := by
  obtain ⟨V,T,L,hV,hT,hL⟩ := exists_spatial_test_linear_maps U i hu
  have hnorm (ψ : V) : ‖T ψ‖ =
      (eLpNorm (ψ : Vec d → ℝ) 2 (volume.restrict U)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (hT ψ)]
  obtain ⟨g,hg,hrep⟩ := exists_riesz_of_linear_factor_bound T L hB (fun ψ => by
    rw [hL, abs_neg, hnorm]
    exact hb ψ ((hV ψ).mp ψ.property))
  refine ⟨g,hg, locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable one_le_two),
    locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp g).locallyIntegrable one_le_two), ?_⟩
  intro ψ hψ
  let v : V := ⟨ψ,(hV ψ).mpr hψ⟩
  have hv := hrep v
  rw [hL, L2.inner_def] at hv
  have he : (∫ x in U, inner ℝ (g x) (T v x)) = ∫ x in U, g x * ψ x := by
    apply integral_congr_ae
    filter_upwards [hT v] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, v, mul_comm]
  rw [he] at hv
  linarith

end EinsteinRelation.Correctors
