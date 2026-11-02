import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_unit_u2D_initialization
import EinsteinFull.Calculus.C6UnforcedDriftGaussianFiniteP
import EinsteinFull.Calculus.C7BoundedTimeGaussianForceDifference
import EinsteinFull.Calculus.C8UnforcedDriftGaussianDecay
import EinsteinFull.Calculus.C8ZeroForceTransposeIdentification
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull.UnitInitialization
private theorem zero_endpoint
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (ν : EndpointIndex d) (t : ℝ≥0) :
    indexedEndpoint hd Q ν 0 P Pdag β a μ t =
      match ν with
      | .inl i => P t (β i)
      | .inr true => P t (β ⟨0, by omega⟩)
      | .inr false => 0 := by
  cases ν with
  | inl j =>
      simp only [indexedEndpoint, velocityEndpoint, zero_smul, add_zero]
      exact c8_centered_unforced_drift hd hβ hP hPdag t j
  | inr b =>
      cases b with
      | false => simp only [indexedEndpoint, clockEndpoint, zero_smul]
      | true => exact (unforced_transpose_identification hP hPdag).2.2 β t

theorem node_p_u3A_scalar_u23_unit_u2D_initialization_of_deps
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt) :
    node_p_u3A_scalar_u23_unit_u2D_initializationStmt := by
  intro d hd D a₀ _ha₀ _ha₀one p hp T hT
  have hT₀ : 0 ≤ T := zero_le_one.trans hT
  obtain ⟨Cp, hCp, hpoint⟩ := point_bound hlocal d hd D T hT₀
  obtain ⟨Cu, hCu, hunforced⟩ :=
    unforced_drift_gaussian_decay_finite_p hlocal hends d hd D T p hT₀ hp
  obtain ⟨Cf, hCf, hforce⟩ :=
    bounded_time_gaussian_force_difference hlocal hends d hd D T p hT₀ hp
  let C := Cp + Cu + Cf
  have hCp₀ : 0 ≤ Cp := zero_le_one.trans hCp
  have hCf₀ : 0 ≤ Cf := zero_le_one.trans hCf
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht
  dsimp only
  constructor
  · obtain ⟨hm, hn⟩ := hpoint Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht
      (ENNReal.ofReal p)
    exact ⟨hm, hn.trans (by dsimp only [C]; linarith)⟩
  · intro s _has hs
    let F := forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d)
    let Fdag := fun z u => complexL2Transpose (reducedLaw Q) (F z u)
    have hF := fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q
      (⟨0, by omega⟩ : Fin d) z
    have hFdag := fun z => isComplexTransposeSemigroup_complexL2Transpose Q (F z)
    let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
    let U₀ := indexedEndpoint hd Q ν 0 (F 0) (Fdag 0) β a μ t
    let G := gaussianAverage hd Q s hs
    let q := ENNReal.ofReal p
    have hq : 1 ≤ q := ENNReal.one_le_ofReal.mpr (by linarith)
    have hu : MemLp (G U₀ : FieldPair d → ℂ) q (reducedLaw Q) ∧
        (eLpNorm (G U₀ : FieldPair d → ℂ) q (reducedLaw Q)).toReal ≤
          Cu * s ^ (-(1/2+(d : ℝ)/4)) := by
      have hb := hunforced Q hQ β a μ hβ ha hμ F Fdag hF hFdag t ht
      dsimp only [U₀]
      rw [zero_endpoint hd β hβ a μ (F 0) (Fdag 0) (hF 0) (hFdag 0) ν t]
      cases ν with
      | inl j => exact hb j s hs
      | inr b =>
          cases b with
          | true => exact hb ⟨0, by omega⟩ s hs
          | false =>
              have hz : G 0 = 0 := by
                change homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0 0 = 0
                exact map_zero _
              rw [hz]
              refine ⟨(MemLp.zero).ae_eq (Lp.coeFn_zero ℂ 2 (reducedLaw Q)).symm, ?_⟩
              rw [eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 (reducedLaw Q)),
                eLpNorm_zero, ENNReal.toReal_zero]
              exact mul_nonneg hCu.le (Real.rpow_nonneg hs.le _)
    have hf := hforce Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht s hs
    change MemLp (G (U - U₀) : FieldPair d → ℂ) q (reducedLaw Q) ∧
      (eLpNorm (G (U - U₀) : FieldPair d → ℂ) q (reducedLaw Q)).toReal ≤
        Cf * ‖ζ‖ * s ^ (-(d : ℝ)/4) at hf
    have he : G U = G (U - U₀) + G U₀ := by
      change homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0 U =
        homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0 (U - U₀) +
          homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0 U₀
      rw [← map_add, sub_add_cancel]
    have hsum := (hf.1.add hu.1).ae_eq
      (Lp.coeFn_add (G (U - U₀)) (G U₀)).symm
    change MemLp (G U : FieldPair d → ℂ) q (reducedLaw Q) ∧
      (eLpNorm (G U : FieldPair d → ℂ) q (reducedLaw Q)).toReal ≤
        C * (s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4))
    rw [he]
    refine ⟨hsum, ?_⟩
    have hn : (eLpNorm (G (U - U₀) + G U₀ : Lp ℂ 2 (reducedLaw Q)) q
        (reducedLaw Q)).toReal ≤
        (eLpNorm (G (U - U₀)) q (reducedLaw Q)).toReal +
          (eLpNorm (G U₀) q (reducedLaw Q)).toReal := by
      rw [← ENNReal.toReal_add hf.1.eLpNorm_ne_top hu.1.eLpNorm_ne_top]
      apply ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨hf.1.eLpNorm_ne_top, hu.1.eLpNorm_ne_top⟩)
      rw [eLpNorm_congr_ae (Lp.coeFn_add _ _)]
      exact eLpNorm_add_le hq
    apply hn.trans
    calc
      _ ≤ Cf * ‖ζ‖ * s ^ (-(d : ℝ)/4) + Cu * s ^ (-(1/2+(d : ℝ)/4)) :=
        add_le_add hf.2 hu.2
      _ ≤ C * (s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4)) := by
        have hx := Real.rpow_nonneg hs.le (-(1/2+(d : ℝ)/4))
        have hy := mul_nonneg (norm_nonneg ζ) (Real.rpow_nonneg hs.le (-(d : ℝ)/4))
        have hCuC : Cu ≤ C := by dsimp only [C]; linarith
        have hCfC : Cf ≤ C := by dsimp only [C]; linarith
        nlinarith [mul_le_mul_of_nonneg_right hCuC hx,
          mul_le_mul_of_nonneg_right hCfC hy]
end EinsteinFull.Blueprint
