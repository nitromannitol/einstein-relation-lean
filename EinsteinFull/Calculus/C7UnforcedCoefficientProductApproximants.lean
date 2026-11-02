import EinsteinFull.Calculus.C7UnitInitializationSupport
import EinsteinFull.Blueprint.G3.Proofs.C9DyadicIncrements
import EinsteinFull.Blueprint.G3.Proofs.W4Queue0420_1
import EinsteinFull.Work.W4.ActualLateForceHomogeneousPropagationProof
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Actual zero-force coefficient products have bounded centered local approximants. -/
theorem unforced_coefficient_product_local_approximants
    : ∀ (hlocal : node_e_u3A_forced_u2D_localityStmt)
        (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
        (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ), 0 ≤ T →
      ∃ B R L c : ℝ, 1 ≤ B ∧ 1 ≤ R ∧ 0 < L ∧ 0 < c ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ →
      ∀ (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
        (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
      ∀ (t : ℝ≥0), (t : ℝ) ≤ T → ∀ (m j k : Fin d),
        let H := centeredComplexLp Q (complexCoefficientMul Q j k (P 0 t (β m)))
        (∀ᵐ ω ∂reducedLaw Q, ‖H ω‖ ≤ B) ∧
        ∀ ρ : ℝ, R ≤ ρ → ∃ K : Lp ℂ 2 (reducedLaw Q),
          IsComplexLocalObservation Q ρ K ∧ (∫ ω, K ω ∂reducedLaw Q) = 0 ∧
          (∀ᵐ ω ∂reducedLaw Q, ‖K ω‖ ≤ B) ∧
          ‖H-K‖ ≤ L * Real.exp (-c * ρ^2) := by
  intro hlocal hends d hd D T hT
  obtain ⟨A₀, hA₀, hzero⟩ := UnitInitialization.zero_time_bound d hd D
  obtain ⟨A₁, hA₁, hpositive⟩ := UnitInitialization.positive_time_bound hlocal d hd D T hT
  let A := max A₀ A₁
  have hA : 1 ≤ A := hA₀.trans (le_max_left _ _)
  obtain ⟨M, hM, hobs⟩ := EndpointFiniteP.observation_bounds d D
  have hpacket := hends d hd D 2 (by norm_num) T 2 hT (by norm_num)
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  obtain ⟨R, c, hR, hc, happ⟩ := hpacket
  let W := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hW : 0 < W := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one D.one_le_ellipticity)
  refine ⟨1 + 2 * (M * A), R, 4 * W * R, c, ?_, hR, ?_, hc, ?_⟩
  · linarith [mul_nonneg hM.le (zero_le_one.trans hA)]
  · positivity
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m j k
  let := reducedLaw_probability Q
  have he : indexedEndpoint hd Q (.inl m) 0 (P 0) (Pdag 0) β a μ t =
      P 0 t (β m) := UnforcedIdentification.velocityEndpoint_zero hd Q (P 0) (hP 0) β hβ a t m
  have hbound : ∀ᵐ ω ∂reducedLaw Q, ‖P 0 t (β m) ω‖ ≤ A := by
    rw [← he]
    by_cases hz : t = 0
    · subst t
      exact (hzero Q hQ β a μ hβ ha hμ 0 (P 0) (Pdag 0) (hP 0) (hPdag 0)
        (.inl m) (by norm_num)).mono fun _ h => h.trans (le_max_left _ _)
    · exact (hpositive Q hQ β a μ hβ ha hμ 0 (P 0) (Pdag 0) (hP 0) (hPdag 0)
        (.inl m) (by norm_num) t (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hz)) ht).mono
        fun _ h => h.trans (le_max_right _ _)
  have hprod : ∀ᵐ ω ∂reducedLaw Q,
      ‖complexCoefficientMul Q j k (P 0 t (β m)) ω‖ ≤ M * A := by
    obtain ⟨_, haB, _⟩ := hobs Q hQ β a μ hβ ha hμ
    filter_upwards [complexCoefficientMul_coe Q j k (P 0 t (β m)),
      ha j k, haB j k, hbound] with ω heq haeq haω hbω
    rw [heq, norm_mul, ← haeq]
    exact mul_le_mul haω hbω (norm_nonneg _) hM.le
  have hHB := UnitInitialization.ae_norm_centered_le Q _ hprod
  have hHB' : ∀ᵐ ω ∂reducedLaw Q,
      ‖centeredComplexLp Q (complexCoefficientMul Q j k (P 0 t (β m))) ω‖ ≤
        1 + 2 * (M * A) := hHB.mono fun _ h => h.trans (by linarith)
  refine ⟨hHB', ?_⟩
  intro ρ hρ
  obtain ⟨E, H, hE, _, _, _, _, happrox⟩ :=
    happ Q hQ β a μ hβ ha hμ P Pdag hP hPdag (.inl m) t ht
  have hE0 : (E 0 : FieldPair d → ℂ) =ᵐ[reducedLaw Q] P 0 t (β m) := by
    simpa only [he] using hE 0
  obtain ⟨L, K, L₂, K₂, hloc, _, _, _, _, herr, _⟩ := happrox ρ hρ
  have hnorm : ‖P 0 t (β m) - L₂ 0‖ = ‖E 0 - L 0‖ := by
    calc
      _ = (eLpNorm (fun ω => E 0 ω - L 0 ω) 2 (reducedLaw Q)).toReal := by
        rw [Lp.norm_def]
        apply congrArg ENNReal.toReal
        apply eLpNorm_congr_ae
        filter_upwards [Lp.coeFn_sub (P 0 t (β m)) (L₂ 0), hE0, (hloc 0).1]
          with ω hsub hEω hLω
        simpa only [hsub, Pi.sub_apply, hEω, hLω]
      _ = (eLpNorm (fun ω => E 0 ω - L 0 ω) (ENNReal.ofReal 2)
          (reducedLaw Q)).toReal := congrArg
            (fun p => (eLpNorm (fun ω => E 0 ω - L 0 ω) p (reducedLaw Q)).toReal) htwo.symm
      _ = ‖E 0 - L 0‖ := by
        rw [Lp.norm_def]
        exact congrArg ENNReal.toReal (eLpNorm_congr_ae (Lp.coeFn_sub (E 0) (L 0)).symm)
  have herr0 : ‖P 0 t (β m) - L₂ 0‖ ≤ R * Real.exp (-c * ρ ^ 2) :=
    hnorm.trans_le (herr 0 (by norm_num)).2.2
  have hlocprod := C9DyadicIncrements.complexCoefficientMul_isLocal Q
    (lt_of_lt_of_le zero_lt_one (hR.trans hρ)) j k (hloc 0).2.2.1
  have hlocalcenter : IsComplexLocalObservation Q ρ
      (centeredComplexLp Q (complexCoefficientMul Q j k (L₂ 0))) := by
    obtain ⟨g, hg, hgf⟩ := hlocprod
    refine ⟨fun ω => g ω - ∫ η, complexCoefficientMul Q j k (L₂ 0) η ∂reducedLaw Q,
      hg.sub measurable_const, ?_⟩
    filter_upwards [hgf, centeredComplexLp_ae Q (complexCoefficientMul Q j k (L₂ 0))]
      with ω hgf heq
    rw [heq, hgf]
  have herror :
      ‖centeredComplexLp Q (complexCoefficientMul Q j k (P 0 t (β m))) -
        centeredComplexLp Q (complexCoefficientMul Q j k (L₂ 0))‖ ≤
        2 * W * (R * Real.exp (-c * ρ ^ 2)) := by
    have hcoeff :
        ‖complexCoefficientMul Q j k (P 0 t (β m)) - complexCoefficientMul Q j k (L₂ 0)‖ ≤
          W * (R * Real.exp (-c * ρ ^ 2)) :=
      (C9DyadicIncrements.norm_complexCoefficientMul_sub_le Q j k _ _).trans
        (mul_le_mul_of_nonneg_left herr0 hW.le)
    calc
      _ = ‖centeredComplexLpCLM Q
          (complexCoefficientMul Q j k (P 0 t (β m)) - complexCoefficientMul Q j k (L₂ 0))‖ := by
        rw [map_sub, centeredComplexLpCLM_apply, centeredComplexLpCLM_apply]
      _ ≤ ‖centeredComplexLpCLM Q‖ *
          ‖complexCoefficientMul Q j k (P 0 t (β m)) - complexCoefficientMul Q j k (L₂ 0)‖ :=
        (centeredComplexLpCLM Q).le_opNorm _
      _ ≤ 2 * (W * (R * Real.exp (-c * ρ ^ 2))) :=
        mul_le_mul (norm_centeredComplexLpCLM_le_two Q) hcoeff (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  obtain ⟨J, hJlocal, hJmean, hJB, hJerr⟩ :=
    UnitInitialization.exists_bounded_centered_local_projection_norm Q ρ _ _ hHB'
      (integral_centeredComplexLp Q _) hlocalcenter herror
  refine ⟨J, hJlocal, hJmean, hJB, hJerr.trans_eq ?_⟩
  ring
end EinsteinFull.Blueprint
