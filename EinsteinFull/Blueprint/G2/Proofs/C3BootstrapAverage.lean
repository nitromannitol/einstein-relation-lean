import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_bootstrap_u2D_average
import EinsteinFull.Calculus.C3BootstrapAverageSupport
import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_unit_u2D_initialization

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The given point bootstrap, evaluated at exactly r/8, supplies the input
of the forced-flux theorem. The structural exponents precede the moment order;
there is no use of the downstream scalar or Duhamel reduction. -/
theorem c3BootstrapForcedFlux_from_point
    (hforced : node_l_u3A_forced_u2D_fluxStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ ε η : ℝ, ∃ L : ℕ → ℕ, 0 < ε ∧ 0 < η ∧ η ≤ 1 / 4 ∧
    ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < growth₀ ∧ 8 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
        (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∀ F T growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
      ‖ζ‖ * Real.sqrt F ≤ F ^ η →
      (∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ T →
        MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ r : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ r : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) *
            ((r : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * (r : ℝ) ^ (-(d : ℝ) / 4))) →
      ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ r : ℝ≥0, 0 < (r : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
          (indexedEndpoint hd Q ν ζ P Pdag β a μ r) (G r) (J r)) ∧
        ∀ r : ℝ≥0, t₀ ≤ (r : ℝ) → (r : ℝ) ≤ 8 * T → (r : ℝ) ≤ F →
        ∀ s : ℝ, 1 ≤ s → ∀ hs : 0 < s,
        ∀ k : ℕ, ∀ dirs : Fin k → Fin d,
          (∀ j, MemLp
            (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J r j)) :
              FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) ∧
          Real.sqrt (∑ j, ((eLpNorm
            (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J r j)) :
              FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2) ≤
            Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ) / 2) *
              (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
                (1 + (r : ℝ) / s) ^ L k := by
  obtain ⟨ε, ηflux, L, hε, hηflux, hmoment⟩ := hforced d hd D
  refine ⟨ε, min ηflux (1 / 4), L, hε, lt_min hηflux (by norm_num),
    min_le_right _ _, ?_⟩
  intro p hp
  obtain ⟨growth₀, t₀, Cder, hgrowth₀, ht₀, hCder, hfluxdata, _⟩ := hmoment p hp
  refine ⟨growth₀, max 8 t₀, Cder, hgrowth₀, le_max_left _ _, hCder, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν F T growth K hgrowth hK hwindow hpoint
  obtain ⟨G, J, hflux, hbound⟩ := hfluxdata Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro r hr hrT hrF s hs hspos k dirs
  have hr8 : 8 ≤ (r : ℝ) := (le_max_left _ _).trans hr
  have hsmall := hpoint (r / 8)
    (by simp only [NNReal.coe_div, NNReal.coe_ofNat]; linarith only [hr8])
    (by simp only [NNReal.coe_div, NNReal.coe_ofNat]; linarith only [hrT])
  have hw : ‖ζ‖ * Real.sqrt (r : ℝ) ≤ (r : ℝ) ^ ηflux :=
    c3Bootstrap_force_window ‖ζ‖ r F (min ηflux (1 / 4)) ηflux (norm_nonneg _)
      (by linarith only [hr8]) hrF
      ((min_le_right _ _).trans (by norm_num)) (min_le_left _ _) hwindow
  apply hbound r ((le_max_right _ _).trans hr) hw growth K hgrowth hK hsmall.1
    ?_ s hs hspos k dirs
  simpa only [NNReal.coe_div, NNReal.coe_ofNat, mul_div_assoc] using hsmall.2

/-- The exact averaged-bootstrap reduction, using only the ordered graph
inputs. The unit input is retained in the prescribed interface. -/
theorem node_p_u3A_scalar_u23_bootstrap_u2D_average_of_deps
    (hcentered : node_e_u3A_centered_u2D_equationsStmt)
    (hforced : node_l_u3A_forced_u2D_fluxStmt)
    (_hunit : node_p_u3A_scalar_u23_unit_u2D_initializationStmt) :
    node_p_u3A_scalar_u23_bootstrap_u2D_averageStmt := by
  intro d hd D
  obtain ⟨ε, η, L, hε, hη, hηquarter, hmoment⟩ :=
    c3BootstrapForcedFlux_from_point hforced hd D
  refine ⟨ε, η, hε, hη, lt_of_le_of_lt hηquarter (by norm_num), ?_⟩
  intro b hb _hb16 p hp
  obtain ⟨gf, tf, Cder, hgf, _htf, hCder, hdata⟩ := hmoment p hp
  let A₀ := Cder 0 * (1 + b⁻¹) ^ L 0
  let A₁ := (d : ℝ) / 2 * Cder 1 * (1 + b⁻¹) ^ L 1
  let C := 2 ^ ε * (A₁ + A₀)
  let growth₀ := max gf (max 1 (sourceReducedBound D.ellipticity))
  let T₀ := max 16 (max (2 * tf) b⁻¹)
  have hA₀ : 0 < A₀ := by dsimp only [A₀]; exact mul_pos (hCder 0) (by positivity)
  have hA₁ : 0 ≤ A₁ := by
    dsimp only [A₁]
    exact mul_nonneg (mul_nonneg (by positivity) (hCder 1).le) (by positivity)
  have hC : 0 < C := mul_pos (by positivity) (add_pos_of_nonneg_of_pos hA₁ hA₀)
  have hgrowth₀ : 0 < growth₀ := hgf.trans_le (le_max_left _ _)
  have hT₀16 : 16 ≤ T₀ := le_max_left _ _
  have hT₀b : b⁻¹ ≤ T₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hT₀tf : 2 * tf ≤ T₀ := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨C, growth₀, T₀, hC, hgrowth₀, hT₀16, hT₀b, ?_⟩
  intro growth hgrowth Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  dsimp only
  intro _hm F T hT _hTF hwindow K Kprime hK hKprime hAvg hPoint r hr1 hrS s hbs hs
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (hT₀16.trans hT)
  have htpos : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one hr1
  have hg : 0 < growth := hgrowth₀.trans_le hgrowth
  have hgr : gf ≤ growth := (le_max_left _ _).trans hgrowth
  have hrate : sourceReducedBound D.ellipticity ≤ growth :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hgrowth)
  have hwpos : 0 ≤ s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4) :=
    add_nonneg (Real.rpow_nonneg hs.le _)
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hs.le _))
  by_cases hrT : (r : ℝ) ≤ T
  · obtain ⟨hmem, hnorm⟩ := hAvg r hr1 hrT s hbs hs
    refine ⟨hmem, hnorm.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ hwpos
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact le_add_of_nonneg_right (by positivity)
  have hTr : T ≤ (r : ℝ) := (lt_of_not_ge hrT).le
  have hr2T : (r : ℝ) ≤ 2 * T := hrS.trans (min_le_left _ _)
  have hrF : (r : ℝ) ≤ F := hrS.trans (min_le_right _ _)
  have hrhalfT : (r : ℝ) / 2 ≤ T := by linarith only [hr2T]
  have hrhalf1 : 1 ≤ (r : ℝ) / 2 := by linarith only [hT₀16, hT, hTr]
  have hhalf : ((r : ℝ) / 2).toNNReal = r / 2 := by
    ext
    rw [NNReal.coe_div, NNReal.coe_ofNat]
    exact Real.coe_toNNReal _ (half_pos htpos).le
  have havgsmall := hAvg (r / 2)
    (by simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hrhalf1)
    (by simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hrhalfT) s
    (by simp only [NNReal.coe_div, NNReal.coe_ofNat]
        exact (mul_le_mul_of_nonneg_left (half_le_self htpos.le) hb.le).trans hbs) hs
  obtain ⟨G, J, hflux, hbound⟩ :=
    hdata Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν F T growth Kprime
      hgr hKprime hwindow hPoint
  have hs1 : 1 ≤ s := by
    have hh := mul_le_mul_of_nonneg_left (hT₀b.trans hT) hb.le
    rw [mul_inv_cancel₀ hb.ne'] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hTr hb.le).trans hbs)
  let B := Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) * ((r : ℝ) / 2) ^ (-1 - ε) * Kprime *
    (A₁ * s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * A₀ * s ^ (-(d : ℝ) / 4))
  have hBpos : 0 ≤ B := by dsimp only [B]; positivity
  have hvector (u : ℝ) (hu : u ∈ Set.Ioo ((r : ℝ) / 2) (r : ℝ)) :
      MemLp (c3BootstrapFluxVector hd Q ν ζ J s hs r u : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (c3BootstrapFluxVector hd Q ν ζ J s hs r u : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ B := by
    have hu0 : 0 ≤ u := (half_pos htpos).le.trans hu.1.le
    have huf : tf ≤ u := by linarith only [hT₀tf, hT, hTr, hu.1]
    have hu8T : u ≤ 8 * T := by linarith only [hu.2, hr2T, hTpos]
    have huflux := fun k dirs => hbound u.toNNReal
      (by simpa only [Real.coe_toNNReal _ hu0] using huf)
      (by simpa only [Real.coe_toNNReal _ hu0] using hu8T)
      (by simpa only [Real.coe_toNNReal _ hu0] using hu.2.le.trans hrF)
      s hs1 hs k dirs
    have hv := c3BootstrapFluxVector_uniform_bound hd Q ν ζ J s hs r u b ε growth Kprime p
      L Cder hp htpos hu.1.le hu.2.le hb hbs hε.le (by linarith only [hKprime])
      (fun k => (hCder k).le) hg.le hrate (by
        intro k dirs
        simpa only [Real.coe_toNNReal _ hu0] using huflux k dirs)
    refine ⟨hv.1, hv.2.trans_eq ?_⟩
    dsimp only [B, A₀, A₁]
    rw [show -(d : ℝ) / 4 - 1 / 2 = -(1 / 2 + (d : ℝ) / 4) by ring]
    ring
  have hstep := c3BootstrapInteraction_half_step hcentered hd D Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν G J hflux s hs r htpos p hp
    (K * Real.exp (growth * ‖ζ‖ ^ 2 * ((r : ℝ) / 2)) *
      (s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4))) B hBpos
    (by simpa only [hhalf] using havgsmall.1)
    (by simpa only [hhalf, NNReal.coe_div, NNReal.coe_ofNat] using havgsmall.2)
    (fun u hu => (hvector u hu).1) (fun u hu => (hvector u hu).2)
  simp only [Real.toNNReal_coe] at hstep
  refine ⟨hstep.1, hstep.2.trans ?_⟩
  let A := ((endpointDriftSign ν : ℂ) * ζ).im ^ 2 *
    homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩ / 2
  have hAg : A ≤ growth * ‖ζ‖ ^ 2 := by
    have hh := c3Bootstrap_gaussian_rate_le Q ⟨0, by omega⟩ ν ζ growth hrate
    exact hh.trans (by nlinarith only [mul_nonneg hg.le (sq_nonneg ‖ζ‖)])
  have hhom := c3Bootstrap_homogeneous_weight A (growth * ‖ζ‖ ^ 2) r K
    (s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4))
    hAg htpos.le (by linarith only [hK]) hwpos
  have herror := c3Bootstrap_half_error_le r T ε Kprime
    (Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ))) A₀ A₁
    (s ^ (-(1 / 2 + (d : ℝ) / 4))) (s ^ (-(d : ℝ) / 4)) ‖ζ‖
    hTpos hTr hε.le (by linarith only [hKprime]) (Real.exp_pos _).le hA₀.le hA₁
    (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hs.le _) (norm_nonneg _)
  have htime : ((endpointDriftSign ν : ℂ) * ζ).im ^ 2 * ((r : ℝ) / 2) *
      homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩ / 2 = A * ((r : ℝ) / 2) := by
    dsimp only [A]
    ring
  rw [htime]
  calc
    _ ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) *
          (s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)) +
        C * T ^ (-ε) * Kprime * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) *
          (s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)) :=
      add_le_add hhom herror
    _ = _ := by ring

end EinsteinFull.Blueprint
