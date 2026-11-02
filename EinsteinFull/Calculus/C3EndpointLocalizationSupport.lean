import EinsteinFull.Calculus.C1EndpointsV2Support
import EinsteinFull.Blueprint.Foundation.Draft.ForcedLocalityV2
import EinsteinFull.Blueprint.G1.Proofs.S3AnnuliReal
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport

/-! Fixed finite-p projection estimates for the endpoint localization packet.
The V2 locality producer is pending review and remains unproved. -/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace EinsteinFull.EndpointLocalization
open EinsteinRelation

private instance probability {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) :
    IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q

/-- An actual local L2 approximation controls the fixed finite-p projection.
No finite-p membership of the approximant is required. -/
theorem norm_sub_project_le {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (ρ : ℝ)
    (E : Lp ℂ p (reducedLaw Q)) (U V : Lp ℂ 2 (reducedLaw Q))
    (hE : (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] U)
    (hV : IsComplexLocalObservation Q ρ V) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ ≤ ε) :
    ‖E - EndpointProjection.project
      (m := localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤ 2 * ε := by
  let m := localSigma {x : Vec d | euclideanNorm x < ρ}
  have hm := Probability.localSigma_le_borel {x : Vec d | euclideanNorm x < ρ}
  obtain ⟨v, hv, hve⟩ := hV
  have he : ∀ᵐ ω ∂reducedLaw Q, ‖U ω - v ω‖ ≤ ε := by
    filter_upwards [herr, hve] with ω h h' using h' ▸ h
  have hb := AnnuliSupport.ae_norm_condExpL2_sub_le hm le_rfl U v hv he
  have hproj : (EndpointProjection.project (m := m) E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      (condExpL2 ℂ ℂ hm U : FieldPair d → ℂ) :=
    (EndpointProjection.project_ae E).trans
      ((condExp_congr_ae hE).trans (AnnuliSupport.condExpL2_ae_eq hm U).symm)
  rw [Lp.norm_def]
  apply AnnuliSupport.eLpNorm_toReal_le_of_ae_norm_le
    (Lp.aestronglyMeasurable _) (by positivity)
  filter_upwards [Lp.coeFn_sub E (EndpointProjection.project (m := m) E), hE, hproj, hb]
    with ω hsub he hp' hb'
  rw [hsub, Pi.sub_apply, he, hp', norm_sub_rev]
  exact hb'

/-- Centering a local approximant preserves locality and costs at most two in
its pointwise error, under the actual probability law. -/
theorem centered_approximation {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (ρ : ℝ) (U V : Lp ℂ 2 (reducedLaw Q))
    (hV : IsComplexLocalObservation Q ρ V) {ε : ℝ}
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ ≤ ε) :
    IsComplexLocalObservation Q ρ (centeredComplexLp Q V) ∧
    ∀ᵐ ω ∂reducedLaw Q,
      ‖centeredComplexLp Q U ω - centeredComplexLp Q V ω‖ ≤ 2 * ε := by
  refine ⟨isComplexLocal_centered Q hV, ?_⟩
  have hiU := (Lp.memLp U).integrable one_le_two
  have hiV := (Lp.memLp V).integrable one_le_two
  have hi : ‖∫ ω, U ω ∂reducedLaw Q - ∫ ω, V ω ∂reducedLaw Q‖ ≤ ε := by
    rw [← integral_sub hiU hiV]
    simpa using norm_integral_le_of_norm_le_const herr
  filter_upwards [centeredComplexLp_ae Q U, centeredComplexLp_ae Q V, herr]
    with ω hu hv he
  rw [hu, hv]
  calc
    ‖(U ω - ∫ ω, U ω ∂reducedLaw Q) - (V ω - ∫ ω, V ω ∂reducedLaw Q)‖ =
        ‖(U ω - V ω) - (∫ ω, U ω ∂reducedLaw Q - ∫ ω, V ω ∂reducedLaw Q)‖ := by congr 1; ring
    _ ≤ ‖U ω - V ω‖ + ‖∫ ω, U ω ∂reducedLaw Q - ∫ ω, V ω ∂reducedLaw Q‖ := norm_sub_le _ _
    _ ≤ 2 * ε := by linarith


/-- Transfer the uncentered approximation to the actual indexed endpoint.
The transpose endpoint stays uncentered; forward and clock endpoints are centered. -/
theorem indexed_approximation {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (ρ : ℝ) (V : Lp ℂ 2 (reducedLaw Q))
    (hV : IsComplexLocalObservation Q ρ V) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - V ω‖ ≤ ε) :
    ∃ W : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ W ∧
      ∀ᵐ ω ∂reducedLaw Q,
        ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω - W ω‖ ≤ 2 * ε := by
  rcases ν with i | b
  · exact ⟨centeredComplexLp Q V, centered_approximation Q ρ _ V hV herr⟩
  · cases b
    · obtain ⟨hl, he⟩ := centered_approximation Q ρ _ V hV herr
      refine ⟨centeredComplexLp Q V, hl, ?_⟩
      filter_upwards [he, smul_centered_ae_eq Q ζ (P t μ)] with ω h h'
      exact h' ▸ h
    · refine ⟨V, hV, ?_⟩
      filter_upwards [herr] with ω h using h.trans (by linarith)

/-- At positive times V2 gives the exact fixed-projection estimate, with its
original time-dependent Gaussian and constants before the environment law. -/
theorem positive_time_projection (hlocal : Blueprint.node_e_u3A_forced_u2D_localityStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, 0 < (t : ℝ) → ∀ ρ : ℝ,
      C * max 1 (Real.sqrt (t : ℝ)) ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        4 * C * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) := by
  obtain ⟨C₁, c₁, N, hC₁, hc₁, hlong⟩ := hlocal.1 d hd D
  obtain ⟨C₂, c₂, hC₂, hc₂, hshort⟩ := hlocal.2 d hd D B hB
  let C := max C₁ C₂
  let c := min c₁ c₂
  have hC : 1 ≤ C := hC₁.trans (le_max_left _ _)
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨C, c, N, hC, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν t ht ρ hρ p _ E hE
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hρ₁ : C₁ * Real.sqrt (t : ℝ) ≤ ρ := by
    apply le_trans _ hρ
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (Real.sqrt_nonneg _) hC0
  have hρ₂ : C₂ ≤ ρ := by
    calc C₂ ≤ C := le_max_right _ _
         _ ≤ C * max 1 (Real.sqrt (t : ℝ)) := le_mul_of_one_le_right hC0 (le_max_left _ _)
         _ ≤ ρ := hρ
  let ε := C * (2 + (t : ℝ)) ^ N *
    Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have happ : ∃ V : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ V ∧
      ∀ᵐ ω ∂reducedLaw Q,
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - V ω‖ ≤ ε := by
    by_cases ht₁ : 1 ≤ (t : ℝ)
    · obtain ⟨G, _, hg, _⟩ := hlong Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
      obtain ⟨V, _, hl, _, he, _⟩ := hg t ht₁ ρ hρ₁
      refine ⟨V, hl, ?_⟩
      have hbound : C₁ * (2 + (t : ℝ)) ^ N *
          Real.exp (C₁ * ‖ζ‖ ^ 2 * (t : ℝ) - c₁ * ρ ^ 2 / (t : ℝ)) ≤ ε := by
        dsimp [ε]
        gcongr
        · exact le_max_left _ _
        · exact le_max_left _ _
        · exact min_le_left _ _
      filter_upwards [he] with ω h
      exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (h.trans hbound)
    · obtain ⟨V, hl, he⟩ := hshort Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν t ht
        (lt_of_not_ge ht₁) ρ hρ₂
      refine ⟨V, hl, ?_⟩
      have hbound : C₂ * Real.exp (-c₂ * ρ ^ 2 / (t : ℝ)) ≤ ε := by
        have hpow : 1 ≤ (2 + (t : ℝ)) ^ N := one_le_pow₀ (by linarith)
        calc
          C₂ * Real.exp (-c₂ * ρ ^ 2 / (t : ℝ)) ≤
              C * 1 * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) := by
            rw [mul_one]
            gcongr
            · exact le_max_right _ _
            · have hc' : c ≤ c₂ := min_le_right _ _
              have hpos : 0 ≤ C * ‖ζ‖ ^ 2 * (t : ℝ) := by positivity
              have hdiv : c * ρ ^ 2 / (t : ℝ) ≤ c₂ * ρ ^ 2 / (t : ℝ) := by gcongr
              rw [neg_mul, neg_div]
              linarith only [hdiv, hpos]
          _ ≤ ε := by dsimp [ε]; gcongr
      exact he.mono fun _ h => h.trans hbound
  obtain ⟨V, hl, he⟩ := happ
  obtain ⟨W, hw, hew⟩ := indexed_approximation hd Q ν ζ P Pdag β a μ t ρ V hl hε he
  have hb := norm_sub_project_le Q ρ E _ W hE hw (by positivity) hew
  dsimp [ε] at hb
  calc
    _ ≤ 2 * (2 * (C * (2 + (t : ℝ)) ^ N *
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)))) := hb
    _ = _ := by ring


/-- The deterministic V2 Gaussian is uniform on a bounded time/force window.
The constants here depend only on the displayed structural constants and window. -/
theorem gaussian_window_bound (C c B T ρ t : ℝ) (N : ℕ)
    (hC : 0 ≤ C) (hc : 0 < c) (_hB : 0 ≤ B) (hT : 0 < T)
    (ht : 0 < t) (htT : t ≤ T) (z : ℂ) (hz : ‖z‖ ≤ B) :
    4 * C * (2 + t) ^ N * Real.exp (C * ‖z‖ ^ 2 * t - c * ρ ^ 2 / t) ≤
      (4 * C * (2 + T) ^ N * Real.exp (C * B ^ 2 * T)) *
        Real.exp (-(c / T) * ρ ^ 2) := by
  have hforce : C * ‖z‖ ^ 2 * t ≤ C * B ^ 2 * T := by gcongr
  have htail : c * ρ ^ 2 / T ≤ c * ρ ^ 2 / t := by
    exact div_le_div_of_nonneg_left (by positivity) ht htT
  have hexp : C * ‖z‖ ^ 2 * t - c * ρ ^ 2 / t ≤ C * B ^ 2 * T + -(c / T) * ρ ^ 2 := by
    have hnorm : -(c / T) * ρ ^ 2 = -(c * ρ ^ 2 / T) := by ring
    rw [hnorm]
    linarith only [hforce, htail]
  calc
    _ ≤ 4 * C * (2 + T) ^ N *
      Real.exp (C * B ^ 2 * T + -(c / T) * ρ ^ 2) := by gcongr
    _ = _ := by rw [Real.exp_add]; ring


/-- Strong L2 continuity and a positive-time Gaussian error prove exact
locality at zero, without any assumed locality of the initial datum. -/
theorem initial_fixed {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (ρ : ℝ)
    (F : ℝ≥0 → Lp ℂ 2 (reducedLaw Q)) (hF : Continuous F)
    (K a : ℝ) (ha : 0 < a)
    (herr : ∀ t : ℝ≥0, 0 < (t : ℝ) → (t : ℝ) ≤ 1 →
      ‖F t - EndpointProjection.project
        (m := localSigma {x : Vec d | euclideanNorm x < ρ}) (F t)‖ ≤
        K * Real.exp (-a / (t : ℝ))) :
    EndpointProjection.project
      (m := localSigma {x : Vec d | euclideanNorm x < ρ}) (F 0) = F 0 := by
  let t : ℕ → ℝ≥0 := fun n => ((n : ℝ≥0) + 1)⁻¹
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have he : Tendsto (fun n => K * Real.exp (-a / (t n : ℝ))) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hg := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hnat.const_mul_atTop ha)
    have hg' : Tendsto (fun n : ℕ => Real.exp (-a / (t n : ℝ))) atTop (𝓝 0) := by
      convert hg using 1
      ext n
      simp [t, div_inv_eq_mul, neg_mul]
    simpa using hg'.const_mul K
  let L := EndpointProjection.projectionCLM (μ := reducedLaw Q)
    (m := localSigma {x : Vec d | euclideanNorm x < ρ}) (p := 2)
  have hn : Tendsto (fun n => ‖F (t n) - L (F (t n))‖) atTop
      (𝓝 ‖F 0 - L (F 0)‖) := ((hF.sub (L.continuous.comp hF)).norm.tendsto 0).comp ht
  have hle : ‖F 0 - L (F 0)‖ ≤ 0 := by
    apply le_of_tendsto_of_tendsto hn he
    apply Filter.Eventually.of_forall
    intro n
    apply herr
    · dsimp [t]; positivity
    · change (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) ≤ 1
      exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (show (0 : ℝ≥0) ≤ (n : ℝ≥0) from zero_le))
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))).symm

/-- All indexed endpoint orbits are strongly continuous, including at zero. -/
theorem continuous_indexed {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) :
    Continuous (fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t) := by
  rcases ν with i | b
  · simpa only [indexedEndpoint, velocityEndpoint, Function.comp_def, centeredComplexLpCLM_apply] using!
      (centeredComplexLpCLM Q).continuous.comp (hP.2.2.1 (β i + ζ • a ⟨0, by omega⟩ i))
  · cases b
    · simpa only [indexedEndpoint, clockEndpoint, Pi.smul_apply, Function.comp_def, centeredComplexLpCLM_apply] using!
        ((centeredComplexLpCLM Q).continuous.comp (hP.2.2.1 μ)).const_smul ζ
    · exact hPdag.continuous_apply hP _


/-- Absorb only the bounded-time prefactor, retaining the small-time tail. -/
theorem gaussian_prefactor_bound (C c B T ρ t : ℝ) (N : ℕ)
    (hC : 0 ≤ C) (ht : 0 ≤ t) (htT : t ≤ T) (z : ℂ) (hz : ‖z‖ ≤ B) :
    4 * C * (2 + t) ^ N * Real.exp (C * ‖z‖ ^ 2 * t - c * ρ ^ 2 / t) ≤
      (4 * C * (2 + T) ^ N * Real.exp (C * B ^ 2 * T)) *
        Real.exp (-c * ρ ^ 2 / t) := by
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  have hT0 : 0 ≤ T := ht.trans htT
  have hforce : C * ‖z‖ ^ 2 * t ≤ C * B ^ 2 * T := by gcongr
  gcongr
  simpa only [sub_eq_add_neg, neg_mul, neg_div] using
    (add_le_add hforce (le_refl (-(c * ρ ^ 2 / t))))

/-- Uniform Gaussian error of the fixed projection of the actual indexed
endpoint, including time zero. Conditional only on pending, unproved V2. -/
theorem uniform_projection (hlocal : Blueprint.node_e_u3A_forced_u2D_localityStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ) :
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
  obtain ⟨C, c, N, hC, hc, hp⟩ := positive_time_projection hlocal d hd D B hB
  let S := max 1 T
  let R := C * max 1 (Real.sqrt S)
  let K := 4 * C * (2 + S) ^ N * Real.exp (C * B ^ 2 * S)
  have hS : 1 ≤ S := le_max_left _ _
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hR : 1 ≤ R := hC.trans
    (le_mul_of_one_le_right hC0.le (le_max_left _ _))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨R, K, c / S, hR, hK, div_pos hc hS0, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν t htT ρ hρ p _ E hE
  have hrad : ∀ s : ℝ≥0, (s : ℝ) ≤ S → C * max 1 (Real.sqrt (s : ℝ)) ≤ ρ := by
    intro s hs
    apply le_trans _ hρ
    dsimp [R]
    gcongr
  have hpos := hp Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν
  by_cases ht : 0 < (t : ℝ)
  · exact (hpos t ht ρ (hrad t (htT.trans (le_max_right _ _))) p E hE).trans
      (gaussian_window_bound C c B S ρ t N hC0.le hc hB.le hS0 ht
        (htT.trans (le_max_right _ _)) ζ hζ)
  · have ht0 : t = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt ht) t.coe_nonneg)
    subst t
    let F := fun s => indexedEndpoint hd Q ν ζ P Pdag β a μ s
    have ha0 : 0 < c * ρ ^ 2 := by
      have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one (hR.trans hρ)
      positivity
    have hf := initial_fixed Q ρ F (continuous_indexed hd Q ν ζ P Pdag β a μ hP hPdag)
      (4 * C * 3 ^ N * Real.exp (C * B ^ 2)) (c * ρ ^ 2) ha0 (by
        intro s hs hs1
        have hh := hpos s hs ρ (hrad s (hs1.trans hS)) 2 (F s) Filter.EventuallyEq.rfl
        have hb := gaussian_prefactor_bound C c B 1 ρ s N hC0.le s.coe_nonneg hs1 ζ hζ
        have hn : -c * ρ ^ 2 / (s : ℝ) = -(c * ρ ^ 2) / (s : ℝ) := by ring
        simpa only [one_mul, mul_one, show (2 : ℝ) + 1 = 3 by norm_num, hn] using hh.trans hb)
    have hloc0 : IsComplexLocalObservation Q ρ (F 0) := by
      obtain ⟨V, he, hv⟩ := EndpointProjection.exists_local_l2 (p := 2) Q ρ le_rfl (F 0)
      have hFV : F 0 = V := by apply Lp.ext; simpa only [hf] using he
      rwa [hFV]
    have hz := norm_sub_project_le Q ρ E (F 0) (F 0) hE hloc0 (le_refl 0)
      (Filter.Eventually.of_forall fun ω => by simp)
    calc
      _ ≤ 0 := by simpa only [mul_zero] using hz
      _ ≤ _ := (mul_pos hK (Real.exp_pos _)).le

end EinsteinFull.EndpointLocalization
