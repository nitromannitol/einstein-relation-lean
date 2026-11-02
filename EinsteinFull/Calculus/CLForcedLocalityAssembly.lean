import EinsteinFull.Calculus.CLTransposeLocality
import EinsteinFull.Calculus.CLForcedLocalityArith
import EinsteinFull.Calculus.C7ForcedLocalityCube
import EinsteinFull.Calculus.C7UnitInitializationSupport
import EinsteinFull.Calculus.C10CrudeEnergyAssembly
import EinsteinFull.Blueprint.Foundation.node_e_u3A_forced_u2D_locality
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal

/-! Assembly of `e:forced-locality`, `paper/main.tex:715`, from the large-time
bounded-force locality of all endpoints. The centred and cube-integral clauses
follow from the joint approximation as in the fleet assembler (copied here so
that this file depends only on committed sources). -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull
open EinsteinRelation Blueprint

theorem clr_fl_local_approximation_transfers {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (U V : Lp ℂ 2 (reducedLaw Q)) (G H : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : IsComplexLocalObservation Q ρ V)
    (hH : ∀ j, IsComplexLocalObservation Q ρ (H j))
    (herr : ∀ᵐ ω ∂reducedLaw Q,
      ‖U ω - V ω‖ + Real.sqrt (∑ j, ‖G j ω - H j ω‖ ^ 2) ≤ ε) :
    (∀ᵐ ω ∂reducedLaw Q,
      ‖centeredComplexLp Q U ω - centeredComplexLp Q V ω‖ ≤ 2 * ε) ∧
    IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ) (cubeIntegralObservation Q ρ V) ∧
    (∀ j, IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ)
      (cubeIntegralObservation Q ρ (H j))) ∧
    (∀ᵐ ω ∂reducedLaw Q,
      ‖cubeIntegralObservation Q ρ U ω - cubeIntegralObservation Q ρ V ω‖ +
        Real.sqrt (∑ j, ‖cubeIntegralObservation Q ρ (G j) ω -
          cubeIntegralObservation Q ρ (H j) ω‖ ^ 2) ≤ ρ ^ d * ε) := by
  have hu : ∀ᵐ ω ∂reducedLaw Q, ‖(U - V) ω‖ ≤ ε := by
    filter_upwards [herr, Lp.coeFn_sub U V] with ω h he
    rw [he]
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans h
  have hc := UnitInitialization.ae_norm_centered_le Q (U - V) hu
  have heq : centeredComplexLp Q (U - V) = centeredComplexLp Q U - centeredComplexLp Q V := by
    simpa only [centeredComplexLpCLM_apply] using (centeredComplexLpCLM Q).map_sub U V
  refine ⟨?_, c7_cubeIntegralObservation_local Q hρ V hV,
    fun j => c7_cubeIntegralObservation_local Q hρ (H j) (hH j),
    c7_cubeIntegralObservation_joint_error Q hρ hε U V G H herr⟩
  rw [heq] at hc
  filter_upwards [hc, Lp.coeFn_sub (centeredComplexLp Q U) (centeredComplexLp Q V)]
    with ω h he
  simpa only [he, Pi.sub_apply] using h


/-- Absorb the volume factor into the polynomial locality bound. -/
theorem clr_fl_cube_polynomial_bound {C t ρ E : ℝ} {N d : ℕ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hρ : 0 ≤ ρ) :
    ρ ^ d * (C * (2 + t) ^ N * Real.exp E) ≤
      C * (2 + t + ρ) ^ (N + d) * Real.exp E := by
  have hbase : 0 ≤ 2 + t + ρ := by linarith
  have htbase : 0 ≤ 2 + t := by linarith
  have hN : (2 + t) ^ N ≤ (2 + t + ρ) ^ N := by
    exact pow_le_pow_left₀ htbase (by linarith) N
  have hd : ρ ^ d ≤ (2 + t + ρ) ^ d := by
    exact pow_le_pow_left₀ hρ (by linarith) d
  calc
    ρ ^ d * (C * (2 + t) ^ N * Real.exp E) =
        C * ((2 + t) ^ N * ρ ^ d) * Real.exp E := by ring
    _ ≤ C * ((2 + t + ρ) ^ N * (2 + t + ρ) ^ d) * Real.exp E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul hN hd (pow_nonneg hρ _) (pow_nonneg hbase _)) hC)
        (Real.exp_nonneg E)
    _ = C * (2 + t + ρ) ^ (N + d) * Real.exp E := by rw [pow_add]


/-- Componentwise local approximations assemble into a joint approximation of
  the actual uncentered endpoint and the chosen gradient. -/

theorem clr_fl_actual_endpoint_center_cube_transfer {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (ν : EndpointIndex d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (ρ C c : ℝ) (N : ℕ)
    (hρ : 0 < ρ) (hC : 0 ≤ C)
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    (hV : IsComplexLocalObservation Q ρ V)
    (hH : ∀ j, IsComplexLocalObservation Q ρ (H j))
    (herr : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - V ω‖ +
        Real.sqrt (∑ j, ‖G j ω - H j ω‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) :
    (∀ᵐ ω ∂reducedLaw Q,
      ‖centeredComplexLp Q (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) ω -
        centeredComplexLp Q V ω‖ ≤
        2 * C * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) ∧
    IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ) (cubeIntegralObservation Q ρ V) ∧
    (∀ j, IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ)
      (cubeIntegralObservation Q ρ (H j))) ∧
    (∀ᵐ ω ∂reducedLaw Q,
      ‖cubeIntegralObservation Q ρ (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) ω -
        cubeIntegralObservation Q ρ V ω‖ +
        Real.sqrt (∑ j, ‖cubeIntegralObservation Q ρ (G j) ω -
          cubeIntegralObservation Q ρ (H j) ω‖ ^ 2) ≤
        C * (2 + (t : ℝ) + ρ) ^ (N + d) *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) := by
  have ht : 0 ≤ (t : ℝ) := t.coe_nonneg
  have hε : 0 ≤ C * (2 + (t : ℝ)) ^ N *
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) := by positivity
  obtain ⟨hc, hv, hh, he⟩ := clr_fl_local_approximation_transfers Q hρ hε
    (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) V G H hV hH herr
  refine ⟨?_, hv, hh, ?_⟩
  · filter_upwards [hc] with ω hω
    convert hω using 1; ring
  · filter_upwards [he] with ω hω
    exact hω.trans (clr_fl_cube_polynomial_bound hC ht hρ.le)



/-- The node conclusion from the joint approximation of the actual uncentered
endpoints, with the common gradient of the local-time node. -/
theorem clr_fl_of_joint_approximation
    (hactual : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
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
      ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t)) ∧
      (∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ ρ : ℝ, C * Real.sqrt (t : ℝ) ≤ ρ →
        ∃ V : Lp ℂ 2 (reducedLaw Q), ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
        IsComplexLocalObservation Q ρ V ∧
        (∀ j, IsComplexLocalObservation Q ρ (H j)) ∧
        ∀ᵐ ω ∂reducedLaw Q,
          ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - V ω‖ +
            Real.sqrt (∑ j, ‖G t j ω - H j ω‖ ^ 2) ≤
          C * (2 + (t : ℝ)) ^ N *
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) ∧
      (∀ t : ℝ≥0, 0 < (t : ℝ) → ‖ζ‖ ≤ 4 → ∀ᵐ ω ∂reducedLaw Q,
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
          Real.sqrt (∑ j, ‖G t j ω‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)))) :
    Blueprint.node_e_u3A_forced_u2D_localityStmt := by
  intro d hd D
  obtain ⟨C, c, N, hC, hc, hactual⟩ := hactual d hd D
  refine ⟨C, c, N, hC, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, hgrad, happ, hbound⟩ := hactual Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, hgrad, ?_, hbound⟩
  intro t ht ρ hρ
  have hρpos : 0 < ρ := by
    have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hp : 0 < C * Real.sqrt (t : ℝ) := mul_pos (by linarith) hs
    exact hp.trans_le hρ
  obtain ⟨V, H, hV, hH, herr⟩ := happ t ht ρ hρ
  obtain ⟨hcenter, hcube, hcubeG, hcubeerr⟩ :=
    clr_fl_actual_endpoint_center_cube_transfer hd Q ν ζ P Pdag β a μ t ρ C c N
      hρpos (by linarith) (G t) H V hV hH herr
  exact ⟨V, H, hV, hH, herr, hcenter, cubeIntegralObservation Q ρ V,
    (fun j => cubeIntegralObservation Q ρ (H j)), hcube, hcubeG, hcubeerr⟩

/-- Horizontal derivatives are unique. -/
theorem clr_horizontalGradient_unique {d : ℕ} {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {f : Lp ℂ 2 Q} {G G' : Fin d → Lp ℂ 2 Q} (hG : HasComplexHorizontalGradient Q hQ f G)
    (hG' : HasComplexHorizontalGradient Q hQ f G') : G = G' := by
  funext i
  exact tendsto_nhds_unique (hG i) (hG' i)

/-- Monotonicity of the target error shape in its constants. -/
theorem clr_shape_mono {K C' c' C c t ρ z : ℝ} {n N : ℕ} (hK : K ≤ C) (hK0 : 0 ≤ K)
    (hC : C' ≤ C) (hc : c ≤ c') (hn : n ≤ N) (ht : 1 ≤ t) (hz : 0 ≤ z) :
    K * (2 + t) ^ n * Real.exp (C' * z * t - c' * ρ ^ 2 / t) ≤
      C * (2 + t) ^ N * Real.exp (C * z * t - c * ρ ^ 2 / t) := by
  have htp : 0 < t := by linarith
  have hp : (2 + t) ^ n ≤ (2 + t) ^ N := pow_le_pow_right₀ (by linarith) hn
  have he : Real.exp (C' * z * t - c' * ρ ^ 2 / t) ≤ Real.exp (C * z * t - c * ρ ^ 2 / t) := by
    apply Real.exp_le_exp.mpr
    have h1 : C' * (z * t) ≤ C * (z * t) := mul_le_mul_of_nonneg_right hC (by positivity)
    have h2 : c * (ρ ^ 2 / t) ≤ c' * (ρ ^ 2 / t) := mul_le_mul_of_nonneg_right hc (by positivity)
    have e1 : C' * z * t - c' * ρ ^ 2 / t = C' * (z * t) - c' * (ρ ^ 2 / t) := by ring
    have e2 : C * z * t - c * ρ ^ 2 / t = C * (z * t) - c * (ρ ^ 2 / t) := by ring
    rw [e1, e2]; linarith
  have hC0 : 0 ≤ C := hK0.trans hK
  calc K * (2 + t) ^ n * Real.exp (C' * z * t - c' * ρ ^ 2 / t)
      ≤ C * (2 + t) ^ N * Real.exp (C * z * t - c * ρ ^ 2 / t) := by
        gcongr

/-- The two retained-family error terms in the target Gaussian shape. -/
theorem clr_error_shape {d N₁ : ℕ} {A₁ C₁ c₁ A₂ C₂ c₂ κ₁ κ₂ κ' : ℝ} (hA₁ : 0 ≤ A₁)
    (hc₁ : 0 < c₁) (hA₂ : 0 ≤ A₂) (hc₂ : 0 < c₂) (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) :
    ∃ K C c : ℝ, ∃ N : ℕ, 0 ≤ K ∧ 0 < c ∧ C = max C₁ C₂ ∧
    ∀ t ρ z : ℝ, 1 ≤ t → 0 ≤ z →
      A₁ * (2 + t) ^ N₁ * Real.exp (C₁ * z * t) * Real.exp (-(c₁ * (κ₁ * ρ) ^ 2 / (8 * t))) *
          Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d +
        A₂ * (2 + t) * Real.exp (C₂ * z * t - c₂ * (κ₂ * ρ) ^ 2 / t) *
          Real.sqrt (Real.exp 1 * Real.sqrt (Real.pi / (1 / (4 * (κ' * ρ) ^ 2))) ^ d) ≤
      K * (2 + t) ^ N * Real.exp (C * z * t - c * ρ ^ 2 / t) := by
  set K₁ := A₁ * (1 + 2 * Real.pi / c₁) ^ d
  set K₂ := A₂ * (2 * Real.exp 1) * (2 + 4 * Real.pi * κ' ^ 2) ^ d *
    (d.factorial * (2 / (c₂ * κ₂ ^ 2)) ^ d * Real.exp (c₂ * κ₂ ^ 2 / 2))
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  refine ⟨K₁ + K₂, max C₁ C₂, min (c₁ * κ₁ ^ 2 / 8) (c₂ * κ₂ ^ 2 / 2), max (N₁ + d) (1 + d),
    by positivity, lt_min (by positivity) (by positivity), rfl, ?_⟩
  intro t ρ z ht hz
  have h1 := clr_family_term1_le (d := d) (n₁ := N₁) (A₁ := A₁) (C₁ := C₁) (κ := κ₁) (ρ := ρ)
    (z := z) hA₁ hc₁ ht
  have h2 := clr_family_term2_le (d := d) (A₂ := A₂) (C₂ := C₂) (κ := κ₂) (κ' := κ') (ρ := ρ)
    (z := z) hA₂ hc₂ hκ₂ ht
  exact (add_le_add h1 h2).trans (clr_two_gaussian_le hK₁ hK₂ ht hz)

/-- A locally measurable retained family with a differentiable orbit error gives
a joint local approximation of the class and its horizontal gradient. -/
theorem clr_joint_of_family {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ρ εF : ℝ) (hεF : 0 ≤ εF) (U : Lp ℂ 2 (reducedLaw Q))
    (Vt : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hVt : @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
      (borel _) Vt)
    (hE : ∀ᵐ ω ∂reducedLaw Q, ∃ E : Vec d → ℂ, Differentiable ℝ E ∧
      (fun x => U (translate x ω) - Vt ω x) =ᵐ[volume] E ∧
      ∀ x, euclideanNorm x ≤ 2 →
        ‖E x‖ + Real.sqrt (∑ j, ‖fderiv ℝ E x (unitVector j)‖ ^ 2) ≤ εF)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) U G) :
    ∃ V : Lp ℂ 2 (reducedLaw Q), ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
      IsComplexLocalObservation Q ρ V ∧ (∀ j, IsComplexLocalObservation Q ρ (H j)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ + Real.sqrt (∑ j, ‖G j ω - H j ω‖ ^ 2) ≤
        4 * (1 + d) * εF := by
  obtain ⟨V, hV, hVe⟩ := clr_scalar_locality_of_family Q ρ εF hεF U Vt hVt hE
  have hgr := fun j => clr_gradient_locality_of_family Q ρ εF hεF U Vt hVt hE G hG j
  choose H hH hHe using hgr
  refine ⟨V, H, hV, hH, ?_⟩
  have hall : ∀ᵐ ω ∂reducedLaw Q, ∀ j, ‖G j ω - H j ω‖ ≤ 2 * (2 * εF) := by
    rw [ae_all_iff]; exact hHe
  filter_upwards [hVe, hall] with ω h1 h2
  have hsum : (∑ j, ‖G j ω - H j ω‖ ^ 2) ≤ (d * (4 * εF)) ^ 2 := by
    calc (∑ j, ‖G j ω - H j ω‖ ^ 2) ≤ ∑ _j : Fin d, (4 * εF) ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _)
            (by linarith [h2 j]) 2
      _ = d * (4 * εF) ^ 2 := by simp
      _ ≤ (d * (4 * εF)) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h | h
          · simp [h]
          · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h
            nlinarith [sq_nonneg (4 * εF)]
  have hsq : Real.sqrt (∑ j, ‖G j ω - H j ω‖ ^ 2) ≤ d * (4 * εF) :=
    (Real.sqrt_le_sqrt hsum).trans (le_of_eq (Real.sqrt_sq (by positivity)))
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith


/-- From a joint approximation with error `4 (1 + d) εF` to the target shape. -/
theorem clr_joint_finish {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (U : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    {ρ εF K Cm cm Cdet c z t : ℝ} {Nm N : ℕ}
    (hJ : ∃ V : Lp ℂ 2 (reducedLaw Q), ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
      IsComplexLocalObservation Q ρ V ∧ (∀ j, IsComplexLocalObservation Q ρ (H j)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ + Real.sqrt (∑ j, ‖G j ω - H j ω‖ ^ 2) ≤
        4 * (1 + d) * εF)
    (hε : εF ≤ K * (2 + t) ^ Nm * Real.exp (Cm * z * t - cm * ρ ^ 2 / t))
    (hK0 : 0 ≤ K) (hK : 4 * (1 + d) * K ≤ Cdet) (hC : Cm ≤ Cdet) (hc : c ≤ cm)
    (hN : Nm ≤ N) (ht : 1 ≤ t) (hz : 0 ≤ z) :
    ∃ V : Lp ℂ 2 (reducedLaw Q), ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
      IsComplexLocalObservation Q ρ V ∧ (∀ j, IsComplexLocalObservation Q ρ (H j)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ + Real.sqrt (∑ j, ‖G j ω - H j ω‖ ^ 2) ≤
        Cdet * (2 + t) ^ N * Real.exp (Cdet * z * t - c * ρ ^ 2 / t) := by
  obtain ⟨V, H, hV, hH, herr⟩ := hJ
  refine ⟨V, H, hV, hH, ?_⟩
  filter_upwards [herr] with ω h
  refine h.trans ?_
  have hd : (0 : ℝ) ≤ 4 * (1 + d) := by positivity
  calc 4 * (1 + d) * εF ≤ 4 * (1 + d) *
        (K * (2 + t) ^ Nm * Real.exp (Cm * z * t - cm * ρ ^ 2 / t)) :=
        mul_le_mul_of_nonneg_left hε hd
    _ = (4 * (1 + d) * K) * (2 + t) ^ Nm * Real.exp (Cm * z * t - cm * ρ ^ 2 / t) := by ring
    _ ≤ _ := clr_shape_mono hK (by positivity) hC hc hN ht hz

/-- Monotonicity of the crude shape in its constants. -/
theorem clr_crude_mono {K C z t : ℝ} {n N : ℕ} (hK0 : 0 ≤ K) (hK : K ≤ C) (hn : n ≤ N)
    (ht : 0 ≤ t) (hz : 0 ≤ z) :
    K * (2 + t) ^ n * Real.exp (K * z * t) ≤ C * (2 + t) ^ N * Real.exp (C * z * t) := by
  have hp : (2 + t) ^ n ≤ (2 + t) ^ N := pow_le_pow_right₀ (by linarith) hn
  have he : Real.exp (K * z * t) ≤ Real.exp (C * z * t) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hK (mul_nonneg hz ht)
    calc K * z * t = K * (z * t) := by ring
      _ ≤ C * (z * t) := this
      _ = C * z * t := by ring
  have hC0 : 0 ≤ C := hK0.trans hK
  gcongr

/-- The force weight is absorbed into the Gaussian growth at times at least one. -/
theorem clr_one_add_le_exp {x t : ℝ} (ht : 1 ≤ t) :
    1 + x ≤ 2 * Real.exp (x ^ 2 * t) := by
  have h1 : x ^ 2 + 1 ≤ Real.exp (x ^ 2) := Real.add_one_le_exp _
  have h2 : Real.exp (x ^ 2) ≤ Real.exp (x ^ 2 * t) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
  nlinarith [sq_nonneg (x - 1 / 4)]

theorem clr_weight_exp_le {w z t C E : ℝ} (hw : w ≤ 2 * Real.exp (z * t)) :
    w * Real.exp (C * z * t - E) ≤ 2 * Real.exp ((C + 1) * z * t - E) := by
  have h : Real.exp ((C + 1) * z * t - E) = Real.exp (z * t) * Real.exp (C * z * t - E) := by
    rw [← Real.exp_add]; ring_nf
  rw [h]
  have := Real.exp_pos (C * z * t - E)
  nlinarith

/-- The forward family error, with its force-weighted datum, in the shape of
`clr_error_shape`. -/
theorem clr_forward_error_absorb {d N₁ : ℕ} {C₁ c₁ C₂ c₂ B₀ t ρ z w : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hB₀ : 0 ≤ B₀) (ht : 0 ≤ t)
    (hw : w ≤ 2 * Real.exp (z * t)) :
    (1 + d) * (C₁ * (2 + t) ^ N₁ * Real.exp (C₁ * z * t) * (B₀ * w) *
        Real.exp (-(c₁ * (ρ / 10) ^ 2 / (8 * t))) * Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d) +
      C₂ * (2 + t) * Real.exp (C₂ * z * t - c₂ * (ρ / 10) ^ 2 / t) *
        (B₀ * w * Real.sqrt (Real.exp 1 * Real.sqrt (Real.pi / (1 / (4 * (ρ / 10) ^ 2))) ^ d)) ≤
    (2 * ((1 + d) * C₁ * B₀)) * (2 + t) ^ N₁ * Real.exp ((C₁ + 1) * z * t) *
        Real.exp (-(c₁ * (1 / 10 * ρ) ^ 2 / (8 * t))) * Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d +
      (2 * (C₂ * B₀)) * (2 + t) * Real.exp ((C₂ + 1) * z * t - c₂ * (1 / 10 * ρ) ^ 2 / t) *
        Real.sqrt (Real.exp 1 * Real.sqrt (Real.pi / (1 / (4 * (1 / 10 * ρ) ^ 2))) ^ d) := by
  have hρ10 : ρ / 10 = 1 / 10 * ρ := by ring
  rw [hρ10]
  have e1 : w * Real.exp (C₁ * z * t - 0) ≤ 2 * Real.exp ((C₁ + 1) * z * t - 0) :=
    clr_weight_exp_le hw
  simp only [sub_zero] at e1
  have e2 := clr_weight_exp_le (C := C₂) (E := c₂ * (1 / 10 * ρ) ^ 2 / t) hw
  set G₁ := Real.exp (-(c₁ * (1 / 10 * ρ) ^ 2 / (8 * t))) * Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d
  set S₂ := Real.sqrt (Real.exp 1 * Real.sqrt (Real.pi / (1 / (4 * (1 / 10 * ρ) ^ 2))) ^ d)
  have hG₁ : 0 ≤ G₁ := by positivity
  have hS₂ : 0 ≤ S₂ := by positivity
  have hd0 : (0 : ℝ) ≤ 1 + d := by positivity
  calc (1 + d) * (C₁ * (2 + t) ^ N₁ * Real.exp (C₁ * z * t) * (B₀ * w) *
        Real.exp (-(c₁ * (1 / 10 * ρ) ^ 2 / (8 * t))) * Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d) +
      C₂ * (2 + t) * Real.exp (C₂ * z * t - c₂ * (1 / 10 * ρ) ^ 2 / t) * (B₀ * w * S₂)
      = (1 + d) * C₁ * B₀ * (2 + t) ^ N₁ * G₁ * (w * Real.exp (C₁ * z * t)) +
        C₂ * B₀ * (2 + t) * S₂ * (w * Real.exp (C₂ * z * t - c₂ * (1 / 10 * ρ) ^ 2 / t)) := by
        rw [show G₁ = Real.exp (-(c₁ * (1 / 10 * ρ) ^ 2 / (8 * t))) *
          Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d from rfl]
        ring
    _ ≤ (1 + d) * C₁ * B₀ * (2 + t) ^ N₁ * G₁ * (2 * Real.exp ((C₁ + 1) * z * t)) +
        C₂ * B₀ * (2 + t) * S₂ *
          (2 * Real.exp ((C₂ + 1) * z * t - c₂ * (1 / 10 * ρ) ^ 2 / t)) := by
        have hA : 0 ≤ (1 + d) * C₁ * B₀ * (2 + t) ^ N₁ * G₁ := by positivity
        have hB : 0 ≤ C₂ * B₀ * (2 + t) * S₂ := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left e1 hA) (mul_le_mul_of_nonneg_left e2 hB)
    _ = _ := by
        rw [show G₁ = Real.exp (-(c₁ * (1 / 10 * ρ) ^ 2 / (8 * t))) *
          Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d from rfl]
        ring

/-- Large-time locality of every actual endpoint and any horizontal gradient of
it, at every force. -/
theorem clr_large_time_locality
    (hcut : node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C c : ℝ, ∃ N : ℕ, 480 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) G →
    ∀ ρ : ℝ, C * Real.sqrt (t : ℝ) ≤ ρ →
      ∃ V : Lp ℂ 2 (reducedLaw Q), ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
      IsComplexLocalObservation Q ρ V ∧ (∀ j, IsComplexLocalObservation Q ρ (H j)) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - V ω‖ +
          Real.sqrt (∑ j, ‖G j ω - H j ω‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) := by
  obtain ⟨C₁, c₁, C₂, c₂, B₀, N₁, hC₁, hc₁, hC₂, hc₂, hB₀, hF⟩ :=
    clr_forward_clock_retained_family hcut d hd D
  obtain ⟨C₁', c₁', C₂', c₂', B₀', B₁', N₁', hC₁', hc₁', hC₂', hc₂', hB₀', hB₁', hT⟩ :=
    clr_transpose_retained_family hcut d hd D
  obtain ⟨K, Cm, cm, Nm, hK, hcm, hCm, hshape⟩ := clr_error_shape (d := d) (N₁ := N₁)
    (A₁ := 2 * ((1 + d) * C₁ * B₀)) (C₁ := C₁ + 1) (c₁ := c₁) (A₂ := 2 * (C₂ * B₀))
    (C₂ := C₂ + 1) (c₂ := c₂)
    (κ₁ := 1 / 10) (κ₂ := 1 / 10) (κ' := 1 / 10) (by positivity) hc₁ (by positivity) hc₂
    (by norm_num) (by norm_num)
  obtain ⟨K', Cm', cm', Nm', hK', hcm', hCm', hshape'⟩ := clr_error_shape (d := d) (N₁ := N₁')
    (A₁ := (1 + d) * C₁' * (B₀' + B₁')) (C₁ := C₁') (c₁ := c₁') (A₂ := C₂' * B₁') (C₂ := C₂')
    (c₂ := c₂') (κ₁ := 1 / 40) (κ₂ := 1 / 40) (κ' := 1 / 20) (by positivity) hc₁'
    (by positivity) hc₂' (by norm_num) (by norm_num)
  set Cdet := max 480 (max (4 * (1 + d) * K) (max (4 * (1 + d) * K') (max Cm Cm')))
  have h480 : 480 ≤ Cdet := le_max_left _ _
  have hKC : 4 * (1 + d) * K ≤ Cdet := (le_max_left _ _).trans (le_max_right _ _)
  have hKC' : 4 * (1 + d) * K' ≤ Cdet :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCmC : Cm ≤ Cdet := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hCmC' : Cm' ≤ Cdet := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨Cdet, min cm cm', max Nm Nm', h480, lt_min hcm hcm', ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht G hG ρ hρ
  have hρ480 : 480 ≤ ρ := by
    have hs : 1 ≤ Real.sqrt (t : ℝ) := Real.one_le_sqrt.mpr ht
    nlinarith
  have hz : 0 ≤ ‖ζ‖ ^ 2 := sq_nonneg _
  have hw : 1 + ‖ζ‖ ≤ 2 * Real.exp (‖ζ‖ ^ 2 * (t : ℝ)) := clr_one_add_le_exp ht
  have hρ20 : ρ / 20 = 1 / 20 * ρ := by ring
  have hρ40 : ρ / 40 = 1 / 40 * ρ := by ring
  rcases ν with j | b
  · obtain ⟨Vt, hVt, hE⟩ := hF Q hQ β a μ hβ ha hμ ζ P hP (Sum.inl j) t ht ρ (by linarith)
    refine clr_joint_finish Q _ G (clr_joint_of_family Q ρ _ (by positivity) _ Vt hVt hE G hG)
      ?_ hK hKC hCmC (min_le_left _ _) (le_max_left _ _) ht hz
    exact (clr_forward_error_absorb (by linarith) (by linarith) hB₀.le t.coe_nonneg hw).trans
      (hshape t ρ _ ht hz)
  · cases b with
    | false =>
      obtain ⟨Vt, hVt, hE⟩ := hF Q hQ β a μ hβ ha hμ ζ P hP (Sum.inr ()) t ht ρ
        (by linarith)
      have hU : uncenteredEndpoint hd Q (Sum.inr false) ζ P Pdag β a μ t = P t (ζ • μ) := by
        simp only [uncenteredEndpoint, map_smul]
      rw [hU] at hG ⊢
      refine clr_joint_finish Q _ G (clr_joint_of_family Q ρ _ (by positivity) _ Vt hVt hE G hG)
        ?_ hK hKC hCmC (min_le_left _ _) (le_max_left _ _) ht hz
      exact (clr_forward_error_absorb (by linarith) (by linarith) hB₀.le t.coe_nonneg hw).trans
        (hshape t ρ _ ht hz)
    | true =>
      obtain ⟨Vt, hVt, hE⟩ := hT Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht ρ hρ480
      refine clr_joint_finish Q _ G (clr_joint_of_family Q ρ _ (by positivity) _ Vt hVt hE G hG)
        ?_ hK' hKC' hCmC' (min_le_right _ _) (le_max_right _ _) ht hz
      refine le_of_eq_of_le ?_ (hshape' t ρ _ ht hz)
      rw [hρ20, hρ40]; ring

/-- Remaining input: the crude endpoint and gradient bound for `0 < t < 1`. -/
def ClrSmallTimeCrude : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, 0 < (t : ℝ) → (t : ℝ) < 1 → ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) G →
      ∀ᵐ ω ∂reducedLaw Q,
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
          Real.sqrt (∑ j, ‖G j ω‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))

/-- `e:forced-locality` from its graph dependencies and the small-time crude bound. -/
theorem clr_forced_locality_of_small_time (hS : ClrSmallTimeCrude) :
    node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt →
    node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt →
    node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt →
    node_e_u3A_local_u2D_timeStmt →
    node_e_u3A_forced_u2D_localityStmt := by
  intro hcut _hoff hpoint hlocal
  apply clr_fl_of_joint_approximation
  intro d hd D
  obtain ⟨Cb, cb, Nb, hCb, hcb, hB⟩ := clr_large_time_locality hcut d hd D
  obtain ⟨Cc, Nc, hCc, hCr⟩ := node_l_u3A_forced_u2D_local_u23_crude_u2D_energy_of_deps hpoint d hd D
  obtain ⟨Cs, Ns, hCs, hSd⟩ := hS d hd D
  obtain ⟨Ct, Cp, hCt, hCp, hTm⟩ := hlocal d hd D 2 le_rfl
  set C := max Cb (max Cc Cs)
  set N := max Nb (max Nc Ns)
  have hCbC : Cb ≤ C := le_max_left _ _
  have hCcC : Cc ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCsC : Cs ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hNb : Nb ≤ N := le_max_left _ _
  have hNc : Nc ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hNs : Ns ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, cb, N, by linarith, hcb, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, V, hGV, -⟩ := hTm Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G', hG', hcr⟩ := hCr Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  have hz : 0 ≤ ‖ζ‖ ^ 2 := sq_nonneg _
  refine ⟨G, fun t ht => ⟨(hGV t ht).1, (hGV t ht).2.1⟩, ?_, ?_⟩
  · intro t ht ρ hρ
    have hs : 0 ≤ Real.sqrt (t : ℝ) := Real.sqrt_nonneg _
    obtain ⟨V, H, hV, hH, herr⟩ := hB Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht (G t)
      (hGV t (by linarith)).2.1 ρ ((mul_le_mul_of_nonneg_right hCbC hs).trans hρ)
    refine ⟨V, H, hV, hH, ?_⟩
    filter_upwards [herr] with ω h
    exact h.trans (clr_shape_mono hCbC (by linarith) hCbC le_rfl hNb ht hz)
  · intro t ht hζ
    have hGt := (hGV t ht).2.1
    rcases lt_or_ge (t : ℝ) 1 with h1 | h1
    · filter_upwards [hSd Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν t ht h1 (G t) hGt]
        with ω h
      exact h.trans (clr_crude_mono (by linarith) hCsC hNs t.coe_nonneg hz)
    · have hGG : G' t = G t := clr_horizontalGradient_unique (hG' t h1) hGt
      filter_upwards [(hcr t h1 hζ).1] with ω h
      rw [hGG] at h
      exact h.trans (clr_crude_mono (by linarith) hCcC hNc t.coe_nonneg hz)

end EinsteinFull
