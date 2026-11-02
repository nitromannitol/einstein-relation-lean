import EinsteinFull.Calculus.C4CrudeEnergyFirstStrip
import EinsteinFull.Calculus.CLForcedLocalityAssembly

/-! The crude endpoint and gradient bound of `e:forced-locality` for `0 < t < 1`.
The first-strip energy argument is valid from time zero; only the time window of
its exported statement changes. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

open private firstStrip_ae_lt_twice_of_pow_integrals firstStrip_endpoint_trace_radial_energy_bound
  firstStrip_initial_power_prefactor_bound firstStrip_initial_trace_packed_bound
  firstStrip_integral_gronwall_of_positive_intervals firstStripGradient firstStripGradient_spec
  firstStripHilbertPrimitive firstStripHilbertPrimitive_integrable
  firstStripHilbertPrimitive_le_initial_bound firstStripSystem_energy_tendsto
  firstStripSystem_moment_of_primitive_bound firstStripSystemPack firstStripSystemPack_coe
  firstStripTimeGradient_eq from EinsteinFull.Calculus.C4CrudeEnergyFirstStrip

/-- The first-strip moment bounds at every time `0 < t < 2`. -/
theorem clr_small_radial_moments :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
    IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P),
    IsComplexTransposeSemigroup Q P Pdag → ∀ (ν : EndpointIndex d),
    ∀ p : ℝ, 2 ≤ p → ∀ t : ℝ≥0, 0 < (t : ℝ) → (t : ℝ) < 2 → ‖ζ‖ ≤ 4 →
    let E : FieldPair d → ℝ := fun ω =>
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ^ 2 +
      ∑ j : Fin d, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2
    Integrable (fun ω => E ω ^ (p / 2)) (reducedLaw Q) ∧
      (∫ ω, E ω ^ (p / 2) ∂reducedLaw Q) ≤
        C ^ p * Real.exp (C * p * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) := by
  intro d hd D
  obtain ⟨C₀, hC₀, hb⟩ := firstStrip_endpoint_trace_radial_energy_bound D
  obtain ⟨M, hM, hMb⟩ := firstStrip_initial_trace_packed_bound hd D
  let C := max 1 (max (Real.exp 1 * (1 + M ^ 2)) C₀)
  have hC : 1 ≤ C := le_max_left _ _
  have hCM : Real.exp 1 * (1 + M ^ 2) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCC : C₀ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hT ν p hp t ht ht₂ hζ
  have := reducedLaw_probability Q
  obtain ⟨G, hGc, hG, hGe, hb⟩ := hb hd Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hT ν
  let F : ℝ → Fin (d + 1) → Lp ℂ 2 (reducedLaw Q) := fun u => Fin.cons (uncenteredEndpoint hd Q ν ζ P Pdag β a μ u.toNNReal)
    (fun j => G u j)
  have hFc : Continuous F := by
    apply continuous_pi
    intro q
    refine Fin.cases ?_ (fun j => ?_) q
    · cases ν with
      | inl k => exact (hP.2.2.1 _).comp continuous_real_toNNReal
      | inr b =>
        cases b with
        | false =>
          change Continuous (fun s : ℝ => ζ • P s.toNNReal μ)
          exact ((hP.2.2.1 μ).comp continuous_real_toNNReal).const_smul ζ
        | true => exact (hT.continuous_apply hP _).comp continuous_real_toNNReal
    · exact (PiLp.continuous_apply 2 _ j).comp hGc
  let α := p / 2 - 1
  have hα : 0 ≤ α := by dsimp only [α]; linarith
  have hαp : α + 1 = p / 2 := by dsimp only [α]; ring
  let A₀ := (1 / 2 : ℝ) * M ^ 2 * (1 + M ^ 2) ^ α
  let B := A₀ * Real.exp (C₀ * (1 + α) * (t : ℝ))
  have hA₀ : 0 ≤ A₀ := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (Real.rpow_nonneg (by positivity) _)
  have hB : 0 ≤ B := mul_nonneg hA₀ (Real.exp_pos _).le
  have hini := hMb Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hT ν (fun j => G 0 j)
    (by simpa using hG 0)
  have he (n : ℕ) : (∫ ω, firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
      ((n : ℝ) + 1) α
      (WithLp.toLp 2 (fun q => F (t : ℝ) q ω) : EuclideanSpace ℂ (Fin (d + 1)))
        ∂reducedLaw Q) ≤ B := by
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hε : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr hN
    have hε₁ : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
      (inv_le_one₀ hN).mpr (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    let en := fun u => ∫ ω, firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
      ((n : ℝ) + 1) α
      (WithLp.toLp 2 (fun q => F u q ω) : EuclideanSpace ℂ (Fin (d + 1))) ∂reducedLaw Q
    have henc : Continuous en := continuous_iff_continuousAt.mpr fun u =>
      firstStripSystem_energy_tendsto hFc.continuousAt hε hN hα
    have hen₀ : en 0 ≤ A₀ := by
      have hi : Integrable (fun ω => firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
          ((n : ℝ) + 1) α
          (WithLp.toLp 2 (fun q => F 0 q ω) : EuclideanSpace ℂ (Fin (d + 1))))
          (reducedLaw Q) :=
        (firstStripHilbertPrimitive_integrable (reducedLaw Q)
          (firstStripSystemPack (reducedLaw Q) (d + 1) (F 0)) hε hN hα).congr
          ((firstStripSystemPack_coe (reducedLaw Q) (d + 1) (F 0)).fun_comp
            (firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) α))
      have hiBound : (fun ω => firstStripHilbertPrimitive ((n : ℝ) + 1)⁻¹
          ((n : ℝ) + 1) α
          (WithLp.toLp 2 (fun q => F 0 q ω) : EuclideanSpace ℂ (Fin (d + 1)))) ≤ᵐ[reducedLaw Q]
          fun _ => A₀ := by
        filter_upwards [hini] with ω hω
        have hF₀ : (fun q => F 0 q ω) =
            Fin.cons (uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 ω) (fun j => G 0 j ω) := by
          funext q
          refine Fin.cases ?_ (fun j => ?_) q <;>
            simp only [F, Fin.cons_zero, Fin.cons_succ, Real.toNNReal_zero]
        rw [hF₀]
        apply (firstStripHilbertPrimitive_le_initial_bound hε hN hα hM _ hω).trans
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
          (by linarith : ((n : ℝ) + 1)⁻¹ + M ^ 2 ≤ 1 + M ^ 2) hα)
          (mul_nonneg (by norm_num) (sq_nonneg _))
      simpa using integral_mono_ae hi (integrable_const A₀) hiBound
    have hg := firstStrip_integral_gronwall_of_positive_intervals henc
      (mul_nonneg (le_trans zero_le_one hC₀) (by linarith : 0 ≤ 1 + α))
      (fun u₀ u₁ hu₀ hu => hb _ _ _ hε hN hα u₀ u₁ hu₀ hu) (t : ℝ) t.coe_nonneg
    exact hg.trans (mul_le_mul_of_nonneg_right hen₀ (Real.exp_pos _).le)
  obtain ⟨hi, hb⟩ := firstStripSystem_moment_of_primitive_bound (reducedLaw Q)
    (F (t : ℝ)) hα hB he
  have hgrad : (fun j => G (t : ℝ) j) = firstStripGradient hd Q β a μ ζ P Pdag hP ν t := by
    have he := firstStripTimeGradient_eq hd Q β a μ ζ P Pdag hP ν
      (show 0 < (t : ℝ) by linarith)
    simpa only [Real.toNNReal_coe] using (congrArg (fun g => fun j => g j)
      (hGe (t : ℝ) (by linarith))).trans he
  have hE (ω : FieldPair d) : (∑ q, ‖F (t : ℝ) q ω‖ ^ 2) =
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ^ 2 +
        ∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2 := by
    simp only [F, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Real.toNNReal_coe]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [congrFun hgrad j]
  refine ⟨?_, ?_⟩
  · simpa only [hE, hαp] using hi
  · have hpref : 2 * (α + 1) * A₀ ≤ C ^ p := by
      have h := firstStrip_initial_power_prefactor_bound (M := M) hp
      have hpC := Real.rpow_le_rpow (by positivity : 0 ≤ Real.exp 1 * (1 + M ^ 2)) hCM
        (by linarith : 0 ≤ p)
      calc
        _ = (p / 2) * M ^ 2 * (1 + M ^ 2) ^ (p / 2 - 1) := by dsimp only [A₀, α]; ring
        _ ≤ (Real.exp 1 * (1 + M ^ 2)) ^ p := h
        _ ≤ C ^ p := hpC
    have hexp : Real.exp (C₀ * (1 + α) * (t : ℝ)) ≤
        Real.exp (C * p * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ t.coe_nonneg
      have hrate : C₀ * (p / 2) ≤ C * p := by
        calc
          _ ≤ C * (p / 2) := mul_le_mul_of_nonneg_right hCC (by linarith)
          _ ≤ C * p := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have hs : C * p ≤ C * p * (1 + ‖ζ‖ ^ 2) := by
        have hz := mul_nonneg (mul_nonneg (show 0 ≤ C by linarith)
          (show 0 ≤ p by linarith)) (sq_nonneg ‖ζ‖)
        nlinarith
      have hα' : 1 + α = p / 2 := by linarith [hαp]
      rw [hα']
      exact hrate.trans hs
    have htotal : 2 * (α + 1) * B ≤
        C ^ p * Real.exp (C * p * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) := by
      dsimp only [B]
      rw [← mul_assoc]
      exact mul_le_mul hpref hexp (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)
    simpa only [hE, hαp] using hb.trans htotal


/-- The crude bound for `0 < t < 1`, for any horizontal gradient of the endpoint. -/
theorem clr_small_time_crude : EinsteinFull.ClrSmallTimeCrude := by
  intro d hd D
  obtain ⟨C₀, hC₀, hb⟩ := clr_small_radial_moments d hd D
  let C := max 1 (8 * C₀ * Real.exp (2 * C₀))
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀n : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hCbase : 8 * C₀ * Real.exp (2 * C₀) ≤ C := le_max_right _ _
  have hCC : C₀ ≤ C := by
    have he := Real.one_le_exp (show 0 ≤ 2 * C₀ by positivity)
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 8 * C₀ by positivity)
    nlinarith
  refine ⟨C, 0, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hT ν t ht ht₁ G hG
  have ht₂ : (t : ℝ) < 2 := by linarith
  have hGe : G = firstStripGradient hd Q β a μ ζ P Pdag hP ν t :=
    EinsteinFull.clr_horizontalGradient_unique hG
      (firstStripGradient_spec hd Q hQ β a μ ζ P Pdag hP hT hβ ν t (NNReal.coe_pos.mp ht))
  subst hGe
  let E := fun ω : FieldPair d => ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ^ 2 +
    ∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2
  let K := C₀ * Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ))
  have hK : 0 < K := mul_pos hC₀n (Real.exp_pos _)
  have hpow (n : ℕ) : C₀ ^ (2 * ((n : ℝ) + 1)) *
      Real.exp (C₀ * (2 * ((n : ℝ) + 1)) * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) =
      (K ^ 2) ^ (n + 1) := by
    have hCpow : C₀ ^ (2 * ((n : ℝ) + 1)) = C₀ ^ (2 * (n + 1) : ℕ) := by
      rw [← Real.rpow_natCast]
      congr 1
      push_cast
      rfl
    have hepow : Real.exp (C₀ * (2 * ((n : ℝ) + 1)) * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) =
        Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) ^ (2 * (n + 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc
      _ = C₀ ^ (2 * (n + 1)) *
          Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) ^ (2 * (n + 1)) :=
        congrArg₂ (fun x y : ℝ => x * y) hCpow hepow
      _ = K ^ (2 * (n + 1)) := (mul_pow _ _ _).symm
      _ = (K ^ 2) ^ (n + 1) := pow_mul _ _ _
  have hm (n : ℕ) : Integrable (fun ω => E ω ^ (n + 1)) (reducedLaw Q) ∧
      (∫ ω, E ω ^ (n + 1) ∂reducedLaw Q) ≤ (K ^ 2) ^ (n + 1) := by
    have hn : 2 ≤ 2 * ((n : ℝ) + 1) := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
    have h := hb Q hQ β a μ hβ ha hμ ζ P Pdag hP hT ν
      (2 * ((n : ℝ) + 1)) hn t ht ht₂ hζ
    have hp : (2 * ((n : ℝ) + 1)) / 2 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    simpa only [hp, Real.rpow_natCast, hpow] using h
  have hae := firstStrip_ae_lt_twice_of_pow_integrals (reducedLaw Q) E
    (sq_pos_of_pos hK) (fun ω => add_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (fun n => (hm n).1) (fun n => (hm n).2)
  have hpoint : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
      Real.sqrt (∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2) ≤ 4 * K := by
    filter_upwards [hae] with ω hω
    have hS : 0 ≤ ∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs := Real.sq_sqrt hS
    have hn := norm_nonneg (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω)
    have hr := Real.sqrt_nonneg (∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2)
    dsimp only [E] at hω
    apply (sq_le_sq₀ (add_nonneg hn hr) (by positivity : 0 ≤ 4 * K)).mp
    nlinarith [sq_nonneg (‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ -
      Real.sqrt (∑ j, ‖firstStripGradient hd Q β a μ ζ P Pdag hP ν t j ω‖ ^ 2))]
  have hfinal : 2 * (4 * K) ≤ C * (2 + (t : ℝ)) ^ (0 : ℕ) *
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    have hexp : Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) ≤
        Real.exp (2 * C₀) * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hCC
        (mul_nonneg (sq_nonneg ‖ζ‖) t.coe_nonneg)
      have ht' := mul_le_mul_of_nonneg_left ht₂.le hC₀n.le
      nlinarith
    calc
      _ = (8 * C₀) * Real.exp (C₀ * (1 + ‖ζ‖ ^ 2) * (t : ℝ)) := by dsimp only [K]; ring
      _ ≤ (8 * C₀) * (Real.exp (2 * C₀) * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ C * (2 + (t : ℝ)) ^ (0 : ℕ) * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
        simp only [pow_zero, mul_one]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hCbase (Real.exp_pos _).le
  exact hpoint.mono (fun ω hω => hω.trans ((le_mul_of_one_le_left
    (show 0 ≤ 4 * K by positivity) (by norm_num : (1 : ℝ) ≤ 2)).trans hfinal))

/-- Graph reduction of `e:forced-locality`, `paper/main.tex:715`. -/
theorem node_e_u3A_forced_u2D_locality_of_deps :
    node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt →
    node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt →
    node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt →
    node_e_u3A_local_u2D_timeStmt →
    node_e_u3A_forced_u2D_localityStmt :=
  EinsteinFull.clr_forced_locality_of_small_time clr_small_time_crude

end EinsteinFull.Blueprint
