import EinsteinFull.Calculus.C10DyadicLargeWindowProjection
import EinsteinFull.Blueprint.Foundation.node_e_u3A_forced_u2D_locality
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-! Joint-locality specialization of the large-window projection argument.
The estimates below use only the source locality premise, without the additional
regularity conclusions in the full forced-local-estimates statement. -/
namespace C8LargeWindow
private theorem projection_errors_of_joint_bound
    {d : ℕ} {Λ r₀ ρ B : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (U Uloc : Lp ℂ 2 (reducedLaw Q))
    (H Hloc : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hUloc : IsComplexLocalObservation Q ρ Uloc)
    (hHloc : ∀ j, IsComplexLocalObservation Q ρ (Hloc j))
    (hB : 0 ≤ B)
    (hb : ∀ᵐ ω ∂reducedLaw Q, ‖U ω - Uloc ω‖ +
      Real.sqrt (∑ j, ‖H j ω - Hloc j ω‖ ^ 2) ≤ B) :
    ‖U - C9ShortTimeLocality.localProjection Q ρ U‖ ≤ 2 * B ∧
    ∀ j, ‖H j - C9ShortTimeLocality.localProjection Q ρ (H j)‖ ≤ 2 * B := by
  have scalar : ‖U - Uloc‖ ≤ B := by
    have h := Lp.norm_le_of_ae_bound hB (f := U - Uloc) (by
      filter_upwards [hb, Lp.coeFn_sub U Uloc] with ω hω he
      rw [he]
      exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hω)
    simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one,
      NNReal.coe_one, Real.one_rpow, one_mul] using h
  refine ⟨(C9ShortTimeLocality.norm_sub_localProjection_le Q ρ hUloc).trans
    (mul_le_mul_of_nonneg_left scalar (by norm_num)), ?_⟩
  intro j
  have coord : ‖H j - Hloc j‖ ≤ B := by
    have h := Lp.norm_le_of_ae_bound hB (f := H j - Hloc j) (by
      filter_upwards [hb, Lp.coeFn_sub (H j) (Hloc j)] with ω hω he
      rw [he]
      have hj : ‖H j ω - Hloc j ω‖ ≤
          Real.sqrt (∑ k, ‖H k ω - Hloc k ω‖ ^ 2) :=
        Real.le_sqrt_of_sq_le (Finset.single_le_sum
          (fun k _ => sq_nonneg ‖H k ω - Hloc k ω‖) (Finset.mem_univ j))
      exact hj.trans ((le_add_of_nonneg_left (norm_nonneg _)).trans hω))
    simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one,
      NNReal.coe_one, Real.one_rpow, one_mul] using h
  exact (C9ShortTimeLocality.norm_sub_localProjection_le Q ρ (hHloc j)).trans
    (mul_le_mul_of_nonneg_left coord (by norm_num))

private theorem dyadic_gaussian_envelope
    (C c s t ρ z : ℝ) (N : ℕ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hs : 1 ≤ s) (hst : s ≤ t) (hts : t ≤ 2*s)
    (hz : 0 ≤ z) (hforce : z * Real.sqrt (2*s) ≤ 2) :
    C * (2+t)^N * Real.exp (C*z^2*t - c*ρ^2/t) ≤
      (C * 2^N * Real.exp (4*C)) * (2+s)^N *
        Real.exp (-(c/2)*ρ^2/s) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : 0 < t := hs0.trans_le hst
  have hsqrt : (Real.sqrt (2*s))^2 = 2*s := Real.sq_sqrt (by positivity)
  have hzz : z^2 * t ≤ 4 := by
    have hnonneg : 0 ≤ z * Real.sqrt (2*s) := by positivity
    have hsq : (z * Real.sqrt (2*s))^2 ≤ 2^2 :=
      (sq_le_sq₀ hnonneg (by norm_num)).mpr hforce
    rw [mul_pow, hsqrt] at hsq
    nlinarith [mul_le_mul_of_nonneg_left hts (sq_nonneg z)]
  have hdecay : -(c*ρ^2/t) ≤ -(c/2)*ρ^2/s := by
    apply (le_div_iff₀ hs0).2
    rw [← neg_div, div_mul_eq_mul_div]
    apply (div_le_iff₀ ht0).2
    nlinarith [mul_le_mul_of_nonneg_left hts (mul_nonneg hc (sq_nonneg ρ))]
  have he : Real.exp (C*z^2*t - c*ρ^2/t) ≤
      Real.exp (4*C) * Real.exp (-(c/2)*ρ^2/s) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcz := mul_le_mul_of_nonneg_left hzz hC
    nlinarith
  have hp : (2+t)^N ≤ 2^N * (2+s)^N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) N
  calc
    _ ≤ C * (2^N * (2+s)^N) *
        (Real.exp (4*C) * Real.exp (-(c/2)*ρ^2/s)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hC) he
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Localization of a literal coefficient row plus the signed transpose
correction, using coordinate bounds on the integrated projection errors. -/
private theorem fluxCombination_projection_error_le
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ ρ E : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (hρ : 0 < ρ) (ζ : ℂ) (hz : ‖ζ‖ ≤ 2) (ν : FluxIndex d) (j : Fin d)
    (H : Fin d → Lp ℂ 2 (reducedLaw Q)) (U : Lp ℂ 2 (reducedLaw Q))
    (hE : 0 ≤ E)
    (hH : ∀ k, ‖H k - C9ShortTimeLocality.localProjection Q ρ (H k)‖ ≤ E)
    (hU : ‖U - C9ShortTimeLocality.localProjection Q ρ U‖ ≤ E) :
    let f := (∑ k, complexCoefficientMul Q j k (H k)) -
      ν.elim (fun _ => 0) (fun _ => (2*ζ) • complexCoefficientMul Q j ⟨0, by omega⟩ U)
    ‖f - C9ShortTimeLocality.localProjection Q ρ f‖ ≤
      2 * ((d : ℝ)+4) * (Real.exp (2*Λ)*Λ) * E := by
  let L := C9ShortTimeLocality.localProjection Q ρ
  let K := Real.exp (2*Λ)*Λ
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter)
  let v := (∑ k, complexCoefficientMul Q j k (L (H k))) -
    ν.elim (fun _ => 0) (fun _ => (2*ζ) • complexCoefficientMul Q j ⟨0, by omega⟩ (L U))
  have hv : IsComplexLocalObservation Q ρ v :=
    C9DyadicIncrements.fluxCombination_isLocal Q hd hρ ζ ν j _ _
      (fun k => C9ShortTimeLocality.localProjection_isLocal Q ρ (H k))
      (C9ShortTimeLocality.localProjection_isLocal Q ρ U)
  have hmul (k : Fin d) (w : Lp ℂ 2 (reducedLaw Q)) :
      ‖complexCoefficientMul Q j k w‖ ≤ K * ‖w‖ :=
    ((complexCoefficientMul Q j k).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_complexCoefficientMul_le Q j k) (norm_nonneg _))
  have hrow : ‖∑ k, complexCoefficientMul Q j k (H k - L (H k))‖ ≤
      (d : ℝ)*K*E := by
    calc
      _ ≤ ∑ k, ‖complexCoefficientMul Q j k (H k - L (H k))‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin d, K*E := Finset.sum_le_sum (fun k _ =>
        (hmul k _).trans (mul_le_mul_of_nonneg_left (hH k) hK))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring
  have htrans : ‖ν.elim (fun _ => 0) (fun _ =>
      (2*ζ) • complexCoefficientMul Q j ⟨0, by omega⟩ (U - L U))‖ ≤ 4*K*E := by
    cases ν with
    | inl i => simp only [Sum.elim_inl, norm_zero]; positivity
    | inr b =>
      simp only [Sum.elim_inr, norm_smul, norm_mul]
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [htwo]
      calc
        _ ≤ (2*‖ζ‖) * (K*E) := mul_le_mul_of_nonneg_left
          ((hmul _ _).trans (mul_le_mul_of_nonneg_left hU hK)) (by positivity)
        _ ≤ 4 * (K*E) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hK hE)
        _ = _ := by ring
  dsimp only
  apply (C9ShortTimeLocality.norm_sub_localProjection_le Q ρ hv).trans
  have he : ((∑ k, complexCoefficientMul Q j k (H k)) -
      ν.elim (fun _ => 0) (fun _ => (2*ζ) • complexCoefficientMul Q j ⟨0, by omega⟩ U)) - v =
      (∑ k, complexCoefficientMul Q j k (H k - L (H k))) -
        ν.elim (fun _ => 0) (fun _ => (2*ζ) •
          complexCoefficientMul Q j ⟨0, by omega⟩ (U - L U)) := by
    simp only [v, map_sub, Finset.sum_sub_distrib, smul_sub]
    cases ν <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> abel
  rw [he]
  have hb := (norm_sub_le _ _).trans (add_le_add hrow htrans)
  nlinarith

/-- Forced-locality witnesses bound the coherent projection of the actual
flux gradient and the actual transpose orbit, without selecting witnesses in time. -/
theorem forced_local_projection_errors
    (hloc : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
    ∀ (t : ℝ≥0), 1 ≤ (t : ℝ) → ∀ ρ : ℝ, C * Real.sqrt (t : ℝ) ≤ ρ →
      (∀ ν j, ‖G t ν j - C9ShortTimeLocality.localProjection Q ρ (G t ν j)‖ ≤
        2 * (C * (2+(t : ℝ))^N * Real.exp (C * ‖ζ‖^2 * (t : ℝ) - c * ρ^2/(t : ℝ)))) ∧
      ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t -
          C9ShortTimeLocality.localProjection Q ρ
            (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t)‖ ≤
        2 * (C * (2+(t : ℝ))^N * Real.exp (C * ‖ζ‖^2 * (t : ℝ) - c * ρ^2/(t : ℝ))) := by
  obtain ⟨C, c, N, hC, hc, hdata⟩ := hloc d hd D
  refine ⟨C, c, N, hC, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF t ht ρ hρ
  have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht
  have hB : 0 ≤ C * (2+(t : ℝ))^N *
      Real.exp (C * ‖ζ‖^2 * (t : ℝ) - c * ρ^2/(t : ℝ)) := by positivity
  have endpoint (ν : EndpointIndex d) :
      ∃ H : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (H t) ∧
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t -
          C9ShortTimeLocality.localProjection Q ρ
            (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤
          2 * (C * (2+(t : ℝ))^N * Real.exp (C * ‖ζ‖^2 * (t : ℝ) - c * ρ^2/(t : ℝ))) ∧
        ∀ j, ‖H t j - C9ShortTimeLocality.localProjection Q ρ (H t j)‖ ≤
          2 * (C * (2+(t : ℝ))^N * Real.exp (C * ‖ζ‖^2 * (t : ℝ) - c * ρ^2/(t : ℝ))) := by
    obtain ⟨H, hgrad, hlocal, _⟩ :=
      hdata Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν
    obtain ⟨Uloc, Hloc, hUl, hHl, hb, _⟩ := hlocal t ht ρ hρ
    exact ⟨H, (hgrad t ht0).1,
      projection_errors_of_joint_bound Q _ Uloc (H t) Hloc hUl hHl hB hb⟩
  constructor
  · intro ν j
    obtain ⟨H, hgrad, _, hbound⟩ := endpoint (ν.elim Sum.inl (fun _ => Sum.inr true))
    have he : H t = G t ν := hgrad.unique (hF.choose_spec.choose_spec.1 t ν)
    simpa only [he] using hbound j
  · obtain ⟨H, _, hu, _⟩ := endpoint (Sum.inr true)
    exact hu

theorem dyadic_large_window_flux_projection_error
    : ∀ (hloc : node_e_u3A_forced_u2D_localityStmt)
      (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ →
      ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag →
      ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
        IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
      ∀ (s u : ℝ≥0), 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2*s →
        ‖ζ‖ * Real.sqrt (2*(s : ℝ)) ≤ 2 →
      ∀ ρ : ℝ, C * Real.sqrt (2*(s : ℝ)) ≤ ρ → ∀ ν : FluxIndex d,
        Real.sqrt (∑ j : Fin d,
          ‖(F u ν j - F s ν j) -
            C9ShortTimeLocality.localProjection Q ρ (F u ν j - F s ν j)‖^2) ≤
        C * (2+(s : ℝ))^N * Real.exp (-c * ρ^2/(s : ℝ)) := by
  intro hloc d hd D
  obtain ⟨C₀, c₀, N, hC₀, hc₀, hlocal⟩ := forced_local_projection_errors hloc d hd D
  let K := Real.exp (2*D.ellipticity)*D.ellipticity
  let A := C₀ * 2^N * Real.exp (4*C₀)
  let L := 4*(d : ℝ)*((d : ℝ)+4)*K*A
  let C := max C₀ (max 1 L)
  have hC0 : 0 ≤ C₀ := (by norm_num : (0 : ℝ) ≤ 1).trans hC₀
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans D.one_le_ellipticity)
  have hA : 0 ≤ A := by positivity
  have hL : 0 ≤ L := by positivity
  have hCC₀ : C₀ ≤ C := le_max_left _ _
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCL : L ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, c₀/2, N+1, hC1, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF s u hs hsu hus hforce ρ hρ ν
  have hs0 : 0 < (s : ℝ) := zero_lt_one.trans_le hs
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos (zero_lt_one.trans_le hC1)
    (Real.sqrt_pos.mpr (by positivity))) hρ
  have hζ : ‖ζ‖ ≤ 2 := by
    have hsq : 1 ≤ Real.sqrt (2*(s : ℝ)) := Real.le_sqrt_of_sq_le (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left hsq (norm_nonneg ζ)
    nlinarith
  let B := 2*A*(2+(s : ℝ))^N * Real.exp (-(c₀/2)*ρ^2/(s : ℝ))
  have hB : 0 ≤ B := by positivity
  have hb (t : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) :
      (∀ ν j, ‖G t ν j - C9ShortTimeLocality.localProjection Q ρ (G t ν j)‖ ≤ B) ∧
      ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t -
        C9ShortTimeLocality.localProjection Q ρ
          (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t)‖ ≤ B := by
    have hts : (t : ℝ) ≤ 2*(s : ℝ) := le_trans (show (t : ℝ) ≤ (u : ℝ) from htu) hus
    have hradius : C₀ * Real.sqrt (t : ℝ) ≤ ρ :=
      (mul_le_mul (hCC₀) (Real.sqrt_le_sqrt hts) (Real.sqrt_nonneg _) (by linarith)).trans hρ
    obtain ⟨hg, hu⟩ := hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF t
      (hs.trans (show (s : ℝ) ≤ (t : ℝ) from hst)) ρ hradius
    have he := dyadic_gaussian_envelope C₀ c₀ (s : ℝ) (t : ℝ) ρ ‖ζ‖ N
      hC0 hc₀.le hs (show (s : ℝ) ≤ (t : ℝ) from hst) hts (norm_nonneg _) hforce
    have he2 : 2 * (C₀ * (2+(t : ℝ))^N *
        Real.exp (C₀*‖ζ‖^2*(t : ℝ) - c₀*ρ^2/(t : ℝ))) ≤ B := by
      dsimp only [B, A]
      nlinarith
    exact ⟨fun ν j => (hg ν j).trans he2, hu.trans he2⟩
  let H (k : Fin d) := ∫ r in Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k
  let U := ∫ r in Icc (s : ℝ) (u : ℝ),
    transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal
  let E := B*((u : ℝ)-(s : ℝ))
  have hE : 0 ≤ E := mul_nonneg hB (sub_nonneg.mpr (show (s : ℝ) ≤ (u : ℝ) from hsu))
  have hH (k : Fin d) : ‖H k - C9ShortTimeLocality.localProjection Q ρ (H k)‖ ≤ E :=
    norm_integral_sub_localProjection_le Q ρ _ (hF.choose ν k) s u hsu B
      (fun t ht ht' => (hb t ht ht').1 ν k)
  have hU : ‖U - C9ShortTimeLocality.localProjection Q ρ U‖ ≤ E :=
    norm_integral_sub_localProjection_le Q ρ _ (hF.choose_spec.choose (β ⟨0, by omega⟩))
      s u hsu B (fun t ht ht' => (hb t ht ht').2)
  have hcoord (j : Fin d) :
      ‖(F u ν j - F s ν j) - C9ShortTimeLocality.localProjection Q ρ (F u ν j - F s ν j)‖ ≤
        2*((d : ℝ)+4)*K*E := by
    have he : F u ν j - F s ν j = (∑ k, complexCoefficientMul Q j k (H k)) -
        ν.elim (fun _ => 0) (fun _ => (2*ζ) • complexCoefficientMul Q j ⟨0, by omega⟩ U) := by
      rw [largeWindow_flux_split hd Q ζ P Pdag β a μ ha G F hF s u hsu ν j]
      cases ν <;> simp only [H, U, Sum.elim_inl, Sum.elim_inr, neg_mul, neg_smul,
        sub_eq_add_neg, neg_zero]
    rw [he]
    exact fluxCombination_projection_error_le hd Q hρ0 ζ hζ ν j H U hE hH hU
  have hsum : Real.sqrt (∑ j : Fin d,
      ‖(F u ν j - F s ν j) - C9ShortTimeLocality.localProjection Q ρ (F u ν j - F s ν j)‖^2) ≤
      (d : ℝ)*(2*((d : ℝ)+4)*K*E) := by
    calc
      _ ≤ ∑ j : Fin d, ‖(F u ν j - F s ν j) -
          C9ShortTimeLocality.localProjection Q ρ (F u ν j - F s ν j)‖ := by
        have hh := Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg
          (s := Finset.univ) (fun j _ => norm_nonneg ((F u ν j - F s ν j) -
            C9ShortTimeLocality.localProjection Q ρ (F u ν j - F s ν j))))
        rwa [Real.sqrt_sq (Finset.sum_nonneg fun j _ => norm_nonneg _)] at hh
      _ ≤ ∑ _ : Fin d, 2*((d : ℝ)+4)*K*E := Finset.sum_le_sum (fun j _ => hcoord j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply hsum.trans
  have hlen : (u : ℝ)-(s : ℝ) ≤ 2+(s : ℝ) := by
    have hh : (u : ℝ) ≤ 2*(s : ℝ) := hus
    linarith
  have hh : L*((2+(s : ℝ))^N * Real.exp (-(c₀/2)*ρ^2/(s : ℝ))) *
      ((u : ℝ)-(s : ℝ)) ≤
      C*((2+(s : ℝ))^N * Real.exp (-(c₀/2)*ρ^2/(s : ℝ))) * (2+(s : ℝ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hCL (by positivity)) hlen
      (sub_nonneg.mpr (show (s : ℝ) ≤ (u : ℝ) from hsu)) (by positivity)
  dsimp only [E, B, L] at hh ⊢
  rw [pow_succ (2+(s : ℝ)) N]
  convert hh using 1 <;> ring

end C8LargeWindow

/-- Localize the actual dyadic flux increment at radius `C n √s`. -/
theorem dyadic_large_window_flux_locality
    (hlocal : node_e_u3A_forced_u2D_localityStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
    ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2*s →
      ‖ζ‖ * Real.sqrt (2*(s : ℝ)) ≤ 2 → ∀ (ν : FluxIndex d) (n : ℕ), 1 ≤ n →
    ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ j, IsComplexLocalObservation Q (C*n*Real.sqrt (s : ℝ)) (V j)) ∧
      Real.sqrt (∑ j : Fin d, ‖F u ν j-F s ν j-V j‖^2) ≤
        C*(2+(s : ℝ))^N*Real.exp (-c*(n : ℝ)^2) := by
  intro d hd D
  obtain ⟨C₀, c, N, hC₀, hc, hbound⟩ :=
    C8LargeWindow.dyadic_large_window_flux_projection_error hlocal d hd D
  let C := 2*C₀
  have hC0 : 0 < C₀ := zero_lt_one.trans_le hC₀
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, c*C^2, N, hC, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF s u hs hsu hus hforce ν n hn
  let ρ := C*(n : ℝ)*Real.sqrt (s : ℝ)
  have hs0 : 0 < (s : ℝ) := zero_lt_one.trans_le hs
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hρ : C₀*Real.sqrt (2*(s : ℝ)) ≤ ρ := by
    have hsqrt : Real.sqrt (2*(s : ℝ)) ≤ 2*Real.sqrt (s : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt (2 : ℝ) ≤ 2)
        (Real.sqrt_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hsqrt hC0.le
    have hn := mul_le_mul_of_nonneg_left hn1
      (mul_nonneg (show 0 ≤ C by linarith) (Real.sqrt_nonneg (s : ℝ)))
    dsimp [ρ, C] at *
    nlinarith
  refine ⟨fun j => C9ShortTimeLocality.localProjection Q ρ (F u ν j-F s ν j),
    fun j => C9ShortTimeLocality.localProjection_isLocal Q ρ _, ?_⟩
  have hb := hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF
    s u hs hsu hus hforce ρ hρ ν
  have hexp : -c*ρ^2/(s : ℝ) = -(c*C^2)*(n : ℝ)^2 := by
    dsimp [ρ]
    rw [mul_pow, mul_pow, Real.sq_sqrt hs0.le]
    field_simp
  rw [hexp] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith : C₀ ≤ C) (by positivity))
    (Real.exp_nonneg _))

end EinsteinFull.Blueprint
