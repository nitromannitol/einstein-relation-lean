import EinsteinFull.Calculus.S2LateScalarSupport
import EinsteinFull.Calculus.ComplexGeneratorUniquenessSupport
import EinsteinFull.Blueprint.G3.node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacement
import EinsteinFull.Blueprint.G3.node_e_u3A_time_u2D_flux
import EinsteinFull.Blueprint.Roots.node_p_u3A_late
import EinsteinFull.Blueprint.Roots.node_l_u3A_late_u2D_propagation
import EinsteinFull.Blueprint.G3.Proofs.W4Queue0400_2

/-!
# `p:endpoint-comparison#force-replacement`

The binders are `e:time-flux`, `p:late` and `l:late-propagation`. The flux family comes from
`p:late` (one application per force, with the zero-force flux of the common semigroup); the
zero-force flux is unique because the horizontal gradient is. The homogeneous propagation of the
force-replacement error is bounded by `S2ForcedFluxScale` from the averaging seminorm bound of
`p:late`; the scalar bookkeeping is in `S2LateScalarSupport`.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull

open EinsteinRelation

theorem isFiniteTimeFlux_F_unique {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    {G G' F F' : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (h : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (h' : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G' F') : F = F' := by
  obtain ⟨hG, hU, hgrad, hF⟩ := h
  obtain ⟨hG', hU', hgrad', hF'⟩ := h'
  have hGG : G = G' := by
    funext τ ν
    exact HasComplexHorizontalGradient.unique (hgrad τ ν) (hgrad' τ ν)
  subst hGG
  funext τ ν j
  apply Lp.ext
  exact (hF τ ν j).trans (hF' τ ν j).symm

theorem sourceReducedBound_pos_of_one_le {L : ℝ} (h : 1 ≤ L) : 0 < sourceReducedBound L := by
  unfold sourceReducedBound
  exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg L])

end EinsteinFull

namespace EinsteinFull.Blueprint

open EinsteinRelation

theorem node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacement_of_deps
    (_hflux : node_e_u3A_time_u2D_fluxStmt) (hlate : node_p_u3A_lateStmt)
    (_hprop : node_l_u3A_late_u2D_propagationStmt) :
    node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacementStmt := by
  intro d hd D
  obtain ⟨Cp, M, hCp, hp⟩ := hlate d hd D
  refine ⟨M, fun C₀ hC₀ => ?_⟩
  have hKpos : 0 < sourceReducedBound D.ellipticity :=
    sourceReducedBound_pos_of_one_le D.one_le_ellipticity
  have hε : 0 < deconvEps D.ellipticity := inv_pos.mpr (mul_pos two_pos hKpos)
  obtain ⟨Rw, hRw⟩ := Filter.eventually_atTop.mp
    (LateUnsmoothing.eventually_force_window_le_rpow (η := 1 / 16) (K := 1)
      (by norm_num) one_pos C₀)
  obtain ⟨c, hc, hlog⟩ := log_pow_le_rpow M
  let A : ℝ := ((deconvEps D.ellipticity / 8) ^ ((d : ℝ) / 4))⁻¹ *
    ((d : ℝ) / 2 * (3 * Real.sqrt (sourceReducedBound D.ellipticity)) + 1)
  have hA : 0 ≤ A := by positivity
  let C : ℝ := A * Cp * (1 + c) + sourceReducedBound D.ellipticity + 2
  have hCpos : 0 < C := by
    have : 0 ≤ A * Cp * (1 + c) := by positivity
    linarith
  have hAC : A * Cp ≤ C := by
    have : 0 ≤ A * Cp * c := by positivity
    have h2 : 0 ≤ sourceReducedBound D.ellipticity + 2 := by linarith
    dsimp only [C]
    nlinarith
  have hACc : A * Cp * c ≤ C := by
    have : 0 ≤ A * Cp := by positivity
    have h2 : 0 ≤ sourceReducedBound D.ellipticity + 2 := by linarith
    dsimp only [C]
    nlinarith
  have hKC : sourceReducedBound D.ellipticity + 2 ≤ C := by
    have : 0 ≤ A * Cp * (1 + c) := by positivity
    dsimp only [C]
    linarith
  refine ⟨C, max 6 (max Rw (16 / deconvEps D.ellipticity)), hCpos,
    (by norm_num : (2 : ℝ) ≤ 6).trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ R hRpos hR z hz
  dsimp only
  intro P Pdag hP hPdag
  have hR6 : 6 ≤ R := (le_max_left _ _).trans hR
  have hRRw : Rw ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans hR
  have hRε : 16 / deconvEps D.ellipticity ≤ R :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hR
  have hall : ∀ w : ℂ, ∃ G F G₀ F₀ : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsFiniteTimeFlux hd Q w (P w) (Pdag w) β a μ G F ∧
      IsFiniteTimeFlux hd Q 0 (P 0) (Pdag 0) β a μ G₀ F₀ ∧
      ∀ t : ℝ≥0, 2 ≤ (t : ℝ) → ‖w‖ * Real.sqrt (t : ℝ) ≤ 1 → ∀ ν : FluxIndex d,
        gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F t ν j)) ≤
          ENNReal.ofReal (Cp * Real.log (2 + (t : ℝ)) ^ M) ∧
        gaussianAveragingSeminorm hd Q
          (fun j => centeredComplexLp Q (F t ν j - F₀ t ν j)) ≤
          ENNReal.ofReal (Cp * ‖w‖ * Real.sqrt (t : ℝ) * Real.log (2 + (t : ℝ)) ^ M) :=
    fun w => hp Q hQ β a μ hβ ha hμ w (P w) (Pdag w) (P 0) (Pdag 0) (hP w) (hPdag w)
      (hP 0) (hPdag 0)
  choose G F G₀ F₀ hGF hGF₀ hbd using hall
  refine ⟨G, F, hGF, ?_⟩
  set T : ℝ := R ^ 2 / 2 with hTdef
  set τ : ℝ := T ^ (1 - (1 / 4 : ℝ)) with hτdef
  set ζ : ℂ := z / (R : ℂ) with hζdef
  have hT16 : 16 ≤ T := by rw [hTdef]; nlinarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hτ2, hτT⟩ := tau_facts hT16
  have hτ0 : 0 ≤ τ := by linarith
  have hs : 0 < T - τ := by linarith
  have hsT : T - τ ≤ T := by linarith
  have hTs : T / 2 ≤ T - τ := by linarith
  have hεs : 2 ≤ deconvEps D.ellipticity * ((T - τ) / 2) := by
    have h16 : 16 ≤ R * deconvEps D.ellipticity := (div_le_iff₀ hε).mp hRε
    have h1 : 8 ≤ deconvEps D.ellipticity * T := by
      rw [hTdef]
      nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : R ≤ R ^ 2) hε.le]
    nlinarith [mul_le_mul_of_nonneg_left hTs hε.le]
  have hzn : ‖z‖ ≤ R ^ (1 / 16 : ℝ) := by
    have h := hRw R hRRw ‖z‖ (by
      rcases hz with h | ⟨x, rfl, h⟩
      · exact Or.inl h
      · exact Or.inr (by simpa using h))
    simpa using h
  have hζn : ‖ζ‖ = ‖z‖ / R := by
    rw [hζdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
  have hsmall : ‖ζ‖ * Real.sqrt τ ≤ 1 := by
    rw [hζn]
    exact window_small (by linarith) (norm_nonneg z) hzn
  have hpz : ‖ζ‖ * Real.sqrt τ ≤ ‖z‖ * T ^ (-(1 / 8) : ℝ) := by
    rw [hζn]
    exact zeta_sqrt_tau_le hRpos (norm_nonneg z)
  have hx : ‖ζ‖ ^ 2 * T = ‖z‖ ^ 2 / 2 := by
    rw [hζn, hTdef]
    field_simp
  have hcoe : ((τ.toNNReal : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal τ hτ0
  have hF0 : F₀ ζ = F 0 :=
    isFiniteTimeFlux_F_unique hd Q 0 (P 0) (Pdag 0) β a μ (hGF₀ ζ) (hGF 0)
  have hLnn : 0 ≤ Real.log (2 + τ) ^ M := pow_nonneg (Real.log_nonneg (by linarith)) M
  have hLT : Real.log (2 + τ) ^ M ≤ c * T ^ (1 / 32 : ℝ) :=
    (hlog τ (by linarith)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)) hc.le)
  refine ⟨hs, hsmall, fun ν => ?_⟩
  have hsem : gaussianAveragingSeminorm hd Q
      (fun j => centeredComplexLp Q (F ζ τ.toNNReal ν j - F 0 τ.toNNReal ν j)) ≤
      ENNReal.ofReal (Cp * ‖ζ‖ * Real.sqrt τ * Real.log (2 + τ) ^ M) := by
    have h := (hbd ζ τ.toNNReal (by rw [hcoe]; exact hτ2) (by rw [hcoe]; exact hsmall) ν).2
    rw [hF0, hcoe] at h
    exact h
  have hC' : 0 ≤ Cp * ‖ζ‖ * Real.sqrt τ * Real.log (2 + τ) ^ M := by positivity
  have hE := norm_forcedFluxE_le_scale hd Q hT0 hs hsT hTs hεs
    (fun j => centeredComplexLp Q (F ζ τ.toNNReal ν j - F 0 τ.toNNReal ν j)) hC' hsem ζ ν
  change ‖forcedFluxE hd Q (T - τ) hs ζ ν
    (fun j => centeredComplexLp Q (F ζ τ.toNNReal ν j - F 0 τ.toNNReal ν j))‖ ≤ _ ∧
    ‖forcedFluxE hd Q (T - τ) hs ζ ν
    (fun j => centeredComplexLp Q (F ζ τ.toNNReal ν j - F 0 τ.toNNReal ν j))‖ ≤ _
  have hEeq : ((deconvEps D.ellipticity / 8) ^ ((d : ℝ) / 4))⁻¹ *
        ((d : ℝ) / 2 * (3 * Real.sqrt (sourceReducedBound D.ellipticity)) + 1) *
          Real.exp ((sourceReducedBound D.ellipticity + 1) * ‖ζ‖ ^ 2 * T) *
            T ^ (-(1 / 2 + (d : ℝ) / 4)) * (Cp * ‖ζ‖ * Real.sqrt τ * Real.log (2 + τ) ^ M) =
      A * Cp * Real.exp ((sourceReducedBound D.ellipticity + 1) * ‖ζ‖ ^ 2 * T) *
        T ^ (-(1 / 2 + (d : ℝ) / 4)) * ((‖ζ‖ * Real.sqrt τ) * Real.log (2 + τ) ^ M) := by
    dsimp only [A]
    ring
  rw [hEeq] at hE
  have hx0 : 0 ≤ ‖ζ‖ ^ 2 * T := by positivity
  constructor
  · refine hE.trans ?_
    have hexp : Real.exp ((sourceReducedBound D.ellipticity + 1) * ‖ζ‖ ^ 2 * T) ≤
        Real.exp (C * ‖ζ‖ ^ 2 * T) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right (by linarith :
        sourceReducedBound D.ellipticity + 1 ≤ C) hx0])
    have hTa : 0 ≤ T ^ (-(1 / 2 + (d : ℝ) / 4)) := Real.rpow_nonneg hT0.le _
    have hpl : 0 ≤ (‖ζ‖ * Real.sqrt τ) * Real.log (2 + τ) ^ M := by positivity
    calc A * Cp * Real.exp ((sourceReducedBound D.ellipticity + 1) * ‖ζ‖ ^ 2 * T) *
          T ^ (-(1 / 2 + (d : ℝ) / 4)) * ((‖ζ‖ * Real.sqrt τ) * Real.log (2 + τ) ^ M)
        ≤ C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4)) *
          ((‖ζ‖ * Real.sqrt τ) * Real.log (2 + τ) ^ M) := by
          apply mul_le_mul_of_nonneg_right _ hpl
          apply mul_le_mul_of_nonneg_right _ hTa
          exact mul_le_mul hAC hexp (Real.exp_pos _).le hCpos.le
      _ = _ := by ring
  · refine hE.trans ?_
    have hsc := scalar_combine (A := A * Cp) (B := sourceReducedBound D.ellipticity + 1)
      (c := c) (T := T) (zn := ‖z‖) (p := ‖ζ‖ * Real.sqrt τ)
      (L := Real.log (2 + τ) ^ M) (a := 1 / 2 + (d : ℝ) / 4) (by positivity)
      (by linarith) hc.le (by linarith) (norm_nonneg z) (by positivity) hLnn hpz hLT
      ((sourceReducedBound D.ellipticity + 1) * ‖ζ‖ ^ 2 * T)
      (by rw [mul_assoc, hx])
    refine hsc.trans ?_
    have hexp : Real.exp ((sourceReducedBound D.ellipticity + 1 + 1) * (1 + ‖z‖) ^ 2) ≤
        Real.exp (C * (1 + ‖z‖) ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
    have hTb : 0 ≤ T ^ (-(1 / 2 + (d : ℝ) / 4) - 1 / 16) := Real.rpow_nonneg hT0.le _
    calc A * Cp * c * Real.exp ((sourceReducedBound D.ellipticity + 1 + 1) * (1 + ‖z‖) ^ 2) *
          T ^ (-(1 / 2 + (d : ℝ) / 4) - 1 / 16)
        ≤ C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - 1 / 16) := by
          apply mul_le_mul_of_nonneg_right _ hTb
          exact mul_le_mul hACc hexp (Real.exp_pos _).le hCpos.le

end EinsteinFull.Blueprint
