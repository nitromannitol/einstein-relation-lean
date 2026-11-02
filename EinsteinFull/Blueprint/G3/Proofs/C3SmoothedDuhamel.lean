import EinsteinFull.Calculus.C3SmoothedDuhamelClosureSupport
import EinsteinFull.Blueprint.G3.node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamel

open MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Exact smoothed Duhamel reduction, using only its three ordered graph dependencies. -/
theorem node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamel_of_deps
    (hscalar : node_p_u3A_scalarStmt)
    (hforced : node_l_u3A_forced_u2D_fluxStmt)
    (hcentered : node_e_u3A_centered_u2D_equationsStmt) :
    node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamelStmt := by
  intro d hd D
  obtain ⟨ε, η, growth, t₀, Cder, L, hε, hη, hηquarter, hgrowth, ht₀, hCder, hflux⟩ :=
    c3ForcedFlux_from_scalar hscalar hforced hd D
  let N := max (L 0) (L 1)
  let a := (1 / 2 : ℝ) * (d : ℝ) * Cder 1 + Cder 0
  let K := max 0 (sourceReducedBound D.ellipticity) + growth + 1
  have ha : 0 < a := by
    have h0 := hCder 0
    have h1 := hCder 1
    dsimp [a]
    positivity
  have hK : 0 < K := by dsimp [K]; have := le_max_left 0 (sourceReducedBound D.ellipticity); linarith
  refine ⟨ε, η, (N : ℝ), hε, hη, Nat.cast_nonneg _, ?_⟩
  intro δ hδ hδhalf b hb hb1 _hbsmall C₀ hC₀
  obtain ⟨T₀, hT₀, hwindow⟩ := c3Late_force_windows η δ t₀ C₀ hη
    (by linarith) hδ (by linarith) hC₀
  let C := max (a / ε * (2 : ℝ) ^ N) K + 1
  have hC : 0 < C := by
    have := (le_max_right (a / ε * (2 : ℝ) ^ N) K)
    dsimp [C]
    linarith
  have hcoeff : a / ε * (2 : ℝ) ^ N ≤ C := by
    exact (le_max_left _ _).trans (by dsimp [C]; linarith)
  have hKC : K ≤ C := by exact (le_max_right _ _).trans (by dsimp [C]; linarith)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro Q hQ β A μ hβ hA hμ T hT hTlarge ζ hζ P Pdag hP hPdag ν
  have hTpos : 0 < T := by linarith
  let τ := T ^ (1 - δ)
  let s := T ^ (1 - b)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hTpos _
  have hs : 0 < s := Real.rpow_pos_of_pos hTpos _
  have hs1 : 1 ≤ s := Real.one_le_rpow hT.le (by linarith)
  have hsT : s ≤ T := by
    exact (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith : 1 - b ≤ 1)).trans_eq
      (Real.rpow_one T)
  have hτT : τ < T := Real.rpow_lt_self_of_one_lt hT (by linarith)
  obtain ⟨hτlarge, hτhalf, hwide⟩ := hwindow T hTlarge
  have hforce : ‖ζ‖ * Real.sqrt T ≤ 2 ∨
      ‖ζ‖ * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ) := by
    rcases hζ with h | ⟨lam, rfl, h⟩
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  obtain ⟨hm, hwide⟩ := hwide ‖ζ‖ (norm_nonneg _) hforce
  obtain ⟨G, J, hphysical, hgaussian⟩ := hflux Q hQ β A μ hβ hA hμ ζ P Pdag hP hPdag ν
  let B := a * Real.exp (K * ‖ζ‖ ^ 2 * T) * s ^ (-(1 / 2 + (d : ℝ) / 4)) *
    (1 + T / s) ^ N
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdecay : ∀ g : Lp ℂ 2 (reducedLaw Q), ∀ t ∈ Set.Ioo τ T,
      ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤
        B * t ^ (-1 - ε) * ‖g‖ := by
    intro g t ht
    have htpos : 0 < t := hτ.trans ht.1
    have htlarge : t₀ ≤ t := hτlarge.trans ht.1.le
    have hw := hwide t htpos ht.2.le
    have hw8 := hwide (t / 8) (by positivity) (by linarith [ht.2])
    have hbound := hgaussian t.toNNReal
      (by simpa only [Real.coe_toNNReal t htpos.le] using htlarge) hm
      (by simpa only [Real.coe_toNNReal t htpos.le] using hw)
      (by simpa only [Real.coe_toNNReal t htpos.le] using hw8) s hs1 hs
    have hnormalized := c3BackwardFluxFunctional_decay_of_gaussian_bounds hd Q ν ζ T t
      htpos.le ht.2 J s hs hsT g ε growth hgrowth.le Cder (fun k => (hCder k).le) L
      (by simpa only [Real.coe_toNNReal t htpos.le] using hbound)
    convert hnormalized using 1
    all_goals
      try dsimp [B, a, K, N]
      ring
  have hnorm := c3SmoothedEndpoint_norm_of_flux_decay hcentered hd D Q hQ β A μ
    hβ hA hμ ζ P Pdag hP hPdag ν G J hphysical s hs T τ hτ hτT B ε hB hε hdecay
  refine ⟨hτhalf, (fun r hr hrT => hwide r (hτ.trans_le hr) hrT), hnorm.trans ?_⟩
  have hscale := c3Smoothing_weight_scale T b (1 / 2 + (d : ℝ) / 4) N hT hb.le
  have hscale' := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ a / ε * Real.exp (K * ‖ζ‖ ^ 2 * T) * τ ^ (-ε) by positivity)
  calc
    B * (τ ^ (-ε) / ε) ≤
        (a / ε * (2 : ℝ) ^ N) * Real.exp (K * ‖ζ‖ ^ 2 * T) *
          T ^ (-(1 / 2 + (d : ℝ) / 4)) *
          T ^ (b * (1 / 2 + (d : ℝ) / 4 + (N : ℝ))) * τ ^ (-ε) := by
      convert hscale' using 1
      all_goals
        try dsimp [B, s]
        ring
    _ ≤ C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4)) *
        T ^ (b * (1 / 2 + (d : ℝ) / 4 + (N : ℝ))) * τ ^ (-ε) := by
      gcongr

end EinsteinFull.Blueprint
