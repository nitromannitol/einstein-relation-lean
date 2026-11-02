import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_average
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_flux
import EinsteinFull.Blueprint.G3.node_stationary_u2D_analytic_u2D_semigroup_u23_clock
import EinsteinFull.Work.W4.ActualHomogeneousGaussianSemigroupProof
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.FDeriv.WithLp

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Division by the force on nested discs, including the removable value at
zero. The second Schwarz estimate controls the change of the quotient. -/
theorem clock_force_quotient_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f {z | ‖z‖ * R < 3})
    (hbound : ∀ z, ‖z‖ * R ≤ 2 → ‖z • f z‖ ≤ M) :
    (∀ z, ‖z‖ * R < 2 → ‖f z‖ ≤ M * R) ∧
    (∀ z, ‖z‖ * R ≤ 1 → ‖f z - f 0‖ ≤ 2 * M * R ^ 2 * ‖z‖) := by
  let B := Metric.ball (0 : ℂ) (2 / R)
  have hB : ∀ z, z ∈ B ↔ ‖z‖ * R < 2 := by
    intro z
    simp only [B, Metric.mem_ball, dist_zero_right, lt_div_iff₀ hR]
  have hdiff : DifferentiableOn ℂ f B := hf.mono (fun z hz => by
    change ‖z‖ * R < 3
    linarith [(hB z).mp hz])
  have hzero : (0 : ℂ) ∈ B := (hB 0).mpr (by simp)
  let g := fun z : ℂ => z • f z
  have hg : DifferentiableOn ℂ g B := differentiableOn_id.smul hdiff
  have hgz : g 0 = 0 := zero_smul ℂ (f 0)
  have hmaps : MapsTo g B (Metric.ball (g 0) (2 * M)) := by
    intro z hz
    rw [Metric.mem_ball, hgz, dist_zero_right]
    exact (hbound z ((hB z).mp hz).le).trans_lt (by linarith)
  have hds : ∀ z, z ∈ B → dslope g 0 z = f z := by
    intro z _hz
    by_cases hz : z = 0
    · subst z
      rw [dslope_same]
      have hf0 := hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hzero)
      simpa only [g, id_eq, zero_smul, one_smul, add_zero, zero_add] using!
        ((hasDerivAt_id (0 : ℂ)).smul hf0.hasDerivAt).deriv
    · rw [dslope_of_ne _ hz, slope_def_module, sub_zero, hgz, sub_zero,
        smul_smul, inv_mul_cancel₀ hz, one_smul]
  have hn : ∀ z, z ∈ B → ‖f z‖ ≤ M * R := by
    intro z hz
    have hh := Complex.norm_dslope_le_div_of_mapsTo_ball hg (fun z hz => Metric.ball_subset_closedBall (hmaps hz)) hz
    rw [hds z hz] at hh
    convert! hh using 1
    field_simp
  refine ⟨fun z hz => hn z ((hB z).mpr hz), ?_⟩
  intro z hz
  have hmapsf : MapsTo f B (Metric.ball (f 0) (4 * M * R)) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖f w - f 0‖ ≤ ‖f w‖ + ‖f 0‖ := norm_sub_le _ _
      _ ≤ M * R + M * R := add_le_add (hn w hw) (hn 0 hzero)
      _ < 4 * M * R := by nlinarith [mul_pos hM hR]
  have hh := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff (fun z hz => Metric.ball_subset_closedBall (hmapsf hz))
    ((hB z).mpr (lt_of_le_of_lt hz (by norm_num)))
  rw [dist_eq_norm, dist_zero_right] at hh
  convert! hh using 1
  field_simp
  ring

/-- Multiplying a time power by the parabolic force radius shifts its
exponent by exactly one half. -/
theorem clock_rpow_mul_sqrt {t : ℝ} (ht : 0 < t) (q : ℝ) :
    t ^ q * Real.sqrt t = t ^ (q + 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]

/-- The finite-p witness at p=2 is the actual L2 class whenever their
representatives agree almost everywhere. Equality of exponents transports
all normed-space instances together. -/
theorem clock_differentiableOn_of_ae_eq_two
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p = 2)
    {f : ℂ → Lp ℂ p ν} {g : ℂ → Lp ℂ 2 ν} {S : Set ℂ}
    (heq : ∀ z, (f z : α → ℂ) =ᵐ[ν] g z)
    (hf : DifferentiableOn ℂ f S) : DifferentiableOn ℂ g S := by
  subst p
  have hfg : f = g := by
    funext z
    exact Lp.ext (heq z)
  rwa [hfg] at hf

/-- Exact clock-average graph reduction. Only the three direct graph Props
are parameters; the analytic-clock contract supplies the outer-disc estimates. -/
theorem node_e_u3A_clock_u2D_average_of_deps
    (hscalar : node_p_u3A_scalarStmt)
    (hflux : node_l_u3A_forced_u2D_fluxStmt)
    (hclock : node_stationary_u2D_analytic_u2D_semigroup_u23_clockStmt) :
    node_e_u3A_clock_u2D_averageStmt := by
  intro d hd D
  obtain ⟨_a₀, ηscalar, _ha₀, _ha₀1, hηscalar, _hscalar⟩ := hscalar d hd D
  obtain ⟨εflux, _ηflux, _L, hεflux, _hηflux, _hflux⟩ := hflux d hd D
  obtain ⟨ε, hε, hc⟩ := hclock d hd D
  let gain := min ε (min εflux ηscalar)
  have hgain : 0 < gain := lt_min hε (lt_min hεflux hηscalar)
  have hgain_le : gain ≤ ε := min_le_left _ _
  have hc2 := hc 2 2 (by norm_num) (by norm_num)
  norm_num only at hc2
  obtain ⟨C, t₀, N, hC, ht₀, hc2⟩ := hc2
  refine ⟨gain, 4 * C, t₀, hgain, by positivity, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP
  obtain ⟨G, J, hGJ, hreg⟩ := hc2 Q hQ a μ ha hμ P hP
  refine ⟨G, J, fun ζ r hr => (hGJ ζ r hr).1, ?_⟩
  intro r hr s hs hrs
  have hr0 : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one (ht₀.trans hr)
  have hR : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr0
  obtain ⟨Wp, Gp, Jp, hWp, hGpJp, hWd_p, hGdJd, _hpoly, havg⟩ := hreg r hr
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hWd := clock_differentiableOn_of_ae_eq_two (reducedLaw Q)
    (by norm_num : ENNReal.ofReal (2 : ℝ) = 2) hWp hWd_p
  have hJd : ∀ j, DifferentiableOn ℂ (fun ζ => J ζ r j)
      {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < 3} := by
    intro j
    exact clock_differentiableOn_of_ae_eq_two (reducedLaw Q)
      (by norm_num : ENNReal.ofReal (2 : ℝ) = 2)
      (fun ζ => (hGpJp ζ j).2) (hGdJd j).2
  obtain ⟨_hUd, _hVd, _hU0, _hV0, hUfac, hVfac, hsize⟩ := havg s hs hrs
  let W := fun ζ => centeredComplexLp Q (P ζ r μ)
  let H := homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0
  have hH (f : Lp ℂ 2 (reducedLaw Q)) : H f = gaussianAverage hd Q s hs f := rfl
  have hHW : DifferentiableOn ℂ (fun ζ => H (W ζ))
      {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < 3} :=
    H.differentiable.comp_differentiableOn hWd
  have hM : 0 < C * (r : ℝ) ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) :=
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos hr0 _)) (Real.rpow_pos_of_pos hs _)
  have hquot := clock_force_quotient_bounds hR hM hHW (fun ζ hζ => by
    rw [hH, ← hUfac ζ]
    simpa only [neg_div] using! (hsize ζ hζ).1)
  have hcancel : (C * (r : ℝ) ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4)) *
      Real.sqrt (r : ℝ) = C * s ^ (-(d : ℝ) / 4) := by
    calc
      _ = C * s ^ (-(d : ℝ) / 4) *
          ((r : ℝ) ^ (-1 / 2 : ℝ) * Real.sqrt (r : ℝ)) := by ring
      _ = _ := by rw [clock_rpow_mul_sqrt hr0]; norm_num
  have hopen : IsOpen {ζ : ℂ | ‖ζ‖ * Real.sqrt (r : ℝ) < 3} :=
    isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have hW0 : DifferentiableAt ℂ W 0 :=
    hWd.differentiableAt (hopen.mem_nhds (by simp))
  refine ⟨?_, hW0, ?_, ?_⟩
  · intro ζ hζ
    refine ⟨rfl, ?_, ?_⟩
    · change ‖H (W ζ)‖ ≤ _
      calc
        _ ≤ C * s ^ (-(d : ℝ) / 4) := by
          simpa only [hcancel] using! hquot.1 ζ (lt_of_le_of_lt hζ (by norm_num))
        _ ≤ 4 * C * s ^ (-(d : ℝ) / 4) := by
          gcongr
          linarith
    · change ‖H (W ζ - W 0)‖ ≤ _
      rw [map_sub]
      calc
        _ ≤ 2 * (C * (r : ℝ) ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4)) *
            Real.sqrt (r : ℝ) ^ 2 * ‖ζ‖ := hquot.2 ζ hζ
        _ = 2 * C * ‖ζ‖ * Real.sqrt (r : ℝ) * s ^ (-(d : ℝ) / 4) := by
          calc
            _ = 2 * ((C * (r : ℝ) ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4)) *
              Real.sqrt (r : ℝ)) * Real.sqrt (r : ℝ) * ‖ζ‖ := by ring
            _ = _ := by rw [hcancel]; ring
        _ ≤ 4 * C * ‖ζ‖ * Real.sqrt (r : ℝ) * s ^ (-(d : ℝ) / 4) := by
          gcongr
          linarith
  · simpa only [clockEndpoint, id_eq, one_smul, zero_smul, add_zero, zero_add] using!
      ((hasDerivAt_id (0 : ℂ)).smul hW0.hasDerivAt).deriv
  · let L := H.comp (centeredComplexLpCLM Q)
    let f := fun ζ => WithLp.toLp 2 (fun j : Fin d => L (J ζ r j))
    have hf : DifferentiableOn ℂ f {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < 3} := by
      apply (differentiableOn_piLp 2).mpr
      intro j
      exact L.differentiable.comp_differentiableOn (hJd j)
    have hMf : 0 < C * (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) :=
      mul_pos (mul_pos hC (Real.rpow_pos_of_pos hr0 _)) (Real.rpow_pos_of_pos hs _)
    have hLf (ζ : ℂ) (j : Fin d) : L (J ζ r j) =
        gaussianAverage hd Q s hs (centeredComplexLp Q (J ζ r j)) := by
      change H (centeredComplexLpCLM Q (J ζ r j)) = _
      rw [centeredComplexLpCLM_apply, hH]
    have hfsize : ∀ ζ, ‖ζ‖ * Real.sqrt (r : ℝ) ≤ 2 →
        ‖ζ • f ζ‖ ≤ C * (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) := by
      intro ζ hζ
      rw [PiLp.norm_eq_of_L2]
      simpa only [f, PiLp.smul_apply, PiLp.toLp_apply, hLf, ← hVfac ζ] using!
        (hsize ζ hζ).2
    have hbound := (clock_force_quotient_bounds hR hMf hf hfsize).1 0 (by simp)
    rw [PiLp.norm_eq_of_L2] at hbound
    have hpow : (r : ℝ) ^ (-1 - ε) * Real.sqrt (r : ℝ) =
        (r : ℝ) ^ (-1 / 2 - ε) := by
      rw [clock_rpow_mul_sqrt hr0]
      congr 1
      ring
    calc
      _ ≤ (C * (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4)) *
          Real.sqrt (r : ℝ) := by
        simpa only [f, PiLp.toLp_apply, hLf] using! hbound
      _ = C * (r : ℝ) ^ (-1 / 2 - ε) * s ^ (-(d : ℝ) / 4) := by
        calc
          _ = C * ((r : ℝ) ^ (-1 - ε) * Real.sqrt (r : ℝ)) *
            s ^ (-(d : ℝ) / 4) := by ring
          _ = _ := by rw [hpow]
      _ ≤ 4 * C * (r : ℝ) ^ (-1 / 2 - ε) * s ^ (-(d : ℝ) / 4) := by
        gcongr
        linarith
      _ ≤ 4 * C * (r : ℝ) ^ (-1 / 2 - gain) * s ^ (-(d : ℝ) / 4) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs.le _)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le (ht₀.trans hr) (by linarith)

end EinsteinFull.Blueprint
