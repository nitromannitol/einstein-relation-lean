import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_local
import EinsteinFull.Calculus.ScalarWeightSupport

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint

theorem c15_dyadic_holder_half_error (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) : ∃ b : ℝ, 0 < b ∧ b ≤ 1/16 ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 → ∀ K : ℝ, 0 ≤ K → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ (t/8)‖ ≤ K * ((t : ℝ)/8) ^ (-(1/2+(d : ℝ)/4)) → ∀ hbt : 0 < b * (t : ℝ), ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t - gaussianAverage hd Q (b*(t : ℝ)) hbt (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤ (K/2) * (t : ℝ) ^ (-(1/2+(d : ℝ)/4)) := by
  obtain ⟨α, Cdet, c, N, hα, hCdet, hc, hloc⟩ := hlocal d hd D
  obtain ⟨C, Cp, hC, hCp, hloc⟩ := hloc 2 (by norm_num)
  let q : ℝ := 1/2 + (d : ℝ)/4
  let A : ℝ := C * 3 ^ C * Real.exp (4 * Cp) * 8 ^ q
  let B : ℝ := max 1 A
  obtain ⟨hb, hbsmall, habs⟩ := inner_smoothing_absorption (1/16) B α (by norm_num) (le_max_left _ _) hα
  refine ⟨_, hb, hbsmall, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hz K hK hU hbt
  have htpos : 0 < (t : ℝ) := by linarith
  obtain ⟨G, V, hgrad, hest, hrest⟩ := hloc Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  have hholder := ((hest t htpos).2.2 _ hb hbsmall hbt).2
  have hholder' : ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t - gaussianAverage hd Q (_ * (t : ℝ)) hbt (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤ C * (min (1/16) ((2 * B) ^ (-2 / α))) ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖indexedEndpoint hd Q ν ζ P Pdag β a μ (t/8)‖ := by
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub _ _)] at hholder
    simpa only [ENNReal.ofReal_ofNat, ← Lp.norm_def] using hholder
  have hpow : (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C ≤ 3 ^ C :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hzsq : ‖ζ‖ ^ 2 * (t : ℝ) ≤ 4 := by
    have hs := Real.sq_sqrt htpos.le
    have hsquare := (sq_le_sq₀ (mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg _)) (by norm_num)).2 hz
    rw [mul_pow, hs] at hsquare
    norm_num at hsquare ⊢
    exact hsquare
  have hexp : Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (4 * Cp) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hscale : ((t : ℝ) / 8) ^ (-q) = 8 ^ q * (t : ℝ) ^ (-q) := by
    rw [Real.div_rpow htpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbpow : 0 ≤ (min (1/16) ((2 * B) ^ (-2 / α))) ^ (α / 2) := Real.rpow_nonneg hb.le _
  have hbound : A * (min (1/16) ((2 * B) ^ (-2 / α))) ^ (α / 2) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (le_max_right 1 A) hbpow).trans habs
  have hfac : C * (min (1/16) ((2 * B) ^ (-2 / α))) ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * 8 ^ q ≤ 1 / 2 := by
    calc
      _ ≤ C * (min (1/16) ((2 * B) ^ (-2 / α))) ^ (α / 2) * 3 ^ C * Real.exp (4 * Cp) * 8 ^ q := by gcongr
      _ = A * (min (1/16) ((2 * B) ^ (-2 / α))) ^ (α / 2) := by dsimp [A]; ring
      _ ≤ 1 / 2 := hbound
  rw [show (-(1 / 2 + (d : ℝ) / 4)) = -q by rfl, hscale] at hU
  have h := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ C * (min (1/16) ((2 * B) ^ (-2 / α))) ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)))
  have h' := mul_le_mul_of_nonneg_right hfac (mul_nonneg hK (Real.rpow_nonneg htpos.le (-q)))
  calc
    _ ≤ _ := hholder'
    _ ≤ (K/2) * (t : ℝ) ^ (-q) := by nlinarith [h, h']

end EinsteinFull.Blueprint
