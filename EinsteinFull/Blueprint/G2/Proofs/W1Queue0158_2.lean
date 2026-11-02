import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_smoothing_u2D_selection
import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average
import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_bootstrap_u2D_average
import EinsteinFull.Calculus.ScalarWeightSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem lp_add_bound {X : Type*} [MeasurableSpace X] (m : Measure X)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f g : Lp ℂ 2 m)
    (hf : MemLp (f : X → ℂ) p m) (hg : MemLp (g : X → ℂ) p m) :
    MemLp ((f + g : Lp ℂ 2 m) : X → ℂ) p m ∧
      (eLpNorm ((f + g : Lp ℂ 2 m) : X → ℂ) p m).toReal ≤
        (eLpNorm (f : X → ℂ) p m).toReal +
        (eLpNorm (g : X → ℂ) p m).toReal := by
  refine ⟨(memLp_congr_ae (Lp.coeFn_add f g)).2 (hf.add hg), ?_⟩
  rw [eLpNorm_congr_ae (Lp.coeFn_add f g)]
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hp)).trans_eq
    (ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top)

/-- The fixed scalar smoothing selection, with exactly its two graph dependencies. -/
theorem node_p_u3A_scalar_u23_smoothing_u2D_selection_of_deps
    (hHolder : node_e_u3A_holder_u2D_averageStmt)
    (hBootstrap : node_p_u3A_scalar_u23_bootstrap_u2D_averageStmt) :
    node_p_u3A_scalar_u23_smoothing_u2D_selectionStmt := by
  intro d hd D
  obtain ⟨α, hα, hHolder⟩ := hHolder d hd D
  obtain ⟨ε, η, _, _, _, hBootstrap⟩ := hBootstrap d hd D
  refine ⟨1 / 16, by norm_num, le_rfl, ?_⟩
  intro p hp
  obtain ⟨C, Cp, hC, hCp, hHolder⟩ := hHolder p hp
  obtain ⟨_, growth₀, _, _, hgrowth₀, _, _, _⟩ :=
    hBootstrap (1 / 16) (by norm_num) le_rfl p hp
  let h : ℝ := 1 / 2 + (d : ℝ) / 4
  let L : ℝ := (1 / 8 : ℝ) ^ (-h)
  let A : ℝ := C * L
  have hA : 0 ≤ A := mul_nonneg (by linarith only [hC]) (Real.rpow_nonneg (by norm_num) _)
  obtain ⟨hb, hba, habsorb⟩ := normalized_holder_absorption (1 / 16) A C α
    (by norm_num) hA (by linarith only [hC]) hα
  let b := min (1 / 16 : ℝ) ((2 * max 1 (A * Real.exp (C ^ 2 / 4))) ^ (-2 / α))
  change 0 < b at hb
  change b ≤ 1 / 16 at hba
  let growth := 8 * (Cp + growth₀ + 1)
  have hgrowth : 0 < growth := by dsimp [growth]; positivity
  refine ⟨b, growth, max 16 b⁻¹, hb, hba, hgrowth,
    le_max_left _ _, le_max_right _ _, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  dsimp only
  let U := fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t
  let w := fun s : ℝ => s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)
  let N := fun f : Lp ℂ 2 (reducedLaw Q) =>
    (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
  change ∀ t : ℝ≥0, _ → ∀ Kprime : ℝ, _ → _ → _ → _
  intro t ht Kprime hK _hmem₈ hbound₈ hbt
  have htpos : 0 < (t : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 16)
    ((le_max_left _ _).trans ht)
  obtain ⟨herrmem₀, herr⟩ := (hHolder Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t
    htpos).2 b hb hba hbt
  have heq := Lp.coeFn_sub (U t) (gaussianAverage hd Q (b * (t : ℝ)) hbt (U t))
  have herrmem := (memLp_congr_ae heq).2 herrmem₀
  rw [← eLpNorm_congr_ae heq] at herr
  have hw : 0 ≤ w (t : ℝ) := add_nonneg (Real.rpow_nonneg htpos.le _)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg htpos.le _))
  have hw₈ : w ((t : ℝ) / 8) ≤ L * w (t : ℝ) := by
    simpa only [w, L, div_eq_mul_inv, one_mul, mul_comm, neg_div, neg_mul] using
      scalar_decay_weight_mul_le (1 / 8) (t : ℝ) ‖ζ‖ h ((d : ℝ) / 4)
      (by norm_num) (by norm_num) htpos (norm_nonneg _) (by dsimp [h]; linarith)
  have herr' : N (U t - gaussianAverage hd Q (b * (t : ℝ)) hbt (U t)) ≤
      (Kprime / 2) * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * w (t : ℝ) := by
    let M := ‖ζ‖ * Real.sqrt (t : ℝ)
    have hMsq : M ^ 2 = ‖ζ‖ ^ 2 * (t : ℝ) := by
      dsimp [M]; rw [mul_pow, Real.sq_sqrt htpos.le]
    have hab := habsorb M (7 * growth / 8 - Cp) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (by dsimp [growth]; linarith)
    have hexp : Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) =
        Real.exp (-(7 * growth / 8 - Cp) * M ^ 2) *
          Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add, hMsq]
      congr 1
      ring
    calc
      _ ≤ C * b ^ (α / 2) * (1 + M) ^ C *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * N (U (t / 8)) := herr
      _ ≤ C * b ^ (α / 2) * (1 + M) ^ C *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (Kprime * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
            (L * w (t : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        · exact hbound₈.trans (mul_le_mul_of_nonneg_left hw₈ (by positivity))
        · positivity
      _ = (A * b ^ (α / 2) * (1 + M) ^ C *
          Real.exp (-(7 * growth / 8 - Cp) * M ^ 2)) *
          (Kprime * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * w (t : ℝ)) := by
        dsimp only [A]
        calc
          _ = (C * L * b ^ (α / 2) * (1 + M) ^ C) *
              (Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
                Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8)) *
              (Kprime * w (t : ℝ)) := by ring
          _ = _ := by rw [hexp]; ring
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right hab
          (mul_nonneg (mul_nonneg (by linarith only [hK]) (Real.exp_pos _).le) hw) using 1
        ring
  refine ⟨herrmem₀, ?_, ?_⟩
  · exact herr'
  intro Kavg hKavg havgmem havg
  have hadd := lp_add_bound (reducedLaw Q) (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith))
    (U t - gaussianAverage hd Q (b * (t : ℝ)) hbt (U t))
    (gaussianAverage hd Q (b * (t : ℝ)) hbt (U t)) herrmem havgmem
  rw [sub_add_cancel] at hadd
  refine ⟨hadd.1, ?_⟩
  have hwb : w (b * (t : ℝ)) ≤ b ^ (-h) * w (t : ℝ) := by
    simpa only [w, neg_div] using scalar_decay_weight_mul_le b (t : ℝ) ‖ζ‖ h ((d : ℝ) / 4)
      hb (hba.trans (by norm_num)) htpos (norm_nonneg _) (by dsimp [h]; linarith)
  change N (U t) ≤ (b ^ (-h) * Kavg + Kprime / 2) *
    Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * w (t : ℝ)
  change N (gaussianAverage hd Q (b * (t : ℝ)) hbt (U t)) ≤
    Kavg * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * w (b * (t : ℝ)) at havg
  calc
    N (U t) ≤ N (U t - gaussianAverage hd Q (b * (t : ℝ)) hbt (U t)) +
        N (gaussianAverage hd Q (b * (t : ℝ)) hbt (U t)) := hadd.2
    _ ≤ (Kprime / 2) * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * w (t : ℝ) +
        Kavg * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * (b ^ (-h) * w (t : ℝ)) :=
      add_le_add herr' (havg.trans (mul_le_mul_of_nonneg_left hwb (by positivity)))
    _ = _ := by ring

end EinsteinFull.Blueprint
