import EinsteinFull.Regeneration.TrialContraction
import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationNoReturn

/-!
# Exponential moment of the first regeneration endpoint

Under the positive slab-exit estimate of GMP Lemma 4.3, the split coupling of every
supplied reduced diffusion has an exponential moment of the scaled displacement at the
first regeneration time, with constants uniform in the environment law and the force
(GMP (5.26); the argument follows Shen, Theorem 4.9, with the uniform window estimate
needed for the rounded failure times).
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The candidate moment factor in real form. -/
theorem candidate_factor_eq_ofReal (lam l a₂ ρ D₁ : ℝ) (hlam : 0 < lam) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) :
    ENNReal.ofReal (Real.exp (a₂ * lam * (11 * (l / lam)))) *
        ((1 - ENNReal.ofReal ρ)⁻¹ * ENNReal.ofReal D₁) =
      ENNReal.ofReal (Real.exp (11 * a₂ * l) * D₁ / (1 - ρ)) := by
  have hρ' : 0 < 1 - ρ := sub_pos.mpr hρ1
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hρ0, ← ENNReal.ofReal_inv_of_pos hρ',
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hρ'.le), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  have h : a₂ * lam * (11 * (l / lam)) = 11 * a₂ * l := by field_simp
  rw [h, div_eq_mul_inv]
  ring

/-- Uniform exponential moment of the first regeneration endpoint, conditional on the
positive slab-exit estimate of GMP Lemma 4.3. -/
theorem uniform_first_regeneration_endpoint_moment (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ)
    (hL : 1 ≤ L) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l δ : ℝ, l₀ ≤ l → r < 2 * l → 0 < δ → δ < 1 →
      ∃ s D : ℝ, 0 < s ∧ 0 < D ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
        IsRegenerationCoupling hd Q μ l δ hμ.le hμ1 P K →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        Integrable (fun q : FieldPair d × CoupledSample d =>
          Real.exp (s * (μ * (q.2.1 (firstRegenerationTime (Renewal.regenDelta μ)
            μ (l / μ) q.2 (Renewal.forceCoord hd)).toNNReal (Renewal.forceCoord hd) -
              q.2.1 0 (Renewal.forceCoord hd))))) (annealedCoupledLaw Q.measure K) ∧
        (∫ q : FieldPair d × CoupledSample d,
          Real.exp (s * (μ * (q.2.1 (firstRegenerationTime (Renewal.regenDelta μ)
            μ (l / μ) q.2 (Renewal.forceCoord hd)).toNNReal (Renewal.forceCoord hd) -
              q.2.1 0 (Renewal.forceCoord hd)))) ∂annealedCoupledLaw Q.measure K) ≤ D := by
  obtain ⟨c, Cw, l₁, hc, hCw, hl₁, hfailU⟩ := uniform_trial_failure_factor d hd Λ r L hL
  obtain ⟨l₂, hl₂, hfin⟩ := first_regeneration_finite_of_positive_slab_exit d hd Λ r L hL
  refine ⟨max l₁ l₂, lt_of_lt_of_le hl₁ (le_max_left _ _), ?_⟩
  intro l δ hl hsep hδ0 hδ1
  have hlpos : 0 < l := lt_of_lt_of_le hl₁ ((le_max_left _ _).trans hl)
  obtain ⟨a₂, D₁, ρ, ha₂, hD₁, hρ0, hρ1, hconst⟩ :=
    uniform_candidate_round_constants hd Λ r l hlpos δ hδ0 hδ1
  set B₀ : ℝ := Real.exp (11 * a₂ * l) * D₁ / (1 - ρ) with hB₀def
  have hB₀ : 0 ≤ B₀ := div_nonneg (mul_nonneg (Real.exp_pos _).le hD₁) (sub_pos.mpr hρ1).le
  set A : ℝ := max (c * B₀ / a₂) Cw with hAdef
  have hA : 0 ≤ A := le_max_of_le_right hCw
  obtain ⟨θ, hθ0, hθ1, _, hθlt⟩ := exists_small_tilt_contraction (13 * c * l) A (1 / 4) (1 / 2)
    hA (by norm_num) (by norm_num) (by norm_num)
  set θ' : ℝ := min θ (a₂ / c) with hθ'def
  have hθ'0 : 0 < θ' := lt_min hθ0 (div_pos ha₂ hc)
  have hθ'θ : θ' ≤ θ := min_le_left _ _
  have hθ'1 : θ' ≤ 1 := hθ'θ.trans hθ1
  set a : ℝ := θ' * c with hadef
  have ha : 0 < a := mul_pos hθ'0 hc
  have haa : a ≤ a₂ := by
    have h := mul_le_mul_of_nonneg_right (min_le_right θ (a₂ / c)) hc.le
    rw [div_mul_cancel₀ _ hc.ne'] at h
    exact h
  set q : ℝ := Real.exp (13 * c * l * θ') * (1 + θ' * A) ^ 2 * (1 / 2 + θ' * (1 / 4)) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq : q < 1 := by
    refine lt_of_le_of_lt ?_ hθlt
    have h1 : Real.exp (13 * c * l * θ') ≤ Real.exp (13 * c * l * θ) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hθ'θ (by positivity))
    have h2 : (1 + θ' * A) ^ 2 ≤ (1 + θ * A) ^ 2 := by
      have : 1 + θ' * A ≤ 1 + θ * A := by nlinarith
      exact pow_le_pow_left₀ (by positivity) this 2
    have h3 : 1 / 2 + θ' * (1 / 4) ≤ 1 / 2 + θ * (1 / 4) := by linarith
    calc q ≤ Real.exp (13 * c * l * θ) * (1 + θ' * A) ^ 2 * (1 / 2 + θ' * (1 / 4)) := by
          rw [hqdef]; gcongr
      _ ≤ Real.exp (13 * c * l * θ) * (1 + θ * A) ^ 2 * (1 / 2 + θ' * (1 / 4)) := by gcongr
      _ ≤ Real.exp (13 * c * l * θ) * (1 + θ * A) ^ 2 * (1 / 2 + θ * (1 / 4)) := by gcongr
  set B : ℝ := Real.exp (a * (3 * l)) * (1 + a / a₂ * B₀) with hBdef
  have hB : 0 < B := by positivity
  refine ⟨a, B / (1 - q), ha, div_pos hB (sub_pos.mpr hq), ?_⟩
  intro Q μ hμ hμ1 P K hK hpos
  obtain ⟨h1st, hcoin⟩ := hconst Q μ hμ hμ1 P K hK
  have hfail := hfailU Q μ hμ hμ1 P hK.2.2.1 hpos l ((le_max_left _ _).trans hl) θ' hθ'0.le hθ'1
  have hfinite := hfin Q μ hμ hμ1 l δ ((le_max_right _ _).trans hl) hsep hδ0 hδ1 P K hK hpos
  have hΔ : 0 < Renewal.regenDelta μ := EinsteinRelation.regenDelta_pos hμ
  have hB₀E := candidate_factor_eq_ofReal μ l a₂ ρ D₁ hμ hρ0 hρ1
  apply first_regeneration_endpoint_moment_of_trial_contraction (annealedCoupledLaw Q.measure K)
    (Renewal.regenDelta μ) hΔ μ (l / μ) a (Renewal.forceCoord hd) B q hB.le hq0 hq hfinite
  · have h := trial_moment_first hd Q μ hμ hμ1 l δ hlpos hsep hδ0 hδ1 P K hK a a₂ D₁ ρ ha.le ha₂
      haa h1st hcoin
    rw [hB₀E] at h
    refine h.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (div_nonneg ha.le ha₂.le), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (mul_nonneg (div_nonneg ha.le ha₂.le) hB₀),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  · intro n
    have h := trial_moment_step hd Q μ hμ hμ1 l δ hlpos hsep hδ0 hδ1 P K hK a a₂ D₁ ρ
      (Real.exp (θ' * c * (13 * l)) * ((1 + θ' * Cw) * (1 / 2 + θ' / 4))) ha.le ha₂ haa
      h1st hcoin hfail n
    rw [hB₀E] at h
    have hfactor : (1 + ENNReal.ofReal (a / a₂) * ENNReal.ofReal B₀) *
        ENNReal.ofReal (Real.exp (θ' * c * (13 * l)) * ((1 + θ' * Cw) * (1 / 2 + θ' / 4))) ≤
        ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_mul (div_nonneg ha.le ha₂.le), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (mul_nonneg (div_nonneg ha.le ha₂.le) hB₀),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hfac1 : 1 + a / a₂ * B₀ ≤ 1 + θ' * A := by
        have h1 : a / a₂ * B₀ = θ' * (c * B₀ / a₂) := by rw [hadef]; field_simp
        rw [h1]
        have h2 : c * B₀ / a₂ ≤ A := le_max_left _ _
        nlinarith
      have hfac2 : 1 + θ' * Cw ≤ 1 + θ' * A := by
        have h2 : Cw ≤ A := le_max_right _ _
        nlinarith
      have hexp : Real.exp (θ' * c * (13 * l)) = Real.exp (13 * c * l * θ') := by ring_nf
      rw [hexp, hqdef]
      have hpos1 : 0 ≤ 1 + a / a₂ * B₀ := by positivity
      have hpos2 : 0 ≤ 1 + θ' * Cw := by positivity
      have hpos3 : 0 ≤ 1 / 2 + θ' / 4 := by positivity
      calc (1 + a / a₂ * B₀) * (Real.exp (13 * c * l * θ') * ((1 + θ' * Cw) * (1 / 2 + θ' / 4)))
          ≤ (1 + θ' * A) * (Real.exp (13 * c * l * θ') * ((1 + θ' * A) * (1 / 2 + θ' / 4))) := by
            gcongr
        _ = Real.exp (13 * c * l * θ') * (1 + θ' * A) ^ 2 * (1 / 2 + θ' * (1 / 4)) := by ring
    have hfinal : (1 + ENNReal.ofReal (a / a₂) * ENNReal.ofReal B₀) *
        ENNReal.ofReal (Real.exp (θ' * c * (13 * l)) * ((1 + θ' * Cw) * (1 / 2 + θ' / 4))) *
        ∫⁻ q, trialStartWeight (Renewal.regenDelta μ) μ (l / μ) a (Renewal.forceCoord hd) n q.2
          ∂annealedCoupledLaw Q.measure K ≤
        ENNReal.ofReal q * ∫⁻ q, trialStartWeight (Renewal.regenDelta μ) μ (l / μ) a
          (Renewal.forceCoord hd) n q.2 ∂annealedCoupledLaw Q.measure K := by
      gcongr
    exact h.trans hfinal


/-- GMP Lemma 5.8, (5.22) and (5.20) for the split coupling, conditional only on the
positive slab-exit estimate of GMP Lemma 4.3: the no-return probability is at least
one half and the first regeneration time has an exponential tail on the scale `λ⁻²`. -/
theorem first_regeneration_bounds_of_positive_exit (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ)
    (hL : 1 ≤ L) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCoupling hd Q μ l δ hμ.le hμ1 P K →
      (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
        coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
          (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
      ENNReal.ofReal (1 / 2 : ℝ) ≤
        annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / μ)) ∧
      ∀ t : ℝ, 0 ≤ t →
        annealedCoupledLaw Q.measure K {q | ENNReal.ofReal t < regenerationTime hd μ l 1 q.2} ≤
          ENNReal.ofReal (C * Real.exp (-c * μ ^ 2 * t)) := by
  obtain ⟨l₁, hl₁, hsep₁, hbounds⟩ :=
    first_regeneration_bounds_of_positive_exit_and_moment d hd Λ r L hL
  obtain ⟨l₂, hl₂, hmoment⟩ := uniform_first_regeneration_endpoint_moment d hd Λ r L hL
  refine ⟨max l₁ l₂, lt_of_lt_of_le hl₁ (le_max_left _ _),
    lt_of_lt_of_le hsep₁ (by linarith [le_max_left l₁ l₂]), ?_⟩
  intro l hl δ hδ0 hδ1
  have hl₁' : l₁ ≤ l := (le_max_left _ _).trans hl
  have hsep : r < 2 * l := lt_of_lt_of_le hsep₁ (by linarith)
  obtain ⟨s, D, hs, hD, hmom⟩ := hmoment l δ ((le_max_right _ _).trans hl) hsep hδ0 hδ1
  obtain ⟨c, C, hc, hC, hfinal⟩ := hbounds l δ hl₁' hδ0 hδ1 s D hs hD
  refine ⟨c, C, hc, hC, ?_⟩
  intro Q μ hμ hμ1 P K hK hpos
  obtain ⟨hint, hle⟩ := hmom Q μ hμ hμ1 P K hK hpos
  exact hfinal Q μ hμ hμ1 P K hK hpos hint hle

end EinsteinFull.Regeneration
