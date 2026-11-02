import EinsteinFull.Blueprint.G1.Proofs.S3Annuli
import EinsteinFull.Calculus.S3TailSumPairing
import EinsteinFull.Calculus.S3TailSumNumeric
import EinsteinRelation.Localization.JointObservationSigma

/-!
# Core of `p:tail#sum`

Everything about the endpoints is abstracted: given the local-mixing estimate for the pair
`(U, P(t - 2T) V)`, the annulus data of `F` and `G` (`p:tail#annuli`) and the identity
`K = ∫ F · P(t - 2T) G`, the double series of pairings of the annulus increments is absolutely
summable with the stated bounds and has sum `K`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinFull EinsteinFull.AnnuliSupport

theorem annSigma_iSup {d : ℕ} {l s : ℝ} (hl : 0 < l) (hs : 0 < s) :
    ⨆ n, annSigma (d := d) l s n = (inferInstance : MeasurableSpace (FieldPair d)) := by
  apply le_antisymm (iSup_le fun n => annSigma_le l s n)
  refine (Localization.localSigma_univ_eq_borel (d := d)).symm.le.trans ?_
  unfold localSigma
  apply iSup_le
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm x.1 * s / l)
  have hx : euclideanNorm x.1 < (n : ℝ) * l / s := by
    rw [lt_div_iff₀ hs]
    have := (div_lt_iff₀ hl).1 hn
    linarith
  have hpt : MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 x.1, ω.2 x.1)) inferInstance ≤
      annSigma (d := d) l s n :=
    le_iSup (fun z : ↥{y : Vec d | euclideanNorm y < (n : ℝ) * l / s} =>
      MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 z, ω.2 z)) inferInstance) ⟨x.1, hx⟩
  exact hpt.trans (le_iSup (fun n => annSigma (d := d) l s n) n)

theorem isRealLocalObservation_mono {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {R R' : ℝ}
    (h : R ≤ R') {F : Lp ℂ 2 (reducedLaw Q)} (hF : IsRealLocalObservation Q R F) :
    IsRealLocalObservation Q R' F := by
  obtain ⟨f, hf, hfe⟩ := hF
  refine ⟨f, hf.mono (Probability.localSigma_mono ?_) le_rfl, hfe⟩
  intro x hx
  have hx' : euclideanNorm x < R := hx
  exact lt_of_lt_of_le hx' h

/-- The annulus data of one endpoint, as delivered by `p:tail#annuli`. -/
def AnnData {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    [IsProbabilityMeasure (reducedLaw Q)] (l s p w Ca h : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    Prop :=
  (∀ n : ℕ, 1 ≤ n → IsRealLocalObservation Q ((n : ℝ) * l / s) (annInc Q l s U n) ∧
      MemLp (annInc Q l s U n : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∫ ω, annInc Q l s U n ω ∂reducedLaw Q) = 0) ∧
  Summable (fun k : ℕ => Real.exp (w * ((k + 1 : ℕ) : ℝ)) *
    annNormp Q p (annInc Q l s U (k + 1))) ∧
  (∑' k : ℕ, Real.exp (w * ((k + 1 : ℕ) : ℝ)) * annNormp Q p (annInc Q l s U (k + 1))) ≤
    Ca * s ^ h * Real.exp (Ca * Real.sqrt (Real.log (1 / s)))

/-- The pair bound from local mixing for the increments `Δ_{n+1} F`, `Δ_{m+1} G`. -/
theorem pair_key {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    [IsProbabilityMeasure (reducedLaw Q)]
    (lam l p lm Cm cm : ℝ) (hl : 0 < l) (hlm : lm ≤ l) (hs : 0 < |lam|)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) (T t : ℝ≥0)
    (F G : Lp ℂ 2 (reducedLaw Q))
    (hmix : ∀ A : ℝ, lm ≤ A → ∀ U V : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) U → IsRealLocalObservation Q (A / |lam|) V →
      MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (V : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, U ω ∂reducedLaw Q) = 0 →
      ‖∫ ω, U ω * P (t - 2 * T) V ω ∂reducedLaw Q‖ ≤
        Cm * Real.exp (Cm * A - cm * lam ^ 2 * (((t - 2 * T : ℝ≥0)) : ℝ)) *
          annNormp Q p U * annNormp Q p V)
    (Ca h w : ℝ)
    (hFA : AnnData Q l |lam| p w Ca h F) (hGA : AnnData Q l |lam| p w Ca h G)
    (X : ℝ) (hXe : cm * lam ^ 2 * (((t - 2 * T : ℝ≥0)) : ℝ) = X) (n m : ℕ) :
    ‖∫ ω, annInc Q l |lam| F (n + 1) ω *
        P (t - 2 * T) (annInc Q l |lam| G (m + 1)) ω ∂reducedLaw Q‖ ≤
      Cm * Real.exp (Cm * ((((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l) - X) *
        annNormp Q p (annInc Q l |lam| F (n + 1)) *
        annNormp Q p (annInc Q l |lam| G (m + 1)) := by
  obtain ⟨hFloc, -, -⟩ := id hFA
  obtain ⟨hGloc, -, -⟩ := id hGA
  obtain ⟨hUl, hUm, hU0⟩ := hFloc (n + 1) (by omega)
  obtain ⟨hVl, hVm, -⟩ := hGloc (m + 1) (by omega)
  have hl0 : 0 ≤ l := hl.le
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
  have hn0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA1 : ((n + 1 : ℕ) : ℝ) * l ≤ (((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l := by
    linarith [mul_nonneg hm0 hl0]
  have hA2 : ((m + 1 : ℕ) : ℝ) * l ≤ (((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l := by
    linarith [mul_nonneg hn0 hl0]
  have hAl : lm ≤ (((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l := by
    linarith [mul_nonneg hm0 hl0, mul_nonneg (sub_nonneg.2 hn1) hl0]
  have hr1 : ((n + 1 : ℕ) : ℝ) * l / |lam| ≤
      ((((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l) / |lam| := by gcongr
  have hr2 : ((m + 1 : ℕ) : ℝ) * l / |lam| ≤
      ((((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l) / |lam| := by gcongr
  have hm' := hmix _ hAl _ _ (isRealLocalObservation_mono hr1 hUl)
    (isRealLocalObservation_mono hr2 hVl) hUm hVm hU0
  rw [hXe] at hm'
  exact hm'

@[nolint unusedArguments]
theorem pair_exp_bound {Cm C l X : ℝ} (hCm : 0 < Cm) (hl : 0 < l)
    (hCmlC : Cm * l ≤ C) (hCmC : Cm ≤ C) (hCpos : 0 ≤ C) (n m : ℕ) {nU nV : ℝ}
    (hnU : 0 ≤ nU) (hnV : 0 ≤ nV) :
    Cm * Real.exp (Cm * ((((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l) - X) * nU * nV ≤
      C * Real.exp (C * (((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) - X) * nU * nV := by
  have hn0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hexp : Cm * ((((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l) - X ≤
      C * (((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) - X := by
    have := mul_le_mul_of_nonneg_right hCmlC (add_nonneg hn0 hm0)
    linarith
  have h1 : Cm * Real.exp (Cm * ((((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l) - X) ≤
      C * Real.exp (C * (((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) - X) :=
    mul_le_mul hCmC (Real.exp_le_exp.2 hexp) (Real.exp_pos _).le hCpos
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hnU) hnV

theorem L_ge_one {s L : ℝ} (hs : 0 < s) (hs1 : s ≤ Real.exp (-1))
    (hLdef : L = Real.log (1 / s)) : 1 ≤ Real.sqrt L := by
  have h1 : Real.exp 1 ≤ 1 / s := by
    rw [le_div_iff₀ hs]
    calc Real.exp 1 * s ≤ Real.exp 1 * Real.exp (-1) :=
          mul_le_mul_of_nonneg_left hs1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have h2 : 1 ≤ L := by
    rw [hLdef]
    exact (Real.le_log_iff_exp_le (one_div_pos.2 hs)).2 h1
  have := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_one] at this

theorem tail_sum_core {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    [IsProbabilityMeasure (reducedLaw Q)]
    (lam l p lm Cm cm Ca C h : ℝ) (hl : 0 < l) (hlm : lm ≤ l) (hCm : 0 < Cm) (hcm : 0 < cm)
    (hCa : 0 < Ca) (hs : 0 < |lam|) (hs1 : |lam| ≤ Real.exp (-1)) (hh2 : 2 * h = (d : ℝ) + 2)
    (hC1 : Cm * Ca ^ 2 + 2 * Ca + 2 * cm + Cm + Cm * l ≤ C)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (T t : ℝ≥0) (hT : (T : ℝ) * |lam| ^ 2 = 1) (h2T : 2 * T ≤ t)
    (F G : Lp ℂ 2 (reducedLaw Q)) (K : ℂ)
    (hK : K = ∫ ω, F ω * P (t - 2 * T) G ω ∂reducedLaw Q)
    (hmix : ∀ A : ℝ, lm ≤ A → ∀ U V : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) U → IsRealLocalObservation Q (A / |lam|) V →
      MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (V : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, U ω ∂reducedLaw Q) = 0 →
      ‖∫ ω, U ω * P (t - 2 * T) V ω ∂reducedLaw Q‖ ≤
        Cm * Real.exp (Cm * A - cm * lam ^ 2 * (((t - 2 * T : ℝ≥0)) : ℝ)) *
          annNormp Q p U * annNormp Q p V)
    (hFA : AnnData Q l |lam| p (Cm * l) Ca h F) (hGA : AnnData Q l |lam| p (Cm * l) Ca h G) :
    (∀ n m : ℕ, ‖∫ ω, annInc Q l |lam| F (n + 1) ω *
        P (t - 2 * T) (annInc Q l |lam| G (m + 1)) ω ∂reducedLaw Q‖ ≤
      C * Real.exp (C * (((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) -
        cm * |lam| ^ 2 * ((t : ℝ) - 2 * (T : ℝ))) *
        annNormp Q p (annInc Q l |lam| F (n + 1)) *
        annNormp Q p (annInc Q l |lam| G (m + 1))) ∧
    Summable (fun k : ℕ × ℕ => ‖∫ ω, annInc Q l |lam| F (k.1 + 1) ω *
        P (t - 2 * T) (annInc Q l |lam| G (k.2 + 1)) ω ∂reducedLaw Q‖) ∧
    HasSum (fun k : ℕ × ℕ => ∫ ω, annInc Q l |lam| F (k.1 + 1) ω *
        P (t - 2 * T) (annInc Q l |lam| G (k.2 + 1)) ω ∂reducedLaw Q) K ∧
    (∑' k : ℕ × ℕ, ‖∫ ω, annInc Q l |lam| F (k.1 + 1) ω *
        P (t - 2 * T) (annInc Q l |lam| G (k.2 + 1)) ω ∂reducedLaw Q‖) ≤
      C * |lam| ^ (2 * h) * Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) -
        cm * |lam| ^ 2 * ((t : ℝ) - 2 * (T : ℝ))) ∧
    ‖K‖ ≤ C * |lam| ^ (d + 2) * Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) -
      cm * lam ^ 2 * (t : ℝ)) := by
  have ht' : (((t - 2 * T : ℝ≥0)) : ℝ) = (t : ℝ) - 2 * (T : ℝ) := by
    rw [NNReal.coe_sub h2T]; push_cast; ring
  have hl2 : lam ^ 2 = |lam| ^ 2 := (sq_abs lam).symm
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = cm * |lam| ^ 2 * ((t : ℝ) - 2 * (T : ℝ)) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (1 / |lam|) := ⟨_, rfl⟩
  have hL1 := L_ge_one hs hs1 hLdef
  have hnn : ∀ U : Lp ℂ 2 (reducedLaw Q), 0 ≤ annNormp Q p U := fun U => ENNReal.toReal_nonneg
  have hXe : cm * lam ^ 2 * (((t - 2 * T : ℝ≥0)) : ℝ) = X := by rw [ht', hl2, hX]
  have key := pair_key Q lam l p lm Cm cm hl hlm hs P T t F G hmix Ca h (Cm * l) hFA hGA X hXe
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun k => Real.exp ((Cm * l) * ((k + 1 : ℕ) : ℝ)) *
      annNormp Q p (annInc Q l |lam| F (k + 1)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun k => Real.exp ((Cm * l) * ((k + 1 : ℕ) : ℝ)) *
      annNormp Q p (annInc Q l |lam| G (k + 1)) := ⟨_, rfl⟩
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    rw [ha]; exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    rw [hb]; exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  obtain ⟨-, hFsum, hFtsum⟩ := id hFA
  obtain ⟨-, hGsum, hGtsum⟩ := id hGA
  have hasum : Summable a := by rw [ha]; exact hFsum
  have hbsum : Summable b := by rw [hb]; exact hGsum
  obtain ⟨Sa, hSa⟩ : ∃ Sa : ℝ,
      Sa = Ca * |lam| ^ h * Real.exp (Ca * Real.sqrt (Real.log (1 / |lam|))) := ⟨_, rfl⟩
  have hatsum : ∑' k, a k ≤ Sa := by rw [ha, hSa]; exact hFtsum
  have hbtsum : ∑' k, b k ≤ Sa := by rw [hb, hSa]; exact hGtsum
  have P1 : ∀ n m : ℕ, ‖∫ ω, annInc Q l |lam| F (n + 1) ω *
      P (t - 2 * T) (annInc Q l |lam| G (m + 1)) ω ∂reducedLaw Q‖ ≤
      Cm * Real.exp (-X) * (a n * b m) := by
    intro n m
    have e : Real.exp (Cm * ((((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ)) * l) - X) =
        Real.exp ((Cm * l) * ((n + 1 : ℕ) : ℝ)) * Real.exp ((Cm * l) * ((m + 1 : ℕ) : ℝ)) *
          Real.exp (-X) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    refine (key n m).trans (le_of_eq ?_)
    rw [e]
    simp only [ha, hb]
    ring
  have hEnn : 0 ≤ Cm * Real.exp (-X) := mul_nonneg hCm.le (Real.exp_pos _).le
  obtain ⟨hpair, hsum1⟩ := pair_series_bound
    (fun k : ℕ × ℕ => ∫ ω, annInc Q l |lam| F (k.1 + 1) ω *
      P (t - 2 * T) (annInc Q l |lam| G (k.2 + 1)) ω ∂reducedLaw Q) a b ha0 hb0 hasum hbsum
    Sa Cm (Real.exp (-X)) hatsum hbtsum hEnn P1
  have hhas := hasSum_lpPair_annDelta (annSigma_mono (d := d) hl.le hs) (annSigma_le l |lam|)
    (annSigma_iSup hl hs) (P (t - 2 * T)) F G hpair
  have hhas' : HasSum (fun k : ℕ × ℕ => ∫ ω, annInc Q l |lam| F (k.1 + 1) ω *
      P (t - 2 * T) (annInc Q l |lam| G (k.2 + 1)) ω ∂reducedLaw Q) K := by
    rw [hK]; exact hhas
  have hKn : ‖K‖ ≤ ∑' k : ℕ × ℕ, ‖∫ ω, annInc Q l |lam| F (k.1 + 1) ω *
      P (t - 2 * T) (annInc Q l |lam| G (k.2 + 1)) ω ∂reducedLaw Q‖ := by
    rw [← hhas'.tsum_eq]; exact norm_tsum_le_tsum_norm hpair
  have hcT : cm * |lam| ^ 2 * (T : ℝ) = cm := by
    rw [mul_assoc, mul_comm (|lam| ^ 2), hT, mul_one]
  have hXe2 : -X = -(cm * lam ^ 2 * (t : ℝ)) + 2 * cm := by
    rw [hX, hl2]; linear_combination 2 * hcT
  obtain ⟨hc4, hc5⟩ := tail_sum_bounds d _ ‖K‖ Cm Ca cm C l |lam| h L X
    (cm * lam ^ 2 * (t : ℝ)) Sa hl hCm hcm hCa hs hL1 hh2 hC1 hXe2
    (by rw [hSa, hLdef]) hKn hsum1
  have hp1 : 0 < Cm * l := mul_pos hCm hl
  have hp2 : 0 ≤ Cm * Ca ^ 2 := mul_nonneg hCm.le (sq_nonneg Ca)
  have hCpos : 0 ≤ C := by linarith
  have hCmlC : Cm * l ≤ C := by linarith
  have hCmC : Cm ≤ C := by linarith
  refine ⟨?_, hpair, hhas', ?_, ?_⟩
  · intro n m
    refine (key n m).trans ?_
    rw [← hX]
    exact pair_exp_bound hCm hl hCmlC hCmC hCpos n m (hnn _) (hnn _)
  · rw [← hX, ← hLdef]; exact hc4
  · rw [← hLdef]; exact hc5

end EinsteinFull.Blueprint
