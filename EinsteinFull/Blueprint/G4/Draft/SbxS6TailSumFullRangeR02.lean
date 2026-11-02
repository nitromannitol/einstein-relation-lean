import EinsteinFull.Calculus.S3TailSumSupport
import EinsteinFull.Blueprint.Roots.node_p_u3A_tail
import EinsteinFull.Calculus.CLBilinearTranspose

/-! Conditional full-range mixing consumer; draft and not an adopted reduction. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint.SbxS6TailSumFullRangeR02

open EinsteinRelation EinsteinFull EinsteinFull.AnnuliSupport

/-- Literal signed full-range smooth local mixing. -/
def fullRangeSmoothLocalMixingStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l p c C : ℝ,
      0 < l ∧ D.dependenceRange < 2 * l ∧ 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ),
      0 < |lam| → |lam| ≤ 1 →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P →
    ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) F →
      IsRealLocalObservation Q (A / |lam|) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * P t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal


/-- Tail summation throughout the range of the endpoint inputs. -/
def tailSumFullRangeStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l p C c C_T : ℝ,
    0 < l ∧ D.dependenceRange < 2 * l ∧ 2 ≤ p ∧
    0 < C ∧ 0 < c ∧ 2 ≤ C_T ∧
  ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β →
    IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P →
    IsComplexTransposeSemigroup Q P Pdag →
    let s := |lam|
    let T : ℝ≥0 := ((s ^ 2)⁻¹).toNNReal
    let h : ℝ := 1 + (d : ℝ) / 2
    let F := transposeEndpoint Q ⟨0, by omega⟩ Pdag β T
    ∀ (j : Fin d) (velocity : Bool),
    let G := if velocity then velocityEndpoint Q ⟨0, by omega⟩ j (lam : ℂ) P β a T
      else clockEndpoint Q (lam : ℂ) P μ T
    let E := fun (U : Lp ℂ 2 (reducedLaw Q)) (n : ℕ) =>
      (condExpL2 ℂ ℂ (Probability.localSigma_le_borel
        {x : Vec d | euclideanNorm x < (n : ℝ) * l / s}) U : Lp ℂ 2 (reducedLaw Q))
    let Δ := fun (U : Lp ℂ 2 (reducedLaw Q)) (n : ℕ) =>
      if n = 1 then E U 1 else E U n - E U (n - 1)
    let normp := fun U : Lp ℂ 2 (reducedLaw Q) =>
      (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
    ∀ t : ℝ≥0, C_T / s ^ 2 ≤ (t : ℝ) →
    let pair := fun k : ℕ × ℕ =>
      ∫ ω, Δ F (k.1 + 1) ω * P (t - 2 * T) (Δ G (k.2 + 1)) ω ∂reducedLaw Q
    let K := if velocity then velocityCorrelation Q ⟨0, by omega⟩ j (lam : ℂ) P β a t
      else clockCorrelation Q ⟨0, by omega⟩ (lam : ℂ) P β μ t
    (∀ n m : ℕ,
      ‖pair (n, m)‖ ≤
        C * Real.exp (C * ((n + 1 : ℕ) + (m + 1 : ℕ)) -
          c * s ^ 2 * ((t : ℝ) - 2 * (T : ℝ))) *
          normp (Δ F (n + 1)) * normp (Δ G (m + 1))) ∧
    Summable (fun k => ‖pair k‖) ∧
    HasSum pair K ∧
    (∑' k, ‖pair k‖) ≤
      C * s ^ (2 * h) * Real.exp (C * Real.sqrt (Real.log (1 / s)) -
        c * s ^ 2 * ((t : ℝ) - 2 * (T : ℝ))) ∧
    2 * h = (d : ℝ) + 2 ∧ s ^ 2 * (T : ℝ) = 1 ∧
    ‖K‖ ≤ C * s ^ (d + 2) *
      Real.exp (C * Real.sqrt (Real.log (1 / s)) - c * lam ^ 2 * (t : ℝ))


/-- Conditional consumer using the original endpoint and annular inputs. -/
theorem tail_sum_full_range_of_local_mixing
    (hsmall : node_p_u3A_tail_u23_small_u2D_endpointsStmt)
    (hann : node_p_u3A_tail_u23_annuliStmt)
    (hlm : fullRangeSmoothLocalMixingStmt) :
    tailSumFullRangeStmt := by
  intro d hd D
  obtain ⟨lm, pm, cm, Cm, hlm0, hlmr, hpm, hcm, hCm, hmixQ⟩ :=
    hlm d hd D
  obtain ⟨l₀, ca, N, hl₀, hl₀r, hca, hann2⟩ := hann d hd D
  obtain ⟨Cs, hCs, hsQ⟩ := hsmall d hd D pm hpm
  obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = max lm l₀ := ⟨_, rfl⟩
  have hlml : lm ≤ l := by rw [hldef]; exact le_max_left _ _
  have hl₀l : l₀ ≤ l := by rw [hldef]; exact le_max_right _ _
  have hlpos : 0 < l := lt_of_lt_of_le hlm0 hlml
  obtain ⟨Ca, C₁, C₂, hCa, hC₁, hC₂, hannQ⟩ :=
    hann2 l pm (Cm * l) hl₀l hpm (mul_pos hCm hlpos).le
  refine ⟨l, pm, Cm * Ca ^ 2 + 2 * Ca + 2 * cm + Cm + Cm * l, cm, 2,
    hlpos, by linarith, hpm, by positivity, hcm, le_refl _, ?_⟩
  intro Q hQ β a μ hβ ha hμ lam hlam hlam₀ P Pdag hP hPd
  haveI := reducedLaw_probability Q
  intro s T h F j velocity G E Δ normp t ht pair K
  have hs : 0 < |lam| := hlam
  have hs1 : |lam| ≤ Real.exp (-1) := hlam₀
  have hsm : |lam| ≤ 1 := hs1.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hTdef : ((T : ℝ≥0) : ℝ) = (s ^ 2)⁻¹ := Real.coe_toNNReal _ (by positivity)
  have hT : (T : ℝ) * |lam| ^ 2 = 1 := by
    rw [hTdef]; exact inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')
  have h2Tr : 2 * (T : ℝ) ≤ (t : ℝ) := by
    rw [hTdef]
    calc 2 * (s ^ 2)⁻¹ = 2 / s ^ 2 := by ring
      _ ≤ (t : ℝ) := ht
  have h2T : 2 * T ≤ t := by
    apply NNReal.coe_le_coe.1
    push_cast
    exact h2Tr
  obtain ⟨-, -, -, -, -, hKid'⟩ := hsQ Q hQ β a μ hβ ha hμ lam hlam hs1 P Pdag hP hPd j velocity
  have hKid := hKid' t h2T
  have hA := hannQ Q hQ β a μ hβ ha hμ lam hlam hs1 P Pdag hP hPd j velocity
  have hAF := hA F (Set.mem_insert _ _)
  have hAG := hA G (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hFA : AnnData Q l |lam| pm (Cm * l) Ca h F := by
    obtain ⟨-, hΔ, hsum, htsum, -⟩ := hAF
    exact ⟨fun n hn => ⟨(hΔ n hn).1, (hΔ n hn).2.1, (hΔ n hn).2.2.1⟩, hsum, htsum⟩
  have hGA : AnnData Q l |lam| pm (Cm * l) Ca h G := by
    obtain ⟨-, hΔ, hsum, htsum, -⟩ := hAG
    exact ⟨fun n hn => ⟨(hΔ n hn).1, (hΔ n hn).2.1, (hΔ n hn).2.2.1⟩, hsum, htsum⟩
  have hh2 : 2 * h = (d : ℝ) + 2 := by
    show 2 * (1 + (d : ℝ) / 2) = (d : ℝ) + 2
    ring
  have core := tail_sum_core Q lam l pm lm Cm cm Ca
    (Cm * Ca ^ 2 + 2 * Ca + 2 * cm + Cm + Cm * l) h hlpos hlml hCm hcm hCa hs hs1 hh2
    (le_refl _) P T t hT h2T F G K hKid
    (fun A hA U V hU hV hUm hVm hU0 =>
      hmixQ Q hQ lam hlam hsm P hP A hA U V hU hV hUm hVm hU0 (t - 2 * T))
    hFA hGA
  obtain ⟨c1, c2, c3, c4, c5⟩ := core
  refine ⟨c1, c2, c3, c4, hh2, ?_, c5⟩
  rw [mul_comm]
  exact hT


/-- The full endpoint range supplies the existing cutoff-based summation interface. -/
theorem tail_sum_of_full_range (h : tailSumFullRangeStmt) :
    node_p_u3A_tail_u23_sumStmt := by
  intro d hd D
  obtain ⟨l, p, C, c, CT, hl, hlD, hp, hC, hc, hCT, hsum⟩ := h d hd D
  exact ⟨l, p, C, c, CT, Real.exp (-1), hl, hlD, hp, hC, hc, hCT,
    Real.exp_pos _, le_rfl, hsum⟩

/-- The full-range summation also implies the original tail root. -/
theorem tail_of_full_range_sum (h : tailSumFullRangeStmt) : node_p_u3A_tailStmt := by
  intro d hd D
  obtain ⟨l, p, C, c, CT, hl, hlD, hp, hC, hc, hCT, hsum⟩ := h d hd D
  refine ⟨C, c, CT, hC, hc, by linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ lam hlam hlaml P hP t ht j
  have hT : IsComplexTransposeSemigroup Q P (fun t => bilinearTranspose (P t)) :=
    fun t f g => integral_mul_bilinearTranspose (P t) f g
  have hv := hsum Q hQ β a μ hβ ha hμ lam hlam hlaml P _ hP hT j true t ht
  have hk := hsum Q hQ β a μ hβ ha hμ lam hlam hlaml P _ hP hT j false t ht
  simp only [ite_true, Bool.false_eq_true, ite_false] at hv hk
  exact ⟨hv.2.2.2.2.2.2, hk.2.2.2.2.2.2⟩

end EinsteinFull.Blueprint.SbxS6TailSumFullRangeR02
