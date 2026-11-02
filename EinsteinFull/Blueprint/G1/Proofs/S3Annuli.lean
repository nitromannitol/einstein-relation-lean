import EinsteinFull.Blueprint.G1.node_p_u3A_tail_u23_annuli
import EinsteinFull.Blueprint.G1.node_p_u3A_tail_u23_small_u2D_endpoints
import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_local
import EinsteinFull.Blueprint.G1.Proofs.S3AnnuliReal
import EinsteinFull.Calculus.S3AnnuliDelta
import EinsteinFull.Calculus.S3AnnuliSums

/-!
# `p:tail#annuli`

Derived from `p:tail#small-endpoints` (`L^p` size, centering) and `l:forced-local` (complex local
approximants at time `s⁻²`). Realness of the endpoints comes from the proved real-force
semigroup facts of `S3RealSemigroup`; the annulus increments and the weighted sums are generic
support (`S3AnnuliDelta`, `S3AnnuliSums`).
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinFull EinsteinFull.AnnuliSupport

/-- The annulus σ-algebra of Euclidean radius `n l / s`. -/
def annSigma {d : ℕ} (l s : ℝ) (n : ℕ) : MeasurableSpace (FieldPair d) :=
  localSigma {x : Vec d | euclideanNorm x < (n : ℝ) * l / s}

theorem annSigma_le {d : ℕ} (l s : ℝ) (n : ℕ) :
    annSigma (d := d) l s n ≤ (inferInstance : MeasurableSpace (FieldPair d)) :=
  Probability.localSigma_le_borel _

theorem annSigma_mono {d : ℕ} {l s : ℝ} (hl : 0 ≤ l) (hs : 0 < s) :
    Monotone (annSigma (d := d) l s) := by
  intro m n hmn
  apply Probability.localSigma_mono
  intro x hx
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hx' : euclideanNorm x < (m : ℝ) * l / s := hx
  show euclideanNorm x < (n : ℝ) * l / s
  refine lt_of_lt_of_le hx' ?_
  gcongr

/-- The `L^p` norm of a complex class on the reduced law. -/
noncomputable def annNormp {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (p : ℝ)
    (U : Lp ℂ 2 (reducedLaw Q)) : ℝ :=
  (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal

/-- The annulus increment `Δ_n U`. -/
@[nolint unusedArguments]
noncomputable abbrev annInc {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    [IsProbabilityMeasure (reducedLaw Q)] (l s : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) (n : ℕ) :
    Lp ℂ 2 (reducedLaw Q) :=
  annDelta (𝓕 := annSigma l s) (annSigma_le l s) U n

/-- Generic assembly of the annulus clauses for one endpoint `U`. -/
theorem annuli_core {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    [IsProbabilityMeasure (reducedLaw Q)]
    (l p weight s h c K A B Cs C C₂ : ℝ) (N : ℕ)
    (hl : 0 < l) (hp : 2 ≤ p) (hs : 0 < s) (hs1 : s ≤ Real.exp (-1)) (hh : 0 < h)
    (hc : 0 < c) (hK : 0 < K) (hB0 : 0 ≤ B) (hA : 2 * A ≤ K) (hB : 4 * B ≤ K) (hKC : K ≤ C)
    (hCs : Cs ≤ C)
    (hsumb : ∀ s : ℝ, 0 < s → s ≤ Real.exp (-1) → ∀ a : ℕ → ℝ, (∀ k, 0 ≤ a k) →
      (∀ k : ℕ, a k ≤ K * min (s ^ h) (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2))) →
      Summable (fun k : ℕ => Real.exp (weight * ((k + 1 : ℕ) : ℝ)) * a k) ∧
      (∑' k : ℕ, Real.exp (weight * ((k + 1 : ℕ) : ℝ)) * a k) ≤
        Cs * s ^ h * Real.exp (Cs * Real.sqrt (Real.log (1 / s))) ∧
      (∑' k : ℕ, if ⌈1 + C₂ * Real.sqrt (Real.log (1 / s))⌉₊ < k + 1 then
        Real.exp (weight * ((k + 1 : ℕ) : ℝ)) * a k else 0) ≤ Cs * s ^ (h + 1))
    (U : Lp ℂ 2 (reducedLaw Q)) (hreal : AeReal U) (hmean : ∫ ω, U ω ∂reducedLaw Q = 0)
    (hmem : MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q))
    (hnorm : annNormp Q p U ≤ A * s ^ h)
    (happ : ∀ n : ℕ, 1 ≤ n → ∃ V : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q ((n : ℝ) * l / (2 * s)) V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ ≤ B * s ^ (-(N : ℝ)) * Real.exp (-c * (n : ℝ) ^ 2)) :
    (∀ n : ℕ, 1 ≤ n → ∃ V : Lp ℂ 2 (reducedLaw Q),
        IsRealLocalObservation Q ((n : ℝ) * l / (2 * s)) V ∧
        ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ ≤ C * s ^ (-(N : ℝ)) * Real.exp (-c * (n : ℝ) ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n →
        IsRealLocalObservation Q ((n : ℝ) * l / s) (annInc Q l s U n) ∧
        MemLp (annInc Q l s U n : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (∫ ω, annInc Q l s U n ω ∂reducedLaw Q) = 0 ∧
        annNormp Q p (annInc Q l s U n) ≤
          C * min (s ^ h) (s ^ (-(N : ℝ)) * Real.exp (-c * ((n : ℝ) - 1) ^ 2))) ∧
    Summable (fun k : ℕ => Real.exp (weight * (k + 1 : ℕ)) * annNormp Q p (annInc Q l s U (k + 1))) ∧
    (∑' k : ℕ, Real.exp (weight * (k + 1 : ℕ)) * annNormp Q p (annInc Q l s U (k + 1))) ≤
      C * s ^ h * Real.exp (C * Real.sqrt (Real.log (1 / s))) ∧
    (∑' k : ℕ, if ⌈1 + C₂ * Real.sqrt (Real.log (1 / s))⌉₊ < k + 1 then
      Real.exp (weight * (k + 1 : ℕ)) * annNormp Q p (annInc Q l s U (k + 1)) else 0) ≤
        C * s ^ (h + 1) := by
  have hs1' : s ≤ 1 := hs1.trans (Real.exp_le_one_iff.2 (by norm_num))
  have hBC : B ≤ C := by linarith
  have hmono := annSigma_mono (d := d) hl.le hs
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hUt : eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≠ ⊤ :=
    hmem.eLpNorm_lt_top.ne
  have hspos : 0 ≤ s ^ h := Real.rpow_nonneg hs.le h
  have hsN : 0 ≤ s ^ (-(N : ℝ)) := Real.rpow_nonneg hs.le _
  have h𝓖 : ∀ n : ℕ,
      (localSigma {x : Vec d | euclideanNorm x < (n : ℝ) * l / (2 * s)}) ≤ annSigma l s n := by
    intro n
    apply Probability.localSigma_mono
    intro x hx
    have hx' : euclideanNorm x < (n : ℝ) * l / (2 * s) := hx
    have hpos : 0 ≤ (n : ℝ) * l / s := by positivity
    have e : (n : ℝ) * l / (2 * s) = ((n : ℝ) * l / s) / 2 := by field_simp
    show euclideanNorm x < (n : ℝ) * l / s
    exact lt_of_lt_of_le hx' (by rw [e]; linarith)
  have happ' : ∀ n : ℕ, 1 ≤ n → ∃ V : FieldPair d → ℂ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < (n : ℝ) * l / (2 * s)}] V ∧
      ∀ᵐ ω ∂reducedLaw Q,
        ‖U ω - V ω‖ ≤ B * s ^ (-(N : ℝ)) * Real.exp (-c * (n : ℝ) ^ 2) := by
    intro n hn
    obtain ⟨V, ⟨f, hf, hfe⟩, hV⟩ := happ n hn
    refine ⟨fun ω => (f ω : ℂ), by exact Complex.measurable_ofReal.comp hf, ?_⟩
    filter_upwards [hV, hfe] with ω h1 h2
    rw [h2]
    exact h1
  have hε : ∀ n : ℕ, 0 ≤ B * s ^ (-(N : ℝ)) * Real.exp (-c * (n : ℝ) ^ 2) :=
    fun n => mul_nonneg (mul_nonneg hB0 hsN) (Real.exp_pos _).le
  have h2U : ∀ n : ℕ, annNormp Q p (annInc Q l s U n) ≤ K * s ^ h := by
    intro n
    have h1 := normp_annDelta_le_two_mul (annSigma_le l s) U hp1 hUt n
    have h3 := mul_le_mul_of_nonneg_right hA hspos
    have h4 : annNormp Q p (annInc Q l s U n) ≤
        2 * (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := h1
    have h5 : (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        A * s ^ h := hnorm
    linarith
  have hnormA : ∀ k : ℕ, 1 ≤ k → annNormp Q p (annInc Q l s U (k + 1)) ≤
      2 * (B * s ^ (-(N : ℝ)) * Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)) +
        2 * (B * s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2)) := by
    intro k hk
    exact normp_annDelta_le_of_approx (annSigma_le l s) U _ h𝓖
      (fun n : ℕ => B * s ^ (-(N : ℝ)) * Real.exp (-c * (n : ℝ) ^ 2)) hε happ'
      (p := ENNReal.ofReal p) (n := k + 1) (by omega)
  have haK : ∀ k : ℕ, annNormp Q p (annInc Q l s U (k + 1)) ≤
      K * min (s ^ h) (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2)) := by
    intro k
    have h1 := h2U (k + 1)
    have h2 : annNormp Q p (annInc Q l s U (k + 1)) ≤
        K * (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2)) := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have hone : Real.exp (-c * ((0 : ℕ) : ℝ) ^ 2) = 1 := by simp
        have hle : s ^ h ≤ s ^ (-(N : ℝ)) * Real.exp (-c * ((0 : ℕ) : ℝ) ^ 2) := by
          rw [hone, mul_one]
          exact (Real.rpow_le_one hs.le hs1' hh.le).trans
            (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1'
              (neg_nonpos.2 (Nat.cast_nonneg N)))
        exact h1.trans (mul_le_mul_of_nonneg_left hle hK.le)
      · have hb := hnormA k hk
        have hmon : Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2) ≤ Real.exp (-c * (k : ℝ) ^ 2) :=
          Real.exp_le_exp.2 (by
            push_cast
            nlinarith [mul_nonneg hc.le (Nat.cast_nonneg (α := ℝ) k)])
        have hX0 : 0 ≤ s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2) :=
          mul_nonneg hsN (Real.exp_pos _).le
        have e1 : B * s ^ (-(N : ℝ)) * Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2) ≤
            B * (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2)) := by
          calc B * s ^ (-(N : ℝ)) * Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)
              ≤ B * s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left hmon (mul_nonneg hB0 hsN)
            _ = B * (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2)) := by ring
        have e2 : B * s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2) =
            B * (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2)) := by ring
        have e3 := mul_le_mul_of_nonneg_right hB hX0
        linarith
    rcases le_total (s ^ h) (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2)) with hxy | hxy
    · rw [min_eq_left hxy]; exact h1
    · rw [min_eq_right hxy]; exact h2
  have ha0 : ∀ k : ℕ, 0 ≤ annNormp Q p (annInc Q l s U (k + 1)) :=
    fun k => ENNReal.toReal_nonneg
  obtain ⟨hsum1, hsum2, hsum3⟩ :=
    hsumb s hs hs1 (fun k => annNormp Q p (annInc Q l s U (k + 1))) ha0 haK
  refine ⟨?_, ?_, hsum1, ?_, ?_⟩
  · intro n hn
    obtain ⟨V, hV, hb⟩ := happ n hn
    refine ⟨V, hV, hb.mono fun ω h => h.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hsN) (Real.exp_pos _).le
  · intro n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨f, hf, hfe⟩ := annDelta_real (annSigma_le l s) hmono U hreal hn
      exact ⟨f, hf, hfe⟩
    · exact memLp_annDelta (annSigma_le l s) U hp1 hmem n
    · exact integral_annDelta (annSigma_le l s) U hmean n
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hcast : (((k + 1 : ℕ) : ℝ) - 1) = (k : ℝ) := by push_cast; ring
      rw [hcast]
      have hmin : 0 ≤ min (s ^ h) (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2)) :=
        le_min hspos (mul_nonneg hsN (Real.exp_pos _).le)
      exact (haK k).trans (mul_le_mul_of_nonneg_right hKC hmin)
  · refine hsum2.trans ?_
    have hC0 : 0 ≤ C := (hK.trans_le hKC).le
    have hsq : 0 ≤ Real.sqrt (Real.log (1 / s)) := Real.sqrt_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_right hCs hspos)
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hCs hsq)) (Real.exp_pos _).le
      (mul_nonneg hC0 hspos)
  · exact hsum3.trans (mul_le_mul_of_nonneg_right hCs (Real.rpow_nonneg hs.le _))

/-- `p:tail#annuli` from `p:tail#small-endpoints` and `l:forced-local`. -/
theorem node_p_u3A_tail_u23_annuli_of_deps
    (hsmall : node_p_u3A_tail_u23_small_u2D_endpointsStmt)
    (hforced : node_l_u3A_forced_u2D_localStmt) :
    node_p_u3A_tail_u23_annuliStmt := by
  intro d hd D
  obtain ⟨α, Cdet, cF, NF, hα, hCdet1, hcF, hloc⟩ := hforced d hd D
  have hCdet : 0 < Cdet := by linarith
  obtain ⟨C0, Cp0, hC0, hCp0, hmain⟩ := hloc 2 (le_refl _)
  obtain ⟨l₀, hl₀def⟩ : ∃ l₀ : ℝ, l₀ = max (2 * Cdet) (D.dependenceRange / 2 + 1) := ⟨_, rfl⟩
  have hl₀2 : 2 * Cdet ≤ l₀ := by rw [hl₀def]; exact le_max_left _ _
  have hl₀r : D.dependenceRange / 2 + 1 ≤ l₀ := by rw [hl₀def]; exact le_max_right _ _
  have hl₀pos : 0 < l₀ := by linarith
  have hc' : 0 < cF * l₀ ^ 2 / 4 := by positivity
  refine ⟨l₀, cF * l₀ ^ 2 / 4, 2 * NF, hl₀pos, by linarith, hc', ?_⟩
  intro l p weight hl hp hw
  obtain ⟨Cse, hCse, hsmallQ⟩ := hsmall d hd D p hp
  have hh : 0 < 1 + (d : ℝ) / 2 := by positivity
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 * Cdet * 3 ^ NF * Real.exp Cdet := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max (max (2 * Cse) (4 * B)) 1 := ⟨_, rfl⟩
  have hKpos : 0 < K := by
    rw [hKdef]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hA : 2 * Cse ≤ K := by
    rw [hKdef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hB4 : 4 * B ≤ K := by
    rw [hKdef]; exact (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨Cs, C₂, hCs, hC₂, hsumb⟩ :=
    annuli_sum_bounds (cF * l₀ ^ 2 / 4) hc' (2 * NF) (1 + (d : ℝ) / 2) hh weight hw K hKpos
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max K Cs := ⟨_, rfl⟩
  have hKC : K ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCsC : Cs ≤ C := by rw [hCdef]; exact le_max_right _ _
  refine ⟨C, 1, C₂, lt_of_lt_of_le hKpos hKC, one_pos, hC₂, ?_⟩
  intro Q hQ β a μ hβ ha hμ lam hlam hlam1 P Pdag hP hPd
  haveI := reducedLaw_probability Q
  intro s T h F j velocity
  have hl0 : 0 < l := hl₀pos.trans_le hl
  have hs : 0 < s := hlam
  have hs1 : s ≤ Real.exp (-1) := hlam1
  have hs1' : s ≤ 1 := hs1.trans (Real.exp_le_one_iff.2 (by norm_num))
  have hTdef : ((T : ℝ≥0) : ℝ) = (s ^ 2) ⁻¹ := Real.coe_toNNReal _ (by positivity)
  have hnl : ‖(lam : ℂ)‖ = s := (Complex.norm_real lam).trans (Real.norm_eq_abs lam)
  have hT1 : 1 ≤ ((T : ℝ≥0) : ℝ) := by
    rw [hTdef]
    exact (one_le_inv₀ (by positivity)).2 (pow_le_one₀ hs.le hs1')
  -- locality of both the uncentered and centered endpoints, with the annulus error
  have hloc_for : ∀ (ν : EndpointIndex d) (n : ℕ), 1 ≤ n →
      ∃ Uloc : Lp ℂ 2 (reducedLaw Q),
        IsComplexLocalObservation Q ((n : ℝ) * l / (2 * s)) Uloc ∧
        (∀ᵐ ω ∂reducedLaw Q,
          ‖uncenteredEndpoint hd Q ν (lam : ℂ) P Pdag β a μ T ω - Uloc ω‖ ≤
            B * s ^ (-((2 * NF : ℕ) : ℝ)) * Real.exp (-(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2)) ∧
        (∀ᵐ ω ∂reducedLaw Q,
          ‖centeredComplexLp Q (uncenteredEndpoint hd Q ν (lam : ℂ) P Pdag β a μ T) ω -
              centeredComplexLp Q Uloc ω‖ ≤
            B * s ^ (-((2 * NF : ℕ) : ℝ)) * Real.exp (-(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2)) := by
    intro ν n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : Real.sqrt ((T : ℝ≥0) : ℝ) = s⁻¹ := by
      rw [hTdef, Real.sqrt_inv, Real.sqrt_sq hs.le]
    have hnl2 : 2 * Cdet ≤ (n : ℝ) * l :=
      calc 2 * Cdet ≤ l₀ := hl₀2
        _ ≤ l := hl
        _ ≤ (n : ℝ) * l := le_mul_of_one_le_left hl0.le hn1
    have hρ : Cdet * Real.sqrt ((T : ℝ≥0) : ℝ) ≤ (n : ℝ) * l / (2 * s) := by
      rw [hsq]
      calc Cdet * s⁻¹ = (2 * Cdet) / (2 * s) := by field_simp
        _ ≤ ((n : ℝ) * l) / (2 * s) := by gcongr
    obtain ⟨G', V', -, -, h3, -⟩ := hmain Q hQ β a μ hβ ha hμ (lam : ℂ) P Pdag hP hPd ν
    obtain ⟨Uloc, Gloc, hUl, -, hb1, hb2, -⟩ := h3 T hT1 ((n : ℝ) * l / (2 * s)) hρ
    have heps := eps_bound Cdet cF l l₀ s ((T : ℝ≥0) : ℝ) ‖(lam : ℂ)‖ NF n hCdet hcF hl₀pos hl hs
      hs1' hTdef hnl
    rw [← hBdef] at heps
    refine ⟨Uloc, hUl, ?_, ?_⟩
    · filter_upwards [hb1] with ω h
      have hb := (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans h
      have hE0 : 0 ≤ Cdet * (2 + ((T : ℝ≥0) : ℝ)) ^ NF * Real.exp (Cdet * ‖(lam : ℂ)‖ ^ 2 *
          ((T : ℝ≥0) : ℝ) - cF * ((n : ℝ) * l / (2 * s)) ^ 2 / ((T : ℝ≥0) : ℝ)) := by positivity
      refine hb.trans (le_trans ?_ heps)
      linarith
    · filter_upwards [hb2] with ω h
      exact h.trans heps
  -- realness
  have hβr : ∀ i, AeReal (β i) := fun i => AeReal.of_ae_eq_ofReal _ (hβ i)
  have har : ∀ i k, AeReal (a i k) :=
    fun i k => AeReal.of_ae_eq_ofReal (fun ω => ω.1 0 i k) (ha i k)
  have hμr : AeReal μ := AeReal.of_ae_eq_ofReal (fun ω => ω.2 0) hμ
  have hPreal : ∀ (t : ℝ≥0) (X : Lp ℂ 2 (reducedLaw Q)), AeReal X → AeReal (P t X) :=
    fun t X hX => aeReal_of_star_eq (hP.star_apply_of_real t (star_eq_of_aeReal hX))
  have hFreal : AeReal F := by
    show AeReal (Pdag T (β ⟨0, by omega⟩))
    refine aeReal_of_star_eq ?_
    rw [← IsComplexTransposeSemigroup.map_star hP hPd, star_eq_of_aeReal (hβr _)]
  have hF_app : ∀ n : ℕ, 1 ≤ n → ∃ V : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q ((n : ℝ) * l / (2 * s)) V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖F ω - V ω‖ ≤
        B * s ^ (-((2 * NF : ℕ) : ℝ)) * Real.exp (-(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2) := by
    intro n hn
    obtain ⟨Uloc, hUl, hb1, -⟩ := hloc_for (Sum.inr true) n hn
    exact exists_real_approx Q F Uloc hFreal hUl hb1
  obtain ⟨hFm, hGm, hF0, hG0, hFG, -⟩ :=
    hsmallQ Q hQ β a μ hβ ha hμ lam hlam hlam1 P Pdag hP hPd j velocity
  have hFn : 0 ≤ annNormp Q p F := ENNReal.toReal_nonneg
  cases velocity
  · -- clock endpoint
    intro G E Δ normp cutoff U hU
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
    have hGn : 0 ≤ annNormp Q p G := ENNReal.toReal_nonneg
    have hFG' : annNormp Q p F + annNormp Q p G ≤ Cse * s ^ h := hFG
    have hGreal : AeReal G :=
      AeReal.smul_real lam (aeReal_centered Q (hPreal T μ hμr))
    have hG_app : ∀ n : ℕ, 1 ≤ n → ∃ V : Lp ℂ 2 (reducedLaw Q),
        IsRealLocalObservation Q ((n : ℝ) * l / (2 * s)) V ∧
        ∀ᵐ ω ∂reducedLaw Q, ‖G ω - V ω‖ ≤
          B * s ^ (-((2 * NF : ℕ) : ℝ)) * Real.exp (-(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2) := by
      intro n hn
      obtain ⟨Uloc, hUl, -, hb2⟩ := hloc_for (Sum.inr false) n hn
      refine exists_real_approx Q G (centeredComplexLp Q Uloc) hGreal
        (isComplexLocal_centered Q hUl) ?_
      filter_upwards [hb2, smul_centered_ae_eq Q (lam : ℂ) (P T μ)] with ω h1 h2
      have e : G ω = centeredComplexLp Q ((lam : ℂ) • P T μ) ω := h2
      rw [e]
      exact h1
    rcases hU with rfl | rfl
    · exact annuli_core Q l p weight s _ (cF * l₀ ^ 2 / 4) K Cse B Cs C C₂ (2 * NF) hl0 hp hs hs1
        hh hc' hKpos hB0 hA hB4 hKC hCsC hsumb _ hFreal hF0 hFm (by linarith) hF_app
    · exact annuli_core Q l p weight s _ (cF * l₀ ^ 2 / 4) K Cse B Cs C C₂ (2 * NF) hl0 hp hs hs1
        hh hc' hKpos hB0 hA hB4 hKC hCsC hsumb _ hGreal hG0 hGm (by linarith) hG_app
  · -- velocity endpoint
    intro G E Δ normp cutoff U hU
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
    have hGn : 0 ≤ annNormp Q p G := ENNReal.toReal_nonneg
    have hFG' : annNormp Q p F + annNormp Q p G ≤ Cse * s ^ h := hFG
    have hGreal : AeReal G :=
      aeReal_centered Q (hPreal T _ ((hβr j).add ((har ⟨0, by omega⟩ j).smul_real lam)))
    have hG_app : ∀ n : ℕ, 1 ≤ n → ∃ V : Lp ℂ 2 (reducedLaw Q),
        IsRealLocalObservation Q ((n : ℝ) * l / (2 * s)) V ∧
        ∀ᵐ ω ∂reducedLaw Q, ‖G ω - V ω‖ ≤
          B * s ^ (-((2 * NF : ℕ) : ℝ)) * Real.exp (-(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2) := by
      intro n hn
      obtain ⟨Uloc, hUl, -, hb2⟩ := hloc_for (Sum.inl j) n hn
      exact exists_real_approx Q G (centeredComplexLp Q Uloc) hGreal
        (isComplexLocal_centered Q hUl) hb2
    rcases hU with rfl | rfl
    · exact annuli_core Q l p weight s _ (cF * l₀ ^ 2 / 4) K Cse B Cs C C₂ (2 * NF) hl0 hp hs hs1
        hh hc' hKpos hB0 hA hB4 hKC hCsC hsumb _ hFreal hF0 hFm (by linarith) hF_app
    · exact annuli_core Q l p weight s _ (cF * l₀ ^ 2 / 4) K Cse B Cs C C₂ (2 * NF) hl0 hp hs hs1
        hh hc' hKpos hB0 hA hB4 hKC hCsC hsumb _ hGreal hG0 hGm (by linarith) hG_app

end EinsteinFull.Blueprint
