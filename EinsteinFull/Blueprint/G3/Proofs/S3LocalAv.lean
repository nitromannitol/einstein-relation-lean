import EinsteinFull.Blueprint.G3.Proofs.S3LocalAvCov
import EinsteinFull.Blueprint.G3.node_e_u3A_local_u2D_av
import EinsteinFull.Blueprint.G3.node_e_u3A_time_u2D_flux
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport

/-!
# `e:local-av`: the local Gaussian averaging estimate

Clause 1 is the Schur-test bound of `S3LocalAvCov` for a centered field local at radius `r ≥ 1`.
Clause 2 decomposes `Y` into the telescoping blocks `P_{n+1} - P_n` of centered local
approximants (`P_n` is `0` when the supplied error exceeds `m`, and the centered `Yloc_n`
otherwise), applies clause 1 to every block, and sums the annuli. The remaining sum estimate is the
pure real-analysis lemma `S3LocalAv.annulus_tail`. The time-flux dependency is not used.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinFull.S3LocalAv

variable {d : ℕ} {Λ r₀ : ℝ}

section Local

variable (Q : EnvironmentLaw d Λ r₀)

theorem IsLocalRep.mono {R R' : ℝ} (h : R ≤ R') {f : Lp ℂ 2 (reducedLaw Q)}
    (hf : IsLocalRep Q R f) : IsLocalRep Q R' f := by
  obtain ⟨g, hg, hgf⟩ := hf
  refine ⟨g, hg.mono (Probability.localSigma_mono ?_) le_rfl, hgf⟩
  intro x hx
  exact lt_of_lt_of_le hx h

theorem IsLocalRep.zero (R : ℝ) : IsLocalRep Q R (0 : Lp ℂ 2 (reducedLaw Q)) :=
  ⟨fun _ => 0, measurable_const, (Lp.coeFn_zero ℂ 2 (reducedLaw Q)).symm⟩

theorem IsLocalRep.sub {R : ℝ} {f g : Lp ℂ 2 (reducedLaw Q)} (hf : IsLocalRep Q R f)
    (hg : IsLocalRep Q R g) : IsLocalRep Q R (f - g) := by
  obtain ⟨g1, hg1, hgf1⟩ := hf
  obtain ⟨g2, hg2, hgf2⟩ := hg
  exact ⟨fun ω => g1 ω - g2 ω, hg1.sub hg2,
    (hgf1.sub hgf2).trans (Lp.coeFn_sub f g).symm⟩

theorem IsLocalRep.centered {R : ℝ} {f : Lp ℂ 2 (reducedLaw Q)} (hf : IsLocalRep Q R f) :
    IsLocalRep Q R (centeredComplexLp Q f) := by
  obtain ⟨g, hg, hgf⟩ := hf
  refine ⟨fun ω => g ω - ∫ ω', (f : FieldPair d → ℂ) ω' ∂reducedLaw Q, hg.sub measurable_const, ?_⟩
  filter_upwards [hgf, coeFn_centeredComplexLp Q f] with ω h1 h2
  rw [h2, h1]

theorem integral_lp_sub (f g : Lp ℂ 2 (reducedLaw Q)) :
    ∫ ω, (f - g) ω ∂reducedLaw Q =
      ∫ ω, f ω ∂reducedLaw Q - ∫ ω, g ω ∂reducedLaw Q := by
  rw [integral_congr_ae (Lp.coeFn_sub f g)]
  exact integral_sub (integrable_complexLp Q f) (integrable_complexLp Q g)

theorem integral_lp_zero : ∫ ω, (0 : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q = 0 := by
  rw [integral_congr_ae (Lp.coeFn_zero ℂ 2 (reducedLaw Q))]
  simp

theorem centeredComplexLp_sub (a b : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q (a - b) = centeredComplexLp Q a - centeredComplexLp Q b := by
  simp only [← centeredComplexLpCLM_apply, map_sub]

theorem centeredComplexLp_of_integral_eq_zero {f : Lp ℂ 2 (reducedLaw Q)}
    (hf : ∫ ω, f ω ∂reducedLaw Q = 0) : centeredComplexLp Q f = f := by
  apply Lp.ext
  filter_upwards [coeFn_centeredComplexLp Q f] with ω hω
  rw [hω, hf, sub_zero]

end Local

theorem vnorm_neg' {E : Type*} [NormedAddCommGroup E] (F : Fin d → E) : vnorm (-F) = vnorm F := by
  simp [vnorm]

theorem vnorm_sub_comm {E : Type*} [NormedAddCommGroup E] (F G : Fin d → E) :
    vnorm (F - G) = vnorm (G - F) := by
  rw [← neg_sub G F, vnorm_neg']

theorem vnorm_sum_le {E : Type*} [NormedAddCommGroup E] (G : ℕ → Fin d → E) (N : ℕ) :
    vnorm (∑ n ∈ Finset.range N, G n) ≤ ∑ n ∈ Finset.range N, vnorm (G n) := by
  induction N with
  | zero => simp [vnorm_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (vnorm_add_le _ _).trans (add_le_add ih le_rfl)

theorem sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = x ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- The constant of clause 1. -/
def avConst (d : ℕ) (r₀ : ℝ) : ℝ := Real.sqrt ((2 * (3 + |r₀|)) ^ d)

theorem avConst_pos (d : ℕ) (r₀ : ℝ) : 0 < avConst d r₀ :=
  Real.sqrt_pos.mpr (by positivity)

theorem sqrt_two_Rc_pow (d : ℕ) (r₀ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    Real.sqrt ((2 * ((3 + |r₀|) * R)) ^ d) = avConst d r₀ * R ^ ((d : ℝ) / 2) := by
  rw [avConst, ← sqrt_pow_eq_rpow hR, ← Real.sqrt_mul (by positivity), ← mul_pow]
  congr 2
  ring

theorem gaussianAveragingSeminorm_le_iff' {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (F : Fin d → Lp ℂ 2 (reducedLaw Q))
    (C : ℝ) (hC : 0 ≤ C) :
    gaussianAveragingSeminorm hd Q F ≤ ENNReal.ofReal C ↔
      ∀ ρ : ℝ, 1 ≤ ρ →
        ρ ^ ((d : ℝ) / 2) * Real.sqrt (∑ j : Fin d,
          ‖∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (F j)‖ ^ 2) ≤ C := by
  simp only [gaussianAveragingSeminorm, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hC]

section Avg

variable (Q : EnvironmentLaw d Λ r₀)

theorem avgV_sub {s : ℝ} (hs : 0 < s) (F G : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    avgV Q s hs (F - G) = avgV Q s hs F - avgV Q s hs G := by
  funext j
  simp [avgV]

theorem avgV_zero {s : ℝ} (hs : 0 < s) : avgV Q s hs 0 = 0 := by
  funext j
  simp [avgV]

theorem vnorm_avgV_le {s : ℝ} (hs : 0 < s) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    vnorm (avgV Q s hs F) ≤ vnorm F := by
  have h := vnorm_le_mul (F := avgV Q s hs F) (G := F) zero_le_one
    (fun j => by
      rw [one_mul]
      exact norm_fluxGaussianAverage_le s hs (F j))
  simpa only [one_mul] using h

/-- One block of the decomposition. -/
theorem exists_block_approx {R m e : ℝ} (Y Yloc : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hY0 : ∀ j, ∫ ω, Y j ω ∂reducedLaw Q = 0) (hYm : vnorm Y ≤ m)
    (hloc : ∀ j, IsLocalRep Q R (Yloc j)) (hdist : vnorm (Y - Yloc) ≤ e) :
    ∃ P : Fin d → Lp ℂ 2 (reducedLaw Q), (∀ j, ∫ ω, P j ω ∂reducedLaw Q = 0) ∧
      (∀ j, IsLocalRep Q R (P j)) ∧ vnorm P ≤ 2 * m ∧ vnorm (Y - P) ≤ min m e := by
  have hm : 0 ≤ m := (vnorm_nonneg Y).trans hYm
  by_cases h : m ≤ e
  · refine ⟨0, fun j => integral_lp_zero Q, fun j => IsLocalRep.zero Q R, ?_, ?_⟩
    · rw [vnorm_zero]
      linarith
    · rw [sub_zero, min_eq_left h]
      exact hYm
  · push_neg at h
    refine ⟨fun j => centeredComplexLp Q (Yloc j), fun j => integral_centeredComplexLp Q _,
      fun j => (hloc j).centered Q, ?_⟩
    have hP : vnorm (Y - fun j => centeredComplexLp Q (Yloc j)) ≤ e := by
      have h1 := vnorm_le_mul (F := Y - fun j => centeredComplexLp Q (Yloc j))
        (G := Y - Yloc) zero_le_one (fun j => by
          have h2 : (Y - fun j => centeredComplexLp Q (Yloc j)) j =
              centeredComplexLp Q (Y j - Yloc j) := by
            rw [centeredComplexLp_sub, centeredComplexLp_of_integral_eq_zero Q (hY0 j)]
            rfl
          rw [h2, one_mul]
          exact norm_fluxCentered_le (Y j - Yloc j))
      rw [one_mul] at h1
      exact h1.trans hdist
    refine ⟨?_, ?_⟩
    · have h3 : (fun j => centeredComplexLp Q (Yloc j)) =
          Y - (Y - fun j => centeredComplexLp Q (Yloc j)) := (sub_sub_cancel _ _).symm
      rw [h3]
      refine (vnorm_sub_le _ _).trans ?_
      linarith
    · rw [min_eq_right h.le]
      exact hP

end Avg

/-- Clause 2 at a fixed averaging scale. -/
theorem local_av_bound (Q : EnvironmentLaw d Λ r₀) {c s m A : ℝ} (hc : 0 < c) (hs : 1 ≤ s)
    (hm : 0 ≤ m) (hA : 0 ≤ A)
    (Y : Fin d → Lp ℂ 2 (reducedLaw Q)) (hY0 : ∀ j, ∫ ω, Y j ω ∂reducedLaw Q = 0)
    (hYm : vnorm Y ≤ m)
    (happrox : ∀ n : ℕ, 1 ≤ n → ∃ Yloc : Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ j, IsLocalRep Q ((n : ℝ) * Real.sqrt s) (Yloc j)) ∧
        vnorm (Y - Yloc) ≤ A * Real.exp (-c * (n : ℝ) ^ 2))
    (hsum : Summable (annulus d c m A s)) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) (by positivity) Y) ≤
      2 * avConst d r₀ * ∑' n, annulus d c m A s n := by
  have hs0 : 0 < s := by linarith
  have hsq : 1 ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hs
  have hρs : 0 < ρ ^ 2 := by positivity
  have hρd : 0 ≤ Real.sqrt (ρ ^ d) := Real.sqrt_nonneg _
  -- the sequence of approximants
  have hex : ∀ n : ℕ, ∃ P : Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ j, ∫ ω, P j ω ∂reducedLaw Q = 0) ∧
      (∀ j, IsLocalRep Q ((n : ℝ) * Real.sqrt s) (P j)) ∧ vnorm P ≤ 2 * m ∧
      (n = 0 → P = 0) ∧
      (1 ≤ n → vnorm (Y - P) ≤ min m (A * Real.exp (-c * (n : ℝ) ^ 2))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨0, fun j => integral_lp_zero Q, fun j => IsLocalRep.zero Q _, ?_, fun _ => rfl,
        fun h => absurd h (by norm_num)⟩
      rw [vnorm_zero]
      linarith
    · obtain ⟨Yloc, hloc, hdist⟩ := happrox n hn
      obtain ⟨P, hP0, hPl, hPn, hPe⟩ := exists_block_approx Q Y Yloc hY0 hYm hloc hdist
      exact ⟨P, hP0, hPl, hPn, fun h => absurd h (by omega), fun _ => hPe⟩
  choose P hP0 hPl hPn hPz hPe using hex
  have hP00 : P 0 = 0 := hPz 0 rfl
  -- the blocks
  have hRn : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) * Real.sqrt s := fun n => by positivity
  have hRn1 : ∀ n : ℕ, 1 ≤ ((n : ℝ) + 1) * Real.sqrt s := fun n => by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  have hb0 : ∀ n : ℕ, ∀ j, ∫ ω, (P (n + 1) - P n) j ω ∂reducedLaw Q = 0 := by
    intro n j
    rw [Pi.sub_apply, integral_lp_sub, hP0, hP0, sub_zero]
  have hbl : ∀ n : ℕ, ∀ j, IsLocalRep Q (((n : ℝ) + 1) * Real.sqrt s) ((P (n + 1) - P n) j) := by
    intro n j
    rw [Pi.sub_apply]
    have e1 : ((n + 1 : ℕ) : ℝ) * Real.sqrt s = ((n : ℝ) + 1) * Real.sqrt s := by push_cast; ring
    have h1 := hPl (n + 1) j
    rw [e1] at h1
    have h2 := (hPl n j).mono Q (show (n : ℝ) * Real.sqrt s ≤ ((n : ℝ) + 1) * Real.sqrt s by
      nlinarith [Real.sqrt_nonneg s])
    exact h1.sub Q h2
  have hbn : ∀ n : ℕ, vnorm (P (n + 1) - P n) ≤
      2 * min m (max m A * Real.exp (-c * (n : ℝ) ^ 2)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hP00, sub_zero]
      have e0 : Real.exp (-c * ((0 : ℕ) : ℝ) ^ 2) = 1 := by simp
      have : min m (max m A * Real.exp (-c * ((0 : ℕ) : ℝ) ^ 2)) = m := by
        rw [e0, mul_one]
        exact min_eq_left (le_max_left _ _)
      rw [this]
      exact hPn 1
    · have h1 := hPe n hn
      have h2 := hPe (n + 1) (by omega)
      have hmono : A * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) ≤ A * Real.exp (-c * (n : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply Real.exp_le_exp.2
        push_cast
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h3 : P (n + 1) - P n = (P (n + 1) - Y) + (Y - P n) := by abel
      rw [h3]
      refine (vnorm_add_le _ _).trans ?_
      rw [vnorm_sub_comm (P (n + 1)) Y]
      have h4 : min m (A * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)) ≤
          min m (max m A * Real.exp (-c * (n : ℝ) ^ 2)) :=
        min_le_min le_rfl (hmono.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.exp_pos _).le))
      have h5 : min m (A * Real.exp (-c * (n : ℝ) ^ 2)) ≤
          min m (max m A * Real.exp (-c * (n : ℝ) ^ 2)) :=
        min_le_min le_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
      linarith [h2.trans h4, h1.trans h5]
  -- every block against the Schur bound
  have hblock : ∀ n : ℕ, Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) hρs (P (n + 1) - P n)) ≤
      2 * avConst d r₀ * annulus d c m A s n := by
    intro n
    have h1 := avgV_vnorm_le Q (hRn n) (Rc := (3 + |r₀|) * (((n : ℝ) + 1) * Real.sqrt s))
      (by nlinarith [hRn1 n, abs_nonneg r₀]) (P (n + 1) - P n)
      (hb0 n) (hbl n) hρ
    rw [sqrt_two_Rc_pow d r₀ (hRn n)] at h1
    have h2 := mul_le_mul_of_nonneg_left (hbn n)
      (mul_nonneg (avConst_pos d r₀).le (Real.rpow_nonneg (hRn n) ((d : ℝ) / 2)))
    unfold annulus
    calc Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) hρs (P (n + 1) - P n))
        ≤ avConst d r₀ * (((n : ℝ) + 1) * Real.sqrt s) ^ ((d : ℝ) / 2) *
            vnorm (P (n + 1) - P n) := h1
      _ ≤ avConst d r₀ * (((n : ℝ) + 1) * Real.sqrt s) ^ ((d : ℝ) / 2) *
            (2 * min m (max m A * Real.exp (-c * (n : ℝ) ^ 2))) := h2
      _ = 2 * avConst d r₀ * ((((n : ℝ) + 1) * Real.sqrt s) ^ ((d : ℝ) / 2) *
            min m (max m A * Real.exp (-c * (n : ℝ) ^ 2))) := by ring
  -- partial sums
  have htel : ∀ N : ℕ, avgV Q (ρ ^ 2) hρs (P N) =
      ∑ n ∈ Finset.range N, avgV Q (ρ ^ 2) hρs (P (n + 1) - P n) := by
    intro N
    induction N with
    | zero => rw [hP00, avgV_zero]; simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ← ih, avgV_sub]
      abel
  have hpartial : ∀ N : ℕ, Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) hρs (P N)) ≤
      2 * avConst d r₀ * ∑' n, annulus d c m A s n := by
    intro N
    rw [htel N]
    calc Real.sqrt (ρ ^ d) * vnorm (∑ n ∈ Finset.range N, avgV Q (ρ ^ 2) hρs (P (n + 1) - P n))
        ≤ Real.sqrt (ρ ^ d) *
            ∑ n ∈ Finset.range N, vnorm (avgV Q (ρ ^ 2) hρs (P (n + 1) - P n)) :=
          mul_le_mul_of_nonneg_left (vnorm_sum_le _ N) hρd
      _ = ∑ n ∈ Finset.range N, Real.sqrt (ρ ^ d) *
            vnorm (avgV Q (ρ ^ 2) hρs (P (n + 1) - P n)) := by rw [Finset.mul_sum]
      _ ≤ ∑ n ∈ Finset.range N, 2 * avConst d r₀ * annulus d c m A s n :=
          Finset.sum_le_sum fun n _ => hblock n
      _ = 2 * avConst d r₀ * ∑ n ∈ Finset.range N, annulus d c m A s n := by
          rw [Finset.mul_sum]
      _ ≤ 2 * avConst d r₀ * ∑' n, annulus d c m A s n :=
          mul_le_mul_of_nonneg_left
            (hsum.sum_le_tsum _ fun n _ => annulus_nonneg d hm n)
            (by have := avConst_pos d r₀; positivity)
  -- the tail error tends to zero
  have hlim : Tendsto (fun N : ℕ => c * (N : ℝ) ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hexp : Tendsto (fun N : ℕ => Real.exp (-(c * (N : ℝ) ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlim
  have hexp' : Tendsto (fun N : ℕ => Real.sqrt (ρ ^ d) * A * Real.exp (-(c * (N : ℝ) ^ 2)))
      atTop (𝓝 0) := by
    have h := hexp.const_mul (Real.sqrt (ρ ^ d) * A)
    rwa [mul_zero] at h
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN1, hN2⟩ := ((eventually_ge_atTop 1).and
    (hexp'.eventually (gt_mem_nhds hε))).exists
  have hsplit : avgV Q (ρ ^ 2) hρs Y =
      avgV Q (ρ ^ 2) hρs (P N) + avgV Q (ρ ^ 2) hρs (Y - P N) := by
    rw [avgV_sub]
    abel
  have hlast : Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) hρs (Y - P N)) ≤ ε := by
    have h1 := vnorm_avgV_le Q hρs (Y - P N)
    have h2 := hPe N hN1
    have h3 : vnorm (Y - P N) ≤ A * Real.exp (-c * (N : ℝ) ^ 2) := h2.trans (min_le_right _ _)
    calc Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) hρs (Y - P N))
        ≤ Real.sqrt (ρ ^ d) * (A * Real.exp (-c * (N : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) hρd
      _ = Real.sqrt (ρ ^ d) * A * Real.exp (-(c * (N : ℝ) ^ 2)) := by
          rw [neg_mul]; ring
      _ ≤ ε := hN2.le
  calc Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) (by positivity) Y)
      ≤ Real.sqrt (ρ ^ d) * (vnorm (avgV Q (ρ ^ 2) hρs (P N)) +
          vnorm (avgV Q (ρ ^ 2) hρs (Y - P N))) := by
        apply mul_le_mul_of_nonneg_left _ hρd
        rw [hsplit]
        exact vnorm_add_le _ _
    _ = Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) hρs (P N)) +
          Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) hρs (Y - P N)) := by ring
    _ ≤ 2 * avConst d r₀ * ∑' n, annulus d c m A s n + ε := add_le_add (hpartial N) hlast

/-- `e:local-av`, proved outright; the time-flux dependency is not used. -/
theorem node_e_u3A_local_u2D_av_proved : node_e_u3A_local_u2D_avStmt := by
  intro d hd D
  refine ⟨⟨avConst d D.dependenceRange, avConst_pos _ _, ?_⟩, ?_⟩
  · intro Q r hr F hF0 hFloc
    have hr0 : 0 ≤ r := by linarith
    rw [gaussianAveragingSeminorm_le_iff' hd Q F _ (by
      have := avConst_pos d D.dependenceRange
      positivity)]
    intro ρ hρ
    have hρ0 : 0 < ρ := by linarith
    have h := avgV_vnorm_le Q hr0 (Rc := (3 + |D.dependenceRange|) * r)
      (by nlinarith [abs_nonneg D.dependenceRange]) F hF0 hFloc hρ0
    rw [sqrt_two_Rc_pow d D.dependenceRange hr0] at h
    rw [← sqrt_pow_eq_rpow hρ0.le d]
    exact h
  · intro c A₀ a hc hA₀ ha
    obtain ⟨Ct, hCt, htail⟩ := annulus_tail d hc hA₀ ha
    have hC1 := avConst_pos d D.dependenceRange
    refine ⟨max (2 * avConst d D.dependenceRange) Ct, d + 1, lt_max_of_lt_right hCt, ?_⟩
    intro Q s m A hs1 hm hA hms hAs Y hY0 hYm happrox
    obtain ⟨hsumm, htsum⟩ := htail s m A hs1 hm hA hms hAs
    have hs0 : 0 < s := by linarith
    have hL : 0 ≤ Real.log (2 + s) ^ (d + 1) :=
      pow_nonneg (Real.log_nonneg (by linarith)) _
    have hT0 : 0 ≤ ∑' n, annulus d c m A s n := tsum_nonneg fun n => annulus_nonneg d hm n
    have hCmax : 0 ≤ max (2 * avConst d D.dependenceRange) Ct :=
      le_max_of_le_left (by linarith)
    have h2 : gaussianAveragingSeminorm hd Q Y ≤
        ENNReal.ofReal (max (2 * avConst d D.dependenceRange) Ct *
          ∑' n, annulus d c m A s n) := by
      rw [gaussianAveragingSeminorm_le_iff' hd Q Y _ (mul_nonneg hCmax hT0)]
      intro ρ hρ
      have hρ0 : 0 < ρ := by linarith
      have h := local_av_bound Q hc hs1 hm hA Y hY0 hYm happrox hsumm hρ0
      rw [← sqrt_pow_eq_rpow hρ0.le d]
      calc Real.sqrt (ρ ^ d) * Real.sqrt (∑ j : Fin d,
            ‖∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (Y j)‖ ^ 2)
          = Real.sqrt (ρ ^ d) * vnorm (avgV Q (ρ ^ 2) (by positivity) Y) := rfl
        _ ≤ 2 * avConst d D.dependenceRange * ∑' n, annulus d c m A s n := h
        _ ≤ max (2 * avConst d D.dependenceRange) Ct * ∑' n, annulus d c m A s n :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hT0
    have h3 : ∑' n, annulus d c m A s n ≤
        max (2 * avConst d D.dependenceRange) Ct * Real.log (2 + s) ^ (d + 1) :=
      htsum.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hL)
    dsimp only
    refine ⟨hsumm, h2, h3, ?_⟩
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    calc max (2 * avConst d D.dependenceRange) Ct * ∑' n, annulus d c m A s n
        ≤ max (2 * avConst d D.dependenceRange) Ct *
            (max (2 * avConst d D.dependenceRange) Ct * Real.log (2 + s) ^ (d + 1)) :=
          mul_le_mul_of_nonneg_left h3 hCmax
      _ = max (2 * avConst d D.dependenceRange) Ct ^ 2 * Real.log (2 + s) ^ (d + 1) := by ring

/-- `e:local-av` with its graph dependency binder. -/
theorem node_e_u3A_local_u2D_av_of_deps (_hdeps : node_e_u3A_time_u2D_fluxStmt) :
    node_e_u3A_local_u2D_avStmt :=
  node_e_u3A_local_u2D_av_proved

end EinsteinFull.Blueprint
