import EinsteinFull.Calculus.C2DyadicAverageMajorantRecurrence
import EinsteinFull.Calculus.C4DyadicPointMajorantRecurrence
import EinsteinFull.Calculus.C7DyadicInitialInvariant
import EinsteinFull.Calculus.C14DyadicTerminalScale
import EinsteinFull.Calculus.C10DyadicActualMajorantIteration
import EinsteinFull.Calculus.C15DyadicUniformAverageInitialization

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c19_dyadic_uniform_majorants (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) : ∃ b growth C : ℝ, 0 < b ∧ b ≤ 1/16 ∧ 0 < growth ∧ 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖*Real.sqrt (t : ℝ) ≤ 1 → dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (t : ℝ) ≤ C ∧ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (t : ℝ) ≤ C := by
  obtain ⟨b, Ca₀, hb, hbmax, hCa₀, hpoint⟩ :=
    c4_dyadic_point_majorant_recurrence hlocal d hd D 1 (by norm_num)
  obtain ⟨ε, growth, T₀, E, hε, hgrowth, hT₀, hE, havg⟩ :=
    c2_dyadic_average_majorant_recurrence hlocal d hd D b hb
  have hTmax : 1 ≤ 2*T₀ := by linarith
  obtain ⟨Ca, hCa, hCa₀Ca, hinit⟩ :=
    c7_dyadic_uniform_initial_invariant hlocal d hd D (2*T₀) Ca₀ hTmax
  obtain ⟨B, hB, hbase⟩ :=
    c15_dyadic_uniform_initial_average_majorant hlocal d hd D (2*T₀) b hTmax hb
  have hCa_nonneg : 0 ≤ Ca := by linarith
  have hden : 0 < 1 - (2 : ℝ)^(-ε) := by
    have h := Real.rpow_lt_one_of_one_lt_of_neg (show (1 : ℝ) < 2 by norm_num) (by linarith : -ε < 0)
    linarith
  let K : ℝ := 2*Ca*E/(1-(2 : ℝ)^(-ε))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hexp : 1 ≤ Real.exp K := by simpa using Real.add_one_le_exp K |>.trans' (by linarith : (1 : ℝ) ≤ K + 1)
  let C : ℝ := (2*Ca+1)*B*Real.exp K
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_nonneg (show 0 ≤ 2*Ca+1 by linarith) (show 0 ≤ B*Real.exp K by positivity), mul_nonneg (show 0 ≤ B-1 by linarith) (show 0 ≤ Real.exp K-1 by linarith)]
  refine ⟨b, growth, C, hb, (le_min_iff.mp hbmax).2, hgrowth, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hforce
  have hζ : ‖ζ‖ ≤ 2 := by
    have hs : 1 ≤ Real.sqrt (t : ℝ) := by simpa using Real.sqrt_le_sqrt ht
    have hn := norm_nonneg ζ
    nlinarith
  have hbase' := fun T => hbase Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth T (le_of_lt hgrowth)
  have hinit' := fun T => hinit Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ b growth T (le_of_lt hgrowth)
  have hsmall : ∀ T : ℝ, 1 ≤ T → T ≤ 2*T₀ →
      dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth T ≤ C ∧
      dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth T ≤ C := by
    intro T hT hTT
    have ha := hbase' T hT hTT
    have hp := hinit' T hT hTT
    have hm : 0 ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth T :=
      (le_max_left 1 _).trans' (by norm_num)
    constructor <;> dsimp [C] <;> nlinarith [mul_nonneg (show 0 ≤ 2*Ca by linarith) (show 0 ≤ B - dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth T by linarith), mul_nonneg (show 0 ≤ (2*Ca+1)*B by positivity) (show 0 ≤ Real.exp K-1 by linarith)]
  by_cases ht₀ : (t : ℝ) < T₀
  · exact hsmall t ht (by linarith)
  · obtain ⟨N, T, hT, hTT, ht_eq⟩ := c14_dyadic_exact_terminal_scale T₀ t (by linarith) (by linarith)
    have hT1 : 1 ≤ T := by linarith
    have hTpos : 0 < T := by linarith
    have hpow (n : ℕ) (hn : n ≤ N) : (2 : ℝ)^n*T ≤ (t : ℝ) := by
      rw [ht_eq]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) (le_of_lt hTpos)
    have hw (n : ℕ) (hn : n < N) : ‖ζ‖ * Real.sqrt (2*((2 : ℝ)^n*T)) ≤ 1 := by
      have hle : 2*((2 : ℝ)^n*T) ≤ (t : ℝ) := by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hpow (n+1) (by omega)
      exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (norm_nonneg ζ)).trans hforce
    have hrecavg : ∀ n : ℕ, n < N → dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth ((2 : ℝ)^(n+1)*T) ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth ((2 : ℝ)^n*T) + (E*((2 : ℝ)^n*T)^(-ε))*dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth ((2 : ℝ)^n*T) := by
      intro n hn
      have hnT : T₀ ≤ (2 : ℝ)^n*T := by
        have : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
        nlinarith
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using havg Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν growth ((2 : ℝ)^n*T) le_rfl hnT (hw n hn)
    have hrecpoint : ∀ n : ℕ, n < N → dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth ((2 : ℝ)^(n+1)*T) ≤ max (dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth ((2 : ℝ)^n*T)) (Ca*dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth ((2 : ℝ)^(n+1)*T) + dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth ((2 : ℝ)^n*T)/2) := by
      intro n hn
      have hnT : 8 ≤ (2 : ℝ)^n*T := by
        have : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
        nlinarith
      have ha_nonneg : 0 ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (2*((2 : ℝ)^n*T)) := (le_max_left 1 _).trans' (by norm_num)
      have hp := hpoint Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν growth ((2 : ℝ)^n*T) (le_of_lt hgrowth) hnT (hw n hn)
      have hh : Ca₀*dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (2*((2 : ℝ)^n*T)) ≤ Ca*dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (2*((2 : ℝ)^n*T)) := mul_le_mul_of_nonneg_right hCa₀Ca ha_nonneg
      have := hp.trans (max_le_max le_rfl (add_le_add hh le_rfl))
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using this
    have hi := hinit' T hT1 (le_of_lt hTT)
    obtain ⟨ha, hp⟩ := c10_dyadic_actual_majorant_iteration d hd D Q β a μ ζ P Pdag ν b growth Ca E T ε hCa_nonneg hE hTpos hε N hi hrecavg hrecpoint N le_rfl
    have hBbase := hbase' T hT1 (le_of_lt hTT)
    have hrpow : T^(-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 (by linarith)
    have hKbound : 2*Ca*(E*T^(-ε))/(1-(2 : ℝ)^(-ε)) ≤ K := by
      dsimp [K]
      apply div_le_div_of_nonneg_right _ (le_of_lt hden)
      nlinarith [mul_nonneg hE (show 0 ≤ 1 - T^(-ε) by linarith)]
    have he := Real.exp_le_exp.mpr hKbound
    have hbase_nonneg : 0 ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth T := (le_max_left 1 _).trans' (by norm_num)
    have hproduct : dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth T * Real.exp (2*Ca*(E*T^(-ε))/(1-(2 : ℝ)^(-ε))) ≤ B*Real.exp K := mul_le_mul hBbase he (Real.exp_pos _).le (by linarith)
    rw [ht_eq]
    constructor
    · exact hp.trans ((mul_le_mul_of_nonneg_left hproduct (by linarith)).trans (by dsimp [C]; nlinarith [show 0 ≤ B*Real.exp K by positivity]))
    · exact ha.trans (hproduct.trans (by dsimp [C]; nlinarith [show 0 ≤ B*Real.exp K by positivity]))

end EinsteinFull.Blueprint
