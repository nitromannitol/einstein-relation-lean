import EinsteinFull.Calculus.C1DyadicActualMajorants
import EinsteinFull.Calculus.ScalarIterationSupport

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c10_dyadic_actual_majorant_iteration (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) (ν : EndpointIndex d) (b growth Ca E T ε : ℝ) (hCa : 0 ≤ Ca) (hE : 0 ≤ E) (hT : 0 < T) (hε : 0 < ε) (N : ℕ) (hinit : dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (T) ≤ 2*Ca*dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (T)) (havg : ∀ n : ℕ, n < N → dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (((2 : ℝ)^(n+1)*T)) ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (((2 : ℝ)^n*T)) + (E*((2 : ℝ)^n*T)^(-ε))*dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (((2 : ℝ)^n*T))) (hpoint : ∀ n : ℕ, n < N → dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (((2 : ℝ)^(n+1)*T)) ≤ max (dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (((2 : ℝ)^n*T))) (Ca*dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (((2 : ℝ)^(n+1)*T)) + dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (((2 : ℝ)^n*T))/2)) (n : ℕ) (hn : n ≤ N) : dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (((2 : ℝ)^n*T)) ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (T) * Real.exp (2*Ca*(E*T^(-ε))/(1-(2 : ℝ)^(-ε))) ∧ dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (((2 : ℝ)^n*T)) ≤ 2*Ca*(dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (T) * Real.exp (2*Ca*(E*T^(-ε))/(1-(2 : ℝ)^(-ε)))) := by
  let K : ℕ → ℝ := fun i => dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth ((2 : ℝ)^i*T)
  let R : ℕ → ℝ := fun i => dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth ((2 : ℝ)^i*T)
  let e : ℕ → ℝ := fun i => E * ((2 : ℝ)^i*T)^(-ε)
  let S : ℕ → ℝ × ℝ := fun i => Nat.rec (K 0, R 0) (fun j v => (v.1 + e j * v.2, max v.2 (Ca * (v.1 + e j * v.2) + v.2 / 2))) i
  have he (i : ℕ) : 0 ≤ e i := by
    dsimp [e]
    exact mul_nonneg hE (Real.rpow_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hT.le) _)
  have hR (i : ℕ) : 0 ≤ R i := by
    dsimp [R, dyadicPointMajorant]
    exact le_trans (by norm_num) (le_max_left _ _)
  have hK (i : ℕ) : 0 ≤ K i := by
    dsimp [K, dyadicAverageMajorant]
    exact le_trans (by norm_num) (le_max_left _ _)
  have hcomp (i : ℕ) (hi : i ≤ N) : K i ≤ (S i).1 ∧ R i ≤ (S i).2 := by
    induction i with
    | zero => exact ⟨le_rfl, le_rfl⟩
    | succ i ih =>
      have hiN : i < N := Nat.lt_of_succ_le hi
      obtain ⟨hk, hr⟩ := ih (Nat.le_of_lt hiN)
      have hs : K (i+1) ≤ (S (i+1)).1 := by
        calc
          K (i+1) ≤ K i + e i * R i := havg i hiN
          _ ≤ (S i).1 + e i * (S i).2 := add_le_add hk (mul_le_mul_of_nonneg_left hr (he i))
      refine ⟨hs, ?_⟩
      calc
        R (i+1) ≤ max (R i) (Ca * K (i+1) + R i / 2) := hpoint i hiN
        _ ≤ max (S i).2 (Ca * (S (i+1)).1 + (S i).2 / 2) :=
          max_le_max hr (add_le_add (mul_le_mul_of_nonneg_left hs hCa) (div_le_div_of_nonneg_right hr (by norm_num)))
  have hbound := coupled_iteration_le_dyadic_exp Ca E T ε hCa hE hT hε
    (fun i => (S i).1) (fun i => (S i).2) N (hK 0)
    (fun i hi => (hR i).trans (hcomp i hi.le).2)
    (by simpa [S, K, R] using hinit) (by intro i hi; rfl)
    (by intro i hi; exact le_rfl) n hn
  exact ⟨(hcomp n hn).1.trans (by simpa [S, K] using hbound.1),
    (hcomp n hn).2.trans (by simpa [S, K] using hbound.2)⟩

end EinsteinFull.Blueprint
