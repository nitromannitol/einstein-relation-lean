import EinsteinRelation.External.GilbargTrudinger

open Real

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Subtracting a constant preserves a Hölder bound. -/
private lemma holderBound_sub_const {d : ℕ} {U : Set (Vec d)} {α : ℝ} {f : Vec d → ℝ} {K : ℝ}
    (hf : HolderBound U α f K) (c : ℝ) :
    HolderBound U α (fun x => f x - c) (K + |c|) := by
  obtain ⟨S, H, hS, hH, hK, hsup, hhold⟩ := hf
  refine ⟨S + |c|, H, add_nonneg hS (abs_nonneg _), hH, ?_, ?_, ?_⟩
  · -- S + |c| + H ≤ K + |c|
    nlinarith
  · -- sup bound: |f x - c| ≤ S + |c|
    intro x hx
    have hfx : |f x| ≤ S := hsup x hx
    calc
      |f x - c| = |f x + (-c)| := by rw [sub_eq_add_neg]
      _ ≤ |f x| + |-c| := abs_add_le _ _
      _ = |f x| + |c| := by simp
      _ ≤ S + |c| := by nlinarith
  · -- Hölder seminorm bound
    intro x hx y hy
    have hdiff : (f x - c) - (f y - c) = f x - f y := by ring
    rw [hdiff]
    exact hhold x hx y hy

/-- Centering a bounded Hölder vector field preserves a shared bound.
Source: `paper/main.tex:735-743`. -/
theorem exists_holderBound_sub_const {d : ℕ} (U : Set (Vec d))
    (F : Vec d → Vec d) (b : Vec d) (α K : ℝ)
    (hF : ∀ j, HolderBound U α (fun x => F x j) K) :
    ∃ C : ℝ, ∀ j, HolderBound U α (fun x => F x j - b j) C := by
  by_cases hd : Nonempty (Fin d)
  · -- Fin d is nonempty: take C = K + max_j |b j|
    have huniv : (Finset.univ : Finset (Fin d)).Nonempty := by
      obtain ⟨j⟩ := hd
      exact ⟨j, Finset.mem_univ j⟩
    let C := K + Finset.sup' (Finset.univ : Finset (Fin d)) huniv (fun j => |b j|)
    refine ⟨C, ?_⟩
    intro j
    have h_sub := holderBound_sub_const (hF j) (b j)
    -- h_sub : HolderBound U α (fun x => F x j - b j) (K + |b j|)
    have h_le : K + |b j| ≤ C := by
      dsimp [C]
      have h_mem : j ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ j
      have h_sup := Finset.le_sup' (fun i => |b i|) h_mem
      nlinarith
    -- Now use a monotonicity property: if HolderBound U α f C₁ and C₁ ≤ C₂, then HolderBound U α f C₂
    obtain ⟨S, H, hS, hH, hK, hsup, hhold⟩ := h_sub
    refine ⟨S, H, hS, hH, ?_, hsup, hhold⟩
    nlinarith
  · -- Fin d is empty (d = 0): take C = K
    have h_empty : IsEmpty (Fin d) := not_nonempty_iff.mp hd
    refine ⟨K, ?_⟩
    intro j
    exact (h_empty.false j).elim
end EinsteinRelation.Correctors
