import EinsteinRelation.External.GilbargTrudinger

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Negation preserves the Hölder bound with the same constant. -/
private lemma holderBound_neg {d : ℕ} {U : Set (Vec d)} {α : ℝ} {f : Vec d → ℝ} {K : ℝ}
    (hf : HolderBound U α f K) : HolderBound U α (-f) K := by
  obtain ⟨S, H, hS, hH, hK, hsup, hhold⟩ := hf
  refine ⟨S, H, hS, hH, hK, ?_, ?_⟩
  · intro x hx; simpa using hsup x hx
  · intro x hx y hy
    have h : (-f) x - (-f) y = -(f x - f y) := by
      simp [sub_eq_add_neg, add_comm]
    rw [h, abs_neg]
    exact hhold x hx y hy

/-- If `HolderBound U α f C` and `C ≤ C'`, then `HolderBound U α f C'`. -/
private lemma holderBound_mono_const {d : ℕ} {U : Set (Vec d)} {α : ℝ} {f : Vec d → ℝ} {C C' : ℝ}
    (hf : HolderBound U α f C) (hCC' : C ≤ C') :
    HolderBound U α f C' := by
  obtain ⟨S, H, hS, hH, hK, hsup, hhold⟩ := hf
  refine ⟨S, H, hS, hH, ?_, hsup, hhold⟩
  nlinarith

/-- A constant function has a Hölder bound with constant `|c|`. -/
private lemma holderBound_const {d : ℕ} {U : Set (Vec d)} {α : ℝ} (c : ℝ) :
    HolderBound U α (fun _ : Vec d => c) (|c|) := by
  refine ⟨|c|, 0, abs_nonneg _, by norm_num, by simp, ?_, ?_⟩
  · intro x _; rfl
  · intro x _ y _; simp

/-- The curl divergence source inherits a common component Hölder bound.
Source: `paper/main.tex:741-743`. -/
theorem exists_holderBound_curlSource {d : ℕ} (U : Set (Vec d))
    (F : Vec d → Vec d) (α K : ℝ)
    (hF : ∀ j, HolderBound U α (fun x => F x j) K) :
    ∃ C : ℝ, ∀ j k l : Fin d,
      HolderBound U α
        (fun x => (F x j • unitVector k - F x k • unitVector j) l) C := by
  by_cases hd : Nonempty (Fin d)
  · obtain ⟨j₀⟩ := hd
    have hK_nonneg : 0 ≤ K := by
      obtain ⟨S, H, hS, hH, hK, _, _⟩ := hF j₀
      nlinarith
    refine ⟨K, fun j k l => ?_⟩
    by_cases hjk : j = k
    · rw [hjk]
      have hzero : (fun x : Vec d => (F x k • unitVector k - F x k • unitVector k) l) = fun _ => (0 : ℝ) := by
        ext x; simp
      rw [hzero]
      have h0 : HolderBound U α (fun _ : Vec d => (0 : ℝ)) (|(0 : ℝ)|) := holderBound_const 0
      have h0K : |(0 : ℝ)| ≤ K := by simpa [abs_zero] using hK_nonneg
      exact holderBound_mono_const h0 h0K
    · by_cases hlj : l = j
      · rw [hlj]
        have hneg : (fun x : Vec d => (F x j • unitVector k - F x k • unitVector j) j) =
            (-fun x => F x k) := by
          ext x
          dsimp [unitVector]
          simp [hjk]
        rw [hneg]
        exact holderBound_neg (hF k)
      · by_cases hlk : l = k
        · rw [hlk]
          have hpos : (fun x : Vec d => (F x j • unitVector k - F x k • unitVector j) k) =
              (fun x => F x j) := by
            ext x
            dsimp [unitVector]
            simp [hjk]
          rw [hpos]
          exact hF j
        · have hzero : (fun x : Vec d => (F x j • unitVector k - F x k • unitVector j) l) = fun _ => (0 : ℝ) := by
            ext x
            dsimp [unitVector]
            simp [hlj, hlk]
          rw [hzero]
          have h0 : HolderBound U α (fun _ : Vec d => (0 : ℝ)) (|(0 : ℝ)|) := holderBound_const 0
          have h0K : |(0 : ℝ)| ≤ K := by simpa [abs_zero] using hK_nonneg
          exact holderBound_mono_const h0 h0K
  · refine ⟨0, fun j => ?_⟩
    exact (hd ⟨j⟩).elim
end EinsteinRelation.Correctors
