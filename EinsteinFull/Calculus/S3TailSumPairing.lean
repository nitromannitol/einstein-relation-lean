import EinsteinFull.Calculus.S3AnnuliDelta
import EinsteinFull.Calculus.S3LevyL2
import EinsteinFull.Blueprint.G1.Proofs.S3RealSemigroup

/-!
# The bilinear `L²` pairing of annulus increments

Generic support for `p:tail#sum`: with `lpPair a b = ∫ a b dμ` (the bilinear complex pairing, an
inner product against `star a`), the double series of pairings of the annulus increments
`Δ_{n+1} F`, `Δ_{m+1} G` has sum `lpPair F (Pt G)` as soon as it is absolutely summable. The finite
square sums are `lpPair (E_N F) (Pt (E_N G))` by telescoping, and `E_N → id` in `L²` by Lévy.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace EinsteinFull.AnnuliSupport

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : ℕ → MeasurableSpace Ω}

/-- The bilinear complex pairing of two classes. -/
noncomputable def lpPair (a b : Lp ℂ 2 μ) : ℂ := ∫ x, a x * b x ∂μ

@[nolint unusedArguments]
theorem lpPair_eq_inner (a b : Lp ℂ 2 μ) : lpPair a b = inner ℂ (star a) b :=
  (EinsteinFull.lpStar_inner_eq_integral a b).symm

@[nolint unusedArguments]
theorem lpStar_zero' : star (0 : Lp ℂ 2 μ) = 0 := by
  have h := EinsteinFull.lpStar_sub (0 : Lp ℂ 2 μ) 0
  rw [sub_self, sub_self] at h
  exact h

theorem lpPair_add_left (a a' b : Lp ℂ 2 μ) : lpPair (a + a') b = lpPair a b + lpPair a' b := by
  rw [lpPair_eq_inner, lpPair_eq_inner, lpPair_eq_inner, EinsteinFull.lpStar_add, inner_add_left]

theorem lpPair_add_right (a b b' : Lp ℂ 2 μ) : lpPair a (b + b') = lpPair a b + lpPair a b' := by
  rw [lpPair_eq_inner, lpPair_eq_inner, lpPair_eq_inner, inner_add_right]

theorem lpPair_sum_left {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 μ) (b : Lp ℂ 2 μ) :
    lpPair (∑ i ∈ s, f i) b = ∑ i ∈ s, lpPair (f i) b :=
  map_sum (AddMonoidHom.mk' (fun a => lpPair a b) (fun a a' => lpPair_add_left a a' b)) f s

theorem lpPair_sum_right {ι : Type*} (s : Finset ι) (a : Lp ℂ 2 μ) (g : ι → Lp ℂ 2 μ) :
    lpPair a (∑ i ∈ s, g i) = ∑ i ∈ s, lpPair a (g i) :=
  map_sum (AddMonoidHom.mk' (fun b => lpPair a b) (fun b b' => lpPair_add_right a b b')) g s

theorem sum_grid_lpPair (Pt : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (f g : ℕ → Lp ℂ 2 μ) (N : ℕ) :
    ∑ k ∈ Finset.range N ×ˢ Finset.range N, lpPair (f k.1) (Pt (g k.2)) =
      lpPair (∑ i ∈ Finset.range N, f i) (Pt (∑ j ∈ Finset.range N, g j)) := by
  rw [map_sum Pt, lpPair_sum_left, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lpPair_sum_right]

@[nolint unusedArguments]
theorem sum_annDelta (hm : ∀ n, 𝓕 n ≤ m0) (U : Lp ℂ 2 μ) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), annDelta hm U (i + 1) =
      (condExpL2 ℂ ℂ (hm (N + 1)) U : Lp ℂ 2 μ) := by
  induction N with
  | zero => simp [annDelta]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have e : N + 1 + 1 - 1 = N + 1 := by omega
    have h2 : annDelta hm U (N + 1 + 1) =
        (condExpL2 ℂ ℂ (hm (N + 1 + 1)) U : Lp ℂ 2 μ) -
          (condExpL2 ℂ ℂ (hm (N + 1)) U : Lp ℂ 2 μ) := by
      have key : ∀ k : ℕ, k = N + 1 →
          (condExpL2 ℂ ℂ (hm k) U : Lp ℂ 2 μ) = (condExpL2 ℂ ℂ (hm (N + 1)) U : Lp ℂ 2 μ) := by
        rintro k rfl; rfl
      rw [annDelta, if_neg (by omega), key _ e]
    rw [h2]
    abel

theorem tendsto_square_sum {f : ℕ × ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1), f k) atTop
      (𝓝 (∑' k, f k)) := by
  have hT : Tendsto (fun s : Finset (ℕ × ℕ) => ∑ k ∈ s, f k) atTop (𝓝 (∑' k, f k)) :=
    hf.hasSum
  have hsq : Tendsto (fun n : ℕ => (Finset.range (n + 1) ×ˢ Finset.range (n + 1) :
      Finset (ℕ × ℕ))) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro s
    refine ⟨s.sup (fun k => max k.1 k.2), fun n hn k hk => ?_⟩
    have h1 : max k.1 k.2 ≤ s.sup (fun k : ℕ × ℕ => max k.1 k.2) :=
      Finset.le_sup (f := fun k : ℕ × ℕ => max k.1 k.2) hk
    simp only [Finset.mem_product, Finset.mem_range]
    constructor <;> omega
  exact hT.comp hsq

theorem hasSum_lpPair_annDelta (hmono : Monotone 𝓕) (hm : ∀ n, 𝓕 n ≤ m0)
    (hsup : ⨆ n, 𝓕 n = m0) (Pt : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (F G : Lp ℂ 2 μ)
    (hsum : Summable (fun k : ℕ × ℕ =>
      ‖lpPair (annDelta hm F (k.1 + 1)) (Pt (annDelta hm G (k.2 + 1)))‖)) :
    HasSum (fun k : ℕ × ℕ => lpPair (annDelta hm F (k.1 + 1)) (Pt (annDelta hm G (k.2 + 1))))
      (lpPair F (Pt G)) := by
  have hs : Summable (fun k : ℕ × ℕ =>
      lpPair (annDelta hm F (k.1 + 1)) (Pt (annDelta hm G (k.2 + 1)))) := hsum.of_norm
  have h1 := tendsto_square_sum hs
  have e : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      lpPair (annDelta hm F (k.1 + 1)) (Pt (annDelta hm G (k.2 + 1))) =
      inner ℂ (star (condExpL2 ℂ ℂ (hm (n + 1)) F : Lp ℂ 2 μ))
        (Pt (condExpL2 ℂ ℂ (hm (n + 1)) G : Lp ℂ 2 μ)) := by
    intro n
    rw [← lpPair_eq_inner, ← sum_annDelta hm F n, ← sum_annDelta hm G n]
    exact sum_grid_lpPair Pt (fun i => annDelta hm F (i + 1)) (fun j => annDelta hm G (j + 1))
      (n + 1)
  have hF := (tendsto_condExpL2 hmono hm hsup F).comp (tendsto_add_atTop_nat 1)
  have hG := (tendsto_condExpL2 hmono hm hsup G).comp (tendsto_add_atTop_nat 1)
  have hF' := ((EinsteinFull.lpStar_continuous (μ := μ)).tendsto F).comp hF
  have hG' := (Pt.continuous.tendsto G).comp hG
  have hI := Filter.Tendsto.inner (𝕜 := ℂ) hF' hG'
  have h2 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      lpPair (annDelta hm F (k.1 + 1)) (Pt (annDelta hm G (k.2 + 1)))) atTop
      (𝓝 (lpPair F (Pt G))) := by
    rw [lpPair_eq_inner]
    exact hI.congr fun n => (e n).symm
  have h3 := tendsto_nhds_unique h1 h2
  rw [← h3]
  exact hs.hasSum

end EinsteinFull.AnnuliSupport
