import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory
open Classical
namespace EinsteinRelation.Correctors

/-- Compatible representatives glue on a countable increasing exhaustion;
source application: `paper/main.tex:693-698`. Every point is covered, so
no value outside the exhaustion is introduced. -/
theorem exists_ae_glue_of_exhaustion {X E : Type*} [MeasurableSpace X]
    (μ : Measure X) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (_hmono : Monotone U) (hcover : ∀ x, ∃ n, x ∈ U n)
    (u : ℕ → X → E)
    (hcompat : ∀ n m : ℕ, n ≤ m → u m =ᵐ[μ.restrict (U n)] u n) :
    ∃ v : X → E, ∀ n, v =ᵐ[μ.restrict (U n)] u n := by
  -- Define the minimal index function
  let n_min (x : X) : ℕ := Nat.find (hcover x)
  have hn_min (x : X) : x ∈ U (n_min x) := Nat.find_spec (hcover x)
  have hn_min_min (x : X) {k : ℕ} (hk : x ∈ U k) : n_min x ≤ k := Nat.find_min' (hcover x) hk
  -- Define v(x) = u_{n_min(x)}(x)
  let v : X → E := λ x => u (n_min x) x
  refine ⟨v, ?_⟩
  intro n
  rw [Filter.EventuallyEq, ae_restrict_iff' (hU n)]
  -- Need: ∀ᵐ x ∂μ, x ∈ U n → v x = u n x
  -- i.e., the set {x | x ∈ U n ∧ v x ≠ u n x} has measure zero
  have h_null (k : ℕ) (hk : k ≤ n) : μ {x | x ∈ U k ∧ u k x ≠ u n x} = 0 := by
    have h_comp := hcompat k n hk
    -- h_comp : u n =ᵐ[μ.restrict (U k)] u k
    have h_ae : ∀ᵐ x ∂μ, x ∈ U k → u n x = u k x := by
      simpa [Filter.EventuallyEq, ae_restrict_iff' (hU k)] using h_comp
    rw [ae_iff] at h_ae
    simpa [eq_comm] using h_ae
  -- The set where v differs from u n on U n
  have h_subset : {x | x ∈ U n ∧ v x ≠ u n x} ⊆ ⋃ k ∈ Finset.range (n + 1), {x | x ∈ U k ∧ u k x ≠ u n x} := by
    intro x ⟨hxU, hx_ne⟩
    have hk : n_min x ≤ n := hn_min_min x hxU
    have hk_lt : n_min x < n + 1 := Nat.lt_succ_of_le hk
    refine Set.mem_biUnion (Finset.mem_range.2 hk_lt) ?_
    refine ⟨hn_min x, ?_⟩
    simpa [v] using hx_ne
  have h_null_union : μ (⋃ k ∈ Finset.range (n + 1), {x | x ∈ U k ∧ u k x ≠ u n x}) = 0 := by
    apply le_antisymm
    · calc
        μ (⋃ k ∈ Finset.range (n + 1), {x | x ∈ U k ∧ u k x ≠ u n x}) ≤
            ∑ k ∈ Finset.range (n + 1), μ {x | x ∈ U k ∧ u k x ≠ u n x} :=
          measure_biUnion_finset_le _ _
        _ = ∑ k ∈ Finset.range (n + 1), 0 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          have hk_le_n : k ≤ n := Nat.le_of_lt_succ hk
          rw [h_null k hk_le_n]
        _ = 0 := Finset.sum_const_zero
    · exact zero_le
  have h_main : μ {x | x ∈ U n ∧ v x ≠ u n x} = 0 :=
    measure_mono_null h_subset h_null_union
  rw [ae_iff]
  simpa using h_main

end EinsteinRelation.Correctors
