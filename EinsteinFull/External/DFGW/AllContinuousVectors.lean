import EinsteinFull.External.DFGW.ContinuousVectors
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! # Strong continuity of all transition orbits

The open-set indicators lie in the closed subspace of strongly continuous vectors. A
monotone-class argument extends this to all measurable-set indicators and then to `L²`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology symmDiff Function

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The indicator of every measurable set lies in the strongly continuous subspace. -/
theorem indicator_measurable_mem_continuousVectors (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    {A : Set S} (hA : MeasurableSet A) (hμA : μ A ≠ ∞) :
    indicatorConstLp 2 hA hμA (1 : ℝ) ∈ continuousVectors hP := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let L := continuousVectors hP
  have hopen : ∀ U (hU : IsOpen U),
      indicatorConstLp 2 hU.measurableSet (measure_ne_top μ U) (1 : ℝ) ∈ L := by
    intro U hU
    exact indicator_mem_continuousVectors hP hU (measure_ne_top μ U)
  have hcompl : ∀ B (hB : MeasurableSet B),
      indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ) ∈ L →
      indicatorConstLp 2 hB.compl (measure_ne_top μ Bᶜ) (1 : ℝ) ∈ L := by
    intro B hB hmem
    have heq : indicatorConstLp 2 hB.compl (measure_ne_top μ Bᶜ) (1 : ℝ) =
        indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ) -
          indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ) := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hB.compl)
        (hμs := measure_ne_top μ Bᶜ) (c := (1 : ℝ)),
        indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
          (hμs := measure_ne_top μ univ) (c := (1 : ℝ)),
        indicatorConstLp_coeFn (p := 2) (hs := hB)
          (hμs := measure_ne_top μ B) (c := (1 : ℝ)),
        Lp.coeFn_sub (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ))
          (indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ))] with x hc hu hb hs
      rw [hs, hc]
      simp only [Pi.sub_apply]
      rw [hu, hb]
      by_cases hx : x ∈ B <;> simp [hx]
    rw [heq]
    exact L.sub_mem (hopen univ isOpen_univ) hmem
  have hunion : ∀ B C (hB : MeasurableSet B) (hC : MeasurableSet C), Disjoint B C →
      indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ) ∈ L →
      indicatorConstLp 2 hC (measure_ne_top μ C) (1 : ℝ) ∈ L →
      indicatorConstLp 2 (hB.union hC) (measure_ne_top μ (B ∪ C)) (1 : ℝ) ∈ L := by
    intro B C hB hC hdisj hBm hCm
    rw [indicatorConstLp_disjoint_union hB hC (measure_ne_top μ B) (measure_ne_top μ C) hdisj]
    exact L.add_mem hBm hCm
  have hiUnion : ∀ (F : ℕ → Set S), Pairwise (Disjoint on F) →
      ∀ (hF : ∀ i, MeasurableSet (F i)),
      (∀ i, indicatorConstLp 2 (hF i) (measure_ne_top μ (F i)) (1 : ℝ) ∈ L) →
      indicatorConstLp 2 (MeasurableSet.iUnion hF) (measure_ne_top μ (⋃ i, F i)) (1 : ℝ) ∈ L := by
    intro F hdisj hF hmem
    let U : ℕ → Set S := fun n => ⋃ i < n, F i
    have hU (n : ℕ) : MeasurableSet (U n) :=
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hF i
    have hsucc (n : ℕ) : U (n + 1) = U n ∪ F n := by
      ext x
      simp only [U, mem_iUnion, mem_union]
      constructor
      · rintro ⟨i, hi, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact Or.inl ⟨i, hi, hx⟩
        · exact Or.inr hx
      · rintro (⟨i, hi, hx⟩ | hx)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
        · exact ⟨n, Nat.lt_succ_self n, hx⟩
    have hpartial : ∀ n, indicatorConstLp 2 (hU n) (measure_ne_top μ (U n)) (1 : ℝ) ∈ L := by
      intro n
      induction n with
      | zero =>
          have hz : U 0 = ∅ := by simp [U]
          simp only [hz, indicatorConstLp_empty]
          exact L.zero_mem
      | succ n ih =>
          have hd : Disjoint (U n) (F n) := by
            apply Set.disjoint_left.mpr
            intro x hxU hxF
            obtain ⟨i, hi, hxFi⟩ := by simpa only [U, mem_iUnion] using hxU
            exact (Set.disjoint_left.mp (hdisj (Nat.ne_of_lt hi))) hxFi hxF
          have hm := hunion (U n) (F n) (hU n) (hF n) hd ih (hmem n)
          simpa only [hsucc] using hm
    have htail : Tendsto (fun n : ℕ => μ (⋃ i ≥ n, F i)) atTop (𝓝 0) :=
      tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint (fun i => (hF i).nullMeasurableSet) hdisj
    have hsub (n : ℕ) : U n ∆ (⋃ i, F i) ⊆ ⋃ i ≥ n, F i := by
      intro x hx
      rcases Set.mem_symmDiff.mp hx with ⟨hxU, hxnot⟩ | ⟨hxall, hxnot⟩
      · have : x ∈ ⋃ i, F i := by
          obtain ⟨i, _, hxi⟩ := by simpa only [U, mem_iUnion] using hxU
          exact mem_iUnion.mpr ⟨i, hxi⟩
        exact (hxnot this).elim
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxall
        have hni : n ≤ i := by
          by_contra h
          apply hxnot
          exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Nat.lt_of_not_ge h, hxi⟩⟩
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hni, hxi⟩⟩
    have hdiff : Tendsto (fun n : ℕ => μ (U n ∆ (⋃ i, F i))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
        (fun _ => zero_le) (fun n => measure_mono (hsub n))
    have hlimit : Tendsto (fun n => indicatorConstLp 2 (hU n) (measure_ne_top μ (U n)) (1 : ℝ))
        atTop (𝓝 (indicatorConstLp 2 (MeasurableSet.iUnion hF)
          (measure_ne_top μ (⋃ i, F i)) (1 : ℝ))) :=
      tendsto_indicatorConstLp_set (by simp : (2 : ℝ≥0∞) ≠ ∞) hdiff
    exact (isClosed_continuousVectors hP).mem_of_tendsto hlimit (Eventually.of_forall hpartial)
  have hall : ∀ B (hB : MeasurableSet B),
      indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ) ∈ L :=
    MeasurableSet.induction_on_open hopen hcompl hiUnion
  exact hall A hA

/-- Every square-integrable observable has a strongly continuous transition orbit at zero. -/
theorem tendsto_transitionOperator_zero (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) : Tendsto (fun t : ℝ≥0 => transitionOperator hP t f) (𝓝 0) (𝓝 f) := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let L := continuousVectors hP
  have hscale (B : Set S) (hB : MeasurableSet B) (c : ℝ) :
      indicatorConstLp 2 hB (measure_ne_top μ B) c =
        c • indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ) := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hB)
      (hμs := measure_ne_top μ B) (c := c),
      indicatorConstLp_coeFn (p := 2) (hs := hB)
        (hμs := measure_ne_top μ B) (c := (1 : ℝ)),
      Lp.coeFn_smul c (indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ))] with x hc h1 hs
    rw [hs, hc]
    simp only [Pi.smul_apply]
    rw [h1]
    by_cases hx : x ∈ B <;> simp [hx, smul_eq_mul]
  have hall : ∀ f : Lp ℝ 2 μ, f ∈ L := by
    refine Lp.induction (by simp : (2 : ℝ≥0∞) ≠ ∞) (fun f => f ∈ L) ?_ ?_
      (isClosed_continuousVectors hP)
    · intro c B hB hμB
      change indicatorConstLp 2 hB hμB.ne c ∈ L
      rw [hscale]
      exact L.smul_mem c (indicator_measurable_mem_continuousVectors hP hB (measure_ne_top μ B))
    · intro f g hf hg hdisj hfm hgm
      exact L.add_mem hfm hgm
  exact hall f

end EinsteinFull.External.DFGW
