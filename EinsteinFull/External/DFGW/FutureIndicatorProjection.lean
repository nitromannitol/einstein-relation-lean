import EinsteinFull.External.DFGW.FutureEventSystem
import EinsteinFull.External.DFGW.AllContinuousVectors

/-! # Past projections of future event indicators

A π–λ argument extends the finite-cylinder Markov property to every future-coordinate event.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology symmDiff Function

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The future-coordinate sigma-algebra is contained in the trajectory Borel sigma-algebra. -/
theorem futureCoordSigma_le : Draft.dfgwCoordSigma (S := S) (Set.Ici 0) ≤
    Draft.dfgwTrajectoryMeasurableSpace (S := S) :=
  iSup₂_le fun t _ => (continuous_eval_const t).measurable.comap_le

/-- The indicator of every future event has a state-determined past projection. -/
theorem future_indicator_mem_stateDeterminedPast (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (B : Set C(ℝ, S)) (hB : MeasurableSet[Draft.dfgwCoordSigma (Set.Ici 0)] B)
    (hfin : P B ≠ ⊤) :
    indicatorConstLp 2 (futureCoordSigma_le B hB) hfin (1 : ℝ) ∈ stateDeterminedPast P := by
  let : IsProbabilityMeasure P := hP.probability
  let L := stateDeterminedPast P
  let m := Draft.dfgwCoordSigma (S := S) (Set.Ici 0)
  have hb : ∀ B (hB : B ∈ futureCylinderEvents (S := S)),
      indicatorConstLp 2 (futureCoordSigma_le B
        (futureCoordSigma_eq_generateFrom (S := S) ▸ MeasurableSpace.GenerateMeasurable.basic B hB))
        (measure_ne_top P B) (1 : ℝ) ∈ L := by
    intro B hB
    obtain ⟨xs, hxs, rfl⟩ := hB
    exact futureCylinderEvent_mem_stateDeterminedPast hP xs hxs _
  have hicon (A B : Set C(ℝ, S)) (hAB : A = B) (hA : MeasurableSet[Draft.dfgwTrajectoryMeasurableSpace (S := S)] A)
      (hB : MeasurableSet[Draft.dfgwTrajectoryMeasurableSpace (S := S)] B) (hAfin : P A ≠ ⊤) (hBfin : P B ≠ ⊤) :
      indicatorConstLp (μ := P) 2 hA hAfin (1 : ℝ) = indicatorConstLp (μ := P) 2 hB hBfin (1 : ℝ) := by
    subst B
    rfl
  have hone : indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P univ) (1 : ℝ) ∈ L := by
    have h := futureCylinderEvent_mem_stateDeterminedPast hP [] (by simp) (measure_ne_top P _)
    have hevent : futureCylinderEvent ([] : List (ℝ≥0 × Set S)) = Set.univ := by
      ext η
      simp [futureCylinderEvent]
    rw [hicon _ _ hevent (measurableSet_futureCylinderEvent [] (by simp))
      MeasurableSet.univ (measure_ne_top P _) (measure_ne_top P _)] at h
    exact h
  have hcompl : ∀ B (hB : MeasurableSet[m] B),
      indicatorConstLp 2 (futureCoordSigma_le B hB) (measure_ne_top P B) (1 : ℝ) ∈ L →
      indicatorConstLp 2 (futureCoordSigma_le Bᶜ hB.compl) (measure_ne_top P Bᶜ) (1 : ℝ) ∈ L := by
    intro B hB hmem
    have heq : indicatorConstLp 2 (futureCoordSigma_le Bᶜ hB.compl) (measure_ne_top P Bᶜ) (1 : ℝ) =
        indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P univ) (1 : ℝ) -
          indicatorConstLp 2 (futureCoordSigma_le B hB) (measure_ne_top P B) (1 : ℝ) := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := futureCoordSigma_le Bᶜ hB.compl)
        (hμs := measure_ne_top P Bᶜ) (c := (1 : ℝ)),
        indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
          (hμs := measure_ne_top P univ) (c := (1 : ℝ)),
        indicatorConstLp_coeFn (p := 2) (hs := futureCoordSigma_le B hB)
          (hμs := measure_ne_top P B) (c := (1 : ℝ)),
        Lp.coeFn_sub (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P univ) (1 : ℝ))
          (indicatorConstLp 2 (futureCoordSigma_le B hB) (measure_ne_top P B) (1 : ℝ))] with x hc hu hb hs
      rw [hs, hc]
      simp only [Pi.sub_apply]
      rw [hu, hb]
      by_cases hx : x ∈ B <;> simp [hx]
    rw [heq]
    exact L.sub_mem hone hmem
  have hunion : ∀ B C (hB : MeasurableSet[m] B) (hC : MeasurableSet[m] C), Disjoint B C →
      indicatorConstLp 2 (futureCoordSigma_le B hB) (measure_ne_top P B) (1 : ℝ) ∈ L →
      indicatorConstLp 2 (futureCoordSigma_le C hC) (measure_ne_top P C) (1 : ℝ) ∈ L →
      indicatorConstLp 2 (futureCoordSigma_le (B ∪ C) (hB.union hC))
        (measure_ne_top P (B ∪ C)) (1 : ℝ) ∈ L := by
    intro B C hB hC hdisj hBm hCm
    rw [indicatorConstLp_disjoint_union (futureCoordSigma_le B hB) (futureCoordSigma_le C hC)
      (measure_ne_top P B) (measure_ne_top P C) hdisj]
    exact L.add_mem hBm hCm
  have hiUnion : ∀ (F : ℕ → Set C(ℝ, S)), Pairwise (Disjoint on F) →
      ∀ (hF : ∀ i, MeasurableSet[m] (F i)),
      (∀ i, indicatorConstLp 2 (futureCoordSigma_le (F i) (hF i))
        (measure_ne_top P (F i)) (1 : ℝ) ∈ L) →
      indicatorConstLp 2 (futureCoordSigma_le (⋃ i, F i) (MeasurableSet.iUnion hF))
        (measure_ne_top P (⋃ i, F i)) (1 : ℝ) ∈ L := by
    intro F hdisj hF hmem
    let U : ℕ → Set C(ℝ, S) := fun n => ⋃ i < n, F i
    have hU (n : ℕ) : MeasurableSet[m] (U n) :=
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
    have hpartial : ∀ n, indicatorConstLp 2 (futureCoordSigma_le (U n) (hU n))
        (measure_ne_top P (U n)) (1 : ℝ) ∈ L := by
      intro n
      induction n with
      | zero =>
        have hz : U 0 = ∅ := by simp [U]
        have hzlp : indicatorConstLp 2 (futureCoordSigma_le (U 0) (hU 0))
            (measure_ne_top P (U 0)) (1 : ℝ) = 0 := by
          apply Lp.ext
          filter_upwards [indicatorConstLp_coeFn (p := 2)
            (hs := futureCoordSigma_le (U 0) (hU 0))
            (hμs := measure_ne_top P (U 0)) (c := (1 : ℝ)), Lp.coeFn_zero ℝ 2 P]
            with x hx hz0
          rw [hx, hz0]
          simp [hz]
        rw [hzlp]
        exact L.zero_mem
      | succ n ih =>
        have hd : Disjoint (U n) (F n) := by
          apply Set.disjoint_left.mpr
          intro x hxU hxF
          obtain ⟨i, hi, hxFi⟩ := by simpa only [U, mem_iUnion] using hxU
          exact (Set.disjoint_left.mp (hdisj (Nat.ne_of_lt hi))) hxFi hxF
        have hm := hunion (U n) (F n) (hU n) (hF n) hd ih (hmem n)
        simpa only [hsucc] using hm
    have htail : Tendsto (fun n : ℕ => P (⋃ i ≥ n, F i)) atTop (𝓝 0) :=
      @tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint C(ℝ, S)
        (Draft.dfgwTrajectoryMeasurableSpace (S := S)) P inferInstance F
        (fun i => (futureCoordSigma_le (F i) (hF i)).nullMeasurableSet) hdisj
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
    have hdiff : Tendsto (fun n : ℕ => P (U n ∆ (⋃ i, F i))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
        (fun _ => zero_le) (fun n => measure_mono (hsub n))
    have hlimit : Tendsto (fun n => indicatorConstLp 2 (futureCoordSigma_le (U n) (hU n))
        (measure_ne_top P (U n)) (1 : ℝ)) atTop
        (𝓝 (indicatorConstLp 2 (futureCoordSigma_le (⋃ i, F i) (MeasurableSet.iUnion hF))
          (measure_ne_top P (⋃ i, F i)) (1 : ℝ))) :=
      tendsto_indicatorConstLp_set (by simp : (2 : ℝ≥0∞) ≠ ∞) hdiff
    exact (isClosed_stateDeterminedPast P).mem_of_tendsto hlimit (Eventually.of_forall hpartial)
  have hall : ∀ B (hB : MeasurableSet[m] B),
      indicatorConstLp 2 (futureCoordSigma_le B hB) (measure_ne_top P B) (1 : ℝ) ∈ L := by
    apply MeasurableSpace.induction_on_inter (m := m)
      (C := fun B hB => indicatorConstLp 2 (futureCoordSigma_le B hB)
        (measure_ne_top P B) (1 : ℝ) ∈ L) futureCoordSigma_eq_generateFrom
      isPiSystem_futureCylinderEvents
    · simp only [indicatorConstLp_empty]
      exact L.zero_mem
    · exact hb
    · exact hcompl
    · exact hiUnion
  exact hall B hB

end EinsteinFull.External.DFGW
