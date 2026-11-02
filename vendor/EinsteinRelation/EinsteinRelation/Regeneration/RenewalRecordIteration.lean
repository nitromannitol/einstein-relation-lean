import EinsteinRelation.Regeneration.FirstRegenerationForward

/-!
# Iterating the literal restricted regeneration record

Source `paper/main.tex:413–426`. Conditional invariance of the first record
implies invariance of its law under the measurable restricted shift. This
module also propagates finiteness, rather than assuming that later times
are finite when composing records.
-/

open MeasureTheory Function
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- The literal record at an iterated regeneration time (`paper/main.tex:331–340`). -/
def iteratedRecord {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k : ℕ)
    (p : FieldPair d × CoupledSample d) : FutureState d i R :=
  futureRecord Δ R p.1 p.2 i (regenerationTime Δ lam R p.2 i k).toNNReal

theorem measurable_iteratedRecord {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k : ℕ) :
    Measurable (iteratedRecord Δ lam R i k) :=
  measurable_futureRecord_at Δ R i _
    (((measurable_regenerationTime Δ lam R i k).comp measurable_snd).ennreal_toNNReal)

/-- Finiteness and forward displacement are the two properties needed to
shift a restricted record (`paper/main.tex:421–425`). -/
def RecordCanShift {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (y : FutureState d i R) : Prop :=
  firstRegenerationTime Δ lam R (recordSample y) i ≠ ⊤ ∧
    0 ≤ y.1 (firstRegenerationTime Δ lam R (recordSample y) i).toNNReal i - y.1 0 i

theorem measurableSet_recordCanShift {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) :
    MeasurableSet {y | RecordCanShift Δ lam R i y} := by
  have hτ := (measurable_firstRegenerationTime Δ lam R i).comp (measurable_recordSample i R)
  have hx := measurable_path_eval.comp (hτ.ennreal_toNNReal.prodMk measurable_fst)
  have hx0 : Measurable (fun y : FutureState d i R => y.1 0 i) :=
    (measurable_pi_apply i).comp ((continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_fst)
  exact (hτ (measurableSet_singleton ⊤)).compl.inter
    (measurableSet_le measurable_const (((measurable_pi_apply i).comp hx).sub hx0))

theorem sampleTimeShift_zero {d : ℕ} (Δ : ℝ≥0) (z : CoupledSample d) :
    sampleTimeShift Δ z 0 = z := by
  apply Prod.ext
  · ext t
    simp [sampleTimeShift, pathTimeShift]
  · funext n
    simp [sampleTimeShift, gridIndex]

theorem regenerationTime_one {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (z : CoupledSample d)
    (i : Fin d) : regenerationTime Δ lam R z i 1 = firstRegenerationTime Δ lam R z i := by
  simp [regenerationTime, sampleTimeShift_zero]

/-- Reading a future record preserves its first regeneration time and its
coordinate increments (`paper/main.tex:421–425`). -/
theorem recordCanShift_futureRecord_iff {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (ω : FieldPair d) (z : CoupledSample d) (t : ℝ≥0) :
    RecordCanShift Δ lam R i (futureRecord Δ R ω z i t) ↔
      firstRegenerationTime Δ lam R (sampleTimeShift Δ z t) i ≠ ⊤ ∧
        0 ≤ z.1 (t + (firstRegenerationTime Δ lam R (sampleTimeShift Δ z t) i).toNNReal) i -
          z.1 t i := by
  have hs : recordSample (futureRecord Δ R ω z i t) =
      recenterSample (z.1 t) (sampleTimeShift Δ z t) := rfl
  unfold RecordCanShift
  rw [hs, firstRegenerationTime_recenterSample]
  change (_ ≠ ⊤ ∧ 0 ≤ (z.1 (t + _) i - z.1 t i) - (z.1 (t + 0) i - z.1 t i)) ↔ _
  simp only [add_zero, sub_self, sub_zero]

/-- On every finite grid record which can shift, the literal next record
is the measurable record shift and the next regeneration time is finite. -/
theorem iteratedRecord_succ_of_canShift {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d)
    (D : (FutureHalfSpace d i R → Mat d × ℝ) → C(FutureHalfSpace d i R, Mat d × ℝ))
    (hD : ∀ f : C(FutureHalfSpace d i R, Mat d × ℝ), D (fun x => f x) = f)
    (p : FieldPair d × CoupledSample d) (k : ℕ)
    (hfin : regenerationTime Δ lam R p.2 i k ≠ ⊤)
    (hcan : RecordCanShift Δ lam R i (iteratedRecord Δ lam R i k p)) :
    regenerationTime Δ lam R p.2 i (k + 1) ≠ ⊤ ∧
      iteratedRecord Δ lam R i (k + 1) p =
        shiftRestrictedRecord Δ lam R i D (iteratedRecord Δ lam R i k p) := by
  obtain ⟨m, hm⟩ := regenerationTime_mem_grid Δ hΔ lam R p.2 i k hfin
  have hcan' := (recordCanShift_futureRecord_iff Δ lam R i p.1 p.2
    (regenerationTime Δ lam R p.2 i k).toNNReal).mp hcan
  have hnext := regenerationTime_succ_eq Δ lam R p.2 i k hfin
  refine ⟨?_, ?_⟩
  · rw [hnext]
    exact ENNReal.add_ne_top.mpr ⟨hfin, hcan'.1⟩
  · have ht : (regenerationTime Δ lam R p.2 i k).toNNReal = (m : ℝ≥0) * Δ := by
      rw [hm, ENNReal.toNNReal_coe]
    have hsum : (regenerationTime Δ lam R p.2 i (k + 1)).toNNReal =
        (m : ℝ≥0) * Δ +
          (firstRegenerationTime Δ lam R (sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)) i).toNNReal := by
      rw [hnext, ENNReal.toNNReal_add hfin hcan'.1, ht]
    unfold iteratedRecord
    rw [hsum, ht]
    exact (shiftRestrictedRecord_futureRecord Δ hΔ lam R i D hD p.1 p.2 m
      (by simpa only [ht] using hcan'.2)).symm

/-- The actual record sequence inherits the first-record law and conditional
invariance. Both laws on the first record are premises to be supplied by the
slice factorization; they are not treated as external inputs. -/
theorem iteratedRecord_law_of_first_and_conditional_law {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (μ κ : Measure (FieldPair d × CoupledSample d)) (hκ : κ ≪ μ)
    (hgood : ∀ᵐ p ∂μ, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i 0 p))
    (hfirst : μ.map (iteratedRecord Δ lam R i 1) = κ.map (iteratedRecord Δ lam R i 0))
    (hcond : κ.map (iteratedRecord Δ lam R i 1) = κ.map (iteratedRecord Δ lam R i 0)) :
    ∀ j : ℕ, (∀ᵐ p ∂μ, regenerationTime Δ lam R p.2 i (j + 1) ≠ ⊤) ∧
      μ.map (iteratedRecord Δ lam R i (j + 1)) =
        κ.map (iteratedRecord Δ lam R i 0) := by
  obtain ⟨D, hDm, hD⟩ := Probability.exists_future_halfSpace_decoder i R
  let Θ := shiftRestrictedRecord Δ lam R i D
  let X := iteratedRecord Δ lam R i
  let ν := κ.map (X 0)
  have hΘ : Measurable Θ := measurable_shiftRestrictedRecord Δ lam R i D hDm
  have hX : ∀ k, Measurable (X k) := measurable_iteratedRecord Δ lam R i
  have hstep0 : ∀ᵐ p ∂μ, regenerationTime Δ lam R p.2 i 1 ≠ ⊤ ∧ X 1 p = Θ (X 0 p) := by
    filter_upwards [hgood] with p hp
    exact iteratedRecord_succ_of_canShift Δ hΔ lam R i D hD p 0 (by simp [regenerationTime]) hp
  have hν : ν.map Θ = ν := by
    rw [Measure.map_map hΘ (hX 0)]
    exact (Measure.map_congr (hκ.ae_eq (hstep0.mono fun _ h => h.2.symm))).trans hcond
  have hνgood : ∀ᵐ y ∂ν, RecordCanShift Δ lam R i y :=
    (ae_map_iff (hX 0).aemeasurable (measurableSet_recordCanShift Δ lam R i)).mpr
      (hκ.ae_le hgood)
  intro j
  induction j with
  | zero => exact ⟨hstep0.mono (fun _ h => h.1), hfirst⟩
  | succ j ih =>
    have hgoodj : ∀ᵐ p ∂μ, RecordCanShift Δ lam R i (X (j + 1) p) := by
      apply ae_of_ae_map (hX (j + 1)).aemeasurable
      rwa [ih.2]
    have hstep : ∀ᵐ p ∂μ,
        regenerationTime Δ lam R p.2 i (j + 1 + 1) ≠ ⊤ ∧
          X (j + 1 + 1) p = Θ (X (j + 1) p) := by
      filter_upwards [ih.1, hgoodj] with p hfin hcan
      exact iteratedRecord_succ_of_canShift Δ hΔ lam R i D hD p (j + 1) hfin hcan
    refine ⟨hstep.mono (fun _ h => h.1), ?_⟩
    change μ.map (X (j + 1 + 1)) = ν
    rw [Measure.map_congr (hstep.mono (fun _ h => h.2))]
    change μ.map (Θ ∘ X (j + 1)) = ν
    rw [← Measure.map_map hΘ (hX (j + 1)), ih.2]
    exact hν


end EinsteinRelation.Regeneration
