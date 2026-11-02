import EinsteinRelation.Regeneration.CycleRewardFactorsDecoder
import EinsteinRelation.Regeneration.CycleRecordMeasurability
import EinsteinRelation.Regeneration.RegenerationGrid

/-!
# The measurable shift of the restricted future record

Source `paper/main.tex:421–426`. A continuous decoder of the restricted field
allows evaluation after the random spatial shift. The resulting map agrees
with the literal next record whenever that shift moves the future half-space
inside itself. No invariance of a probability law is asserted here.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- Reading the path and Bernoulli coordinates of a future record. -/
def recordSample {d : ℕ} {i : Fin d} {R : ℝ} (y : FutureState d i R) : CoupledSample d :=
  (y.1, y.2.1)

theorem measurable_recordSample {d : ℕ} (i : Fin d) (R : ℝ) :
    Measurable (recordSample (d := d) (i := i) (R := R)) :=
  measurable_fst.prodMk measurable_snd.fst

/-- A future record built directly from its reduced environment, without
applying the physical-to-reduced map again (`paper/main.tex:331–340`). -/
def recordFromReduced {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (E : FieldPair d) (z : CoupledSample d) (t : ℝ≥0) : FutureState d i R :=
  ((recenterSample (z.1 t) (sampleTimeShift Δ z t)).1,
    (sampleTimeShift Δ z t).2,
    fun x => ((translate (z.1 t) E).1 x, (translate (z.1 t) E).2 x))

/-- Joint measurability of a reduced future record at a variable time. -/
theorem measurable_recordFromReduced {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) :
    Measurable (fun p : (FieldPair d × CoupledSample d) × ℝ≥0 =>
      recordFromReduced Δ R i p.1.1 p.1.2 p.2) := by
  have hx : Measurable (fun p : (FieldPair d × CoupledSample d) × ℝ≥0 => p.1.2.1 p.2) :=
    measurable_path_eval.comp (measurable_snd.prodMk measurable_fst.snd.fst)
  have hs : Measurable (fun p : (FieldPair d × CoupledSample d) × ℝ≥0 =>
      sampleTimeShift Δ p.1.2 p.2) :=
    (measurable_sampleTimeShift Δ).comp (measurable_snd.prodMk measurable_fst.snd)
  have hsample := measurable_recenterSample.comp (hx.prodMk hs)
  have hE := Probability.continuous_translate.measurable.comp (hx.prodMk measurable_fst.fst)
  have hfield : Measurable (fun p : (FieldPair d × CoupledSample d) × ℝ≥0 =>
      (recordFromReduced Δ R i p.1.1 p.1.2 p.2).2.2) := by
    apply measurable_pi_iff.mpr
    intro x
    have heval : Continuous (fun E : FieldPair d => (E.1 (x : Vec d), E.2 (x : Vec d))) :=
      (continuous_fst.eval continuous_const).prodMk (continuous_snd.eval continuous_const)
    exact heval.measurable.comp hE
  exact hsample.fst.prodMk (hs.snd.prodMk hfield)

/-- The source future record uses precisely the reduced physical environment. -/
theorem recordFromReduced_reduce {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (ω : FieldPair d) (z : CoupledSample d) (t : ℝ≥0) :
    recordFromReduced Δ R i (reduce ω) z t = futureRecord Δ R ω z i t := rfl

/-- The measurable record shift associated with a continuous field decoder.
Its characterization on actual records is proved below. -/
def shiftRestrictedRecord {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (D : (FutureHalfSpace d i R → Mat d × ℝ) → C(FutureHalfSpace d i R, Mat d × ℝ))
    (y : FutureState d i R) : FutureState d i R :=
  recordFromReduced Δ R i (extendFromHalfSpace i R (D y.2.2)) (recordSample y)
    (firstRegenerationTime Δ lam R (recordSample y) i).toNNReal

theorem measurable_shiftRestrictedRecord {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (D : (FutureHalfSpace d i R → Mat d × ℝ) → C(FutureHalfSpace d i R, Mat d × ℝ))
    (hD : @Measurable _ _ inferInstance (borel _) D) :
    Measurable (shiftRestrictedRecord Δ lam R i D) := by
  have hs := measurable_recordSample i R
  have hE : Measurable (fun y : FutureState d i R => extendFromHalfSpace i R (D y.2.2)) :=
    (measurable_extendFromHalfSpace i R).comp (hD.comp measurable_snd.snd)
  have ht := ((measurable_firstRegenerationTime Δ lam R i).comp hs).ennreal_toNNReal
  exact (measurable_recordFromReduced Δ R i).comp ((hE.prodMk hs).prodMk ht)

/-- Adding a grid time adds its exact integer bit index. -/
theorem gridIndex_grid_add (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) (t : ℝ≥0) :
    gridIndex Δ ((n : ℝ≥0) * Δ + t) = n + gridIndex Δ t := by
  have hΔR : (Δ : ℝ) ≠ 0 := ne_of_gt hΔ
  simp only [gridIndex, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, add_div,
    mul_div_cancel_right₀ _ hΔR]
  rw [add_comm (n : ℝ), Nat.floor_add_natCast (by positivity) n, Nat.add_comm]

/-- Future records compose at grid times if the second spatial shift is
forward. The decoder is only used on actual continuous restrictions. -/
theorem shiftRestrictedRecord_futureRecord {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d)
    (D : (FutureHalfSpace d i R → Mat d × ℝ) → C(FutureHalfSpace d i R, Mat d × ℝ))
    (hD : ∀ f : C(FutureHalfSpace d i R, Mat d × ℝ), D (fun x => f x) = f)
    (ω : FieldPair d) (z : CoupledSample d) (n : ℕ)
    (hforward : 0 ≤ z.1 ((n : ℝ≥0) * Δ +
        (firstRegenerationTime Δ lam R (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) i).toNNReal) i -
      z.1 ((n : ℝ≥0) * Δ) i) :
    shiftRestrictedRecord Δ lam R i D
        (futureRecord Δ R ω z i ((n : ℝ≥0) * Δ)) =
      futureRecord Δ R ω z i ((n : ℝ≥0) * Δ +
        (firstRegenerationTime Δ lam R (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) i).toNNReal) := by
  let t : ℝ≥0 := (n : ℝ≥0) * Δ
  let u : ℝ≥0 := (firstRegenerationTime Δ lam R (sampleTimeShift Δ z t) i).toNNReal
  have hsample : recordSample (futureRecord Δ R ω z i t) =
      recenterSample (z.1 t) (sampleTimeShift Δ z t) := rfl
  have htime : (firstRegenerationTime Δ lam R
      (recordSample (futureRecord Δ R ω z i t)) i).toNNReal = u := by
    rw [hsample, firstRegenerationTime_recenterSample]
  have hfield : D (futureRecord Δ R ω z i t).2.2 =
      restrictHalfSpace i R (translate (z.1 t) (reduce ω)) :=
    hD (restrictHalfSpace i R (translate (z.1 t) (reduce ω)))
  change shiftRestrictedRecord Δ lam R i D (futureRecord Δ R ω z i t) =
    futureRecord Δ R ω z i (t + u)
  unfold shiftRestrictedRecord
  rw [htime, hfield, hsample]
  apply Prod.ext
  · apply ContinuousMap.ext
    intro s
    change (z.1 (t + (u + s)) - z.1 t) - (z.1 (t + u) - z.1 t) =
      z.1 (t + u + s) - z.1 (t + u)
    rw [← add_assoc]
    abel
  · apply Prod.ext
    · funext k
      change z.2 (gridIndex Δ t + (gridIndex Δ u + k)) = z.2 (gridIndex Δ (t + u) + k)
      rw [show gridIndex Δ (t + u) = n + gridIndex Δ u from gridIndex_grid_add Δ hΔ n u,
        show gridIndex Δ t = n from gridIndex_mul Δ hΔ n, Nat.add_assoc]
    · funext x
      have hx : -2 * R ≤ ((z.1 (t + u) - z.1 t) + (x : Vec d)) i := by
        change -2 * R ≤ (z.1 (t + u) i - z.1 t i) + (x : Vec d) i
        linarith [x.2]
      have heq := translate_extend_eq_of_mem i R (translate (z.1 t) (reduce ω))
        (z.1 (t + u) - z.1 t) x hx
      change ((translate (z.1 (t + u) - z.1 t)
          (extendFromHalfSpace i R (restrictHalfSpace i R
            (translate (z.1 t) (reduce ω))))).1 x,
        (translate (z.1 (t + u) - z.1 t)
          (extendFromHalfSpace i R (restrictHalfSpace i R
            (translate (z.1 t) (reduce ω))))).2 x) =
        ((translate (z.1 (t + u)) (reduce ω)).1 x,
          (translate (z.1 (t + u)) (reduce ω)).2 x)
      rw [heq.1, heq.2, translate_add, sub_add_cancel]


end EinsteinRelation.Regeneration
