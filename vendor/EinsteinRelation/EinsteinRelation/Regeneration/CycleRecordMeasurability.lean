import EinsteinRelation.Regeneration.RegenerationShiftObservables
import EinsteinRelation.Regeneration.RenewalCarriers

/-! # Measurability of the actual cycle records

Source `paper/main.tex:331–348,421–426`. The record consists of the recentered
future path, future bits and the reduced translated environment restricted to
the future half-space. All components remain measurable when evaluated at the
literal regeneration time, with `ENNReal.toNNReal` totalizing infinite times.
No finiteness, renewal identity or conditional invariance is assumed.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-- Evaluating the complete future record at any measurable nonnegative time
preserves measurability (`paper/main.tex:331–340,421–426`). -/
theorem measurable_futureRecord_at {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (t : FieldPair d × CoupledSample d → ℝ≥0) (ht : Measurable t) :
    Measurable (fun p : FieldPair d × CoupledSample d =>
      futureRecord Δ R p.1 p.2 i (t p)) := by
  have hx : Measurable (fun p : FieldPair d × CoupledSample d => p.2.1 (t p)) :=
    measurable_path_eval.comp (ht.prodMk measurable_snd.fst)
  have hshift : Measurable (fun p : FieldPair d × CoupledSample d =>
      sampleTimeShift Δ p.2 (t p)) :=
    (measurable_sampleTimeShift Δ).comp (ht.prodMk measurable_snd)
  have hsample : Measurable (fun p : FieldPair d × CoupledSample d =>
      recenterSample (p.2.1 (t p)) (sampleTimeShift Δ p.2 (t p))) :=
    measurable_recenterSample.comp (hx.prodMk hshift)
  have henv : Measurable (fun p : FieldPair d × CoupledSample d =>
      translate (p.2.1 (t p)) (reduce p.1)) :=
    Probability.continuous_translate.measurable.comp
      (hx.prodMk (Probability.measurable_reduce.comp measurable_fst))
  have hfield : Measurable (fun p : FieldPair d × CoupledSample d =>
      (futureRecord Δ R p.1 p.2 i (t p)).2.2) := by
    apply measurable_pi_iff.mpr
    intro x
    have heval : Continuous (fun ω : FieldPair d =>
        (ω.1 (x : Vec d), ω.2 (x : Vec d))) :=
      (continuous_fst.eval continuous_const).prodMk (continuous_snd.eval continuous_const)
    exact heval.measurable.comp henv
  exact hsample.fst.prodMk (hsample.snd.prodMk hfield)

/-- Every literal cycle record is measurable, including on samples where its
regeneration time is infinite (`paper/main.tex:331–348`). -/
theorem measurable_cycleRecord {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (k : ℕ) :
    Measurable (Renewal.cycleRecord hd lam l k) :=
  measurable_futureRecord_at (Renewal.regenDelta lam) (l / lam) (Renewal.forceCoord hd)
    _ (((measurable_regenerationTime (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) k).comp measurable_snd).ennreal_toNNReal)


end EinsteinRelation.Regeneration
