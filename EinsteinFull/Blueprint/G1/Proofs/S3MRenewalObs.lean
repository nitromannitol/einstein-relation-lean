import EinsteinFull.Blueprint.G1.Proofs.S3MRenewalGeom
import EinsteinRelation.Regeneration.CycleRewardFactorsDecoder

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion
  gridIndex recenterSample)

/-! # `rt:m-renewal`: the recorded `m`-cycle observable -/

theorem gain_shift {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d) (z : CoupledSample d)
    (n : ℕ)
    (h : ∀ k : ℕ, z.2 k = true →
      z.1 ((k : ℝ≥0) * Δ) i + 8 * R ≤ z.1 (((k + 1 : ℕ) : ℝ≥0) * Δ) i) :
    ∀ k : ℕ, (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)).2 k = true →
      (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)).1 ((k : ℝ≥0) * Δ) i + 8 * R ≤
        (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)).1 (((k + 1 : ℕ) : ℝ≥0) * Δ) i := by
  intro k hk
  have hk' : z.2 (n + k) = true := by
    have : (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)).2 k = z.2 (n + k) := by
      change z.2 (gridIndex Δ ((n : ℝ≥0) * Δ) + k) = _
      rw [Regeneration.gridIndex_mul Δ hΔ]
    rw [← this]
    exact hk
  have hh := h (n + k) hk'
  have e1 : (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)).1 ((k : ℝ≥0) * Δ) i =
      z.1 (((n + k : ℕ) : ℝ≥0) * Δ) i := by
    change z.1 ((n : ℝ≥0) * Δ + (k : ℝ≥0) * Δ) i = _
    rw [← add_mul, ← Nat.cast_add]
  have e2 : (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)).1 (((k + 1 : ℕ) : ℝ≥0) * Δ) i =
      z.1 (((n + k + 1 : ℕ) : ℝ≥0) * Δ) i := by
    change z.1 ((n : ℝ≥0) * Δ + ((k + 1 : ℕ) : ℝ≥0) * Δ) i = _
    rw [← add_mul, ← Nat.cast_add, Nat.add_assoc]
  rw [e1, e2]
  exact hh

theorem sampleTimeShift_recenter {d : ℕ} (Δ : ℝ≥0) (x : Vec d) (z : CoupledSample d)
    (t : ℝ≥0) :
    sampleTimeShift Δ (recenterSample x z) t = recenterSample x (sampleTimeShift Δ z t) := by
  apply Prod.ext
  · ext u i
    rfl
  · rfl

theorem regenerationTime_recenter {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (x : Vec d) :
    ∀ (j : ℕ) (z : CoupledSample d),
      Regeneration.regenerationTime Δ lam R (recenterSample x z) i j =
        Regeneration.regenerationTime Δ lam R z i j := by
  intro j
  induction j with
  | zero => intro z; rfl
  | succ j ih =>
    intro z
    rw [Regeneration.regenerationTime, Regeneration.regenerationTime, ih z,
      sampleTimeShift_recenter,
      EinsteinRelation.firstRegenerationTime_recenterSample]

open scoped Classical in
/-- The `m`-cycle observable as a function of the recorded future. -/
noncomputable def PhiM {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (D : (Regeneration.FutureHalfSpace d i R → Mat d × ℝ) →
      C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ))
    (G : FieldPair d → ℝ) (m : ℕ) (u : ℝ≥0) (y : Regeneration.FutureState d i R) : ℝ :=
  if Regeneration.regenerationTime Δ lam R (y.1, y.2.1) i m ≤ (u : ℝ≥0∞) then
    G (translate (y.1 u) (extendFromHalfSpace i R (D y.2.2))) else 0

theorem measurable_PhiM {d : ℕ} (Δ : ℝ≥0) (lam R ρ : ℝ) (i : Fin d)
    (D : (Regeneration.FutureHalfSpace d i R → Mat d × ℝ) →
      C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ))
    (hD : @Measurable (Regeneration.FutureHalfSpace d i R → Mat d × ℝ)
      (C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ)) inferInstance (borel _) D)
    (G : FieldPair d → ℝ)
    (hG : @Measurable (FieldPair d) ℝ (localSigma {x : Vec d | euclideanNorm x < ρ})
      inferInstance G)
    (m : ℕ) (u : ℝ≥0) : Measurable (PhiM Δ lam R i D G m u) := by
  classical
  have hpath : Measurable (fun y : Regeneration.FutureState d i R => y.1 u) :=
    (continuous_eval_const u).measurable.comp measurable_fst
  have hY : Measurable (fun y : Regeneration.FutureState d i R => y.2.2) :=
    measurable_snd.comp measurable_snd
  have hE : Measurable (fun y : Regeneration.FutureState d i R =>
      extendFromHalfSpace i R (D y.2.2)) :=
    (measurable_extendFromHalfSpace i R).comp (hD.comp hY)
  have hΦ : Measurable (fun y : Regeneration.FutureState d i R =>
      translate (y.1 u) (extendFromHalfSpace i R (D y.2.2))) :=
    (Probability.continuous_translate (d := d)).measurable.comp (hpath.prodMk hE)
  have hΦloc : @Measurable (Regeneration.FutureState d i R) (FieldPair d) inferInstance
      (localSigma {x : Vec d | euclideanNorm x < ρ})
      (fun y : Regeneration.FutureState d i R =>
        translate (y.1 u) (extendFromHalfSpace i R (D y.2.2))) := by
    refine measurable_iff_comap_le.2 ?_
    unfold localSigma
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun x => ?_
    rw [MeasurableSpace.comap_comp]
    have hev : Measurable (fun ω : FieldPair d => (ω.1 (x : Vec d), ω.2 (x : Vec d))) :=
      (((continuous_eval_const (x : Vec d)).comp continuous_fst).prodMk
        ((continuous_eval_const (x : Vec d)).comp continuous_snd)).measurable
    exact measurable_iff_comap_le.1 (hev.comp hΦ)
  have hGΦ : Measurable (fun y : Regeneration.FutureState d i R =>
      G (translate (y.1 u) (extendFromHalfSpace i R (D y.2.2)))) := hG.comp hΦloc
  have hcond : MeasurableSet {y : Regeneration.FutureState d i R |
      Regeneration.regenerationTime Δ lam R (y.1, y.2.1) i m ≤ (u : ℝ≥0∞)} :=
    measurableSet_le
      ((Regeneration.measurable_regenerationTime Δ lam R i m).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))) measurable_const
  exact Measurable.ite hcond hGΦ measurable_const

theorem boundedRealTest_PhiM {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (D : (Regeneration.FutureHalfSpace d i R → Mat d × ℝ) →
      C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ))
    (G : FieldPair d → ℝ) (hG : Regeneration.BoundedRealTest G) (m : ℕ) (u : ℝ≥0) :
    Regeneration.BoundedRealTest (PhiM Δ lam R i D G m u) := by
  classical
  obtain ⟨C, hC⟩ := hG
  refine ⟨max C 0, fun y => ?_⟩
  unfold PhiM
  split_ifs
  · exact (hC _).trans (le_max_left _ _)
  · simpa only [abs_zero] using le_max_right C 0

/-- The observation at the record equals the reduced observation at the shifted time. -/
theorem observation_record_eq {d : ℕ} (Δ : ℝ≥0) (R ρ : ℝ) (i : Fin d)
    (D : (Regeneration.FutureHalfSpace d i R → Mat d × ℝ) →
      C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ))
    (hDr : ∀ f : C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ), D (fun x => f x) = f)
    (G : FieldPair d → ℝ)
    (hG : @Measurable (FieldPair d) ℝ (localSigma {x : Vec d | euclideanNorm x < ρ})
      inferInstance G)
    (ω : FieldPair d) (z : CoupledSample d) (a u : ℝ≥0)
    (hv : ∀ x : Vec d, euclideanNorm x < ρ → -2 * R ≤ (z.1 (a + u) - z.1 a + x) i) :
    G (translate ((Regeneration.futureRecord Δ R ω z i a).1 u)
        (extendFromHalfSpace i R (D (Regeneration.futureRecord Δ R ω z i a).2.2))) =
      G (translate (z.1 (a + u)) (reduce ω)) := by
  have hD : D (Regeneration.futureRecord Δ R ω z i a).2.2 =
      restrictHalfSpace i R (translate (z.1 a) (reduce ω)) :=
    hDr (restrictHalfSpace i R (translate (z.1 a) (reduce ω)))
  rw [hD]
  show G (translate (z.1 (a + u) - z.1 a)
      (extendFromHalfSpace i R (restrictHalfSpace i R (translate (z.1 a) (reduce ω))))) =
    G (translate (z.1 (a + u)) (reduce ω))
  have hloc : G (translate (z.1 (a + u) - z.1 a)
      (extendFromHalfSpace i R (restrictHalfSpace i R (translate (z.1 a) (reduce ω))))) =
      G (translate (z.1 (a + u) - z.1 a) (translate (z.1 a) (reduce ω))) :=
    eq_of_measurable_localSigma hG fun x hx =>
      translate_extend_eq_of_mem i R (translate (z.1 a) (reduce ω)) _ x (hv x hx)
  rw [hloc, translate_add, sub_add_cancel]

/-- After `m ≥ 1` regeneration cycles the path is far enough in the force direction. -/
theorem support_after_regen {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam)
    (hR : 0 < R) (i : Fin d) (hs : SliceChar Δ lam R i) (m : ℕ) (hm : 1 ≤ m) (ρ : ℝ)
    (hρ : ρ ≤ (10 * (m : ℝ) + 1) * R) (w : CoupledSample d)
    (hgain : ∀ n : ℕ, w.2 n = true →
      w.1 ((n : ℝ≥0) * Δ) i + 8 * R ≤ w.1 (((n + 1 : ℕ) : ℝ≥0) * Δ) i)
    (u : ℝ≥0) (hu : Regeneration.regenerationTime Δ lam R w i m ≤ (u : ℝ≥0∞)) :
    ∀ x : Vec d, euclideanNorm x < ρ → -2 * R ≤ (w.1 u - w.1 0 + x) i := by
  intro x hx
  have hfin : Regeneration.regenerationTime Δ lam R w i m ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hu
  have hpos := position_after_regen Δ hΔ lam R hlam hR i hs m w hgain hfin
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hNB := Regeneration.regenerationTime_succ_noBacktracking Δ hΔ lam R w i j hfin
  set a := (Regeneration.regenerationTime Δ lam R w i (j + 1)).toNNReal with ha
  have hau : a ≤ u := by
    have h1 : Regeneration.regenerationTime Δ lam R w i (j + 1) = (a : ℝ≥0∞) :=
      (ENNReal.coe_toNNReal hfin).symm
    rw [h1] at hu
    exact ENNReal.coe_le_coe.mp hu
  have hgt := coord_gt_of_noBacktracking w.1 i R a (u - a) hNB
  rw [add_tsub_cancel_of_le hau] at hgt
  have hxi : |x i| < ρ := lt_of_le_of_lt (Regeneration.coordinate_abs_le_euclideanNorm x i) hx
  have hxi' := (abs_lt.mp hxi).1
  rw [Pi.add_apply, Pi.sub_apply]
  push_cast at hpos hρ
  linarith

end EinsteinFull.Blueprint
