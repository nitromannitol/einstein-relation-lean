import EinsteinRelation.External.GantertSection7Support
import EinsteinRelation.Probability.ContinuousFieldDecoder
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

/-!
# Deterministic-time future laws of the actual GMP realization

Ordered finite-dimensional laws determine finite measures on the literal
continuous-path carrier. Applying that reconstruction to the supplied GMP
finite-dimensional laws identifies the complete shifted future law, and the
future law restricted by every finite ordered past cylinder, with the actual
path-law mixture against the corresponding endpoint distribution. Both
identities hold at every spatial starting point.

This is a predecessor for the environmental/regeneration factorization chain.
Extension to the full past sigma-algebra, the exit-killed semigroup law and
identification with the variational interior evolution remain obligations.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull
open EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
noncomputable section

private theorem continuous_listGetD {E : Type*} [TopologicalSpace E] (e : E) (n : ℕ) :
    Continuous (fun z : List E => z.getD n e) := by
  apply continuous_iff_continuousAt.mpr
  induction n with
  | zero =>
    apply List.tendsto_nhds
    · exact tendsto_pure_nhds _ _
    · intro l a _
      simpa only [List.getD_cons_zero] using
        (tendsto_fst : Tendsto (fun p : E × List E => p.1) (𝓝 a ×ˢ 𝓝 l) (𝓝 a))
  | succ n ih =>
    apply List.tendsto_nhds
    · exact tendsto_pure_nhds _ _
    · intro l a _
      have h : Tendsto (fun p : E × List E => p.2.getD n e) (𝓝 a ×ˢ 𝓝 l)
          (𝓝 (l.getD n e)) := Filter.Tendsto.comp (ih l) tendsto_snd
      simpa only [List.getD_cons_succ] using h

/-- The accumulated times based at s are the original times translated by s. -/
theorem cumulativeTimesFrom_eq_map_add (s : ℝ≥0) (inc : List ℝ≥0) :
    cumulativeTimesFrom s inc = (cumulativeTimes inc).map (s + ·) := by
  have h (a b : ℝ≥0) (ts : List ℝ≥0) :
      cumulativeTimesFrom (a + b) ts = (cumulativeTimesFrom b ts).map (a + ·) := by
    induction ts generalizing b with
    | nil => rfl
    | cons t ts ih =>
      simp only [cumulativeTimesFrom, List.map_cons]
      rw [add_assoc, ih]
  simpa only [add_zero, cumulativeTimes] using h s 0 inc

private theorem exists_increments_from (s : ℝ≥0) (ts : List ℝ≥0)
    (hs : ∀ t ∈ ts, s ≤ t) (ht : ts.Pairwise (· ≤ ·)) :
    ∃ inc, cumulativeTimesFrom s inc = ts := by
  induction ts generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons t ts ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp ht
    obtain ⟨inc, hi⟩ := ih t hhead htail
    refine ⟨(t - s) :: inc, ?_⟩
    simpa only [cumulativeTimesFrom, add_tsub_cancel_of_le (hs t (List.mem_cons_self))] using
      congrArg (t :: ·) hi

/-- Every finite nondecreasing time list is represented by genuine nonnegative increments. -/
theorem exists_cumulativeTimes_eq (ts : List ℝ≥0) (ht : ts.Pairwise (· ≤ ·)) :
    ∃ inc, cumulativeTimes inc = ts :=
  exists_increments_from 0 ts (fun _ _ => zero_le) ht

private theorem measure_eq_of_bounded_integrals {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : E → ℝ), Measurable f → (∃ B : ℝ, ∀ x, |f x| ≤ B) →
      ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  apply Measure.ext
  intro A hA
  apply (measureReal_eq_measureReal_iff (measure_ne_top μ A) (measure_ne_top ν A)).mp
  have hi := h (A.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hA)
    ⟨1, fun x => by by_cases hx : x ∈ A <;> simp [hx]⟩
  simpa only [integral_indicator hA, integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ] using hi

/-- Finite continuous-path laws are determined by bounded tests of ordered observations. -/
theorem pathMeasure_eq_of_ordered_cylinder_integrals {d : ℕ}
    (μ ν : Measure (Path d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (inc : List ℝ≥0) (F : List (Vec d) → ℝ), Measurable F →
      (∃ B : ℝ, ∀ z, |F z| ≤ B) →
      (∫ γ, F (pathPositionsAtTimes (cumulativeTimes inc) γ) ∂μ) =
        ∫ γ, F (pathPositionsAtTimes (cumulativeTimes inc) γ) ∂ν) : μ = ν := by
  classical
  have hmap (inc : List ℝ≥0) :
      μ.map (pathPositionsAtTimes (cumulativeTimes inc)) =
        ν.map (pathPositionsAtTimes (cumulativeTimes inc)) := by
    apply measure_eq_of_bounded_integrals
    intro F hF hB
    simpa only [integral_map (measurable_pathPositionsAtTimes _).aemeasurable
      hF.aestronglyMeasurable] using h inc F hF hB
  let raw : Path d → ℝ≥0 → Vec d := fun γ t => γ t
  have hm : Measurable raw := Measurable.of_eval measurable_pathPosition
  have hfin (I : Finset ℝ≥0) :
      μ.map (fun γ => I.restrict (raw γ)) = ν.map (fun γ => I.restrict (raw γ)) := by
    let ts := I.sort (· ≤ ·)
    obtain ⟨inc, hi⟩ := exists_cumulativeTimes_eq ts (I.pairwise_sort _)
    let read : List (Vec d) → I → Vec d := fun z t => z.getD (ts.idxOf t.val) 0
    have hr : Measurable read := Measurable.of_eval fun t =>
      (continuous_listGetD (0 : Vec d) (ts.idxOf t.val)).measurable
    have he : read ∘ pathPositionsAtTimes ts = fun γ => I.restrict (raw γ) := by
      funext γ t
      change (ts.map (fun r => γ r)).getD (ts.idxOf t.val) 0 = γ t.val
      have ht : t.val ∈ ts := (Finset.mem_sort _).mpr t.property
      have hb : ts.idxOf t.val < (ts.map (fun r => γ r)).length := by
        simpa only [List.length_map] using List.idxOf_lt_length_iff.mpr ht
      rw [List.getD_eq_getElem _ _ hb, List.getElem_map,
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr ht)]
    have hh := congrArg (Measure.map read) (hmap inc)
    rw [hi, Measure.map_map hr (measurable_pathPositionsAtTimes ts),
      Measure.map_map hr (measurable_pathPositionsAtTimes ts), he] at hh
    exact hh
  have heq : μ.map raw = ν.map raw := by
    have hμ := isProjectiveLimit_map hm.aemeasurable (P := μ)
    have hν := isProjectiveLimit_map hm.aemeasurable (P := ν)
    have hμ' : IsProjectiveLimit (μ.map raw)
        (fun I => ν.map (fun γ => I.restrict (raw γ))) :=
      fun I => (hμ I).trans (hfin I)
    exact hμ'.unique hν
  haveI : PolishSpace (Path d) := by
    haveI : CompleteSpace (Path d) := inferInstance
    haveI : Filter.IsCountablyGenerated (uniformity (Path d)) := inferInstance
    haveI : SecondCountableTopology (Path d) := inferInstance
    infer_instance
  obtain ⟨D, hD, hdecode⟩ :=
    EinsteinRelation.Probability.exists_measurable_continuousMap_decoder (X := ℝ≥0) (E := Vec d)
  have hc : D ∘ raw = id := funext hdecode
  have hh := congrArg (Measure.map D) heq
  simpa only [Measure.map_map hD hm, hc, Measure.map_id] using hh

/-- A continuous path shifted to the displayed deterministic time. -/
def gmpShiftPath {d : ℕ} (s : ℝ≥0) (γ : Path d) : Path d :=
  ⟨fun t => γ (s + t), γ.continuous.comp (continuous_const.add continuous_id)⟩

/-- Time shift is measurable on the actual continuous-path carrier. -/
theorem measurable_gmpShiftPath {d : ℕ} (s : ℝ≥0) :
    Measurable (gmpShiftPath (d := d) s) := by
  apply Continuous.measurable
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_fst.eval (continuous_const.add continuous_snd)

private theorem continuous_listTake {E : Type*} [TopologicalSpace E] (n : ℕ) :
    Continuous (fun z : List E => z.take n) := by
  apply continuous_iff_continuousAt.mpr
  induction n with
  | zero => exact fun _ => continuousAt_const
  | succ n ih =>
    apply List.tendsto_nhds
    · exact tendsto_pure_nhds _ _
    · intro l a _
      have h : Tendsto (fun p : E × List E => p.1 :: List.take n p.2) (𝓝 a ×ˢ 𝓝 l)
          (𝓝 (a :: List.take n l)) :=
        tendsto_fst.cons (Filter.Tendsto.comp (ih l) tendsto_snd)
      simpa only [List.take_succ_cons] using h

private theorem continuous_listDrop {E : Type*} [TopologicalSpace E] (n : ℕ) :
    Continuous (fun z : List E => z.drop n) := by
  apply continuous_iff_continuousAt.mpr
  induction n with
  | zero => exact fun _ => continuousAt_id
  | succ n ih =>
    apply List.tendsto_nhds
    · exact tendsto_pure_nhds _ _
    · intro l a _
      have h : Tendsto (fun p : E × List E => List.drop n p.2) (𝓝 a ×ˢ 𝓝 l)
          (𝓝 (List.drop n l)) := Filter.Tendsto.comp (ih l) tendsto_snd
      simpa only [List.drop_succ_cons] using h

private theorem measurable_listGetLastD {d : ℕ} (x : Vec d) :
    Measurable (fun z : List (Vec d) => z.getLastD x) := by
  have hm : Measurable (fun p : List (Vec d) × ℕ => p.1.getD p.2 x) :=
    measurable_from_prod_countable_left fun n => (continuous_listGetD x n).measurable
  have hl : Measurable (fun z : List (Vec d) => z.length - 1) :=
    ((continuous_iff_continuousAt.mpr List.continuousAt_length).measurable).sub measurable_const
  have h : Measurable (fun z : List (Vec d) => z[z.length - 1]?.getD x) :=
    hm.comp (measurable_id.prodMk hl)
  simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
    List.getD_eq_getElem?_getD] using h

private theorem cumulativeTimesFrom_append (s : ℝ≥0) (pre post : List ℝ≥0) :
    cumulativeTimesFrom s (pre ++ post) =
      cumulativeTimesFrom s pre ++ cumulativeTimesFrom (s + pre.sum) post := by
  induction pre generalizing s with
  | nil => simp only [List.nil_append, cumulativeTimesFrom, List.sum_nil, add_zero]
  | cons t ts ih =>
    simp only [List.cons_append, cumulativeTimesFrom, List.sum_cons]
    rw [ih, add_assoc]

/-- Ordered observations of concatenated increments split at the actual elapsed time. -/
theorem pathPositionsAtTimes_cumulativeTimes_append {d : ℕ}
    (pre post : List ℝ≥0) (γ : Path d) :
    pathPositionsAtTimes (cumulativeTimes (pre ++ post)) γ =
      pathPositionsAtTimes (cumulativeTimes pre) γ ++
        pathPositionsAtTimes (cumulativeTimes post) (gmpShiftPath pre.sum γ) := by
  change (cumulativeTimesFrom 0 (pre ++ post)).map _ = _
  rw [cumulativeTimesFrom_append, List.map_append, zero_add,
    cumulativeTimesFrom_eq_map_add pre.sum post]
  simp only [List.map_map, pathPositionsAtTimes, cumulativeTimes]
  rfl

private theorem cumulativeTimesFrom_getLastD (s : ℝ≥0) (inc : List ℝ≥0) :
    (cumulativeTimesFrom s inc).getLastD s = s + inc.sum := by
  induction inc generalizing s with
  | nil => simp only [cumulativeTimesFrom, List.getLastD_nil, List.sum_nil, add_zero]
  | cons t ts ih =>
    rw [cumulativeTimesFrom, List.getLastD_cons, ih, List.sum_cons, add_assoc]

/-- The last ordered observation is the literal endpoint, using the actual initial value. -/
theorem pathPositionsAtTimes_cumulativeTimes_getLastD {d : ℕ}
    (inc : List ℝ≥0) (γ : Path d) :
    (pathPositionsAtTimes (cumulativeTimes inc) γ).getLastD (γ 0) = γ inc.sum := by
  change ((cumulativeTimesFrom 0 inc).map (fun t => γ t)).getLastD (γ 0) = _
  rw [List.getLastD_map, cumulativeTimesFrom_getLastD, zero_add]

private theorem iteratedMarkovCylinderIntegral_append {d : ℕ}
    (K : ℝ≥0 → Kernel (Vec d) (Vec d)) (pre post : List ℝ≥0)
    (Φ : List (Vec d) → List (Vec d) → ℝ) (x : Vec d) :
    iteratedMarkovCylinderIntegral K (pre ++ post)
      (fun z => Φ (z.take pre.length) (z.drop pre.length)) x =
      iteratedMarkovCylinderIntegral K pre
        (fun ys => iteratedMarkovCylinderIntegral K post (Φ ys) (ys.getLastD x)) x := by
  induction pre generalizing Φ x with
  | nil => simp only [List.nil_append, List.length_nil, List.take_zero, List.drop_zero,
      iteratedMarkovCylinderIntegral, List.getLastD_nil]
  | cons t ts ih =>
    simp only [List.cons_append, List.length_cons, iteratedMarkovCylinderIntegral,
      List.take_succ_cons, List.drop_succ_cons, List.getLastD_cons]
    apply integral_congr_ae
    exact ae_of_all _ fun y => ih (fun ys zs => Φ (y :: ys) zs) y

private theorem iteratedMarkovCylinderIntegral_zero {d : ℕ}
    (K : ℝ≥0 → Kernel (Vec d) (Vec d)) (inc : List ℝ≥0) (x : Vec d) :
    iteratedMarkovCylinderIntegral K inc (fun _ => 0) x = 0 := by
  induction inc generalizing x with
  | nil => rfl
  | cons t ts ih =>
    simp only [iteratedMarkovCylinderIntegral, ih, integral_zero]

private theorem cumulativeTimesFrom_length (s : ℝ≥0) (inc : List ℝ≥0) :
    (cumulativeTimesFrom s inc).length = inc.length := by
  induction inc generalizing s with
  | nil => rfl
  | cons t ts ih => simp only [cumulativeTimesFrom, List.length_cons, ih]

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)

/-- The complete future law at a deterministic time is the actual path law
mixed against the actual transition kernel, for every initial point. -/
theorem gmpPathLaw_map_shift (s : ℝ≥0) :
    G.pathLaw.map (gmpShiftPath s) = G.pathLaw ∘ₖ G.transitionKernel s := by
  letI := G.pathLaw_isMarkovKernel
  letI := G.transitionKernel_isMarkovKernel s
  apply Kernel.ext
  intro x
  rw [Kernel.map_apply _ (measurable_gmpShiftPath s)]
  apply pathMeasure_eq_of_ordered_cylinder_integrals
  intro inc F hF hB
  let H : Path d → ℝ := fun γ => F (pathPositionsAtTimes (cumulativeTimes inc) γ)
  have hH : Measurable H := hF.comp (measurable_pathPositionsAtTimes _)
  have hi : Integrable H ((G.pathLaw ∘ₖ G.transitionKernel s) x) := by
    obtain ⟨B, hB⟩ := hB
    exact (integrable_const B).mono' hH.aestronglyMeasurable
      (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using hB _)
  have htail : Measurable (fun z : List (Vec d) => F (z.eraseIdx 0)) :=
    hF.comp List.continuous_eraseIdx.measurable
  have hobs (γ : Path d) :
      (pathPositionsAtTimes (cumulativeTimes (s :: inc)) γ).eraseIdx 0 =
        pathPositionsAtTimes (cumulativeTimes inc) (gmpShiftPath s γ) := by
    change (pathPositionsAtTimes (cumulativeTimesFrom 0 (s :: inc)) γ).eraseIdx 0 = _
    rw [cumulativeTimesFrom]
    simp only [zero_add, pathPositionsAtTimes, List.map_cons, List.eraseIdx_zero, List.tail_cons]
    rw [cumulativeTimesFrom_eq_map_add]
    simp only [List.map_map]
    rfl
  have h := G.pathLaw_ordered_finite_dimensional (s :: inc) x
    (fun z => F (z.eraseIdx 0)) htail ⟨hB.choose, fun z => hB.choose_spec _⟩
  rw [integral_map (measurable_gmpShiftPath s).aemeasurable
    hH.aestronglyMeasurable]
  change (∫ γ, H (gmpShiftPath s γ) ∂G.pathLaw x) =
    ∫ γ, H γ ∂(G.pathLaw ∘ₖ G.transitionKernel s) x
  rw [Kernel.integral_comp hi]
  change (∫ γ, F (pathPositionsAtTimes (cumulativeTimes inc) (gmpShiftPath s γ))
    ∂G.pathLaw x) = _
  simp_rw [← hobs]
  rw [h]
  simp only [iteratedMarkovCylinderIntegral, List.eraseIdx_zero, List.tail_cons]
  apply integral_congr_ae
  exact ae_of_all _ fun y =>
    (G.pathLaw_ordered_finite_dimensional inc y F hF hB).symm

/-- The actual path kernel restricted to the displayed finite past cylinder. -/
def gmpPastCylinderKernel (pre : List ℝ≥0) (A : Set (List (Vec d)))
    (hA : MeasurableSet A) : Kernel (Vec d) (Path d) :=
  G.pathLaw.restrict (hA.preimage (measurable_pathPositionsAtTimes (cumulativeTimes pre)))

/-- Restricting the actual probability law to a finite past event gives a finite kernel. -/
theorem isFiniteKernel_gmpPastCylinderKernel (pre : List ℝ≥0)
    (A : Set (List (Vec d))) (hA : MeasurableSet A) :
    IsFiniteKernel (gmpPastCylinderKernel G pre A hA) := by
  letI := G.pathLaw_isMarkovKernel
  unfold gmpPastCylinderKernel
  infer_instance

/-- Complete deterministic future restart under every finite ordered past cylinder,
with the actual restricted endpoint distribution and every starting point. -/
theorem gmpPastCylinderKernel_map_shift (pre : List ℝ≥0)
    (A : Set (List (Vec d))) (hA : MeasurableSet A) :
    (gmpPastCylinderKernel G pre A hA).map (gmpShiftPath pre.sum) =
      G.pathLaw ∘ₖ ((gmpPastCylinderKernel G pre A hA).map (pathPosition pre.sum)) := by
  classical
  letI := G.pathLaw_isMarkovKernel
  letI := isFiniteKernel_gmpPastCylinderKernel G pre A hA
  let κ := gmpPastCylinderKernel G pre A hA
  let past : Path d → List (Vec d) := pathPositionsAtTimes (cumulativeTimes pre)
  let E : Set (Path d) := past ⁻¹' A
  have hE : MeasurableSet E := hA.preimage (measurable_pathPositionsAtTimes _)
  have hκ (x : Vec d) : κ x = (G.pathLaw x).restrict E := rfl
  apply Kernel.ext
  intro x
  rw [Kernel.map_apply _ (measurable_gmpShiftPath _)]
  apply pathMeasure_eq_of_ordered_cylinder_integrals
  intro inc F hF hbound
  obtain ⟨B, hB⟩ := hbound
  let H : Path d → ℝ := fun γ => F (pathPositionsAtTimes (cumulativeTimes inc) γ)
  have hH : Measurable H := hF.comp (measurable_pathPositionsAtTimes _)
  let J : Vec d → ℝ := fun y => ∫ γ, H γ ∂G.pathLaw y
  have hJ : Measurable J := hH.stronglyMeasurable.integral_kernel.measurable
  have hJB (y : Vec d) : |J y| ≤ B := by
    have hi := norm_integral_le_of_norm_le_const
      (μ := G.pathLaw y) (f := H) (ae_of_all _ fun γ => by
        simpa only [Real.norm_eq_abs] using hB (pathPositionsAtTimes (cumulativeTimes inc) γ))
    simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using hi
  let Φ : List (Vec d) → List (Vec d) → ℝ := fun ys zs => if ys ∈ A then F zs else 0
  let C : List (Vec d) → ℝ := fun z => Φ (z.take pre.length) (z.drop pre.length)
  have hC : Measurable C := Measurable.ite
    (hA.preimage (continuous_listTake _).measurable)
    (hF.comp (continuous_listDrop _).measurable) measurable_const
  have hCB : ∀ z, |C z| ≤ max B 0 := by
    intro z
    dsimp only [C, Φ]
    split_ifs
    · exact (hB _).trans (le_max_left _ _)
    · exact (by simp only [abs_zero]; exact le_max_right _ _)
  let P : List (Vec d) → ℝ := fun ys => if ys ∈ A then J (ys.getLastD x) else 0
  have hP : Measurable P := Measurable.ite hA
    (hJ.comp (measurable_listGetLastD x)) measurable_const
  have hPB : ∀ ys, |P ys| ≤ max B 0 := by
    intro ys
    dsimp only [P]
    split_ifs
    · exact (hJB _).trans (le_max_left _ _)
    · exact (by simp only [abs_zero]; exact le_max_right _ _)
  have hobs (γ : Path d) :
      C (pathPositionsAtTimes (cumulativeTimes (pre ++ inc)) γ) =
        if past γ ∈ A then H (gmpShiftPath pre.sum γ) else 0 := by
    have hlen : (past γ).length = pre.length := by
      change ((cumulativeTimesFrom 0 pre).map _).length = _
      rw [List.length_map, cumulativeTimesFrom_length]
    change Φ ((pathPositionsAtTimes (cumulativeTimes (pre ++ inc)) γ).take pre.length)
      ((pathPositionsAtTimes (cumulativeTimes (pre ++ inc)) γ).drop pre.length) = _
    rw [pathPositionsAtTimes_cumulativeTimes_append, ← hlen, List.take_left, List.drop_left]
  have hleft : (∫ γ, H γ ∂(κ x).map (gmpShiftPath pre.sum)) =
      ∫ γ, C (pathPositionsAtTimes (cumulativeTimes (pre ++ inc)) γ) ∂G.pathLaw x := by
    rw [integral_map (measurable_gmpShiftPath _).aemeasurable hH.aestronglyMeasurable,
      hκ, ← integral_indicator hE]
    apply integral_congr_ae
    exact ae_of_all _ fun γ => (hobs γ).symm
  have hi : Integrable H
      ((G.pathLaw ∘ₖ (κ.map (pathPosition pre.sum))) x) :=
    (integrable_const B).mono' hH.aestronglyMeasurable
      (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using hB _)
  have hright : (∫ γ, H γ ∂(G.pathLaw ∘ₖ (κ.map (pathPosition pre.sum))) x) =
      ∫ γ, P (past γ) ∂G.pathLaw x := by
    rw [Kernel.integral_comp hi, Kernel.map_apply _ (measurable_pathPosition _),
      integral_map (measurable_pathPosition _).aemeasurable hJ.aestronglyMeasurable,
      hκ, ← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [G.pathLaw_starts_at x] with γ hstart
    have hend : (past γ).getLastD x = γ pre.sum := by
      rw [← hstart]
      exact pathPositionsAtTimes_cumulativeTimes_getLastD pre γ
    change (if past γ ∈ A then J (γ pre.sum) else 0) = P (past γ)
    simp only [P, hend]
  change (∫ γ, H γ ∂(κ x).map (gmpShiftPath pre.sum)) =
    ∫ γ, H γ ∂(G.pathLaw ∘ₖ (κ.map (pathPosition pre.sum))) x
  rw [hleft, hright, G.pathLaw_ordered_finite_dimensional (pre ++ inc) x C hC ⟨_, hCB⟩,
    G.pathLaw_ordered_finite_dimensional pre x P hP ⟨_, hPB⟩]
  change iteratedMarkovCylinderIntegral G.transitionKernel (pre ++ inc)
    (fun z => Φ (z.take pre.length) (z.drop pre.length)) x = _
  rw [iteratedMarkovCylinderIntegral_append]
  congr 1
  funext ys
  change iteratedMarkovCylinderIntegral G.transitionKernel inc
    (fun zs => if ys ∈ A then F zs else 0) (ys.getLastD x) = P ys
  by_cases hy : ys ∈ A
  · simp only [hy, ↓reduceIte, P]
    exact (G.pathLaw_ordered_finite_dimensional inc (ys.getLastD x) F hF ⟨_, hB⟩).symm
  · simp only [hy, ↓reduceIte, P]
    exact iteratedMarkovCylinderIntegral_zero _ _ _

end
end EinsteinFull
