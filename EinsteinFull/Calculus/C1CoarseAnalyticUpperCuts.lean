import EinsteinFull.External.Source.AKMCoarsenedObjects
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM
theorem coarse_analytic_upperCuts_aestronglyMeasurable :
∀ {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (J : X → ℝ),
    (∀ t : ℝ, AnalyticSet {x | t < J x}) → AEStronglyMeasurable J μ := by
  intro X _ _ _ μ _ J hJ
  have hnull {s : Set X} (hs : AnalyticSet s) : NullMeasurableSet s μ := by
    classical
    have hSouslin (P : List ℕ → Set X) (hP : ∀ t, MeasurableSet (P t)) :
        NullMeasurableSet {x : X | ∃ b : ℕ → ℕ,
          ∀ n : ℕ, x ∈ P (List.ofFn (fun i : Fin n => b i))} μ := by
      classical
      let pref (b : ℕ → ℕ) (n : ℕ) := List.ofFn (fun i : Fin n => b i)
      have hpref (b : ℕ → ℕ) (n : ℕ) : pref b (n + 1) = (pref b n).concat (b n) := by
        simp only [pref, List.ofFn_succ', Fin.val_castSucc, Fin.val_last]
      let A (s : List ℕ) : Set X := {x | ∃ b : ℕ → ℕ,
        (∀ n, x ∈ P (pref b n)) ∧ pref b s.length = s}
      have hsub (s : List ℕ) : A s ⊆ P s := by
        rintro x ⟨b, hb, hs⟩
        simpa only [hs] using hb s.length
      have hsplit (s : List ℕ) : A s = ⋃ i : ℕ, A (s.concat i) := by
        ext x
        constructor
        · rintro ⟨b, hb, hs⟩
          apply Set.mem_iUnion.mpr
          refine ⟨b s.length, b, hb, ?_⟩
          simp only [List.length_concat, hpref, hs]
        · intro hx
          rcases Set.mem_iUnion.mp hx with ⟨i, b, hb, hs⟩
          refine ⟨b, hb, ?_⟩
          simp only [List.length_concat, hpref] at hs
          simpa only [List.concat_eq_append, List.dropLast_concat] using congrArg List.dropLast hs
      let H (s : List ℕ) := toMeasurable μ (A s)
      have henv {s t : Set X} (ht : MeasurableSet t) (hst : s ⊆ t) :
          μ (toMeasurable μ s \ t) = 0 := by
        rw [Set.sdiff_eq, μ.measure_toMeasurable_inter ht.compl (measure_ne_top μ s)]
        rw [← Set.sdiff_eq, Set.sdiff_eq_empty.mpr hst, measure_empty]
      have hgood : ∀ᵐ x ∂μ, ∀ s : List ℕ,
          (x ∈ H s → x ∈ P s) ∧ (x ∈ H s → x ∈ ⋃ i : ℕ, H (s.concat i)) := by
        apply ae_all_iff.mpr
        intro s
        have h1 : μ (H s \ P s) = 0 := henv (hP s) (hsub s)
        have h2 : μ (H s \ ⋃ i : ℕ, H (s.concat i)) = 0 := by
          apply henv (MeasurableSet.iUnion (fun i => measurableSet_toMeasurable μ (A (s.concat i))))
          rw [hsplit s]
          exact Set.iUnion_mono (fun i => subset_toMeasurable μ (A (s.concat i)))
        exact (ae_le_set.mpr h1).and (ae_le_set.mpr h2)
      have heq : H [] =ᵐ[μ] A [] := by
        filter_upwards [hgood] with x hx
        apply propext
        constructor
        · intro hx0
          have hstep (s : List ℕ) (hs : x ∈ H s) : ∃ i, x ∈ H (s.concat i) :=
            Set.mem_iUnion.mp ((hx s).2 hs)
          let next (s : List ℕ) := if hs : x ∈ H s then (hstep s hs).choose else 0
          have hnext (s : List ℕ) (hs : x ∈ H s) : x ∈ H (s.concat (next s)) := by
            dsimp only [next]
            rw [dite_eq_left hs]
            exact (hstep s hs).choose_spec
          let path : ℕ → List ℕ := Nat.rec [] (fun _ s => s.concat (next s))
          have hpath (n : ℕ) : x ∈ H (path n) := by
            induction n with
            | zero => exact hx0
            | succ n ih => exact hnext (path n) ih
          let b (n : ℕ) := next (path n)
          have hb (n : ℕ) : pref b n = path n := by
            induction n with
            | zero => rfl
            | succ n ih => rw [hpref, ih]
          refine ⟨b, ?_, ?_⟩
          · intro n
            rw [hb]
            exact (hx (path n)).1 (hpath n)
          · simp only [List.length_nil, pref, List.ofFn_zero]
        · exact fun ha => subset_toMeasurable μ (A []) ha
      have hn : NullMeasurableSet (A []) μ :=
        (measurableSet_toMeasurable μ (A [])).nullMeasurableSet.congr heq
      simpa only [A, List.length_nil, pref, List.ofFn_zero, and_true] using hn
    have hrange (f : (ℕ → ℕ) → X) (hf : Continuous f) :
        ∃ P : List ℕ → Set X, (∀ t, IsClosed (P t)) ∧
          Set.range f = {x | ∃ b : ℕ → ℕ,
            ∀ n : ℕ, x ∈ P (List.ofFn (fun i : Fin n => b i))} := by
      classical
      let pref (b : ℕ → ℕ) (n : ℕ) := List.ofFn (fun i : Fin n => b i)
      let C (s : List ℕ) : Set (ℕ → ℕ) := {z | pref z s.length = s}
      let P (s : List ℕ) : Set X := closure (f '' C s)
      refine ⟨P, fun _ => isClosed_closure, ?_⟩
      ext x
      constructor
      · rintro ⟨b, rfl⟩
        refine ⟨b, fun n => subset_closure ?_⟩
        refine ⟨b, ?_, rfl⟩
        simp only [C, Set.mem_ofPred_eq, pref, List.length_ofFn, Fin.val_cast]
      · rintro ⟨b, hb⟩
        have hz (n : ℕ) : ∃ z : ℕ → ℕ,
            pref z n = pref b n ∧ dist x (f z) < 1 / ((n : ℝ) + 1) := by
          obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp (hb n)
            (1 / ((n : ℝ) + 1)) (by positivity)
          refine ⟨z, ?_, hy⟩
          simpa only [C, Set.mem_ofPred_eq, pref, List.length_ofFn, Fin.val_cast] using hz
        choose z hp hd using hz
        have hzb : Filter.Tendsto z Filter.atTop (nhds b) := by
          apply tendsto_pi_nhds.mpr
          intro i
          apply tendsto_const_nhds.congr'
          filter_upwards [Filter.eventually_gt_atTop i] with n hn
          have he := List.ofFn_injective (hp n)
          exact (congrFun he (⟨i, hn⟩ : Fin n)).symm
        have hzx : Filter.Tendsto (fun n => f (z n)) Filter.atTop (nhds x) := by
          apply tendsto_iff_dist_tendsto_zero.mpr
          apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa only [dist_comm] using le_of_lt (hd n)
        exact ⟨b, tendsto_nhds_unique ((hf.tendsto b).comp hzb) hzx⟩
    rw [AnalyticSet] at hs
    rcases hs with hs | ⟨f, hf, rfl⟩
    · rw [hs]
      exact MeasurableSet.empty.nullMeasurableSet
    · obtain ⟨P, hP, heq⟩ := hrange f hf
      rw [heq]
      exact hSouslin P (fun t => (hP t).measurableSet)
  have hm : @Measurable (NullMeasurableSpace X μ) ℝ _ _ J :=
    measurable_of_Ioi (fun t => hnull (hJ t))
  exact (show NullMeasurable J μ from hm).aemeasurable.aestronglyMeasurable

end EinsteinFull.Blueprint
