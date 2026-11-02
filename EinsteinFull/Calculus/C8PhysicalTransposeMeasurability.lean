import EinsteinFull.Calculus.C3PhysicalBilinearTranspose
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.Compactness.Lindelof
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- Bilinear physical duality transfers measurable actions to the transpose. -/
theorem physical_bilinear_transpose_action_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P T : Ω → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      StronglyMeasurable (fun ω => P ω f))
    (hdual : ∀ (ω : Ω) (f g : Lp ℂ 2 (volume : Measure (Vec d))),
      (∫ x : Vec d, (P ω f) x * g x) = ∫ x : Vec d, f x * (T ω g) x) :
    ∀ g : Lp ℂ 2 (volume : Measure (Vec d)),
      StronglyMeasurable (fun ω => T ω g) := by
  classical
  let E : Type := Lp ℂ 2 (volume : Measure (Vec d))
  have hbilin (f g : E) :
      (∫ x : Vec d, f x * g x) = inner ℂ (star g) f := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star g] with x hx
    simp only [hx, Pi.star_apply, RCLike.inner_apply, starRingEnd_apply, star_star]
  have hbilin' (f g : E) :
      (∫ x : Vec d, f x * g x) = inner ℂ (star f) g := by
    rw [← hbilin]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology E := Lp.SecondCountableTopology
  intro g
  have hcoord (f : E) : StronglyMeasurable (fun ω => inner ℂ f (T ω g)) := by
    have he (ω : Ω) : inner ℂ f (T ω g) = inner ℂ (star g) (P ω (star f)) := by
      calc
        inner ℂ f (T ω g) = ∫ x : Vec d, (star f) x * (T ω g) x := by
          rw [hbilin', star_star]
        _ = ∫ x : Vec d, (P ω (star f)) x * g x := (hdual ω (star f) g).symm
        _ = inner ℂ (star g) (P ω (star f)) := hbilin _ _
    simp_rw [he]
    exact stronglyMeasurable_const.inner (hP (star f))
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ E
  let : DiscreteTopology w := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro i
    have he : {j : w | inner ℂ (b i) (b j) ≠ 0} = {i} := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      by_cases hij : i = j
      · subst j
        rw [orthonormal_iff_ite.mp b.orthonormal i i]
        norm_num
      · simp only [b.orthonormal.inner_eq_zero hij, ne_self_iff_false,
          eq_false_intro (Ne.symm hij)]
    rw [← he]
    exact isOpen_ne.preimage
      (continuous_const.inner (by simpa only [hb] using continuous_subtype_val))
  let : Countable w := countable_of_Lindelof_of_discrete
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset w))
      (f := fun s ω => ∑ j ∈ s, b.repr (T ω g) j • b j)
  · intro s
    apply Finset.stronglyMeasurable_fun_sum
    intro j _
    simpa only [b.repr_apply_apply] using (hcoord (b j)).smul_const (b j)
  · rw [tendsto_pi_nhds]
    intro ω
    exact b.hasSum_repr (T ω g)
end EinsteinFull.Blueprint
