import EinsteinRelation.Probability.LocalSigma
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Metrizable.Basic

/-! # Measurability of local integrals of the field

For a set `S` of points and a neighbourhood `W` of `S + U`, the translation
`(x, ω) ↦ translate x ω` is measurable from the product of `S` with the local σ-algebra of `W`
to the local σ-algebra of `U`. Consequently a cube integral `∫ x in S, k x * f (translate x ω)`
of a field observed on `U` is measurable for the local σ-algebra of `W`. The one-colour cube
integrals of `paper/main.tex:1159–1161` are independent by separation; this file supplies the
measurability of such integrals for the local σ-algebra of a neighbourhood of the cube.

Every σ-algebra on a field pair is written out explicitly with `@Measurable`, because
`Measurable` takes its σ-algebras by instance and the global Borel structure on `FieldPair d`
must not be picked up in place of `localSigma`.
-/

open MeasureTheory

namespace EinsteinRelation

/-- A translation whose shifted window `x + U` lies in `W` is measurable from the local
σ-algebra of `W` to the local σ-algebra of `U`. -/
theorem measurable_translate_localSigma {d : ℕ} {U W : Set (Vec d)} (x : Vec d)
    (hxUW : ∀ y ∈ U, x + y ∈ W) :
    @Measurable (FieldPair d) (FieldPair d) (localSigma W) (localSigma U) (translate x) := by
  have hsub : (fun y => x + y) '' U ⊆ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact hxUW y hy
  exact (Probability.measurable_translate_local x U).mono
    (Probability.localSigma_mono hsub) le_rfl

/-- Measurability into the local σ-algebra of `U` reduces to the coordinate pairs
`(F a).1 y`, `(F a).2 y` for `y ∈ U`. -/
private theorem measurable_localSigma_of_coordinates {d : ℕ} {α : Type*} {U : Set (Vec d)}
    {m : MeasurableSpace α} {F : α → FieldPair d}
    (h : ∀ y ∈ U, @Measurable α (Mat d × ℝ) m inferInstance
      (fun a => ((F a).1 y, (F a).2 y))) :
    @Measurable α (FieldPair d) m (localSigma U) F := by
  refine Measurable.of_comap_le ?_
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun y => ?_
  rw [MeasurableSpace.comap_comp]
  exact (h y.1 y.2).comap_le

/-- The coordinate pair `(ω.1 z, ω.2 z)` at a point `z ∈ W` is measurable for `localSigma W`. -/
private theorem measurable_pair_localSigma {d : ℕ} {W : Set (Vec d)} {z : Vec d} (hz : z ∈ W) :
    @Measurable (FieldPair d) (Mat d × ℝ) (localSigma W) inferInstance
      (fun ω => (ω.1 z, ω.2 z)) := by
  refine Measurable.of_comap_le ?_
  unfold localSigma
  exact le_iSup_of_le (⟨z, hz⟩ : ↥W) le_rfl

/-- For a fixed shift `y` and `x ∈ S`, the coefficient pair at the moving point `x + y` is jointly
measurable in `(x, ω)`: it is continuous in `x`, and measurable in `ω` for `localSigma W`. -/
private theorem measurable_fieldPair_eval_joint {d : ℕ} {S W : Set (Vec d)} (y : Vec d)
    (hy : ∀ x ∈ S, x + y ∈ W) :
    @Measurable (↥S × FieldPair d) (Mat d × ℝ)
      (@Prod.instMeasurableSpace ↥S (FieldPair d) _ (localSigma W)) inferInstance
      (fun p => (p.2.1 ((p.1 : Vec d) + y), p.2.2 ((p.1 : Vec d) + y))) := by
  have hMat : @Measurable (↥S × FieldPair d) (Mat d)
      (@Prod.instMeasurableSpace ↥S (FieldPair d) _ (localSigma W)) inferInstance
      (fun p => p.2.1 ((p.1 : Vec d) + y)) := by
    haveI : TopologicalSpace.PseudoMetrizableSpace (Mat d) :=
      inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
    have hcont : ∀ ω : FieldPair d, Continuous fun x : ↥S => ω.1 ((x : Vec d) + y) :=
      fun ω => ω.1.continuous.comp (continuous_subtype_val.add continuous_const)
    have hcoord : ∀ x : ↥S, @Measurable (FieldPair d) (Mat d) (localSigma W) inferInstance
        (fun ω => ω.1 ((x : Vec d) + y)) :=
      fun x => measurable_fst.comp (measurable_pair_localSigma (hy x.1 x.2))
    exact MeasureTheory.measurable_uncurry_of_continuous_of_measurable
      (u := fun (x : ↥S) (ω : FieldPair d) => ω.1 ((x : Vec d) + y)) hcont hcoord
  have hReal : @Measurable (↥S × FieldPair d) ℝ
      (@Prod.instMeasurableSpace ↥S (FieldPair d) _ (localSigma W)) inferInstance
      (fun p => p.2.2 ((p.1 : Vec d) + y)) := by
    have hcont : ∀ ω : FieldPair d, Continuous fun x : ↥S => ω.2 ((x : Vec d) + y) :=
      fun ω => ω.2.continuous.comp (continuous_subtype_val.add continuous_const)
    have hcoord : ∀ x : ↥S, @Measurable (FieldPair d) ℝ (localSigma W) inferInstance
        (fun ω => ω.2 ((x : Vec d) + y)) :=
      fun x => measurable_snd.comp (measurable_pair_localSigma (hy x.1 x.2))
    exact MeasureTheory.measurable_uncurry_of_continuous_of_measurable
      (u := fun (x : ↥S) (ω : FieldPair d) => ω.2 ((x : Vec d) + y)) hcont hcoord
  exact hMat.prodMk hReal

/-- The joint translation `(x, ω) ↦ translate x ω` is measurable from the product of the
subtype of `S` (with `localSigma W` on the field) to `localSigma U`, provided every shifted
point `x + y` with `x ∈ S` and `y ∈ U` lies in `W`. -/
theorem measurable_translate_joint {d : ℕ} {S U W : Set (Vec d)}
    (hSW : ∀ x ∈ S, ∀ y ∈ U, x + y ∈ W) :
    @Measurable (↥S × FieldPair d) (FieldPair d)
      (@Prod.instMeasurableSpace ↥S (FieldPair d) _ (localSigma W)) (localSigma U)
      (fun p => translate (p.1 : Vec d) p.2) :=
  measurable_localSigma_of_coordinates fun y hy =>
    measurable_fieldPair_eval_joint y fun x hx => hSW x hx y hy

/-- Integrating the first coordinate of a measurable function on `Vec d × β` gives a measurable
function of the second coordinate, for whatever σ-algebra `β` carries. -/
private theorem measurable_integral_fst {d : ℕ} {β : Type*} [mβ : MeasurableSpace β]
    {G : Vec d × β → ℝ} (hG : Measurable G) :
    Measurable fun ω : β => ∫ x, G (x, ω) :=
  (hG.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable

/-- A point of `S` gives a measurable selection `Vec d → ↥S` that is the identity on `S`. -/
private theorem exists_measurable_repair {d : ℕ} {S : Set (Vec d)} (hS : MeasurableSet S)
    {x0 : Vec d} (hx0 : x0 ∈ S) :
    ∃ rep : Vec d → ↥S, Measurable rep ∧ ∀ x ∈ S, ((rep x : ↥S) : Vec d) = x := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : Vec d → Vec d, ∀ x, r x = if x ∈ S then x else x0 :=
    ⟨fun x => if x ∈ S then x else x0, fun x => rfl⟩
  have hr_mem : ∀ x, r x ∈ S := by
    intro x
    rw [hr x]
    split_ifs with h
    · exact h
    · exact hx0
  have hr_id : ∀ x ∈ S, r x = x := fun x hx => by rw [hr x, if_pos hx]
  have hr_meas : Measurable r := by
    have hfun : r = fun x => if x ∈ S then x else x0 := funext hr
    rw [hfun]
    exact Measurable.ite (p := fun x => x ∈ S) hS measurable_id measurable_const
  exact ⟨fun x => ⟨r x, hr_mem x⟩, Measurable.subtype_mk hr_meas, fun x hx => hr_id x hx⟩

/-- A cube integral of a local field against a measurable test function is measurable for the
local σ-algebra of a neighbourhood `W` of the cube. Here `f` is measurable for the local
σ-algebra of `U`, and every shifted point `x + y` with `x ∈ S`, `y ∈ U` lies in `W`. -/
theorem measurable_localSigma_setIntegral_translate {d : ℕ} {S U W : Set (Vec d)}
    (hS : MeasurableSet S) (hSW : ∀ x ∈ S, ∀ y ∈ U, x + y ∈ W)
    (k : Vec d → ℝ) (hk : Measurable k)
    (f : FieldPair d → ℝ) (hf : @Measurable (FieldPair d) ℝ (localSigma U) inferInstance f) :
    @Measurable (FieldPair d) ℝ (localSigma W) inferInstance
      (fun ω => ∫ x in S, k x * f (translate x ω)) := by
  rcases S.eq_empty_or_nonempty with hS0 | ⟨x0, hx0⟩
  · subst hS0
    simp only [setIntegral_empty]
    exact measurable_const
  · obtain ⟨rep, hrep, hrep_id⟩ := exists_measurable_repair hS hx0
    have hpair : @Measurable (Vec d × FieldPair d) (↥S × FieldPair d)
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W))
        (@Prod.instMeasurableSpace ↥S (FieldPair d) _ (localSigma W))
        (fun q => (rep q.1, q.2)) :=
      (hrep.comp measurable_fst).prodMk measurable_snd
    have hT : @Measurable (Vec d × FieldPair d) (FieldPair d)
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) (localSigma U)
        (fun q => translate ((rep q.1 : ↥S) : Vec d) q.2) :=
      (measurable_translate_joint hSW).comp hpair
    have hk' : @Measurable (Vec d × FieldPair d) ℝ
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) inferInstance
        (fun q => S.indicator k q.1) :=
      (hk.indicator hS).comp measurable_fst
    have hf' : @Measurable (Vec d × FieldPair d) ℝ
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) inferInstance
        (fun q => f (translate ((rep q.1 : ↥S) : Vec d) q.2)) :=
      hf.comp hT
    have hG : @Measurable (Vec d × FieldPair d) ℝ
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) inferInstance
        (fun q => S.indicator k q.1 * f (translate ((rep q.1 : ↥S) : Vec d) q.2)) :=
      hk'.mul hf'
    have hfun : (fun ω : FieldPair d => ∫ x in S, k x * f (translate x ω)) =
        fun ω : FieldPair d => ∫ x, S.indicator k x * f (translate ((rep x : ↥S) : Vec d) ω) := by
      funext ω
      rw [← integral_indicator hS]
      congr 1
      funext x
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx, hrep_id x hx]
      · simp only [Set.indicator_of_notMem hx, zero_mul]
    rw [hfun]
    exact measurable_integral_fst (mβ := localSigma W) hG

end EinsteinRelation
