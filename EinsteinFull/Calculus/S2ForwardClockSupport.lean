import EinsteinFull.Calculus.S2ClockLeftInverseSupport
import EinsteinRelation.Sharpness.PhysicalRegularityMeasurability
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# The forward time change `X ↦ X ∘ A⁻¹` of a physical path

For a regular environment `ω`, the forward path map is the inverse-clock construction for the
sign-flipped potential, `γ ↦ γ ∘ (∫₀ᵗ exp (2 ω.2 (γ u)) du)⁻¹`.  It is a two-sided inverse of
`γ ↦ inverseClockPath ω γ`, measurable at fixed `ω`, and jointly measurable in `(ω, γ)` after
extension by the identity off the regular set.  Applied to a quenched path-law kernel at the
origin, it gives a kernel family whose origin laws are the forward images.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Clock EinsteinRelation.Clock.InverseMeaningV3

/-- The forward time change of a path at a regular environment. -/
def forwardClockPath {d : ℕ} {L : ℝ} {ω : FieldPair d} (hω : IsRegular L ω) (γ : Path d) :
    Path d :=
  inverseClockPath (flipPotential ω) γ L (isRegular_flipPotential hω)

theorem flipPotential_flipPotential {d : ℕ} (ω : FieldPair d) :
    flipPotential (flipPotential ω) = ω := by
  refine Prod.ext rfl (ContinuousMap.ext fun x => ?_)
  show -(-ω.2 x) = ω.2 x
  exact neg_neg _

theorem inverseClockPath_congr_field {d : ℕ} {L : ℝ} {ω₁ ω₂ : FieldPair d} (h : ω₁ = ω₂)
    (hω₁ : IsRegular L ω₁) (hω₂ : IsRegular L ω₂) (γ : Path d) :
    inverseClockPath ω₁ γ L hω₁ = inverseClockPath ω₂ γ L hω₂ := by
  subst h
  exact inverseClockPath_independent ω₁ γ hω₁ hω₂

theorem inverseClockPath_forwardClockPath {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hω : IsRegular L ω) (γ : Path d) :
    inverseClockPath ω (forwardClockPath hω γ) L hω = γ := by
  have h := inverseClockPath_flip_inverseClockPath (flipPotential ω) γ L
    (isRegular_flipPotential hω)
  calc inverseClockPath ω (forwardClockPath hω γ) L hω
      = inverseClockPath (flipPotential (flipPotential ω)) (forwardClockPath hω γ) L
          (isRegular_flipPotential (isRegular_flipPotential hω)) :=
        inverseClockPath_congr_field (flipPotential_flipPotential ω).symm hω _ _
    _ = γ := h

theorem forwardClockPath_inverseClockPath {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hω : IsRegular L ω) (γ : Path d) :
    forwardClockPath hω (inverseClockPath ω γ L hω) = γ :=
  inverseClockPath_flip_inverseClockPath ω γ L hω

theorem measurable_forwardClockPath {d : ℕ} {L : ℝ} {ω : FieldPair d} (hω : IsRegular L ω) :
    Measurable (forwardClockPath hω) :=
  measurable_inverseClockPath_fixed (flipPotential ω) L (isRegular_flipPotential hω)

theorem forwardClockPath_zero {d : ℕ} {L : ℝ} {ω : FieldPair d} (hω : IsRegular L ω)
    (γ : Path d) : forwardClockPath hω γ 0 = γ 0 :=
  inverseClockPath_zero (flipPotential ω) γ L (isRegular_flipPotential hω)

theorem measurable_flipPotential (d : ℕ) : Measurable (flipPotential (d := d)) :=
  (continuous_fst.prodMk continuous_snd.neg : Continuous fun ω : FieldPair d =>
    ((ω.1, -ω.2) : FieldPair d)).measurable

/-- The forward time change, extended by the identity off the regular set. -/
def forwardPathMap (d : ℕ) (L : ℝ) (z : FieldPair d × Path d) : Path d := by
  classical
  exact if h : IsRegular L z.1 then forwardClockPath h z.2 else z.2

theorem forwardPathMap_of_regular {d : ℕ} {L : ℝ} {ω : FieldPair d} (hω : IsRegular L ω)
    (γ : Path d) : forwardPathMap d L (ω, γ) = forwardClockPath hω γ := by
  unfold forwardPathMap
  rw [dif_pos hω]

theorem measurable_forwardPathMap (d : ℕ) (L : ℝ) : Measurable (forwardPathMap d L) := by
  classical
  have hs : MeasurableSet {z : FieldPair d × Path d | IsRegular L z.1} :=
    (Sharpness.measurableSet_isRegular_fieldPair (d := d) L).preimage measurable_fst
  have hf : Measurable (fun z : {z : FieldPair d × Path d | IsRegular L z.1} =>
      forwardClockPath (L := L) (ω := z.1.1) z.2 z.1.2) := by
    have hphys : Measurable (fun z : {z : FieldPair d × Path d | IsRegular L z.1} =>
        (⟨flipPotential z.1.1, isRegular_flipPotential z.2⟩ :
          Clock.PathMapV4.PhysicalInput d L)) :=
      Measurable.subtype_mk ((measurable_flipPotential d).comp
        (measurable_fst.comp measurable_subtype_coe))
    exact (Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := L)).comp
      (hphys.prodMk (measurable_snd.comp measurable_subtype_coe))
  have hg : Measurable (fun z : ({z : FieldPair d × Path d | IsRegular L z.1}ᶜ : Set _) => z.1.2) :=
    measurable_snd.comp measurable_subtype_coe
  exact Measurable.dite hf hg hs

/-- A kernel family whose origin laws are the forward images of those of `κ` (where `κ` has
probability origin laws at regular environments). -/
theorem exists_forwardKernel {d : ℕ} (L : ℝ) (κ : QuenchedPathLaws d) :
    ∃ κ' : QuenchedPathLaws d, ∀ (ω : FieldPair d) (hω : IsRegular L ω),
      IsProbabilityMeasure (κ (0, ω)) →
        κ' (0, ω) = (κ (0, ω)).map (forwardClockPath hω) := by
  classical
  let S : Set (Vec d × FieldPair d) := {a | a.1 = 0 ∧ κ a Set.univ = 1}
  have hS : MeasurableSet S := by
    show MeasurableSet ({a : Vec d × FieldPair d | a.1 = 0} ∩ {a | κ a Set.univ = 1})
    refine MeasurableSet.inter ?_ ?_
    · exact (measurableSet_singleton (0 : Vec d)).preimage measurable_fst
    · exact measurableSet_eq_fun (Kernel.measurable_coe κ MeasurableSet.univ) measurable_const
  let κ₁ : QuenchedPathLaws d := Kernel.piecewise hS κ 0
  haveI : IsFiniteKernel κ₁ := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun a => ?_⟩⟩
    simp only [κ₁, Kernel.piecewise_apply]
    split_ifs with h
    · exact h.2.le
    · simp
  let g : (Vec d × FieldPair d) × Path d → Path d := fun p => forwardPathMap d L (p.1.2, p.2)
  have hg : Measurable g :=
    (measurable_forwardPathMap d L).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  refine ⟨Kernel.map (Kernel.id ×ₖ κ₁) g, fun ω hω hprob => ?_⟩
  have hmem : ((0 : Vec d), ω) ∈ S := ⟨rfl, measure_univ⟩
  have h1 : κ₁ (0, ω) = κ (0, ω) := by
    simp only [κ₁, Kernel.piecewise_apply, hmem, ite_true]
  rw [Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod, h1,
    Measure.map_map hg measurable_prodMk_left]
  congr 1
  funext γ
  exact forwardPathMap_of_regular hω γ

end EinsteinFull
