import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Probability.LocalSigma
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-! # The actual strongly continuous translation group on L²

Source `paper/main.tex:240–244`. Each isometry composes an actual L² class
with the literal translation of the physical environment. Its representative,
group law, inverse and strong continuity are proved from the given stationary
probability measure and compact-open topology. No density, generator-domain
characterization, horizontal H¹ identity or stochastic invariance is assumed.
The physical carrier transports the joint reduced-field observations.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

theorem measurePreserving_translate {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) : MeasurePreserving (translate x) Q Q :=
  ⟨Probability.measurable_translate x, hQ x⟩

def translationLp {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (x : Vec d) : Lp ℝ 2 Q →ₗᵢ[ℝ] Lp ℝ 2 Q :=
  Lp.compMeasurePreservingₗᵢ ℝ (translate x) (measurePreserving_translate Q hQ x)

theorem coeFn_translationLp {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (x : Vec d) (f : Lp ℝ 2 Q) : translationLp Q hQ x f =ᵐ[Q] fun ω => f (translate x ω) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_translate Q hQ x)

theorem translationLp_zero {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (f : Lp ℝ 2 Q) : translationLp Q hQ 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_translationLp Q hQ 0 f] with ω hω
  simpa only [translate_zero] using hω

theorem translationLp_add {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (x y : Vec d) (f : Lp ℝ 2 Q) :
    translationLp Q hQ (x + y) f = translationLp Q hQ x (translationLp Q hQ y f) := by
  apply Lp.ext
  have hm := measurePreserving_translate Q hQ x
  have hc := hm.quasiMeasurePreserving.ae (coeFn_translationLp Q hQ y f)
  filter_upwards [coeFn_translationLp Q hQ (x+y) f,
    coeFn_translationLp Q hQ x (translationLp Q hQ y f), hc] with ω ha hb hcω
  rw [ha, hb, hcω]
  rw [translate_add, add_comm y x]

theorem norm_translationLp {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (x : Vec d) (f : Lp ℝ 2 Q) : ‖translationLp Q hQ x f‖ = ‖f‖ :=
  (translationLp Q hQ x).norm_map f

theorem translationLp_neg_cancel {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (x : Vec d) (f : Lp ℝ 2 Q) : translationLp Q hQ (-x) (translationLp Q hQ x f) = f := by
  rw [← translationLp_add, neg_add_cancel, translationLp_zero]

theorem continuous_translationLp {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) : Continuous (fun p : Vec d × Lp ℝ 2 Q => translationLp Q hQ p.1 p.2) := by
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  let g : Vec d × Lp ℝ 2 Q → C(FieldPair d, FieldPair d) :=
    fun p => ⟨translate p.1, Probability.continuous_translate.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Probability.continuous_translate.comp ((continuous_fst.fst).prodMk continuous_snd)
  exact continuous_snd.compMeasurePreservingLp hg (fun p => measurePreserving_translate Q hQ p.1)
    (by norm_num)

theorem tendsto_translationLp_zero {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (f : Lp ℝ 2 Q) :
    Filter.Tendsto (fun x : Vec d => translationLp Q hQ x f) (nhds 0) (nhds f) := by
  have h : Continuous (fun x : Vec d => translationLp Q hQ x f) :=
    (continuous_translationLp Q hQ).comp (continuous_id.prodMk continuous_const)
  simpa only [translationLp_zero] using h.tendsto 0

/-- Every L² class is reached by translating back along the same actual action. -/
theorem surjective_translationLp {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (x : Vec d) : Function.Surjective (translationLp Q hQ x) := by
  intro f
  refine ⟨translationLp Q hQ (-x) f, ?_⟩
  simpa only [neg_neg] using translationLp_neg_cancel Q hQ (-x) f

/-- The action on genuine integrable representatives is exactly composition. -/
theorem translationLp_toLp {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (x : Vec d) {F : FieldPair d → ℝ} (hF : MemLp F 2 Q) :
    translationLp Q hQ x (hF.toLp F) =
      (hF.comp_measurePreserving (measurePreserving_translate Q hQ x)).toLp
        (fun ω => F (translate x ω)) := rfl

end EinsteinRelation
