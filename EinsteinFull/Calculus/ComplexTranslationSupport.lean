import EinsteinFull.Frozen.ComplexHorizontalDerivative

/-! Basic facts for the actual complex translation action.

The composition, inverse and continuity arguments are adapted from
`EinsteinRelation/Calculus/HorizontalTranslationLp.lean` at blueprint revision
`7748a8e9000034825873768d309be8915ae53b07`, replacing the real target by `ℂ`.
They apply to arbitrary stationary measures, with probability needed only for
the continuity argument. No diffusion or paper-specific estimate is used.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace EinsteinFull

open EinsteinRelation

theorem coeFn_complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (f : Lp ℂ 2 Q) :
    complexTranslation Q hQ x f =ᵐ[Q] fun ω => f (translate x ω) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_translate Q hQ x)

theorem complexTranslation_zero {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : Lp ℂ 2 Q) : complexTranslation Q hQ 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_complexTranslation Q hQ 0 f] with ω hω
  simpa only [translate_zero] using hω

theorem complexTranslation_add {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x y : Vec d) (f : Lp ℂ 2 Q) :
    complexTranslation Q hQ (x + y) f =
      complexTranslation Q hQ x (complexTranslation Q hQ y f) := by
  apply Lp.ext
  have hm := measurePreserving_translate Q hQ x
  have hc := hm.quasiMeasurePreserving.ae (coeFn_complexTranslation Q hQ y f)
  filter_upwards [coeFn_complexTranslation Q hQ (x + y) f,
    coeFn_complexTranslation Q hQ x (complexTranslation Q hQ y f), hc] with ω ha hb hcω
  rw [ha, hb, hcω, translate_add, add_comm y x]

theorem norm_complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (f : Lp ℂ 2 Q) :
    ‖complexTranslation Q hQ x f‖ = ‖f‖ :=
  (complexTranslation Q hQ x).norm_map f

theorem complexTranslation_neg_cancel {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (f : Lp ℂ 2 Q) :
    complexTranslation Q hQ (-x) (complexTranslation Q hQ x f) = f := by
  rw [← complexTranslation_add, neg_add_cancel, complexTranslation_zero]

theorem surjective_complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) : Function.Surjective (complexTranslation Q hQ x) := by
  intro f
  refine ⟨complexTranslation Q hQ (-x) f, ?_⟩
  simpa only [neg_neg] using complexTranslation_neg_cancel Q hQ (-x) f

theorem continuous_complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) :
    Continuous (fun p : Vec d × Lp ℂ 2 Q => complexTranslation Q hQ p.1 p.2) := by
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  let g : Vec d × Lp ℂ 2 Q → C(FieldPair d, FieldPair d) :=
    fun p => ⟨translate p.1,
      Probability.continuous_translate.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Probability.continuous_translate.comp ((continuous_fst.fst).prodMk continuous_snd)
  exact continuous_snd.compMeasurePreservingLp hg
    (fun p => measurePreserving_translate Q hQ p.1) (by norm_num)

theorem tendsto_complexTranslation_zero {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : Lp ℂ 2 Q) :
    Tendsto (fun x : Vec d => complexTranslation Q hQ x f) (𝓝 0) (𝓝 f) := by
  have h : Continuous (fun x : Vec d => complexTranslation Q hQ x f) :=
    (continuous_complexTranslation Q hQ).comp (continuous_id.prodMk continuous_const)
  simpa only [complexTranslation_zero] using h.tendsto 0

theorem HasComplexHorizontalDerivative.unique {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {f g h : Lp ℂ 2 Q}
    (hg : HasComplexHorizontalDerivative Q hQ i f g)
    (hh : HasComplexHorizontalDerivative Q hQ i f h) : g = h :=
  tendsto_nhds_unique hg hh

end EinsteinFull
