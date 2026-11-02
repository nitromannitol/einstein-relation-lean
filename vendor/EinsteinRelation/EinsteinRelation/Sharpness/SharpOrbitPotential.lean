import EinsteinRelation.Sharpness.SharpGradientField
import EinsteinRelation.Sharpness.ScalarSmoothBorel
import EinsteinRelation.Sharpness.FieldDerivativeMeasurability
import EinsteinRelation.Sharpness.PhysicalLawSampleBounds

/-! # Bounded orbit potentials for the sharp physical law

Source: `paper/main.tex` 1234–1238. A normalized smooth potential with constant harmonic flux
is unique for a regular coefficient. Lusin–Souslin therefore makes its existence a Borel
condition on the environment. This transfers the samplewise bounded potential to the physical
law without assuming measurability of the image of the distribution sample space.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

noncomputable section

private def harmonicPotentialPairs {d : ℕ} (i : Fin d) (Λ M : ℝ) (D : Set (Vec d)) :
    Set (FieldPair d × C(Vec d, ℝ)) :=
  {z | IsRegular Λ z.1 ∧ ContDiff ℝ (⊤ : ℕ∞) (z.2 : Vec d → ℝ) ∧ z.2 0 = 0 ∧
    ∀ x : D, |z.2 x| ≤ M ∧ euclideanNorm (gradient (z.2 : Vec d → ℝ) x) ≤ 1 / 4 ∧
      (reducedCoefficient z.1 x).mulVec (unitVector i + gradient (z.2 : Vec d → ℝ) x) =
        unitVector i}

private theorem measurableSet_harmonicPotentialPairs {d : ℕ} (i : Fin d) (Λ M : ℝ)
    {D : Set (Vec d)} (hD : D.Countable) :
    MeasurableSet (harmonicPotentialPairs i Λ M D) := by
  letI : Countable D := hD.to_subtype
  have hgrad (x : Vec d) : Measurable (fun z : FieldPair d × C(Vec d, ℝ) =>
      gradient (z.2 : Vec d → ℝ) x) := by
    refine measurable_pi_iff.mpr fun k => ?_
    exact (measurable_continuousMap_coordinateDerivative d k).comp
      (measurable_snd.prodMk measurable_const)
  have ha (x : Vec d) : Measurable (fun z : FieldPair d × C(Vec d, ℝ) =>
      reducedCoefficient z.1 x) := by
    have h1 : Continuous (fun z : FieldPair d × C(Vec d, ℝ) => z.1.1 x) :=
      (continuous_eval_const x).comp (continuous_fst.comp continuous_fst)
    have h2 : Continuous (fun z : FieldPair d × C(Vec d, ℝ) => z.1.2 x) :=
      (continuous_eval_const x).comp (continuous_snd.comp continuous_fst)
    exact ((Real.continuous_exp.comp (continuous_const.mul h2)).smul h1).measurable
  have hflux (x : Vec d) : Measurable (fun z : FieldPair d × C(Vec d, ℝ) =>
      (reducedCoefficient z.1 x).mulVec (unitVector i + gradient (z.2 : Vec d → ℝ) x)) := by
    refine measurable_pi_iff.mpr fun k => ?_
    exact Finset.measurable_sum Finset.univ fun j _ =>
      (((continuous_apply j).comp (continuous_apply k)).measurable.comp (ha x) |>.mul
        (measurable_const.add ((measurable_pi_apply j).comp (hgrad x))))
  have hnorm (x : Vec d) : Measurable (fun z : FieldPair d × C(Vec d, ℝ) =>
      euclideanNorm (gradient (z.2 : Vec d → ℝ) x)) := by
    unfold euclideanNorm euclideanSq dot
    exact (Finset.measurable_sum Finset.univ fun k _ =>
      ((measurable_pi_apply k).comp (hgrad x)).mul
        ((measurable_pi_apply k).comp (hgrad x))).sqrt
  unfold harmonicPotentialPairs
  apply MeasurableSet.inter ((measurableSet_isRegular_fieldPair Λ).preimage measurable_fst)
  apply MeasurableSet.inter (measurableSet_contDiff_continuousMap.preimage measurable_snd)
  apply MeasurableSet.inter (measurableSet_eq_fun
    (((continuous_eval_const (0 : Vec d)).comp continuous_snd).measurable) measurable_const)
  change MeasurableSet {z : FieldPair d × C(Vec d, ℝ) | ∀ x : D,
    |z.2 x| ≤ M ∧ euclideanNorm (gradient (z.2 : Vec d → ℝ) x) ≤ 1 / 4 ∧
      (reducedCoefficient z.1 x).mulVec (unitVector i + gradient (z.2 : Vec d → ℝ) x) =
        unitVector i}
  simp only [Set.setOf_forall, Set.setOf_and]
  exact MeasurableSet.iInter fun x : D =>
    (measurableSet_le (((continuous_eval_const (x : Vec d)).comp
      continuous_snd).measurable.abs) measurable_const).inter
      ((measurableSet_le (hnorm x) measurable_const).inter
        (measurableSet_eq_fun (hflux x) measurable_const))

private theorem harmonicPotentialPairs_properties {d : ℕ} {i : Fin d} {Λ M : ℝ}
    {D : Set (Vec d)} (hD : Dense D) {z : FieldPair d × C(Vec d, ℝ)}
    (hz : z ∈ harmonicPotentialPairs i Λ M D) :
    (∀ x, |z.2 x| ≤ M) ∧ (∀ x, euclideanNorm (gradient (z.2 : Vec d → ℝ) x) ≤ 1 / 4) ∧ ∀ x,
      (reducedCoefficient z.1 x).mulVec (unitVector i + gradient (z.2 : Vec d → ℝ) x) =
        unitVector i := by
  have hg : Continuous (gradient (z.2 : Vec d → ℝ)) := by
    refine continuous_pi fun k => ?_
    exact (hz.2.1.continuous_fderiv_apply
      (by simp)).comp
        (continuous_id.prodMk continuous_const)
  have ha : Continuous (reducedCoefficient z.1) := by
    exact (Real.continuous_exp.comp (continuous_const.mul z.1.2.continuous)).smul
      z.1.1.continuous
  constructor
  · exact fun x => (hD.closure_eq ▸ (isClosed_le z.2.continuous.abs continuous_const).closure_subset_iff.mpr
      (fun x hx => (hz.2.2.2 ⟨x, hx⟩).1)) (Set.mem_univ x)
  · constructor
    · have hc : Continuous fun x => euclideanNorm (gradient (z.2 : Vec d → ℝ) x) := by
        unfold euclideanNorm euclideanSq dot
        exact (continuous_finset_sum _ fun k _ =>
          ((continuous_apply k).comp hg).mul ((continuous_apply k).comp hg)).sqrt
      exact fun x => (hD.closure_eq ▸ (isClosed_le hc continuous_const).closure_subset_iff.mpr
        (fun x hx => (hz.2.2.2 ⟨x, hx⟩).2.1)) (Set.mem_univ x)
    · have hc : IsClosed {x : Vec d |
        (reducedCoefficient z.1 x).mulVec (unitVector i + gradient (z.2 : Vec d → ℝ) x) =
          unitVector i} := isClosed_eq (ha.matrix_mulVec (continuous_const.add hg)) continuous_const
      exact fun x => (hD.closure_eq ▸ hc.closure_subset_iff.mpr
        (fun x hx => (hz.2.2.2 ⟨x, hx⟩).2.2)) (Set.mem_univ x)

private theorem harmonicPotentialPairs_fst_injOn {d : ℕ} (i : Fin d) {Λ M : ℝ}
    (hΛ : 1 ≤ Λ) {D : Set (Vec d)} (hD : Dense D) :
    Set.InjOn Prod.fst (harmonicPotentialPairs i Λ M D) := by
  rintro ⟨ω, φ⟩ hφ ⟨ω', χ⟩ hχ (hω : ω = ω')
  subst ω'
  have hφflux := (harmonicPotentialPairs_properties hD hφ).2.2
  have hχflux := (harmonicPotentialPairs_properties hD hχ).2.2
  have hg : ∀ x, gradient (φ : Vec d → ℝ) x = gradient (χ : Vec d → ℝ) x := by
    intro x
    have hinj := Matrix.mulVec_injective_of_isUnit
      ((reducedCoefficient ω x).isUnit_iff_isUnit_det.mpr
        (isUnit_det_reducedCoefficient hΛ hφ.1 x))
    exact add_left_cancel (hinj ((hφflux x).trans (hχflux x).symm))
  have hd : ∀ x, fderiv ℝ (φ : Vec d → ℝ) x = fderiv ℝ (χ : Vec d → ℝ) x := by
    intro x
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = ∑ k, v k • unitVector k := by
      ext j
      simp [unitVector, Pi.single_apply]
    rw [hv]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun a : ℝ => v k • a) (congrFun (hg x) k)
  have heq := eq_of_fderiv_eq
    (hφ.2.1.differentiable (by simp))
    (hχ.2.1.differentiable (by simp)) hd 0 (hφ.2.2.1.trans hχ.2.2.1.symm)
  exact Prod.ext rfl (ContinuousMap.coe_injective heq)

/-- The bounded potential of the sharp pair descends to almost every physical environment.
Source: `paper/main.tex` 1234–1238. The potential is centered at the spatial origin, so its
bound is `2 * ε`. -/
theorem ae_clippedSharpGradient_orbit {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) (hε : 0 < ε) :
    ∀ᵐ ω ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)), ∃ φ : Vec d → ℝ,
      ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ 2 * ε) ∧
        ∀ x, gradient φ x = clippedSharpGradient i (translate x ω) := by
  obtain ⟨Λ, hΛ, hreg⟩ := sharpPhysicalPair_regular i δ ε hgrad hμ
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  let S := harmonicPotentialPairs i Λ (2 * ε) D
  letI : PolishSpace (Mat d) := inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  letI : PolishSpace C(Vec d, Mat d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  letI : PolishSpace C(Vec d, ℝ) := inferInstance
  have hS : MeasurableSet (Prod.fst '' S) :=
    (measurableSet_harmonicPotentialPairs i Λ (2 * ε) hDc).image_of_continuousOn_injOn
      continuous_fst.continuousOn (harmonicPotentialPairs_fst_injOn i (by linarith) hDd)
  have hp : ∀ W, sharpPhysicalPair i δ ε hgrad hμ W ∈ Prod.fst '' S := by
    intro W
    let φ : C(Vec d, ℝ) := ⟨fun x => ε * seedField d W x - ε * seedField d W 0,
      (sharpSeed_contDiff ε W).continuous.sub continuous_const⟩
    have hgφ : ∀ x, gradient (φ : Vec d → ℝ) x = gradient (fun y => ε * seedField d W y) x := by
      intro x
      ext k
      exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector k))
        (fderiv_sub_const (ε * seedField d W 0))
    refine ⟨(sharpPhysicalPair i δ ε hgrad hμ W, φ), ?_, rfl⟩
    refine ⟨hreg W, (sharpSeed_contDiff ε W).sub contDiff_const, sub_self _, fun x => ?_⟩
    constructor
    · exact (abs_sub _ _).trans (by linarith [sharpSeed_abs_le hε W x, sharpSeed_abs_le hε W 0])
    · constructor
      · rw [hgφ]
        exact hgrad W x
      · rw [hgφ]
        exact sharpPhysicalPair_harmonic i δ ε hgrad hμ W x
  have hae : ∀ᵐ ω ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)), ω ∈ Prod.fst '' S :=
    (ae_map_iff (measurable_sharpPhysicalPair i δ ε hgrad hμ).aemeasurable hS).mpr
      (ae_of_all P hp)
  filter_upwards [hae] with ω hω
  obtain ⟨⟨ω', φ⟩, hφ, (hω' : ω' = ω)⟩ := hω
  subst ω'
  obtain ⟨hb, hgb, hharm⟩ := harmonicPotentialPairs_properties hDd hφ
  refine ⟨φ, hφ.2.1.of_le (by norm_num), hb, fun x => ?_⟩
  have hg : gradient (φ : Vec d → ℝ) x = sharpGradientField i (translate x ω) := by
    have hinj := Matrix.mulVec_injective_of_isUnit
      ((reducedCoefficient ω x).isUnit_iff_isUnit_det.mpr
        (isUnit_det_reducedCoefficient (by linarith) hφ.1 x))
    apply add_left_cancel (a := unitVector i)
    apply hinj
    exact (hharm x).trans (sharpGradientField_harmonic_of_regular i (by linarith) hφ.1 x).symm
  have hbound : euclideanNorm (sharpGradientField i (translate x ω)) ≤ 1 / 4 := by
    rw [← hg]
    exact hgb x
  rw [clippedSharpGradient, if_pos hbound, hg]

end

end EinsteinRelation.Sharpness
