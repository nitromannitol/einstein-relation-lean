import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Environment.Reduction

/-! The replacement pair `(a / a₁₁, -(1/2) log a₁₁)` of `sharp.example#replacement-pair`
(`paper/main.tex:1565`), as a total pointwise-local, translation-equivariant measurable map on
field pairs (the argument of the logarithm is clamped below, which does not change the map on the
event `a₁₁ ≥ 1/3`), together with the transfer of stationarity and joint finite range to its image
law. -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1

open EinsteinRelation

variable {d : ℕ}

/-- The pointwise replacement of `(a₀, V)` at one point. -/
noncomputable def replacePhi (first : Fin d) (p : Mat d × ℝ) : Mat d × ℝ :=
  ((max (Real.exp (-2 * p.2) * p.1 first first) (1 / 4))⁻¹ • (Real.exp (-2 * p.2) • p.1),
   -(1 / 2 : ℝ) * Real.log (max (Real.exp (-2 * p.2) * p.1 first first) (1 / 4)))

theorem continuous_replacePhi (first : Fin d) : Continuous (replacePhi first) := by
  have hexp : Continuous fun p : Mat d × ℝ => Real.exp (-2 * p.2) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_snd)
  have hA : Continuous fun p : Mat d × ℝ => p.1 first first :=
    continuous_fst.matrix_elem first first
  have hm : Continuous fun p : Mat d × ℝ =>
      max (Real.exp (-2 * p.2) * p.1 first first) (1 / 4) :=
    (hexp.mul hA).max continuous_const
  have hne : ∀ p : Mat d × ℝ, max (Real.exp (-2 * p.2) * p.1 first first) (1 / 4) ≠ 0 :=
    fun p => (lt_max_of_lt_right (by norm_num : (0 : ℝ) < 1 / 4)).ne'
  refine Continuous.prodMk ?_ ?_
  · exact (hm.inv₀ hne).smul (hexp.smul continuous_fst)
  · exact continuous_const.mul (hm.log hne)

/-- The replacement pair of a field pair. -/
noncomputable def replacePair (first : Fin d) (ω : FieldPair d) : FieldPair d :=
  (⟨fun x => (replacePhi first (ω.1 x, ω.2 x)).1,
      (continuous_replacePhi first |>.comp
        (ω.1.continuous.prodMk ω.2.continuous)).fst⟩,
   ⟨fun x => (replacePhi first (ω.1 x, ω.2 x)).2,
      (continuous_replacePhi first |>.comp
        (ω.1.continuous.prodMk ω.2.continuous)).snd⟩)

theorem replacePair_fst (first : Fin d) (ω : FieldPair d) (x : Vec d) :
    (replacePair first ω).1 x =
      (max (reducedCoefficient ω x first first) (1 / 4))⁻¹ • reducedCoefficient ω x := rfl

theorem replacePair_snd (first : Fin d) (ω : FieldPair d) (x : Vec d) :
    (replacePair first ω).2 x =
      -(1 / 2 : ℝ) * Real.log (max (reducedCoefficient ω x first first) (1 / 4)) := rfl

theorem measurable_replacePair (first : Fin d) : Measurable (replacePair first) := by
  refine measurable_fieldPair_of_evaluations _ fun x => ?_
  have hev : Measurable fun ω : FieldPair d => (ω.1 x, ω.2 x) :=
    (((continuous_eval_const x).comp continuous_fst).prodMk
      ((continuous_eval_const x).comp continuous_snd)).measurable
  exact (continuous_replacePhi first).measurable.comp hev

theorem replacePair_translate (first : Fin d) (x : Vec d) (ω : FieldPair d) :
    replacePair first (translate x ω) = translate x (replacePair first ω) :=
  Prod.ext (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl)

/-- The replacement is local: it is measurable for the local σ-algebra of any set. -/
theorem measurable_replacePair_local (first : Fin d) (V : Set (Vec d)) :
    @Measurable (FieldPair d) (FieldPair d) (localSigma V) (localSigma V) (replacePair first) := by
  refine measurable_iff_comap_le.mpr ?_
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun a => ?_
  rw [MeasurableSpace.comap_comp]
  have heq : (fun ω : FieldPair d => (ω.1 (a : Vec d), ω.2 (a : Vec d))) ∘ replacePair first =
      replacePhi first ∘ (fun ω : FieldPair d => (ω.1 (a : Vec d), ω.2 (a : Vec d))) :=
    funext fun ω => rfl
  rw [heq, ← MeasurableSpace.comap_comp]
  refine le_trans (MeasurableSpace.comap_mono (continuous_replacePhi first).measurable.comap_le) ?_
  exact le_iSup (fun a : ↥V => MeasurableSpace.comap
    (fun ω : FieldPair d => (ω.1 (a : Vec d), ω.2 (a : Vec d))) inferInstance) a

theorem isStationary_map_replacePair (first : Fin d) {Q : Measure (FieldPair d)}
    (hQ : IsStationary Q) : IsStationary (Q.map (replacePair first)) := by
  intro x
  have hF := measurable_replacePair first
  have hT := Probability.measurable_translate (d := d) x
  rw [Measure.map_map hT hF]
  have hcomp : translate x ∘ replacePair first = replacePair first ∘ translate x :=
    funext fun ω => (replacePair_translate first x ω).symm
  rw [hcomp, ← Measure.map_map hF hT, hQ x]

theorem hasFiniteRange_map_replacePair (first : Fin d) {Q : Measure (FieldPair d)} {r : ℝ}
    (hQ : HasFiniteRange r Q) : HasFiniteRange r (Q.map (replacePair first)) := by
  intro U W hU hW hsep
  have hF := measurable_replacePair first
  rw [ProbabilityTheory.Indep_iff]
  intro t1 t2 h1 h2
  have hpre1 : MeasurableSet[localSigma U] (replacePair first ⁻¹' t1) :=
    measurable_replacePair_local first U h1
  have hpre2 : MeasurableSet[localSigma W] (replacePair first ⁻¹' t2) :=
    measurable_replacePair_local first W h2
  have ht1 : MeasurableSet t1 := Probability.localSigma_le_borel U _ h1
  have ht2 : MeasurableSet t2 := Probability.localSigma_le_borel W _ h2
  rw [Measure.map_apply hF (ht1.inter ht2), Measure.map_apply hF ht1, Measure.map_apply hF ht2,
    Set.preimage_inter]
  exact (ProbabilityTheory.Indep_iff _ _ _).1 (hQ U W hU hW hsep) _ _ hpre1 hpre2

end EinsteinFull.Calculus.S1
