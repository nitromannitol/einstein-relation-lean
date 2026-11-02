import EinsteinFull.Calculus.S4PhysicalWellPosedSupport
import EinsteinFull.Calculus.S4TimeChangeMartingale
import EinsteinFull.Calculus.FellerRegularSet
import EinsteinFull.Frozen.SmoothEnvironment

/-!
# Pieces of the smooth-scope pathwise node

* uniqueness half (`pathwiseV2_uniqueness_part`): from the draft well-posedness input, any
  quenched path laws solving the physical and reduced martingale problems are related by the
  literal inverse-clock map, for almost every environment of a law with `HasSmoothBounds`;
* existence half (`pathwiseV2_existence_part_of_kernel`): from a Markov kernel of reduced
  solutions (the measurable-selection step), the physical kernel is the clock image.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Classical

namespace EinsteinFull
open EinsteinRelation

/-- The joint clock map `((x, ω), γ) ↦ inverseClockPath ω γ` on regular environments (identity
elsewhere). -/
noncomputable def timeChangeFamily {d : ℕ} (Λ : ℝ) (p : (Vec d × FieldPair d) × Path d) :
    Path d :=
  if h : IsRegular Λ p.1.2 then timeChangeMap h p.2 else p.2

theorem measurable_timeChangeFamily (d : ℕ) (Λ : ℝ) :
    Measurable (timeChangeFamily (d := d) Λ) := by
  have hS : MeasurableSet {p : (Vec d × FieldPair d) × Path d | IsRegular Λ p.1.2} :=
    (Calculus.Feller.measurableSet_setOf_isRegular d Λ).preimage
      (measurable_snd.comp measurable_fst)
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · have e : (Set.domRestrict {p : (Vec d × FieldPair d) × Path d | IsRegular Λ p.1.2}
        (timeChangeFamily (d := d) Λ)) = fun q =>
        Clock.PathMapV4.inverseClockPathMap (d := d) (L := Λ) (⟨q.1.1.2, q.2⟩, q.1.2) := by
      funext q
      have hq : IsRegular Λ q.1.1.2 := q.2
      show (if h : IsRegular Λ q.1.1.2 then timeChangeMap h q.1.2 else q.1.2) = _
      exact (dif_pos hq).trans rfl
    rw [e]
    exact (Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := Λ)).comp
      (Measurable.prodMk
        (Measurable.subtype_mk (measurable_snd.comp (measurable_fst.comp measurable_subtype_coe)))
        (measurable_snd.comp measurable_subtype_coe))
  · have e : (Set.domRestrict {p : (Vec d × FieldPair d) × Path d | IsRegular Λ p.1.2}ᶜ
        (timeChangeFamily (d := d) Λ)) = fun q => q.1.2 := by
      funext q
      have hq : ¬ IsRegular Λ q.1.1.2 := q.2
      show (if h : IsRegular Λ q.1.1.2 then timeChangeMap h q.1.2 else q.1.2) = _
      exact dif_neg hq
    rw [e]
    exact measurable_snd.comp measurable_subtype_coe

theorem pathwiseV2_uniqueness_part {d : ℕ} (hwp : External.Draft.svWellPosedStmt)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    (PX PY : QuenchedPathLaws d)
    (hX : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω))) :
    ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular D.ellipticity ω,
      PX (0, ω) = Measure.map
        (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω)
        (PY (0, ω)) ∧
      ∀ᵐ γ ∂PY (0, ω), ∀ t : ℝ≥0,
        Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω
          (Clock.physicalPathClock ω γ t) = γ t := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  filter_upwards [hX, hY, hsm] with ω hXω hYω hsω hω
  refine ⟨?_, Filter.Eventually.of_forall fun γ t => ?_⟩
  · have h1 := timeChange_solves hΛ hω hsω i lam 0 hYω
    obtain ⟨P, _, hP⟩ := exists_unique_physical_solution hwp hΛ hω hsω i lam 0
    exact (hP _ hXω).trans (hP _ h1).symm
  · exact Clock.InverseMeaningV3.inverseClockPath_atPhysicalClock ω γ _ hω t

theorem pathwiseV2_existence_part_of_kernel {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω)
    (i : Fin d) (lam : ℝ) (PY : QuenchedPathLaws d) [hMarkov : IsMarkovKernel PY]
    (hPY : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → IsSmoothFieldPair ω →
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω))) :
    ∃ PX PY' : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) ∧
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY' (0, ω))) := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  refine ⟨(Kernel.id ×ₖ PY).map (timeChangeFamily D.ellipticity), PY, ?_, ?_⟩
  · filter_upwards [Q.regular, hsm] with ω hreg hsω
    have hY := hPY ω hreg hsω
    have e : ((Kernel.id ×ₖ PY).map (timeChangeFamily D.ellipticity)) (0, ω) =
        (PY (0, ω)).map (timeChangeMap hreg) := by
      rw [Kernel.map_apply _ (measurable_timeChangeFamily d D.ellipticity), Kernel.prod_apply,
        Kernel.id_apply, Measure.dirac_prod,
        Measure.map_map (measurable_timeChangeFamily d D.ellipticity) measurable_prodMk_left]
      congr 1
      funext γ
      show (if h : IsRegular D.ellipticity ω then timeChangeMap h γ else γ) =
        timeChangeMap hreg γ
      exact dif_pos hreg
    rw [e]
    exact timeChange_solves hΛ hreg hsω i lam 0 hY
  · filter_upwards [Q.regular, hsm] with ω hreg hsω
    exact hPY ω hreg hsω

end EinsteinFull
