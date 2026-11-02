import EinsteinRelation.Diffusion.ClockInverseSupport
import EinsteinRelation.Diffusion.EnvironmentProcessFamily
import EinsteinRelation.Diffusion.PathLawUniquenessSupport
import EinsteinRelation.Environment.ReductionImageSupport
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped NNReal

noncomputable section

namespace EinsteinRelation.Clock.PathMapV4

open EinsteinRelation.ReductionImageV3
open EinsteinRelation.Clock.InverseMeaningV3

abbrev PhysicalInput (d : ℕ) (L : ℝ) := PhysicalField d L

private theorem continuous_physicalClockAt {d : ℕ} {L : ℝ} (s : ℝ≥0) :
    Continuous (fun z : PhysicalInput d L × Path d =>
      EinsteinRelation.Clock.physicalPathClock z.1.1 z.2 s) := by
  have hγ : Continuous (fun q : (PhysicalInput d L × Path d) × ℝ =>
      q.1.2 q.2.toNNReal) :=
    (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0) (Y := Vec d)).comp
      (continuous_fst.snd.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hV : Continuous (fun q : (PhysicalInput d L × Path d) × ℝ =>
      q.1.1.1.2 (q.1.2 q.2.toNNReal)) := by
    have hfield : Continuous (fun q : (PhysicalInput d L × Path d) × ℝ =>
        q.1.1.1.2) :=
      continuous_snd.comp (continuous_subtype_val.comp (continuous_fst.fst))
    exact hfield.eval hγ
  let integrand : PhysicalInput d L × Path d → ℝ → ℝ := fun z u =>
    Real.exp (-2 * z.1.1.2 (z.2 u.toNNReal))
  have hf : Continuous integrand.uncurry := by
    change Continuous (fun q : (PhysicalInput d L × Path d) × ℝ =>
      Real.exp (-2 * q.1.1.1.2 (q.1.2 q.2.toNNReal)))
    exact Real.continuous_exp.comp (continuous_const.mul hV)
  have hreal : Continuous (fun z : PhysicalInput d L × Path d =>
      EinsteinRelation.Clock.pathClock (clockDensity z.1.1) z.2 s) := by
    change Continuous (fun z : PhysicalInput d L × Path d =>
      ∫ u in (0 : ℝ)..(s : ℝ), integrand z u)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := integrand) hf 0 (s : ℝ)
  change Continuous (fun z : PhysicalInput d L × Path d =>
    (⟨EinsteinRelation.Clock.pathClock (clockDensity z.1.1) z.2 s,
      intervalIntegral.integral_nonneg s.property
        (fun u _ => (clockDensity_pos z.1.1 (z.2 u.toNNReal)).le)⟩ : ℝ≥0))
  exact hreal.subtype_mk fun z =>
    intervalIntegral.integral_nonneg s.property
      (fun u _ => (clockDensity_pos z.1.1 (z.2 u.toNNReal)).le)

def inversePhysicalTime {d : ℕ} {L : ℝ}
    (z : PhysicalInput d L × Path d) (t : ℝ≥0) : ℝ≥0 :=
  inversePhysicalPathClock z.1.1 z.2 L z.1.2 t

private theorem inversePhysicalTime_lt_iff {d : ℕ} {L : ℝ}
    (z : PhysicalInput d L × Path d) (t s : ℝ≥0) :
    inversePhysicalTime z t < s ↔
      t < EinsteinRelation.Clock.physicalPathClock z.1.1 z.2 s := by
  let e := physicalPathClockOrderIso z.1.1 z.2 L z.1.2
  change e.symm t < s ↔ t < e s
  constructor
  · intro h
    have h' : e (e.symm t) < e s := e.strictMono h
    simpa using h'
  · intro h
    have h' : e.symm t < e.symm (e s) := e.symm.strictMono h
    simpa using h'

theorem measurable_inversePhysicalTime {d : ℕ} {L : ℝ} :
    Measurable (fun z : (PhysicalInput d L × Path d) × ℝ≥0 =>
      inversePhysicalTime z.1 z.2) := by
  apply measurable_of_Iio
  intro s
  change MeasurableSet {z : (PhysicalInput d L × Path d) × ℝ≥0 |
    inversePhysicalTime z.1 z.2 < s}
  rw [show {z : (PhysicalInput d L × Path d) × ℝ≥0 |
      inversePhysicalTime z.1 z.2 < s} =
      {z | z.2 < EinsteinRelation.Clock.physicalPathClock z.1.1.1 z.1.2 s} by
        ext z
        exact inversePhysicalTime_lt_iff z.1 z.2 s]
  exact measurableSet_lt measurable_snd
    ((continuous_physicalClockAt (d := d) (L := L) s).measurable.comp measurable_fst)

private theorem measurable_inversePhysicalTimeAt {d : ℕ} {L : ℝ}
    (t : ℝ≥0) :
    Measurable (fun z : PhysicalInput d L × Path d => inversePhysicalTime z t) := by
  apply measurable_of_Iio
  intro s
  change MeasurableSet {z : PhysicalInput d L × Path d | inversePhysicalTime z t < s}
  rw [show {z : PhysicalInput d L × Path d | inversePhysicalTime z t < s} =
      {z | t < EinsteinRelation.Clock.physicalPathClock z.1.1 z.2 s} by
        ext z
        exact inversePhysicalTime_lt_iff z t s]
  exact measurableSet_lt measurable_const
    (continuous_physicalClockAt (d := d) (L := L) s).measurable

def inverseClockPathMap {d : ℕ} {L : ℝ}
    (z : PhysicalInput d L × Path d) : Path d :=
  inverseClockPath z.1.1 z.2 L z.1.2

@[simp] theorem inverseClockPathMap_apply {d : ℕ} {L : ℝ}
    (z : PhysicalInput d L × Path d) (t : ℝ≥0) :
    inverseClockPathMap z t = z.2 (inversePhysicalTime z t) := rfl

theorem measurable_inverseClockPathMap {d : ℕ} {L : ℝ} :
    Measurable (inverseClockPathMap (d := d) (L := L)) := by
  have hEval : ∀ t : ℝ≥0,
      Measurable (fun z : PhysicalInput d L × Path d => inverseClockPathMap z t) := by
    intro t
    have hinv : Measurable (fun z : PhysicalInput d L × Path d => inversePhysicalTime z t) :=
      measurable_inversePhysicalTimeAt t
    have heval :=
      (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0) (Y := Vec d)).measurable
    exact heval.comp (measurable_snd.prodMk hinv)
  change @Measurable (PhysicalInput d L × Path d) (Path d) _
    (borel (Path d)) (inverseClockPathMap (d := d) (L := L))
  rw [borel_eq_generateFrom_measurablePathCylinders]
  apply measurable_generateFrom
  intro s hs
  rcases hs with ⟨c, hc, rfl⟩
  induction c with
  | nil => simp [pathEvalCylinder]
  | cons p c ih =>
    rcases p with ⟨t, A⟩
    simp only [pathEvalCylinder, Set.preimage_inter]
    exact (hEval t (hc (t, A) (by simp))).inter
      (ih (fun q hq => hc q (by simp [hq])))

def physicalClockTimeChangeMap {d : ℕ} {L : ℝ}
    (z : PhysicalInput d L × Path d) : PhysicalInput d L × Path d :=
  (z.1, inverseClockPathMap z)

theorem measurable_physicalClockTimeChangeMap {d : ℕ} {L : ℝ} :
    Measurable (physicalClockTimeChangeMap (d := d) (L := L)) :=
  measurable_fst.prodMk measurable_inverseClockPathMap

noncomputable def physicalClockTimeChangeLaw {d : ℕ} {L : ℝ}
    (P : Measure (PhysicalInput d L × Path d)) :
    Measure (PhysicalInput d L × Path d) :=
  P.map physicalClockTimeChangeMap

theorem physicalClockTimeChangeLaw_isProbabilityMeasure {d : ℕ} {L : ℝ}
    (P : Measure (PhysicalInput d L × Path d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (physicalClockTimeChangeLaw P) := by
  unfold physicalClockTimeChangeLaw
  exact inferInstance

theorem physicalClockTimeChangeMap_startsAtOrigin {d : ℕ} {L : ℝ}
    (z : PhysicalInput d L × Path d) (hγ : z.2 0 = 0) :
    (physicalClockTimeChangeMap z).2 0 = 0 := by
  change inverseClockPath z.1.1 z.2 L z.1.2 0 = 0
  exact inverseClockPath_startsAtOrigin z.1.1 z.2 L z.1.2 hγ

theorem physicalClockTimeChangeLaw_startsAtOrigin {d : ℕ} {L : ℝ}
    (P : Measure (PhysicalInput d L × Path d))
    (hstart : ∀ᵐ z ∂P, z.2 0 = 0) :
    ∀ᵐ z ∂physicalClockTimeChangeLaw P, z.2 0 = 0 := by
  have hset : MeasurableSet {z : PhysicalInput d L × Path d | z.2 0 = 0} :=
    ((continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_snd)
      (measurableSet_singleton (0 : Vec d))
  rw [physicalClockTimeChangeLaw, ae_map_iff
    measurable_physicalClockTimeChangeMap.aemeasurable hset]
  filter_upwards [hstart] with z hz
  exact physicalClockTimeChangeMap_startsAtOrigin z hz

theorem suppliedReducedLaw_timeChange_consumer {d : ℕ} {L : ℝ}
    (P : Measure (PhysicalInput d L × Path d)) [IsProbabilityMeasure P]
    (hstart : ∀ᵐ z ∂P, z.2 0 = 0) :
    IsProbabilityMeasure (physicalClockTimeChangeLaw P) ∧
      ∀ᵐ z ∂physicalClockTimeChangeLaw P, z.2 0 = 0 := by
  exact ⟨physicalClockTimeChangeLaw_isProbabilityMeasure P,
    physicalClockTimeChangeLaw_startsAtOrigin P hstart⟩

theorem physicalClockTimeChangeMap_pathwise {d : ℕ} {L : ℝ}
    (z : PhysicalInput d L × Path d) (t : ℝ≥0) :
    (physicalClockTimeChangeMap z).2
      (EinsteinRelation.Clock.physicalPathClock z.1.1 z.2 t) = z.2 t := by
  change inverseClockPath z.1.1 z.2 L z.1.2
    (EinsteinRelation.Clock.physicalPathClock z.1.1 z.2 t) = z.2 t
  exact inverseClockPath_atPhysicalClock z.1.1 z.2 L z.1.2 t

private def pathStartsAtOriginSet {d : ℕ} : Set (Path d) :=
  {γ | γ 0 = 0}

private theorem measurableSet_pathStartsAtOriginSet {d : ℕ} :
    MeasurableSet (pathStartsAtOriginSet (d := d)) := by
  exact ((continuous_eval_const (0 : ℝ≥0)).measurable)
    (measurableSet_singleton (0 : Vec d))

private def originPathStartsAtOriginSet {d : ℕ} (P : QuenchedPathLaws d) :
    Set (FieldPair d) :=
  {ω | (originLaw P ω) (pathStartsAtOriginSet (d := d)) = 1}

private theorem measurableSet_originPathStartsAtOriginSet {d : ℕ}
    (P : QuenchedPathLaws d) :
    MeasurableSet (originPathStartsAtOriginSet P) := by
  exact ((originLaw P).measurable_coe
    (measurableSet_pathStartsAtOriginSet (d := d)))
    (measurableSet_singleton 1)

/-- The reference `Q`-law paired with the supplied origin-path fibers, lifted
to the existing physical-field subtype. The actual-family consumer below
derives its probability and start-point properties from the existing
`IsReducedDiffusionFamily` contract; this construction does not identify a
canonical physical diffusion law or prove a stochastic time-change coupling. -/
noncomputable def actualPhysicalInputPathLaw {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (P : QuenchedPathLaws d) :
    Measure (PhysicalInput d L × Path d) :=
  (ReductionImageV3.physicalReferenceLaw Q).compProd
    (Probability.probabilityPart ((originLaw P).comap
      (Subtype.val : PhysicalInput d L → FieldPair d) measurable_subtype_coe))

/-- The lifted joint law uses the probability fibres supplied by the actual reduced family. -/
theorem actualPhysicalInputPathLaw_isProbabilityMeasure {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (P : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)) :
    IsProbabilityMeasure (actualPhysicalInputPathLaw Q P) := by
  let μ := ReductionImageV3.physicalReferenceLaw Q
  let K := (originLaw P).comap
    (Subtype.val : PhysicalInput d L → FieldPair d) measurable_subtype_coe
  let probSet : Set (FieldPair d) := {ω | (originLaw P ω) Set.univ = 1}
  have hprobSet : MeasurableSet probSet := by
    exact ((originLaw P).measurable_coe MeasurableSet.univ)
      (measurableSet_singleton 1)
  have hprobSetAE : ∀ᵐ ω ∂Q.measure, ω ∈ probSet := by
    filter_upwards [hprob] with ω hω
    exact hω.measure_univ
  have hprobLift : ∀ᵐ z ∂μ, z.1 ∈ probSet := by
    have hmap : μ.map (Subtype.val : PhysicalInput d L → FieldPair d) = Q.measure :=
      ReductionImageV3.physicalReferenceLaw_forget Q
    have hprobMap : ∀ᵐ ω ∂μ.map (Subtype.val : PhysicalInput d L → FieldPair d),
        ω ∈ probSet := by
      rw [hmap]
      exact hprobSetAE
    exact (ae_map_iff measurable_subtype_coe.aemeasurable hprobSet).mp hprobMap
  have hKprob : ∀ᵐ z ∂μ, IsProbabilityMeasure (K z) := by
    filter_upwards [hprobLift] with z hz
    change IsProbabilityMeasure ((originLaw P) z.1)
    exact ⟨hz⟩
  letI : IsProbabilityMeasure μ := ReductionImageV3.physicalReferenceLaw_probability Q
  change IsProbabilityMeasure (μ.compProd (Probability.probabilityPart K))
  exact Probability.isProbabilityMeasure_compProd_probabilityPart μ K hKprob

/-- The actual reduced family starts at the origin under its lifted physical joint law. -/
theorem actualPhysicalInputPathLaw_startsAtOrigin {d : ℕ} {L r₀ : ℝ} {i : Fin d}
    (Q : EnvironmentLaw d L r₀) (P : DiffusionFamily d)
    (hP : IsReducedDiffusionFamily i Q P) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ᵐ z ∂actualPhysicalInputPathLaw Q (P lam), z.2 0 = 0 := by
  let μ := ReductionImageV3.physicalReferenceLaw Q
  let K := (originLaw (P lam)).comap
    (Subtype.val : PhysicalInput d L → FieldPair d) measurable_subtype_coe
  let startSet := pathStartsAtOriginSet (d := d)
  let startFieldSet := originPathStartsAtOriginSet (P lam)
  have hstartQ : ∀ᵐ ω ∂Q.measure, ω ∈ startFieldSet := by
    filter_upwards [hP lam hlam] with ω hω
    letI : IsProbabilityMeasure (P lam (0, ω)) := hω.1
    have hstart := (ae_iff_measure_eq
      (measurableSet_pathStartsAtOriginSet (d := d)).nullMeasurableSet).mp hω.2.1
    change (originLaw (P lam) ω) startSet = 1
    simpa [originLaw, startSet, pathStartsAtOriginSet] using hstart
  have hstartFieldSet : MeasurableSet startFieldSet :=
    measurableSet_originPathStartsAtOriginSet (P lam)
  have hstartLift : ∀ᵐ z ∂μ, z.1 ∈ startFieldSet := by
    have hmap : μ.map (Subtype.val : PhysicalInput d L → FieldPair d) = Q.measure :=
      ReductionImageV3.physicalReferenceLaw_forget Q
    have hstartMap : ∀ᵐ ω ∂μ.map (Subtype.val : PhysicalInput d L → FieldPair d),
        ω ∈ startFieldSet := by
      rw [hmap]
      exact hstartQ
    exact (ae_map_iff measurable_subtype_coe.aemeasurable hstartFieldSet).mp hstartMap
  have hprobQ : ∀ᵐ ω ∂Q.measure,
      IsProbabilityMeasure (originLaw (P lam) ω) := hP.probability hlam
  let probSet : Set (FieldPair d) := {ω | (originLaw (P lam) ω) Set.univ = 1}
  have hprobSet : MeasurableSet probSet := by
    exact ((originLaw (P lam)).measurable_coe MeasurableSet.univ)
      (measurableSet_singleton 1)
  have hprobSetAE : ∀ᵐ ω ∂Q.measure, ω ∈ probSet := by
    filter_upwards [hprobQ] with ω hω
    exact hω.measure_univ
  have hprobLift : ∀ᵐ z ∂μ, z.1 ∈ probSet := by
    have hmap : μ.map (Subtype.val : PhysicalInput d L → FieldPair d) = Q.measure :=
      ReductionImageV3.physicalReferenceLaw_forget Q
    have hprobMap : ∀ᵐ ω ∂μ.map (Subtype.val : PhysicalInput d L → FieldPair d),
        ω ∈ probSet := by
      rw [hmap]
      exact hprobSetAE
    exact (ae_map_iff measurable_subtype_coe.aemeasurable hprobSet).mp hprobMap
  have hstartFiber : ∀ᵐ z ∂μ, ∀ᵐ γ ∂Probability.probabilityPart K z,
      γ 0 = 0 := by
    filter_upwards [hprobLift, hstartLift] with z hzprob hzstart
    have hzprobK : IsProbabilityMeasure (K z) := ⟨hzprob⟩
    letI := hzprobK
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure K z]
    have hstartMass : (K z) startSet = (K z) Set.univ := by
      change (originLaw (P lam) z.1) startSet = 1 at hzstart
      calc
        (K z) startSet = 1 := hzstart
        _ = (K z) Set.univ := hzprobK.measure_univ.symm
    exact (ae_iff_measure_eq
      (measurableSet_pathStartsAtOriginSet (d := d)).nullMeasurableSet).mpr hstartMass
  have hset : MeasurableSet {z : PhysicalInput d L × Path d | z.2 0 = 0} :=
    ((continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_snd)
      (measurableSet_singleton (0 : Vec d))
  change ∀ᵐ z ∂μ.compProd (Probability.probabilityPart K), z.2 0 = 0
  exact Measure.ae_compProd_of_ae_ae hset hstartFiber

/-- The actual reduced joint law has a measurable clock pushforward preserving start zero. -/
theorem actualPhysicalClockTimeChangeLaw_consumer {d : ℕ} {L r₀ : ℝ} {i : Fin d}
    (Q : EnvironmentLaw d L r₀) (P : DiffusionFamily d)
    (hP : IsReducedDiffusionFamily i Q P) {lam : ℝ} (hlam : 0 ≤ lam) :
    IsProbabilityMeasure (physicalClockTimeChangeLaw (actualPhysicalInputPathLaw Q (P lam))) ∧
      ∀ᵐ z ∂physicalClockTimeChangeLaw (actualPhysicalInputPathLaw Q (P lam)),
        z.2 0 = 0 := by
  letI : IsProbabilityMeasure (actualPhysicalInputPathLaw Q (P lam)) :=
    actualPhysicalInputPathLaw_isProbabilityMeasure Q (P lam) (hP.probability hlam)
  exact suppliedReducedLaw_timeChange_consumer (actualPhysicalInputPathLaw Q (P lam))
    (actualPhysicalInputPathLaw_startsAtOrigin Q P hP hlam)

end EinsteinRelation.Clock.PathMapV4

#print axioms EinsteinRelation.Clock.PathMapV4.measurable_inversePhysicalTime
#print axioms EinsteinRelation.Clock.PathMapV4.inversePhysicalTime
#print axioms EinsteinRelation.Clock.PathMapV4.measurable_inverseClockPathMap
#print axioms EinsteinRelation.Clock.PathMapV4.inverseClockPathMap
#print axioms EinsteinRelation.Clock.PathMapV4.physicalClockTimeChangeMap
#print axioms EinsteinRelation.Clock.PathMapV4.physicalClockTimeChangeLaw
#print axioms EinsteinRelation.Clock.PathMapV4.physicalClockTimeChangeLaw_isProbabilityMeasure
#print axioms EinsteinRelation.Clock.PathMapV4.physicalClockTimeChangeLaw_startsAtOrigin
#print axioms EinsteinRelation.Clock.PathMapV4.suppliedReducedLaw_timeChange_consumer
#print axioms EinsteinRelation.Clock.PathMapV4.physicalClockTimeChangeMap_pathwise
#print axioms EinsteinRelation.Clock.PathMapV4.actualPhysicalInputPathLaw
#print axioms EinsteinRelation.Clock.PathMapV4.actualPhysicalInputPathLaw_isProbabilityMeasure
#print axioms EinsteinRelation.Clock.PathMapV4.actualPhysicalInputPathLaw_startsAtOrigin
#print axioms EinsteinRelation.Clock.PathMapV4.actualPhysicalClockTimeChangeLaw_consumer
