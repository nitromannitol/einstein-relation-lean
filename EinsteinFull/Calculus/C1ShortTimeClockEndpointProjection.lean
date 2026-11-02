import EinsteinFull.Calculus.C3EndpointLocalizationSupport
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Calculus.C1ForcedLocalityClosureSupport
import EinsteinFull.Calculus.C2RetainedPhysicalMeasurableEvolution
import EinsteinFull.Calculus.C6GaussianLocalLocalDivergenceTesting
import EinsteinFull.Calculus.C3PhysicalEvolutionJointMeasurability
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
/-- Global ellipticity of a continuous coefficient field is a closed condition.
Uncountable spatial and vector quantifiers are handled by closed intersections. -/
private theorem short_time_clock_elliptic_fields_closed {d : ℕ}
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    IsClosed {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} := by
  have hset : {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} =
      ⋂ x : Vec d,
        ((⋂ j : Fin d, ⋂ k : Fin d, {ω : FieldPair d | ω.1 x j k = ω.1 x k j}) ∩
          ⋂ ξ : Fin d → ℝ,
            ({ω : FieldPair d | Λ⁻¹ * ∑ j, ξ j ^ 2 ≤ s5Bil (ω.1 x) ξ ξ} ∩
             {ω : FieldPair d | s5Bil (ω.1 x) ξ ξ ≤ Λ * ∑ j, ξ j ^ 2})) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro h x
      exact ⟨(h x).symm, fun ξ => ⟨(h x).lower ξ, (h x).upper ξ⟩⟩
    · intro h x
      exact ⟨hΛ, (h x).1, fun ξ => ((h x).2 ξ).1, fun ξ => ((h x).2 ξ).2⟩
  rw [hset]
  apply isClosed_iInter
  intro x
  refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun k => ?_)
    (isClosed_iInter fun ξ => IsClosed.inter ?_ ?_)
  · apply isClosed_eq <;> fun_prop
  · apply isClosed_le continuous_const
    unfold s5Bil
    fun_prop
  · apply isClosed_le _ continuous_const
    unfold s5Bil
    fun_prop

/-- The good event for the retained evolution belongs to the local sigma
algebra, so the elliptic subtype can be used under the actual reduced law. -/
private theorem short_time_clock_retained_elliptic_measurable {d : ℕ}
    (χ : C(Vec d, ℝ)) (U : Set (Vec d))
    (hχ : ∀ x, x ∉ U → χ x = 0) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    MeasurableSet[EinsteinRelation.localSigma U]
      {ω : FieldPair d | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ} :=
  (short_time_clock_elliptic_fields_closed Λ hΛ).measurableSet.preimage
    (ForcedLocality.measurable_retainedPair χ U hχ)

/-- The retained coefficient evolution is constructed on the actual elliptic
retained fields, with the sigma algebra inherited from the joint local fields.
The subtype imposes no stationarity on the retained environment. -/
theorem short_time_clock_retained_physical_evolution {d : ℕ}
    (χ : C(Vec d, ℝ)) (U : Set (Vec d))
    (hχ : ∀ x, x ∉ U → χ x = 0) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (i : Fin d) (ζ : ℂ) :
    let Ω := {ω : FieldPair d //
      ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ}
    let : MeasurableSpace Ω := (EinsteinRelation.localSigma U).comap Subtype.val
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    ∃ P Pdag : Ω → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ ω, IsPhysicalComplexSemigroup
          (fun x => (ForcedLocality.retainedPair χ ω.val).1 x) i ζ (P ω) ∧
        IsPhysicalComplexTransposeSemigroup
          (fun x => (ForcedLocality.retainedPair χ ω.val).1 x) i ζ (P ω) (Pdag ω)) ∧
      (∀ t f, Measurable (fun ω => P ω t f) ∧
        Measurable (fun ω => Pdag ω t f)) ∧
      Measurable (fun p : Ω × (ℝ≥0 × Lp ℂ 2 (volume : Measure (Vec d))) =>
        P p.1 p.2.1 p.2.2) ∧
      Measurable (fun p : Ω × (ℝ≥0 × Lp ℂ 2 (volume : Measure (Vec d))) =>
        Pdag p.1 p.2.1 p.2.2) := by
  let Ω := {ω : FieldPair d //
    ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ}
  let : MeasurableSpace Ω := (EinsteinRelation.localSigma U).comap Subtype.val
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  have hval : Measurable[(EinsteinRelation.localSigma U).comap
      (Subtype.val : Ω → FieldPair d), EinsteinRelation.localSigma U]
      (Subtype.val : Ω → FieldPair d) := measurable_iff_comap_le.mpr le_rfl
  have hpair : Measurable (fun ω : Ω => ForcedLocality.retainedPair χ ω.val) :=
    (ForcedLocality.measurable_retainedPair χ U hχ).comp hval
  have heval : Continuous (fun p : FieldPair d × Vec d => p.1.1 p.2) := by
    fun_prop
  have ha : Measurable (fun s : Ω × Vec d =>
      (ForcedLocality.retainedPair χ s.1.val).1 s.2) :=
    heval.measurable.comp ((hpair.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨P, Pdag, hP, hPm⟩ := retained_physical_complex_measurable_evolution
    d i ζ Λ hΛ
    (fun ω : Ω => fun x => (ForcedLocality.retainedPair χ ω.val).1 x)
    ha (fun ω => ω.property)
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) :=
    Lp.SecondCountableTopology
  have hjoint
      (V : Ω → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hVc : ∀ ω f, Continuous (fun t : ℝ≥0 => V ω t f))
      (hVm : ∀ t f, Measurable (fun ω => V ω t f)) :
      Measurable (fun p : Ω × (ℝ≥0 × Lp ℂ 2 (volume : Measure (Vec d))) =>
        V p.1 p.2.1 p.2.2) := by
    have htime (f : Lp ℂ 2 (volume : Measure (Vec d))) :
        Measurable (fun p : ℝ≥0 × Ω => V p.2 p.1 f) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => hVc ω f) (fun t => hVm t f)
    have hdata : Measurable
        (fun p : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × Ω) =>
          V p.2.2 p.2.1 p.1) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun p : ℝ≥0 × Ω => (V p.2 p.1).continuous) htime
    exact hdata.comp (measurable_snd.snd.prodMk
      (measurable_snd.fst.prodMk measurable_fst))
  exact ⟨P, Pdag, hP, hPm,
    hjoint P (fun ω => (hP ω).1.2.2.1) (fun t f => (hPm t f).1),
    hjoint Pdag (fun ω => (hP ω).2.2.2.1) (fun t f => (hPm t f).2)⟩

/-- The retained clock minus its fixed exterior value is genuine spatial L2
initial data. No spatial integrability of the stationary clock is assumed. -/
private theorem short_time_clock_retained_initial_memLp {d : ℕ}
    (χ : C(Vec d, ℝ)) (hχ : HasCompactSupport χ) (ω : FieldPair d) :
    MemLp (fun x => ((ForcedLocality.retainedPair χ ω).2 x : ℂ) - 1)
      2 (volume : Measure (Vec d)) := by
  have hc : Continuous (fun x : Vec d => χ x • ((ω.2 x : ℂ) - 1)) :=
    χ.continuous.smul ((Complex.continuous_ofReal.comp ω.2.continuous).sub continuous_const)
  have hm : MemLp (fun x : Vec d => χ x • ((ω.2 x : ℂ) - 1))
      2 (volume : Measure (Vec d)) :=
    hc.memLp_of_hasCompactSupport hχ.smul_right
  convert hm using 1
  funext x
  change ((χ x * ω.2 x + (1 - χ x) : ℝ) : ℂ) - 1 =
    (χ x : ℂ) * ((ω.2 x : ℂ) - 1)
  push_cast
  ring

/-- Joint measurability descends to the actual complex spatial L2 classes. -/
private theorem short_time_clock_measurable_toLp {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (f : Ω → Vec d → ℂ)
    (hf : Measurable (fun s : Ω × Vec d => f s.1 s.2))
    (hL : ∀ ω, MemLp (f ω) 2 (volume : Measure (Vec d))) :
    @Measurable Ω (Lp ℂ 2 (volume : Measure (Vec d))) _ (borel _)
      (fun ω => (hL ω).toLp (f ω)) := by
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) :=
    Lp.SecondCountableTopology
  have hcriterion (g : Ω → Lp ℂ 2 (volume : Measure (Vec d)))
      (hg : ∀ y, Measurable (fun ω => dist (g ω) y)) : Measurable g := by
    apply measurable_of_isOpen
    intro s hs
    let I := {b : Lp ℂ 2 (volume : Measure (Vec d)) × ℝ // Metric.ball b.1 b.2 ⊆ s}
    have heq : (⋃ b : I, Metric.ball b.val.1 b.val.2) = s := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun b => b.property
      · intro y hy
        obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hs y hy
        exact Set.mem_iUnion.mpr ⟨⟨(y, ε), hsub⟩, Metric.mem_ball_self hε⟩
    obtain ⟨T, hT, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun b : I => Metric.ball b.val.1 b.val.2) (fun _ => Metric.isOpen_ball)
    rw [← heq, ← hcover, Set.preimage_iUnion₂]
    exact MeasurableSet.biUnion hT
      (fun b _ => measurableSet_lt (hg b.val.1) measurable_const)
  apply hcriterion
  intro u
  have hm : Measurable (fun s : Ω × Vec d => f s.1 s.2 - u s.2) :=
    hf.sub ((Lp.stronglyMeasurable u).measurable.comp measurable_snd)
  have hnorm : Measurable
      (fun ω => eLpNorm (fun x => f ω x - u x) 2 volume) := by
    have hformula (ω : Ω) : eLpNorm (fun x => f ω x - u x) 2 volume =
        (∫⁻ x, ‖f ω x - u x‖ₑ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) :=
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        ((hL ω).aestronglyMeasurable.sub (Lp.aestronglyMeasurable u))
    simp_rw [hformula]
    exact ENNReal.continuous_rpow_const.measurable.comp
      ((ENNReal.continuous_rpow_const.measurable.comp hm.enorm).lintegral_prod_right')
  have heq : (fun ω => dist ((hL ω).toLp (f ω)) u) =
      (fun ω => (eLpNorm (fun x => f ω x - u x) 2 volume).toReal) := by
    funext ω
    rw [Lp.dist_def, eLpNorm_congr_ae ((hL ω).coeFn_toLp.sub Filter.EventuallyEq.rfl)]
    rfl
  rw [heq]
  exact hnorm.ennreal_toReal

/-- The compactly supported retained clock initial class is measurable from
the joint local coefficient and clock fields. -/
theorem short_time_clock_retained_initial_measurable {d : ℕ}
    (χ : C(Vec d, ℝ)) (hcompact : HasCompactSupport χ) (U : Set (Vec d))
    (hχ : ∀ x, x ∉ U → χ x = 0) :
    @Measurable (FieldPair d) (Lp ℂ 2 (volume : Measure (Vec d)))
      (EinsteinRelation.localSigma U) (borel _)
      (fun ω => (short_time_clock_retained_initial_memLp χ hcompact ω).toLp
        (fun x => ((ForcedLocality.retainedPair χ ω).2 x : ℂ) - 1)) := by
  have heval : Continuous (fun p : FieldPair d × Vec d => (p.1.2 p.2 : ℂ) - 1) := by
    fun_prop
  have hevalm := heval.measurable
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  have hpair : @Measurable (FieldPair d) (FieldPair d) (EinsteinRelation.localSigma U)
      (borel _) (ForcedLocality.retainedPair χ) :=
    ForcedLocality.measurable_retainedPair χ U hχ
  exact short_time_clock_measurable_toLp _
    (hevalm.comp ((hpair.comp measurable_fst).prodMk measurable_snd))
    (short_time_clock_retained_initial_memLp χ hcompact)

/-- A jointly locally measurable retained clock orbit, represented by the
actual physical evolution wherever the retained coefficients are elliptic. -/
theorem short_time_clock_retained_orbit {d : ℕ}
    (χ : C(Vec d, ℝ)) (hcompact : HasCompactSupport χ) (U : Set (Vec d))
    (hχ : ∀ x, x ∉ U → χ x = 0) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (i : Fin d) (ζ : ℂ) :
    let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      Measurable (Function.uncurry V) ∧
      ∀ ω, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
        ∃ P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexSemigroup
            (fun x => (ForcedLocality.retainedPair χ ω).1 x) i ζ P ∧
          ∀ t, V ω t = P t
            ((short_time_clock_retained_initial_memLp χ hcompact ω).toLp
              (fun x => ((ForcedLocality.retainedPair χ ω).2 x : ℂ) - 1)) := by
  classical
  have hgood := short_time_clock_retained_elliptic_measurable χ U hχ Λ hΛ
  have hinit := short_time_clock_retained_initial_measurable χ hcompact U hχ
  obtain ⟨P, Pdag, hP, _, hPm, _⟩ :=
    short_time_clock_retained_physical_evolution χ U hχ Λ hΛ i ζ
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let good : Set (FieldPair d) :=
    {ω | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ}
  let Ω := {ω : FieldPair d // ω ∈ good}
  let u₀ (ω : FieldPair d) : Lp ℂ 2 (volume : Measure (Vec d)) :=
    (short_time_clock_retained_initial_memLp χ hcompact ω).toLp
      (fun x => ((ForcedLocality.retainedPair χ ω).2 x : ℂ) - 1)
  let V (ω : FieldPair d) (t : ℝ≥0) :=
    if h : ω ∈ good then P ⟨ω, h⟩ t (u₀ ω) else 0
  refine ⟨V, ?_, ?_⟩
  · let s : Set (FieldPair d × ℝ≥0) := {q | q.1 ∈ good}
    have hs : MeasurableSet s := hgood.preimage measurable_fst
    have hv : Measurable (fun q : s => (⟨q.val.1, q.property⟩ : Ω)) :=
      (measurable_subtype_coe.fst).subtype_mk
    have ht : Measurable (fun q : s => q.val.2) := measurable_subtype_coe.snd
    have hu : Measurable (fun q : s => u₀ q.val.1) :=
      hinit.comp measurable_subtype_coe.fst
    exact Measurable.dite (hPm.comp (hv.prodMk (ht.prodMk hu)))
      measurable_const hs
  · intro ω hω
    exact ⟨P ⟨ω, hω⟩, (hP ⟨ω, hω⟩).1, fun t => dite_eq_left hω⟩

/-- The actual clock density is local in every positive neighborhood of zero. -/
private theorem short_time_clock_initial_local {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (μ : Lp ℂ 2 (reducedLaw Q))
    (hμ : IsReducedClockObservation Q μ) (ρ : ℝ) (hρ : 0 < ρ) :
    IsComplexLocalObservation Q ρ μ := by
  have hzero : (0 : Vec d) ∈ {x : Vec d | euclideanNorm x < ρ} := by
    simpa only [Set.mem_ofPred_eq, euclideanNorm, euclideanSq, dot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, Real.sqrt_zero] using hρ
  have heval : Measurable[EinsteinRelation.localSigma
      {x : Vec d | euclideanNorm x < ρ}]
      (fun ω : FieldPair d => (ω.1 0, ω.2 0)) :=
    Measurable.of_comap_le (le_iSup_of_le ⟨0, hzero⟩ le_rfl)
  exact ⟨fun ω => (ω.2 0 : ℂ), Complex.measurable_ofReal.comp heval.snd, hμ.symm⟩

/-- At time zero the clock endpoint has exactly zero projection error, on any
of the finite-p carriers in the target and for any positive radius. -/
theorem short_time_clock_initial_projection_error {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (μ : Lp ℂ 2 (reducedLaw Q))
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : P 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (reducedLaw Q)))
    (ρ : ℝ) (hρ : 0 < ρ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (E : Lp ℂ p (reducedLaw Q))
    (hE : (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] clockEndpoint Q ζ P μ 0) :
    ‖E - EndpointProjection.project
      (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ = 0 := by
  have hlocal : IsComplexLocalObservation Q ρ (clockEndpoint Q ζ P μ 0) := by
    obtain ⟨v, hv, hve⟩ := isComplexLocal_centered Q
      (short_time_clock_initial_local Q μ hμ ρ hρ)
    rw [clockEndpoint, hP, ContinuousLinearMap.id_apply]
    exact ⟨fun ω => ζ • v ω, hv.const_smul ζ,
      (hve.const_smul ζ).trans (Lp.coeFn_smul ζ _).symm⟩
  have hb := EndpointLocalization.norm_sub_project_le Q ρ E
    (clockEndpoint Q ζ P μ 0) (clockEndpoint Q ζ P μ 0) hE hlocal
    (ε := 0) le_rfl (Filter.Eventually.of_forall (fun ω => by rw [sub_self, norm_zero]))
  exact le_antisymm (by simpa only [mul_zero] using hb) (norm_nonneg _)

/- Pending exact task; this comment is not a declaration or proof claim.
theorem endpoint_short_time_clock_projection_of_graph_deps :
∀ (hA : node_stationary_u2D_analytic_u2D_semigroupStmt) (hlocal : node_e_u3A_forced_u2D_localityStmt),
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ),
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → (t : ℝ) ≤ 1 → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q (Sum.inr false) ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2)
-/

end EinsteinFull.Blueprint
