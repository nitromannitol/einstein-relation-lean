import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_generator_u23_pathwise
import EinsteinFull.Calculus.C16FoundationInstantiation
import EinsteinFull.Calculus.C16InverseClockFamily
import EinsteinFull.Calculus.C16RegularTimeChange
import EinsteinFull.Calculus.U5RegularPhysicalOccupation
import EinsteinFull.Calculus.U5RegularStoppingRestart
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinFull.Calculus.U3ForcedHorizonLaw
import EinsteinFull.Work.W1.StoppedLawReconstructionSupport
import EinsteinRelation.Regeneration.RenewalCarriers
import EinsteinRelation.Environment.SourceReducedBoundSupport
import MarkovProcess.Path.Polish
import MarkovProcess.Path.MeasureIdentification

/-! Construction of the actual reduced law and its physical inverse-clock image. -/

open MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Regeneration

/-- A measurable reduced solution family and its physical inverse-clock image,
with the literal clock identity holding simultaneously at every time. -/
theorem suna_s2_pathwise_construct (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) :
    ∃ PX PY : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) ∧
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω))) ∧
      (∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
        PX (0, ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
          (PY (0, ω)) ∧
        ∀ᵐ γ ∂PY (0, ω), ∀ t : ℝ≥0,
          Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω
            (Clock.physicalPathClock ω γ t) = γ t) := by
  obtain ⟨PY, hY⟩ := c16_reduced_mp_exists d hd Λ₀ r₀ Q i lam
  obtain ⟨PX, hPX⟩ := c16_inverse_clock_quenched_family_of_reduced_mp
    d Λ₀ r₀ Q i lam PY hY
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  refine ⟨PX, PY, ?_, hY, ?_⟩
  · filter_upwards [Q.regular, hY, hPX] with ω hω hYω hPXω
    rw [hPXω hω]
    exact c16_time_change_solves_of_regular hΛ hω i lam 0 hYω
  · filter_upwards [hPX] with ω hPXω hω
    refine ⟨hPXω hω, Filter.Eventually.of_forall fun γ t => ?_⟩
    exact Clock.InverseMeaningV3.inverseClockPath_atPhysicalClock ω γ Λ₀ hω t

/-- Actual reduced and physical solution families related by the inverse clock. -/
theorem s2_reduced_physical_inverse_clock_pair
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (lam : ℝ) :
    ∃ PX PY : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0,ω))) ∧
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0,ω))) ∧
      ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ ω,
        PX (0,ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω) (PY (0,ω)) := by
  obtain ⟨PX, PY, hPX, hPY, hclock⟩ := suna_s2_pathwise_construct d hd Λ r Q i lam
  refine ⟨PX, PY, hPX, hPY, ?_⟩
  filter_upwards [hclock] with ω hω hregular
  exact (hω hregular).1

/-- A supplied physical solution family has a measurable reduced clock partner. -/
theorem s2_supplied_physical_family_has_measurable_reduced_clock_partner
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (lam : ℝ) (PX : QuenchedPathLaws d)
    (hX : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0,ω))) :
    ∃ PY : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0,ω))) ∧
      ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ ω,
        PX (0,ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω)
          (PY (0,ω)) := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0) with ⟨n, rfl⟩
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨PY, hPY⟩ := exists_forwardKernel (d := n + 1) Λ PX
  refine ⟨PY, ?_, ?_⟩
  · filter_upwards [Q.regular, hX] with ω hω hXω
    rw [hPY ω hω hXω.1]
    exact u5_forwardClock_solves hΛ hω i lam 0 hXω
  · filter_upwards [hX] with ω hXω hω
    rw [hPY ω hω hXω.1,
      Measure.map_map (measurable_inverseClockPath_fixed ω Λ hω)
        (measurable_forwardClockPath hω)]
    have hid : (fun γ : Path (n + 1) => Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω) ∘
        forwardClockPath hω = id := funext fun γ => inverseClockPath_forwardClockPath hω γ
    rw [hid, Measure.map_id]

/-- The pathwise statement follows from uniqueness for the actual supplied
physical solution families. This isolates the remaining uniqueness obligation. -/
theorem s2_pathwise_of_physical_family_uniqueness
    (huniq : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ)
      (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ)
      (PX PX' : QuenchedPathLaws d),
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) →
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))) →
      ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω)) :
    Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt := by
  intro d hd Λ r Q i lam
  obtain ⟨PX, PY, hX, hY, _⟩ := suna_s2_pathwise_construct d hd Λ r Q i lam
  refine ⟨⟨PX, PY, hX, hY⟩, ?_⟩
  intro PX PY hX hY
  obtain ⟨PZ, hZ⟩ := c16_inverse_clock_quenched_family_of_reduced_mp d Λ r Q i lam PY hY
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hPZ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PZ (0, ω)) := by
    filter_upwards [Q.regular, hY, hZ] with ω hω hYω hZω
    rw [hZω hω]
    exact c16_time_change_solves_of_regular hΛ hω i lam 0 hYω
  filter_upwards [huniq d hd Λ r Q i lam PX PZ hX hPZ, hZ] with ω heq hZω hω
  refine ⟨heq.trans (hZω hω), Filter.Eventually.of_forall fun γ t => ?_⟩
  exact Clock.InverseMeaningV3.inverseClockPath_atPhysicalClock ω γ Λ hω t

/-- The canonical finite-dimensional laws solve the textbook physical problem
at every starting point, with the same path law throughout. -/
theorem s2_canonical_FDD_law_solves_physical_textbook_mp
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) :
    SolvesMartingaleProblem
      (External.Draft.svGenerator (⇑ω.1)
        (physicalDrift ω (firstCoordinateIndex hd) lam)) x (K x) := by
  have hmarg (t : ℝ≥0) (ht : 0 < t) :
      (K x).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
    rw [Blueprint.k11_endpoint _ K hfdd]
    exact u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht x
  have hocc := u2_averaged_occupation_ac_of_marginals (K x) hmarg
  exact c4_textbook_solves_of_physical_and_averaged_occupation
    (lt_of_lt_of_le zero_lt_one hΛ) hω (firstCoordinateIndex hd) lam
    (u5_regular_same_FDD_physical_MP_all_real hd ω lam Λ hΛ hω K hfdd x) hocc

/-- The canonical finite-dimensional path law solves the textbook physical
martingale problem at each starting point. -/
theorem s2_finish_canonical_FDD_law_solves_physical_textbook_mp
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) :
    SolvesMartingaleProblem
      (External.Draft.svGenerator (⇑ω.1)
        (physicalDrift ω (firstCoordinateIndex hd) lam)) x (K x) :=
  s2_canonical_FDD_law_solves_physical_textbook_mp hd ω lam Λ hΛ hω K hfdd x

/-- The same supplied realization solves the textbook physical martingale
problem at every starting point. -/
theorem s2_supplied_gmp_solves_physical_textbook_mp
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (x : Vec d) :
    SolvesMartingaleProblem
      (External.Draft.svGenerator (⇑ω.1)
        (physicalDrift ω (firstCoordinateIndex hd) lam)) x (r.pathLaw x) := by
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  exact s2_finish_canonical_FDD_law_solves_physical_textbook_mp hd ω lam Λ hΛ hω
    r.pathLaw (u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r) x

/-- Equal coefficient and potential fields on an open set have equal physical
    drifts there, including the derivative of the reduced coefficient. -/
theorem s2_physicalDrift_eq_on_open {d : ℕ} (ω ω' : FieldPair d)
    (i : Fin d) (lam : ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (x : Vec d) (hx : x ∈ U) :
    physicalDrift ω i lam x = physicalDrift ω' i lam x := by
  have hred : (reducedCoefficient ω) =ᶠ[𝓝 x] (reducedCoefficient ω') := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [reducedCoefficient, clockDensity, (hag y hy).1, (hag y hy).2]
  have hclock : clockDensity ω x = clockDensity ω' x := by
    simp only [clockDensity, (hag x hx).2]
  have hder (k j : Fin d) :
      coordinateDerivative k (fun y => reducedCoefficient ω y k j) x =
        coordinateDerivative k (fun y => reducedCoefficient ω' y k j) x := by
    have he : (fun y => reducedCoefficient ω y k j) =ᶠ[𝓝 x]
        (fun y => reducedCoefficient ω' y k j) :=
      hred.mono fun y hy => congrArg (fun a => a k j) hy
    simp only [coordinateDerivative, he.fderiv_eq]
  funext j
  simp only [physicalDrift, forcedDrift, matrixDivDrift, hclock,
    hred.self_of_nhds, hder]

/-- The textbook physical generators coincide where both fields agree. -/
theorem s2_physical_textbook_generator_eq_on_open {d : ℕ}
    (ω ω' : FieldPair d) (i : Fin d) (lam : ℝ)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (x : Vec d) (hx : x ∈ U) (f : Vec d → ℝ) :
    External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f x =
      External.Draft.svGenerator (⇑ω'.1) (physicalDrift ω' i lam) f x := by
  simp only [External.Draft.svGenerator, (hag x hx).1,
    s2_physicalDrift_eq_on_open ω ω' i lam U hU hag x hx]


/-- The physical textbook compensators agree on any path segment that stays
in the common region before its endpoint. The endpoint has zero time mass. -/
theorem s2_physical_textbook_compensatedTest_eq_of_stays {d : ℕ}
    (ω ω' : FieldPair d) (i : Fin d) (lam : ℝ)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (f : Vec d → ℝ) (γ : Path d) (T : ℝ≥0)
    (hstay : ∀ t : ℝ≥0, t < T → γ t ∈ U) :
    compensatedTest (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) f T γ =
      compensatedTest (External.Draft.svGenerator (⇑ω'.1) (physicalDrift ω' i lam)) f T γ := by
  have hi : (∫ u in (0 : ℝ)..(T : ℝ),
      External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f (γ u.toNNReal)) =
      ∫ u in (0 : ℝ)..(T : ℝ),
        External.Draft.svGenerator (⇑ω'.1) (physicalDrift ω' i lam) f (γ u.toNNReal) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (T : ℝ)] with u hu huI
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ (T : ℝ) from T.prop)] at huI
    have huT : u < (T : ℝ) := lt_of_le_of_ne huI.2 hu
    have huNN : u.toNNReal < T := by
      exact_mod_cast (show (u.toNNReal : ℝ) < (T : ℝ) by
        rw [Real.coe_toNNReal u huI.1.le]
        exact huT)
    exact s2_physical_textbook_generator_eq_on_open ω ω' i lam U hU hag
      (γ u.toNNReal) (hstay _ huNN) f
  simp only [compensatedTest, hi]


/-- The two textbook compensated processes agree after stopping at any finite
path-dependent time that does not pass the first exit from the common region. -/
theorem s2_physical_textbook_compensatedTest_eq_at_local_stop {d : ℕ}
    (ω ω' : FieldPair d) (i : Fin d) (lam : ℝ)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (f : Vec d → ℝ) (γ : Path d) (τ t : ℝ≥0)
    (hstay : ∀ u : ℝ≥0, u < τ → γ u ∈ U) :
    compensatedTest (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) f (min t τ) γ =
      compensatedTest (External.Draft.svGenerator (⇑ω'.1) (physicalDrift ω' i lam)) f (min t τ) γ := by
  apply s2_physical_textbook_compensatedTest_eq_of_stays ω ω' i lam U hU hag f γ
  intro u hu
  exact hstay u (lt_of_lt_of_le hu (min_le_right _ _))

/-- Appending paths varies continuously with the finite joining time and both
paths. This is the path-space map needed for random-time continuation. -/
theorem s2_continuous_appendPaths_at_variable_time {d : ℕ} :
    Continuous (fun q : ℝ≥0 × Path d × Path d => u3AppendPaths q.1 q.2.1 q.2.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (((continuous_fst.snd.fst).eval (continuous_snd.min continuous_fst.fst)).add
    ((continuous_fst.snd.snd).eval (continuous_snd.sub continuous_fst.fst))).sub
      ((continuous_fst.snd.snd).eval continuous_const)

/-- Killed finite-dimensional laws determine the stopped path law. -/
theorem s2_supplied_stopped_locality_of_killed_fdd
    {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (μ ν : Measure (Path d)) [IsFiniteMeasure ν]
    (hkilled : ∀ I : Finset ℕ,
      μ.map (fun γ => I.restrict (localityKilledTrace U γ)) =
      ν.map (fun γ => I.restrict (localityKilledTrace U γ))) :
    μ.map (Diffusion.localityStoppedPath U) = ν.map (Diffusion.localityStoppedPath U) :=
  map_localityStoppedPath_eq_of_killedTrace_fdd_eq U hU μ ν hkilled

/-- The missing comparison of killed observations for the actual supplied laws. -/
def S2SuppliedKilledFDDLocality : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
    (U : Set (Vec d)), IsOpen U →
    (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
    ∀ x ∈ U, ∀ I : Finset ℕ,
      (r.pathLaw x).map (fun γ => I.restrict (localityKilledTrace U γ)) =
      (r'.pathLaw x).map (fun γ => I.restrict (localityKilledTrace U γ))

/-- Conditional comparison for supplied laws on an arbitrary open set. -/
theorem s2_supplied_stopped_locality_of_generic_killed_fdd
    (hk : S2SuppliedKilledFDDLocality)
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hfields : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (x : Vec d) (hx : x ∈ U) :
    (r.pathLaw x).map (Diffusion.localityStoppedPath U) =
      (r'.pathLaw x).map (Diffusion.localityStoppedPath U) := by
  letI : IsMarkovKernel r'.pathLaw := r'.pathLaw_isMarkovKernel
  exact s2_supplied_stopped_locality_of_killed_fdd U hU _ _
    (hk hd Λ hΛ ω ω' hω hω' lam h0 h1 r r' U hU hfields x hx)

/-- The literal divergence-form physical generator is local on open sets. -/
theorem s2_physical_generator_eq_on_open
    {d : ℕ} (i : Fin d) (lam : ℝ) (ω ω' : FieldPair d)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (f : Vec d → ℝ) (x : Vec d) (hx : x ∈ U) :
    physicalGenerator i ω lam f x = physicalGenerator i ω' lam f x := by
  have hred : (reducedCoefficient ω) =ᶠ[𝓝 x] (reducedCoefficient ω') := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [reducedCoefficient, clockDensity, (hag y hy).1, (hag y hy).2]
  have hdiv : divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x =
      divergence (fun y => (reducedCoefficient ω' y).mulVec (gradient f y)) x := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro k hk
    have he : (fun y => ((reducedCoefficient ω y).mulVec (gradient f y)) k) =ᶠ[𝓝 x]
        (fun y => ((reducedCoefficient ω' y).mulVec (gradient f y)) k) :=
      hred.mono fun y hy => by
        change ((reducedCoefficient ω y).mulVec (gradient f y)) k =
          ((reducedCoefficient ω' y).mulVec (gradient f y)) k
        rw [hy]
    simp only [coordinateDerivative, he.fderiv_eq]
  simp only [physicalGenerator, (hag x hx).1, (hag x hx).2, hdiv]



/-- Before exit, the physical generator integrals agree along the same path. -/
theorem s2_physical_local_generator_integral_eq_before_exit
    {d : ℕ} (i : Fin d) (ω ω' : FieldPair d) (lam : ℝ)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (f : Vec d → ℝ) (γ : Path d) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < Diffusion.localityExitTime U γ) :
    (∫ s in (0 : ℝ)..(t : ℝ), physicalGenerator i ω lam f (γ s.toNNReal)) =
      ∫ s in (0 : ℝ)..(t : ℝ), physicalGenerator i ω' lam f (γ s.toNNReal) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with s hs
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.prop)] at hs
  have hst : s.toNNReal ≤ t := by
    exact_mod_cast (show (s.toNNReal : ℝ) ≤ (t : ℝ) by
      rw [Real.coe_toNNReal s hs.1.le]
      exact hs.2)
  exact s2_physical_generator_eq_on_open i lam ω ω' U hU hag f _
    ((lt_localityExitTime_iff U hU γ t).mp ht _ hst)

/-- Physical generator integrals agree up to a finite stop bounded by exit. -/
theorem s2_physical_local_generator_integral_eq_at_stop
    {d : ℕ} (i : Fin d) (ω ω' : FieldPair d) (lam : ℝ)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (f : Vec d → ℝ) (γ : Path d) (τ t : ℝ≥0)
    (hτ : (τ : ℝ≥0∞) ≤ Diffusion.localityExitTime U γ) :
    (∫ s in (0 : ℝ)..((min t τ : ℝ≥0) : ℝ),
      physicalGenerator i ω lam f (γ s.toNNReal)) =
      ∫ s in (0 : ℝ)..((min t τ : ℝ≥0) : ℝ),
        physicalGenerator i ω' lam f (γ s.toNNReal) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne ((min t τ : ℝ≥0) : ℝ)] with s hs hsI
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ ((min t τ : ℝ≥0) : ℝ) from (min t τ).prop)] at hsI
  have hst : s.toNNReal < min t τ := by
    exact_mod_cast (show (s.toNNReal : ℝ) < ((min t τ : ℝ≥0) : ℝ) by
      rw [Real.coe_toNNReal s hsI.1.le]
      exact lt_of_le_of_ne hsI.2 hs)
  have hexit : (s.toNNReal : ℝ≥0∞) < Diffusion.localityExitTime U γ :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr (lt_of_lt_of_le hst (min_le_right _ _))) hτ
  exact s2_physical_generator_eq_on_open i lam ω ω' U hU hag f _
    ((lt_localityExitTime_iff U hU γ s.toNNReal).mp hexit _ le_rfl)

/-- The physical generator integrals agree up to the actual exit stop. -/
theorem s2_physical_local_generator_integral_eq_at_exit_stop
    {d : ℕ} (i : Fin d) (ω ω' : FieldPair d) (lam : ℝ)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (f : Vec d → ℝ) (γ : Path d) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(((min (t : ℝ≥0∞) (Diffusion.localityExitTime U γ)).toNNReal : ℝ)),
      physicalGenerator i ω lam f (γ s.toNNReal)) =
      ∫ s in (0 : ℝ)..(((min (t : ℝ≥0∞) (Diffusion.localityExitTime U γ)).toNNReal : ℝ)),
        physicalGenerator i ω' lam f (γ s.toNNReal) := by
  let T := (min (t : ℝ≥0∞) (Diffusion.localityExitTime U γ)).toNNReal
  have hT : (T : ℝ≥0∞) ≤ Diffusion.localityExitTime U γ := by
    dsimp only [T]
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  simpa only [min_self] using
    s2_physical_local_generator_integral_eq_at_stop i ω ω' lam U hU hag f γ T T hT


end EinsteinFull
