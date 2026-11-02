import EinsteinFull.Calculus.SbxS4KilledRegularityR02
import EinsteinFull.Work.W1.PhysicalCompactMollificationSupport
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3TubeProbability

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open SubdiffusiveProcess
open EinsteinFull.Blueprint.TubeProbability

/-- On a bounded region, the literal zero extension of each physical graph
coordinate belongs to unweighted L² on the whole space. -/
theorem s9_zeroBoundary_zeroExtension_memLp
    {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (U K : Set (Vec d))
    (hU : MeasurableSet U) (hK : IsCompact K) (hUK : U ⊆ K)
    (u : physicalH1ZeroBoundary U hd lam) :
    MemLp (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value) 2 volume ∧
      ∀ i, MemLp (U.indicator (fun x =>
        (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i))
        2 volume := by
  let g := physicalH1SpaceRepresentative hd lam u.1
  have hzero (f : Vec d → ℝ) :
      ∀ᵐ x ∂(volume : Measure (Vec d)), x ∉ K → U.indicator f x = 0 := by
    filter_upwards with x hx
    exact Set.indicator_of_notMem (fun h => hx (hUK h)) _
  constructor
  · apply (memLp_physicalForceMeasure_iff_of_ae_zero_off_compact
      (firstCoordinateIndex hd) lam hK (hzero g.value)).mp
    exact g.value_memLp.indicator hU
  · intro i
    apply (memLp_physicalForceMeasure_iff_of_ae_zero_off_compact
      (firstCoordinateIndex hd) lam hK (hzero (fun x => (WithLp.ofLp (g.weakGradient x)) i))).mp
    let T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin d => ℝ) i
    have hcoord : MemLp (fun x => T (g.weakGradient x)) 2
        (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam) :=
      g.gradient_memLp.continuousLinearMap_comp T
    change MemLp (fun x => (WithLp.ofLp (g.weakGradient x)) i) 2 _ at hcoord
    exact hcoord.indicator hU

/-- The physical zero extension defines an unweighted cube Sobolev graph,
with both the value and each Euclidean gradient coordinate preserved. -/
theorem s9_zeroBoundary_cube_weakGraph
    {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (U K : Set (Vec d))
    (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    (u : physicalH1ZeroBoundary U hd lam) (Ω : TopologicalSpace.Opens (SpatialCoordinates d)) :
    ∃ v : weakSobolevGraph Ω,
      v.val.1 =ᵐ[volume.restrict Ω]
        U.indicator (physicalH1SpaceRepresentative hd lam u.1).value ∧
      ∀ i, v.val.2 i =ᵐ[volume.restrict Ω]
        U.indicator (fun x =>
          (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i) := by
  let f := U.indicator (physicalH1SpaceRepresentative hd lam u.1).value
  let G := U.indicator (fun x => WithLp.ofLp
    ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
  have hmem := s9_zeroBoundary_zeroExtension_memLp hd lam U K hU.measurableSet hK hUK u
  have hGi (i : Fin d) : (fun x => G x i) = U.indicator (fun x =>
      (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i) := by
    funext x
    by_cases hx : x ∈ U <;> simp [G, hx]
  have hg : ∀ i, MemLp (fun x => G x i) 2 volume := by
    intro i
    rw [hGi i]
    exact hmem.2 i
  have hw : HasWeakGradient Set.univ f G :=
    s4_zeroBoundary_representative_zero_extension hd lam U u
  refine ⟨cubeGraphOfGlobalWeakGradient Ω f G hmem.1 hg hw, ?_, ?_⟩
  · exact (cubeGraphOfGlobalWeakGradient_coe Ω f G hmem.1 hg hw).1
  · intro i
    have hi := (cubeGraphOfGlobalWeakGradient_coe Ω f G hmem.1 hg hw).2 i
    rw [hGi i] at hi
    exact hi

/-- The actual killed resolvent is the unique physical variational resolvent on
its completed zero-boundary graph. The force in this representation is the
nonnegative auxiliary force used by the killed realization. -/
theorem s9_killed_resolvent_eq_physical_variational
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryValue U hd ω lam L hω
      (physicalZeroBoundaryResolvent U hd ω lam L (μ : ℝ) hL hω μ.property
        f.val (Lp.memLp f.val)) = (gmpKilledInteriorResolvent r U hU μ f).val := by
  obtain ⟨u, hu, _, heq⟩ :=
    s4_killed_resolvent_weighted_equation_and_trace r U hU μ f
  have hspec : HasPhysicalZeroBoundaryResolvent U ω hd lam μ f.val u := by
    refine ⟨μ.property, fun v => ?_⟩
    have hmass : (∫ x, s4PhysicalRho hd ω lam x *
        (gmpKilledInteriorResolvent r U hU μ f).val x *
        physicalZeroBoundaryValue U hd ω lam L hω v x) =
        ∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
          ∂physicalReversibleMeasure ω hd lam := by
      rw [Work.W5.gantert_integral_physicalMeasure]
      apply integral_congr_ae
      filter_upwards [physicalZeroBoundaryValue_ae_eq_volume U hd ω lam L hω u,
        physicalZeroBoundaryValue_ae_eq_volume U hd ω lam L hω v] with x hx hy
      rw [hu] at hx
      rw [hx, hy]
      simp only [s4PhysicalRho]
      ring
    have hforce : (∫ x, s4PhysicalRho hd ω lam x * f.val x *
        physicalZeroBoundaryValue U hd ω lam L hω v x) =
        ∫ x, f.val x * densityWeightedH1SpaceValue v.1 x
          ∂physicalReversibleMeasure ω hd lam := by
      rw [Work.W5.gantert_integral_physicalMeasure]
      apply integral_congr_ae
      filter_upwards [physicalZeroBoundaryValue_ae_eq_volume U hd ω lam L hω v] with x hx
      rw [hx]
      simp only [s4PhysicalRho]
      ring
    have hh := heq v
    rw [← s4_physical_form_lebesgue, hmass, hforce] at hh
    linarith only [hh]
  have hunique := (physicalZeroBoundaryResolvent_existsUnique U hd ω lam L μ hL hω
    μ.property f.val (Lp.memLp f.val)).unique hspec
    (physicalZeroBoundaryResolvent_spec U hd ω lam L μ hL hω μ.property
      f.val (Lp.memLp f.val))
  rw [← hunique]
  exact hu

/-- The killed resolvent agrees with the physical L² resolvent operator. -/
theorem s9_killed_resolvent_eq_physical_resolventL2
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryResolventL2 U hd ω lam L μ hL hω μ.property f.val =
      (gmpKilledInteriorResolvent r U hU μ f).val := by
  have hf : (Lp.memLp f.val).toLp f.val = f.val := by
    apply Lp.ext
    exact (Lp.memLp f.val).coeFn_toLp
  have hgraph := physicalZeroBoundaryResolventGraph_toLp U hd ω lam L μ hL hω
    μ.property f.val (Lp.memLp f.val)
  rw [hf] at hgraph
  change physicalZeroBoundaryValue U hd ω lam L hω
    (physicalZeroBoundaryResolventGraph U hd ω lam L μ hL hω μ.property f.val) = _
  rw [hgraph]
  exact s9_killed_resolvent_eq_physical_variational r U hU μ f

/-- The same physical identification applies to either sign of the force,
using its absolute value in the fixed-environment realization. -/
theorem s9_killed_resolvent_eq_physical_variational_abs
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    (lam : ℝ) (hpos : 0 < |lam|) (hbound : |lam| ≤ 1)
    (r : GantertFixedEnvironmentRealization hd L hL ω hω |lam|
      (le_of_lt hpos) hbound)
    (U : Set (Vec d)) (hU : IsOpen U)
    (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω |lam| L hω) :
    physicalZeroBoundaryValue U hd ω |lam| L hω
      (physicalZeroBoundaryResolvent U hd ω |lam| L (μ : ℝ) hL hω μ.property
        f.val (Lp.memLp f.val)) = (gmpKilledInteriorResolvent r U hU μ f).val :=
  s9_killed_resolvent_eq_physical_variational r U hU μ f

end EinsteinFull
