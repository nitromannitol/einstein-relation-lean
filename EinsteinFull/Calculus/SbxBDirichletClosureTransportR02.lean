import EinsteinFull.Work.W1.PhysicalCompactMollificationSupport
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3TubeProbability

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open SubdiffusiveProcess

noncomputable section

/-- On the actual source ball Lebesgue measure is dominated by a finite
multiple of the whole-space physical force measure, for either force sign. -/
theorem sbxB_ball_volume_le_physicalForce {d : ℕ} (hd : 2 ≤ d)
    (lam R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      volume.restrict (sourceBall (0 : Vec d) R) ≤
        C • External.GantertSection7Support.physicalForceMeasure hd lam := by
  let K : Set (Vec d) := Metric.closedBall 0 (2 * R)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hBK : sourceBall (0 : Vec d) R ⊆ K := by
    intro x hx
    have hx' := sourceBall_subset_cube R hR hx
    change dist x (0 : Vec d) < 2 * R / 2 at hx'
    change dist x (0 : Vec d) ≤ 2 * R
    linarith
  obtain ⟨c, _, hc, _, hlo, _⟩ :=
    physicalForceMeasure_compact_comparison (firstCoordinateIndex hd) lam hK
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hc)
  have hreverse : volume.restrict K ≤
      (c : ℝ≥0∞)⁻¹ • (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam).restrict K := by
    apply Measure.le_iff.mpr
    intro S hS
    have h := mul_le_mul_right (Measure.le_iff.mp hlo S hS) (c : ℝ≥0∞)⁻¹
    simpa only [Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul] using h
  refine ⟨(c : ℝ≥0∞)⁻¹, by simp [hc0], ?_⟩
  calc
    _ ≤ volume.restrict K := Measure.restrict_mono_set volume hBK
    _ ≤ (c : ℝ≥0∞)⁻¹ • (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam).restrict K := hreverse
    _ ≤ (c : ℝ≥0∞)⁻¹ • External.GantertSection7Support.physicalForceMeasure hd lam :=
      by gcongr; exact Measure.restrict_le_self

/-- The value projection in the physical weighted graph norm. -/
@[nolint defsWithUnderscore]
def sbxB_physicalValueMap {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    PhysicalH1Space hd lam →L[ℝ]
      Lp ℝ 2 (External.GantertSection7Support.physicalForceMeasure hd lam) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap.comp
      (densityWeightedH1Submodule (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)).subtypeL)

/-- The full Euclidean gradient projection in the physical weighted graph norm. -/
@[nolint defsWithUnderscore]
def sbxB_physicalGradientMap {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    PhysicalH1Space hd lam →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2
        (External.GantertSection7Support.physicalForceMeasure hd lam) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap.comp
      (densityWeightedH1Submodule (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)).subtypeL)

/-- Restriction to the same ball is a continuous graph map. It retains the
literal weighted value and all Euclidean weak-gradient coordinates. -/
theorem sbxB_exists_physicalToBallGraph {d : ℕ} (hd : 2 ≤ d)
    (lam R : ℝ) (hR : 0 < R) :
    ∃ F : PhysicalH1Space hd lam →L[ℝ] SobolevData (dirichletBall (d := d) R),
      (∀ u, (F u).1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        densityWeightedH1SpaceValue u) ∧
      (∀ u i, (F u).2 i =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u).weakGradient x)) i)) := by
  obtain ⟨C, hC, hbound⟩ := sbxB_ball_volume_le_physicalForce hd lam R hR
  let L : Lp ℝ 2 (External.GantertSection7Support.physicalForceMeasure hd lam) →L[ℝ]
      Lp ℝ 2 (volume.restrict (sourceBall (0 : Vec d) R)) :=
    Lp.LpToLpOfMeasureLeSMul hC hbound
  let P (i : Fin d) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin d => ℝ) i
  let F : PhysicalH1Space hd lam →L[ℝ] SobolevData (dirichletBall (d := d) R) :=
    (L.comp (sbxB_physicalValueMap hd lam)).prod
      (ContinuousLinearMap.pi fun i =>
        L.comp ((P i).compLpL 2 _ |>.comp (sbxB_physicalGradientMap hd lam)))
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪
      External.GantertSection7Support.physicalForceMeasure hd lam :=
    Measure.absolutelyContinuous_of_le_smul hbound
  refine ⟨F, ?_, ?_⟩
  · intro u
    exact Lp.coeFn_LpToLpOfMeasureLeSMul hC hbound _
  · intro u i
    have hg : (physicalH1SpaceRepresentative hd lam u).weakGradient =ᵐ[
        External.GantertSection7Support.physicalForceMeasure hd lam]
        densityWeightedH1SpaceGradient u := by
      have he : (physicalH1SpaceRepresentative hd lam u).gradient_memLp.toLp
          (physicalH1SpaceRepresentative hd lam u).weakGradient =
            densityWeightedH1SpaceGradient u :=
        congrArg Prod.snd (physicalH1SpaceRepresentative_pair hd lam u)
      exact (physicalH1SpaceRepresentative hd lam u).gradient_memLp.coeFn_toLp.symm.trans
        (Filter.EventuallyEq.of_eq (congrArg
          (fun f : Lp (EuclideanSpace ℝ (Fin d)) 2
              (External.GantertSection7Support.physicalForceMeasure hd lam) =>
            (f : Vec d → EuclideanSpace ℝ (Fin d))) he))
    have hproj := hac.ae_eq ((P i).coeFn_compLp (sbxB_physicalGradientMap hd lam u))
    have hrep := hac.ae_eq hg
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hC hbound
      ((P i).compLp (sbxB_physicalGradientMap hd lam u)), hproj, hrep] with x hx hp hr
    change (L ((P i).compLp (sbxB_physicalGradientMap hd lam u))) x =
      (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u).weakGradient x)) i
    rw [hx, hp, hr]
    rfl

/-- Restriction sends the physical smooth-core closure into the closure of the
same smooth tests on the source ball. -/
theorem sbxB_exists_physicalToKilledGraph {d : ℕ} (hd : 2 ≤ d)
    (lam R : ℝ) (hR : 0 < R) :
    ∃ F : PhysicalH1Space hd lam →L[ℝ] SobolevData (dirichletBall (d := d) R),
      (∀ u, (F u).1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        densityWeightedH1SpaceValue u) ∧
      (∀ u i, (F u).2 i =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u).weakGradient x)) i)) ∧
      ∀ u ∈ physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam,
        F u ∈ killedSobolevGraph (dirichletBall R) := by
  obtain ⟨F, hvalue, hgrad⟩ := sbxB_exists_physicalToBallGraph hd lam R hR
  obtain ⟨C, hC, hbound⟩ := sbxB_ball_volume_le_physicalForce hd lam R hR
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪
      External.GantertSection7Support.physicalForceMeasure hd lam :=
    Measure.absolutelyContinuous_of_le_smul hbound
  have hrep (u : PhysicalH1Space hd lam) :
      (physicalH1SpaceRepresentative hd lam u).weakGradient =ᵐ[
        volume.restrict (sourceBall (0 : Vec d) R)] densityWeightedH1SpaceGradient u := by
    apply hac.ae_eq
    have he : (physicalH1SpaceRepresentative hd lam u).gradient_memLp.toLp
        (physicalH1SpaceRepresentative hd lam u).weakGradient =
          densityWeightedH1SpaceGradient u :=
      congrArg Prod.snd (physicalH1SpaceRepresentative_pair hd lam u)
    exact (physicalH1SpaceRepresentative hd lam u).gradient_memLp.coeFn_toLp.symm.trans
      (Filter.EventuallyEq.of_eq (congrArg
        (fun f : Lp (EuclideanSpace ℝ (Fin d)) 2
          (External.GantertSection7Support.physicalForceMeasure hd lam) =>
          (f : Vec d → EuclideanSpace ℝ (Fin d))) he))
  have htest (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall (0 : Vec d) R) φ) :
      F (physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1) =
        smoothSobolevData (Ω := dirichletBall R) ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩ := by
    let ψ : TestFunction (dirichletBall (d := d) R) ℝ ⊤ := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
    change F (physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1) = smoothSobolevData ψ
    apply Prod.ext
    · apply Lp.ext
      exact (hvalue _).trans ((hac.ae_eq
        (physicalH1SmoothTest_value hd lam φ hφ.1 hφ.2.1)).trans
          (testL2_coeFn ψ).symm)
    · funext i
      apply Lp.ext
      refine (hgrad _ i).trans ?_
      filter_upwards [hrep (physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1),
        hac.ae_eq (physicalH1SmoothTest_gradient hd lam φ hφ.1 hφ.2.1),
        testPartialL2_coeFn ψ i] with x hr hs ht
      change (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam
        (physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1)).weakGradient x)) i =
          testPartialL2 ψ i x
      rw [hr, hs, ht]
      rfl
  refine ⟨F, hvalue, hgrad, ?_⟩
  have hc : IsClosed (((killedSobolevGraph (dirichletBall (d := d) R)).comap
      F.toLinearMap : Submodule ℝ (PhysicalH1Space hd lam)) : Set (PhysicalH1Space hd lam)) :=
    isClosed_killedSobolevGraph.preimage F.continuous
  have hcore : physicalH1SmoothCore (sourceBall (0 : Vec d) R) hd lam ≤
      (killedSobolevGraph (dirichletBall R)).comap F.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨φ, hφ, rfl⟩
    apply Submodule.mem_comap.mpr
    rw [show F.toLinearMap (physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1) =
      smoothSobolevData (Ω := dirichletBall R) ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩ from htest φ hφ]
    exact smoothSobolevData_mem_killed _
  intro u hu
  exact (Submodule.topologicalClosure_minimal _ hcore hc) hu

/-- Every physical zero-boundary vector yields a Dirichlet completion vector
with the same scalar value and every Euclidean gradient coordinate on the ball. -/
theorem sbxB_exists_dirichletHilbert_of_physicalZeroBoundary {d : ℕ}
    (hd : 2 ≤ d) (lam R : ℝ) (hR : 0 < R)
    (u : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam) :
    ∃ v : DirichletHilbertSpace (d := d) R hR,
      densityWeightedH1SpaceValue u.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        (fun x => v.val none x) ∧
      ∀ i : Fin d,
        (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i)
          =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => v.val (some i) x) := by
  obtain ⟨F, hvalue, hgrad, hkilled⟩ := sbxB_exists_physicalToKilledGraph hd lam R hR
  obtain ⟨w, hw, hwg⟩ := exists_nativeH10Function_of_killedSobolevGraph
    ⟨F u.1, hkilled u.1 u.2⟩
  obtain ⟨v, hv, hvg⟩ := exists_dirichletHilbert_of_nativeH10 R hR w
  change w.toH1Function.toFun = (fun x => (F u.1).1 x) at hw
  change w.toH1Function.grad = (fun x i => (F u.1).2 i x) at hwg
  change (fun x => v.val none x) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
    w.toH1Function.toFun at hv
  have hvg' (i : Fin d) : (fun x => v.val (some i) x) =ᵐ[
      volume.restrict (sourceBall (0 : Vec d) R)]
      (fun x => w.toH1Function.grad x i) := hvg i
  refine ⟨v, (hvalue u.1).symm.trans ?_, ?_⟩
  · rw [hw] at hv
    exact hv.symm
  · intro i
    refine (hgrad u.1 i).symm.trans ?_
    rw [hwg] at hvg'
    exact (hvg' i).symm

/-- The reverse comparison on the same ball uses an upper bound for the
literal force density on a compact containing set. -/
theorem sbxB_ball_physicalForce_le_volume {d : ℕ} (hd : 2 ≤ d)
    (lam R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      (External.GantertSection7Support.physicalForceMeasure hd lam).restrict
          (sourceBall (0 : Vec d) R) ≤
        C • volume.restrict (sourceBall (0 : Vec d) R) := by
  let K : Set (Vec d) := Metric.closedBall 0 (2 * R)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hBK : sourceBall (0 : Vec d) R ⊆ K := by
    intro x hx
    have hx' := sourceBall_subset_cube R hR hx
    change dist x (0 : Vec d) < 2 * R / 2 at hx'
    change dist x (0 : Vec d) ≤ 2 * R
    linarith
  obtain ⟨_, C, _, _, _, hupper⟩ :=
    physicalForceMeasure_compact_comparison (firstCoordinateIndex hd) lam hK
  refine ⟨(C : ℝ≥0∞), ENNReal.coe_ne_top, ?_⟩
  change (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam).restrict
      (sourceBall (0 : Vec d) R) ≤ _
  have h := Measure.restrict_mono_measure hupper (sourceBall (0 : Vec d) R)
  simpa only [Measure.restrict_smul, Measure.restrict_restrict_of_subset hBK] using h

/-- Zero extension identifies the L² space over a restricted measure with its
closed subspace of the whole-space L² space. -/
@[nolint defsWithUnderscore]
def sbxB_zeroExtensionLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S) : Lp ℝ 2 (μ.restrict S) →L[ℝ] Lp ℝ 2 μ := by
  let A (f : Lp ℝ 2 (μ.restrict S)) : Lp ℝ 2 μ :=
    ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp (S.indicator f)
  have hA (f : Lp ℝ 2 (μ.restrict S)) : A f =ᵐ[μ] S.indicator f :=
    MemLp.coeFn_toLp _
  let L : Lp ℝ 2 (μ.restrict S) →ₗ[ℝ] Lp ℝ 2 μ := {
    toFun := A
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [hA (f + g), hA f, hA g, Lp.coeFn_add (A f) (A g),
        (ae_restrict_iff' hS).mp (Lp.coeFn_add f g)] with x ha hb hc hd he
      change A (f + g) x = (A f + A g) x
      rw [ha, hd]
      change S.indicator (f + g) x = A f x + A g x
      rw [hb, hc]
      by_cases hx : x ∈ S
      · simpa only [Set.indicator_of_mem hx, Pi.add_apply] using he hx
      · simp only [Set.indicator_of_notMem hx, add_zero]
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [hA (c • f), hA f, Lp.coeFn_smul c (A f),
        (ae_restrict_iff' hS).mp (Lp.coeFn_smul c f)] with x ha hb hc hd
      change A (c • f) x = (c • A f) x
      rw [ha, hc]
      change S.indicator (c • f) x = c • A f x
      rw [hb]
      by_cases hx : x ∈ S
      · simpa only [Set.indicator_of_mem hx, Pi.smul_apply] using hd hx
      · simp only [Set.indicator_of_notMem hx, smul_zero]
  }
  have hnorm (f : Lp ℝ 2 (μ.restrict S)) : ‖A f‖ = ‖f‖ := by
    rw [show A f = ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp
      (S.indicator f) from rfl, Lp.norm_toLp,
      eLpNorm_indicator_eq_eLpNorm_restrict hS, Lp.norm_def]
  exact L.mkContinuous 1 (fun f => by
    change ‖A f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using (hnorm f).le)

/-- The zero-extension map retains the literal indicator representative. -/
theorem sbxB_zeroExtensionLp_coe {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S) (f : Lp ℝ 2 (μ.restrict S)) :
    sbxB_zeroExtensionLp μ S hS f =ᵐ[μ] S.indicator f := by
  change ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp
    (S.indicator f) =ᵐ[μ] S.indicator f
  exact MemLp.coeFn_toLp _

/-- Assemble scalar L² coordinate classes into their Euclidean vector class. -/
@[nolint defsWithUnderscore]
def sbxB_assembleGradient {d : ℕ} (μ : Measure (Vec d)) :
    (Fin d → Lp ℝ 2 μ) →L[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 μ := by
  classical
  exact ∑ j : Fin d, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).compLpL 2 μ).comp (ContinuousLinearMap.proj j)

/-- The assembled class has exactly the prescribed Euclidean coordinates. -/
theorem sbxB_assembleGradient_coe {d : ℕ} (μ : Measure (Vec d))
    (G : Fin d → Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, ∀ j : Fin d, (sbxB_assembleGradient μ G x) j = G j x := by
  classical
  let f (j : Fin d) := (ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).compLp (G j)
  have hsum (s : Finset (Fin d)) :
      ⇑(∑ j ∈ s, f j) =ᵐ[μ] fun x => ∑ j ∈ s, f j x := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using!
        (Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 μ)
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with x hx hi
      rw [hx]
      change f j x + (∑ k ∈ s, f k) x = _
      rw [hi]
  have hf : ∀ᵐ x ∂μ, ∀ j : Fin d,
      f j x = G j x • EuclideanSpace.single j (1 : ℝ) := by
    apply ae_all_iff.mpr
    intro j
    exact (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))).coeFn_compLp (G j)
  filter_upwards [hsum Finset.univ, hf] with x hx hfx
  intro j
  simp only [sbxB_assembleGradient, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change (WithLp.ofLp ((∑ k : Fin d, f k) x)) j = _
  rw [hx]
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j) (∑ k : Fin d, f k x) = _
  rw [map_sum]
  simp only [PiLp.projₗ_apply, hfx, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- The scalar zero extension from the unweighted ball to the physical measure
is continuous and preserves the representative on that ball. -/
theorem sbxB_exists_ballToPhysicalValue {d : ℕ} (hd : 2 ≤ d)
    (lam R : ℝ) (hR : 0 < R) :
    ∃ T : Lp ℝ 2 (volume.restrict (sourceBall (0 : Vec d) R)) →L[ℝ]
        Lp ℝ 2 (External.GantertSection7Support.physicalForceMeasure hd lam),
      ∀ f, T f =ᵐ[External.GantertSection7Support.physicalForceMeasure hd lam]
        (sourceBall (0 : Vec d) R).indicator f := by
  let μ := External.GantertSection7Support.physicalForceMeasure hd lam
  let B := sourceBall (0 : Vec d) R
  have hB : MeasurableSet B := (dirichletBall (d := d) R).isOpen.measurableSet
  obtain ⟨C, hC, hbound⟩ := sbxB_ball_physicalForce_le_volume hd lam R hR
  let L : Lp ℝ 2 (volume.restrict B) →L[ℝ] Lp ℝ 2 (μ.restrict B) :=
    Lp.LpToLpOfMeasureLeSMul hC hbound
  refine ⟨(sbxB_zeroExtensionLp μ B hB).comp L, ?_⟩
  intro f
  have hf : L f =ᵐ[μ.restrict B] f := Lp.coeFn_LpToLpOfMeasureLeSMul hC hbound f
  filter_upwards [sbxB_zeroExtensionLp_coe μ B hB (L f),
    (ae_restrict_iff' hB).mp hf] with x hx hf'
  change sbxB_zeroExtensionLp μ B hB (L f) x = B.indicator f x
  rw [hx]
  by_cases h : x ∈ B
  · simpa only [Set.indicator_of_mem h] using hf' h
  · simp only [Set.indicator_of_notMem h]

/-- Zero extension continuously transports the full unweighted ball graph to
the physical value/Euclidean-gradient ambient space. -/
theorem sbxB_exists_ballToPhysicalAmbient {d : ℕ} (hd : 2 ≤ d)
    (lam R : ℝ) (hR : 0 < R) :
    ∃ F : SobolevData (dirichletBall (d := d) R) →L[ℝ]
        DensityWeightedH1Ambient (physicalForceWeight hd lam),
      (∀ z, ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _) (F z)).1 =ᵐ[
        External.GantertSection7Support.physicalForceMeasure hd lam]
        (sourceBall (0 : Vec d) R).indicator z.1) ∧
      (∀ z, ∀ᵐ x ∂External.GantertSection7Support.physicalForceMeasure hd lam,
        ∀ i : Fin d, (((WithLp.prodContinuousLinearEquiv 2 ℝ _ _) (F z)).2 x) i =
          (sourceBall (0 : Vec d) R).indicator (z.2 i) x) := by
  let μ := External.GantertSection7Support.physicalForceMeasure hd lam
  let B := sourceBall (0 : Vec d) R
  obtain ⟨T, hT⟩ := sbxB_exists_ballToPhysicalValue hd lam R hR
  let V : SobolevData (dirichletBall (d := d) R) →L[ℝ] Lp ℝ 2 μ :=
    T.comp (ContinuousLinearMap.fst ℝ (DomainL2 (dirichletBall (d := d) R))
      (Fin d → DomainL2 (dirichletBall (d := d) R)))
  let G : SobolevData (dirichletBall (d := d) R) →L[ℝ] (Fin d → Lp ℝ 2 μ) :=
    ContinuousLinearMap.pi fun i => T.comp ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ (DomainL2 (dirichletBall (d := d) R))
        (Fin d → DomainL2 (dirichletBall (d := d) R))))
  let F : SobolevData (dirichletBall (d := d) R) →L[ℝ]
      DensityWeightedH1Ambient (physicalForceWeight hd lam) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      (V.prod ((sbxB_assembleGradient μ).comp G))
  refine ⟨F, ?_, ?_⟩
  · intro z
    exact hT z.1
  · intro z
    have hcoord : ∀ᵐ x ∂μ, ∀ i : Fin d, T (z.2 i) x = B.indicator (z.2 i) x := by
      apply ae_all_iff.mpr
      intro i
      exact hT (z.2 i)
    filter_upwards [sbxB_assembleGradient_coe μ (fun i => T (z.2 i)), hcoord]
      with x hx hc
    intro i
    exact (hx i).trans (hc i)

/-- Zero extension of the ball graph sends the closure of its smooth tests
into the physical smooth-core closure on the same ball. -/
theorem sbxB_exists_killedGraphToPhysicalClosure {d : ℕ} (hd : 2 ≤ d)
    (lam R : ℝ) (hR : 0 < R) :
    ∃ F : SobolevData (dirichletBall (d := d) R) →L[ℝ]
        DensityWeightedH1Ambient (physicalForceWeight hd lam),
      (∀ z, ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _) (F z)).1 =ᵐ[
        External.GantertSection7Support.physicalForceMeasure hd lam]
        (sourceBall (0 : Vec d) R).indicator z.1) ∧
      (∀ z, ∀ᵐ x ∂External.GantertSection7Support.physicalForceMeasure hd lam,
        ∀ i : Fin d, (((WithLp.prodContinuousLinearEquiv 2 ℝ _ _) (F z)).2 x) i =
          (sourceBall (0 : Vec d) R).indicator (z.2 i) x) ∧
      ∀ z ∈ killedSobolevGraph (dirichletBall R),
        ∃ u : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam,
          F z = u.1.1 := by
  let μ := External.GantertSection7Support.physicalForceMeasure hd lam
  let B := sourceBall (0 : Vec d) R
  let V := physicalH1ZeroBoundary B hd lam
  let J : PhysicalH1Space hd lam →ₗ[ℝ] DensityWeightedH1Ambient (physicalForceWeight hd lam) :=
    (densityWeightedH1Submodule (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)).subtype
  let W := V.map J
  have hB : MeasurableSet B := (dirichletBall (d := d) R).isOpen.measurableSet
  obtain ⟨C, hC, hbound⟩ := sbxB_ball_physicalForce_le_volume hd lam R hR
  have hac : μ.restrict B ≪ volume.restrict B :=
    Measure.absolutelyContinuous_of_le_smul hbound
  obtain ⟨F, hvalue, hgradient⟩ := sbxB_exists_ballToPhysicalAmbient hd lam R hR
  have htest (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤) :
      F (smoothSobolevData φ) =
        (physicalH1SmoothTest hd lam φ φ.contDiff φ.hasCompactSupport).1 := by
    let w := physicalH1SmoothTest hd lam φ φ.contDiff φ.hasCompactSupport
    have hφval : (testL2 φ : Vec d → ℝ) =ᵐ[μ.restrict B] φ :=
      hac.ae_eq (testL2_coeFn φ)
    have hφgrad : ∀ᵐ x ∂μ, ∀ i : Fin d, x ∈ B →
        testPartialL2 φ i x = fderiv ℝ φ x (Pi.single i 1) := by
      apply ae_all_iff.mpr
      intro i
      exact (ae_restrict_iff' hB).mp (hac.ae_eq (testPartialL2_coeFn φ i))
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [hvalue (smoothSobolevData φ),
        (ae_restrict_iff' hB).mp hφval,
        physicalH1SmoothTest_value hd lam φ φ.contDiff φ.hasCompactSupport] with x hv ht hw
      change ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _)
        (F (smoothSobolevData φ))).1 x = densityWeightedH1SpaceValue w x
      rw [hv, hw]
      change B.indicator (testL2 φ) x = φ x
      by_cases hx : x ∈ B
      · simpa only [Set.indicator_of_mem hx] using ht hx
      · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (φ.tsupport_subset h))
        simp only [Set.indicator_of_notMem hx, hz]
    · apply Lp.ext
      filter_upwards [hgradient (smoothSobolevData φ), hφgrad,
        physicalH1SmoothTest_gradient hd lam φ φ.contDiff φ.hasCompactSupport] with x hg ht hw
      apply PiLp.ext
      intro i
      change (((WithLp.prodContinuousLinearEquiv 2 ℝ _ _)
        (F (smoothSobolevData φ))).2 x) i = (densityWeightedH1SpaceGradient w x) i
      rw [hg i, hw]
      change B.indicator (testPartialL2 φ i) x = fderiv ℝ φ x (Pi.single i 1)
      by_cases hx : x ∈ B
      · simpa only [Set.indicator_of_mem hx] using ht i hx
      · have hz : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ
          (fun h => hx (φ.tsupport_subset h))
        simp only [Set.indicator_of_notMem hx, hz, ContinuousLinearMap.zero_apply]
  have hW : IsClosed (W : Set (DensityWeightedH1Ambient (physicalForceWeight hd lam))) := by
    have himage : (W : Set (DensityWeightedH1Ambient (physicalForceWeight hd lam))) =
        Subtype.val '' (V : Set (PhysicalH1Space hd lam)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.mp hx
        exact ⟨u, hu, hu'⟩
      · rintro ⟨u, hu, rfl⟩
        exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    rw [himage]
    exact (densityWeightedH1Submodule_isClosed _ _ _).isClosedMap_subtype_val _
      (physicalH1ZeroBoundary_isClosed B hd lam)
  have hclosed : IsClosed ((W.comap F.toLinearMap) : Set
      (SobolevData (dirichletBall (d := d) R))) := hW.preimage F.continuous
  have hrange : LinearMap.range (smoothSobolevDataLinear (Ω := dirichletBall (d := d) R)) ≤
      W.comap F.toLinearMap := by
    rintro _ ⟨φ, rfl⟩
    apply Submodule.mem_comap.mpr
    change F (smoothSobolevData φ) ∈ W
    rw [htest φ]
    apply Submodule.mem_map.mpr
    exact ⟨_, physicalH1SmoothTest_mem_zeroBoundary B hd lam φ
      ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩, rfl⟩
  refine ⟨F, hvalue, hgradient, ?_⟩
  intro z hz
  have hz' : F z ∈ W := (Submodule.topologicalClosure_minimal _ hrange hclosed) hz
  obtain ⟨u, hu, heq⟩ := Submodule.mem_map.mp hz'
  exact ⟨⟨u, hu⟩, heq.symm⟩

/-- Every killed ball graph has a physical zero-boundary representative with
the same value and every weak-gradient coordinate on the ball. -/
theorem sbxB_exists_physicalZeroBoundary_of_killedGraph {d : ℕ} (hd : 2 ≤ d)
    (lam R : ℝ) (hR : 0 < R) (z : killedSobolevGraph (dirichletBall (d := d) R)) :
    ∃ u : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam,
      densityWeightedH1SpaceValue u.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] z.1.1 ∧
      ∀ i : Fin d,
        (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i)
          =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] z.1.2 i := by
  let μ := External.GantertSection7Support.physicalForceMeasure hd lam
  let B := sourceBall (0 : Vec d) R
  have hB : MeasurableSet B := (dirichletBall (d := d) R).isOpen.measurableSet
  obtain ⟨C, hC, hbound⟩ := sbxB_ball_volume_le_physicalForce hd lam R hR
  have hac : volume.restrict B ≪ μ := Measure.absolutelyContinuous_of_le_smul hbound
  obtain ⟨F, hvalue, hgradient, hclosed⟩ :=
    sbxB_exists_killedGraphToPhysicalClosure hd lam R hR
  obtain ⟨u, heq⟩ := hclosed z.1 z.2
  have hrep : (physicalH1SpaceRepresentative hd lam u.1).weakGradient =ᵐ[μ]
      densityWeightedH1SpaceGradient u.1 := by
    have he : (physicalH1SpaceRepresentative hd lam u.1).gradient_memLp.toLp
        (physicalH1SpaceRepresentative hd lam u.1).weakGradient =
          densityWeightedH1SpaceGradient u.1 :=
      congrArg Prod.snd (physicalH1SpaceRepresentative_pair hd lam u.1)
    exact (physicalH1SpaceRepresentative hd lam u.1).gradient_memLp.coeFn_toLp.symm.trans
      (Filter.EventuallyEq.of_eq (congrArg
        (fun f : Lp (EuclideanSpace ℝ (Fin d)) 2 μ =>
          (f : Vec d → EuclideanSpace ℝ (Fin d))) he))
  refine ⟨u, ?_, ?_⟩
  · filter_upwards [hac.ae_eq (hvalue z.1), ae_restrict_mem hB] with x hv hx
    rw [heq] at hv
    change densityWeightedH1SpaceValue u.1 x = B.indicator z.1.1 x at hv
    rw [Set.indicator_of_mem hx] at hv
    exact hv
  · intro i
    filter_upwards [hac.ae_eq hrep, hac.ae_le (hgradient z.1), ae_restrict_mem hB]
      with x hr hg hx
    change (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i = _
    rw [hr]
    have hi := hg i
    rw [heq] at hi
    change (densityWeightedH1SpaceGradient u.1 x) i = B.indicator (z.1.2 i) x at hi
    rw [Set.indicator_of_mem hx] at hi
    exact hi

/-- Every Dirichlet completion vector has a physical zero-boundary
representative with the same value and all gradient coordinates on the ball. -/
theorem sbxB_exists_physicalZeroBoundary_of_dirichletHilbert {d : ℕ} (hd : 2 ≤ d)
    (lam R : ℝ) (hR : 0 < R) (v : DirichletHilbertSpace (d := d) R hR) :
    ∃ u : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam,
      densityWeightedH1SpaceValue u.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        (fun x => v.val none x) ∧
      ∀ i : Fin d,
        (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i)
          =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => v.val (some i) x) := by
  let z : killedSobolevGraph (dirichletBall (d := d) R) :=
    ⟨dirichletHilbertBallData R hR v.val,
      dirichletHilbertBallData_mem_killedSobolevGraph R hR v⟩
  obtain ⟨u, hu, hg⟩ := sbxB_exists_physicalZeroBoundary_of_killedGraph hd lam R hR z
  refine ⟨u, hu.trans ?_, fun i => (hg i).trans ?_⟩
  · exact sourceBallL2Restriction_coe R hR (v.val none)
  · exact sourceBallL2Restriction_coe R hR (v.val (some i))

end
end EinsteinFull
