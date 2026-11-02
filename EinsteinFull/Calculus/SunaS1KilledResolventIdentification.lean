import EinsteinFull.Blueprint.Foundation.Proofs.SbxS1PastKernel
import EinsteinFull.Blueprint.G1.Proofs.SbxS8StoppedLocality
import EinsteinFull.Work.W1.StoppedKernelLocalitySupport
import Mathlib.Tactic.Linter

open MeasureTheory
open Filter Topology
open scoped NNReal
open EinsteinRelation EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint EinsteinRelation.SpatialDirichlet

namespace EinsteinFull

/-- The full-space killed Laplace integral is the inclusion of the interior
resolvent applied to the orthogonal projection of the original datum. -/
theorem s1_killed_Laplace_eq_interior_resolvent
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    let p : physicalZeroBoundaryL2 U hd ω lam L hω :=
      ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
        physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) =
      (gmpKilledInteriorResolvent G U hU ⟨α, hα⟩ p).val := by
  dsimp only
  let p : physicalZeroBoundaryL2 U hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
      physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩
  let S := gmpKilledInteriorSemigroup G U hU
  let J := (physicalZeroBoundaryL2 U hd ω lam L hω).subtypeL
  have hp (t : ℝ≥0) : gmpKilledL2Operator G U hU t p.val =
      gmpKilledL2Operator G U hU t f := by
    have h := congrArg (fun A => A f) (gmpKilledL2Operator_add_time G U hU t 0)
    simpa only [add_zero, ContinuousLinearMap.comp_apply, gmpKilledL2Operator_apply,
      gmpKilledL2_zero, p] using h.symm
  change _ = J (S.resolvent ⟨α, hα⟩ p)
  rw [MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.resolvent_apply,
    ← ContinuousLinearMap.integral_comp_comm J (S.integrableOn_laplaceIntegrand hα p)]
  apply integral_congr_ae
  filter_upwards with t
  change Real.exp (-α*t) • gmpKilledL2Operator G U hU t.toNNReal f =
    J (Real.exp (-α*t) • S t.toNNReal p)
  rw [map_smul]
  change _ = Real.exp (-α*t) • gmpKilledL2Operator G U hU t.toNNReal p.val
  rw [hp]

/-- The actual killed Laplace integral has a representative in the original
physical zero-boundary graph for every full-space L² datum. -/
theorem s1_killed_Laplace_exists_zeroBoundary
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ∃ u : physicalH1ZeroBoundary U hd lam,
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
        gmpKilledL2Operator G U hU t.toNNReal f) =
        physicalZeroBoundaryValue U hd ω lam L hω u := by
  let p : physicalZeroBoundaryL2 U hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
      physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩
  obtain ⟨u, hu, hval, _, _⟩ := gmpKilledInteriorResolvent_exists_zeroBoundary
    G U hU ⟨α, hα⟩ p
  refine ⟨⟨u, hu⟩, (s1_killed_Laplace_eq_interior_resolvent hd L hL ω hω
    lam h0 h1 G U hU α hα f).trans ?_⟩
  rw [← hval]
  apply Lp.ext
  exact (gmpPhysicalH1Value_ae_eq hd ω lam L hω u).trans
    (physicalZeroBoundaryValue_ae_eq U hd ω lam L hω ⟨u, hu⟩).symm

/-- The actual supplied killed Laplace orbit has an H¹₀ representative satisfying
its physical weak resolvent equation. This is the remaining form-association step. -/
def S1KilledLaplaceWeakAssociation
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) : Prop :=
  ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
    ∃ u : physicalH1ZeroBoundary U hd lam,
      HasPhysicalZeroBoundaryResolvent U ω hd lam α (f : Vec d → ℝ) u ∧
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
        gmpKilledL2Operator G U hU t.toNNReal f) =
        physicalZeroBoundaryValue U hd ω lam L hω u

/-- The remaining mixed-form identity, expressed on an actual Laplace lift. -/
def S1KilledLaplaceWeakEquation
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) : Prop :=
  ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (u : physicalH1ZeroBoundary U hd lam),
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) =
      physicalZeroBoundaryValue U hd ω lam L hω u →
    HasPhysicalZeroBoundaryResolvent U ω hd lam α (f : Vec d → ℝ) u

/-- The existing H¹₀ lift reduces association to the mixed-form equation. -/
theorem s1_killed_LaplaceWeakAssociation_of_weakEquation
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (hweak : S1KilledLaplaceWeakEquation hd L hL ω hω lam h0 h1 G U hU α) :
    S1KilledLaplaceWeakAssociation hd L hL ω hω lam h0 h1 G U hU α := by
  intro f
  obtain ⟨u, hu⟩ := s1_killed_Laplace_exists_zeroBoundary hd L hL ω hω lam h0 h1
    G U hU α hα f
  exact ⟨u, hweak f u hu, hu⟩

/-- Variational uniqueness identifies the actual killed Laplace orbit once its
physical weak equation has been established. -/
theorem s1_supplied_killed_Laplace_eq_zeroBoundaryResolvent_of_association
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (hassoc : S1KilledLaplaceWeakAssociation hd L hL ω hω lam h0 h1 G U hU α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) =
    physicalZeroBoundaryValue U hd ω lam L hω
      (physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα
        (f : Vec d → ℝ) (Lp.memLp f)) := by
  obtain ⟨u, hu, hval⟩ := hassoc f
  have heq : u = physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα
      (f : Vec d → ℝ) (Lp.memLp f) :=
    (physicalZeroBoundaryResolvent_existsUnique U hd ω lam L α hL hω hα
      (f : Vec d → ℝ) (Lp.memLp f)).unique hu
      (physicalZeroBoundaryResolvent_spec U hd ω lam L α hL hω hα
        (f : Vec d → ℝ) (Lp.memLp f))
  rw [hval, heq]

/-- The physical weak equation identifies the supplied killed Laplace orbit. -/
theorem s1_supplied_killed_Laplace_eq_zeroBoundaryResolvent_of_weakEquation
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (hweak : S1KilledLaplaceWeakEquation hd L hL ω hω lam h0 h1 G U hU α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) =
    physicalZeroBoundaryValue U hd ω lam L hω
      (physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα
        (f : Vec d → ℝ) (Lp.memLp f)) :=
  s1_supplied_killed_Laplace_eq_zeroBoundaryResolvent_of_association hd L hL ω hω
    lam h0 h1 G U hU α hα
    (s1_killed_LaplaceWeakAssociation_of_weakEquation hd L hL ω hω lam h0 h1
      G U hU α hα hweak) f

/-- A mixed quotient identity for the actual interior resolvent implies its
physical weak equation. -/
theorem s1_killed_LaplaceWeakEquation_of_mixedQuotient
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (hform : ∀ (f : physicalZeroBoundaryL2 U hd ω lam L hω)
      (u w : physicalH1ZeroBoundary U hd lam),
      gmpPhysicalH1Value hd ω lam L hω u.val =
        (gmpKilledInteriorResolvent G U hU ⟨α, hα⟩ f).val →
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        inner ℝ ((gmpKilledInteriorResolvent G U hU ⟨α, hα⟩ f).val -
          gmpKilledL2Operator G U hU t
            (gmpKilledInteriorResolvent G U hU ⟨α, hα⟩ f).val)
          (gmpPhysicalH1Value hd ω lam L hω w.val))
        (𝓝[>] (0 : ℝ≥0))
        (𝓝 (gmpPhysicalH1Energy hd ω lam L hω u.val w.val))) :
    S1KilledLaplaceWeakEquation hd L hL ω hω lam h0 h1 G U hU α := by
  intro f u hu
  let p : physicalZeroBoundaryL2 U hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
      physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩
  have huval : gmpPhysicalH1Value hd ω lam L hω u.val =
      (gmpKilledInteriorResolvent G U hU ⟨α, hα⟩ p).val := by
    have h := (s1_killed_Laplace_eq_interior_resolvent hd L hL ω hω lam h0 h1
      G U hU α hα f).symm.trans hu
    rw [h]
    apply Lp.ext
    exact (gmpPhysicalH1Value_ae_eq hd ω lam L hω u.val).trans
      (physicalZeroBoundaryValue_ae_eq U hd ω lam L hω u).symm
  refine ⟨hα, fun w => ?_⟩
  let q := physicalZeroBoundaryInteriorValue U hd ω lam L hω w
  have ht := gmpKilledInteriorResolvent_tendsto_mixedQuotient G U hU ⟨α, hα⟩ p q
  have he := tendsto_nhds_unique (hform p u w huval) ht
  have hp : inner ℝ p.val q.val = inner ℝ f q.val := by
    change inner ℝ ((physicalZeroBoundaryL2 U hd ω lam L hω).starProjection f) q.val = _
    rw [Submodule.inner_starProjection_left_eq_right]
    rw [(physicalZeroBoundaryL2 U hd ω lam L hω).starProjection_eq_self_iff.mpr q.property]
  have hm (a : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
      inner ℝ a (gmpPhysicalH1Value hd ω lam L hω w.val) =
        ∫ x, a x * densityWeightedH1SpaceValue w.val x ∂physicalReversibleMeasure ω hd lam := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [gmpPhysicalH1Value_ae_eq hd ω lam L hω w.val] with x hx
    rw [hx]
    simp only [RCLike.inner_apply', conj_trivial]
    rfl
  have henergy : gmpPhysicalH1Energy hd ω lam L hω u.val w.val =
      ∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.val)
        (physicalH1SpaceRepresentative hd lam w.val) x ∂physicalReversibleMeasure ω hd lam := by
    unfold gmpPhysicalH1Energy
    apply integral_congr_ae
    filter_upwards [gmpPhysicalH1Gradient_ae hd ω lam L hω u.val,
      gmpPhysicalH1Gradient_ae hd ω lam L hω w.val] with x hu hw
    change (1 / 2 : ℝ) * _ = (1 / 2 : ℝ) * _
    rw [hu, hw]
    rfl
  have hq : q.val = gmpPhysicalH1Value hd ω lam L hω w.val := by
    apply Lp.ext
    exact (physicalZeroBoundaryValue_ae_eq U hd ω lam L hω w).trans
      (gmpPhysicalH1Value_ae_eq hd ω lam L hω w.val).symm
  change gmpPhysicalH1Energy hd ω lam L hω u.val w.val =
    inner ℝ (p.val - α • (gmpKilledInteriorResolvent G U hU ⟨α, hα⟩ p).val) q.val at he
  rw [inner_sub_left, real_inner_smul_left] at he
  rw [hp, ← huval, hq] at he
  rw [hm, hm, henergy] at he
  have hmass : (∫ x, gmpPhysicalH1Value hd ω lam L hω u.val x *
      densityWeightedH1SpaceValue w.val x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, densityWeightedH1SpaceValue u.val x * densityWeightedH1SpaceValue w.val x
        ∂physicalReversibleMeasure ω hd lam := by
    apply integral_congr_ae
    filter_upwards [gmpPhysicalH1Value_ae_eq hd ω lam L hω u.val] with x hx
    rw [hx]
    rfl
  rw [hmass] at he
  linarith

/-- The actual supplied killed Laplace lift satisfies the physical weak equation. -/
theorem s1_supplied_killed_Laplace_weak_equation
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (u : physicalH1ZeroBoundary U hd lam)
    (hu : (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) =
      physicalZeroBoundaryValue U hd ω lam L hω u) :
    HasPhysicalZeroBoundaryResolvent U ω hd lam α (f : Vec d → ℝ) u := by
  apply s1_killed_LaplaceWeakEquation_of_mixedQuotient hd L hL ω hω lam h0 h1
    G U hU α hα ?_ f u hu
  intro g v w hv
  rw [← hv]
  exact sbxS8_gmp_killedMixedForm_tendsto G U hU v.val w.val v.property w.property

/-- The supplied killed Laplace integral equals the physical resolvent. -/
theorem s1_supplied_killed_Laplace_eq_zeroBoundaryResolvent
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) =
    physicalZeroBoundaryValue U hd ω lam L hω
      (physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα
        (f : Vec d → ℝ) (Lp.memLp f)) :=
  s1_supplied_killed_Laplace_eq_zeroBoundaryResolvent_of_weakEquation hd L hL ω hω
    lam h0 h1 G U hU α hα
    (fun f u hu => s1_supplied_killed_Laplace_weak_equation hd L hL ω hω
      lam h0 h1 G U hU α hα f u hu) f

/-- The supplied killed Laplace integral has the sharp contraction bound. -/
theorem s1_supplied_killed_Laplace_norm_le
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f‖ ≤ α⁻¹ * ‖f‖ := by
  let p : physicalZeroBoundaryL2 U hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
      physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩
  rw [s1_killed_Laplace_eq_interior_resolvent hd L hL ω hω lam h0 h1 G U hU α hα f]
  change ‖gmpKilledInteriorResolvent G U hU ⟨α, hα⟩ p‖ ≤ α⁻¹ * ‖f‖
  refine (gmpKilledInteriorResolvent_norm_le G U hU ⟨α, hα⟩ p).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hα.le)
  change ‖physicalZeroBoundaryProjection U hd ω lam L hω f‖ ≤ ‖f‖
  exact (physicalZeroBoundaryL2 U hd ω lam L hω).norm_starProjection_apply_le f

/-- The exponentially discounted supplied killed orbit has a uniform tail bound. -/
theorem s1_supplied_killed_Laplace_tail_norm_le
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α R : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖∫ t : ℝ in Set.Ioi R, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f‖ ≤
      ‖f‖ / α * Real.exp (-α*R) := by
  have hg : IntegrableOn (fun t : ℝ => ‖f‖ * Real.exp (-α*t)) (Set.Ioi R) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hα) R).const_mul ‖f‖
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi R),
      ‖Real.exp (-α*t) • gmpKilledL2Operator G U hU t.toNNReal f‖ ≤
        ‖f‖ * Real.exp (-α*t) := by
    filter_upwards with t
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [gmpKilledL2Operator_apply]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (gmpKilledL2_norm_le G U hU t.toNNReal f)
        (Real.exp_nonneg (-α*t))
  calc
    ‖∫ t : ℝ in Set.Ioi R, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f‖ ≤
        ∫ t : ℝ in Set.Ioi R, ‖f‖ * Real.exp (-α*t) :=
      norm_integral_le_of_norm_le hg hn
    _ = ‖f‖ / α * Real.exp (-α*R) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hα)]
      ring

/-- The truncated supplied killed Laplace orbit converges to the physical resolvent. -/
theorem s1_supplied_killed_truncated_Laplace_tendsto
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in Set.Ioc 0 R, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) atTop
      (𝓝 (physicalZeroBoundaryValue U hd ω lam L hω
        (physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα
          (f : Vec d → ℝ) (Lp.memLp f)))) := by
  let p : physicalZeroBoundaryL2 U hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
      physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩
  let S := gmpKilledInteriorSemigroup G U hU
  let J := (physicalZeroBoundaryL2 U hd ω lam L hω).subtypeL
  have hp (t : ℝ≥0) : gmpKilledL2Operator G U hU t p.val =
      gmpKilledL2Operator G U hU t f := by
    have h := congrArg (fun A => A f) (gmpKilledL2Operator_add_time G U hU t 0)
    simpa only [add_zero, ContinuousLinearMap.comp_apply, gmpKilledL2Operator_apply,
      gmpKilledL2_zero, p] using h.symm
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) (Set.Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => J (S.laplaceIntegrand α p t)) (Set.Ioi 0) :=
      J.integrable_comp (S.integrableOn_laplaceIntegrand hα p)
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro t ht
    change J (Real.exp (-α*t) • S t.toNNReal p) = _
    rw [map_smul]
    change Real.exp (-α*t) • gmpKilledL2Operator G U hU t.toNNReal p.val = _
    rw [hp]
  have hexp : Tendsto (fun R : ℝ => Real.exp (-α * R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hα)).2 tendsto_id)
  have hbound : Tendsto (fun R : ℝ => ‖f‖ / α * Real.exp (-α * R)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hexp
  have htail : Tendsto (fun R : ℝ => ∫ t : ℝ in Set.Ioi R, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) atTop (𝓝 0) :=
    squeeze_zero_norm (fun R => s1_supplied_killed_Laplace_tail_norm_le hd L hL ω hω
      lam h0 h1 G U hU α R hα f) hbound
  have hlim : Tendsto (fun R : ℝ =>
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
        gmpKilledL2Operator G U hU t.toNNReal f) -
      (∫ t : ℝ in Set.Ioi R, Real.exp (-α*t) •
        gmpKilledL2Operator G U hU t.toNNReal f)) atTop
      (𝓝 ((∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
        gmpKilledL2Operator G U hU t.toNNReal f) - 0)) :=
    tendsto_const_nhds.sub htail
  have heq : ∀ᶠ R : ℝ in atTop,
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
        gmpKilledL2Operator G U hU t.toNNReal f) -
        (∫ t : ℝ in Set.Ioi R, Real.exp (-α*t) •
          gmpKilledL2Operator G U hU t.toNNReal f) =
      (∫ t : ℝ in Set.Ioc 0 R, Real.exp (-α*t) •
        gmpKilledL2Operator G U hU t.toNNReal f) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    rw [sub_eq_iff_eq_add, ← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set Set.Ioc_subset_Ioi_self) (hi.mono_set (Set.Ioi_subset_Ioi hR)),
      Set.Ioc_union_Ioi_eq_Ioi hR]
  have ht := hlim.congr' heq
  simpa only [sub_zero, s1_supplied_killed_Laplace_eq_zeroBoundaryResolvent hd L hL ω hω
    lam h0 h1 G U hU α hα f] using ht

/-- Two positive discount parameters for the same supplied killed orbit. -/
theorem s1_supplied_killed_Laplace_parameter_bound
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖(∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
      gmpKilledL2Operator G U hU t.toNNReal f) -
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-β*t) •
      gmpKilledL2Operator G U hU t.toNNReal f)‖ ≤
      |β - α| * (α⁻¹ * (β⁻¹ * ‖f‖)) := by
  let p : physicalZeroBoundaryL2 U hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
      physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩
  let S := gmpKilledInteriorSemigroup G U hU
  have hp : ‖p‖ ≤ ‖f‖ := by
    change ‖physicalZeroBoundaryProjection U hd ω lam L hω f‖ ≤ ‖f‖
    exact (physicalZeroBoundaryL2 U hd ω lam L hω).norm_starProjection_apply_le f
  have hid := DFunLike.congr_fun (S.resolvent_sub_resolvent ⟨α, hα⟩ ⟨β, hβ⟩) p
  change S.resolvent ⟨α, hα⟩ p - S.resolvent ⟨β, hβ⟩ p =
    (β - α) • S.resolvent ⟨α, hα⟩ (S.resolvent ⟨β, hβ⟩ p) at hid
  rw [s1_killed_Laplace_eq_interior_resolvent hd L hL ω hω lam h0 h1 G U hU α hα f,
    s1_killed_Laplace_eq_interior_resolvent hd L hL ω hω lam h0 h1 G U hU β hβ f]
  change ‖(S.resolvent ⟨α, hα⟩ p - S.resolvent ⟨β, hβ⟩ p).val‖ ≤ _
  change ‖S.resolvent ⟨α, hα⟩ p - S.resolvent ⟨β, hβ⟩ p‖ ≤ _
  rw [hid, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    ‖S.resolvent ⟨α, hα⟩ (S.resolvent ⟨β, hβ⟩ p)‖ ≤
        α⁻¹ * ‖S.resolvent ⟨β, hβ⟩ p‖ :=
      gmpKilledInteriorResolvent_norm_le G U hU ⟨α, hα⟩ _
    _ ≤ α⁻¹ * (β⁻¹ * ‖p‖) :=
      mul_le_mul_of_nonneg_left
        (gmpKilledInteriorResolvent_norm_le G U hU ⟨β, hβ⟩ p) (inv_nonneg.mpr hα.le)
    _ ≤ α⁻¹ * (β⁻¹ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hβ.le))
        (inv_nonneg.mpr hα.le)

/-- The supplied killed-L² Laplace transform is Lipschitz in the positive
parameter, with the explicit two-parameter resolvent bound. -/
theorem s1_supplied_killed_Laplace_parameter_norm_le
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖(∫ t : ℝ in Set.Ioi 0, Real.exp (-α*t) •
        gmpKilledL2Operator G U hU t.toNNReal f) -
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-β*t) •
        gmpKilledL2Operator G U hU t.toNNReal f)‖ ≤
      |α - β| / (α * β) * ‖f‖ := by
  have h := s1_supplied_killed_Laplace_parameter_bound hd L hL ω hω
    lam h0 h1 G U hU α β hα hβ f
  convert h using 1 <;> rw [abs_sub_comm α β, div_eq_mul_inv, mul_inv_rev] <;> ring

#print axioms s1_supplied_killed_Laplace_parameter_norm_le

#print axioms s1_supplied_killed_truncated_Laplace_tendsto

#print axioms s1_supplied_killed_Laplace_tail_norm_le

#print axioms s1_supplied_killed_Laplace_norm_le

#print axioms s1_supplied_killed_Laplace_weak_equation
#print axioms s1_supplied_killed_Laplace_eq_zeroBoundaryResolvent

#lint

end EinsteinFull
