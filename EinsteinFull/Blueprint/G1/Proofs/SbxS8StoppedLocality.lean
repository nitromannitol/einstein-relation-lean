import EinsteinFull.Work.W1.StoppedKernelLocalitySupport
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS1PastKernel
import MarkovProcess.Semigroup.GeneratorUniqueness
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Linter

/-!
# Actual GMP form comparison on the completed interior domain

The realization's full closed-form fields give the limits below for its actual
transition kernels. Local agreement of both physical fields then compares these
limits on the completed zero-boundary domain, whose exterior gradient support
has already been proved. No stopped-law or locality premise is used.

Domination of the actual killed endpoint law by the full endpoint law first
identifies the killed form on nonnegative zero-boundary data. Smooth positive
shifts and the parallelogram identity then give the exact limit on the signed
smooth core. A uniform quadratic energy-defect bound extends it to the entire
completed zero-boundary domain. Its infinitesimal comparison therefore holds
for independently supplied actual GMP killed laws, without a sign restriction.

This is support for `app:factorization#future-kernel`. Identifying the constructed
interior evolution with the killed GMP law, including every starting point,
remains necessary before it gives stopped-law locality.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology
open scoped InnerProductSpace

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support

/-- The actual GMP form limit on any full weak-gradient representative. The
quotient representative required by the realization is constructed internally. -/
theorem sbxS8_gmp_closedForm_tendsto {d : ℕ} {hd : 2 ≤ d}
    {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (u : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    Tendsto
      (fun t => semigroupFormDifferenceQuotient ω hd lam r.transitionKernel t u.value)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 (physicalH1FormEnergy ω hd lam u)) := by
  have hq : densityWeightedH1Value (physicalForceWeight hd lam) (Quotient.mk _ u)
      =ᵐ[physicalReversibleMeasure ω hd lam] u.value := by
    apply (ae_withDensity_iff_volume_of_continuous_pos
      (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
      (physicalReversibleDensity_pos ω hd lam) _).mpr
    exact (ae_withDensity_iff_volume_of_continuous_pos
      (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
      (physicalForceWeight_pos hd lam) _).mp u.value_memLp.coeFn_toLp
  exact r.closedForm_value u.value (Quotient.mk _ u) hq u EventuallyEq.rfl

/-- The full form-domain tests of two actual GMP realizations at a common
force agree. The two physical L² conditions retain their respective measures. -/
theorem sbxS8_gmp_closedForm_domain_iff {d : ℕ} {hd : 2 ≤ d}
    {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (hf' : MemLp f 2 (physicalReversibleMeasure ω' hd lam)) :
    (∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω hd lam r.transitionKernel t f ≤ C) ↔
    (∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω' hd lam r'.transitionKernel t f ≤ C) := by
  rw [r.closedForm_domain f hf, r'.closedForm_domain f hf']
  exact physicalH1Member_environment_iff ω ω' hd lam f

/-- On the actual completed interior domain, locally equal physical fields give
the same infinitesimal quadratic-form limit for the supplied GMP kernels.
This does not identify their finite-time killed kernels. -/
theorem sbxS8_gmp_closedForm_difference_tendsto_zero {d : ℕ} {hd : 2 ≤ d}
    {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : MeasurableSet U)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1ZeroBoundary U hd lam) :
    Tendsto (fun t =>
      semigroupFormDifferenceQuotient ω hd lam r.transitionKernel t
        (physicalH1SpaceRepresentative hd lam u).value -
      semigroupFormDifferenceQuotient ω' hd lam r'.transitionKernel t
        (physicalH1SpaceRepresentative hd lam u).value)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 0) := by
  have h := (sbxS8_gmp_closedForm_tendsto r
    (physicalH1SpaceRepresentative hd lam u)).sub
      (sbxS8_gmp_closedForm_tendsto r' (physicalH1SpaceRepresentative hd lam u))
  simpa only [physicalH1FormEnergy_eq_on_zeroBoundary U hU ω ω' heq hd lam u hu,
    sub_self] using h

/-- For nonnegative physical L² data, literal killing increases the quadratic
form quotient. The comparison uses the supplied endpoint laws themselves. -/
theorem sbxS8_gmp_fullForm_le_killed_of_nonneg {d : ℕ} {hd : 2 ≤ d}
    {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x) :
    semigroupFormDifferenceQuotient ω hd lam r.transitionKernel t f ≤
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t f := by
  have hcomp : ∀ᵐ y ∂r.transitionKernel t ∘ₘ physicalReversibleMeasure ω hd lam,
      0 ≤ f y := by
    rw [r.transitionKernel_invariant hd hL t]
    exact hf
  have hinner : ⟪gmpKilledL2Operator r U hU t f, f⟫_ℝ ≤
      ⟪r.kernelL2Action hd hL t f, f⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_mono_ae (L2.integrable_inner _ _) (L2.integrable_inner _ _)
    filter_upwards [hf, Measure.ae_ae_of_ae_comp hcomp,
      ae_integrable_gmpTransitionKernel r t f, gmpKilledL2_ae_eq r U hU t f,
      gmpTransitionL2_ae_eq r t f] with x hx hpos hi hk hp
    change (f x) * (gmpKilledL2Operator r U hU t f x) ≤
      (f x) * (r.kernelL2Action hd hL t f x)
    rw [gmpKilledL2Operator_apply, hk, hp]
    exact mul_le_mul_of_nonneg_left
      (integral_mono_measure (gmpKilledEndpointKernel_le r U hU t x) hpos hi) hx
  rw [gmpTransitionFormDifferenceQuotient_eq_inner,
    gmpKilledFormDifferenceQuotient_eq_inner]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [inner_sub_left]
  linarith

/-- The supplied full GMP form limit on the canonical physical L² value of a
completed weighted H¹ graph. Both quotient representatives are constructed. -/
theorem sbxS8_gmp_fullForm_tendsto_physicalValue {d : ℕ} {hd : 2 ≤ d}
    {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (u : PhysicalH1Space hd lam) :
    Tendsto (fun t => semigroupFormDifferenceQuotient ω hd lam r.transitionKernel t
      (gmpPhysicalH1Value hd ω lam L hω u)) (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u))) := by
  let g := physicalH1SpaceRepresentative hd lam u
  have hg0 : g.value =ᵐ[physicalReversibleMeasure ω hd lam]
      densityWeightedH1SpaceValue u :=
    (gmp_force_ae_iff_physical hd ω lam _).mp
      (gmpH1Representative_value_ae (physicalForceWeight hd lam)
        (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) u)
  have hg : g.value =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalH1Value hd ω lam L hω u :=
    hg0.trans (gmpPhysicalH1Value_ae_eq hd ω lam L hω u).symm
  have hq : densityWeightedH1Value (physicalForceWeight hd lam) (Quotient.mk _ g)
      =ᵐ[physicalReversibleMeasure ω hd lam] g.value :=
    (gmp_force_ae_iff_physical hd ω lam _).mp g.value_memLp.coeFn_toLp
  exact r.closedForm_value _ (Quotient.mk _ g) (hq.trans hg) g hg

/-- Exact short-time form identification for the actual killed GMP law on
nonnegative members of the existing completed zero-boundary domain. -/
theorem sbxS8_gmp_killedForm_tendsto_of_nonneg {d : ℕ} {hd : 2 ≤ d}
    {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1ZeroBoundary U hd lam)
    (hn : ∀ᵐ x ∂EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam,
      0 ≤ densityWeightedH1SpaceValue u x) :
    Tendsto (fun t => semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel r U hU) t (gmpPhysicalH1Value hd ω lam L hω u))
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u))) := by
  have hn' : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      0 ≤ gmpPhysicalH1Value hd ω lam L hω u x := by
    have hnphys : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        0 ≤ densityWeightedH1SpaceValue u x :=
      (gmp_force_ae_iff_physical hd ω lam _).mp hn
    filter_upwards [hnphys,
      gmpPhysicalH1Value_ae_eq hd ω lam L hω u] with x hx hrep
    exact hrep.symm ▸ hx
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (sbxS8_gmp_fullForm_tendsto_physicalValue r u) tendsto_const_nhds
  · exact Eventually.of_forall fun t =>
      sbxS8_gmp_fullForm_le_killed_of_nonneg r U hU t _ hn'
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact gmpKilledFormDifferenceQuotient_le_of_zeroBoundary r U hU t ht u hu

/-- Locally equal coefficient fields and potentials give equal actual killed
infinitesimal energies on nonnegative zero-boundary data, with their original
physical measures and independently supplied GMP realizations. -/
theorem sbxS8_gmp_killedForm_difference_tendsto_zero_of_nonneg
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1ZeroBoundary U hd lam)
    (hn : ∀ᵐ x ∂EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam,
      0 ≤ densityWeightedH1SpaceValue u x) :
    Tendsto (fun t =>
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t
        (gmpPhysicalH1Value hd ω lam L hω u) -
      semigroupFormDifferenceQuotient ω' hd lam (gmpKilledEndpointKernel r' U hU) t
        (gmpPhysicalH1Value hd ω' lam L hω' u))
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 0) := by
  have h := (sbxS8_gmp_killedForm_tendsto_of_nonneg r U hU u hu hn).sub
    (sbxS8_gmp_killedForm_tendsto_of_nonneg r' U hU u hu hn)
  simpa only [physicalH1FormEnergy_eq_on_zeroBoundary U hU.measurableSet
    ω ω' heq hd lam u hu, sub_self] using h

/-- The discrepancy between the literal killed and full quadratic quotients
satisfies the parallelogram identity, without any sign condition. -/
theorem sbxS8_gmp_killedForm_defect_parallelogram
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (u v : PhysicalH1Space hd lam) :
    let D := fun w : PhysicalH1Space hd lam =>
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t
        (gmpPhysicalH1Value hd ω lam L hω w) -
      semigroupFormDifferenceQuotient ω hd lam r.transitionKernel t
        (gmpPhysicalH1Value hd ω lam L hω w)
    D (v + u) + D (v - u) = 2 * D v + 2 * D u := by
  dsimp only
  have hJa := (gmpPhysicalH1ValueLinear hd ω lam L hω).map_add v u
  have hJs := (gmpPhysicalH1ValueLinear hd ω lam L hω).map_sub v u
  change gmpPhysicalH1Value hd ω lam L hω (v + u) =
    gmpPhysicalH1Value hd ω lam L hω v + gmpPhysicalH1Value hd ω lam L hω u at hJa
  change gmpPhysicalH1Value hd ω lam L hω (v - u) =
    gmpPhysicalH1Value hd ω lam L hω v - gmpPhysicalH1Value hd ω lam L hω u at hJs
  have hPa (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
      r.kernelL2Action hd hL t (f + g) =
        r.kernelL2Action hd hL t f + r.kernelL2Action hd hL t g := by
    have h := r.kernelL2Action_sub hd hL t (f + g) g
    rw [add_sub_cancel_right] at h
    exact sub_eq_iff_eq_add.mp h.symm
  simp only [gmpKilledFormDifferenceQuotient_eq_inner,
    gmpTransitionFormDifferenceQuotient_eq_inner, hJa, hJs,
    map_add, map_sub, hPa, r.kernelL2Action_sub hd hL,
    inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
  ring

/-- A nonnegative zero-boundary shift dominating both signs of a datum removes
the sign restriction from its exact actual killed-form limit. -/
theorem sbxS8_gmp_killedForm_tendsto_of_nonneg_shift
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (u v : PhysicalH1Space hd lam)
    (hu : u ∈ physicalH1ZeroBoundary U hd lam)
    (hv : v ∈ physicalH1ZeroBoundary U hd lam)
    (hn : ∀ w ∈ ({v, v + u, v - u} : Set (PhysicalH1Space hd lam)),
      ∀ᵐ x ∂EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam,
        0 ≤ densityWeightedH1SpaceValue w x) :
    Tendsto (fun t => semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel r U hU) t (gmpPhysicalH1Value hd ω lam L hω u))
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u))) := by
  let D := fun (w : PhysicalH1Space hd lam) (t : ℝ≥0) =>
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t
      (gmpPhysicalH1Value hd ω lam L hω w) -
    semigroupFormDifferenceQuotient ω hd lam r.transitionKernel t
      (gmpPhysicalH1Value hd ω lam L hω w)
  have hD (w : PhysicalH1Space hd lam) (hw : w ∈ physicalH1ZeroBoundary U hd lam)
      (hm : w ∈ ({v, v + u, v - u} : Set (PhysicalH1Space hd lam))) :
      Tendsto (D w) (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 0) := by
    simpa only [D, sub_self] using
      (sbxS8_gmp_killedForm_tendsto_of_nonneg r U hU w hw (hn w hm)).sub
        (sbxS8_gmp_fullForm_tendsto_physicalValue r w)
  have hv' := hD v hv (by simp)
  have hp := hD (v + u) ((physicalH1ZeroBoundary U hd lam).add_mem hv hu) (by simp)
  have hm := hD (v - u) ((physicalH1ZeroBoundary U hd lam).sub_mem hv hu) (by simp)
  have hlim : Tendsto (D u) (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 0) := by
    have h := ((hp.add hm).sub (hv'.const_mul 2)).div_const 2
    have hEq (t : ℝ≥0) : (D (v + u) t + D (v - u) t - 2 * D v t) / 2 = D u t := by
      have hpar := sbxS8_gmp_killedForm_defect_parallelogram r U hU t u v
      change D (v + u) t + D (v - u) t = 2 * D v t + 2 * D u t at hpar
      linarith
    simpa only [hEq, zero_add, mul_zero, sub_zero, zero_div] using h
  have h := (sbxS8_gmp_fullForm_tendsto_physicalValue r u).add hlim
  simpa only [D, add_sub_cancel, add_zero] using h

/-- Every signed spatial test admits a nonnegative spatial test that dominates
its absolute value, still compactly supported in the same open region. -/
theorem sbxS8_exists_spatialTest_dominating {d : ℕ}
    (U : Set (Vec d)) (hU : IsOpen U) (φ : Vec d → ℝ) (hφ : IsSpatialTest U φ) :
    ∃ ψ : Vec d → ℝ, IsSpatialTest U ψ ∧ ∀ x, |φ x| ≤ ψ x := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hφ.2.1 hU hφ.2.2
  obtain ⟨η, hη, hηrange, hηsupp, hηone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV
      hφ.2.1.isClosed hKV
  have hηc : HasCompactSupport η := by
    simpa only [HasCompactSupport, tsupport, hηsupp] using hVc
  have hηU : tsupport η ⊆ U := by
    simpa only [tsupport, hηsupp] using hVU
  obtain ⟨R, hR⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  have hR0 : 0 ≤ R := (norm_nonneg (φ 0)).trans (hR 0)
  refine ⟨R • η, ⟨contDiff_const.smul hη, hηc.smul_left, ?_⟩, ?_⟩
  · exact (tsupport_smul_subset_right (fun _ : Vec d => R) η).trans hηU
  · intro x
    change |φ x| ≤ R * η x
    by_cases hx : x ∈ tsupport φ
    · rw [(hηone x).mp hx, mul_one]
      simpa only [Real.norm_eq_abs] using hR x
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
      exact mul_nonneg hR0 (hηrange ⟨x, rfl⟩).1

/-- The literal killed GMP form has the exact physical-energy limit on every
signed member of the existing smooth interior core. -/
theorem sbxS8_gmp_killedForm_tendsto_of_smoothCore
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1SmoothCore U hd lam) :
    Tendsto (fun t => semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel r U hU) t (gmpPhysicalH1Value hd ω lam L hω u))
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u))) := by
  obtain ⟨φ, hφ, huφ⟩ := physicalH1SmoothCore_exists_spatialTest U u hu
  obtain ⟨ψ, hψ, hbound⟩ := sbxS8_exists_spatialTest_dominating U hU φ hφ
  let v := physicalH1SmoothTest hd lam ψ hψ.1 hψ.2.1
  have hvψ := physicalH1SmoothTest_value hd lam ψ hψ.1 hψ.2.1
  change densityWeightedH1SpaceValue v =ᵐ[_] ψ at hvψ
  have hva := (gmpForceH1ValueLinear hd lam).map_add v u
  have hvs := (gmpForceH1ValueLinear hd lam).map_sub v u
  have hplus := (Lp.ext_iff.mp hva).trans (Lp.coeFn_add _ _)
  have hminus := (Lp.ext_iff.mp hvs).trans (Lp.coeFn_sub _ _)
  apply sbxS8_gmp_killedForm_tendsto_of_nonneg_shift r U hU u v
    (Submodule.le_topologicalClosure _ hu)
    (physicalH1SmoothTest_mem_zeroBoundary U hd lam ψ hψ)
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · filter_upwards [hvψ] with x hx
    rw [hx]
    exact (abs_nonneg _).trans (hbound x)
  · filter_upwards [hplus, hvψ, huφ] with x hx hvx hux
    change densityWeightedH1SpaceValue (v + u) x =
      densityWeightedH1SpaceValue v x + densityWeightedH1SpaceValue u x at hx
    rw [hx, hvx, hux]
    linarith [hbound x, neg_abs_le (φ x)]
  · filter_upwards [hminus, hvψ, huφ] with x hx hvx hux
    change densityWeightedH1SpaceValue (v - u) x =
      densityWeightedH1SpaceValue v x - densityWeightedH1SpaceValue u x at hx
    rw [hx, hvx, hux]
    linarith [hbound x, le_abs_self (φ x)]

/-- The literal anisotropic physical energy is quadratic on the full weighted
weak-gradient space, retaining its original physical measure. -/
theorem sbxS8_physicalH1Energy_parallelogram {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω)
    (u v : PhysicalH1Space hd lam) :
    let E := fun w : PhysicalH1Space hd lam =>
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam w)
    E (v + u) + E (v - u) = 2 * E v + 2 * E u := by
  let E := gmpPhysicalH1Energy hd ω lam L hω
  have hsymm (u v : PhysicalH1Space hd lam) : E u v = E v u :=
    gmpPhysicalH1Energy_symm hd ω lam L hω u v
  have hadd (u v w : PhysicalH1Space hd lam) : E (u + v) w = E u w + E v w :=
    gmpPhysicalH1Energy_add_left hd ω lam L hL hω u v w
  have hsmul (c : ℝ) (u v : PhysicalH1Space hd lam) : E (c • u) v = c * E u v :=
    gmpPhysicalH1Energy_smul_left hd ω lam L hω c u v
  let B : PhysicalH1Space hd lam →ₗ[ℝ] PhysicalH1Space hd lam →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ E hadd (by intro c u v; exact hsmul c u v)
      (by intro u v w; rw [hsymm u (v + w), hadd, hsymm v u, hsymm w u])
      (by intro c u v; rw [hsymm u (c • v), hsmul, hsymm v u]; rfl)
  have hE (w : PhysicalH1Space hd lam) : E w w =
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam w) :=
    (gmpPhysicalH1Energy_eq_source hd ω lam L hω w w).trans
      (sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω w)
  dsimp only
  simp only [← hE]
  change B (v + u) (v + u) + B (v - u) (v - u) = 2 * B v v + 2 * B u u
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  ring

/-- The nonnegative energy defect of actual killing is controlled by a smooth
approximation and the physical energy of its error. This estimate is uniform
over every positive time. -/
theorem sbxS8_gmp_killedForm_energy_defect_le
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t)
    (u v : PhysicalH1Space hd lam)
    (hu : u ∈ physicalH1ZeroBoundary U hd lam)
    (hv : v ∈ physicalH1ZeroBoundary U hd lam) :
    let E := fun w : PhysicalH1Space hd lam =>
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam w)
    let Q := fun w : PhysicalH1Space hd lam =>
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t
        (gmpPhysicalH1Value hd ω lam L hω w)
    E u - Q u ≤ 2 * (E v - Q v) + 2 * E (u - v) := by
  let E := fun w : PhysicalH1Space hd lam =>
    physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam w)
  let Q := fun w : PhysicalH1Space hd lam =>
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t
      (gmpPhysicalH1Value hd ω lam L hω w)
  have hQ (a b : PhysicalH1Space hd lam) :
      Q (b + a) + Q (b - a) = 2 * Q b + 2 * Q a := by
    let J := gmpPhysicalH1ValueLinear hd ω lam L hω
    have hJa := J.map_add b a
    have hJs := J.map_sub b a
    change gmpPhysicalH1Value hd ω lam L hω (b + a) =
      gmpPhysicalH1Value hd ω lam L hω b + gmpPhysicalH1Value hd ω lam L hω a at hJa
    change gmpPhysicalH1Value hd ω lam L hω (b - a) =
      gmpPhysicalH1Value hd ω lam L hω b - gmpPhysicalH1Value hd ω lam L hω a at hJs
    dsimp only [Q]
    simp only [gmpKilledFormDifferenceQuotient_eq_inner, hJa, hJs,
      map_add, map_sub, inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
    ring
  have hE := sbxS8_physicalH1Energy_parallelogram hd ω lam L hL hω (u - v) v
  change E (v + (u - v)) + E (v - (u - v)) = 2 * E v + 2 * E (u - v) at hE
  have hQ' := hQ (u - v) v
  have hsum : v + (u - v) = u := by abel
  rw [hsum] at hE hQ'
  have hz := gmpKilledFormDifferenceQuotient_le_of_zeroBoundary r U hU t ht
    (v - (u - v)) ((physicalH1ZeroBoundary U hd lam).sub_mem hv
      ((physicalH1ZeroBoundary U hd lam).sub_mem hu hv))
  have hn := gmpKilledFormDifferenceQuotient_nonneg r U hU t
    (gmpPhysicalH1Value hd ω lam L hω (u - v))
  change Q (v - (u - v)) ≤ E (v - (u - v)) at hz
  change 0 ≤ Q (u - v) at hn
  change E u - Q u ≤ 2 * (E v - Q v) + 2 * E (u - v)
  linarith

/-- Exact short-time form identification for the actual killed GMP law on the
entire existing completed zero-boundary domain, including signed data. -/
theorem sbxS8_gmp_killedForm_tendsto
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1ZeroBoundary U hd lam) :
    Tendsto (fun t => semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel r U hU) t (gmpPhysicalH1Value hd ω lam L hω u))
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u))) := by
  let E := fun w : PhysicalH1Space hd lam =>
    physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam w)
  let Q := fun (w : PhysicalH1Space hd lam) (t : ℝ≥0) =>
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t
      (gmpPhysicalH1Value hd ω lam L hω w)
  have hE0 : E 0 = 0 := by
    have h := sbxS8_physicalH1Energy_parallelogram hd ω lam L hL hω 0 0
    change E (0 + 0) + E (0 - 0) = 2 * E 0 + 2 * E 0 at h
    simp only [add_zero, sub_zero] at h
    linarith
  have hcont : Continuous E := continuous_physicalH1FormEnergy (hL := hL) (hω := hω)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hopen : IsOpen {v : PhysicalH1Space hd lam | E (u - v) < ε / 4} :=
    isOpen_lt (hcont.comp (continuous_const.sub continuous_id)) continuous_const
  have humem : u ∈ {v : PhysicalH1Space hd lam | E (u - v) < ε / 4} := by
    simpa only [Set.mem_ofPred_eq, sub_self, hE0] using (show 0 < ε / 4 by positivity)
  change u ∈ closure (physicalH1SmoothCore U hd lam : Set (PhysicalH1Space hd lam)) at hu
  obtain ⟨v, hve, hv⟩ := mem_closure_iff.mp hu _ hopen humem
  have hlim := sbxS8_gmp_killedForm_tendsto_of_smoothCore r U hU v hv
  have hnear := Metric.tendsto_nhds.mp hlim (ε / 4) (by positivity)
  filter_upwards [hnear, self_mem_nhdsWithin] with t htv ht
  have hupper := gmpKilledFormDifferenceQuotient_le_of_zeroBoundary r U hU t ht u
    (show u ∈ physicalH1ZeroBoundary U hd lam from hu)
  have hbound := sbxS8_gmp_killedForm_energy_defect_le r U hU t ht u v hu
    (Submodule.le_topologicalClosure _ hv)
  change Q u t ≤ E u at hupper
  change E u - Q u t ≤ 2 * (E v - Q v t) + 2 * E (u - v) at hbound
  change E (u - v) < ε / 4 at hve
  change dist (Q v t) (E v) < ε / 4 at htv
  change dist (Q u t) (E u) < ε
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper), neg_sub]
  rw [Real.dist_eq] at htv
  linarith [neg_le_abs (Q v t - E v)]

/-- Local agreement of both physical fields gives identical infinitesimal
energies for the actual killed kernels on all signed zero-boundary data. -/
theorem sbxS8_gmp_killedForm_difference_tendsto_zero
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (u : PhysicalH1Space hd lam) (hu : u ∈ physicalH1ZeroBoundary U hd lam) :
    Tendsto (fun t =>
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t
        (gmpPhysicalH1Value hd ω lam L hω u) -
      semigroupFormDifferenceQuotient ω' hd lam (gmpKilledEndpointKernel r' U hU) t
        (gmpPhysicalH1Value hd ω' lam L hω' u))
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 0) := by
  have h := (sbxS8_gmp_killedForm_tendsto r U hU u hu).sub
    (sbxS8_gmp_killedForm_tendsto r' U hU u hu)
  simpa only [physicalH1FormEnergy_eq_on_zeroBoundary U hU.measurableSet
    ω ω' heq hd lam u hu, sub_self] using h

/-- Polarization of the literal physical energy on the full weighted H¹ graph. -/
theorem sbxS8_physicalH1Energy_polarization {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω)
    (u v : PhysicalH1Space hd lam) :
    physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam (u + v)) -
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam (u - v)) =
      4 * gmpPhysicalH1Energy hd ω lam L hω u v := by
  let E := gmpPhysicalH1Energy hd ω lam L hω
  have hsymm (u v : PhysicalH1Space hd lam) : E u v = E v u :=
    gmpPhysicalH1Energy_symm hd ω lam L hω u v
  have hadd (u v w : PhysicalH1Space hd lam) : E (u + v) w = E u w + E v w :=
    gmpPhysicalH1Energy_add_left hd ω lam L hL hω u v w
  have hsmul (c : ℝ) (u v : PhysicalH1Space hd lam) : E (c • u) v = c * E u v :=
    gmpPhysicalH1Energy_smul_left hd ω lam L hω c u v
  let B : PhysicalH1Space hd lam →ₗ[ℝ] PhysicalH1Space hd lam →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ E hadd (by intro c u v; exact hsmul c u v)
      (by intro u v w; rw [hsymm u (v + w), hadd, hsymm v u, hsymm w u])
      (by intro c u v; rw [hsymm u (c • v), hsmul, hsymm v u]; rfl)
  have hE (w : PhysicalH1Space hd lam) : E w w =
      physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam w) :=
    (gmpPhysicalH1Energy_eq_source hd ω lam L hω w w).trans
      (sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω w)
  rw [← hE, ← hE]
  change B (u + v) (u + v) - B (u - v) (u - v) = 4 * B u v
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  change E u u + E v u + (E u v + E v v) -
    (E u u - E v u - (E u v - E v v)) = 4 * E u v
  rw [hsymm v u]
  ring

/-- Polarization of the actual killed form uses its proved L² symmetry. -/
theorem sbxS8_gmp_killedForm_polarization
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t
        (f + g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) -
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel r U hU) t
        (f - g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) =
      4 * ((t : ℝ)⁻¹ * inner ℝ (f - gmpKilledL2Operator r U hU t f) g) := by
  simp only [gmpKilledFormDifferenceQuotient_eq_inner, map_add, map_sub,
    inner_sub_left, inner_add_left, inner_sub_right, inner_add_right]
  have hs : inner ℝ (gmpKilledL2Operator r U hU t g) f =
      inner ℝ (gmpKilledL2Operator r U hU t f) g :=
    (gmpKilledL2Operator_isSymmetric r U hU t g f).trans
      (real_inner_comm (gmpKilledL2Operator r U hU t f) g)
  rw [real_inner_comm f g, hs]
  simp only [one_div]
  ring

/-- The mixed actual killed form converges to the full physical bilinear energy
against every member of the completed zero-boundary domain. -/
theorem sbxS8_gmp_killedMixedForm_tendsto
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (u v : PhysicalH1Space hd lam)
    (hu : u ∈ physicalH1ZeroBoundary U hd lam)
    (hv : v ∈ physicalH1ZeroBoundary U hd lam) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      inner ℝ (gmpPhysicalH1Value hd ω lam L hω u -
        gmpKilledL2Operator r U hU t (gmpPhysicalH1Value hd ω lam L hω u))
        (gmpPhysicalH1Value hd ω lam L hω v))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (gmpPhysicalH1Energy hd ω lam L hω u v)) := by
  have h := ((sbxS8_gmp_killedForm_tendsto r U hU (u + v)
    ((physicalH1ZeroBoundary U hd lam).add_mem hu hv)).sub
    (sbxS8_gmp_killedForm_tendsto r U hU (u - v)
      ((physicalH1ZeroBoundary U hd lam).sub_mem hu hv))).div_const 4
  rw [sbxS8_physicalH1Energy_polarization hd ω lam L hL hω u v,
    mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0)] at h
  apply h.congr
  intro t
  have ha := (gmpPhysicalH1ValueLinear hd ω lam L hω).map_add u v
  have hs := (gmpPhysicalH1ValueLinear hd ω lam L hω).map_sub u v
  change gmpPhysicalH1Value hd ω lam L hω (u + v) = _ at ha
  change gmpPhysicalH1Value hd ω lam L hω (u - v) = _ at hs
  rw [ha, hs, sbxS8_gmp_killedForm_polarization]
  change 4 * ((t : ℝ)⁻¹ * inner ℝ (gmpPhysicalH1Value hd ω lam L hω u -
    gmpKilledL2Operator r U hU t (gmpPhysicalH1Value hd ω lam L hω u))
    (gmpPhysicalH1Value hd ω lam L hω v)) / 4 = _
  ring

/-- The two existing physical graph-value maps define the same L² element. -/
theorem sbxS8_physicalZeroBoundaryValue_eq {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hω : IsRegular L ω) (v : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryValue U hd ω lam L hω v =
      gmpPhysicalH1Value hd ω lam L hω v.val := by
  apply Lp.ext
  exact (physicalZeroBoundaryValue_ae_eq U hd ω lam L hω v).trans
    (gmpPhysicalH1Value_ae_eq hd ω lam L hω v.val).symm

/-- The existing physical graph representative has the encoded physical gradient. -/
theorem sbxS8_physicalH1Representative_gradient_ae {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ) (u : PhysicalH1Space hd lam) :
    (physicalH1SpaceRepresentative hd lam u).weakGradient =ᵐ[
      physicalReversibleMeasure ω hd lam] densityWeightedH1SpaceGradient u := by
  apply (gmp_force_ae_iff_physical hd ω lam _).mp
  let g := physicalH1SpaceRepresentative hd lam u
  have hgradient : g.gradient_memLp.toLp g.weakGradient =
      densityWeightedH1SpaceGradient u :=
    congrArg Prod.snd (physicalH1SpaceRepresentative_pair hd lam u)
  exact g.gradient_memLp.coeFn_toLp.symm.trans
    (Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp (EuclideanSpace ℝ (Fin d)) 2
        (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) =>
        (f : Vec d → EuclideanSpace ℝ (Fin d))) hgradient))

/-- The GMP bilinear energy is the literal integral of the existing graph representatives. -/
theorem sbxS8_physicalH1Energy_eq_integral {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (u v : PhysicalH1Space hd lam) :
    gmpPhysicalH1Energy hd ω lam L hω u v =
      (∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u)
        (physicalH1SpaceRepresentative hd lam v) x ∂physicalReversibleMeasure ω hd lam) := by
  apply integral_congr_ae
  filter_upwards [gmpPhysicalH1Gradient_ae_spaceGradient hd ω lam L hω u,
    gmpPhysicalH1Gradient_ae_spaceGradient hd ω lam L hω v,
    sbxS8_physicalH1Representative_gradient_ae hd ω lam u,
    sbxS8_physicalH1Representative_gradient_ae hd ω lam v] with x hu hv hgu hgv
  change (1 / 2 : ℝ) * _ = (1 / 2 : ℝ) * _
  rw [hu, hv, hgu, hgv]
  rfl

/-- A mixed actual killed form has its generator limit against every interior test. -/
theorem sbxS8_gmp_killedMixedForm_tendsto_generator
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z : (gmpKilledInteriorSemigroup r U hU).generatorDomain)
    (v : physicalH1ZeroBoundary U hd lam) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * inner ℝ
      (z.val.val - gmpKilledL2Operator r U hU t z.val.val)
      (physicalZeroBoundaryValue U hd ω lam L hω v))
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (-inner ℝ ((gmpKilledInteriorSemigroup r U hU).generator z).val
        (physicalZeroBoundaryValue U hd ω lam L hω v))) := by
  let S := gmpKilledInteriorSemigroup r U hU
  let jv := physicalZeroBoundaryInteriorValue U hd ω lam L hω v
  have hgen := ((S.tendsto_generator' z).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := jv))).neg
  apply hgen.congr
  intro t
  change -(inner ℝ ((t : ℝ)⁻¹ •
    (gmpKilledL2Operator r U hU t z.val.val - z.val.val))
    (physicalZeroBoundaryValue U hd ω lam L hω v)) = _
  rw [real_inner_smul_left, inner_sub_left, inner_sub_left]
  ring

/-- The generator of the actual killed GMP semigroup satisfies the literal
physical weak zero-boundary equation against every completed H¹ test. -/
theorem sbxS8_gmp_killedGenerator_isPhysicalPair
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z : (gmpKilledInteriorSemigroup r U hU).generatorDomain) :
    IsPhysicalZeroBoundaryGeneratorPair U hd ω lam L hω z.val
      ((gmpKilledInteriorSemigroup r U hU).generator z) := by
  obtain ⟨u, hu, huz⟩ := gmpKilledInteriorGenerator_exists_zeroBoundary r U hU z
  have hvalue := sbxS8_physicalZeroBoundaryValue_eq U hd ω lam L hω
  refine ⟨⟨u, hu⟩, (hvalue _).trans huz, ?_⟩
  intro v
  have hform := sbxS8_gmp_killedMixedForm_tendsto r U hU u v.val hu v.property
  rw [huz, ← hvalue v] at hform
  have hgen := sbxS8_gmp_killedMixedForm_tendsto_generator r U hU z v
  have hlim := tendsto_nhds_unique hform hgen
  exact (sbxS8_physicalH1Energy_eq_integral hd ω lam L hω u v.val).symm.trans hlim

/-- The actual killed unit resolvent is the uniquely constructed physical
zero-boundary variational resolvent on its existing interior L² carrier. -/
theorem sbxS8_gmp_killedUnitResolvent_eq
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    (gmpKilledInteriorSemigroup r U hU).resolvent
        ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩ f =
      physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f := by
  let S := gmpKilledInteriorSemigroup r U hU
  let μ : MarkovProcess.Semigroup.PositiveShift := ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩
  let z : S.generatorDomain := ⟨S.resolvent μ f, S.resolvent_mem_generatorDomain μ f⟩
  have hp := sbxS8_gmp_killedGenerator_isPhysicalPair r U hU z
  have he := (isPhysicalZeroBoundaryGeneratorPair_iff_resolvent
    U hd ω lam L hL hω z.val (S.generator z)).mp hp
  have hg : S.generator z = z.val - f := by
    simp only [z, S.generator_resolvent, μ, one_smul]
  rw [hg, sub_sub_cancel] at he
  exact he.symm

/-- Package the already constructed physical interior evolution with its
proved contraction and strong-continuity laws. -/
noncomputable def sbxS8PhysicalZeroBoundarySemigroup {d : ℕ}
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω) :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (physicalZeroBoundaryL2 U hd ω lam L hω) where
  operator := physicalZeroBoundaryEvolution U hd ω lam L hL hω
  operator_zero := physicalZeroBoundaryEvolution_zero U hd ω lam L hL hω
  operator_add := physicalZeroBoundaryEvolution_add U hd ω lam L hL hω
  opNorm_le_one := norm_physicalZeroBoundaryEvolution_le U hd ω lam L hL hω
  continuous_orbit := continuous_physicalZeroBoundaryEvolution_apply U hd ω lam L hL hω

/-- The actual killed GMP semigroup is the physical zero-boundary evolution.
Both generator inclusions are proved, using the actual unit resolvent for the
reverse inclusion. -/
theorem sbxS8_gmp_killedSemigroup_eq
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) :
    gmpKilledInteriorSemigroup r U hU =
      sbxS8PhysicalZeroBoundarySemigroup U hd ω lam L hL hω := by
  let S := gmpKilledInteriorSemigroup r U hU
  let T := sbxS8PhysicalZeroBoundarySemigroup U hd ω lam L hL hω
  let μ : MarkovProcess.Semigroup.PositiveShift := ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩
  have hforward (z : S.generatorDomain) :
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (T t z.val - z.val))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (S.generator z)) :=
    (sbxS8_gmp_killedGenerator_isPhysicalPair r U hU z).tendsto_evolution_slope hL
  have hdom : S.generatorDomain = T.generatorDomain := by
    ext f
    constructor
    · intro hf
      exact T.mem_generatorDomain_of_tendsto (hforward ⟨f, hf⟩)
    · intro hf
      have hp := (tendsto_physicalZeroBoundaryEvolution_slope_iff
        U hd ω lam L hL hω f (T.generator ⟨f, hf⟩)).mp (T.tendsto_generator' ⟨f, hf⟩)
      have he := (isPhysicalZeroBoundaryGeneratorPair_iff_resolvent
        U hd ω lam L hL hω f (T.generator ⟨f, hf⟩)).mp hp
      rw [← sbxS8_gmp_killedUnitResolvent_eq r U hU] at he
      change S.resolvent μ (f - T.generator ⟨f, hf⟩) = f at he
      exact he ▸ S.resolvent_mem_generatorDomain μ (f - T.generator ⟨f, hf⟩)
  exact S.ext_of_generator T hdom (fun f hfS hfT =>
    (T.generator_eq_of_tendsto ⟨f, hfT⟩ (hforward ⟨f, hfS⟩)).symm)

/-- Canonical local equality of both physical fields intertwines the ACTUAL
killed GMP evolutions on the completed interior L² spaces at every time. -/
theorem sbxS8_gmp_killedSemigroup_localIsometry
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (t : ℝ≥0) (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    physicalZeroBoundaryLocalIsometry U hU.measurableSet hd ω ω' heq lam L L hω hω'
        (gmpKilledInteriorSemigroup r U hU t f) =
      gmpKilledInteriorSemigroup r' U hU t
        (physicalZeroBoundaryLocalIsometry U hU.measurableSet hd ω ω' heq lam L L hω hω' f) := by
  rw [sbxS8_gmp_killedSemigroup_eq r U hU, sbxS8_gmp_killedSemigroup_eq r' U hU]
  exact physicalZeroBoundaryEvolution_localIsometry U hU.measurableSet hd ω ω'
    heq lam L L hL hL hω hω' t f

/-- Finite-time pairings of the actual killed kernels agree on all completed
zero-boundary graph values when both physical fields agree inside the domain. -/
theorem sbxS8_gmp_killedPairing_eq_of_local
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (t : ℝ≥0) (u v : physicalH1ZeroBoundary U hd lam) :
    inner ℝ (gmpKilledL2Operator r U hU t
        (physicalZeroBoundaryValue U hd ω lam L hω u))
      (physicalZeroBoundaryValue U hd ω lam L hω v) =
    inner ℝ (gmpKilledL2Operator r' U hU t
        (physicalZeroBoundaryValue U hd ω' lam L hω' u))
      (physicalZeroBoundaryValue U hd ω' lam L hω' v) := by
  let e := physicalZeroBoundaryLocalIsometry U hU.measurableSet hd ω ω' heq lam L L hω hω'
  let ju := physicalZeroBoundaryInteriorValue U hd ω lam L hω u
  let jv := physicalZeroBoundaryInteriorValue U hd ω lam L hω v
  have h := e.inner_map_map (gmpKilledInteriorSemigroup r U hU t ju) jv
  rw [sbxS8_gmp_killedSemigroup_localIsometry r r' U hU heq t ju,
    physicalZeroBoundaryLocalIsometry_value U hU.measurableSet hd ω ω' heq lam L L hω hω' u,
    physicalZeroBoundaryLocalIsometry_value U hU.measurableSet hd ω ω' heq lam L L hω hω' v] at h
  exact h.symm

/-- The canonical local isometry preserves actual representatives almost everywhere
inside the common domain, rather than only preserving abstract Hilbert pairings. -/
theorem sbxS8_physicalZeroBoundaryLocalIsometry_ae {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (lam L L' : ℝ) (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f).val =ᵐ[
      (physicalReversibleMeasure ω hd lam).restrict U] f.val := by
  let ν := (physicalReversibleMeasure ω hd lam).restrict U
  have hν : ν ≤ (1 : ℝ≥0∞) • physicalReversibleMeasure ω hd lam := by
    simpa only [one_smul] using (Measure.restrict_le_self (μ := physicalReversibleMeasure ω hd lam)
      (s := U))
  have hν' : ν ≤ (1 : ℝ≥0∞) • physicalReversibleMeasure ω' hd lam := by
    rw [show ν = (physicalReversibleMeasure ω' hd lam).restrict U from
      physicalReversibleMeasure_restrict_eq_of_physical_eqOn U hU ω ω' heq hd lam]
    simpa only [one_smul] using (Measure.restrict_le_self (μ := physicalReversibleMeasure ω' hd lam)
      (s := U))
  let R : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ] Lp ℝ 2 ν :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν
  let R' : Lp ℝ 2 (physicalReversibleMeasure ω' hd lam) →L[ℝ] Lp ℝ 2 ν :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν'
  let e := physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
  have heqR : (fun g : physicalZeroBoundaryL2 U hd ω lam L hω => R g.val) =
      (fun g => R' (e g).val) := by
    apply Continuous.ext_on (denseRange_physicalZeroBoundaryInteriorValue U hd ω lam L hω)
      (R.continuous.comp continuous_subtype_val)
      (R'.continuous.comp (continuous_subtype_val.comp e.continuous))
    rintro _ ⟨u, rfl⟩
    change R (physicalZeroBoundaryInteriorValue U hd ω lam L hω u).val =
      R' (e (physicalZeroBoundaryInteriorValue U hd ω lam L hω u)).val
    rw [show e (physicalZeroBoundaryInteriorValue U hd ω lam L hω u) =
      physicalZeroBoundaryInteriorValue U hd ω' lam L' hω' u from
        physicalZeroBoundaryLocalIsometry_value U hU hd ω ω' heq lam L L' hω hω' u]
    apply Lp.ext
    have hu := (physicalZeroBoundaryValue_ae_eq U hd ω lam L hω u).filter_mono
      (ae_mono (show ν ≤ physicalReversibleMeasure ω hd lam by simpa using hν))
    have hu' := (physicalZeroBoundaryValue_ae_eq U hd ω' lam L' hω' u).filter_mono
      (ae_mono (show ν ≤ physicalReversibleMeasure ω' hd lam by simpa using hν'))
    exact (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν _).trans
      ((hu.trans hu'.symm).trans
        (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν' _).symm)
  have hf := congrFun heqR f
  have hRf : R f.val =ᵐ[ν] R' (e f).val := Filter.EventuallyEq.of_eq
    (congrArg (fun g : Lp ℝ 2 ν => (g : Vec d → ℝ)) hf)
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν' _).symm.trans
    (hRf.symm.trans (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν _))

/-- Actual killed GMP evolutions of the same completed graph value agree almost
everywhere in the common domain whenever both physical fields agree there. -/
theorem sbxS8_gmp_killedL2_eq_ae_of_local
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (t : ℝ≥0) (u : physicalH1ZeroBoundary U hd lam) :
    gmpKilledL2Operator r U hU t (physicalZeroBoundaryValue U hd ω lam L hω u) =ᵐ[
      (physicalReversibleMeasure ω hd lam).restrict U]
      gmpKilledL2Operator r' U hU t (physicalZeroBoundaryValue U hd ω' lam L hω' u) := by
  let ju := physicalZeroBoundaryInteriorValue U hd ω lam L hω u
  have h := sbxS8_physicalZeroBoundaryLocalIsometry_ae U hU.measurableSet hd ω ω'
    heq lam L L hω hω' (gmpKilledInteriorSemigroup r U hU t ju)
  rw [sbxS8_gmp_killedSemigroup_localIsometry r r' U hU heq t ju,
    physicalZeroBoundaryLocalIsometry_value U hU.measurableSet hd ω ω' heq lam L L hω hω' u] at h
  exact h.symm

/-- The actual killed L² evolution is the literal endpoint integral of the same
completed graph value, almost everywhere under the physical starting measure. -/
theorem sbxS8_gmp_killedL2_physicalValue_ae_eq_integral
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
    {hω : IsRegular L ω} {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (u : physicalH1ZeroBoundary U hd lam) :
    gmpKilledL2Operator r U hU t (physicalZeroBoundaryValue U hd ω lam L hω u) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      (fun x => ∫ y, densityWeightedH1SpaceValue u.val y
        ∂gmpKilledEndpointKernel r U hU t x) := by
  filter_upwards [gmpKilledL2_ae_eq r U hU t (physicalZeroBoundaryValue U hd ω lam L hω u),
    ae_ae_gmpKilledEndpointKernel_of_ae r U hU t
      (physicalZeroBoundaryValue_ae_eq U hd ω lam L hω u)] with x hx hux
  exact hx.trans (integral_congr_ae hux)

/-- The actual killed endpoint kernels have equal integrals of every common completed
graph value, for physical almost every starting point inside the common domain. -/
theorem sbxS8_gmp_killedIntegral_eq_ae_of_local
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (t : ℝ≥0) (u : physicalH1ZeroBoundary U hd lam) :
    (fun x => ∫ y, densityWeightedH1SpaceValue u.val y
      ∂gmpKilledEndpointKernel r U hU t x) =ᵐ[
      (physicalReversibleMeasure ω hd lam).restrict U]
      (fun x => ∫ y, densityWeightedH1SpaceValue u.val y
        ∂gmpKilledEndpointKernel r' U hU t x) := by
  have hν' : (physicalReversibleMeasure ω hd lam).restrict U ≤
      physicalReversibleMeasure ω' hd lam := by
    rw [physicalReversibleMeasure_restrict_eq_of_physical_eqOn U hU.measurableSet ω ω' heq hd lam]
    exact Measure.restrict_le_self
  exact ((sbxS8_gmp_killedL2_physicalValue_ae_eq_integral r U hU t u).filter_mono
    (ae_mono Measure.restrict_le_self)).symm.trans
      ((sbxS8_gmp_killedL2_eq_ae_of_local r r' U hU heq t u).trans
        ((sbxS8_gmp_killedL2_physicalValue_ae_eq_integral r' U hU t u).filter_mono
          (ae_mono hν')))

#print axioms sbxS8_gmp_closedForm_tendsto
#print axioms sbxS8_gmp_closedForm_domain_iff
#print axioms sbxS8_gmp_closedForm_difference_tendsto_zero
#print axioms sbxS8_gmp_fullForm_le_killed_of_nonneg
#print axioms sbxS8_gmp_fullForm_tendsto_physicalValue
#print axioms sbxS8_gmp_killedForm_tendsto_of_nonneg
#print axioms sbxS8_gmp_killedForm_difference_tendsto_zero_of_nonneg
#print axioms sbxS8_gmp_killedForm_defect_parallelogram
#print axioms sbxS8_gmp_killedForm_tendsto_of_nonneg_shift
#print axioms sbxS8_exists_spatialTest_dominating
#print axioms sbxS8_gmp_killedForm_tendsto_of_smoothCore
#print axioms sbxS8_physicalH1Energy_parallelogram
#print axioms sbxS8_gmp_killedForm_energy_defect_le
#print axioms sbxS8_gmp_killedForm_tendsto
#print axioms sbxS8_gmp_killedForm_difference_tendsto_zero

#print axioms sbxS8_physicalH1Energy_polarization
#print axioms sbxS8_gmp_killedForm_polarization
#print axioms sbxS8_gmp_killedMixedForm_tendsto
#print axioms sbxS8_physicalZeroBoundaryValue_eq
#print axioms sbxS8_physicalH1Representative_gradient_ae
#print axioms sbxS8_physicalH1Energy_eq_integral
#print axioms sbxS8_gmp_killedMixedForm_tendsto_generator
#print axioms sbxS8_gmp_killedGenerator_isPhysicalPair

#print axioms sbxS8_gmp_killedUnitResolvent_eq
#print axioms sbxS8PhysicalZeroBoundarySemigroup
#print axioms sbxS8_gmp_killedSemigroup_eq
#print axioms sbxS8_gmp_killedSemigroup_localIsometry

#print axioms sbxS8_gmp_killedPairing_eq_of_local

#print axioms sbxS8_physicalZeroBoundaryLocalIsometry_ae
#print axioms sbxS8_gmp_killedL2_eq_ae_of_local

#print axioms sbxS8_gmp_killedL2_physicalValue_ae_eq_integral
#print axioms sbxS8_gmp_killedIntegral_eq_ae_of_local

#lint

end EinsteinFull.Blueprint
