import EinsteinFull.Work.W1.GMPKilledEndpointSupport
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Strong continuity at zero of the actual killed GMP operators

The operators are the survival-weighted endpoint expectations constructed in
`GMPKilledEndpointSupport`. Compact interior tests converge by path continuity
and dominated convergence. Contractivity and the actual completed smooth core
extend this to every physical interior L² datum. Ambient data converge to the
physical interior projection.

This supplies a predecessor for the environmental/regeneration factorization
chain. The killed semigroup law and identification with the variational interior
evolution remain separate obligations.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet

noncomputable section

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)

/-- Bounded inputs have bounded actual killed expectations, at every time and start. -/
theorem norm_integral_gmpKilledEndpointKernel_le (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) (φ : Vec d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hφ : ∀ y, ‖φ y‖ ≤ B) :
    ‖∫ y, φ y ∂gmpKilledEndpointKernel G U hU t x‖ ≤ B := by
  letI := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  have hm : (gmpKilledEndpointKernel G U hU t x).real Set.univ ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      simpa only [ENNReal.ofReal_one] using gmpKilledEndpointKernel_mass_le_one G U hU t x)
  exact (norm_integral_le_of_norm_le_const (ae_of_all _ hφ)).trans
    (mul_le_of_le_one_right hB hm)

/-- The actual physical representative of a smooth interior graph value is its literal test. -/
theorem physicalZeroBoundaryValue_smoothTest_ae_eq
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest U φ) :
    physicalZeroBoundaryValue U hd ω lam L hω
      ⟨physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1,
        physicalH1SmoothTest_mem_zeroBoundary U hd lam φ hφ⟩
      =ᵐ[physicalReversibleMeasure ω hd lam] φ := by
  apply (physicalZeroBoundaryValue_ae_eq U hd ω lam L hω _).trans
  apply (ae_withDensity_iff_volume_of_continuous_pos
    (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
    (physicalReversibleDensity_pos ω hd lam) _).mpr
  exact (ae_withDensity_iff_volume_of_continuous_pos
    (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
    (physicalForceWeight_pos hd lam) _).mp
    (physicalH1SmoothTest_value hd lam φ hφ.1 hφ.2.1)

/-- Compact interior continuous data recover their physical diagonal pairing at zero. -/
theorem tendsto_inner_gmpKilledL2_at_zero_of_continuous
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (φ : Vec d → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hf : f =ᵐ[physicalReversibleMeasure ω hd lam] φ) :
    Tendsto (fun t : ℝ≥0 => inner ℝ (gmpKilledL2 G U hU t f) f)
      (𝓝 0) (𝓝 (‖f‖ ^ 2)) := by
  letI : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    densityWeightedMeasure_locallyFinite _ (physicalReversibleDensity_continuous ω hd lam)
  obtain ⟨B, hB⟩ := (hφc.isCompact_range hφ).isBounded.exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg (φ 0)).trans (hB _ ⟨0, rfl⟩)
  have hb : ∀ y, ‖φ y‖ ≤ B := fun y => hB _ ⟨y, rfl⟩
  let F : ℝ≥0 → Vec d → ℝ := fun t x =>
    (∫ y, φ y ∂gmpKilledEndpointKernel G U hU t x) * φ x
  have he (t : ℝ≥0) : inner ℝ (gmpKilledL2 G U hU t f) f =
      ∫ x, F t x ∂physicalReversibleMeasure ω hd lam := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [gmpKilledL2_ae_eq G U hU t f, hf,
      ae_ae_gmpKilledEndpointKernel_of_ae G U hU t hf] with x hx hfx hker
    rw [hx, hfx, integral_congr_ae hker]
    simp only [F, RCLike.inner_apply, conj_trivial]
    ring
  have hmeas (t : ℝ≥0) : AEStronglyMeasurable (F t) (physicalReversibleMeasure ω hd lam) :=
    ((hφ.stronglyMeasurable.integral_kernel (κ := gmpKilledEndpointKernel G U hU t)).mul
      hφ.stronglyMeasurable).aestronglyMeasurable
  have hbound (t : ℝ≥0) : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      ‖F t x‖ ≤ B * ‖φ x‖ := by
    apply ae_of_all
    intro x
    change ‖(∫ y, φ y ∂gmpKilledEndpointKernel G U hU t x) * φ x‖ ≤ B * ‖φ x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_integral_gmpKilledEndpointKernel_le G U hU t x φ B hB0 hb) (norm_nonneg _)
  have hlim : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      Tendsto (fun t => F t x) (𝓝 0) (𝓝 (φ x ^ 2)) := by
    apply ae_of_all
    intro x
    by_cases hx : x ∈ U
    · simpa only [F, pow_two] using
        (tendsto_integral_gmpKilledEndpointKernel_at_zero G U hU x hx φ hφ B
          (fun y => by simpa only [Real.norm_eq_abs] using hb y)).mul_const (φ x)
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))
      simp only [F, hz, mul_zero, zero_pow (by decide : 2 ≠ 0)]
      exact tendsto_const_nhds
  have h := tendsto_integral_filter_of_dominated_convergence (fun x => B * ‖φ x‖)
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound)
    ((hφ.integrable_of_hasCompactSupport hφc).norm.const_mul B) hlim
  have hi : (∫ x, φ x ^ 2 ∂physicalReversibleMeasure ω hd lam) = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial, pow_two]
  simpa only [← he, hi] using h

private theorem tendsto_of_inner_and_contraction {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {l : Filter ι} (T : ι → E) (f : E)
    (hT : ∀ t, ‖T t‖ ≤ ‖f‖)
    (hi : Tendsto (fun t => inner ℝ (T t) f) l (𝓝 (‖f‖ ^ 2))) :
    Tendsto T l (𝓝 f) := by
  have hb : ∀ t, ‖T t - f‖ ^ 2 ≤ 2 * (‖f‖ ^ 2 - inner ℝ (T t) f) := by
    intro t
    rw [norm_sub_sq_real]
    have hn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hT t)
    linarith only [hn]
  have hz : Tendsto (fun t => 2 * (‖f‖ ^ 2 - inner ℝ (T t) f)) l (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ι => ‖f‖ ^ 2) l (𝓝 (‖f‖ ^ 2))).sub hi).const_mul 2
  have hs := squeeze_zero (fun t => sq_nonneg ‖T t - f‖) hb hz
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

/-- Compact interior continuous data are strongly recovered by the actual killed L² operators. -/
theorem tendsto_gmpKilledL2_at_zero_of_continuous
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (φ : Vec d → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hf : f =ᵐ[physicalReversibleMeasure ω hd lam] φ) :
    Tendsto (fun t : ℝ≥0 => gmpKilledL2 G U hU t f) (𝓝 0) (𝓝 f) :=
  tendsto_of_inner_and_contraction _ f (fun t => gmpKilledL2_norm_le G U hU t f)
    (tendsto_inner_gmpKilledL2_at_zero_of_continuous G U hU f φ hφ hφc hφU hf)

private def killedRecoverySubmodule (U : Set (Vec d)) (hU : IsOpen U) :
    Submodule ℝ (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) where
  carrier := {f | Tendsto (fun t : ℝ≥0 => gmpKilledL2 G U hU t f) (𝓝 0) (𝓝 f)}
  zero_mem' := by
    simpa only [Set.mem_setOf_eq, ← gmpKilledL2Operator_apply, map_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (0 : Lp ℝ 2
        (physicalReversibleMeasure ω hd lam))) (𝓝 0) (𝓝 0))
  add_mem' := by
    intro f g hf hg
    simpa only [Set.mem_setOf_eq, gmpKilledL2_add] using hf.add hg
  smul_mem' := by
    intro c f hf
    simpa only [Set.mem_setOf_eq, gmpKilledL2_smul] using hf.const_smul c

private theorem killedRecoverySubmodule_isClosed (U : Set (Vec d)) (hU : IsOpen U) :
    IsClosed (killedRecoverySubmodule G U hU : Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) := by
  have hLip (t : ℝ≥0) : LipschitzWith 1 (gmpKilledL2 G U hU t) :=
    (gmpKilledL2Operator G U hU t).lipschitzWith_of_opNorm_le
      (gmpKilledL2Operator_norm_le_one G U hU t)
  exact (LipschitzWith.uniformEquicontinuous (fun t => gmpKilledL2 G U hU t) 1 hLip).equicontinuous.isClosed_setOf_tendsto
    continuous_id

private theorem closure_span_values_mem {V H : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (s : Set V) (J : (Submodule.span ℝ s).topologicalClosure →L[ℝ] H)
    (S : Submodule ℝ H) (hS : IsClosed (S : Set H))
    (ht : ∀ u (hu : u ∈ s), J ⟨u, Submodule.le_topologicalClosure _ (Submodule.subset_span hu)⟩ ∈ S)
    (u : (Submodule.span ℝ s).topologicalClosure) : J u ∈ S := by
  have hcore (v : V) (hv : v ∈ Submodule.span ℝ s) :
      ∀ hv' : v ∈ (Submodule.span ℝ s).topologicalClosure, J ⟨v, hv'⟩ ∈ S := by
    induction hv using Submodule.span_induction with
    | mem v hv => intro hv'; exact ht v hv
    | zero =>
      intro hv'
      change J 0 ∈ S
      rw [map_zero]
      exact S.zero_mem
    | add v w hv hw ihv ihw =>
      intro hvw'
      have hv' : v ∈ (Submodule.span ℝ s).topologicalClosure :=
        Submodule.le_topologicalClosure _ hv
      have hw' : w ∈ (Submodule.span ℝ s).topologicalClosure :=
        Submodule.le_topologicalClosure _ hw
      change J ((⟨v, hv'⟩ : (Submodule.span ℝ s).topologicalClosure) + ⟨w, hw'⟩) ∈ S
      rw [map_add]
      exact S.add_mem (ihv hv') (ihw hw')
    | smul c v hv ihv =>
      intro hcv'
      have hv' : v ∈ (Submodule.span ℝ s).topologicalClosure :=
        Submodule.le_topologicalClosure _ hv
      change J (c • (⟨v, hv'⟩ : (Submodule.span ℝ s).topologicalClosure)) ∈ S
      rw [map_smul]
      exact S.smul_mem c (ihv hv')
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp u.property
  let vs : ℕ → (Submodule.span ℝ s).topologicalClosure :=
    fun n => ⟨v n, Submodule.le_topologicalClosure _ (hv n)⟩
  have htend : Tendsto vs atTop (𝓝 u) := tendsto_subtype_rng.mpr hlim
  exact hS.mem_of_tendsto ((J.continuous.tendsto u).comp htend)
    (Eventually.of_forall fun n => hcore (v n) (hv n) _)

private theorem interior_le_of_smooth_mem
    (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (S : Submodule ℝ (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
    (hS : IsClosed (S : Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam))))
    (ht : ∀ (φ : Vec d → ℝ) (hφ : IsSpatialTest U φ),
      physicalZeroBoundaryValue U hd ω lam L hω
        ⟨physicalH1SmoothTest hd lam φ hφ.1 hφ.2.1,
          physicalH1SmoothTest_mem_zeroBoundary U hd lam φ hφ⟩ ∈ S) :
    physicalZeroBoundaryL2 U hd ω lam L hω ≤ S := by
  have hgraph (u : physicalH1ZeroBoundary U hd lam) :
      physicalZeroBoundaryValue U hd ω lam L hω u ∈ S := by
    apply closure_span_values_mem _ (physicalZeroBoundaryValue U hd ω lam L hω) S hS ?_ u
    rintro v ⟨φ, hφ, rfl⟩
    exact ht φ hφ
  exact closure_minimal (by rintro _ ⟨u, rfl⟩; exact hgraph u) hS

/-- Every actual interior physical L² datum is strongly recovered at time zero. -/
theorem tendsto_gmpKilledL2_at_zero_of_mem
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun t : ℝ≥0 => gmpKilledL2 G U hU t f) (𝓝 0) (𝓝 f) := by
  apply interior_le_of_smooth_mem U hd ω lam L hω (killedRecoverySubmodule G U hU)
    (killedRecoverySubmodule_isClosed G U hU) ?_ hf
  intro φ hφ
  exact tendsto_gmpKilledL2_at_zero_of_continuous G U hU _ φ hφ.1.continuous hφ.2.1 hφ.2.2
    (physicalZeroBoundaryValue_smoothTest_ae_eq U hd ω lam L hω φ hφ)

/-- Strong continuity at zero holds on exactly the carrier of the physical interior evolution. -/
theorem tendsto_gmpKilledInteriorOperator_at_zero
    (U : Set (Vec d)) (hU : IsOpen U) (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Tendsto (fun t : ℝ≥0 => gmpKilledInteriorOperator G U hU t f) (𝓝 0) (𝓝 f) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_gmpKilledL2_at_zero_of_mem G U hU f.val f.property

/-- Actual killed expectations depend only on the interior physical projection of their input. -/
theorem gmpKilledL2_projection (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpKilledL2 G U hU t (physicalZeroBoundaryProjection U hd ω lam L hω f) =
      gmpKilledL2 G U hU t f := by
  classical
  apply Lp.ext
  filter_upwards [gmpKilledL2_ae_eq G U hU t
      (physicalZeroBoundaryProjection U hd ω lam L hω f),
    gmpKilledL2_ae_eq G U hU t f,
    ae_ae_gmpKilledEndpointKernel_of_ae G U hU t
      (physicalZeroBoundaryProjection_ae_eq_indicator U hU hd ω lam L hω f)]
    with x hx hy hproj
  rw [hx, hy]
  apply integral_congr_ae
  filter_upwards [hproj, gmpKilledEndpointKernel_ae_mem G U hU t x] with y hp hyU
  exact hp.trans (Set.indicator_of_mem hyU f)

/-- Ambient physical L² data converge strongly to their actual interior projection. -/
theorem tendsto_gmpKilledL2_at_zero
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun t : ℝ≥0 => gmpKilledL2 G U hU t f) (𝓝 0)
      (𝓝 (physicalZeroBoundaryProjection U hd ω lam L hω f)) := by
  simpa only [gmpKilledL2_projection] using
    tendsto_gmpKilledL2_at_zero_of_mem G U hU
      (physicalZeroBoundaryProjection U hd ω lam L hω f)
      (physicalZeroBoundaryProjection_mem U hd ω lam L hω f)

end
end EinsteinFull
