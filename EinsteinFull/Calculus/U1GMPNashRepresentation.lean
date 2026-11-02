import EinsteinFull.Calculus.ParabolicBridgeCoeff
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinFull.Calculus.U2GMPNashDomain
import EinsteinFull.Calculus.U8PhysicalUltracontractive
import EinsteinFull.Calculus.U7PhysicalL1Contraction
import EinsteinFull.Calculus.PhysicalMeasureSupport
import EinsteinFull.Calculus.PhysicalGaugeDomainSupport
import EinsteinRelation.Diffusion.PhysicalH1Representatives
import EinsteinFull.Calculus.C16SourceExponentialMax
import EinsteinFull.Calculus.C10PhysicalMPC2BallStoppedMartingale
import EinsteinFull.Calculus.C9PhysicalPathBallExitExhaustion
import EinsteinFull.Calculus.C4FoundationPhysicalLawUniqueness
import EinsteinFull.Calculus.U2GMPKernelReversibility
import EinsteinFull.Calculus.C8GMPMartingale
import EllipticRegularity.Parabolic.NashKernel.AssemblyKernel

/-! The normalized spatial coefficient satisfies the hypotheses used by the
parabolic Nash kernel construction. -/

noncomputable section

namespace EinsteinFull

open EinsteinRelation PDE MeasureTheory Set Filter

/-- Normalize the lower ellipticity constant to one, including inverse
ellipticity, without changing the coordinate carrier. -/
theorem u1_normalized_parabolic_coefficient {d : ℕ} (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (s t : ℝ) :
    IsParabolicCoeff 1 (Λ ^ 2)
      (fun z : EinsteinRelation.Vec d × ℝ => Λ • ω.1 z.1) univ (Icc s t) := by
  refine ⟨fun j k => ?_, ae_of_all _ fun z => ?_⟩
  · exact (((continuous_const.mul ((continuous_apply k).comp
      ((continuous_apply j).comp ω.1.continuous))).comp continuous_fst)).measurable.aemeasurable
  · exact ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hΛ
      (hω.1 z.1).1 (fun ξ => ((hω.1 z.1).2 ξ).1)
      (fun ξ => ((hω.1 z.1).2 ξ).2)

/-- The physical divergence coefficient, including the factor one half,
normalized to lower ellipticity one. -/
theorem u1_normalized_reduced_parabolic_coefficient {d : ℕ} (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (s t : ℝ) :
    IsParabolicCoeff 1 (sourceReducedBound Λ ^ 2)
      (fun z : EinsteinRelation.Vec d × ℝ =>
        (2 * sourceReducedBound Λ) • ((1 / 2 : ℝ) • reducedCoefficient ω z.1))
      univ (Icc s t) := by
  have hs := sourceReducedBound_support hΛ hω
  have heq : ∀ x, (2 * sourceReducedBound Λ) • ((1 / 2 : ℝ) • reducedCoefficient ω x) =
      sourceReducedBound Λ • reducedCoefficient ω x := by
    intro x
    rw [smul_smul]
    congr 1
    ring
  refine ⟨fun j k => ?_, ae_of_all _ fun z => ?_⟩
  · have hc : Continuous (reducedCoefficient ω) := (reduce ω).1.continuous
    have hm : AEMeasurable (fun z : EinsteinRelation.Vec d × ℝ =>
        sourceReducedBound Λ * reducedCoefficient ω z.1 j k) :=
      ((continuous_const.mul ((continuous_apply k).comp
        ((continuous_apply j).comp hc))).comp continuous_fst).measurable.aemeasurable
    have hfun : (fun z : EinsteinRelation.Vec d × ℝ =>
        ((2 * sourceReducedBound Λ) • ((1 / 2 : ℝ) • reducedCoefficient ω z.1)) j k) =
        (fun z => sourceReducedBound Λ * reducedCoefficient ω z.1 j k) := by
      funext z
      simpa only [Matrix.smul_apply, smul_eq_mul] using
        congrArg (fun A : EinsteinRelation.Mat d => A j k) (heq z.1)
    rw [hfun]
    exact hm.mono_measure Measure.restrict_le_self
  · rw [heq]
    exact ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hs.1
      (hs.2.1 z.1).1 (fun ξ => ((hs.2.1 z.1).2 ξ).1)
      (fun ξ => ((hs.2.1 z.1).2 ξ).2)

open PDE.NashKernelDyadic PDE.Parabolic.NashKernel
open scoped BigOperators NNReal Topology

/-- The actual physical transition kernel applied to a dyadic cube. -/
def u1PhysicalDyadicOutput {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ)
    (x : EinsteinRelation.Vec d) : ℝ :=
  ∫ y, (cube n k).indicator (fun _ => (1 : ℝ)) y ∂
    (Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x)

/-- Dyadic outputs of the actual physical kernel are measurable. -/
theorem u1_physicalDyadicOutput_measurable {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ) :
    Measurable (u1PhysicalDyadicOutput hd ω Λ hΛ hω hSmooth t n k) := by
  let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth
  have heq : u1PhysicalDyadicOutput hd ω Λ hΛ hω hSmooth t n k =
      fun x => (P t x (cube n k)).toReal := by
    funext x
    simp only [u1PhysicalDyadicOutput, integral_indicator (measurableSet_cube n k),
      integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
    rfl
  rw [heq]
  exact ((P t).measurable_coe (measurableSet_cube n k)).ennreal_toReal

/-- Cube outputs are nonnegative. -/
theorem u1_physicalDyadicOutput_nonneg {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ) (x : EinsteinRelation.Vec d) :
    0 ≤ u1PhysicalDyadicOutput hd ω Λ hΛ hω hSmooth t n k x := by
  apply integral_nonneg
  intro y
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) y

/-- The actual kernel respects the finite partition of a dyadic cube. -/
theorem u1_physicalDyadicOutput_child_add {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ) (x : EinsteinRelation.Vec d) :
    u1PhysicalDyadicOutput hd ω Λ hΛ hω hSmooth t n k x =
      ∑ ε : Fin d → Bool, u1PhysicalDyadicOutput hd ω Λ hΛ hω hSmooth t (n + 1) (child k ε) x := by
  let μ := Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x
  let : IsProbabilityMeasure μ := ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω 0 Λ hΛ hω hSmooth t x⟩
  have hi : ∀ ε : Fin d → Bool, Integrable
      ((cube (n + 1) (child k ε)).indicator (fun _ => (1 : ℝ))) μ := by
    intro ε
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_cube _ _)
  change (∫ y, (cube n k).indicator (fun _ => (1 : ℝ)) y ∂μ) =
    ∑ ε : Fin d → Bool, ∫ y, (cube (n + 1) (child k ε)).indicator (fun _ => (1 : ℝ)) y ∂μ
  rw [indicator_cube_succ_eq_sum]
  simp only [Finset.sum_apply]
  exact integral_finsetSum _ (fun ε _ => hi ε)


/-- The signed physical transition kernel applied to a dyadic cube. -/
def u1SignedPhysicalDyadicOutput {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ)
    (x : EinsteinRelation.Vec d) : ℝ :=
  ∫ y, (cube n k).indicator (fun _ => (1 : ℝ)) y ∂
    (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)

/-- Dyadic outputs of the signed physical kernel are measurable. -/
theorem u1_signedPhysicalDyadicOutput_measurable {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ) :
    Measurable (u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k) := by
  let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  have heq : u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k =
      fun x => (P t x (cube n k)).toReal := by
    funext x
    simp only [u1SignedPhysicalDyadicOutput, integral_indicator (measurableSet_cube n k),
      integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
    rfl
  rw [heq]
  exact ((P t).measurable_coe (measurableSet_cube n k)).ennreal_toReal

/-- Cube outputs are nonnegative. -/
theorem u1_signedPhysicalDyadicOutput_nonneg {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ) (x : EinsteinRelation.Vec d) :
    0 ≤ u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k x := by
  apply integral_nonneg
  intro y
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) y

/-- The signed physical kernel respects the finite partition of a dyadic cube. -/
theorem u1_signedPhysicalDyadicOutput_child_add {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ) (x : EinsteinRelation.Vec d) :
    u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k x =
      ∑ ε : Fin d → Bool, u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t (n + 1) (child k ε) x := by
  let μ := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x
  let : IsProbabilityMeasure μ := ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
  have hi : ∀ ε : Fin d → Bool, Integrable
      ((cube (n + 1) (child k ε)).indicator (fun _ => (1 : ℝ))) μ := by
    intro ε
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_cube _ _)
  change (∫ y, (cube n k).indicator (fun _ => (1 : ℝ)) y ∂μ) =
    ∑ ε : Fin d → Bool, ∫ y, (cube (n + 1) (child k ε)).indicator (fun _ => (1 : ℝ)) y ∂μ
  rw [indicator_cube_succ_eq_sum]
  simp only [Finset.sum_apply]
  exact integral_finsetSum _ (fun ε _ => hi ε)

open EinsteinRelation.External.GantertSection7Support PDE.NashKernelExtend
open scoped ENNReal

/-- A Lebesgue L² input is L² for the actual unforced reversible measure. -/
theorem u1_unforced_volume_memLp_physical {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω)
    (f : EinsteinRelation.Vec d → ℝ) (hf : MemLp f 2 volume) :
    MemLp f 2 (physicalReversibleMeasure ω hd 0) := by
  exact hf.of_measure_le_smul (c := ENNReal.ofReal (Real.exp (2 * Λ)))
    ENNReal.ofReal_ne_top (u4_unforced_physical_measure_comparable hd ω Λ hω).1

/-- The physical kernel and physical L² semigroup agree Lebesgue almost everywhere. -/
theorem u1_unforced_kernel_integral_ae_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : EinsteinRelation.Vec d → ℝ) (hf : MemLp f 2 volume) :
    (fun x => ∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t
      ((u1_unforced_volume_memLp_physical hd ω Λ hω f hf).toLp f) x) := by
  exact (Measure.absolutelyContinuous_of_le_smul
    (u4_unforced_physical_measure_comparable hd ω Λ hω).2).ae_eq
    (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2 hd ω 0 Λ hΛ hω hSmooth t f
      (u1_unforced_volume_memLp_physical hd ω Λ hω f hf)).2

/-- The positive signed physical density has the same null sets as volume. -/
theorem u1_signed_physical_ae_to_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) {p : EinsteinRelation.Vec d → Prop}
    (hp : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, p x) :
    ∀ᵐ x ∂(volume : Measure (EinsteinRelation.Vec d)), p x := by
  rw [EinsteinRelation.Diffusion.physicalReversibleMeasure_eq_sourceDensity] at hp
  unfold EinsteinRelation.SpatialDirichlet.densityWeightedMeasure at hp
  rw [ae_withDensity_iff ((EinsteinRelation.SpatialDirichlet.continuousSourcePhysicalDensity
    ω hd lam).measurable.ennreal_ofReal)] at hp
  filter_upwards [hp] with x hx
  exact hx (ENNReal.ofReal_pos.mpr
    (EinsteinRelation.SpatialDirichlet.positiveSourcePhysicalDensity ω hd lam x)).ne'

/-- Signed physical L² kernel association holds for Lebesgue almost every start. -/
theorem u1_signed_kernel_integral_ae_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : EinsteinRelation.Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    (fun x => ∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω lam Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f) x) := by
  exact u1_signed_physical_ae_to_volume hd ω lam
    (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2 hd ω lam Λ hΛ hω hSmooth t f hf).2

/-- A bounded measurable indicator belongs to signed physical L², since the
actual reversible measure is locally finite. -/
theorem u1_signed_physical_bounded_indicator_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (A : Set (EinsteinRelation.Vec d))
    (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A) :
    MemLp (A.indicator (fun _ => (1 : ℝ))) 2 (physicalReversibleMeasure ω hd lam) := by
  let : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hfinite : physicalReversibleMeasure ω hd lam A < ∞ :=
    lt_of_le_of_lt (measure_mono subset_closure) hbounded.isCompact_closure.measure_lt_top
  exact memLp_indicator_const 2 hA (1 : ℝ) (Or.inr hfinite.ne)

/-- Each dyadic cube indicator belongs to the actual signed physical L² space. -/
theorem u1_signed_physical_dyadic_indicator_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (n : ℕ) (k : Fin d → ℤ) :
    MemLp ((cube n k).indicator (fun _ => (1 : ℝ))) 2
      (physicalReversibleMeasure ω hd lam) := by
  apply u1_signed_physical_bounded_indicator_memLp hd ω lam _ (measurableSet_cube n k)
  have hc : IsCompact (Set.pi Set.univ fun i : Fin d =>
      Set.Icc ((k i : ℝ) / 2 ^ n) (((k i : ℝ) + 1) / 2 ^ n)) :=
    by
      simpa only [← Set.mem_univ_pi] using!
        (isCompact_pi_infinite (fun i : Fin d =>
          isCompact_Icc (a := (k i : ℝ) / 2 ^ n) (b := ((k i : ℝ) + 1) / 2 ^ n)))
  apply hc.isBounded.subset
  intro y hy
  simp only [cube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
    Set.mem_Icc] at hy ⊢
  exact fun i => ⟨(hy i).1, (hy i).2.le⟩

/-- The signed dyadic output is the actual physical L² evolution of the same
cube indicator, for Lebesgue almost every starting point. -/
theorem u1_signed_dyadic_output_ae_physical_L2 {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ) :
    u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k =ᵐ[volume]
      (fun x => Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
        ((u1_signed_physical_dyadic_indicator_memLp hd ω lam n k).toLp
          ((cube n k).indicator (fun _ => (1 : ℝ)))) x) := by
  exact u1_signed_kernel_integral_ae_volume hd ω lam Λ hΛ hω hSmooth t _
    (u1_signed_physical_dyadic_indicator_memLp hd ω lam n k)

/-- Signed physical L² inputs are integrable against the transition kernel for
Lebesgue almost every starting point. -/
theorem u1_signed_kernel_integrable_ae_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : EinsteinRelation.Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    ∀ᵐ x ∂(volume : Measure (EinsteinRelation.Vec d)),
      Integrable f (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) := by
  exact u1_signed_physical_ae_to_volume hd ω lam
    (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2 hd ω lam Λ hΛ hω hSmooth t f hf).1

/-- The signed kernel is additive on its physical L² inputs, almost everywhere
for Lebesgue measure on starting points. -/
theorem u1_signed_kernel_L2_add_ae_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f g : EinsteinRelation.Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (hg : MemLp g 2 (physicalReversibleMeasure ω hd lam)) :
    (fun x => ∫ y, (f + g) y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω lam Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => (∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω lam Λ hΛ hω hSmooth t x) +
      ∫ y, g y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) := by
  filter_upwards [u1_signed_kernel_integrable_ae_volume hd ω lam Λ hΛ hω hSmooth t f hf,
    u1_signed_kernel_integrable_ae_volume hd ω lam Λ hΛ hω hSmooth t g hg] with x hfi hgi
  exact integral_add hfi hgi

/-- Finite sums of signed physical L² inputs commute with kernel integration
for Lebesgue almost every starting point. -/
theorem u1_signed_kernel_L2_sum_ae_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → EinsteinRelation.Vec d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (physicalReversibleMeasure ω hd lam)) :
    (fun x => ∫ y, (∑ i ∈ S, f i) y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω lam Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => ∑ i ∈ S, ∫ y, f i y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω lam Λ hΛ hω hSmooth t x) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hS : MemLp (∑ j ∈ S, f j) 2 (physicalReversibleMeasure ω hd lam) :=
      memLp_finsetSum' S fun j _ => hf j
    filter_upwards [u1_signed_kernel_L2_add_ae_volume
      hd ω lam Λ hΛ hω hSmooth t (f i) (∑ j ∈ S, f j) (hf i) hS, ih] with x ha hb
    simpa only [Pi.add_apply] using ha.trans (congrArg (fun z => _ + z) hb)

/-- Compact continuous tests are integrable against every signed physical kernel. -/
theorem u1_signed_kernel_compact_integrable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (x : EinsteinRelation.Vec d)
    (f : EinsteinRelation.Vec d → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) := by
  let : IsProbabilityMeasure (Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω lam Λ hΛ hω hSmooth t x) :=
    ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
  exact hf.integrable_of_hasCompactSupport hc

/-- Signed physical kernel integration is additive on compact continuous tests. -/
theorem u1_signed_kernel_compact_add {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (x : EinsteinRelation.Vec d)
    (f g : EinsteinRelation.Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ y, (f + g) y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω lam Λ hΛ hω hSmooth t x) =
    (∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) +
      ∫ y, g y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x := by
  exact integral_add (u1_signed_kernel_compact_integrable hd ω lam Λ hΛ hω hSmooth t x f hf hfc)
    (u1_signed_kernel_compact_integrable hd ω lam Λ hΛ hω hSmooth t x g hg hgc)

/-- The signed physical kernel agrees with the physical evolution for compact tests,
Lebesgue almost everywhere in the starting point. -/
theorem u1_signed_kernel_compact_integral_ae_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : EinsteinRelation.Vec d → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (fun x => ∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω lam Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
      ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hc).toLp f) x) := by
  exact u1_signed_kernel_integral_ae_volume hd ω lam Λ hΛ hω hSmooth t f
    (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hc)

/-- The actual physical kernel is additive on the Nash representation domain. -/
theorem u1_unforced_kernel_dom_add {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f g : EinsteinRelation.Vec d → ℝ) (hf : Dom f) (hg : Dom g) :
    (fun x => ∫ y, (f + g) y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => (∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) +
      ∫ y, g y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x) := by
  exact u2_unforced_physical_kernel_integral_add_ae hd ω Λ hΛ hω hSmooth t f g
    (u1_unforced_volume_memLp_physical hd ω Λ hω f hf.2)
    (u1_unforced_volume_memLp_physical hd ω Λ hω g hg.2)

/-- Scalar multiplication commutes with the actual physical kernel. -/
theorem u1_unforced_kernel_dom_smul {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (c : ℝ) (f : EinsteinRelation.Vec d → ℝ) :
    (fun x => ∫ y, (c • f) y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => c * ∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) := by
  filter_upwards with x
  exact u2_unforced_physical_kernel_integral_smul hd ω Λ hΛ hω hSmooth t f c x

/-- Compact continuous tests belong to the Lebesgue Nash domain. -/
theorem u1_compactContinuous_nash_dom {d : ℕ}
    (g : EinsteinRelation.Vec d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g) :
    Dom g := by
  exact ⟨hg.integrable_of_hasCompactSupport hc, hg.memLp_of_hasCompactSupport hc⟩

/-- The L¹ mass of a dyadic indicator is the Lebesgue volume of its cube. -/
theorem u1_dyadic_indicator_integral_abs {d : ℕ} (n : ℕ) (k : Fin d → ℤ) :
    (∫ y, |(cube n k).indicator (fun _ => (1 : ℝ)) y|) =
      (volume (cube n k)).toReal := by
  have h : (fun y => |(cube n k).indicator (fun _ => (1 : ℝ)) y|) =
      (cube n k).indicator (fun _ => (1 : ℝ)) := by
    ext y
    by_cases hy : y ∈ cube n k <;> simp [hy]
  rw [h, integral_indicator (measurableSet_cube n k)]
  simp [Measure.real]

/-- The actual unforced physical kernel has a bounded jointly measurable density
representation on compact continuous tests. -/
theorem u1_unforced_physical_nash_representation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ (M : ℝ) (P : EinsteinRelation.Vec d → EinsteinRelation.Vec d → ℝ), 0 < M ∧
      Measurable (Function.uncurry P) ∧
      (∀ x y, 0 ≤ P x y ∧ P x y ≤ M) ∧
      ∀ (g : EinsteinRelation.Vec d → ℝ), Continuous g → HasCompactSupport g →
        (fun x => ∫ y, g y ∂Blueprint.gmpPhysicalC0KernelSemigroup
          hd ω 0 Λ hΛ hω hSmooth t x) =ᵐ[volume]
        (fun x => ∫ y, P x y * g y) := by
  obtain ⟨M, hM, hbound⟩ := u8_unforced_physical_L1_to_Linfty hd ω Λ hΛ hω t ht
  let Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ := fun f x =>
    ∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x
  have hL : LinearBoundedD M Tf :=
    { add := fun f g hf hg => u1_unforced_kernel_dom_add hd ω Λ hΛ hω hSmooth t f g hf hg
      smul := fun c f _ => u1_unforced_kernel_dom_smul hd ω Λ hΛ hω hSmooth t c f
      bound := fun f hf => by
        have hb := u1_signed_physical_ae_to_volume hd ω 0
          (hbound f hf.1 (u1_unforced_volume_memLp_physical hd ω Λ hω f hf.2))
        filter_upwards [hb, u1_unforced_kernel_integral_ae_volume
          hd ω Λ hΛ hω hSmooth t f hf.2] with x hx heq
        change |Tf f x| ≤ _
        rw [show Tf f x = _ from heq]
        exact hx }
  have hcube (n : ℕ) (k : Fin d → ℤ) :
      ∀ᵐ x, 0 ≤ u1PhysicalDyadicOutput hd ω Λ hΛ hω hSmooth t n k x ∧
        u1PhysicalDyadicOutput hd ω Λ hΛ hω hSmooth t n k x ≤ M * (volume (cube n k)).toReal := by
    have hb := hL.bound _ (dom_indicator_one (measurableSet_cube n k) (volume_cube_lt_top n k))
    rw [u1_dyadic_indicator_integral_abs] at hb
    filter_upwards [hb] with x hx
    exact ⟨u1_physicalDyadicOutput_nonneg hd ω Λ hΛ hω hSmooth t n k x,
      (abs_le.mp hx).2⟩
  obtain ⟨P, hPm, hPb, hP⟩ := exists_kernel_representationD hM.le
    (T := u1PhysicalDyadicOutput hd ω Λ hΛ hω hSmooth t)
    (fun n k => (u1_physicalDyadicOutput_measurable hd ω Λ hΛ hω hSmooth t n k).aemeasurable)
    hcube
    (fun n k => Filter.Eventually.of_forall
      (u1_physicalDyadicOutput_child_add hd ω Λ hΛ hω hSmooth t n k))
    hL (fun n k => Filter.Eventually.of_forall fun _ => rfl)
  exact ⟨M, P, hM, hPm, hPb, fun g hg hc => hP g (u1_compactContinuous_nash_dom g hg hc)⟩


open EinsteinRelation.SpatialDirichlet

/-- The clock factor is uniformly bounded above and below relative to the
signed exponential force measure. -/
theorem u1_signed_physical_force_measure_comparable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    physicalReversibleMeasure ω hd lam ≤ ENNReal.ofReal (Real.exp (2 * Λ)) •
        physicalForceMeasure (firstCoordinateIndex hd) lam ∧
    physicalForceMeasure (firstCoordinateIndex hd) lam ≤
      ENNReal.ofReal (Real.exp (2 * Λ)) • physicalReversibleMeasure ω hd lam := by
  have hm : densityWeightedMeasure (sourcePhysicalDensity ω hd lam) =
      physicalReversibleMeasure ω hd lam := by
    simp [densityWeightedMeasure, sourcePhysicalDensity, sourceForceWeight,
      physicalReversibleMeasure, physicalReversibleDensity, physicalForceWeight,
      firstCoordinateIndex]
  have hr : densityWeightedMeasure (sourceReducedDensity hd lam) =
      physicalForceMeasure (firstCoordinateIndex hd) lam := by
    rfl
  constructor
  · simpa only [hm, hr] using sourcePhysicalMeasure_le_reduced ω hd lam Λ hω
  · simpa only [hm, hr] using sourceReducedMeasure_le_physical ω hd lam Λ hω

/-- The signed force-measure gradient mass is controlled by the actual
physical graph gradient mass. -/
theorem u1_signed_force_graph_gradient_comparison {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam)) :
    (∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalForceMeasure (firstCoordinateIndex hd) lam) ≤
      Real.exp (2 * Λ) *
        (∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalReversibleMeasure ω hd lam) := by
  exact integral_le_const_mul_of_measure_le
    (physicalForceMeasure (firstCoordinateIndex hd) lam)
    (physicalReversibleMeasure ω hd lam) (Real.exp (2 * Λ)) (Real.exp_pos _).le
    (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).2
    (fun x => ‖u.weakGradient x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (u.gradient_memLp.integrable_norm_pow (by norm_num : 2 ≠ 0))

/-- The actual signed physical weak graph has the same representatives in
the exponential force measure. -/
def u1SignedPhysicalGraphToForce {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam)) :
    WeightedSobolevGraph (physicalForceMeasure (firstCoordinateIndex hd) lam) where
  value := u.value
  weakGradient := u.weakGradient
  value_memLp := u.value_memLp.of_measure_le_smul ENNReal.ofReal_ne_top
    (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).2
  gradient_memLp := u.gradient_memLp.of_measure_le_smul ENNReal.ofReal_ne_top
    (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).2
  distributionalGradient := u.distributionalGradient

/-- The real force graph embeds in the complex force graph used by the gauge
transport, with the original value and gradient representatives. -/
theorem u1_force_graph_complex {d : ℕ} (i : Fin d) (lam : ℝ)
    (u : WeightedSobolevGraph (physicalForceMeasure i lam)) :
    ∃ (f : Lp ℂ 2 (physicalForceMeasure i lam))
      (G : Fin d → Lp ℂ 2 (physicalForceMeasure i lam)),
      IsPhysicalH1Graph (physicalForceMeasure i lam)
        (Or.inr ⟨i, lam, rfl⟩) f G ∧
      (f : EinsteinRelation.Vec d → ℂ) =ᵐ[physicalForceMeasure i lam]
        (fun x => (u.value x : ℂ)) ∧
      ∀ j, (G j : EinsteinRelation.Vec d → ℂ) =ᵐ[physicalForceMeasure i lam]
        (fun x => (u.weakGradient x j : ℂ)) := by
  have hf : MemLp (fun x => (u.value x : ℂ)) 2
      (physicalForceMeasure i lam) :=
    Complex.ofRealCLM.comp_memLp' u.value_memLp
  have hG (j : Fin d) : MemLp (fun x => (u.weakGradient x j : ℂ)) 2
      (physicalForceMeasure i lam) :=
    Complex.ofRealCLM.comp_memLp' (Blueprint.gmpEuclideanMemLp_coordinate u.gradient_memLp j)
  let f := hf.toLp _
  let G (j : Fin d) := (hG j).toLp _
  refine ⟨f, G, ?_, hf.coeFn_toLp, fun j => (hG j).coeFn_toLp⟩
  rw [isPhysicalH1Graph_iff_representatives _ (Or.inr ⟨i, lam, rfl⟩)
    f G _ _ hf.coeFn_toLp (fun j => (hG j).coeFn_toLp)]
  constructor
  · intro j
    simpa only [Complex.ofReal_re] using u.distributionalGradient j
  · intro j
    simp only [Complex.ofReal_im]
    have hz : coordinateDerivative j (fun _ : EinsteinRelation.Vec d => (0 : ℝ)) = (fun _ => 0) := by
      funext x
      simp [EinsteinRelation.coordinateDerivative]
    simpa only [hz] using
      hasWeakPartialDerivative_of_contDiff j (fun _ : EinsteinRelation.Vec d => (0 : ℝ)) contDiff_const

/-- The exponential gauge transports the actual signed physical weak graph
to the spatial complex H1 graph, with explicit gradient representatives. -/
theorem u1_signed_physical_graph_gauge_forward {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam)) :
    ∃ (f : Lp ℂ 2 (physicalForceMeasure (firstCoordinateIndex hd) lam))
      (G : Fin d → Lp ℂ 2 (physicalForceMeasure (firstCoordinateIndex hd) lam))
      (H : Fin d → Lp ℂ 2 (volume : Measure (EinsteinRelation.Vec d))),
      (f : EinsteinRelation.Vec d → ℂ) =ᵐ[physicalForceMeasure (firstCoordinateIndex hd) lam]
        (fun x => (u.value x : ℂ)) ∧
      (∀ j, (G j : EinsteinRelation.Vec d → ℂ) =ᵐ[physicalForceMeasure (firstCoordinateIndex hd) lam]
        (fun x => (u.weakGradient x j : ℂ))) ∧
      IsPhysicalH1Graph volume (Or.inl rfl)
        (physicalGaugeUnitary (firstCoordinateIndex hd) lam f) H ∧
      ∀ j, (H j : EinsteinRelation.Vec d → ℂ) =ᵐ[volume] fun x =>
        (Real.exp (lam * x (firstCoordinateIndex hd)) : ℂ) *
          (G j x + (lam : ℂ) * (unitVector (firstCoordinateIndex hd) j : ℂ) * f x) := by
  obtain ⟨f, G, hG, hf, hg⟩ := u1_force_graph_complex (firstCoordinateIndex hd) lam
    (u1SignedPhysicalGraphToForce hd ω lam Λ hω u)
  obtain ⟨H, hH, hrep⟩ := physicalH1Graph_gauge_forward (firstCoordinateIndex hd) lam f G hG
  exact ⟨f, G, H, hf, hg, hH, hrep⟩

/-- The signed gauge adds at most a quadratic force term to the Euclidean
gradient energy. -/
theorem u1_signed_gauge_gradient_sq_le {d : ℕ} (i : Fin d)
    (lam a : ℝ) (v : EinsteinRelation.Vec d) :
    euclideanSq (fun j => v j + lam * unitVector i j * a) ≤
      2 * euclideanSq v + 2 * lam ^ 2 * a ^ 2 := by
  have hsum : (∑ j : Fin d, (lam * unitVector i j * a) ^ 2) =
      lam ^ 2 * a ^ 2 := by
    simp [unitVector, Pi.single_apply]
    ring
  unfold euclideanSq dot
  calc
    (∑ j, (v j + lam * unitVector i j * a) *
        (v j + lam * unitVector i j * a)) ≤
        ∑ j, (2 * (v j * v j) + 2 * (lam * unitVector i j * a) ^ 2) := by
          apply Finset.sum_le_sum
          intro j _
          nlinarith [sq_nonneg (v j - lam * unitVector i j * a)]
    _ = 2 * (∑ j, v j * v j) + 2 * lam ^ 2 * a ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
      ring

/-- Ellipticity controls the physical graph gradient with the actual half-energy. -/
theorem u1_signed_physical_graph_energy_lower {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam)) :
    ((1 / 2 : ℝ) * Λ⁻¹) *
        (∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalReversibleMeasure ω hd lam) ≤
      ∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd lam := by
  have hi := u.gradient_memLp.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hf := physicalWeightedFormIntegrand_integrable_of_regular ω Λ hΛ hω u u
  have hp : ∀ x, ((1 / 2 : ℝ) * Λ⁻¹) * ‖u.weakGradient x‖ ^ 2 ≤
      weightedFormIntegrand ω.1 u u x := by
    intro x
    have he := (hω.1 x).2 (WithLp.ofLp (u.weakGradient x))
    have hn : euclideanSq (WithLp.ofLp (u.weakGradient x)) = ‖u.weakGradient x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]
    unfold weightedFormIntegrand
    calc
      ((1 / 2 : ℝ) * Λ⁻¹) * ‖u.weakGradient x‖ ^ 2 =
          (1 / 2 : ℝ) * (Λ⁻¹ * euclideanSq (WithLp.ofLp (u.weakGradient x))) := by
        rw [hn]
        ring
      _ ≤ (1 / 2 : ℝ) * dot (WithLp.ofLp (u.weakGradient x))
          ((ω.1 x).mulVec (WithLp.ofLp (u.weakGradient x))) :=
        mul_le_mul_of_nonneg_left he.1 (by norm_num)
  have hm := integral_mono_ae (hi.const_mul ((1 / 2 : ℝ) * Λ⁻¹)) hf
    (Filter.Eventually.of_forall hp)
  rw [integral_const_mul] at hm
  exact hm

/-- Pointwise gauge-gradient control by the actual elliptic half-energy and
the force contribution, before integrating against the force measure. -/
theorem u1_signed_physical_gauge_gradient_energy {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (x : EinsteinRelation.Vec d) :
    euclideanSq (fun j => u.weakGradient x j +
      lam * unitVector (firstCoordinateIndex hd) j * u.value x) ≤
      4 * Λ * weightedFormIntegrand ω.1 u u x + 2 * lam ^ 2 * u.value x ^ 2 := by
  have hΛp : 0 < Λ := by linarith
  have he := ((hω.1 x).2 (WithLp.ofLp (u.weakGradient x))).1
  have hb : euclideanSq (WithLp.ofLp (u.weakGradient x)) ≤
      2 * Λ * weightedFormIntegrand ω.1 u u x := by
    unfold weightedFormIntegrand
    have h := mul_le_mul_of_nonneg_left he hΛp.le
    have hi : Λ * Λ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hΛp)
    rw [← mul_assoc, hi, one_mul] at h
    nlinarith
  have hg := u1_signed_gauge_gradient_sq_le (firstCoordinateIndex hd)
    lam (u.value x) (WithLp.ofLp (u.weakGradient x))
  exact hg.trans (by nlinarith)

/-- The pointwise gauge estimate integrates against the signed force measure. -/
theorem u1_signed_physical_gauge_gradient_energy_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam)) :
    (∫ x, euclideanSq (fun j => u.weakGradient x j +
      lam * unitVector (firstCoordinateIndex hd) j * u.value x)
      ∂physicalForceMeasure (firstCoordinateIndex hd) lam) ≤
    Real.exp (2 * Λ) * (4 * Λ *
      (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd lam) +
      2 * lam ^ 2 * (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd lam)) := by
  let μ := physicalReversibleMeasure ω hd lam
  let ν := physicalForceMeasure (firstCoordinateIndex hd) lam
  let K := Real.exp (2 * Λ)
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hνμ : ν ≤ ENNReal.ofReal K • μ :=
    (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).2
  have hval : MemLp u.value 2 ν :=
    u.value_memLp.of_measure_le_smul ENNReal.ofReal_ne_top hνμ
  have hgrad : MemLp u.weakGradient 2 ν :=
    u.gradient_memLp.of_measure_le_smul ENNReal.ofReal_ne_top hνμ
  have hsqμ : Integrable (fun x => u.value x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      u.value_memLp.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hsqν : Integrable (fun x => u.value x ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      hval.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hformμ : Integrable (fun x => weightedFormIntegrand ω.1 u u x) μ :=
    physicalWeightedFormIntegrand_integrable_of_regular ω Λ hΛ hω u u
  have hformν : Integrable (fun x => weightedFormIntegrand ω.1 u u x) ν :=
    memLp_one_iff_integrable.mp <| (memLp_one_iff_integrable.mpr hformμ).of_measure_le_smul
      ENNReal.ofReal_ne_top hνμ
  have hleft : Integrable (fun x => euclideanSq (fun j => u.weakGradient x j +
      lam * unitVector (firstCoordinateIndex hd) j * u.value x)) ν := by
    unfold euclideanSq dot
    apply integrable_finsetSum
    intro j _
    have hj := (Blueprint.gmpEuclideanMemLp_coordinate hgrad j).add
      (hval.const_mul (lam * unitVector (firstCoordinateIndex hd) j))
    simpa only [Pi.add_apply, Real.norm_eq_abs, ← pow_two, sq_abs] using
      hj.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hn : ∀ x, 0 ≤ weightedFormIntegrand ω.1 u u x := by
    intro x
    unfold weightedFormIntegrand
    have he := ((hω.1 x).2 (WithLp.ofLp (u.weakGradient x))).1
    have hs : 0 ≤ euclideanSq (WithLp.ofLp (u.weakGradient x)) := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    exact mul_nonneg (by norm_num) ((mul_nonneg (by positivity) hs).trans he)
  have hE := integral_le_const_mul_of_measure_le ν μ K hK hνμ
    (fun x => weightedFormIntegrand ω.1 u u x) (Filter.Eventually.of_forall hn) hformμ
  have hV := integral_le_const_mul_of_measure_le ν μ K hK hνμ
    (fun x => u.value x ^ 2) (Filter.Eventually.of_forall fun x => sq_nonneg _) hsqμ
  have hmain := integral_mono_ae hleft
    ((hformν.const_mul (4 * Λ)).add (hsqν.const_mul (2 * lam ^ 2)))
    (Filter.Eventually.of_forall (u1_signed_physical_gauge_gradient_energy hd ω lam Λ hΛ hω u))
  change (∫ x, euclideanSq (fun j => u.weakGradient x j +
    lam * unitVector (firstCoordinateIndex hd) j * u.value x) ∂ν) ≤
    ∫ x, (4 * Λ * weightedFormIntegrand ω.1 u u x + 2 * lam ^ 2 * u.value x ^ 2) ∂ν at hmain
  rw [integral_add (hformν.const_mul (4 * Λ)) (hsqν.const_mul (2 * lam ^ 2)),
    integral_const_mul, integral_const_mul] at hmain
  have hΛ0 : 0 ≤ Λ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hE (show 0 ≤ 4 * Λ by positivity),
    mul_le_mul_of_nonneg_left hV (show 0 ≤ 2 * lam ^ 2 by positivity)]

/-- The force-measure gradient integral is exactly the Lebesgue energy of
the exponentially gauged gradient. -/
theorem u1_signed_gauge_gradient_integral_identity {d : ℕ} (i : Fin d)
    (lam : ℝ) (v : EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (a : EinsteinRelation.Vec d → ℝ) :
    (∫ x, euclideanSq (fun j => Real.exp (lam * x i) *
      (v x j + lam * unitVector i j * a x))) =
    ∫ x, euclideanSq (fun j => v x j + lam * unitVector i j * a x)
      ∂physicalForceMeasure i lam := by
  unfold physicalForceMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x : EinsteinRelation.Vec d =>
      ENNReal.ofReal (Real.exp (2 * lam * x i))) from
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_apply i)))).measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  unfold euclideanSq dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : Real.exp (2 * lam * x i) = Real.exp (lam * x i) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  ring

/-- The actual signed graph supplies a Lebesgue H¹ function with the gauge
value and gradient as its almost-everywhere representatives. -/
theorem u1_signed_physical_graph_gauge_spatial_h1 {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam)) :
    ∃ h : PDE.H1Function (Set.univ : Set (EinsteinRelation.Vec d)),
      (fun x => h x) =ᵐ[volume] (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) ∧
      ∀ j, (fun x => h.grad x j) =ᵐ[volume] (fun x =>
        Real.exp (lam * x (firstCoordinateIndex hd)) *
          (u.weakGradient x j + lam * unitVector (firstCoordinateIndex hd) j * u.value x)) := by
  let i := firstCoordinateIndex hd
  obtain ⟨f, G, H, hf, hG, hH, hrep⟩ :=
    u1_signed_physical_graph_gauge_forward hd ω lam Λ hω u
  let F := physicalGaugeUnitary i lam f
  have hfre : MemLp (fun x => (F x).re) 2 volume := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp F)
  have hGre (j : Fin d) : MemLp (fun x => (H j x).re) 2 volume := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp (H j))
  let h : PDE.H1Function (Set.univ : Set (EinsteinRelation.Vec d)) :=
    { toFun := fun x => (F x).re
      grad := fun x j => (H j x).re
      memL2 := by simpa only [PDE.MemL2On, PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hfre
      gradMemL2 := fun j => by
        simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hGre j
      hasWeakGradient := Blueprint.gmpHasWeakGradient_toPDE hH.1 }
  refine ⟨h, ?_, ?_⟩
  · filter_upwards [physicalGaugeUnitary_coe i lam f,
      (volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq hf] with x hx hfx
    change (F x).re = _
    rw [hx]
    simp only [physicalGaugeMultiplier]
    rw [hfx]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  · intro j
    filter_upwards [hrep j, (volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq hf,
      (volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq (hG j)] with x hx hfx hgx
    change (H j x).re = _
    rw [hx, hfx, hgx]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero]

/-- Spatial H¹ realization with a quantitative gradient bound for the actual
signed physical graph. -/
theorem u1_signed_physical_gauge_spatial_energy {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam)) :
    ∃ h : PDE.H1Function (Set.univ : Set (EinsteinRelation.Vec d)),
      (fun x => h x) =ᵐ[volume] (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) ∧
      (∫ x, euclideanSq (h.grad x)) ≤
        Real.exp (2 * Λ) * (4 * Λ *
          (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd lam) +
          2 * lam ^ 2 * (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd lam)) := by
  obtain ⟨h, hv, hg⟩ := u1_signed_physical_graph_gauge_spatial_h1 hd ω lam Λ hω u
  refine ⟨h, hv, ?_⟩
  have heq : (∫ x, euclideanSq (h.grad x)) =
      ∫ x, euclideanSq (fun j => Real.exp (lam * x (firstCoordinateIndex hd)) *
        (u.weakGradient x j + lam * unitVector (firstCoordinateIndex hd) j * u.value x)) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hg] with x hx
    congr 1
    funext j
    exact hx j
  rw [heq, u1_signed_gauge_gradient_integral_identity]
  exact u1_signed_physical_gauge_gradient_energy_integral hd ω lam Λ hΛ hω u

/-- Nash's inequality for the gauge of the signed physical graph, with the
physical energy and the signed-force mass correction. -/
theorem u1_signed_physical_gauge_nash {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) volume →
      (∫ x, (Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) ^ 2) ≤
        C * (Real.exp (2 * Λ) * (4 * Λ *
          (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd lam) +
          2 * lam ^ 2 * (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd lam))) ^
            ((d : ℝ) / (d + 2)) *
        (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x|) ^
          ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := PDE.exists_nash_constant d (by omega)
  refine ⟨C, hC, ?_⟩
  intro u hu
  obtain ⟨h, hv, he⟩ := u1_signed_physical_gauge_spatial_energy hd ω lam Λ hΛ hω u
  have hh : Integrable h volume := hu.congr hv.symm
  have hn := hN h hh
  have hsq : (∫ x, h x ^ 2) =
      ∫ x, (Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  have habs : (∫ x, |h x|) =
      ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x| := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  have hgrad : (∫ x, PDE.vecEuclideanNorm (h.grad x) ^ 2) =
      ∫ x, euclideanSq (h.grad x) := by
    apply integral_congr_ae
    filter_upwards with x
    change euclideanNorm (h.grad x) ^ 2 = euclideanSq (h.grad x)
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  rw [hsq, habs, hgrad] at hn
  have hgrad0 : 0 ≤ ∫ x, euclideanSq (h.grad x) := by
    apply integral_nonneg
    intro x
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have ha : 0 ≤ (d : ℝ) / (d + 2) := by positivity
  exact hn.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hgrad0 he ha) hC.le)
    (Real.rpow_nonneg (integral_nonneg fun x => abs_nonneg _) _))

/-- The squared Lebesgue norm of the exponential gauge is exactly the
force-measure squared norm. -/
theorem u1_signed_gauge_mass_integral_identity {d : ℕ} (i : Fin d)
    (lam : ℝ) (f : EinsteinRelation.Vec d → ℝ) :
    (∫ x, (Real.exp (lam * x i) * f x) ^ 2) =
      ∫ x, f x ^ 2 ∂physicalForceMeasure i lam := by
  unfold physicalForceMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x : EinsteinRelation.Vec d =>
      ENNReal.ofReal (Real.exp (2 * lam * x i))) from
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_apply i)))).measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  have he : Real.exp (2 * lam * x i) = Real.exp (lam * x i) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  ring

/-- The physical squared mass and the gauged Lebesgue squared mass are
uniformly comparable, including for arbitrary signed force. -/
theorem u1_signed_physical_gauge_mass_comparable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam)) :
    (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd lam) ≤
      Real.exp (2 * Λ) * (∫ x, (Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) ^ 2) ∧
    (∫ x, (Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) ^ 2) ≤
      Real.exp (2 * Λ) * (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd lam) := by
  let μ := physicalReversibleMeasure ω hd lam
  let ν := physicalForceMeasure (firstCoordinateIndex hd) lam
  have hcomp := u1_signed_physical_force_measure_comparable hd ω lam Λ hω
  have hμ : Integrable (fun x => u.value x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      u.value_memLp.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hν : Integrable (fun x => u.value x ^ 2) ν := by
    have hv : MemLp u.value 2 ν :=
      u.value_memLp.of_measure_le_smul ENNReal.ofReal_ne_top hcomp.2
    simpa only [Real.norm_eq_abs, sq_abs] using
      hv.integrable_norm_pow (by norm_num : 2 ≠ 0)
  rw [u1_signed_gauge_mass_integral_identity]
  exact ⟨integral_le_const_mul_of_measure_le μ ν (Real.exp (2 * Λ))
      (Real.exp_pos _).le hcomp.1 (fun x => u.value x ^ 2)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hν,
    integral_le_const_mul_of_measure_le ν μ (Real.exp (2 * Λ))
      (Real.exp_pos _).le hcomp.2 (fun x => u.value x ^ 2)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hμ⟩

/-- Nash controls the actual physical squared mass by the physical energy and
mass correction, with the Lebesgue L¹ norm of the gauge. -/
theorem u1_signed_physical_mass_gauge_nash {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) volume →
      (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd lam) ≤
        C * (Real.exp (2 * Λ) * (4 * Λ *
          (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd lam) +
          2 * lam ^ 2 * (∫ x, u.value x ^ 2 ∂physicalReversibleMeasure ω hd lam))) ^
            ((d : ℝ) / (d + 2)) *
        (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x|) ^
          ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := u1_signed_physical_gauge_nash hd ω lam Λ hΛ hω
  refine ⟨Real.exp (2 * Λ) * C, mul_pos (Real.exp_pos _) hC, ?_⟩
  intro u hu
  have hm := (u1_signed_physical_gauge_mass_comparable hd ω lam Λ hω u).1
  have hn := hN u hu
  calc
    _ ≤ Real.exp (2 * Λ) * (∫ x, (Real.exp (lam * x (firstCoordinateIndex hd)) * u.value x) ^ 2) := hm
    _ ≤ Real.exp (2 * Λ) * (C * _ * _) :=
      mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
    _ = _ := by ring

/-- The signed gauge Nash estimate on the actual physical closed-form domain. -/
theorem u1_signed_physical_closedForm_gauge_nash {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      physicalH1Member ω hd lam f →
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
      (∫ x, f x ^ 2 ∂physicalReversibleMeasure ω hd lam) ≤
        C * (Real.exp (2 * Λ) * (4 * Λ *
          (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form f f +
          2 * lam ^ 2 * (∫ x, f x ^ 2 ∂physicalReversibleMeasure ω hd lam))) ^
            ((d : ℝ) / (d + 2)) *
        (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|) ^
          ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := u1_signed_physical_mass_gauge_nash hd ω lam Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro f hf hi
  obtain ⟨v, rfl⟩ := (Blueprint.gmpPhysicalH1Value_range_iff hd ω lam Λ hω f).mpr hf
  let g : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam) :=
    sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) v
  have hv : g.value =ᵐ[physicalReversibleMeasure ω hd lam]
      (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v : EinsteinRelation.Vec d → ℝ) :=
    g.value_memLp.coeFn_toLp.symm
  have hvVol := u1_signed_physical_ae_to_volume hd ω lam hv
  have hvg : (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * g.value x) =ᵐ[volume]
      (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
        (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v) x) :=
    hvVol.mono fun x hx => by
      simpa only using congrArg (fun z : ℝ => Real.exp (lam * x (firstCoordinateIndex hd)) * z) hx
  have hn := hN g (hi.congr hvg.symm)
  have hm : (∫ x, g.value x ^ 2 ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v) x ^ 2
        ∂physicalReversibleMeasure ω hd lam := by
    exact integral_congr_ae (hv.mono fun x hx => by simpa only using congrArg (fun z : ℝ => z ^ 2) hx)
  have hL : (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * g.value x|) =
      ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
        (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v) x| := by
    exact integral_congr_ae (hvg.mono fun x hx => by simpa only using congrArg (fun z : ℝ => |z|) hx)
  have he : (∫ x, weightedFormIntegrand ω.1 g g x ∂physicalReversibleMeasure ω hd lam) =
      (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
        (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v)
        (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v) := by
    rw [Blueprint.gmpPhysicalClosedForm_value]
    rfl
  simpa only [hm, hL, he] using hn

/-- Coordinate exponentials are uniform supersolutions for the actual signed
physical generator, with a constant independent of the spatial point. -/
theorem u1_signed_physical_generator_coordinate_exp_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x,
      physicalGenerator (firstCoordinateIndex hd) ω lam
          (fun y => Real.exp (q * y i)) x ≤ Real.exp (q * x i) * K := by
  obtain ⟨_, _, ⟨Ma, hMa⟩, _, _, ⟨Mb, hMb⟩⟩ :=
    physical_svHypotheses (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam
  let K : ℝ := max 1 (|q| * Mb + q ^ 2 / 2 * Ma)
  refine ⟨K, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x
  rw [physicalGenerator_eq_svGenerator hSmooth _ lam
    ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp)]
  exact (c16_svGenerator_coordinate_exp_le _ _ i q x (hMa x i i) (hMb x i)).trans
    (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_nonneg _))

/-- The corresponding absolute generator bound supports stopped-test
integrability for coordinate exponentials. -/
theorem u1_signed_physical_generator_coordinate_exp_abs_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x,
      |physicalGenerator (firstCoordinateIndex hd) ω lam
          (fun y => Real.exp (q * y i)) x| ≤ Real.exp (q * x i) * K := by
  obtain ⟨_, _, ⟨Ma, hMa⟩, _, _, ⟨Mb, hMb⟩⟩ :=
    physical_svHypotheses (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam
  let K : ℝ := max 1 (|q| * Mb + q ^ 2 / 2 * Ma)
  refine ⟨K, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x
  rw [physicalGenerator_eq_svGenerator hSmooth _ lam
    ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp)]
  exact (c16_svGenerator_coordinate_exp_abs_le _ _ i q x (hMa x i i) (hMb x i)).trans
    (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_nonneg _))

/-- The absolute generator of a coordinate exponential is bounded before
exit from a fixed Euclidean ball. -/
theorem u1_signed_physical_generator_coordinate_exp_before_exit_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : Path d), euclideanNorm (γ 0) < R →
      ∀ t u : ℝ≥0, u ≤ MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : EinsteinRelation.Vec d | euclideanNorm y < R} t γ →
      |physicalGenerator (firstCoordinateIndex hd) ω lam
        (fun y => Real.exp (q * y i)) (γ u)| ≤ C := by
  obtain ⟨K, hK, hgen⟩ :=
    u1_signed_physical_generator_coordinate_exp_abs_le hd ω lam Λ hΛ hω hSmooth i q
  refine ⟨Real.exp (|q| * R) * K, mul_nonneg (Real.exp_nonneg _) hK.le, ?_⟩
  intro γ h0 t u hu
  exact (hgen (γ u)).trans (mul_le_mul_of_nonneg_right
    (c16_exp_coordinate_before_ball_exit R q γ i h0 t u hu) hK.le)

/-- The stopped compensated exponential is centered under any solution of
the actual signed physical martingale problem. -/
theorem u1_signed_physical_exp_ball_stopped_centered
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ)
    (hSmooth : IsSmoothFieldPair ω) (i : Fin d)
    {x : EinsteinRelation.Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P)
    (q R : ℝ) (hR : 0 < R) (t : ℝ≥0) :
    let M := fun γ : Path d => EinsteinRelation.compensatedTest
      (physicalGenerator (firstCoordinateIndex hd) ω lam) (fun y => Real.exp (q * y i))
      (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : EinsteinRelation.Vec d | euclideanNorm y < R} t γ) γ
    Integrable M P ∧ ∫ γ, M γ ∂P = 0 := by
  letI : IsProbabilityMeasure P := hP.1
  have hm := Blueprint.physical_mp_c2_ball_stopped_rightCont_martingale
    (firstCoordinateIndex hd) ω hSmooth lam x P hP
    (fun y => Real.exp (q * y i)) ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp) R hR
  refine ⟨hm.integrable t, ?_⟩
  have h := hm.setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le) MeasurableSet.univ
  have hz (γ : Path d) : MarkovProcess.ContinuousPath.exitTimeTrunc
      {y : EinsteinRelation.Vec d | euclideanNorm y < R} 0 γ = 0 :=
    le_antisymm (MarkovProcess.ContinuousPath.exitTimeTrunc_le _ _ _) bot_le
  simpa [hz, EinsteinRelation.compensatedTest] using h.symm

/-- The stopped physical exponential moment equals its initial value plus
the expected integrated physical generator. -/
theorem u1_signed_physical_exp_stopped_moment_identity
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ)
    (hSmooth : IsSmoothFieldPair ω) (i : Fin d)
    {x : EinsteinRelation.Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P)
    (q R : ℝ) (hR : euclideanNorm x < R) (t : ℝ≥0) :
    let U := {y : EinsteinRelation.Vec d | euclideanNorm y < R}
    let F := fun γ : Path d => Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ)) i)
    let J := fun γ : Path d => ∫ u in (0 : ℝ)..
      (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
      physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => Real.exp (q * y i))
        (γ u.toNNReal)
    Integrable J P ∧ (∫ γ, F γ ∂P) = Real.exp (q * x i) + ∫ γ, J γ ∂P := by
  letI : IsProbabilityMeasure P := hP.1
  let U := {y : EinsteinRelation.Vec d | euclideanNorm y < R}
  let F := fun γ : Path d => Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ)) i)
  let J := fun γ : Path d => ∫ u in (0 : ℝ)..
    (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
    physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => Real.exp (q * y i))
      (γ u.toNNReal)
  let M := fun γ : Path d => EinsteinRelation.compensatedTest
    (physicalGenerator (firstCoordinateIndex hd) ω lam) (fun y => Real.exp (q * y i))
    (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ) γ
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hF : Integrable F P := by
    have hFm : AEStronglyMeasurable F P := by
      simpa only [F, Function.comp_def, id_eq] using
        ((c16_measurable_stopped_coordinate_exp U hU i q).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    apply Integrable.of_bound hFm (Real.exp (|q| * R))
    filter_upwards [hP.2.1] with γ hγ
    have h0 : euclideanNorm (γ 0) < R := by rw [hγ]; exact hR
    have hb := c16_exp_coordinate_before_ball_exit R q γ i h0 t
      (MarkovProcess.ContinuousPath.exitTimeTrunc U t γ) le_rfl
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb
  have hRpos : 0 < R := (Real.sqrt_nonneg _).trans_lt hR
  have hM := u1_signed_physical_exp_ball_stopped_centered hd ω lam hSmooth i hP q R hRpos t
  change Integrable M P ∧ (∫ γ, M γ ∂P) = 0 at hM
  have heq : J =ᵐ[P] fun γ => (F γ - Real.exp (q * x i)) - M γ := by
    filter_upwards [hP.2.1] with γ hγ
    simp only [J, F, M, EinsteinRelation.compensatedTest, hγ]
    ring
  have hJ : Integrable J P := ((hF.sub (integrable_const _)).sub hM.1).congr heq.symm
  refine ⟨hJ, ?_⟩
  have hJi : (∫ γ, J γ ∂P) = (∫ γ, F γ ∂P) - Real.exp (q * x i) := by
    calc
      _ = ∫ γ, (F γ - Real.exp (q * x i)) - M γ ∂P := integral_congr_ae heq
      _ = (∫ γ, F γ ∂P) - Real.exp (q * x i) := by
        have hsub := integral_sub (hF.sub (integrable_const (Real.exp (q * x i)))) hM.1
        simp only [Pi.sub_apply] at hsub
        rw [hsub, integral_sub hF (integrable_const _), hM.2]
        simp
  linarith

/-- Along each path, the stopped physical generator integral is dominated by
the time integral of the stopped exponential. -/
theorem u1_signed_physical_exp_stopped_generator_path_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (EinsteinRelation.Vec d)) (t : ℝ≥0) (γ : Path d),
      (∫ u in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
        physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => Real.exp (q * y i))
          (γ u.toNNReal)) ≤ C * ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (q *
        (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U u.toNNReal γ)) i) := by
  obtain ⟨C, hC, hbound⟩ :=
    u1_signed_physical_generator_coordinate_exp_le hd ω lam Λ hΛ hω hSmooth i q
  refine ⟨C, hC.le, ?_⟩
  intro U t γ
  let r := MarkovProcess.ContinuousPath.exitTimeTrunc U t γ
  let f : ℝ → ℝ := fun u => physicalGenerator (firstCoordinateIndex hd) ω lam
    (fun y => Real.exp (q * y i)) (γ u.toNNReal)
  let g : ℝ → ℝ := fun u => Real.exp (q * (γ u.toNNReal) i)
  have hg : Continuous g := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_apply i).comp (γ.continuous.comp continuous_real_toNNReal)))
  have hc : Continuous (physicalGenerator (firstCoordinateIndex hd) ω lam
      (fun y => Real.exp (q * y i))) := by
    rw [funext (physicalGenerator_eq_svGenerator hSmooth _ lam
      ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp))]
    apply continuous_svGenerator _ _ (fun j k => (hSmooth.1 j k).continuous) _
      ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp)
    intro j
    exact ((reduce ω).2.continuous.inv₀ (fun y => (clockDensity_pos ω y).ne')).mul
      (continuous_forcedDrift_apply hSmooth (firstCoordinateIndex hd) lam j)
  have hfi : IntervalIntegrable f volume 0 (r : ℝ) := by
    exact (hc.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hr : (r : ℝ) ≤ t := NNReal.coe_le_coe.mpr
    (MarkovProcess.ContinuousPath.exitTimeTrunc_le U t γ)
  have hbound' := c16_integral_generator_le_stopped f g hg (fun u => Real.exp_nonneg _)
    hC.le r.coe_nonneg hr hfi (fun u _ => by simpa only [f, g, mul_comm] using hbound (γ u.toNNReal))
  refine hbound'.trans_eq ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le t.coe_nonneg] at hu
  have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
  have he := c16_exitTimeTrunc_min U γ u.toNNReal t
  rw [min_eq_left hut] at he
  have he' : ((MarkovProcess.ContinuousPath.exitTimeTrunc U u.toNNReal γ : ℝ≥0) : ℝ) =
      min u (r : ℝ) := by
    rw [he, NNReal.coe_min, Real.coe_toNNReal u hu.1]
  simp only [g, ← he', Real.toNNReal_coe]

theorem u1_general_continuous_stopped_exp_moment {d : ℕ}
    (L : (EinsteinRelation.Vec d → ℝ) → EinsteinRelation.Vec d → ℝ) (i : Fin d) {x : EinsteinRelation.Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P)
    (q R : ℝ) (hR : euclideanNorm x < R) :
    Continuous (fun s : ℝ => ∫ γ : Path d, Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : EinsteinRelation.Vec d | euclideanNorm y < R} s.toNNReal γ)) i) ∂P) := by
  letI : IsProbabilityMeasure P := hP.1
  let U := {y : EinsteinRelation.Vec d | euclideanNorm y < R}
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  apply continuous_of_dominated (bound := fun _ : Path d => Real.exp (|q| * R))
  · intro s
    exact ((c16_measurable_stopped_coordinate_exp U hU i q).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · intro s
    filter_upwards [hP.2.1] with γ hγ
    have h0 : euclideanNorm (γ 0) < R := by rw [hγ]; exact hR
    have hb := c16_exp_coordinate_before_ball_exit R q γ i h0 s.toNNReal
      (MarkovProcess.ContinuousPath.exitTimeTrunc U s.toNNReal γ) le_rfl
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb
  · exact integrable_const _
  · exact ae_of_all _ fun γ =>
      (c16_continuous_stopped_coordinate_exp U γ i q).comp continuous_real_toNNReal


theorem u1_general_stopped_exp_moment_integral_swap {d : ℕ}
    (L : (EinsteinRelation.Vec d → ℝ) → EinsteinRelation.Vec d → ℝ) (i : Fin d) {x : EinsteinRelation.Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P)
    (q R : ℝ) (hR : euclideanNorm x < R) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), ∫ γ : Path d, Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : EinsteinRelation.Vec d | euclideanNorm y < R} s.toNNReal γ)) i) ∂P) =
    ∫ γ : Path d, (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : EinsteinRelation.Vec d | euclideanNorm y < R} s.toNNReal γ)) i)) ∂P := by
  letI : IsProbabilityMeasure P := hP.1
  let U := {y : EinsteinRelation.Vec d | euclideanNorm y < R}
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  let F : ℝ × Path d → ℝ := fun p => Real.exp (q *
    (p.2 (MarkovProcess.ContinuousPath.exitTimeTrunc U p.1.toNNReal p.2)) i)
  have hF : Measurable F := (c16_measurable_stopped_coordinate_exp U hU i q).comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) (t : ℝ))) := by
    rw [Set.uIoc_of_le t.coe_nonneg]
    infer_instance
  apply intervalIntegral_integral_swap
  apply Integrable.of_bound hF.aestronglyMeasurable (Real.exp (|q| * R))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hF.norm measurable_const)).mpr
  filter_upwards [] with s
  filter_upwards [hP.2.1] with γ hγ
  have h0 : euclideanNorm (γ 0) < R := by rw [hγ]; exact hR
  have hb := c16_exp_coordinate_before_ball_exit R q γ i h0 s.toNNReal
    (MarkovProcess.ContinuousPath.exitTimeTrunc U s.toNNReal γ) le_rfl
  simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb


theorem u1_general_integrable_stopped_exp_time_integral {d : ℕ}
    (L : (EinsteinRelation.Vec d → ℝ) → EinsteinRelation.Vec d → ℝ) (i : Fin d) {x : EinsteinRelation.Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P)
    (q R : ℝ) (hR : euclideanNorm x < R) (t : ℝ≥0) :
    Integrable (fun γ : Path d => ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (q *
      (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : EinsteinRelation.Vec d | euclideanNorm y < R} s.toNNReal γ)) i)) P := by
  let : IsProbabilityMeasure P := hP.1
  let U := {y : EinsteinRelation.Vec d | euclideanNorm y < R}
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  let F : ℝ × Path d → ℝ := fun p => Real.exp (q *
    (p.2 (MarkovProcess.ContinuousPath.exitTimeTrunc U p.1.toNNReal p.2)) i)
  have hF : Measurable F := (c16_measurable_stopped_coordinate_exp U hU i q).comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  letI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by infer_instance
  have hi : Integrable F ((volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))).prod P) := by
    apply Integrable.of_bound hF.aestronglyMeasurable (Real.exp (|q| * R))
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hF.norm measurable_const)).mpr
    filter_upwards [] with s
    filter_upwards [hP.2.1] with γ hγ
    have h0 : euclideanNorm (γ 0) < R := by rw [hγ]; exact hR
    have hb := c16_exp_coordinate_before_ball_exit R q γ i h0 s.toNNReal
      (MarkovProcess.ContinuousPath.exitTimeTrunc U s.toNNReal γ) le_rfl
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb
  simpa only [F, intervalIntegral.integral_of_le t.coe_nonneg] using hi.integral_prod_right


/-- Uniform in the stopping radius, the physical coordinate-exponential
moment grows at most exponentially in time. -/
theorem u1_signed_physical_exp_stopped_moment_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x : EinsteinRelation.Vec d} {P : Measure (Path d)},
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P →
      ∀ R : ℝ, euclideanNorm x < R → ∀ t : ℝ≥0,
      (∫ γ : Path d, Real.exp (q *
        (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : EinsteinRelation.Vec d | euclideanNorm y < R} t γ)) i) ∂P) ≤
        Real.exp (q * x i) * Real.exp (C * (t : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    u1_signed_physical_exp_stopped_generator_path_bound hd ω lam Λ hΛ hω hSmooth i q
  refine ⟨C, hC, ?_⟩
  intro x P hP R hR t
  let : IsProbabilityMeasure P := hP.1
  let U := {y : EinsteinRelation.Vec d | euclideanNorm y < R}
  let E : ℝ → ℝ := fun s => ∫ γ : Path d, Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U s.toNNReal γ)) i) ∂P
  have hE : Continuous E := u1_general_continuous_stopped_exp_moment _ i hP q R hR
  have hE0 : E 0 = Real.exp (q * x i) := by
    have heq : (fun γ : Path d => Real.exp (q *
        (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U (0 : ℝ≥0) γ)) i)) =ᵐ[P]
        fun _ => Real.exp (q * x i) := by
      filter_upwards [hP.2.1] with γ hγ
      have hz : MarkovProcess.ContinuousPath.exitTimeTrunc U 0 γ = 0 :=
        le_antisymm (MarkovProcess.ContinuousPath.exitTimeTrunc_le _ _ _) bot_le
      simp [hz, hγ]
    simpa [E] using integral_congr_ae heq
  have hineq : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ), E s ≤ E 0 + C * ∫ u in 0..s, E u := by
    intro s hs
    let v := s.toNNReal
    have hv : (v : ℝ) = s := Real.coe_toNNReal s hs.1
    have hid := u1_signed_physical_exp_stopped_moment_identity hd ω lam hSmooth i hP q R hR v
    have hi := u1_general_integrable_stopped_exp_time_integral _ i hP q R hR v
    have hb := integral_mono_ae hid.1 (hi.const_mul C) (ae_of_all P (hbound U v))
    have hswap := u1_general_stopped_exp_moment_integral_swap _ i hP q R hR v
    rw [integral_const_mul, ← hswap] at hb
    have hm := hid.2
    have hh := add_le_add_left hb (Real.exp (q * x i))
    simp only [add_comm] at hh
    rw [← hm] at hh
    simpa only [E, hE0, hv] using hh
  have hg := c16_integral_gronwall hE hC hineq (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  simpa only [E, hE0, Real.toNNReal_coe] using hg

/-- Exponential moments of every signed physical martingale-problem solution
are bounded uniformly in the starting point and in the solution law. -/
theorem u1_signed_physical_coordinate_exp_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x : EinsteinRelation.Vec d} {P : Measure (Path d)},
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P →
      ∀ t : ℝ≥0, Integrable (fun γ : Path d => Real.exp (q * (γ t) i)) P ∧
        (∫ γ : Path d, Real.exp (q * (γ t) i) ∂P) ≤
          Real.exp (q * x i) * Real.exp (C * (t : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    u1_signed_physical_exp_stopped_moment_le hd ω lam Λ hΛ hω hSmooth i q
  refine ⟨C, hC, ?_⟩
  intro x P hP t
  let : IsProbabilityMeasure P := hP.1
  let U : ℕ → Set (EinsteinRelation.Vec d) := fun n => {y | euclideanNorm y < (n + 1 : ℝ)}
  let F : ℕ → Path d → ℝ := fun n γ => Real.exp (q *
    (γ (MarkovProcess.ContinuousPath.exitTimeTrunc (U n) t γ)) i)
  let G : Path d → ℝ := fun γ => Real.exp (q * (γ t) i)
  let B := Real.exp (q * x i) * Real.exp (C * (t : ℝ))
  have hU (n : ℕ) : IsOpen (U n) := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hFm (n : ℕ) : Measurable (F n) := by
    simpa only [F, Function.comp_def, id_eq] using
      (c16_measurable_stopped_coordinate_exp (U n) (hU n) i q).comp
        (measurable_const.prodMk measurable_id)
  have hGm : AEStronglyMeasurable G P := by
    exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_apply i).comp (continuous_eval_const t)))).measurable.aestronglyMeasurable
  have hlim (γ : Path d) : ∀ᶠ n : ℕ in atTop, F n γ = G γ := by
    filter_upwards [Blueprint.physical_path_euclidean_ball_exit_exhaustion γ t] with n hn
    simp only [F, G, U, hn t le_rfl]
  have hlarge : ∀ᶠ n : ℕ in atTop, euclideanNorm x < (n + 1 : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (euclideanNorm x)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hFint (n : ℕ) (hn : euclideanNorm x < (n + 1 : ℝ)) : Integrable (F n) P := by
    apply Integrable.of_bound (hFm n).aestronglyMeasurable (Real.exp (|q| * (n + 1)))
    filter_upwards [hP.2.1] with γ hγ
    have h0 : euclideanNorm (γ 0) < (n + 1 : ℝ) := by rw [hγ]; exact hn
    have hh := c16_exp_coordinate_before_ball_exit (n + 1) q γ i h0 t
      (MarkovProcess.ContinuousPath.exitTimeTrunc (U n) t γ) le_rfl
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hh
  have hfatou := lintegral_liminf_le' (μ := P) (u := (atTop : Filter ℕ))
    (fun n => (hFm n).aemeasurable.ennreal_ofReal)
  have hlim' (γ : Path d) : liminf (fun n => ENNReal.ofReal (F n γ)) atTop =
      ENNReal.ofReal (G γ) := by
    rw [Filter.liminf_congr ((hlim γ).mono fun n hn => by rw [hn])]
    exact Filter.liminf_const _
  simp only [hlim'] at hfatou
  have hle : ∀ᶠ n : ℕ in atTop, (∫⁻ γ, ENNReal.ofReal (F n γ) ∂P) ≤ ENNReal.ofReal B := by
    filter_upwards [hlarge] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint n hn)
      (ae_of_all _ fun γ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (hbound hP (n + 1) hn t)
  have hL : (∫⁻ γ, ENNReal.ofReal (G γ) ∂P) ≤ ENNReal.ofReal B := hfatou.trans (by
    calc
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal B) atTop := Filter.liminf_le_liminf hle
      _ = _ := Filter.liminf_const _)
  have hGi : Integrable G P := ⟨hGm,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun γ => (Real.exp_pos _).le)).2
      (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hGi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hGi
    (ae_of_all _ fun γ => (Real.exp_pos _).le)] at hL
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le
    (Real.exp_pos _).le)).mp hL

/-- Exponential moments of coordinate displacements, uniformly over starts and laws. -/
theorem u1_signed_physical_coordinate_increment_exp_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x : EinsteinRelation.Vec d} {P : Measure (Path d)},
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x P →
      ∀ t : ℝ≥0, Integrable (fun γ : Path d => Real.exp (q * ((γ t) i - x i))) P ∧
        (∫ γ : Path d, Real.exp (q * ((γ t) i - x i)) ∂P) ≤ Real.exp (C * (t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := u1_signed_physical_coordinate_exp_moment hd ω lam Λ hΛ hω hSmooth i q
  refine ⟨C, hC, ?_⟩
  intro x P hP t
  obtain ⟨hF, hbound⟩ := hb hP t
  have heq (γ : Path d) : Real.exp (q * ((γ t) i - x i)) =
      Real.exp (-q * x i) * Real.exp (q * (γ t) i) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · exact (hF.const_mul _).congr (Filter.Eventually.of_forall fun γ => (heq γ).symm)
  · have he : (∫ γ : Path d, Real.exp (q * ((γ t) i - x i)) ∂P) =
        Real.exp (-q * x i) * ∫ γ : Path d, Real.exp (q * (γ t) i) ∂P := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall heq)
    rw [he]
    have h := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (-q * x i))
    have hc : Real.exp (-q * x i) * Real.exp (q * x i) = 1 := by
      rw [← Real.exp_add]
      have : -q * x i + q * x i = 0 := by ring
      rw [this, Real.exp_zero]
    simpa only [← mul_assoc, hc, one_mul] using h

/-- Uniform exponential displacement moments for the actual signed physical kernel. -/
theorem u1_signed_physical_kernel_coordinate_increment_exp_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : EinsteinRelation.Vec d) (t : ℝ≥0),
      Integrable (fun y : EinsteinRelation.Vec d => Real.exp (q * (y i - x i)))
        (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ∧
      (∫ y : EinsteinRelation.Vec d, Real.exp (q * (y i - x i)) ∂
        Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ≤
        Real.exp (C * (t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ :=
    u1_signed_physical_coordinate_increment_exp_moment hd ω lam Λ hΛ hω hSmooth i q
  obtain ⟨K, ⟨hK, hfdd⟩, _⟩ :=
    Blueprint.gmpPhysicalC0KernelSemigroup_existsUnique_continuous_realization
      hd ω lam Λ hΛ hω hSmooth
  letI : ProbabilityTheory.IsMarkovKernel K := hK
  refine ⟨C, hC, ?_⟩
  intro x t
  have hP := c4_gmpPhysical_realization_solves_martingale_problem
    hd ω lam Λ hΛ hω hSmooth K hfdd x
  obtain ⟨hi, hbound⟩ := hb hP t
  have hmarg := SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
    (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) (K x) x t (by
      have h := congrArg (fun k => k x) (hfdd {t})
      simpa only [ProbabilityTheory.Kernel.map_apply _
        (MarkovProcess.ContinuousPath.measurable_finsetEvaluation _)] using h)
  have hf : Continuous (fun y : EinsteinRelation.Vec d => Real.exp (q * (y i - x i))) :=
    Real.continuous_exp.comp (continuous_const.mul ((continuous_apply i).sub continuous_const))
  have heval : Measurable (fun γ : Path d => γ t) :=
    MarkovProcess.ContinuousPath.measurable_coordinateProcess t
  rw [← hmarg]
  constructor
  · exact (integrable_map_measure hf.aestronglyMeasurable heval.aemeasurable).2 hi
  · rw [integral_map heval.aemeasurable hf.aestronglyMeasurable]
    exact hbound

/-- The actual physical kernel sends each coordinate exponential to a bounded
multiple of the same exponential, uniformly in the starting point. -/
theorem u1_signed_physical_kernel_coordinate_exp_subinvariant
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : EinsteinRelation.Vec d) (t : ℝ≥0),
      Integrable (fun y : EinsteinRelation.Vec d => Real.exp (q * y i))
        (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ∧
      (∫ y : EinsteinRelation.Vec d, Real.exp (q * y i) ∂
        Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ≤
        Real.exp (q * x i) * Real.exp (C * (t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ :=
    u1_signed_physical_kernel_coordinate_increment_exp_moment hd ω lam Λ hΛ hω hSmooth i q
  refine ⟨C, hC, ?_⟩
  intro x t
  obtain ⟨hi, hbound⟩ := hb x t
  have heq (y : EinsteinRelation.Vec d) : Real.exp (q * y i) =
      Real.exp (q * x i) * Real.exp (q * (y i - x i)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · exact (hi.const_mul _).congr (Filter.Eventually.of_forall fun y => (heq y).symm)
  · have he : (∫ y : EinsteinRelation.Vec d, Real.exp (q * y i) ∂
        Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) =
      Real.exp (q * x i) * ∫ y : EinsteinRelation.Vec d, Real.exp (q * (y i - x i)) ∂
        Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall heq)
    rw [he]
    exact mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)

/-- Detailed balance exchanges nonnegative measurable kernel pairings, including
unbounded weights. -/
theorem u1_signed_physical_kernel_lintegral_swap
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (f g : EinsteinRelation.Vec d → ℝ≥0∞) (hf : Measurable f)
    (hg : Measurable g) :
    (∫⁻ x, ∫⁻ y, f x * g y ∂
      Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x
      ∂physicalReversibleMeasure ω hd lam) =
    ∫⁻ x, ∫⁻ y, g x * f y ∂
      Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x
      ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  letI : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  letI : ProbabilityTheory.IsMarkovKernel K := ⟨fun x =>
    ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩⟩
  have hrev : ProbabilityTheory.Kernel.IsReversible K μ := by
    intro A B hA hB
    exact u2_gmpPhysicalC0KernelSemigroup_measurable_rectangles
      hd ω lam Λ hΛ hω hSmooth t A B hA hB
  let F : EinsteinRelation.Vec d × EinsteinRelation.Vec d → ℝ≥0∞ := fun z => f z.1 * g z.2
  have hF : Measurable F := (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  calc
    _ = ∫⁻ z, F z ∂(μ.compProd K) := (Measure.lintegral_compProd hF).symm
    _ = ∫⁻ z, F (Prod.swap z) ∂(μ.compProd K) := by
      have h := lintegral_map (μ := μ.compProd K) hF measurable_swap
      rw [C8GMP.reversible_compProd_swap μ K hrev] at h
      exact h
    _ = _ := by
      change (∫⁻ z, (F ∘ Prod.swap) z ∂(μ.compProd K)) = _
      rw [Measure.lintegral_compProd (hF.comp measurable_swap)]
      simp only [F, Function.comp_apply, Prod.swap, mul_comm]
      rfl

/-- Exponential-weighted L¹ growth for nonnegative kernel inputs in the
physical reversible measure. -/
theorem u1_signed_physical_kernel_weighted_lintegral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (i : Fin d) (q : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0)
      (f : EinsteinRelation.Vec d → ℝ≥0∞), Measurable f →
    (∫⁻ x, ENNReal.ofReal (Real.exp (q * x i)) *
      (∫⁻ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)
      ∂physicalReversibleMeasure ω hd lam) ≤
    ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (q * x i)) * f x
        ∂physicalReversibleMeasure ω hd lam := by
  obtain ⟨C, hC, hb⟩ :=
    u1_signed_physical_kernel_coordinate_exp_subinvariant hd ω lam Λ hΛ hω hSmooth i q
  refine ⟨C, hC, ?_⟩
  intro t f hf
  let μ := physicalReversibleMeasure ω hd lam
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  let w : EinsteinRelation.Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (q * x i))
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (C * (t : ℝ)))
  have hw : Measurable w := (ENNReal.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply i)))).measurable
  have hbound (x : EinsteinRelation.Vec d) : (∫⁻ y, w y ∂K x) ≤ w x * B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hb x t).1
      (ae_of_all _ fun y => (Real.exp_pos _).le)]
    change ENNReal.ofReal (∫ y, Real.exp (q * y i) ∂K x) ≤
      ENNReal.ofReal (Real.exp (q * x i)) * ENNReal.ofReal (Real.exp (C * (t : ℝ)))
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hb x t).2
  change (∫⁻ x, w x * (∫⁻ y, f y ∂K x) ∂μ) ≤ B * ∫⁻ x, w x * f x ∂μ
  calc
    _ = ∫⁻ x, ∫⁻ y, w x * f y ∂K x ∂μ := by
      simp_rw [lintegral_const_mul _ hf]
    _ = ∫⁻ x, ∫⁻ y, f x * w y ∂K x ∂μ :=
      u1_signed_physical_kernel_lintegral_swap hd ω lam Λ hΛ hω hSmooth t w f hw hf
    _ ≤ ∫⁻ x, f x * (w x * B) ∂μ := by
      apply lintegral_mono
      intro x
      change (∫⁻ y, f x * w y ∂K x) ≤ f x * (w x * B)
      rw [lintegral_const_mul _ hw]
      simpa only [mul_comm] using mul_le_mul_left (hbound x) (f x)
    _ = ∫⁻ x, B * (w x * f x) ∂μ := by
      congr 1
      funext x
      ac_rfl
    _ = B * ∫⁻ x, w x * f x ∂μ := lintegral_const_mul _ (hw.mul hf)

/-- The inverse exponential weight against the force measure is exactly the
Lebesgue exponential gauge, for arbitrary nonnegative functions. -/
theorem u1_signed_gauge_lintegral_identity {d : ℕ} (i : Fin d)
    (lam : ℝ) (f : EinsteinRelation.Vec d → ℝ≥0∞) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-lam * x i)) * f x
      ∂physicalForceMeasure i lam) =
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x i)) * f x := by
  unfold physicalForceMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume
    (show Measurable (fun x : EinsteinRelation.Vec d =>
      ENNReal.ofReal (Real.exp (2 * lam * x i))) from
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_apply i)))).measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (Real.exp (2 * lam * x i)) *
    (ENNReal.ofReal (Real.exp (-lam * x i)) * f x) = _
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

/-- The actual signed kernel grows Lebesgue gauge L¹ mass at most
exponentially, with the physical clock comparison included. -/
theorem u1_signed_physical_kernel_gauge_lintegral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0)
      (f : EinsteinRelation.Vec d → ℝ≥0∞), Measurable f →
    (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
      (∫⁻ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
    (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * f x := by
  obtain ⟨C, hC, hbound⟩ := u1_signed_physical_kernel_weighted_lintegral_le
    hd ω lam Λ hΛ hω hSmooth (firstCoordinateIndex hd) (-lam)
  refine ⟨C, hC, ?_⟩
  intro t f hf
  let μ := physicalReversibleMeasure ω hd lam
  let ν := physicalForceMeasure (firstCoordinateIndex hd) lam
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  let w : EinsteinRelation.Vec d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd)))
  let A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * Λ))
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (C * (t : ℝ)))
  have hc := u1_signed_physical_force_measure_comparable hd ω lam Λ hω
  calc
    _ = ∫⁻ x, w x * (∫⁻ y, f y ∂K x) ∂ν :=
      (u1_signed_gauge_lintegral_identity (firstCoordinateIndex hd) lam _).symm
    _ ≤ A * ∫⁻ x, w x * (∫⁻ y, f y ∂K x) ∂μ := by
      have h := lintegral_mono' hc.2 (le_refl (fun x => w x * (∫⁻ y, f y ∂K x)))
      simpa only [lintegral_smul_measure, smul_eq_mul] using h
    _ ≤ A * (B * ∫⁻ x, w x * f x ∂μ) :=
      by simpa only [mul_comm] using mul_le_mul_left (hbound t f hf) A
    _ ≤ A * (B * (A * ∫⁻ x, w x * f x ∂ν)) := by
      gcongr
      have h := lintegral_mono' hc.1 (le_refl (fun x => w x * f x))
      simpa only [lintegral_smul_measure, smul_eq_mul] using h
    _ = _ := by
      rw [u1_signed_gauge_lintegral_identity (firstCoordinateIndex hd) lam f]
      simp only [pow_two]
      dsimp only [A, B]
      ac_rfl

/-- An exponential weight against the force measure is exactly the
corresponding Lebesgue exponential weight, for arbitrary nonnegative functions. -/
theorem u1_signed_weight_lintegral_identity {d : ℕ} (i : Fin d)
    (lam q : ℝ) (f : EinsteinRelation.Vec d → ℝ≥0∞) :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((q - 2 * lam) * x i)) * f x
      ∂physicalForceMeasure i lam) =
    ∫⁻ x, ENNReal.ofReal (Real.exp (q * x i)) * f x := by
  unfold physicalForceMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume
    (show Measurable (fun x : EinsteinRelation.Vec d =>
      ENNReal.ofReal (Real.exp (2 * lam * x i))) from
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_apply i)))).measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (Real.exp (2 * lam * x i)) *
    (ENNReal.ofReal (Real.exp ((q - 2 * lam) * x i)) * f x) = _
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

/-- The actual signed kernel grows arbitrary exponentially weighted Lebesgue L¹ mass at most
exponentially, with the physical clock comparison included. -/
theorem u1_signed_physical_kernel_weight_lintegral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0)
      (f : EinsteinRelation.Vec d → ℝ≥0∞), Measurable f →
    (∫⁻ x, ENNReal.ofReal (Real.exp (q * x (firstCoordinateIndex hd))) *
      (∫⁻ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
    (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (q * x (firstCoordinateIndex hd))) * f x := by
  obtain ⟨C, hC, hbound⟩ := u1_signed_physical_kernel_weighted_lintegral_le
    hd ω lam Λ hΛ hω hSmooth (firstCoordinateIndex hd) (q - 2 * lam)
  refine ⟨C, hC, ?_⟩
  intro t f hf
  let μ := physicalReversibleMeasure ω hd lam
  let ν := physicalForceMeasure (firstCoordinateIndex hd) lam
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  let w : EinsteinRelation.Vec d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp ((q - 2 * lam) * x (firstCoordinateIndex hd)))
  let A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * Λ))
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (C * (t : ℝ)))
  have hc := u1_signed_physical_force_measure_comparable hd ω lam Λ hω
  calc
    _ = ∫⁻ x, w x * (∫⁻ y, f y ∂K x) ∂ν :=
      (u1_signed_weight_lintegral_identity (firstCoordinateIndex hd) lam q _).symm
    _ ≤ A * ∫⁻ x, w x * (∫⁻ y, f y ∂K x) ∂μ := by
      have h := lintegral_mono' hc.2 (le_refl (fun x => w x * (∫⁻ y, f y ∂K x)))
      simpa only [lintegral_smul_measure, smul_eq_mul] using h
    _ = (∫⁻ x, w x * (∫⁻ y, f y ∂K x) ∂μ) * A := mul_comm _ _
    _ ≤ (B * ∫⁻ x, w x * f x ∂μ) * A :=
      mul_le_mul_left (hbound t f hf) A
    _ = A * (B * ∫⁻ x, w x * f x ∂μ) := mul_comm _ _
    _ ≤ A * (B * (A * ∫⁻ x, w x * f x ∂ν)) := by
      gcongr
      have h := lintegral_mono' hc.1 (le_refl (fun x => w x * f x))
      simpa only [lintegral_smul_measure, smul_eq_mul] using h
    _ = _ := by
      rw [u1_signed_weight_lintegral_identity (firstCoordinateIndex hd) lam q f]
      simp only [pow_two]
      dsimp only [A, B]
      ac_rfl

/-- The gauge L¹ estimate transfers to the actual physical L² semigroup. -/
theorem u1_signed_physical_semigroup_gauge_lintegral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (f : EinsteinRelation.Vec d → ℝ)
      (hf : Measurable f) (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam)),
    (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
      ENNReal.ofReal |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x|) ≤
    (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * ENNReal.ofReal |f x| := by
  obtain ⟨C, hC, hb⟩ := u1_signed_physical_kernel_gauge_lintegral_le
    hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, hC, ?_⟩
  intro t f hf hf2
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  let F : EinsteinRelation.Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal |f y|
  have hF : Measurable F := by
    simpa only [F, Real.norm_eq_abs] using hf.norm.ennreal_ofReal
  have hpoint : ∀ᵐ x ∂(volume : Measure (EinsteinRelation.Vec d)),
      ENNReal.ofReal |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x| ≤
        ∫⁻ y, F y ∂K x := by
    filter_upwards [u1_signed_kernel_integral_ae_volume hd ω lam Λ hΛ hω hSmooth t f hf2,
      u1_signed_kernel_integrable_ae_volume hd ω lam Λ hΛ hω hSmooth t f hf2] with x he hi
    rw [← he, ← ofReal_integral_eq_lintegral_ofReal hi.abs
      (ae_of_all _ fun y => abs_nonneg (f y))]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := f) (μ := K x)))
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
      (∫⁻ y, F y ∂K x) := by
        apply lintegral_mono_ae
        filter_upwards [hpoint] with x hx
        simpa only [mul_comm] using mul_le_mul_left hx
          (ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))))
    _ ≤ _ := hb t F hF

/-- Gauge integrability is preserved by the actual signed physical semigroup. -/
theorem u1_signed_physical_semigroup_gauge_integrable
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (f : EinsteinRelation.Vec d → ℝ) (hf : Measurable f)
    (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (hfi : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume) :
    Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x) volume := by
  let G : EinsteinRelation.Vec d → ℝ := fun x =>
    Real.exp (lam * x (firstCoordinateIndex hd)) * f x
  let H : EinsteinRelation.Vec d → ℝ := fun x =>
    Real.exp (lam * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x
  have hG : (∫⁻ x, ENNReal.ofReal |G x|) < ∞ := by
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => abs_nonneg (G x))).mp
    simpa only [Real.norm_eq_abs] using hfi.hasFiniteIntegral.norm
  obtain ⟨C, _, hb⟩ := u1_signed_physical_semigroup_gauge_lintegral_le
    hd ω lam Λ hΛ hω hSmooth
  have hrewrite (a : ℝ) (x : EinsteinRelation.Vec d) :
      ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * ENNReal.ofReal |a| =
        ENNReal.ofReal |Real.exp (lam * x (firstCoordinateIndex hd)) * a| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hH : (∫⁻ x, ENNReal.ofReal |H x|) < ∞ := by
    have h := hb t f hf hf2
    simp_rw [hrewrite] at h
    exact lt_of_le_of_lt h (by
      apply ENNReal.mul_lt_top
      · apply ENNReal.mul_lt_top
        · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
        · exact ENNReal.ofReal_lt_top
      · exact hG)
  have hm : AEStronglyMeasurable H volume := by
    apply Measurable.aestronglyMeasurable
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_apply (firstCoordinateIndex hd)))).measurable.mul
      (Lp.stronglyMeasurable _).measurable
  refine ⟨hm, (hasFiniteIntegral_norm_iff H).mp ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => abs_nonneg (H x))).mpr
  simpa only [Real.norm_eq_abs] using hH

/-- Real-valued gauge L¹ growth for the signed physical semigroup. -/
theorem u1_signed_physical_semigroup_gauge_L1_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (f : EinsteinRelation.Vec d → ℝ)
      (hf : Measurable f) (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
    (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x|) ≤
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
      ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x| := by
  obtain ⟨C, hC, hb⟩ := u1_signed_physical_semigroup_gauge_lintegral_le
    hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, hC, ?_⟩
  intro t f hf hf2 hfi
  have hfo := u1_signed_physical_semigroup_gauge_integrable
    hd ω lam Λ hΛ hω hSmooth t f hf hf2 hfi
  have hrewrite (a : ℝ) (x : EinsteinRelation.Vec d) :
      ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * ENNReal.ofReal |a| =
        ENNReal.ofReal |Real.exp (lam * x (firstCoordinateIndex hd)) * a| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have h := hb t f hf hf2
  simp_rw [hrewrite] at h
  rw [← ofReal_integral_eq_lintegral_ofReal hfo.abs (ae_of_all _ fun x => abs_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hfi.abs (ae_of_all _ fun x => abs_nonneg _),
    ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- On each bounded time interval, the signed physical L² orbit has a
uniform gauge L¹ bound. -/
theorem u1_signed_physical_semigroup_gauge_L1_interval
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
      ∀ (t s : ℝ≥0), s ≤ t →
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω s f x) volume ∧
      (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω s f x|) ≤
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
        ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x| := by
  obtain ⟨C, hC, hb⟩ := u1_signed_physical_semigroup_gauge_L1_le
    hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, hC, ?_⟩
  intro f hf t s hst
  have hmeas : Measurable (f : EinsteinRelation.Vec d → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hi := u1_signed_physical_semigroup_gauge_integrable
    hd ω lam Λ hΛ hω hSmooth s f hmeas (Lp.memLp f) hf
  have hbound := hb s f hmeas (Lp.memLp f) hf
  rw [Lp.toLp_coeFn] at hi hbound
  refine ⟨hi, hbound.trans ?_⟩
  have hExp : Real.exp (C * (s : ℝ)) ≤ Real.exp (C * (t : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hst) hC)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hExp (sq_nonneg _)) (integral_nonneg fun _ => abs_nonneg _)

/-- The exponentially weighted L¹ estimate transfers to the actual physical L² semigroup. -/
theorem u1_signed_physical_semigroup_weight_lintegral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (f : EinsteinRelation.Vec d → ℝ)
      (hf : Measurable f) (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam)),
    (∫⁻ x, ENNReal.ofReal (Real.exp (q * x (firstCoordinateIndex hd))) *
      ENNReal.ofReal |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x|) ≤
    (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (q * x (firstCoordinateIndex hd))) * ENNReal.ofReal |f x| := by
  obtain ⟨C, hC, hb⟩ := u1_signed_physical_kernel_weight_lintegral_le
    hd ω lam Λ hΛ hω hSmooth q
  refine ⟨C, hC, ?_⟩
  intro t f hf hf2
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  let F : EinsteinRelation.Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal |f y|
  have hF : Measurable F := by
    simpa only [F, Real.norm_eq_abs] using hf.norm.ennreal_ofReal
  have hpoint : ∀ᵐ x ∂(volume : Measure (EinsteinRelation.Vec d)),
      ENNReal.ofReal |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x| ≤
        ∫⁻ y, F y ∂K x := by
    filter_upwards [u1_signed_kernel_integral_ae_volume hd ω lam Λ hΛ hω hSmooth t f hf2,
      u1_signed_kernel_integrable_ae_volume hd ω lam Λ hΛ hω hSmooth t f hf2] with x he hi
    rw [← he, ← ofReal_integral_eq_lintegral_ofReal hi.abs
      (ae_of_all _ fun y => abs_nonneg (f y))]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := f) (μ := K x)))
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (q * x (firstCoordinateIndex hd))) *
      (∫⁻ y, F y ∂K x) := by
        apply lintegral_mono_ae
        filter_upwards [hpoint] with x hx
        simpa only [mul_comm] using mul_le_mul_left hx
          (ENNReal.ofReal (Real.exp (q * x (firstCoordinateIndex hd))))
    _ ≤ _ := hb t F hF

/-- Weighted integrability is preserved by the actual signed physical semigroup. -/
theorem u1_signed_physical_semigroup_weight_integrable
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (q : ℝ)
    (t : ℝ≥0) (f : EinsteinRelation.Vec d → ℝ) (hf : Measurable f)
    (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam))
    (hfi : Integrable (fun x => Real.exp (q * x (firstCoordinateIndex hd)) * f x) volume) :
    Integrable (fun x => Real.exp (q * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x) volume := by
  let G : EinsteinRelation.Vec d → ℝ := fun x =>
    Real.exp (q * x (firstCoordinateIndex hd)) * f x
  let H : EinsteinRelation.Vec d → ℝ := fun x =>
    Real.exp (q * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x
  have hG : (∫⁻ x, ENNReal.ofReal |G x|) < ∞ := by
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => abs_nonneg (G x))).mp
    simpa only [Real.norm_eq_abs] using hfi.hasFiniteIntegral.norm
  obtain ⟨C, _, hb⟩ := u1_signed_physical_semigroup_weight_lintegral_le
    hd ω lam Λ hΛ hω hSmooth q
  have hrewrite (a : ℝ) (x : EinsteinRelation.Vec d) :
      ENNReal.ofReal (Real.exp (q * x (firstCoordinateIndex hd))) * ENNReal.ofReal |a| =
        ENNReal.ofReal |Real.exp (q * x (firstCoordinateIndex hd)) * a| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hH : (∫⁻ x, ENNReal.ofReal |H x|) < ∞ := by
    have h := hb t f hf hf2
    simp_rw [hrewrite] at h
    exact lt_of_le_of_lt h (by
      apply ENNReal.mul_lt_top
      · apply ENNReal.mul_lt_top
        · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
        · exact ENNReal.ofReal_lt_top
      · exact hG)
  have hm : AEStronglyMeasurable H volume := by
    apply Measurable.aestronglyMeasurable
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_apply (firstCoordinateIndex hd)))).measurable.mul
      (Lp.stronglyMeasurable _).measurable
  refine ⟨hm, (hasFiniteIntegral_norm_iff H).mp ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => abs_nonneg (H x))).mpr
  simpa only [Real.norm_eq_abs] using hH

/-- Real-valued exponentially weighted L¹ growth for the signed physical semigroup. -/
theorem u1_signed_physical_semigroup_weight_L1_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (f : EinsteinRelation.Vec d → ℝ)
      (hf : Measurable f) (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (q * x (firstCoordinateIndex hd)) * f x) volume →
    (∫ x, |Real.exp (q * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x|) ≤
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
      ∫ x, |Real.exp (q * x (firstCoordinateIndex hd)) * f x| := by
  obtain ⟨C, hC, hb⟩ := u1_signed_physical_semigroup_weight_lintegral_le
    hd ω lam Λ hΛ hω hSmooth q
  refine ⟨C, hC, ?_⟩
  intro t f hf hf2 hfi
  have hfo := u1_signed_physical_semigroup_weight_integrable
    hd ω lam Λ hΛ hω hSmooth q t f hf hf2 hfi
  have hrewrite (a : ℝ) (x : EinsteinRelation.Vec d) :
      ENNReal.ofReal (Real.exp (q * x (firstCoordinateIndex hd))) * ENNReal.ofReal |a| =
        ENNReal.ofReal |Real.exp (q * x (firstCoordinateIndex hd)) * a| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have h := hb t f hf hf2
  simp_rw [hrewrite] at h
  rw [← ofReal_integral_eq_lintegral_ofReal hfo.abs (ae_of_all _ fun x => abs_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hfi.abs (ae_of_all _ fun x => abs_nonneg _),
    ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- On each bounded time interval, the signed physical L² orbit has a
uniform exponentially weighted L¹ bound. -/
theorem u1_signed_physical_semigroup_weight_L1_interval
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (q * x (firstCoordinateIndex hd)) * f x) volume →
      ∀ (t s : ℝ≥0), s ≤ t →
      Integrable (fun x => Real.exp (q * x (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω s f x) volume ∧
      (∫ x, |Real.exp (q * x (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω s f x|) ≤
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
        ∫ x, |Real.exp (q * x (firstCoordinateIndex hd)) * f x| := by
  obtain ⟨C, hC, hb⟩ := u1_signed_physical_semigroup_weight_L1_le
    hd ω lam Λ hΛ hω hSmooth q
  refine ⟨C, hC, ?_⟩
  intro f hf t s hst
  have hmeas : Measurable (f : EinsteinRelation.Vec d → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hi := u1_signed_physical_semigroup_weight_integrable
    hd ω lam Λ hΛ hω hSmooth q s f hmeas (Lp.memLp f) hf
  have hbound := hb s f hmeas (Lp.memLp f) hf
  rw [Lp.toLp_coeFn] at hi hbound
  refine ⟨hi, hbound.trans ?_⟩
  have hExp : Real.exp (C * (s : ℝ)) ≤ Real.exp (C * (t : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hst) hC)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hExp (sq_nonneg _)) (integral_nonneg fun _ => abs_nonneg _)

/-- The signed physical generator orbit obeys the raised gauge Nash
inequality, including the force-dependent mass correction. -/
theorem u1_signed_physical_generator_orbit_gauge_nash_raised
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    let μ := physicalReversibleMeasure ω hd lam
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    ∃ C : ℝ, 0 < C ∧ ∀ (f : S.generatorDomain) (t : ℝ≥0), 0 < t →
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * S t f x) volume →
      (‖S t f‖ ^ 2) ^ (1 + 2 / (d : ℝ)) ≤
        C * (Real.exp (2 * Λ) * (4 * Λ *
          (-inner ℝ (S t (S.generator f)) (S t f)) +
          2 * lam ^ 2 * ‖S t f‖ ^ 2)) *
        (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * S t f x|) ^
          (4 / (d : ℝ)) := by
  let μ := physicalReversibleMeasure ω hd lam
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  obtain ⟨C, hC, hN⟩ := u1_signed_physical_closedForm_gauge_nash hd ω lam Λ hΛ hω
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  refine ⟨C ^ (1 + 2 / (d : ℝ)), Real.rpow_pos_of_pos hC _, ?_⟩
  intro f t ht hi
  let u : Lp ℝ 2 μ := S t f
  let E : ℝ := -inner ℝ (S t (S.generator f)) u
  let M : ℝ := ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * u x|
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hE : 0 ≤ E := by
    simpa only [E, u, Real.toNNReal_coe] using
      (SubdiffusiveProcess.Nash.orbit_energy_nonneg S f htR)
  have hnorm : (∫ x, u x ^ 2 ∂μ) = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have heq : (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form u u = E :=
    Blueprint.gmpPhysicalSemigroup_orbit_energy_generator hd ω lam Λ hΛ hω f t
  have hu : physicalH1Member ω hd lam u :=
    Blueprint.gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω
      ⟨u, S.operator_mem_generatorDomain f t⟩
  have hn := hN u hu hi
  rw [hnorm, heq] at hn
  have hΛ0 : 0 ≤ Λ := by linarith
  have hQ : 0 ≤ Real.exp (2 * Λ) * (4 * Λ * E + 2 * lam ^ 2 * ‖u‖ ^ 2) := by
    positivity
  have hM : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  exact u7_nash_raise d C (‖u‖ ^ 2)
    (Real.exp (2 * Λ) * (4 * Λ * E + 2 * lam ^ 2 * ‖u‖ ^ 2)) M
    hdR hC.le (sq_nonneg _) hQ hM hn

/-- Nash decay with a nonnegative linear growth term, removed by an
exponential integrating factor. -/
theorem u1_nash_decay_with_linear_term (u v : ℝ → ℝ) (d c b t : ℝ)
    (hd : 0 < d) (hc : 0 < c) (hb : 0 ≤ b) (ht : 0 < t)
    (hu : ContinuousOn u (Icc 0 t))
    (hpos : ∀ s ∈ Icc 0 t, 0 < u s)
    (hder : ∀ s ∈ Ioo 0 t, HasDerivAt u (v s) s)
    (hineq : ∀ s ∈ Ioo 0 t,
      v s ≤ -(d * c) * u s ^ (1 + 1 / d) + b * u s) :
    u t ≤ Real.exp (b * t) * (c * t) ^ (-d) := by
  let w : ℝ → ℝ := fun s => Real.exp (-b * s) * u s
  let z : ℝ → ℝ := fun s => Real.exp (-b * s) * (v s - b * u s)
  have hw : ContinuousOn w (Icc 0 t) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hu
  have hwp (s : ℝ) (hs : s ∈ Icc 0 t) : 0 < w s :=
    mul_pos (Real.exp_pos _) (hpos s hs)
  have hwder (s : ℝ) (hs : s ∈ Ioo 0 t) : HasDerivAt w (z s) s := by
    have h := (((hasDerivAt_id s).const_mul (-b)).exp).mul (hder s hs)
    convert h using 1
    · funext x
      simp only [w, Pi.mul_apply, id_eq, neg_mul]
    · dsimp [z]
      ring
  have hwineq (s : ℝ) (hs : s ∈ Ioo 0 t) :
      z s ≤ -(d * c) * w s ^ (1 + 1 / d) := by
    have hexp : Real.exp (-b * s) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [hs.1])
    have hpow : Real.exp (-b * s) ^ (1 + 1 / d) ≤ Real.exp (-b * s) :=
      Real.rpow_le_self_of_le_one (Real.exp_nonneg _) hexp (le_add_of_nonneg_right (by positivity))
    have hpowu : 0 ≤ u s ^ (1 + 1 / d) :=
      Real.rpow_nonneg (hpos s (Ioo_subset_Icc_self hs)).le _
    have hcomp : w s ^ (1 + 1 / d) ≤ Real.exp (-b * s) * u s ^ (1 + 1 / d) := by
      dsimp [w]
      rw [Real.mul_rpow (Real.exp_nonneg _) (hpos s (Ioo_subset_Icc_self hs)).le]
      exact mul_le_mul_of_nonneg_right hpow hpowu
    have hm := mul_le_mul_of_nonneg_left (hineq s hs) (Real.exp_nonneg (-b * s))
    dsimp [z]
    nlinarith [mul_nonneg hd.le hc.le]
  have hdec := SubdiffusiveProcess.Nash.decay_rpow w z d c t hd hc ht hw hwp hwder hwineq
  have he : Real.exp (b * t) * Real.exp (-b * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hm := mul_le_mul_of_nonneg_left hdec (Real.exp_nonneg (b * t))
  dsimp [w] at hm
  calc
    u t = Real.exp (b * t) * (Real.exp (-b * t) * u t) := by rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp (b * t) * (c * t) ^ (-d) := hm

/-- The signed generator orbit satisfies the Nash differential inequality
with the gauge mass bounded uniformly on the chosen time interval. -/
theorem u1_signed_physical_generator_nash_differential
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    ∃ C : ℝ, 0 < C ∧ ∀ (f : S.generatorDomain)
      (hf : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x) volume)
      (t : ℝ≥0) (F : ℝ), 0 < F →
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
        (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x|) ≤ F →
      ∀ (s : ℝ≥0), 0 < s → s ≤ t →
      let K := C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))
      2 * inner ℝ (S s (S.generator f)) (S s f) ≤
        -(2 / (4 * Λ * K)) * (‖S s f‖ ^ 2) ^ (1 + 2 / (d : ℝ)) +
          (lam ^ 2 / Λ) * ‖S s f‖ ^ 2 := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  obtain ⟨C₁, hC₁, hN⟩ := u1_signed_physical_generator_orbit_gauge_nash_raised hd ω lam Λ hΛ hω
  obtain ⟨C₂, hC₂, hM⟩ := u1_signed_physical_semigroup_gauge_L1_interval hd ω lam Λ hΛ hω hSmooth
  let C := max C₁ (C₂ + 1)
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro f hf t F hF hfF s hs hst
  let E : ℝ := -inner ℝ (S s (S.generator f)) (S s f)
  let U : ℝ := ‖S s f‖ ^ 2
  let M : ℝ := ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * S s f x|
  let K : ℝ := C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hΛp : 0 < Λ := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hE : 0 ≤ E := by
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    simpa only [E, S, Real.toNNReal_coe] using
      (SubdiffusiveProcess.Nash.orbit_energy_nonneg S f hsR)
  have hmass := hM (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) hf t s hst
  have hMF : M ≤ F := by
    apply hmass.2.trans
    apply (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => abs_nonneg _)).trans hfF
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (le_trans (by linarith : C₂ ≤ C₂ + 1) (le_max_right _ _)) t.coe_nonneg
  have hM0 : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  have hn := hN f s hs hmass.1
  have hb : U ^ (1 + 2 / (d : ℝ)) ≤ K * (4 * Λ * E + 2 * lam ^ 2 * U) := by
    calc
      _ ≤ C₁ * (Real.exp (2 * Λ) * (4 * Λ * E + 2 * lam ^ 2 * U)) * M ^ (4 / (d : ℝ)) := hn
      _ ≤ C * (Real.exp (2 * Λ) * (4 * Λ * E + 2 * lam ^ 2 * U)) * F ^ (4 / (d : ℝ)) := by
        gcongr
        exact le_max_left _ _
      _ = K * (4 * Λ * E + 2 * lam ^ 2 * U) := by dsimp [K]; ring
  have hdiv : U ^ (1 + 2 / (d : ℝ)) / (4 * Λ * K) ≤ E + (lam ^ 2 / (2 * Λ)) * U := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Λ * K)).2
    calc
      _ ≤ K * (4 * Λ * E + 2 * lam ^ 2 * U) := hb
      _ = (E + lam ^ 2 / (2 * Λ) * U) * (4 * Λ * K) := by
        field_simp [ne_of_gt hΛp]
        <;> ring
  have hident : 2 * inner ℝ (S s (S.generator f)) (S s f) = -2 * E := by
    dsimp [E]
    ring
  dsimp only
  rw [hident]
  change -2 * E ≤ -(2 / (4 * Λ * K)) * U ^ (1 + 2 / (d : ℝ)) + (lam ^ 2 / Λ) * U
  have hΛne : Λ ≠ 0 := ne_of_gt hΛp
  have hKne : K ≠ 0 := ne_of_gt hK
  field_simp at hdiv ⊢
  nlinarith

private theorem u1_closedForm_energyEpigraph_isClosed {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (E : SubdiffusiveProcess.DirichletForm.ClosedForm μ) :
    IsClosed {p : Lp ℝ 2 μ × ℝ | p.1 ∈ E.domain ∧ E.form p.1 p.1 ≤ p.2} :=
  IsSeqClosed.isClosed <| by
    intro ps p hps hp
    have hfirst : Tendsto (fun n => (ps n).1) atTop (𝓝 p.1) :=
      (continuous_fst.tendsto p).comp hp
    have hsecond : Tendsto (fun n => (ps n).2) atTop (𝓝 p.2) :=
      (continuous_snd.tendsto p).comp hp
    have hbound (ε : ℝ) (hε : 0 < ε) :
        p.1 ∈ E.domain ∧ E.form p.1 p.1 ≤ p.2 + ε := by
      have hclosed : IsClosed {u : Lp ℝ 2 μ | u ∈ E.domain ∧ E.form u u ≤ p.2 + ε} :=
        IsSeqClosed.isClosed <| by
          intro us u hus hlim
          exact E.mem_domain_of_tendsto_of_form_le (fun n => (hus n).1) hlim
            (fun n => (hus n).2)
      apply hclosed.mem_of_tendsto hfirst
      filter_upwards [(tendsto_order.1 hsecond).2 (p.2 + ε) (lt_add_of_pos_right _ hε)] with n hn
      exact ⟨(hps n).1, (hps n).2.trans hn.le⟩
    exact ⟨(hbound 1 zero_lt_one).1, le_of_forall_pos_le_add fun ε hε => (hbound ε hε).2⟩

/-- The signed physical orbit enters the form domain with a quantitative energy bound. -/
theorem u1_signed_physical_positive_time_energy
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ≥0) (ht : 0 < t) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    let E := Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω
    physicalH1Member ω hd lam (S t f) ∧
      E.form (S t f) (S t f) ≤ (t : ℝ)⁻¹ * (2 * ‖f‖ * ‖f‖) := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let E := Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  have ht0 : 0 < (t : ℝ) := NNReal.coe_pos.mpr ht
  have hgen (g : S.generatorDomain) :
      E.form (S t g) (S t g) ≤ (t : ℝ)⁻¹ * (2 * ‖(g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))‖ * ‖g‖) := by
    let en (s : ℝ) : ℝ := E.form (S (Real.toNNReal s) g) (S (Real.toNNReal s) g)
    let q (s : ℝ) : ℝ := -inner ℝ (S (Real.toNNReal s) (S.generator g)) g
    have hmono (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) : en t ≤ en s := by
      let r := Real.toNNReal s
      have hr : r ≤ t := by
        have hc : (r : ℝ) ≤ (t : ℝ) := by
          simpa [r, Real.toNNReal_of_nonneg hs.1] using hs.2
        exact_mod_cast hc
      have hg := Blueprint.gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω g
      have h := Blueprint.gmpPhysicalSemigroup_energy_le hd ω lam Λ hΛ hω (t - r)
        (Blueprint.gmpPhysicalSemigroup_energy_le hd ω lam Λ hΛ hω r hg).1
      have h := h.2
      change E.form (S (t - r) (S r g)) (S (t - r) (S r g)) ≤ E.form (S r g) (S r g) at h
      rw [← S.add_apply, tsub_add_cancel_of_le hr] at h
      simpa [en, r, Real.toNNReal_coe] using h
    have hpoint (s : ℝ) : en s ≤ q s := by
      let r := Real.toNNReal s
      have hr : r / 2 + r / 2 = r := by ext; simp
      have hb := Blueprint.gmpPhysicalSemigroup_orbit_energy_double_le hd ω lam Λ hΛ hω g (r / 2)
      change E.form (S (r / 2 + r / 2) g) (S (r / 2 + r / 2) g) ≤ _ at hb
      rw [hr] at hb
      have he := Blueprint.gmpPhysicalSemigroup_orbit_energy_generator hd ω lam Λ hΛ hω g (r / 2)
      change E.form (S (r / 2) g) (S (r / 2) g) = -inner ℝ (S (r / 2) (S.generator g)) (S (r / 2) g) at he
      rw [Blueprint.gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω (r / 2)
        (S.generator g) (S (r / 2) g), ← S.add_apply, hr,
        ← Blueprint.gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω r (S.generator g) g] at he
      exact hb.trans_eq he
    have hen : IntervalIntegrable en volume 0 t :=
      (Blueprint.gmpPhysicalSemigroup_continuous_orbit_energy hd ω lam Λ hΛ hω g).intervalIntegrable 0 t
    have hq : IntervalIntegrable q volume 0 t :=
      (((S.continuous_operator_toNNReal (S.generator g)).inner continuous_const).neg).intervalIntegrable 0 t
    have hm := intervalIntegral.integral_mono_on (μ := volume) t.coe_nonneg
      (intervalIntegrable_const) hen hmono
    have hi := intervalIntegral.integral_mono_on (μ := volume) t.coe_nonneg hen hq (fun s _ => hpoint s)
    have hc : (∫ s in (0 : ℝ)..t, q s) = inner ℝ ((g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) - S t g) g := by
      dsimp [q]
      rw [intervalIntegral.integral_neg]
      have h := (innerSL ℝ (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))).intervalIntegral_comp_comm (μ := volume)
        ((S.continuous_operator_toNNReal (S.generator g)).intervalIntegrable 0 t)
      simp only [innerSL_apply_apply] at h
      have hs : (∫ s in (0 : ℝ)..t, inner ℝ (S (Real.toNNReal s) (S.generator g)) g) =
          ∫ s in (0 : ℝ)..t, inner ℝ (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (S (Real.toNNReal s) (S.generator g)) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact real_inner_comm _ _
      rw [hs, h, ← S.operator_sub_eq_integral g t]
      rw [inner_sub_right, inner_sub_left, real_inner_comm (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (S t g)]
      ring
    have hb : inner ℝ ((g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) - S t g) g ≤ 2 * ‖g‖ * ‖g‖ := by
      calc
        _ ≤ ‖(g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) - S t g‖ * ‖g‖ := real_inner_le_norm _ _
        _ ≤ (‖g‖ + ‖S t g‖) * ‖g‖ := mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
        _ ≤ (‖g‖ + ‖g‖) * ‖g‖ := mul_le_mul_of_nonneg_right (add_le_add_right (S.norm_apply_le t g) _) (norm_nonneg _)
        _ = _ := by ring
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
    rw [hc] at hi
    have hx : (t : ℝ) * en t ≤ 2 * ‖g‖ * ‖g‖ := hm.trans (hi.trans hb)
    have := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr ht0.le)
    rw [← mul_assoc, inv_mul_cancel₀ ht0.ne', one_mul] at this
    simpa [en, Real.toNNReal_coe] using this
  let a (r : ℝ≥0) : S.generatorDomain := ⟨(r : ℝ)⁻¹ • S.orbitIntegral f r,
    S.generatorDomain.smul_mem _ (S.orbitIntegral_mem_generatorDomain f r)⟩
  have ha : Tendsto (fun r : ℝ≥0 => (a r : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
      (𝓝[Set.Ioi 0] 0) (𝓝 f) := S.tendsto_inv_smul_orbitIntegral f
  have hp := (((S t).continuous.tendsto f).comp ha).prodMk_nhds
    ((((ha.norm.const_mul 2).mul ha.norm).const_mul ((t : ℝ)⁻¹)))
  have hm := (u1_closedForm_energyEpigraph_isClosed E).mem_of_tendsto hp
    (Filter.Eventually.of_forall fun r => by
      have hdom := S.operator_mem_generatorDomain (a r) t
      exact ⟨(Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr
        (Blueprint.gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω ⟨_, hdom⟩), hgen (a r)⟩)
  exact ⟨(Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mp hm.1, hm.2⟩


/-- The positive-time form is jointly bounded on actual L² inputs. -/
theorem u1_signed_physical_positive_time_form_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (t : ℝ≥0) (ht : 0 < t) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    let E := Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω
    E.form (S t f) (S t v) ^ 2 ≤
      ((t : ℝ)⁻¹ * (2 * ‖f‖ * ‖f‖)) *
        ((t : ℝ)⁻¹ * (2 * ‖v‖ * ‖v‖)) := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let E := Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  have hf := u1_signed_physical_positive_time_energy hd ω lam Λ hΛ hω f t ht
  have hv := u1_signed_physical_positive_time_energy hd ω lam Λ hΛ hω v t ht
  have hfD : S t f ∈ E.domain :=
    (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr hf.1
  have hvD : S t v ∈ E.domain :=
    (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr hv.1
  exact (E.form_sq_le_mul hfD hvD).trans
    (mul_le_mul hf.2 hv.2 (E.form_nonneg _ hvD)
      (mul_nonneg (inv_nonneg.mpr t.coe_nonneg) (by positivity)))

/-- Semigroup symmetry intertwines the form on its whole domain. -/
theorem u1_signed_physical_form_semigroup_intertwine_full
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : physicalH1Member ω hd lam f) (hv : physicalH1Member ω hd lam v)
    (t : ℝ≥0) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    let E := Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω
    E.form (S t f) v = E.form f (S t v) := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  have hSf := (Blueprint.gmpPhysicalSemigroup_energy_le hd ω lam Λ hΛ hω t hf).1
  have hSv := (Blueprint.gmpPhysicalSemigroup_energy_le hd ω lam Λ hΛ hω t hv).1
  have hleft := Blueprint.gmpPhysicalSemigroup_formLimit hd ω lam Λ hΛ hω hSf hv
  have hright := Blueprint.gmpPhysicalSemigroup_formLimit hd ω lam Λ hΛ hω hf hSv
  have he (s : ℝ≥0) :
      inner ℝ (S t f - S s (S t f)) v = inner ℝ (f - S s f) (S t v) := by
    rw [← S.add_apply, add_comm s t, S.add_apply, inner_sub_left, inner_sub_left,
      Blueprint.gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω t f v,
      Blueprint.gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω t (S s f) v]
  change Tendsto (fun s : ℝ≥0 => (s : ℝ)⁻¹ * inner ℝ (S t f - S s (S t f)) v)
    (𝓝[Set.Ioi 0] 0) (𝓝 ((Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form (S t f) v)) at hleft
  simp_rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

/-- At positive time the physical form defines a bounded L² functional. -/
theorem u1_signed_physical_positive_time_form_represented
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (t : ℝ≥0) (ht : 0 < t) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    let E := Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω
    ∃ g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      ∀ v, E.form (S t f) (S t v) = inner ℝ g v := by
  let H := Lp ℝ 2 (physicalReversibleMeasure ω hd lam)
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let E := Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  have hdom (v : H) : S t v ∈ E.domain :=
    (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr
      (u1_signed_physical_positive_time_energy hd ω lam Λ hΛ hω v t ht).1
  let L : H →ₗ[ℝ] ℝ := {
    toFun := fun v => E.form (S t f) (S t v)
    map_add' := by
      intro v w
      rw [map_add, E.form_add_right (hdom f) (hdom v) (hdom w)]
    map_smul' := by
      intro c v
      rw [map_smul, E.form_smul_right c (hdom f) (hdom v)]
      rfl }
  let C : ℝ := (t : ℝ)⁻¹ * (2 * ‖f‖)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (v : H) : ‖L v‖ ≤ C * ‖v‖ := by
    have hs := u1_signed_physical_positive_time_form_bound hd ω lam Λ hΛ hω f v t ht
    have hs' : (E.form (S t f) (S t v)) ^ 2 ≤ (C * ‖v‖) ^ 2 := by
      calc
        _ ≤ ((t : ℝ)⁻¹ * (2 * ‖f‖ * ‖f‖)) *
              ((t : ℝ)⁻¹ * (2 * ‖v‖ * ‖v‖)) := hs
        _ = _ := by dsimp [C]; ring
    have hpos : 0 ≤ C * ‖v‖ := mul_nonneg hC (norm_nonneg v)
    change |E.form (S t f) (S t v)| ≤ C * ‖v‖
    nlinarith [sq_abs (E.form (S t f) (S t v)), abs_nonneg (E.form (S t f) (S t v))]
  let ℓ : StrongDual ℝ H := L.mkContinuous C hbound
  let g : H := (InnerProductSpace.toDual ℝ H).symm ℓ
  refine ⟨g, fun v => ?_⟩
  have he := (InnerProductSpace.toDual ℝ H).apply_symm_apply ℓ
  have hv := congrArg (fun q : StrongDual ℝ H => q v) he
  change inner ℝ g v = E.form (S t f) (S t v) at hv
  exact hv.symm

/-- Every positive-time actual physical orbit lies in the generator domain. -/
theorem u1_signed_physical_positive_time_generator
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (t : ℝ≥0) (ht : 0 < t) :
    Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f ∈
      (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let E := Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  let r : ℝ≥0 := t / 2
  have hr : 0 < r := div_pos ht (by norm_num)
  have hsum : r + r = t := by ext; simp [r]
  obtain ⟨g, hg⟩ := u1_signed_physical_positive_time_form_represented
    hd ω lam Λ hΛ hω f r hr
  have hf := (u1_signed_physical_positive_time_energy hd ω lam Λ hΛ hω f t ht).1
  have hhalf := (u1_signed_physical_positive_time_energy hd ω lam Λ hΛ hω f r hr).1
  have hex : ∃ h : S t f ∈ S.generatorDomain, S.generator ⟨S t f, h⟩ = -g := by
    apply (Blueprint.gmpPhysicalSemigroup_generator_iff hd ω lam Λ hΛ hω _ _).mpr
    refine ⟨hf, ?_⟩
    intro v hv
    have hv' := (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω v).mp hv
    have h := u1_signed_physical_form_semigroup_intertwine_full
      hd ω lam Λ hΛ hω (S r f) v hhalf hv' r
    change E.form (S r (S r f)) v = E.form (S r f) (S r v) at h
    rw [← S.add_apply, hsum, hg v] at h
    rw [inner_neg_left, h]
    ring
  exact hex.choose



/-- Quantitative signed physical generator-orbit decay with gauge L¹ data. -/
theorem u1_signed_physical_generator_decay
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    ∃ C : ℝ, 0 < C ∧ ∀ (f : S.generatorDomain)
      (hf : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
        (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x) volume)
      (t : ℝ≥0) (F : ℝ), 0 < t → 0 < F →
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
        (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
          (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x|) ≤ F →
      ‖S t f‖ ^ 2 ≤ Real.exp ((lam ^ 2 / Λ) * (t : ℝ)) *
        ((1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))))) *
          (t : ℝ)) ^ (-(d : ℝ) / 2) := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  obtain ⟨C, hC, hN⟩ := u1_signed_physical_generator_nash_differential hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, hC, ?_⟩
  intro f hf t F ht hF hfF
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hΛp : 0 < Λ := by linarith
  let K : ℝ := C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  let c : ℝ := 1 / ((d : ℝ) * Λ * K)
  have hc : 0 < c := by dsimp [c]; positivity
  let u : ℝ → ℝ := fun s => ‖S (Real.toNNReal s) f‖ ^ 2
  let v : ℝ → ℝ := fun s => 2 * inner ℝ (S (Real.toNNReal s) (S.generator f))
    (S (Real.toNNReal s) f)
  by_cases hut : u t = 0
  · have heq : ‖S t f‖ ^ 2 = 0 := by simpa [u] using hut
    rw [heq]
    positivity
  have hutP : 0 < u t := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hut)
  have huA : Antitone u := by
    intro a b hab
    exact pow_le_pow_left₀ (norm_nonneg _)
      (SubdiffusiveProcess.Nash.orbit_norm_antitone S f (Real.toNNReal_mono hab)) 2
  have hpos (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) : 0 < u s := hutP.trans_le (huA hs.2)
  have hineq (s : ℝ) (hs : s ∈ Ioo 0 (t : ℝ)) :
      v s ≤ -(((d : ℝ) / 2) * c) * u s ^ (1 + 1 / ((d : ℝ) / 2)) +
        (lam ^ 2 / Λ) * u s := by
    have hs0 : (0 : ℝ≥0) < Real.toNNReal s := Real.toNNReal_pos.mpr hs.1
    have hst : Real.toNNReal s ≤ t := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hs.2.le
    have hn := hN f hf t F hF hfF (Real.toNNReal s) hs0 hst
    have hex : 1 + 1 / ((d : ℝ) / 2) = 1 + 2 / (d : ℝ) := by field_simp
    rw [hex]
    change v s ≤ -(2 / (4 * Λ * K)) * u s ^ (1 + 2 / (d : ℝ)) +
      (lam ^ 2 / Λ) * u s at hn
    convert hn using 1
    dsimp [c]
    field_simp [ne_of_gt hdR, ne_of_gt hΛp, ne_of_gt hK] <;> ring
  have hdec := u1_nash_decay_with_linear_term u v ((d : ℝ) / 2) c (lam ^ 2 / Λ) t
    (by positivity) hc (by positivity) ht
    (((S.continuous_operator_toNNReal f).norm.pow 2).continuousOn) hpos
    (fun s hs => SubdiffusiveProcess.Nash.hasDerivAt_orbit_norm_sq S f hs.1) hineq
  simpa only [u, c, K, S, Real.toNNReal_coe, neg_div] using hdec

/-- Signed gauge Nash decay for arbitrary physical L² data, after a half-time shift. -/
theorem u1_signed_physical_L1_L2_decay
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧
      ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
        (hf : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume)
        (t : ℝ≥0) (F : ℝ), 0 < t → 0 < F →
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * ((t / 2 : ℝ≥0) : ℝ)) *
        ((Real.exp (2 * Λ)) ^ 2 * Real.exp (B * ((t / 2 : ℝ≥0) : ℝ)) *
          (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|)) ≤ F →
      ‖S t f‖ ^ 2 ≤ Real.exp ((lam ^ 2 / Λ) * ((t / 2 : ℝ≥0) : ℝ)) *
        ((1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))))) *
          ((t / 2 : ℝ≥0) : ℝ)) ^ (-(d : ℝ) / 2) := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  obtain ⟨C, hC, hdec⟩ := u1_signed_physical_generator_decay hd ω lam Λ hΛ hω hSmooth
  obtain ⟨B, hB, hb⟩ := u1_signed_physical_semigroup_gauge_L1_interval hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hf t F ht hF hfF
  let r : ℝ≥0 := t / 2
  have hr : 0 < r := div_pos ht (by norm_num)
  have hsum : r + r = t := by ext; simp [r]
  let g : S.generatorDomain := ⟨S r f,
    u1_signed_physical_positive_time_generator hd ω lam Λ hΛ hω f r hr⟩
  have hg := hb f hf r r le_rfl
  have hmass : (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (r : ℝ)) *
      (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
        (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x|) ≤ F := by
    calc
      _ ≤ (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (r : ℝ)) *
          ((Real.exp (2 * Λ)) ^ 2 * Real.exp (B * (r : ℝ)) *
            (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|)) :=
        mul_le_mul_of_nonneg_left hg.2 (by positivity)
      _ ≤ F := hfF
  have h := hdec g hg.1 r F hr hF hmass
  change ‖S r (S r f)‖ ^ 2 ≤ _ at h
  rw [← S.add_apply, hsum] at h
  exact h

/-- At every positive time, signed physical evolution maps gauge L¹ data to L². -/
theorem u1_signed_physical_gauge_L1_to_L2
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
      ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f‖ ≤
        M * ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x| := by
  obtain ⟨C, B, hC, hB, hdec⟩ := u1_signed_physical_L1_L2_decay hd ω lam Λ hΛ hω hSmooth
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hΛp : 0 < Λ := by linarith
  let r : ℝ := ((t / 2 : ℝ≥0) : ℝ)
  have hr : 0 < r := by dsimp [r]; exact_mod_cast (div_pos ht (by norm_num) : 0 < t / 2)
  let A : ℝ := (1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ)))) * r
  let D : ℝ := Real.exp ((lam ^ 2 / Λ) * r)
  let K : ℝ := (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * r) *
    ((Real.exp (2 * Λ)) ^ 2 * Real.exp (B * r))
  let L : ℝ := Real.sqrt D * A ^ (-(d : ℝ) / 4)
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L * K, mul_pos hL hK, ?_⟩
  intro f hf
  let m : ℝ := ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|
  have hm : 0 ≤ m := integral_nonneg fun _ => abs_nonneg _
  apply le_of_forall_pos_le_add
  intro ε hε
  let F : ℝ := K * m + ε / L
  have hF : 0 < F := by dsimp [F]; positivity
  have hmass : (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * r) *
      ((Real.exp (2 * Λ)) ^ 2 * Real.exp (B * r) * m) ≤ F := by
    dsimp [F, K]
    nlinarith [div_pos hε hL]
  have hb := hdec f hf t F ht hF hmass
  have hp : -(4 / (d : ℝ)) * (-(d : ℝ) / 2) = (2 : ℝ) := by field_simp; ring
  have he : (1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))))) * r =
      A * F ^ (-(4 / (d : ℝ))) := by
    rw [Real.rpow_neg hF.le]
    dsimp [A]
    ring
  change ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f‖ ^ 2 ≤
    D * ((1 / ((d : ℝ) * Λ * (C * Real.exp (2 * Λ) * F ^ (4 / (d : ℝ))))) * r) ^
      (-(d : ℝ) / 2) at hb
  rw [he, Real.mul_rpow hA.le (Real.rpow_nonneg hF.le _),
    ← Real.rpow_mul hF.le, hp, Real.rpow_two] at hb
  have hp2 : (-(d : ℝ) / 4) * 2 = -(d : ℝ) / 2 := by ring
  have hsq : (L * F) ^ 2 = D * A ^ (-(d : ℝ) / 2) * F ^ 2 := by
    dsimp [L]
    rw [mul_pow, mul_pow, Real.sq_sqrt hD.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hA.le]
    norm_num only [Nat.cast_ofNat]
    rw [hp2]
  have hn : ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f‖ ≤ L * F := by
    rw [← mul_assoc, ← hsq] at hb
    nlinarith [norm_nonneg (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f),
      mul_nonneg hL.le hF.le]
  calc
    _ ≤ L * F := hn
    _ = (L * K) * m + ε := by dsimp [F]; field_simp

/-- The signed gauge L¹-to-L² bound applies to concrete measurable representatives. -/
theorem u1_signed_physical_gauge_L1_to_L2_fun
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (g : EinsteinRelation.Vec d → ℝ)
      (hg : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * g x) volume)
      (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd lam)),
      ‖Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hg2.toLp g)‖ ≤
        M * ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * g x| := by
  obtain ⟨M, hM, hbound⟩ := u1_signed_physical_gauge_L1_to_L2 hd ω lam Λ hΛ hω hSmooth t ht
  refine ⟨M, hM, ?_⟩
  intro g hg hg2
  have he := u1_signed_physical_ae_to_volume hd ω lam hg2.coeFn_toLp
  have hi : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
      (hg2.toLp g) x) volume := hg.congr (by
        filter_upwards [he] with x hx
        rw [hx])
  have h := hbound (hg2.toLp g) hi
  convert h using 1
  apply congrArg (fun a : ℝ => M * a)
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

/-- The signed gauge evolution is L¹-to-L² bounded in Lebesgue measure. -/
theorem u1_signed_physical_gauge_L1_to_L2_volume
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
      (∫ x, (Real.exp (lam * x (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f x) ^ 2) ≤
        M * (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := u1_signed_physical_gauge_L1_to_L2 hd ω lam Λ hΛ hω hSmooth t ht
  refine ⟨Real.exp (2 * Λ) * C ^ 2, by positivity, ?_⟩
  intro f hf
  let μ := physicalReversibleMeasure ω hd lam
  let ν := physicalForceMeasure (firstCoordinateIndex hd) lam
  let u : Lp ℝ 2 μ := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f
  have hi : Integrable (fun x => u x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Lp.memLp u).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hcomp : (∫ x, u x ^ 2 ∂ν) ≤ Real.exp (2 * Λ) * (∫ x, u x ^ 2 ∂μ) :=
    integral_le_const_mul_of_measure_le ν μ (Real.exp (2 * Λ)) (Real.exp_pos _).le
      (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).2
      (fun x => u x ^ 2) (Filter.Eventually.of_forall fun x => sq_nonneg _) hi
  have hnorm : (∫ x, u x ^ 2 ∂μ) = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hm : 0 ≤ ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x| :=
    integral_nonneg fun _ => abs_nonneg _
  have hb : ‖u‖ ^ 2 ≤ (C * ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hbound f hf) 2
  rw [u1_signed_gauge_mass_integral_identity]
  change (∫ x, u x ^ 2 ∂ν) ≤ _
  calc
    _ ≤ Real.exp (2 * Λ) * (∫ x, u x ^ 2 ∂μ) := hcomp
    _ ≤ Real.exp (2 * Λ) * (C * ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|) ^ 2 := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

/-- The signed semigroup has a two-sided gauge L¹ pairing bound. -/
theorem u1_signed_physical_gauge_L1_pairing_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * g x) volume →
      |inner ℝ (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f) g| ≤
        M * (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|) *
          (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * g x|) := by
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨C, hC, hbound⟩ :=
    u1_signed_physical_gauge_L1_to_L2 hd ω lam Λ hΛ hω hSmooth (t / 2) ht2
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro f g hf hg
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  have heq : inner ℝ (S t f) g = inner ℝ (S (t / 2) f) (S (t / 2) g) := by
    rw [show S t f = S (t / 2) (S (t / 2) f) by
      simpa only [add_halves] using S.add_apply (t / 2) (t / 2) f]
    exact Blueprint.gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω (t / 2) _ _
  rw [heq]
  calc
    _ ≤ ‖S (t / 2) f‖ * ‖S (t / 2) g‖ := abs_real_inner_le_norm _ _
    _ ≤ (C * ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|) *
        (C * ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * g x|) :=
      mul_le_mul (hbound f hf) (hbound g hg) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The actual signed transition kernel satisfies the two-sided gauge pairing bound. -/
theorem u1_signed_kernel_gauge_L1_pairing_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f g : EinsteinRelation.Vec d → ℝ)
      (hf2 : MemLp f 2 (physicalReversibleMeasure ω hd lam))
      (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * g x) volume →
      |∫ x, (∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
          hd ω lam Λ hΛ hω hSmooth t x) * g x ∂physicalReversibleMeasure ω hd lam| ≤
        M * (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x|) *
          (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * g x|) := by
  obtain ⟨M, hM, hbound⟩ :=
    u1_signed_physical_gauge_L1_pairing_bound hd ω lam Λ hΛ hω hSmooth t ht
  refine ⟨M, hM, ?_⟩
  intro f g hf2 hg2 hf hg
  have hfvol := u1_signed_physical_ae_to_volume hd ω lam hf2.coeFn_toLp
  have hgvol := u1_signed_physical_ae_to_volume hd ω lam hg2.coeFn_toLp
  have hfi : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
      (hf2.toLp f) x) volume := hf.congr (by filter_upwards [hfvol] with x hx; rw [hx])
  have hgi : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
      (hg2.toLp g) x) volume := hg.congr (by filter_upwards [hgvol] with x hx; rw [hx])
  have hb := hbound (hf2.toLp f) (hg2.toLp g) hfi hgi
  have hmassf : (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * (hf2.toLp f) x|) =
      ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x| := by
    apply integral_congr_ae
    filter_upwards [hfvol] with x hx
    rw [hx]
  have hmassg : (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * (hg2.toLp g) x|) =
      ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * g x| := by
    apply integral_congr_ae
    filter_upwards [hgvol] with x hx
    rw [hx]
  rw [hmassf, hmassg] at hb
  convert hb using 1
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2
    hd ω lam Λ hΛ hω hSmooth t f hf2).2, hg2.coeFn_toLp] with x hx hy
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hy]
  ring

/-- Bounded set tests satisfy the actual kernel's two-sided gauge estimate. -/
theorem u1_signed_kernel_bounded_sets_gauge_pairing
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (A B : Set (EinsteinRelation.Vec d)),
      MeasurableSet A → Bornology.IsBounded A →
      MeasurableSet B → Bornology.IsBounded B →
      (∫ x in B, (Blueprint.gmpPhysicalC0KernelSemigroup
        hd ω lam Λ hΛ hω hSmooth t x A).toReal ∂physicalReversibleMeasure ω hd lam) ≤
        M * (∫ x in A, Real.exp (lam * x (firstCoordinateIndex hd))) *
          (∫ x in B, Real.exp (lam * x (firstCoordinateIndex hd))) := by
  obtain ⟨M, hM, hbound⟩ :=
    u1_signed_kernel_gauge_L1_pairing_bound hd ω lam Λ hΛ hω hSmooth t ht
  refine ⟨M, hM, ?_⟩
  intro A B hA hAb hB hBb
  let w : EinsteinRelation.Vec d → ℝ := fun x => Real.exp (lam * x (firstCoordinateIndex hd))
  have hw : Continuous w := Real.continuous_exp.comp (continuous_const.mul
    (continuous_apply (firstCoordinateIndex hd)))
  have hwA : IntegrableOn w A volume :=
    (hw.continuousOn.integrableOn_compact hAb.isCompact_closure).mono_set subset_closure
  have hwB : IntegrableOn w B volume :=
    (hw.continuousOn.integrableOn_compact hBb.isCompact_closure).mono_set subset_closure
  have he (S : Set (EinsteinRelation.Vec d)) :
      (fun x => w x * S.indicator (fun _ => (1 : ℝ)) x) = S.indicator w := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  have hA1 : Integrable (fun x => w x * A.indicator (fun _ => (1 : ℝ)) x) volume := by
    rw [he]
    exact hwA.integrable_indicator hA
  have hB1 : Integrable (fun x => w x * B.indicator (fun _ => (1 : ℝ)) x) volume := by
    rw [he]
    exact hwB.integrable_indicator hB
  have hb := hbound _ _ (u1_signed_physical_bounded_indicator_memLp hd ω lam A hA hAb)
    (u1_signed_physical_bounded_indicator_memLp hd ω lam B hB hBb) hA1 hB1
  have habs (S : Set (EinsteinRelation.Vec d)) (hS : MeasurableSet S) :
      (∫ x, |w x * S.indicator (fun _ => (1 : ℝ)) x|) = ∫ x in S, w x := by
    have hfun : (fun x => |w x * S.indicator (fun _ => (1 : ℝ)) x|) = S.indicator w := by
      funext x
      by_cases hx : x ∈ S <;> simp [hx, w, (Real.exp_pos _).le]
    rw [hfun, integral_indicator hS]
  rw [habs A hA, habs B hB] at hb
  have hlhs : (∫ x, (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂
        Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) *
        B.indicator (fun _ => (1 : ℝ)) x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in B, (Blueprint.gmpPhysicalC0KernelSemigroup
        hd ω lam Λ hΛ hω hSmooth t x A).toReal ∂physicalReversibleMeasure ω hd lam := by
    have heq : (fun x => (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂
        Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) *
        B.indicator (fun _ => (1 : ℝ)) x) =
        B.indicator (fun x => (Blueprint.gmpPhysicalC0KernelSemigroup
          hd ω lam Λ hΛ hω hSmooth t x A).toReal) := by
      funext x
      by_cases hx : x ∈ B <;>
        simp [hx, integral_indicator hA, Measure.real]
    rw [heq, integral_indicator hB]
  rw [hlhs] at hb
  exact (le_abs_self _).trans hb

/-- On a bounded set, an upper coordinate bound controls its gauge mass. -/
theorem u1_signed_gauge_set_integral_le {d : ℕ} (hd : 2 ≤ d) (lam a : ℝ)
    (A : Set (EinsteinRelation.Vec d)) (hA : MeasurableSet A)
    (hAb : Bornology.IsBounded A)
    (ha : ∀ x ∈ A, lam * x (firstCoordinateIndex hd) ≤ a) :
    (∫ x in A, Real.exp (lam * x (firstCoordinateIndex hd))) ≤
      Real.exp a * (volume A).toReal := by
  have hc : Continuous (fun x : EinsteinRelation.Vec d =>
      Real.exp (lam * x (firstCoordinateIndex hd))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_apply (firstCoordinateIndex hd)))
  have hi : IntegrableOn (fun x : EinsteinRelation.Vec d =>
      Real.exp (lam * x (firstCoordinateIndex hd))) A volume :=
    (hc.continuousOn.integrableOn_compact hAb.isCompact_closure).mono_set subset_closure
  have hm : volume A ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono subset_closure) hAb.isCompact_closure.measure_lt_top).ne
  have hb := integral_mono_ae hi (integrableOn_const (C := Real.exp a) hm) (by
    filter_upwards [ae_restrict_mem hA] with x hx
    exact Real.exp_le_exp.mpr (ha x hx))
  simpa [Measure.real, mul_comm] using hb

/-- On a coordinate lower slab, the force measure dominates a constant multiple
of Lebesgue measure. -/
theorem u1_signed_force_measure_slab_lower {d : ℕ} (hd : 2 ≤ d)
    (lam r : ℝ) (B : Set (EinsteinRelation.Vec d)) (hB : MeasurableSet B)
    (hr : ∀ x ∈ B, r ≤ lam * x (firstCoordinateIndex hd)) :
    ENNReal.ofReal (Real.exp (2 * r)) • volume.restrict B ≤
      (physicalForceMeasure (firstCoordinateIndex hd) lam).restrict B := by
  rw [physicalForceMeasure, restrict_withDensity hB,
    ← withDensity_const]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem hB] with x hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  nlinarith [hr x hx]

#print axioms u1_signed_force_measure_slab_lower

/-- On a coordinate lower slab, Lebesgue measure is dominated by the actual
physical reversible measure with an explicit location-dependent constant. -/
theorem u1_signed_physical_measure_slab_comparison {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ r : ℝ) (hω : IsRegular Λ ω)
    (B : Set (EinsteinRelation.Vec d)) (hB : MeasurableSet B)
    (hr : ∀ x ∈ B, r ≤ lam * x (firstCoordinateIndex hd)) :
    volume.restrict B ≤ ENNReal.ofReal (Real.exp (2 * Λ - 2 * r)) •
      (physicalReversibleMeasure ω hd lam).restrict B := by
  have hforce : (physicalForceMeasure (firstCoordinateIndex hd) lam).restrict B ≤
      ENNReal.ofReal (Real.exp (2 * Λ)) •
        (physicalReversibleMeasure ω hd lam).restrict B := by
    simpa only [Measure.restrict_smul] using
      Measure.restrict_mono (Set.Subset.rfl : B ⊆ B)
        (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).2
  have h := (u1_signed_force_measure_slab_lower hd lam r B hB hr).trans hforce
  have hs : ENNReal.ofReal (Real.exp (-2 * r)) •
      (ENNReal.ofReal (Real.exp (2 * r)) • volume.restrict B) ≤
      ENNReal.ofReal (Real.exp (-2 * r)) •
        (ENNReal.ofReal (Real.exp (2 * Λ)) •
          (physicalReversibleMeasure ω hd lam).restrict B) := by
    gcongr
  simp only [smul_smul, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← Real.exp_add] at hs
  have he : -2 * r + 2 * r = 0 := by ring
  have he' : -(2 * r) + 2 * Λ = 2 * Λ - 2 * r := by ring
  simpa [he, he'] using hs

#print axioms u1_signed_physical_measure_slab_comparison

/-- The actual kernel's local set pairing has explicit exponential coordinate bounds. -/
theorem u1_signed_kernel_bounded_sets_coordinate_pairing
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (A B : Set (EinsteinRelation.Vec d)) (a b : ℝ),
      MeasurableSet A → Bornology.IsBounded A →
      MeasurableSet B → Bornology.IsBounded B →
      (∀ x ∈ A, lam * x (firstCoordinateIndex hd) ≤ a) →
      (∀ x ∈ B, lam * x (firstCoordinateIndex hd) ≤ b) →
      (∫ x in B, (Blueprint.gmpPhysicalC0KernelSemigroup
        hd ω lam Λ hΛ hω hSmooth t x A).toReal ∂physicalReversibleMeasure ω hd lam) ≤
        M * Real.exp (a + b) * (volume A).toReal * (volume B).toReal := by
  obtain ⟨M, hM, hbound⟩ :=
    u1_signed_kernel_bounded_sets_gauge_pairing hd ω lam Λ hΛ hω hSmooth t ht
  refine ⟨M, hM, ?_⟩
  intro A B a b hA hAb hB hBb ha hb
  have hAint := u1_signed_gauge_set_integral_le hd lam a A hA hAb ha
  have hBint := u1_signed_gauge_set_integral_le hd lam b B hB hBb hb
  have hnA : 0 ≤ ∫ x in A, Real.exp (lam * x (firstCoordinateIndex hd)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hnB : 0 ≤ ∫ x in B, Real.exp (lam * x (firstCoordinateIndex hd)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  calc
    _ ≤ M * (∫ x in A, Real.exp (lam * x (firstCoordinateIndex hd))) *
        (∫ x in B, Real.exp (lam * x (firstCoordinateIndex hd))) :=
      hbound A B hA hAb hB hBb
    _ ≤ M * (Real.exp a * (volume A).toReal) * (Real.exp b * (volume B).toReal) := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring

/-- The signed kernel has a Lebesgue set-pairing estimate on coordinate slabs.
The exponent records the separation of the two sets in the force direction. -/
theorem u1_signed_kernel_volume_slab_pairing
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (A B : Set (EinsteinRelation.Vec d)) (a b r : ℝ),
      MeasurableSet A → Bornology.IsBounded A →
      MeasurableSet B → Bornology.IsBounded B →
      (∀ x ∈ A, lam * x (firstCoordinateIndex hd) ≤ a) →
      (∀ x ∈ B, lam * x (firstCoordinateIndex hd) ≤ b) →
      (∀ x ∈ B, r ≤ lam * x (firstCoordinateIndex hd)) →
      (∫ x in B, (Blueprint.gmpPhysicalC0KernelSemigroup
        hd ω lam Λ hΛ hω hSmooth t x A).toReal) ≤
        M * Real.exp (2 * Λ - 2 * r + a + b) *
          (volume A).toReal * (volume B).toReal := by
  obtain ⟨M, hM, hbound⟩ :=
    u1_signed_kernel_bounded_sets_coordinate_pairing hd ω lam Λ hΛ hω hSmooth t ht
  refine ⟨M, hM, ?_⟩
  intro A B a b r hA hAb hB hBb ha hb hr
  let μ := physicalReversibleMeasure ω hd lam
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  letI : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  letI : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono subset_closure) hBb.isCompact_closure.measure_lt_top).ne
  have hp (x : EinsteinRelation.Vec d) : (K x A).toReal ≤ 1 := by
    letI : IsProbabilityMeasure (K x) :=
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
    have h := ENNReal.toReal_mono (measure_ne_top (K x) Set.univ)
      (measure_mono (Set.subset_univ A))
    simpa using h
  have hi : Integrable (fun x => (K x A).toReal) (μ.restrict B) := by
    apply (integrable_const (1 : ℝ)).mono'
      (K.measurable_coe hA).ennreal_toReal.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hp x
  have hc := integral_le_const_mul_of_measure_le (volume.restrict B) (μ.restrict B)
    (Real.exp (2 * Λ - 2 * r)) (Real.exp_pos _).le
    (u1_signed_physical_measure_slab_comparison hd ω lam Λ r hω B hB hr)
    (fun x => (K x A).toReal) (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hi
  calc
    _ ≤ Real.exp (2 * Λ - 2 * r) * ∫ x in B, (K x A).toReal ∂μ := hc
    _ ≤ Real.exp (2 * Λ - 2 * r) *
        (M * Real.exp (a + b) * (volume A).toReal * (volume B).toReal) := by
      gcongr
      exact hbound A B a b hA hAb hB hBb ha hb
    _ = _ := by
      have he : Real.exp (2 * Λ - 2 * r) * Real.exp (a + b) =
          Real.exp (2 * Λ - 2 * r + a + b) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← he]
      ring

#print axioms u1_signed_kernel_volume_slab_pairing

/-- A common upper slab gives a location-independent Lebesgue pairing bound.
The first set may extend arbitrarily far below the lower edge of the slab. -/
theorem u1_signed_kernel_volume_one_sided_slab_pairing
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) (R : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (A B : Set (EinsteinRelation.Vec d)) (r : ℝ),
      MeasurableSet A → Bornology.IsBounded A →
      MeasurableSet B → Bornology.IsBounded B →
      (∀ x ∈ A, lam * x (firstCoordinateIndex hd) ≤ r + R) →
      (∀ x ∈ B, r ≤ lam * x (firstCoordinateIndex hd) ∧
        lam * x (firstCoordinateIndex hd) ≤ r + R) →
      (∫ x in B, (Blueprint.gmpPhysicalC0KernelSemigroup
        hd ω lam Λ hΛ hω hSmooth t x A).toReal) ≤
        M * (volume A).toReal * (volume B).toReal := by
  obtain ⟨M, hM, hbound⟩ :=
    u1_signed_kernel_volume_slab_pairing hd ω lam Λ hΛ hω hSmooth t ht
  refine ⟨M * Real.exp (2 * Λ + 2 * R), by positivity, ?_⟩
  intro A B r hA hAb hB hBb ha hb
  have h := hbound A B (r + R) (r + R) r hA hAb hB hBb ha
    (fun x hx => (hb x hx).2) (fun x hx => (hb x hx).1)
  have he : 2 * Λ - 2 * r + (r + R) + (r + R) = 2 * Λ + 2 * R := by ring
  rw [he] at h
  exact h

#print axioms u1_signed_kernel_volume_one_sided_slab_pairing

/-- Exponential moments give an off-diagonal Lebesgue mass bound for
coordinate-separated sets. -/
theorem u1_signed_kernel_weighted_set_separation
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (A B : Set (EinsteinRelation.Vec d)) (a b : ℝ),
      MeasurableSet A → MeasurableSet B →
      (∀ x ∈ A, q * x (firstCoordinateIndex hd) ≤ a) →
      (∀ x ∈ B, b ≤ q * x (firstCoordinateIndex hd)) →
      (∫⁻ x in B, Blueprint.gmpPhysicalC0KernelSemigroup
        hd ω lam Λ hΛ hω hSmooth t x A) ≤
      ENNReal.ofReal (Real.exp (-b)) *
        ((ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
          ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
          (ENNReal.ofReal (Real.exp a) * volume A)) := by
  obtain ⟨C, hC, hb⟩ := u1_signed_physical_kernel_weight_lintegral_le
    hd ω lam Λ hΛ hω hSmooth q
  refine ⟨C, hC, ?_⟩
  intro t A B a b hA hB ha hbB
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  let w : EinsteinRelation.Vec d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (q * x (firstCoordinateIndex hd)))
  let f : EinsteinRelation.Vec d → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hw : Measurable w := (ENNReal.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_apply (firstCoordinateIndex hd))))).measurable
  have hf : Measurable f := measurable_one.indicator hA
  have hk (x : EinsteinRelation.Vec d) : (∫⁻ y, f y ∂K x) = K x A := by
    exact lintegral_indicator_one hA
  have hi : (∫⁻ x, w x * f x) ≤ ENNReal.ofReal (Real.exp a) * volume A := by
    calc
      _ = ∫⁻ x in A, w x := by
        rw [← lintegral_indicator hA]
        apply lintegral_congr
        intro x
        by_cases hx : x ∈ A <;> simp [f, hx]
      _ ≤ ∫⁻ _ in A, ENNReal.ofReal (Real.exp a) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hA] with x hx
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (ha x hx))
      _ = _ := by simp
  have hmass : (∫⁻ x, w x * K x A) ≤
      (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
          (ENNReal.ofReal (Real.exp a) * volume A) := by
    have h := hb t f hf
    change (∫⁻ x, w x * (∫⁻ y, f y ∂K x)) ≤ _ at h
    simp_rw [hk] at h
    apply h.trans
    gcongr
  calc
    _ ≤ ∫⁻ x in B, ENNReal.ofReal (Real.exp (-b)) * (w x * K x A) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with x hx
      have hwge : 1 ≤ ENNReal.ofReal (Real.exp (-b)) * w x := by
        dsimp [w]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        have hp : 0 ≤ -b + q * x (firstCoordinateIndex hd) := by linarith [hbB x hx]
        simpa only [Real.exp_zero, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hp)
      simpa only [one_mul, mul_assoc] using mul_le_mul_left hwge (K x A)
    _ = ENNReal.ofReal (Real.exp (-b)) * (∫⁻ x in B, w x * K x A) :=
      lintegral_const_mul _ (hw.mul (ProbabilityTheory.Kernel.measurable_coe K hA))
    _ ≤ ENNReal.ofReal (Real.exp (-b)) * (∫⁻ x, w x * K x A) := by
      gcongr
      exact Measure.restrict_le_self
    _ ≤ _ := by gcongr

#print axioms u1_signed_kernel_weighted_set_separation

/-- The gauge-conjugated physical kernel has a Lebesgue L¹ pairing bound. -/
theorem u1_signed_conjugated_kernel_L1_pairing_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f g : EinsteinRelation.Vec d → ℝ),
      Integrable f volume → Integrable g volume →
      MemLp (fun x => Real.exp (-lam * x (firstCoordinateIndex hd)) * f x) 2
        (physicalReversibleMeasure ω hd lam) →
      MemLp (fun x => Real.exp (-lam * x (firstCoordinateIndex hd)) * g x) 2
        (physicalReversibleMeasure ω hd lam) →
      |∫ x, (∫ y, Real.exp (-lam * y (firstCoordinateIndex hd)) * f y ∂
          Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) *
          (Real.exp (-lam * x (firstCoordinateIndex hd)) * g x)
          ∂physicalReversibleMeasure ω hd lam| ≤
        M * (∫ x, |f x|) * (∫ x, |g x|) := by
  obtain ⟨M, hM, hbound⟩ :=
    u1_signed_kernel_gauge_L1_pairing_bound hd ω lam Λ hΛ hω hSmooth t ht
  refine ⟨M, hM, ?_⟩
  intro f g hf hg hf2 hg2
  have hcancel (x : EinsteinRelation.Vec d) (v : ℝ) :
      Real.exp (lam * x (firstCoordinateIndex hd)) *
        (Real.exp (-lam * x (firstCoordinateIndex hd)) * v) = v := by
    rw [← mul_assoc, ← Real.exp_add]
    have he : lam * x (firstCoordinateIndex hd) + -lam * x (firstCoordinateIndex hd) = 0 := by ring
    rw [he, Real.exp_zero, one_mul]
  have hfi : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
      (Real.exp (-lam * x (firstCoordinateIndex hd)) * f x)) volume := by
    simpa only [hcancel] using hf
  have hgi : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
      (Real.exp (-lam * x (firstCoordinateIndex hd)) * g x)) volume := by
    simpa only [hcancel] using hg
  simpa only [hcancel] using hbound _ _ hf2 hg2 hfi hgi

/-- The signed physical semigroup contracts the weighted L¹ norm. -/
theorem u1_signed_physical_L1_contraction
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (g : EinsteinRelation.Vec d → ℝ) (hg1 : Integrable g (physicalReversibleMeasure ω hd lam))
    (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd lam)) :
    Integrable (fun x => Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
      (hg2.toLp g) x) (physicalReversibleMeasure ω hd lam) ∧
    (∫ x, |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hg2.toLp g) x|
      ∂physicalReversibleMeasure ω hd lam) ≤
      ∫ x, |g x| ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
  let F := hg2.toLp g
  have hga : MemLp (fun x => |g x|) 2 μ := hg2.abs
  have heq : hga.toLp (fun x => |g x|) = |F| := by
    apply Lp.ext
    filter_upwards [hga.coeFn_toLp, Lp.coeFn_abs F, hg2.coeFn_toLp] with x ha hb hc
    change F x = g x at hc
    rw [ha, hb, hc]
  have hpositive := u7_physical_positive_L1_contraction hd ω lam Λ hΛ hω t
    (fun x => |g x|) hg1.abs hga (Filter.Eventually.of_forall fun x => abs_nonneg _)
  rw [heq] at hpositive
  have hdom : ∀ᵐ x ∂μ, |(P F) x| ≤ (P |F|) x := by
    have h := (Lp.coeFn_le _ _).mpr (u7_physical_semigroup_abs_le hd ω lam Λ hΛ hω t F)
    filter_upwards [h, Lp.coeFn_abs (P F)] with x hx he
    change (|P F|) x ≤ (P |F|) x at hx
    simpa only [he] using hx
  have hInt : Integrable (P F) μ := hpositive.1.mono' (Lp.aestronglyMeasurable _)
    (by filter_upwards [hdom] with x hx; simpa only [Real.norm_eq_abs] using hx)
  refine ⟨hInt, ?_⟩
  exact (integral_mono_ae hInt.abs hpositive.1 hdom).trans hpositive.2



/-- Signed dyadic kernel outputs are integrable in the actual reversible
measure, with mass at most the reversible measure of the input cube. -/
theorem u1_signed_dyadic_output_L1_contraction {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ) :
    Integrable (u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k)
      (physicalReversibleMeasure ω hd lam) ∧
    (∫ x, u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k x
      ∂physicalReversibleMeasure ω hd lam) ≤
        (physicalReversibleMeasure ω hd lam (cube n k)).toReal := by
  let μ := physicalReversibleMeasure ω hd lam
  let f : EinsteinRelation.Vec d → ℝ := (cube n k).indicator (fun _ => 1)
  have hf2 : MemLp f 2 μ := u1_signed_physical_dyadic_indicator_memLp hd ω lam n k
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hc : IsCompact (Set.pi Set.univ fun i : Fin d =>
      Set.Icc ((k i : ℝ) / 2 ^ n) (((k i : ℝ) + 1) / 2 ^ n)) := by
    simpa only [← Set.mem_univ_pi] using!
      (isCompact_pi_infinite (fun i : Fin d =>
        isCompact_Icc (a := (k i : ℝ) / 2 ^ n) (b := ((k i : ℝ) + 1) / 2 ^ n)))
  have hsub : cube n k ⊆ Set.pi Set.univ (fun i : Fin d =>
      Set.Icc ((k i : ℝ) / 2 ^ n) (((k i : ℝ) + 1) / 2 ^ n)) := by
    intro y hy
    simp only [cube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
      Set.mem_Icc] at hy ⊢
    exact fun i => ⟨(hy i).1, (hy i).2.le⟩
  have hfinite : μ (cube n k) ≠ ∞ := (lt_of_le_of_lt (measure_mono hsub) hc.measure_lt_top).ne
  have hf1 : Integrable f μ := memLp_one_iff_integrable.mp
    (memLp_indicator_const 1 (measurableSet_cube n k) (1 : ℝ) (Or.inr hfinite))
  have h := u1_signed_physical_L1_contraction hd ω lam Λ hΛ hω t f hf1 hf2
  have heq : u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k =ᵐ[μ]
      (fun x => Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x) :=
    (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2 hd ω lam Λ hΛ hω hSmooth t f hf2).2
  have hInt := h.1.congr heq.symm
  refine ⟨hInt, ?_⟩
  have hnonneg : ∀ x, 0 ≤ f x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have habs : (fun x => |f x|) = f := funext fun x => abs_of_nonneg (hnonneg x)
  have houtput : ∀ x, 0 ≤ u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k x :=
    u1_signedPhysicalDyadicOutput_nonneg hd ω lam Λ hΛ hω hSmooth t n k
  calc
    _ = ∫ x, |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf2.toLp f) x| ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [← hx, abs_of_nonneg (houtput x)]
    _ ≤ ∫ x, |f x| ∂μ := h.2
    _ = (μ (cube n k)).toReal := by
      rw [habs]
      simp [f, integral_indicator (measurableSet_cube n k), Measure.real]

/-- A signed dyadic output is a probability and therefore lies in `[0, 1]`. -/
theorem u1_signed_dyadic_output_le_one {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ)
    (x : EinsteinRelation.Vec d) :
    u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k x ≤ 1 := by
  let μ := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x
  let : IsProbabilityMeasure μ := ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative
    hd ω lam Λ hΛ hω hSmooth t x⟩
  change (∫ y, (cube n k).indicator (fun _ => (1 : ℝ)) y ∂μ) ≤ 1
  have hi : Integrable ((cube n k).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_cube n k)
  have hb : ∀ y, (cube n k).indicator (fun _ => (1 : ℝ)) y ≤ 1 := by
    intro y
    by_cases hy : y ∈ cube n k <;> simp [hy]
  simpa using integral_mono hi (integrable_const (1 : ℝ)) hb

/-- The squared weighted mass of a signed dyadic output is bounded by the
weighted mass of its input cube. -/
theorem u1_signed_dyadic_output_sq_integral_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (n : ℕ) (k : Fin d → ℤ) :
    (∫ x, (u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k x) ^ 2
      ∂physicalReversibleMeasure ω hd lam) ≤
        (physicalReversibleMeasure ω hd lam (cube n k)).toReal := by
  let f := u1SignedPhysicalDyadicOutput hd ω lam Λ hΛ hω hSmooth t n k
  let μ := physicalReversibleMeasure ω hd lam
  have h := u1_signed_dyadic_output_L1_contraction hd ω lam Λ hΛ hω hSmooth t n k
  have hp : ∀ x, f x ^ 2 ≤ f x := by
    intro x
    have hn := u1_signedPhysicalDyadicOutput_nonneg hd ω lam Λ hΛ hω hSmooth t n k x
    have hu := u1_signed_dyadic_output_le_one hd ω lam Λ hΛ hω hSmooth t n k x
    change 0 ≤ f x at hn
    change f x ≤ 1 at hu
    nlinarith
  have hi : Integrable (fun x => f x ^ 2) μ := h.1.mono'
    ((u1_signedPhysicalDyadicOutput_measurable hd ω lam Λ hΛ hω hSmooth t n k).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))]
      exact hp x)
  exact (integral_mono hi h.1 hp).trans h.2

/-- Each finite dyadic window has finite mass for the signed physical measure. -/
theorem u1_signed_physical_window_finite {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (F : Finset (Fin d → ℤ)) :
    physicalReversibleMeasure ω hd lam (win F) < ∞ := by
  let μ := physicalReversibleMeasure ω hd lam
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hc (k : Fin d → ℤ) : μ (cube 0 k) < ∞ := by
    have hcompact : IsCompact (Set.pi Set.univ fun i : Fin d =>
        Set.Icc ((k i : ℝ) / 2 ^ (0 : ℕ)) (((k i : ℝ) + 1) / 2 ^ (0 : ℕ))) := by
      simpa only [← Set.mem_univ_pi] using!
        (isCompact_pi_infinite (fun i : Fin d => isCompact_Icc
          (a := (k i : ℝ) / 2 ^ (0 : ℕ)) (b := ((k i : ℝ) + 1) / 2 ^ (0 : ℕ))))
    apply lt_of_le_of_lt (measure_mono ?_) hcompact.measure_lt_top
    intro y hy
    simp only [cube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
      Set.mem_Icc] at hy ⊢
    exact fun i => ⟨(hy i).1, (hy i).2.le⟩
  have he : win F = ⋃ k ∈ F, cube 0 k := by
    ext y
    simp only [win, Set.mem_preimage, Finset.mem_coe, Set.mem_iUnion, mem_cube_iff, exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨k, hk, h⟩ => h ▸ hk⟩
  rw [he]
  exact (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun k _ => hc k)

/-- Nash's bounded window truncations belong to the signed physical L² space. -/
theorem u1_signed_physical_trunc_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (N : ℕ) (f : EinsteinRelation.Vec d → ℝ)
    (hf : AEStronglyMeasurable f volume) :
    MemLp (trunc N f) 2 (physicalReversibleMeasure ω hd lam) := by
  let μ := physicalReversibleMeasure ω hd lam
  have hac : μ ≪ (volume : Measure (EinsteinRelation.Vec d)) := by
    change physicalReversibleMeasure ω hd lam ≪ volume
    rw [EinsteinRelation.Diffusion.physicalReversibleMeasure_eq_sourceDensity]
    exact withDensity_absolutelyContinuous _ _
  have hm : AEStronglyMeasurable (fun y => clampN N (f y)) μ :=
    (continuous_clampN N).comp_aestronglyMeasurable (hf.mono_ac hac)
  let : IsFiniteMeasure (μ.restrict (win (box (d := d) N))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact u1_signed_physical_window_finite hd ω lam _⟩
  unfold trunc
  rw [memLp_indicator_iff_restrict (measurableSet_win _)]
  exact MemLp.of_bound hm.restrict (N : ℝ) (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]; exact abs_clampN_le N _)

/-- Each Nash truncation is transported by the actual signed physical kernel
and L² semigroup, Lebesgue almost everywhere. -/
theorem u1_signed_kernel_trunc_ae_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (N : ℕ)
    (f : EinsteinRelation.Vec d → ℝ) (hf : AEStronglyMeasurable f volume) :
    (fun x => ∫ y, trunc N f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω lam Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
      ((u1_signed_physical_trunc_memLp hd ω lam N f hf).toLp (trunc N f)) x) := by
  exact u1_signed_kernel_integral_ae_volume hd ω lam Λ hΛ hω hSmooth t _
    (u1_signed_physical_trunc_memLp hd ω lam N f hf)

#print axioms u1_signed_physical_force_measure_comparable
#print axioms u1_signed_force_graph_gradient_comparison
#print axioms u1_force_graph_complex
#print axioms u1_signed_physical_graph_gauge_forward
#print axioms u1_signed_kernel_trunc_ae_volume
#print axioms u1_signed_physical_window_finite
#print axioms u1_signed_physical_trunc_memLp
#print axioms u1_signed_dyadic_output_le_one
#print axioms u1_signed_dyadic_output_sq_integral_le
#print axioms u1_signed_physical_graph_energy_lower
#print axioms u1_signed_dyadic_output_L1_contraction

#print axioms u1_signed_physical_L1_contraction

#print axioms u1_unforced_physical_nash_representation
#print axioms u1_dyadic_indicator_integral_abs
#print axioms u1_compactContinuous_nash_dom
#print axioms u1_unforced_volume_memLp_physical
#print axioms u1_signed_physical_bounded_indicator_memLp
#print axioms u1_signed_physical_dyadic_indicator_memLp
#print axioms u1_signed_dyadic_output_ae_physical_L2
#print axioms u1_signed_gauge_gradient_sq_le
#print axioms u1_signed_physical_gauge_gradient_energy
#print axioms u1_signed_physical_gauge_gradient_energy_integral
#print axioms u1_signed_gauge_gradient_integral_identity
#print axioms u1_signed_physical_graph_gauge_spatial_h1
#print axioms u1_signed_physical_gauge_spatial_energy
#print axioms u1_signed_physical_gauge_nash
#print axioms u1_signed_gauge_mass_integral_identity
#print axioms u1_signed_physical_gauge_mass_comparable
#print axioms u1_signed_physical_mass_gauge_nash
#print axioms u1_signed_physical_closedForm_gauge_nash
#print axioms u1_signed_physical_generator_decay
#print axioms u1_nash_decay_with_linear_term
#print axioms u1_signed_physical_generator_nash_differential
#print axioms u1_signed_physical_generator_orbit_gauge_nash_raised
#print axioms u1_signed_physical_generator_coordinate_exp_le
#print axioms u1_signed_physical_generator_coordinate_exp_abs_le
#print axioms u1_signed_physical_generator_coordinate_exp_before_exit_bound
#print axioms u1_signed_physical_exp_ball_stopped_centered
#print axioms u1_signed_physical_exp_stopped_moment_identity
#print axioms u1_signed_physical_exp_stopped_generator_path_bound
#print axioms u1_signed_physical_exp_stopped_moment_le
#print axioms u1_signed_physical_coordinate_exp_moment
#print axioms u1_signed_kernel_integrable_ae_volume
#print axioms u1_signed_kernel_L2_add_ae_volume
#print axioms u1_signed_kernel_L2_sum_ae_volume
#print axioms u1_signed_kernel_compact_integrable
#print axioms u1_signed_kernel_compact_add
#print axioms u1_signed_kernel_compact_integral_ae_volume
#print axioms u1_signed_physical_ae_to_volume
#print axioms u1_signed_kernel_integral_ae_volume
#print axioms u1_unforced_kernel_integral_ae_volume
#print axioms u1_unforced_kernel_dom_add
#print axioms u1_unforced_kernel_dom_smul

#print axioms u1_signedPhysicalDyadicOutput_measurable
#print axioms u1_signedPhysicalDyadicOutput_nonneg
#print axioms u1_signedPhysicalDyadicOutput_child_add

#print axioms u1_physicalDyadicOutput_measurable
#print axioms u1_physicalDyadicOutput_nonneg
#print axioms u1_physicalDyadicOutput_child_add

#print axioms u1_normalized_parabolic_coefficient
#print axioms u1_normalized_reduced_parabolic_coefficient

#print axioms u1_signed_physical_coordinate_increment_exp_moment

#print axioms u1_signed_physical_kernel_coordinate_increment_exp_moment

#print axioms u1_signed_physical_kernel_coordinate_exp_subinvariant

#print axioms u1_signed_physical_kernel_lintegral_swap

#print axioms u1_signed_physical_semigroup_gauge_L1_interval

#print axioms u1_signed_physical_semigroup_gauge_L1_le

#print axioms u1_signed_physical_semigroup_gauge_integrable

#print axioms u1_signed_physical_semigroup_gauge_lintegral_le

#print axioms u1_signed_physical_semigroup_weight_lintegral_le

#print axioms u1_signed_physical_semigroup_weight_integrable

#print axioms u1_signed_physical_semigroup_weight_L1_le

#print axioms u1_signed_physical_semigroup_weight_L1_interval

#print axioms u1_signed_weight_lintegral_identity

#print axioms u1_signed_physical_kernel_weight_lintegral_le

#print axioms u1_signed_gauge_lintegral_identity

#print axioms u1_signed_physical_kernel_gauge_lintegral_le

#print axioms u1_signed_physical_kernel_weighted_lintegral_le

#print axioms u1_signed_physical_positive_time_energy

#print axioms u1_signed_physical_positive_time_generator

#print axioms u1_signed_physical_L1_L2_decay

#print axioms u1_signed_physical_gauge_L1_to_L2

#print axioms u1_signed_physical_gauge_L1_to_L2_fun

#print axioms u1_signed_physical_gauge_L1_to_L2_volume


/-- The symmetric weighted energy identity underlying exponential conjugation.
The last term is the cost of the multiplier gradient. -/
theorem u1_symmetric_weighted_energy_identity {d : ℕ}
    (A : EinsteinRelation.Mat d) (hA : A.transpose = A)
    (φ u : ℝ) (g v : EinsteinRelation.Vec d) :
    dot (φ • g + u • v) (A.mulVec (φ • g + u • v)) =
      dot g (A.mulVec ((φ ^ 2) • g + (2 * φ * u) • v)) +
        u ^ 2 * dot v (A.mulVec v) := by
  have hs : dot g (A.mulVec v) = dot v (A.mulVec g) := by
    change dotProduct g (A.mulVec v) = dotProduct v (A.mulVec g)
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA]
    exact dotProduct_comm _ _
  change dotProduct _ _ = dotProduct _ _ + u ^ 2 * dotProduct _ _
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  change φ * (φ * dot g (A.mulVec g) + u * dot v (A.mulVec g)) +
      u * (φ * dot g (A.mulVec v) + u * dot v (A.mulVec v)) =
    φ ^ 2 * dot g (A.mulVec g) + (2 * φ * u) * dot g (A.mulVec v) +
      u ^ 2 * dot v (A.mulVec v)
  rw [hs]
  ring


/-- A smooth multiplier with square-integrable value and gradient products
preserves the real weighted Sobolev graph used by the physical form. -/
theorem u1_weighted_graph_mul_smooth {d : ℕ} (ρ : EinsteinRelation.Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (φ : EinsteinRelation.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hv : MemLp (fun x => φ x * u.value x) 2
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hG : MemLp (fun x => φ x • u.weakGradient x +
      u.value x • WithLp.toLp 2 (PDE.classicalGradient φ x)) 2
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) :
    ∃ w : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))),
      w.value = (fun x => φ x * u.value x) ∧
      w.weakGradient = (fun x => φ x • u.weakGradient x +
        u.value x • WithLp.toLp 2 (PDE.classicalGradient φ x)) := by
  let G : EinsteinRelation.Vec d → EuclideanSpace ℝ (Fin d) := fun x =>
    φ x • u.weakGradient x + u.value x • WithLp.toLp 2 (PDE.classicalGradient φ x)
  have hw : PDE.HasWeakGradientOn univ (fun x => φ x * u.value x)
      (fun x => WithLp.ofLp (G x)) := by
    intro i ψ hs hc hsub
    have hp := Correctors.hasWeakPartialDerivative_mul_smooth isOpen_univ i
      (u.distributionalGradient i) hφ
    have he : (fun x => WithLp.ofLp (G x) i) =
        (fun x => φ x * WithLp.ofLp (u.weakGradient x) i +
          u.value x * coordinateDerivative i φ x) := by
      funext x
      simp [G, PDE.classicalGradient, coordinateDerivative, PDE.basisVec, unitVector]
    rw [he]
    exact hp.2.2 ψ ⟨hs, hc, hsub⟩
  let w := EinsteinRelation.SpatialDirichlet.weightedSobolevGraph_mk_of_density_distributionalData
    ρ hρ hρpos (fun x => φ x * u.value x) G hv hG
      (fun i ψ hψ => hw i ψ hψ.1 hψ.2.1 hψ.2.2)
  exact ⟨w, rfl, rfl⟩


/-- Bounded smooth multipliers preserve the real weighted Sobolev graph. -/
theorem u1_weighted_graph_mul_bounded_smooth {d : ℕ} (ρ : EinsteinRelation.Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (φ : EinsteinRelation.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) :
    ∃ w : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))),
      w.value = (fun x => φ x * u.value x) ∧
      w.weakGradient = (fun x => φ x • u.weakGradient x +
        u.value x • WithLp.toLp 2 (PDE.classicalGradient φ x)) := by
  apply u1_weighted_graph_mul_smooth ρ hρ hρpos u φ hφ
  · exact hφb.fun_mul u.value_memLp
  · exact (hφb.smul (r := 2) u.gradient_memLp).add
      (u.value_memLp.smul (r := 2) hDφ)


/-- A bounded smooth multiplier preserves the actual signed physical H¹ domain. -/
theorem u1_signed_physicalH1_mul_bounded_smooth {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (f φ : EinsteinRelation.Vec d → ℝ)
    (hf : physicalH1Member ω hd lam f)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam)) :
    physicalH1Member ω hd lam (fun x => φ x * f x) := by
  obtain ⟨u, hu⟩ := (physicalH1Member_iff_exists_graph ω hd lam f).mp hf
  obtain ⟨w, hw, _⟩ := u1_weighted_graph_mul_bounded_smooth
    (sourceReducedDensity hd lam) (continuousSourceReducedDensity hd lam)
    (positiveSourceReducedDensity hd lam) u φ hφ hφb hDφ
  apply (physicalH1Member_iff_exists_graph ω hd lam _).mpr
  refine ⟨w, ?_⟩
  filter_upwards [hu] with x hx
  rw [hw]
  simp only [hx]

/-- The closed form domain is stable under bounded smooth multipliers. -/
theorem u1_signed_physical_closedForm_mul_bounded_smooth {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain)
    (φ : EinsteinRelation.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam)) :
    let hφp : MemLp φ ∞ (physicalReversibleMeasure ω hd lam) :=
      hφb.of_measure_le_smul ENNReal.ofReal_ne_top
        (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
    let hm : MemLp (fun x => φ x * f x) 2 (physicalReversibleMeasure ω hd lam) :=
      hφp.fun_mul (Lp.memLp f)
    hm.toLp (fun x => φ x * f x) ∈
      (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain := by
  dsimp only
  let hφp : MemLp φ ∞ (physicalReversibleMeasure ω hd lam) :=
    hφb.of_measure_le_smul ENNReal.ofReal_ne_top
      (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
  apply (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr
  have hfH := (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mp hf
  have hm := u1_signed_physicalH1_mul_bounded_smooth hd ω lam f φ hfH hφ hφb hDφ
  obtain ⟨q, hq⟩ := hm
  refine ⟨q, hq.trans ?_⟩
  exact (hφp.fun_mul (Lp.memLp f)).coeFn_toLp.symm

/-- The multiplier product rule turns the symmetric energy into the
unweighted cross energy plus the exact gradient correction. -/
theorem u1_weighted_graph_multiplier_energy_identity {d : ℕ}
    {m : Measure (EinsteinRelation.Vec d)}
    (A : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (hA : ∀ x, (A x).transpose = A x)
    (u w z : WeightedSobolevGraph m)
    (φ : EinsteinRelation.Vec d → ℝ)
    (v : EinsteinRelation.Vec d → EuclideanSpace ℝ (Fin d))
    (hw : ∀ x, w.weakGradient x = φ x • u.weakGradient x + u.value x • v x)
    (hz : ∀ x, z.weakGradient x = (φ x ^ 2) • u.weakGradient x +
      (2 * φ x * u.value x) • v x) (x : EinsteinRelation.Vec d) :
    weightedFormIntegrand A w w x = weightedFormIntegrand A u z x +
      (1 / 2 : ℝ) * u.value x ^ 2 *
        dot (WithLp.ofLp (v x)) ((A x).mulVec (WithLp.ofLp (v x))) := by
  have h := u1_symmetric_weighted_energy_identity (A x) (hA x)
    (φ x) (u.value x) (WithLp.ofLp (u.weakGradient x)) (WithLp.ofLp (v x))
  unfold weightedFormIntegrand
  rw [hw x, hz x]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul] at ⊢
  rw [h]
  ring

/-- The two actual weighted Sobolev products used in the energy identity. -/
theorem u1_weighted_graph_multiplier_energy_products {d : ℕ}
    (ρ : EinsteinRelation.Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (A : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (hA : ∀ x, (A x).transpose = A x)
    (u : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (φ : EinsteinRelation.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) :
    ∃ w z : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))),
      w.value = (fun x => φ x * u.value x) ∧
      z.value = (fun x => φ x ^ 2 * u.value x) ∧
      ∀ x, weightedFormIntegrand A w w x = weightedFormIntegrand A u z x +
        (1 / 2 : ℝ) * u.value x ^ 2 *
          dot (PDE.classicalGradient φ x) ((A x).mulVec (PDE.classicalGradient φ x)) := by
  obtain ⟨w, hwv, hwg⟩ := u1_weighted_graph_mul_bounded_smooth ρ hρ hρpos u φ hφ hφb hDφ
  obtain ⟨z, hzv, hzg⟩ := u1_weighted_graph_mul_bounded_smooth ρ hρ hρpos w φ hφ hφb hDφ
  have hzw : z.value = (fun x => φ x ^ 2 * u.value x) := by
    rw [hzv, hwv]
    funext x
    ring
  have hzg' (x : EinsteinRelation.Vec d) : z.weakGradient x =
      (φ x ^ 2) • u.weakGradient x +
        (2 * φ x * u.value x) • WithLp.toLp 2 (PDE.classicalGradient φ x) := by
    rw [hzg, hwg, hwv]
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.toLp_apply]
    ring
  refine ⟨w, z, hwv, hzw, ?_⟩
  intro x
  simpa only [WithLp.ofLp_toLp] using
    u1_weighted_graph_multiplier_energy_identity A hA u w z φ
      (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x))
      (fun x => congrFun hwg x) hzg' x

/-- Transfer a force graph to the comparable physical reversible measure,
without changing its value or weak gradient. -/
def u1SignedForceGraphToPhysical {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalForceMeasure (firstCoordinateIndex hd) lam)) :
    WeightedSobolevGraph (physicalReversibleMeasure ω hd lam) where
  value := u.value
  weakGradient := u.weakGradient
  value_memLp := u.value_memLp.of_measure_le_smul ENNReal.ofReal_ne_top
    (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
  gradient_memLp := u.gradient_memLp.of_measure_le_smul ENNReal.ofReal_ne_top
    (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
  distributionalGradient := u.distributionalGradient

/-- Smooth multiplier products and their energy identity in the actual
signed physical measure. -/
theorem u1_signed_physical_graph_multiplier_products {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (φ : EinsteinRelation.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam)) :
    ∃ w z : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam),
      w.value = (fun x => φ x * u.value x) ∧
      z.value = (fun x => φ x ^ 2 * u.value x) ∧
      ∀ x, weightedFormIntegrand ω.1 w w x = weightedFormIntegrand ω.1 u z x +
        (1 / 2 : ℝ) * u.value x ^ 2 *
          dot (PDE.classicalGradient φ x) ((ω.1 x).mulVec (PDE.classicalGradient φ x)) := by
  have hp := (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
  exact u1_weighted_graph_multiplier_energy_products
    (sourcePhysicalDensity ω hd lam) (continuousSourcePhysicalDensity ω hd lam)
    (positiveSourcePhysicalDensity ω hd lam) ω.1 (fun x => (hω.1 x).1) u φ hφ
    (hφb.of_measure_le_smul ENNReal.ofReal_ne_top hp)
    (hDφ.of_measure_le_smul ENNReal.ofReal_ne_top hp)

#print axioms u1_signed_physical_graph_multiplier_products

/-- An identity of integrable terms also makes its correction integrable. -/
theorem u1_integral_eq_add_of_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g c : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ x, f x = g x + c x) :
    Integrable c μ ∧ (∫ x, f x ∂μ) = (∫ x, g x ∂μ) + ∫ x, c x ∂μ := by
  have hc : Integrable c μ := by
    apply (hf.sub hg).congr
    filter_upwards [] with x
    dsimp only [Pi.sub_apply]
    linarith [h x]
  exact ⟨hc, (integral_congr_ae (Filter.Eventually.of_forall h)).trans (integral_add hg hc)⟩

/-- Integrated multiplier energy identity for the signed physical graph. -/
theorem u1_signed_physical_graph_multiplier_energy {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (φ : EinsteinRelation.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam)) :
    ∃ w z : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam),
      w.value = (fun x => φ x * u.value x) ∧
      z.value = (fun x => φ x ^ 2 * u.value x) ∧
      (∫ x, weightedFormIntegrand ω.1 w w x ∂physicalReversibleMeasure ω hd lam) =
        (∫ x, weightedFormIntegrand ω.1 u z x ∂physicalReversibleMeasure ω hd lam) +
        ∫ x, (1 / 2 : ℝ) * u.value x ^ 2 *
          dot (PDE.classicalGradient φ x) ((ω.1 x).mulVec (PDE.classicalGradient φ x))
          ∂physicalReversibleMeasure ω hd lam := by
  obtain ⟨w, z, hw, hz, he⟩ :=
    u1_signed_physical_graph_multiplier_products hd ω lam Λ hω u φ hφ hφb hDφ
  refine ⟨w, z, hw, hz, ?_⟩
  exact (u1_integral_eq_add_of_integrable (physicalReversibleMeasure ω hd lam)
    (weightedFormIntegrand ω.1 w w) (weightedFormIntegrand ω.1 u z)
    (fun x => (1 / 2 : ℝ) * u.value x ^ 2 *
      dot (PDE.classicalGradient φ x) ((ω.1 x).mulVec (PDE.classicalGradient φ x)))
    (physicalWeightedFormIntegrand_integrable_of_regular ω Λ hΛ hω w w)
    (physicalWeightedFormIntegrand_integrable_of_regular ω Λ hΛ hω u z) he).2

#print axioms u1_signed_physical_graph_multiplier_energy

/-- Equal physical graph values determine the same physical weak gradient. -/
theorem u1_signed_physical_graph_gradient_ae_eq {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ)
    (u v : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (huv : u.value =ᵐ[physicalReversibleMeasure ω hd lam] v.value) :
    u.weakGradient =ᵐ[physicalReversibleMeasure ω hd lam] v.weakGradient := by
  have hv := weakGradients_ae_eq_of_value_ae_eq
    (u1_signed_physical_ae_to_volume hd ω lam huv)
    u.distributionalGradient v.distributionalGradient
  have hp : (fun x => WithLp.ofLp (u.weakGradient x)) =ᵐ[
      physicalReversibleMeasure ω hd lam] (fun x => WithLp.ofLp (v.weakGradient x)) :=
    (withDensity_absolutelyContinuous _ _).ae_eq hv
  filter_upwards [hp] with x hx
  exact WithLp.ofLp_injective 2 hx

#print axioms u1_signed_physical_graph_gradient_ae_eq


#print axioms u1SignedForceGraphToPhysical
#print axioms u1_integral_eq_add_of_integrable

#print axioms u1_weighted_graph_multiplier_energy_products

#print axioms u1_weighted_graph_multiplier_energy_identity

#print axioms u1_signed_physicalH1_mul_bounded_smooth
#print axioms u1_signed_physical_closedForm_mul_bounded_smooth

#print axioms u1_weighted_graph_mul_bounded_smooth

#print axioms u1_weighted_graph_mul_smooth

#print axioms u1_symmetric_weighted_energy_identity

/-- The physical closed form may be evaluated on any physical graph
representatives of its two values. -/
theorem u1_signed_physical_closedForm_eq_graph_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (a b : Blueprint.GMPForceH1 hd lam)
    (u v : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam]
      Blueprint.gmpPhysicalH1Value hd ω lam Λ hω a)
    (hv : v.value =ᵐ[physicalReversibleMeasure ω hd lam]
      Blueprint.gmpPhysicalH1Value hd ω lam Λ hω b) :
    (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
      (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω a)
      (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω b) =
      ∫ x, weightedFormIntegrand ω.1 u v x ∂physicalReversibleMeasure ω hd lam := by
  rw [Blueprint.gmpPhysicalClosedForm_value]
  let ga := sourcePhysicalGraph (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) a
  let gb := sourcePhysicalGraph (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) b
  change weightedSpatialForm ω.1 ga gb = weightedSpatialForm ω.1 u v
  apply weightedSpatialForm_congr_of_graph_value_ae
    (hρ := continuousSourcePhysicalDensity ω hd lam)
    (hρpos := positiveSourcePhysicalDensity ω hd lam)
  · exact ga.value_memLp.coeFn_toLp.symm.trans hu.symm
  · exact gb.value_memLp.coeFn_toLp.symm.trans hv.symm

#print axioms u1_signed_physical_closedForm_eq_graph_integral

/-- The physical form on arbitrary domain elements can be evaluated using
any physical Sobolev graphs representing those elements. -/
theorem u1_signed_physical_closedForm_domain_eq_graph_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (a b : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (ha : a ∈ (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain)
    (hb : b ∈ (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain)
    (u v : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] a)
    (hv : v.value =ᵐ[physicalReversibleMeasure ω hd lam] b) :
    (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form a b =
      ∫ x, weightedFormIntegrand ω.1 u v x ∂physicalReversibleMeasure ω hd lam := by
  obtain ⟨a', ha'⟩ := (Blueprint.gmpPhysicalH1Value_range_iff hd ω lam Λ hω a).mpr
    ((Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω a).mp ha)
  obtain ⟨b', hb'⟩ := (Blueprint.gmpPhysicalH1Value_range_iff hd ω lam Λ hω b).mpr
    ((Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω b).mp hb)
  subst a
  subst b
  exact u1_signed_physical_closedForm_eq_graph_integral hd ω lam Λ hΛ hω a' b' u v hu hv

#print axioms u1_signed_physical_closedForm_domain_eq_graph_integral

end EinsteinFull


#print axioms EinsteinFull.u1_signed_physical_gauge_L1_pairing_bound

#print axioms EinsteinFull.u1_signed_kernel_gauge_L1_pairing_bound

#print axioms EinsteinFull.u1_signed_conjugated_kernel_L1_pairing_bound

#print axioms EinsteinFull.u1_signed_kernel_bounded_sets_gauge_pairing

#print axioms EinsteinFull.u1_signed_kernel_bounded_sets_coordinate_pairing
