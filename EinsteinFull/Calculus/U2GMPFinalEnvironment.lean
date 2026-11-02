import EinsteinFull.Calculus.U6RegularPathRealization
import EinsteinFull.Calculus.U5RegularPhysicalCompensator
import EinsteinFull.Calculus.U6GMPSmoothRealization
import EinsteinFull.Calculus.U4RegularKernelSmoothing
import EinsteinFull.Calculus.U5RegularGaugeGrowth
import EinsteinFull.Calculus.U7RegularKernelDensity
import EinsteinFull.Calculus.SunaSuppliedLawIdentification
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- A measurable physical origin law whose fibers solve the textbook problem
on almost every regular environment. -/
theorem u2_measurable_physical_textbook_origin_kernel
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) (lam : ℝ) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      ∀ᵐ ω ∂Q.measure, ∀ _hω : IsRegular Λ ω,
        SolvesMartingaleProblem
          (External.Draft.svGenerator (⇑ω.1)
            (physicalDrift ω (firstCoordinateIndex hd) lam)) 0 (K ω) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let i := firstCoordinateIndex hd
  obtain ⟨PY, hmarkov, hPY⟩ := foundation_reduced_textbook_kernel hΛpos i lam
  let : IsMarkovKernel PY := hmarkov
  obtain ⟨PX, hPX⟩ := c16_inverse_clock_quenched_family_of_isSFiniteKernel d hd Λ r Q PY
  have htext : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ ω,
      SolvesMartingaleProblem
        (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) 0 (PX (0, ω)) := by
    filter_upwards [hPX] with ω he hω
    have hY := hPY ω hω
    let : IsProbabilityMeasure (PY (0, ω)) := hY.1
    have hocc := foundation_reduced_textbook_averaged_occupation_ac_of_two_le
      hd hΛpos hω i lam hY
    have hactual := c16_reduced_solves_of_textbook_and_averaged_occupation
      hΛpos hω i lam hY hocc
    have hclock := c16_time_change_solves_of_regular hΛpos hω i lam 0 hactual
    have hclockocc := u5_inverse_clock_averaged_occupation_ac hω (PY (0, ω)) hocc
    rw [he hω]
    exact c4_textbook_solves_of_physical_and_averaged_occupation
      hΛpos hω i lam hclock hclockocc
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw PX ω) := by
    filter_upwards [Q.regular, htext] with ω hω ht
    exact (ht hω).1
  obtain ⟨K, hK, hKmark⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  refine ⟨K, hKmark, ?_⟩
  filter_upwards [hK, htext] with ω he ht hω
  rw [← he]
  exact ht hω

/-- The actual regular kernel supplies the same measurable GMP origin law
whenever its positive-time transition probabilities are absolutely continuous. -/
theorem u2_foundation_gmp_physical_origin_law_and_mp_of_kernel_ac
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hac : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ ω,
      ∀ (t : ℝ≥0), 0 < t → ∀ x,
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ (volume : Measure (Vec d))) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      IsGMPPhysicalOriginLaw hd hΛ Q lam h0 h1 K ∧
      ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (K ω) := by
  obtain ⟨K, hmark, htext⟩ := u2_measurable_physical_textbook_origin_kernel hd hΛ Q lam
  have hGMP : IsGMPPhysicalOriginLaw hd hΛ Q lam h0 h1 K := by
    filter_upwards [Q.regular, hac, htext] with ω hω hacω hK
    obtain ⟨L, hL, hfdd⟩ := u6_regular_continuous_kernel_of_volume_ac
      hd ω lam Λ hΛ hω (hacω hω)
    let : IsMarkovKernel L := hL
    obtain ⟨⟨R, hRL, hRP⟩, hMP⟩ :=
      u2_regular_fixed_environment_realization_and_mp_of_ac_fdd
        hd ω lam Λ hΛ hω h0 h1 L hfdd (hacω hω)
    let : IsProbabilityMeasure (R.pathLaw 0) := by rw [hRL]; infer_instance
    have hmarg : ∀ t : ℝ≥0, 0 < t →
        (R.pathLaw 0).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
      intro t ht
      rw [R.pathLaw_endpoint, hRP]
      exact hacω hω t ht 0
    have hocc := u2_averaged_occupation_ac_of_marginals (R.pathLaw 0) hmarg
    have hphys : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam)
        0 (R.pathLaw 0) := by rw [hRL]; exact hMP 0
    have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
    have hRtext := c4_textbook_solves_of_physical_and_averaged_occupation
      hΛpos hω (firstCoordinateIndex hd) lam hphys hocc
    obtain ⟨hc, hs, hb, he, hm, hbd⟩ :=
      physical_svHypotheses hΛpos hω (firstCoordinateIndex hd) lam
    obtain ⟨S, _, hu⟩ := foundation_textbook_well_posed d (by omega)
      (⇑ω.1) (physicalDrift ω (firstCoordinateIndex hd) lam) hc hs hb he hm hbd 0
    exact ⟨hω, R, (hu _ (hK hω)).trans (hu _ hRtext).symm⟩
  exact ⟨K, hmark, hGMP, u2_gmp_physical_origin_law_solves_mp hd hΛ Q lam h0 h1 K hGMP⟩

/-- A pointwise exponential barrier yields gauge L¹ growth for the actual
regular physical semigroup. -/
theorem u2_regular_gauge_growth_of_exponential_barrier {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C : ℝ) (hC : 0 ≤ C)
    (hbarrier : ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (-lam * y (firstCoordinateIndex hd))) ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd))) *
        ENNReal.ofReal (Real.exp (C * (t : ℝ)))) :
    u4SignedGaugeL1Interval hd ω lam Λ hΛ hω := by
  have hkg : u4RegularKernelGaugeGrowth hd ω lam Λ hΛ hω :=
    ⟨C, hC, u5_regular_signed_kernel_gauge_growth_of_barrier hd ω lam Λ hΛ hω C hbarrier⟩
  exact u4_regular_physical_semigroup_gauge_L1_interval_of_kernel_growth hd ω lam Λ hΛ hω hkg


/-- Gauge-weighted L¹ growth supplies absolute continuity of the actual
regular transition kernel at every positive time and starting point. -/
theorem u2_regular_kernel_ac_of_gauge_growth {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hgrowth : u4SignedGaugeL1Interval hd ω lam Λ hΛ hω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  apply u7_regular_signed_kernel_ac_of_local_L2_bound hd ω lam Λ hΛ hω t
  intro x
  exact u4_regular_signed_kernel_local_L2_bound_of_gauge hd ω lam Λ hΛ hω hgrowth t ht x


/-- Gauge-weighted L¹ growth on almost every regular field yields the same
measurable physical origin kernel for the GMP law and martingale problem. -/
theorem u2_foundation_gmp_physical_origin_law_and_mp_of_gauge_growth
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hgrowth : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ ω,
      u4SignedGaugeL1Interval hd ω lam Λ hΛ hω) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      IsGMPPhysicalOriginLaw hd hΛ Q lam h0 h1 K ∧
      ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (K ω) := by
  apply u2_foundation_gmp_physical_origin_law_and_mp_of_kernel_ac hd hΛ Q lam h0 h1
  filter_upwards [hgrowth] with ω hω hreg t ht x
  exact u2_regular_kernel_ac_of_gauge_growth hd ω lam Λ hΛ hreg (hω hreg) t ht x


/-- On smooth regular fields, the regular and smooth C₀ constructions yield
identical kernels, since both realize the same physical L² semigroup. -/
theorem u2_regular_kernel_eq_smooth_kernel {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (x : Vec d) :
    u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
      Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let S := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let : IsProbabilityMeasure (P t x) := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
  let : IsProbabilityMeasure (S t x) :=
    ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, f.continuous⟩, f.hasCompactSupport.is_zero_at_infty⟩
  let F := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f f.continuous f.hasCompactSupport
  have hP := u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t g (F.toLp f) F.coeFn_toLp
  have hS := (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2_compact
    hd ω lam Λ hΛ hω hSmooth t f f.continuous f.hasCompactSupport).2
  have hae : (fun z => ∫ y, f y ∂P t z) =ᵐ[volume]
      (fun z => ∫ y, f y ∂S t z) := by
    apply (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp
    filter_upwards [hP, hS] with z hp hs
    exact hp.trans hs.symm
  have hp : Continuous (fun z => ∫ y, f y ∂P t z) := by
    change Continuous (fun z => ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t g).continuous
  have hs : Continuous (fun z => ∫ y, f y ∂S t z) := by
    change Continuous (fun z => ∫ y, g y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t z)
    simp_rw [Blueprint.gmpPhysicalC0KernelSemigroup_integral]
    exact (Blueprint.gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth t g).continuous
  exact congrFun (Measure.eq_of_ae_eq hae hp hs) x


/-- The regular kernel has Lebesgue densities at every positive time and
start when the field is smooth, for arbitrary real force. -/
theorem u2_regular_smooth_kernel_absolutelyContinuous {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ (volume : Measure (Vec d)) := by
  rw [u2_regular_kernel_eq_smooth_kernel hd ω lam Λ hΛ hω hSmooth t x]
  exact u6_physical_transition_absolutelyContinuous_volume hd ω lam Λ hΛ hω hSmooth t ht x

/-- Each smooth regular field has a realization of its actual regular kernel
that solves the physical martingale problem from every starting point. -/
theorem u2_regular_smooth_fixed_environment_realization_and_mp
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1,
      R.transitionKernel = (fun t => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t) ∧
      ∀ x, SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam)
        x (R.pathLaw x) := by
  have hac := u2_regular_smooth_kernel_absolutelyContinuous hd ω lam Λ hΛ hω hSmooth
  obtain ⟨K, hK, hfdd⟩ := u6_regular_continuous_kernel_of_volume_ac hd ω lam Λ hΛ hω hac
  let : IsMarkovKernel K := hK
  obtain ⟨⟨R, hRK, hRP⟩, hMP⟩ :=
    u2_regular_fixed_environment_realization_and_mp_of_ac_fdd
      hd ω lam Λ hΛ hω h0 h1 K hfdd hac
  refine ⟨R, hRP, ?_⟩
  intro x
  rw [hRK]
  exact hMP x


/-- The same-kernel GMP and martingale-problem conclusion holds for any
environment law concentrated on smooth fields, for the full signed-force range. -/
theorem u2_foundation_smooth_gmp_physical_origin_law_and_mp
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hsmooth : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      IsGMPPhysicalOriginLaw hd hΛ Q lam h0 h1 K ∧
      ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (K ω) := by
  apply u2_foundation_gmp_physical_origin_law_and_mp_of_kernel_ac hd hΛ Q lam h0 h1
  filter_upwards [hsmooth] with ω hSmooth hω t ht x
  exact u2_regular_smooth_kernel_absolutelyContinuous hd ω lam Λ hΛ hω hSmooth t ht x


/-- At zero force the foundation law is the actual GMP physical origin law. -/
theorem u2_foundation_unforced_gmp_physical_origin_law_and_mp
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      IsGMPPhysicalOriginLaw hd hΛ Q 0 (le_refl 0) (by norm_num) K ∧
      ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω 0) 0 (K ω) := by
  apply u2_foundation_gmp_physical_origin_law_and_mp_of_kernel_ac hd hΛ Q 0
    (le_refl 0) (by norm_num)
  filter_upwards with ω hω t ht x
  obtain ⟨M, hM, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  exact Measure.absolutelyContinuous_of_le_smul (hdom x)

/-- A measurable unforced origin law has the actual regular spatial kernel as
its marginal at every time, on one full event. -/
theorem u2_foundation_unforced_origin_kernel_and_regular_marginals
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ ω,
        SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω 0) 0 (K ω) ∧
        ∀ t : ℝ≥0, (K ω).map (pathPosition t) =
          u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t 0 := by
  obtain ⟨K, hmark, htext⟩ := u2_measurable_physical_textbook_origin_kernel hd hΛ Q 0
  refine ⟨K, hmark, ?_⟩
  filter_upwards [htext] with ω hK hω
  have hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≪ (volume : Measure (Vec d)) := by
    intro t ht x
    obtain ⟨M, hM, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
    exact Measure.absolutelyContinuous_of_le_smul (hdom x)
  obtain ⟨L, hL, hfdd⟩ := u6_regular_continuous_kernel_of_volume_ac
    hd ω 0 Λ hΛ hω hac
  let : IsMarkovKernel L := hL
  obtain ⟨⟨R, hRL, hRP⟩, hMP⟩ :=
    u2_regular_fixed_environment_realization_and_mp_of_ac_fdd
      hd ω 0 Λ hΛ hω (by norm_num) (by norm_num) L hfdd hac
  let : IsProbabilityMeasure (R.pathLaw 0) := by rw [hRL]; infer_instance
  have hmarg : ∀ t : ℝ≥0, 0 < t →
      (R.pathLaw 0).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
    intro t ht
    rw [R.pathLaw_endpoint, hRP]
    exact hac t ht 0
  have hocc := u2_averaged_occupation_ac_of_marginals (R.pathLaw 0) hmarg
  have hphys : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω 0)
      0 (R.pathLaw 0) := by rw [hRL]; exact hMP 0
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hRtext := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛpos hω (firstCoordinateIndex hd) 0 hphys hocc
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ :=
    physical_svHypotheses hΛpos hω (firstCoordinateIndex hd) 0
  obtain ⟨S, _, hu⟩ := foundation_textbook_well_posed d (by omega)
    (⇑ω.1) (physicalDrift ω (firstCoordinateIndex hd) 0) hc hs hb he hm hbd 0
  have heq : K ω = R.pathLaw 0 := (hu _ (hK hω)).trans (hu _ hRtext).symm
  constructor
  · rw [heq]; exact hphys
  · intro t
    rw [heq, R.pathLaw_endpoint, hRP]

/-- The supplied reduced GMP law itself solves the reduced martingale problem. -/
theorem u2_arbitrary_supplied_reduced_kernel_MP
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω)) := by
  filter_upwards [hP] with ω hω
  obtain ⟨hreg, R, hR⟩ := hω
  rw [hR 0]
  have hgen : physicalGenerator (firstCoordinateIndex hd) (zeroPotentialReducedPair ω) lam =
      reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam := by
    funext f x
    unfold physicalGenerator reducedGenerator
    simp_rw [reducedCoefficient_zeroPotentialReducedPair]
    change Real.exp (2 * (0 : ℝ)) / 2 * _ + _ = _
    rw [mul_zero, Real.exp_zero]
    rfl
  rw [← hgen]
  exact foundation_arbitrary_supplied_gmp_physical_MP hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
    hreg lam h0 h1 R 0


/-- The supplied reduced GMP law solves the martingale problem at every start. -/
theorem u2_arbitrary_supplied_reduced_kernel_MP_every_start
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, SolvesMartingaleProblem
      (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) x (P (x, ω)) := by
  filter_upwards [hP] with ω hω
  obtain ⟨hreg, R, hR⟩ := hω
  intro x
  rw [hR x]
  have hgen : physicalGenerator (firstCoordinateIndex hd) (zeroPotentialReducedPair ω) lam =
      reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam := by
    funext f x
    unfold physicalGenerator reducedGenerator
    simp_rw [reducedCoefficient_zeroPotentialReducedPair]
    change Real.exp (2 * (0 : ℝ)) / 2 * _ + _ = _
    rw [mul_zero, Real.exp_zero]
    rfl
  rw [← hgen]
  exact foundation_arbitrary_supplied_gmp_physical_MP hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
    hreg lam h0 h1 R x






end EinsteinFull
