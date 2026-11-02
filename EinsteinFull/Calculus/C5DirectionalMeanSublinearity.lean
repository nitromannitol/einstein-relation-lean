import EinsteinFull.Calculus.C5VectorCorrectorAssembly
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open EinsteinRelation MeasureTheory Filter
open Environment.AKMTestIntegralSupport ReductionImageV3
open EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.External.GilbargTrudinger
open scoped Topology BigOperators

noncomputable section
namespace EinsteinFull

/-- An almost-everywhere vanishing ergodic average converges to zero in L². -/
theorem c5_l2_ergodic_average_tendsto_zero_of_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hT : ‖T‖ ≤ 1) (f : Lp ℝ 2 μ)
    (hae : ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (birkhoffAverage ℝ T id n f : Lp ℝ 2 μ) ω) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => birkhoffAverage ℝ T id n f) atTop (𝓝 0) := by
  let v : Lp ℝ 2 μ := (T.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)).orthogonalProjectionOnto f
  have hv : Tendsto (fun n : ℕ => birkhoffAverage ℝ T id n f) atTop (𝓝 v) :=
    T.tendsto_birkhoffAverage_orthogonalProjection hT f
  have hμ := tendstoInMeasure_of_tendsto_Lp hv
  have hzero : TendstoInMeasure μ
      (fun n : ℕ => (birkhoffAverage ℝ T id n f : Lp ℝ 2 μ)) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => Lp.aestronglyMeasurable _) hae
  have heq : (v : Ω → ℝ) =ᵐ[μ] (fun _ => 0) := tendstoInMeasure_ae_unique hμ hzero
  have : v = 0 := by
    apply Lp.ext
    exact heq.trans (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)).symm
  simpa [this] using hv

/-- The L² ergodic average of a measure-preserving composition is represented
by the corresponding pointwise orbit average. -/
theorem c5_comp_ergodic_average_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ) (f : Lp ℝ 2 μ) (n : ℕ) :
    let T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := (Lp.compMeasurePreservingₗᵢ ℝ τ hτ).toContinuousLinearMap
    (birkhoffAverage ℝ T id n f : Lp ℝ 2 μ) =ᵐ[μ]
      fun ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f ((τ^[k]) ω) := by
  classical
  let T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := (Lp.compMeasurePreservingₗᵢ ℝ τ hτ).toContinuousLinearMap
  have hi (k : ℕ) : (T^[k]) f = Lp.compMeasurePreserving (τ^[k]) (hτ.iterate k) f := by
    change ((Lp.compMeasurePreserving τ hτ)^[k]) f = _
    rw [Lp.compMeasurePreserving_iterate]
  have hc (k : ℕ) : (T^[k]) f =ᵐ[μ] fun ω => f ((τ^[k]) ω) := by
    rw [hi]
    exact Lp.coeFn_compMeasurePreserving f (hτ.iterate k)
  change ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, (T^[k]) f : Lp ℝ 2 μ) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_smul (n : ℝ)⁻¹ (∑ k ∈ Finset.range n, (T^[k]) f),
    Lp.coeFn_finsetSum (Finset.range n) (fun k => (T^[k]) f),
    ae_all_iff.mpr hc] with ω hs hm hk
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, hm]
  simp only [Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk'
  exact hk k

/-- Iterated physical translations follow the corresponding integer displacement. -/
theorem c5_physicalTranslate_iterate {d : ℕ} {L : ℝ} (x : Vec d)
    (ω : PhysicalField d L) (n : ℕ) :
    ((physicalTranslate x)^[n] ω).1 = translate ((n : ℝ) • x) ω.1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change translate x (((physicalTranslate x)^[n] ω).1) = _
    rw [ih, translate_add]
    congr 1
    push_cast
    simp [add_smul, add_comm]

/-- A stationary corrector cocycle telescopes along a physical translation orbit. -/
@[nolint unusedArguments]
theorem c5_physical_corrector_orbit_sum {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ}
    (Q : EnvironmentLaw d L r) (χ : FieldPair d → Vec d → Vec d)
    (hz : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q, χ ω 0 = 0)
    (hcoc : ∀ y : Vec d, ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      ∀ x : Vec d, χ (translate y ω.1) x = χ ω (y+x)-χ ω y)
    (x : Vec d) (i : Fin d) :
    ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q, ∀ n : ℕ,
      (∑ k ∈ Finset.range n, χ (((physicalTranslate x)^[k] ω).1) x i) =
        χ ω ((n : ℝ) • x) i := by
  filter_upwards [hz, ae_all_iff.mpr (fun k : ℕ => hcoc ((k : ℝ) • x))] with ω hzero hc
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, c5_physicalTranslate_iterate, hc n x]
    simp only [Pi.sub_apply, Nat.cast_succ, add_smul, one_smul]
    ring

/-- Uniform spatial sublinearity implies sublinearity along each fixed ray. -/
theorem c5_corrector_ray_tendsto_zero {d : ℕ} (χ : Vec d → Vec d)
    (hsub : ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ x)/(t+1) ≤ ε)
    (x : Vec d) (i : Fin d) :
    Tendsto (fun n : ℕ => χ (((n : ℝ)+1) • x) i / ((n : ℝ)+1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hR : 0 < euclideanNorm x + 1 := by
    have : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    linarith
  have he : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (hsub (euclideanNorm x+1) (ε/2) hR he))
  refine ⟨N, fun n hn => ?_⟩
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have hx : euclideanNorm (((n : ℝ)+1) • x) ≤ ((n : ℝ)+1)*(euclideanNorm x+1) := by
    rw [euclideanNorm_smul _ hp.le]
    have : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    nlinarith
  have hb := hN n hn _ hx
  have hcoord := Regeneration.coordinate_abs_le_euclideanNorm (χ (((n : ℝ)+1) • x)) i
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hp]
  calc
    _ ≤ euclideanNorm (χ (((n : ℝ)+1) • x)) / ((n : ℝ)+1) :=
      div_le_div_of_nonneg_right hcoord hp.le
    _ ≤ ε/2 := hb
    _ < ε := by linarith

/-- Translation by a fixed vector acts isometrically on the physical L² space. -/
def c5PhysicalTranslationOperator {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) (x : Vec d) :
    Lp ℝ 2 (physicalReferenceLaw Q) →L[ℝ] Lp ℝ 2 (physicalReferenceLaw Q) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (physicalTranslate x)
    ⟨measurable_physicalTranslate x, physicalReferenceLaw_translation_invariant Q x⟩).toContinuousLinearMap

/-- The translation averages represent the normalized corrector on each orbit. -/
theorem c5_physical_corrector_ergodic_average_ae
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d) (x : Vec d) (i : Fin d)
    (f : Lp ℝ 2 (physicalReferenceLaw Q))
    (hf : (f : PhysicalField d L → ℝ) =ᵐ[physicalReferenceLaw Q] fun ω => χ ω x i)
    (hz : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q, χ ω 0 = 0)
    (hcoc : ∀ y : Vec d, ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      ∀ z : Vec d, χ (translate y ω.1) z = χ ω (y+z)-χ ω y) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ n : ℕ,
      (birkhoffAverage ℝ (c5PhysicalTranslationOperator Q x) id n f :
        Lp ℝ 2 (physicalReferenceLaw Q)) ω = (n : ℝ)⁻¹ * χ ω ((n : ℝ) • x) i := by
  let hτ : MeasurePreserving (physicalTranslate x) (physicalReferenceLaw Q)
      (physicalReferenceLaw Q) :=
    ⟨measurable_physicalTranslate x, physicalReferenceLaw_translation_invariant Q x⟩
  have hpoint (n : ℕ) :
      (birkhoffAverage ℝ (c5PhysicalTranslationOperator Q x) id n f :
        Lp ℝ 2 (physicalReferenceLaw Q)) =ᵐ[physicalReferenceLaw Q]
      fun ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f ((physicalTranslate x)^[k] ω) := by
    exact c5_comp_ergodic_average_ae (physicalReferenceLaw Q) (physicalTranslate x) hτ f n
  have hrep : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ k : ℕ,
      f ((physicalTranslate x)^[k] ω) = χ (((physicalTranslate x)^[k] ω).1) x i :=
    ae_all_iff.mpr (fun k => (hτ.iterate k).quasiMeasurePreserving.ae hf)
  filter_upwards [ae_all_iff.mpr hpoint, hrep,
    c5_physical_corrector_orbit_sum Q χ hz hcoc x i] with ω ha hf' hc n
  rw [ha n, ← hc n]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact hf' k

/-- Corrector orbit averages converge to zero in physical L² in every direction. -/
theorem c5_physical_corrector_ergodic_average_tendsto_zero
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d) (x : Vec d) (i : Fin d)
    (f : Lp ℝ 2 (physicalReferenceLaw Q))
    (hf : (f : PhysicalField d L → ℝ) =ᵐ[physicalReferenceLaw Q] fun ω => χ ω x i)
    (hχ : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      χ ω 0 = 0 ∧ ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∀ z, euclideanNorm z ≤ (t+1)*R → euclideanNorm (χ ω z)/(t+1) ≤ ε)
    (hcoc : ∀ y : Vec d, ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      ∀ z : Vec d, χ (translate y ω.1) z = χ ω (y+z)-χ ω y) :
    Tendsto (fun n : ℕ => birkhoffAverage ℝ (c5PhysicalTranslationOperator Q x) id n f)
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  have hT : ‖c5PhysicalTranslationOperator Q x‖ ≤ 1 := by
    unfold c5PhysicalTranslationOperator
    exact (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 2) ℝ (physicalTranslate x)
      ⟨measurable_physicalTranslate x, physicalReferenceLaw_translation_invariant Q x⟩).norm_toContinuousLinearMap_le
  apply c5_l2_ergodic_average_tendsto_zero_of_ae (physicalReferenceLaw Q) _ hT f
  filter_upwards [c5_physical_corrector_ergodic_average_ae Q χ x i f hf
    (hχ.mono fun _ h => h.1) hcoc, hχ] with ω hr hω
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hs := c5_corrector_ray_tendsto_zero (χ ω) hω.2 x i
  apply hs.congr'
  filter_upwards with n
  simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm] using (hr (n+1)).symm

/-- Squared-integrable stationary increments give square-integrable corrector values. -/
theorem c5_physical_corrector_value_memLp
    {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (hz : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q, χ ω 0 = 0)
    (hi : ∀ x y : Vec d, Integrable (fun ω : PhysicalField d L =>
      (euclideanNorm (χ ω x - χ ω y))^2) (physicalReferenceLaw Q)) :
    ∀ x : Vec d, MemLp (fun ω : PhysicalField d L => euclideanNorm (χ ω x))
      2 (physicalReferenceLaw Q) := by
  intro x
  have hc : Continuous (fun v : Vec d => euclideanNorm v) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i))
  have hm : Measurable (fun ω : PhysicalField d L => euclideanNorm (χ ω x)) :=
    hc.measurable.comp (hχ.comp (measurable_subtype_coe.prodMk measurable_const))
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  apply (hi x 0).congr
  filter_upwards [hz] with ω hω
  simp only [hω, sub_zero]

/-- Each coordinate of a square-integrable corrector value belongs to L². -/
theorem c5_physical_corrector_coordinate_memLp
    {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (hmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L => euclideanNorm (χ ω x))
      2 (physicalReferenceLaw Q)) (x : Vec d) (i : Fin d) :
    MemLp (fun ω : PhysicalField d L => χ ω x i) 2 (physicalReferenceLaw Q) := by
  have hm : Measurable (fun ω : PhysicalField d L => χ ω x i) :=
    (measurable_pi_apply i).comp (hχ.comp (measurable_subtype_coe.prodMk measurable_const))
  apply (hmem x).mono' hm.aestronglyMeasurable
  filter_upwards with ω
  simpa only [Real.norm_eq_abs] using Regeneration.coordinate_abs_le_euclideanNorm (χ ω x) i

/-- The squared normalized coordinate has vanishing mean along a fixed ray. -/
theorem c5_physical_corrector_coordinate_mean_tendsto_zero
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d) (x : Vec d) (i : Fin d)
    (f : Lp ℝ 2 (physicalReferenceLaw Q))
    (hf : (f : PhysicalField d L → ℝ) =ᵐ[physicalReferenceLaw Q] fun ω => χ ω x i)
    (hχ : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      χ ω 0 = 0 ∧ ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∀ z, euclideanNorm z ≤ (t+1)*R → euclideanNorm (χ ω z)/(t+1) ≤ ε)
    (hcoc : ∀ y : Vec d, ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      ∀ z : Vec d, χ (translate y ω.1) z = χ ω (y+z)-χ ω y) :
    Tendsto (fun n : ℕ => ∫ ω : PhysicalField d L,
      (χ ω (((n : ℝ)+1) • x) i / ((n : ℝ)+1))^2 ∂physicalReferenceLaw Q)
      atTop (𝓝 0) := by
  let g (n : ℕ) : Lp ℝ 2 (physicalReferenceLaw Q) :=
    birkhoffAverage ℝ (c5PhysicalTranslationOperator Q x) id (n+1) f
  have hg : Tendsto g atTop (𝓝 0) := by
    exact (tendsto_add_atTop_iff_nat 1).2
      (c5_physical_corrector_ergodic_average_tendsto_zero Q χ x i f hf hχ hcoc)
  have hn : Tendsto (fun n : ℕ => ‖g n‖^2) atTop (𝓝 0) := by
    simpa using (continuous_norm.continuousAt.tendsto.comp hg).pow 2
  apply hn.congr'
  filter_upwards with n
  have he := c5_physical_corrector_ergodic_average_ae Q χ x i f hf
    (hχ.mono fun _ h => h.1) hcoc
  have he' : (fun ω : PhysicalField d L => (g n ω)^2) =ᵐ[physicalReferenceLaw Q]
      fun ω => (χ ω (((n : ℝ)+1) • x) i / ((n : ℝ)+1))^2 := by
    filter_upwards [he] with ω hω
    simpa [g, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm] using
      congrArg (fun a : ℝ => a^2) (hω (n+1))
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using integral_congr_ae he'

/-- The canonical physical corrector has vanishing directional mean-square growth. -/
theorem exists_physical_corrector_directional_mean_sublinearity
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
    ∃ χ : FieldPair d → Vec d → Vec d,
    Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
    (∀ x : Vec d, MemLp (fun ω : ReductionImageV3.PhysicalField d L => euclideanNorm (χ ω x)) 2 (ReductionImageV3.physicalReferenceLaw Q)) ∧
    (∀ᵐ (ω : ReductionImageV3.PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
      Continuous (χ ω) ∧ χ ω 0 = 0 ∧ ∀ i : Fin d, ∀ R : ℝ, 0 < R →
        WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
          (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))).ofLp)) ∧
    ∀ x : Vec d, Tendsto (fun n : ℕ => ∫ ω : ReductionImageV3.PhysicalField d L,
      (euclideanNorm (χ ω (((n : ℝ)+1) • x))/((n : ℝ)+1))^2
      ∂ ReductionImageV3.physicalReferenceLaw Q) atTop (𝓝 0) := by
  obtain ⟨χ, hm, ha, hcoc, C, hC, hi⟩ :=
    exists_physical_l2_corrector_with_stationary_cocycle Q
  have hz : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q, χ ω 0 = 0 :=
    ha.mono fun _ h => h.2.1
  have hsub : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      χ ω 0 = 0 ∧ ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∀ z, euclideanNorm z ≤ (t+1)*R → euclideanNorm (χ ω z)/(t+1) ≤ ε :=
    ha.mono fun _ h => ⟨h.2.1, h.2.2.1⟩
  have hmem := c5_physical_corrector_value_memLp Q χ hm hz (fun x y => (hi x y).1)
  have hcoord := c5_physical_corrector_coordinate_memLp Q χ hm hmem
  refine ⟨χ, hm, hmem, ?_, ?_⟩
  · filter_upwards [ha] with ω h
    exact ⟨h.1, h.2.1, h.2.2.2.2⟩
  · intro x
    have ht (i : Fin d) : Tendsto (fun n : ℕ => ∫ ω : PhysicalField d L,
        (χ ω (((n : ℝ)+1) • x) i / ((n : ℝ)+1))^2 ∂physicalReferenceLaw Q)
        atTop (𝓝 0) := by
      let hf := hcoord x i
      exact c5_physical_corrector_coordinate_mean_tendsto_zero Q χ x i
        (hf.toLp _) hf.coeFn_toLp hsub hcoc
    have hs := tendsto_finset_sum Finset.univ (fun i _ => ht i)
    simp only [Finset.sum_const_zero] at hs
    apply hs.congr'
    filter_upwards with n
    have hint (i : Fin d) : Integrable (fun ω : PhysicalField d L =>
        (χ ω (((n : ℝ)+1) • x) i / ((n : ℝ)+1))^2) (physicalReferenceLaw Q) := by
      simpa only [Real.norm_eq_abs, sq_abs, div_eq_mul_inv] using
        ((hcoord (((n : ℝ)+1) • x) i).mul_const (((n : ℝ)+1)⁻¹)).norm.integrable_sq
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    apply integral_congr_ae
    filter_upwards with ω
    rw [div_pow, ← TimeChange.euclideanSq_eq_sq_euclideanNorm]
    simp only [euclideanSq, dot, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_two, div_mul_div_comm]

end EinsteinFull
