import EinsteinRelation.Regeneration.ForcedBitSlice
import EinsteinRelation.Probability.ProbabilityPart
import EinsteinRelation.Regeneration.CorrectedHalfSpaceIndependence
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini
import EinsteinRelation.Regeneration.BoundedMeasurableKilledFutureVersion

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration

open scoped Classical in
theorem c15_clean_integrable_spatial_kernel_average {d : ℕ} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : ProbabilityTheory.Kernel α β)
    (hκ : ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a))
    (i : Fin d) (R : ℝ) (hR : 0 < R) (X : β → Vec d) (hX : Measurable X)
    (G : α × β → ℝ) (hG : Measurable G) (hbG : BoundedRealTest G) :
    Integrable (fun p : Vec d × α => ∫ b, G (p.2, b) *
      (if p.1 ∈ endpointBall i R (X b) then 1 else 0) ∂κ p.2)
      (volume.prod μ) := by
  classical
  let κ' := Probability.probabilityPart κ
  let ρ := μ.compProd κ'
  have : IsProbabilityMeasure ρ :=
    Probability.isProbabilityMeasure_compProd_probabilityPart μ κ hκ
  let J : (α × β) × Vec d → ℝ := fun q =>
    (endpointBall i R (X q.1.2)).indicator (fun _ => G q.1) q.2
  have hJ : Measurable J := by
    apply (hG.comp measurable_fst).indicator
    exact (measurableSet_endpointBall_pair i R).preimage
      ((hX.comp measurable_fst.snd).prodMk measurable_snd)
  have hiJ : Integrable J (ρ.prod volume) :=
    integrable_endpointBall_indicator ρ i R hR (fun q => X q.2)
      (hX.comp measurable_snd) (fun q => G q.1) (hG.comp measurable_fst)
      (by obtain ⟨C, hC⟩ := hbG; exact ⟨C, fun q => hC q.1⟩)
  obtain ⟨C, hC⟩ := hbG
  have hbJ : ∀ q, ‖J q‖ ≤ max C 0 := by
    intro q
    by_cases hq : q.2 ∈ endpointBall i R (X q.1.2)
    · simpa only [J, Set.indicator_of_mem hq, Real.norm_eq_abs] using
        (hC q.1).trans (le_max_left C 0)
    · simpa only [J, Set.indicator_of_notMem hq, norm_zero] using le_max_right C 0
  let A : Vec d × α → ℝ := fun p => ∫ b, J ((p.2, b), p.1) ∂κ' p.2
  have hA : StronglyMeasurable A := by
    exact (hJ.stronglyMeasurable.comp_measurable
      ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)).integral_kernel_prod_right'
        (κ := κ'.comap Prod.snd measurable_snd)
  have hiJy : ∀ y, Integrable (fun q : α × β => J (q, y)) ρ := fun y =>
    Integrable.of_bound (hJ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (max C 0) (Filter.Eventually.of_forall fun q => hbJ (q, y))
  have hiNy : ∀ y, Integrable (fun a => ∫ b, ‖J ((a, b), y)‖ ∂κ' a) μ :=
    fun y => ((Measure.integrable_compProd_iff (hiJy y).aestronglyMeasurable).mp (hiJy y)).2
  have hiAy : ∀ y, Integrable (fun a => A (y, a)) μ := by
    intro y
    apply (hiNy y).mono' (hA.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun a => norm_integral_le_integral_norm _
  have hiA : Integrable A (volume.prod μ) := by
    apply (integrable_prod_iff hA.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hiAy, ?_⟩
    apply hiJ.norm.integral_prod_right.mono'
      hA.norm.integral_prod_right'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (A (y, a)))),
      Measure.integral_compProd (hiJy y).norm]
    exact integral_mono (hiAy y).norm (hiNy y)
      (fun a => norm_integral_le_integral_norm _)
  apply hiA.congr
  have hae := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d))) (ν := μ)).ae
    (Probability.probabilityPart_ae_eq μ κ hκ)
  filter_upwards [hae] with p hp
  change (∫ b, J ((p.2, b), p.1) ∂κ' p.2) = _
  rw [show κ' p.2 = κ p.2 from hp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    by_cases hb : p.1 ∈ endpointBall i R (X b) <;> simp [J, hb]

open scoped Classical in
theorem c15_clean_spatial_kernel_average_integral {d : ℕ} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : ProbabilityTheory.Kernel α β)
    (hκ : ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a))
    (i : Fin d) (R : ℝ) (hR : 0 < R) (X : β → Vec d) (hX : Measurable X)
    (G : α × β → ℝ) (hG : Measurable G) (hbG : BoundedRealTest G) :
    (∫ y, ∫ a, ∫ b, G (a, b) *
      (if y ∈ endpointBall i R (X b) then 1 else 0) ∂κ a ∂μ) =
      (volume (endpointBall i R 0)).toReal * ∫ a, ∫ b, G (a, b) ∂κ a ∂μ := by
  classical
  let ρ := μ.compProd (Probability.probabilityPart κ)
  have : IsProbabilityMeasure ρ :=
    Probability.isProbabilityMeasure_compProd_probabilityPart μ κ hκ
  let J : (α × β) × Vec d → ℝ := fun q =>
    (endpointBall i R (X q.1.2)).indicator (fun _ => G q.1) q.2
  have hJ : Measurable J := by
    apply (hG.comp measurable_fst).indicator
    exact (measurableSet_endpointBall_pair i R).preimage
      ((hX.comp measurable_fst.snd).prodMk measurable_snd)
  have hiJ : Integrable J (ρ.prod volume) :=
    integrable_endpointBall_indicator ρ i R hR (fun q => X q.2)
      (hX.comp measurable_snd) (fun q => G q.1) (hG.comp measurable_fst)
      (by obtain ⟨C, hC⟩ := hbG; exact ⟨C, fun q => hC q.1⟩)
  obtain ⟨C, hC⟩ := hbG
  have hbJ : ∀ y, BoundedRealTest (fun q : α × β => J (q, y)) := by
    intro y
    refine ⟨max C 0, fun q => ?_⟩
    by_cases hq : y ∈ endpointBall i R (X q.2)
    · simpa only [J, Set.indicator_of_mem hq] using
        (hC q).trans (le_max_left C 0)
    · simpa only [J, Set.indicator_of_notMem hq, abs_zero] using le_max_right C 0
  have hiter : ∀ y, (∫ q, J (q, y) ∂ρ) =
      ∫ a, ∫ b, G (a, b) *
        (if y ∈ endpointBall i R (X b) then 1 else 0) ∂κ a ∂μ := by
    intro y
    calc
      _ = ∫ a, ∫ b, J ((a, b), y) ∂κ a ∂μ :=
        Probability.integral_compProd_probabilityPart μ κ hκ (fun q => J (q, y))
          (hJ.comp (measurable_id.prodMk measurable_const)) (hbJ y)
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a => integral_congr_ae
          (Filter.Eventually.of_forall fun b => by
            by_cases hb : y ∈ endpointBall i R (X b) <;> simp [J, hb])
  calc
    _ = ∫ y, ∫ q, J (q, y) ∂ρ := integral_congr_ae
      (Filter.Eventually.of_forall fun y => (hiter y).symm)
    _ = ∫ q, ∫ y, J (q, y) ∂volume ∂ρ := (integral_integral_swap hiJ).symm
    _ = ∫ q, (volume (endpointBall i R 0)).toReal * G q ∂ρ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      have hball : MeasurableSet (endpointBall i R (X q.2)) :=
        (measurableSet_endpointBall_pair i R).preimage
          (measurable_const.prodMk measurable_id)
      simp only [J, integral_indicator hball, integral_const, smul_eq_mul,
        Measure.real, Measure.restrict_apply_univ, endpointBall_volume_eq]
    _ = (volume (endpointBall i R 0)).toReal * ∫ q, G q ∂ρ := integral_const_mul _ _
    _ = _ := by
      rw [Probability.integral_compProd_probabilityPart μ κ hκ G hG ⟨C, hC⟩]



open scoped Classical in
/-- The event endpoint past kernel is integrable and has the expected mass. -/
theorem c15_clean_burn_spatial_past_integrable_mass {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K) (Δ : ℝ≥0)
    (R : ℝ) (hR : 0 < R) (i : Fin d) (m k : ℕ)
    (E : Set (Regeneration.CoupledSample d)) (hE : MeasurableSet E) :
    Integrable (fun p : Vec d × FieldPair d => ∫ z,
      ((E).indicator (fun _ => (1 : ℝ))) z *
      (if p.1 ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0)
      ∂K (0, p.2)) (volume.prod Q.measure) ∧
    (∫ y, ∫ ω, ∫ z,
      ((E).indicator (fun _ => (1 : ℝ))) z *
      (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0)
      ∂K (0, ω) ∂Q.measure) =
    (volume (Regeneration.endpointBall i R 0)).toReal *
      ∫ ω, ∫ z, ((E).indicator
        (fun _ => (1 : ℝ))) z ∂K (0, ω) ∂Q.measure := by
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    (E).indicator (fun _ => (1 : ℝ)) q.2
  have hG : Measurable G := (measurable_const.indicator
    hE).comp measurable_snd
  have hbG : Regeneration.BoundedRealTest G := by
    refine ⟨1, fun q => ?_⟩
    by_cases hq : q.2 ∈ E <;> simp [G, hq]
  let X : Regeneration.CoupledSample d → Vec d := fun z =>
    z.1 (((m + k : ℕ) : ℝ≥0) * Δ)
  have hX : Measurable X := (continuous_eval_const _).measurable.comp measurable_fst
  have hi := c15_clean_integrable_spatial_kernel_average Q.measure
    (Regeneration.originCoupledLaw K) hK.1 i R hR X hX G hG hbG
  have hm := c15_clean_spatial_kernel_average_integral Q.measure
    (Regeneration.originCoupledLaw K) hK.1 i R hR X hX G hG hbG
  exact ⟨hi, hm⟩



open scoped Classical in
theorem c15_clean_burn_prebridge_finite_range {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d) (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (m k : ℕ) (E : Set (Regeneration.CoupledSample d)) (H : Regeneration.CoupledSample d → ℝ) (Φ : Regeneration.FutureState d i R → ℝ) (y : Vec d) (hgap : r₀ < 2 * R) (hApast : ∃ A : FieldPair d → ℝ, Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧ (fun ω => ∫ z, ((E).indicator H) z * (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, ω)) =ᵐ[Q.measure] A) (hBfuture : ∃ B : FieldPair d → ℝ, Measurable[localSigma {x : Vec d | y i - 2 * R ≤ x i}] B ∧ (fun ω => ∫ z, Regeneration.killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)) =ᵐ[Q.measure] B) : (∫ ω, (fun ω => ∫ z, ((E).indicator H) z * (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, ω)) ω * (fun ω => ∫ z, Regeneration.killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)) ω ∂Q.measure) = (∫ ω, (fun ω => ∫ z, ((E).indicator H) z * (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, ω)) ω ∂Q.measure) * ∫ ω, (fun ω => ∫ z, Regeneration.killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)) ω ∂Q.measure := by
  obtain ⟨A, hA, hAe⟩ := hApast
  obtain ⟨B, hB, hBe⟩ := hBfuture
  exact Regeneration.integral_mul_eq_of_corrected_halfSpace_versions Q i (y i) R hgap
    _ _ A B hA hB hAe hBe


open scoped Classical in
/-- The measurable event past and killed future factorize for almost every endpoint. -/
theorem c15_clean_burn_prebridge_finite_range_ae {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (m k : ℕ)
    (E : Set (Regeneration.CoupledSample d))
    (H : Regeneration.CoupledSample d → ℝ) (Φ : Regeneration.FutureState d i R → ℝ)
    (hgap : r₀ < 2 * R)
    (hApast : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧
      (fun ω => ∫ z, ((E).indicator H) z *
        (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0)
        ∂K (0, ω)) =ᵐ[Q.measure] A)
    (hBfuture : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ B : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | y i - 2 * R ≤ x i}] B ∧
      (fun ω => ∫ z, Regeneration.killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω))
        =ᵐ[Q.measure] B) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, (∫ z, ((E).indicator H) z *
        (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0)
        ∂K (0, ω)) *
        (∫ z, Regeneration.killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
      (∫ ω, ∫ z, ((E).indicator H) z *
        (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0)
        ∂K (0, ω) ∂Q.measure) *
      (∫ ω, ∫ z, Regeneration.killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω) ∂Q.measure) := by
  filter_upwards [hApast, hBfuture] with y hA hB
  exact c15_clean_burn_prebridge_finite_range Q K Δ R i m k E H Φ y hgap hA hB


open scoped Classical in
/-- Spatially integrated finite-range lower bound for the event past. -/
theorem c15_clean_burn_spatial_factor_lower {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K) (Δ : ℝ≥0)
    (R : ℝ) (hR : 0 < R) (i : Fin d) (m k : ℕ)
    (E : Set (Regeneration.CoupledSample d))
    (hE : MeasurableSet E)
    (hgap : r₀ < 2 * R) (η : ℝ)
    (hmean : ∀ᵐ y ∂(volume : Measure (Vec d)), η ≤
      ∫ ω, ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω) ∂Q.measure)
    (hApast : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧
      (fun ω => ∫ z, ((E).indicator
        (fun _ => (1 : ℝ))) z *
        (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0)
        ∂K (0, ω)) =ᵐ[Q.measure] A)
    (hBfuture : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ B : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | y i - 2 * R ≤ x i}] B ∧
      (fun ω => ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω)) =ᵐ[Q.measure] B)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B)
    (hbB : Regeneration.BoundedRealTest B)
    (hBe : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) (p, z) ∂K p) :
    η * ((volume (Regeneration.endpointBall i R 0)).toReal *
      ∫ ω, ∫ z, ((E).indicator
        (fun _ => (1 : ℝ))) z ∂K (0, ω) ∂Q.measure) ≤
    ∫ y, ∫ ω, (∫ z, ((E).indicator
      (fun _ => (1 : ℝ))) z *
      (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0)
      ∂K (0, ω)) * B (y, ω) ∂Q.measure := by
  let P : Vec d × FieldPair d → ℝ := fun p => ∫ z,
    ((E).indicator (fun _ => (1 : ℝ))) z *
    (if p.1 ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0)
    ∂K (0, p.2)
  obtain ⟨hiP, hmass⟩ := c15_clean_burn_spatial_past_integrable_mass Q K hK Δ R hR i m k E hE
  change Integrable P (volume.prod Q.measure) at hiP
  have hiPB : Integrable (fun p => P p * B p) (volume.prod Q.measure) := by
    obtain ⟨C, hC⟩ := hbB
    exact hiP.mul_bdd hB.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hC p)
  have hfac := c15_clean_burn_prebridge_finite_range_ae Q K Δ R i m k E
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) hgap hApast hBfuture
  have hBe' := Measure.ae_ae_of_ae_prod hBe
  have hnonneg : ∀ p, 0 ≤ P p := by
    intro p
    apply integral_nonneg
    intro z
    apply mul_nonneg
    · by_cases hz : z ∈ E <;> simp [hz]
    · split_ifs <;> norm_num
  have hcmp : ∀ᵐ y ∂(volume : Measure (Vec d)),
      η * (∫ ω, P (y, ω) ∂Q.measure) ≤ ∫ ω, P (y, ω) * B (y, ω) ∂Q.measure := by
    filter_upwards [hmean, hfac, hBe'] with y hy hf he
    have heq : (∫ ω, P (y, ω) * B (y, ω) ∂Q.measure) =
        ∫ ω, P (y, ω) * (∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ))
          ((y, ω), z) ∂K (y, ω)) ∂Q.measure := by
      apply integral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]
    rw [heq, hf]
    change η * (∫ ω, P (y, ω) ∂Q.measure) ≤
      (∫ ω, P (y, ω) ∂Q.measure) *
        (∫ ω, ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ))
          ((y, ω), z) ∂K (y, ω) ∂Q.measure)
    have hp : 0 ≤ ∫ ω, P (y, ω) ∂Q.measure :=
      integral_nonneg fun ω => hnonneg (y, ω)
    have hm := mul_le_mul_of_nonneg_left hy hp
    rwa [mul_comm _ η] at hm
  have hle := integral_mono_ae (hiP.integral_prod_left.const_mul η)
    hiPB.integral_prod_left hcmp
  rw [integral_const_mul] at hle
  rw [hmass] at hle
  exact hle

open scoped Classical in
theorem c15_clean_burn_endpoint_average_lower_of_local_versions {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q.measure K) (Δ : ℝ≥0) (R : ℝ) (hR : 0 < R) (i : Fin d) (m k : ℕ) (E : Set (Regeneration.CoupledSample d)) (hE : MeasurableSet E) (hgap : r₀ < 2 * R) (η : ℝ) (hmean : ∀ᵐ y ∂(volume : Measure (Vec d)), η ≤ ∫ ω, (fun p : Vec d × FieldPair d => ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) (p, z) ∂K p) (y, ω) ∂Q.measure) (hApast : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ, Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧ (fun ω => (fun p : Vec d × FieldPair d => ∫ z, ((E).indicator (fun _ => (1 : ℝ))) z * (if p.1 ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, p.2)) (y, ω)) =ᵐ[Q.measure] A) (hBfuture : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ B : FieldPair d → ℝ, Measurable[localSigma {x : Vec d | y i - 2 * R ≤ x i}] B ∧ (fun ω => (fun p : Vec d × FieldPair d => ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) (p, z) ∂K p) (y, ω)) =ᵐ[Q.measure] B) : η * (∫ ω, ∫ z, ((E).indicator (fun _ => (1 : ℝ))) z ∂K (0, ω) ∂Q.measure) ≤ ∫ ω, ∫ z, ((E).indicator (fun _ => (1 : ℝ))) z * Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => (fun p : Vec d × FieldPair d => ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) (p, z) ∂K p) (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  obtain ⟨C, _, B, hB, hbB, _, hBp⟩ :=
    Regeneration.exists_globally_bounded_measurable_killed_future_version
      Q.measure K hK R i (fun _ => (1 : ℝ)) measurable_const
      ⟨1, by intro p; simp⟩
  have hBp' : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) (p, z) ∂K p := by
    filter_upwards [hBp] with p hp
    simpa only [Regeneration.killedFutureTest, Regeneration.spatialFutureRecord] using hp
  let G : Regeneration.CoupledSample d → ℝ :=
    (E).indicator (fun _ => (1 : ℝ))
  have hG : Measurable G := measurable_const.indicator
    hE
  have hbG : Regeneration.BoundedRealTest G := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ E <;> simp [G, hz]
  have hsp := c15_clean_burn_spatial_factor_lower Q K hK Δ R hR i m k
    E hE hgap η hmean hApast hBfuture B hB ⟨C, hbB⟩ hBp'
  have hfub := Regeneration.integral_annealed_endpointAverage_fubini Q.measure K hK
    Δ (m + k) i R hR G hG hbG B hB ⟨C, hbB⟩
  have hs := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hBp')
  have heq : (∫ ω, ∫ z, G z * Regeneration.endpointAverage i R
      (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, ω)) ∂K (0, ω) ∂Q.measure) =
      ∫ ω, ∫ z, G z * Regeneration.endpointAverage i R
      (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
        (fun y => ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ))
          ((y, ω), z) ∂K (y, ω)) ∂K (0, ω) ∂Q.measure := by
    apply integral_congr_ae
    filter_upwards [hs] with ω hω
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    unfold Regeneration.endpointAverage
    congr 1
    apply integral_congr_ae
    exact ae_restrict_of_ae hω
  have hV : 0 < (volume (Regeneration.endpointBall i R (0 : Vec d))).toReal :=
    ENNReal.toReal_pos (Regeneration.endpointBall_volume_pos i R hR 0).ne'
      (Regeneration.endpointBall_volume_ne_top i R hR 0)
  have hm := mul_le_mul_of_nonneg_left hsp (inv_nonneg.mpr hV.le)
  have hnorm : (volume (Regeneration.endpointBall i R (0 : Vec d))).toReal⁻¹ *
      (η * ((volume (Regeneration.endpointBall i R (0 : Vec d))).toReal *
        ∫ ω, ∫ z, G z ∂K (0, ω) ∂Q.measure)) =
      η * (∫ ω, ∫ z, G z ∂K (0, ω) ∂Q.measure) := by
    field_simp
  change _ ≤ _ at hm
  rw [hnorm, ← hfub, heq] at hm
  exact hm


open scoped Classical in
theorem c15_clean_literal_burn_endpoint_lower {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q.measure K) (Δ : ℝ≥0) (_hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m J N k : ℕ) (hE : MeasurableSet ({z : Regeneration.CoupledSample d |
    let w := Regeneration.forceSampleBit k
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))
    let S := Regeneration.trialStartSequence Δ lam R w i J
    Regeneration.trialStartSequence Δ lam R w i (J + N) =
      ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
    S ≠ ⊤ ∧ z.1 0 i + Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) ≤
      z.1 ((m : ℝ≥0) * Δ + (S.toNNReal - Δ)) i + R})) (hgap : r₀ < 2 * R) (η : ℝ) (_hη : 0 ≤ η) (_hη1 : η ≤ 1) (hmean : ∀ᵐ y ∂(volume : Measure (Vec d)), η ≤ ∫ ω, (fun p : Vec d × FieldPair d => ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) (p, z) ∂K p) (y, ω) ∂Q.measure) (hApast : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ, Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧ (fun ω => (fun p : Vec d × FieldPair d => ∫ z, (({z : Regeneration.CoupledSample d |
    let w := Regeneration.forceSampleBit k
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))
    let S := Regeneration.trialStartSequence Δ lam R w i J
    Regeneration.trialStartSequence Δ lam R w i (J + N) =
      ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
    S ≠ ⊤ ∧ z.1 0 i + Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) ≤
      z.1 ((m : ℝ≥0) * Δ + (S.toNNReal - Δ)) i + R}).indicator (fun _ => (1 : ℝ))) z * (if p.1 ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, p.2)) (y, ω)) =ᵐ[Q.measure] A) (hBfuture : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ B : FieldPair d → ℝ, Measurable[localSigma {x : Vec d | y i - 2 * R ≤ x i}] B ∧ (fun ω => (fun p : Vec d × FieldPair d => ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) (p, z) ∂K p) (y, ω)) =ᵐ[Q.measure] B) : η * (∫ ω, ∫ z, (({z : Regeneration.CoupledSample d |
    let w := Regeneration.forceSampleBit k
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))
    let S := Regeneration.trialStartSequence Δ lam R w i J
    Regeneration.trialStartSequence Δ lam R w i (J + N) =
      ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
    S ≠ ⊤ ∧ z.1 0 i + Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) ≤
      z.1 ((m : ℝ≥0) * Δ + (S.toNNReal - Δ)) i + R}).indicator (fun _ => (1 : ℝ))) z ∂K (0, ω) ∂Q.measure) ≤ ∫ ω, ∫ z, (({z : Regeneration.CoupledSample d |
    let w := Regeneration.forceSampleBit k
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))
    let S := Regeneration.trialStartSequence Δ lam R w i J
    Regeneration.trialStartSequence Δ lam R w i (J + N) =
      ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
    S ≠ ⊤ ∧ z.1 0 i + Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) ≤
      z.1 ((m : ℝ≥0) * Δ + (S.toNNReal - Δ)) i + R}).indicator (fun _ => (1 : ℝ))) z * Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => (fun p : Vec d × FieldPair d => ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) (p, z) ∂K p) (y, ω)) ∂K (0, ω) ∂Q.measure := by
  exact c15_clean_burn_endpoint_average_lower_of_local_versions Q K hK Δ R hR i m k
    ({z : Regeneration.CoupledSample d |
    let w := Regeneration.forceSampleBit k
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))
    let S := Regeneration.trialStartSequence Δ lam R w i J
    Regeneration.trialStartSequence Δ lam R w i (J + N) =
      ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
    S ≠ ⊤ ∧ z.1 0 i + Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) ≤
      z.1 ((m : ℝ≥0) * Δ + (S.toNNReal - Δ)) i + R}) hE hgap η hmean hApast hBfuture

end EinsteinFull.Blueprint
