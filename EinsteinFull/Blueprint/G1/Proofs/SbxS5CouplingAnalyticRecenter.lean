import EinsteinFull.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinRelation.Regeneration.RenewalCarriers
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Tactic.Linter

/-!
# Analytic clauses of spatially conjugated GMP couplings

Source `paper/main.tex:1510–1516`. The endpoint identity is transported
with both origin and product qualifiers. The one-interval helper transports
all five integrability clauses and both identities from the exact bridge map.
The supplied GMP realization gives probability simultaneously at every start.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Regeneration.Renewal

/-- Evaluation of the shared conjugated path kernel at literal coordinates. -/
theorem sbxS5_analyticRecenterPaths_apply {d : ℕ} (y x : Vec d)
    (P : QuenchedPathLaws d) (η : FieldPair d) :
    sbxS9RecenteredPathLaws P y (x, η) =
      (P (y + x, translate (-y) η)).map (recenterPathEquiv y) := by
  rw [sbxS9RecenteredPathLaws_apply]
  rfl

/-- Evaluation of the shared conjugated coupled kernel at literal coordinates. -/
theorem sbxS5_analyticRecenterCoupling_apply {d : ℕ} (y x : Vec d)
    (K : CoupledQuenchedLaws d) (η : FieldPair d) :
    sbxS9RecenteredCoupledLaws K y (x, η) =
      (K (y + x, translate (-y) η)).map (recenterSampleEquiv y) := by
  rw [sbxS9RecenteredCoupledLaws_apply]
  rfl

/-- Translation of the actual Euclidean endpoint average, including its volume. -/
theorem sbxS5_endpointAverage_recenter {d : ℕ} (y x : Vec d) (i : Fin d)
    (R : ℝ) (φ : Vec d → ℝ) :
    endpointAverage i R (x - y) φ =
      endpointAverage i R x (fun v => φ (v - y)) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-y)
  have hv : (volume : Measure (Vec d)).map e = volume :=
    (measurePreserving_add_right volume (-y)).map_eq
  have hB : e ⁻¹' endpointBall i R (x - y) = endpointBall i R x := by
    ext v
    exact sub_mem_endpointBall_iff i R y v x
  have hm : volume (endpointBall i R (x - y)) =
      volume (endpointBall i R x) := by
    calc
      _ = (volume.map e) (endpointBall i R (x - y)) := by rw [hv]
      _ = _ := by rw [e.measurableEmbedding.map_apply, hB]
  unfold endpointAverage
  rw [hm]
  congr 1
  calc
    _ = ∫ v in endpointBall i R (x - y), φ v ∂(volume.map e) := by rw [hv]
    _ = _ := by rw [e.restrict_map, hB, integral_map_equiv]; rfl

/-- The uniform endpoint clause is preserved at each translated input. -/
theorem sbxS5_uniformSuccessfulEndpointAt_recenter {d : ℕ}
    (y x : Vec d) (η : FieldPair d) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d)
    (hK : UniformSuccessfulEndpointAt Δ δ R i K (y + x, translate (-y) η)) :
    UniformSuccessfulEndpointAt Δ δ R i (sbxS9RecenteredCoupledLaws K y) (x, η) := by
  intro n H φ hH hHb hφ hφb
  obtain ⟨CH, hCH⟩ := hHb
  obtain ⟨Cφ, hCφ⟩ := hφb
  have h := hK n (fun z => H (recenterSample y z)) (fun v => φ (v - y))
    (measurable_finiteHistory_comp_recenter Δ n y H hH)
    ⟨CH, fun z => hCH _⟩ (hφ.comp (measurable_id.sub measurable_const))
    ⟨Cφ, fun v => hCφ _⟩
  rw [sbxS5_analyticRecenterCoupling_apply]
  simp only [integral_map_equiv, recenterSampleEquiv_apply, recenterSample,
    ContinuousMap.coe_mk, sbxS5_endpointAverage_recenter]
  exact h

/-- A product-a.e. clause gives a common spatial good set for origin and
product inputs. The origin fibre is obtained by Fubini before stationarity. -/
theorem sbxS5_recenter_input_ae {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {S : Vec d × FieldPair d → Prop}
    (hS : ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q.measure), S xω) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q.measure, S (y, translate (-y) η)) ∧
      ∀ᵐ xη ∂((volume : Measure (Vec d)).prod Q.measure),
        S (y + xη.1, translate (-y) xη.2) := by
  simpa only [sbxS9RecenterInput, add_zero] using
    sbxS9_ae_recenterInput Q.measure Q.stationary hS

/-- Both required endpoint qualifiers hold on one spatial good set. -/
theorem sbxS5_hasUniformSuccessfulEndpoint_recenter {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d)
    (hK : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      HasUniformSuccessfulEndpoint Q.measure Δ δ R i (sbxS9RecenteredCoupledLaws K y) := by
  filter_upwards [sbxS5_recenter_input_ae Q hK.2] with y hy
  constructor
  · filter_upwards [hy.1] with η hη
    apply sbxS5_uniformSuccessfulEndpointAt_recenter y 0 η Δ δ R i K
    simpa only [add_zero] using hη
  · filter_upwards [hy.2] with xη hxη
    exact sbxS5_uniformSuccessfulEndpointAt_recenter y xη.1 xη.2 Δ δ R i K hxη

/-- The all-start realization supplies probability at every start on the
same environment good set, as required by the RN bridge transport. -/
theorem sbxS5_probability_all_starts_of_gmp {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)) := by
  filter_upwards [hP] with ω hω
  obtain ⟨hreg, r, hr⟩ := hω
  intro x
  rw [hr x]
  have := r.pathLaw_isMarkovKernel
  infer_instance

/-- Source `paper/main.tex:400–402`: the actual killed bridge mixture commutes with spatial translation, including its endpoint Radon--Nikodym reweighting. -/
theorem sbxS5_map_recenter_killedBridgeMixture {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P P' : QuenchedPathLaws d) (a x : Vec d) (ω ω' : FieldPair d)
    [IsProbabilityMeasure (P (a + x, ω))]
    (heq : (P (a + x, ω)).map (recenterPathEquiv a) = P' (x, ω')) :
    (Renewal.killedBridgeMixture Δ R i P (a + x) ω).map (recenterPathEquiv a) =
      Renewal.killedBridgeMixture Δ R i P' x ω' := by
  let p := recenterPathEquiv a
  let q : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-a)
  let ev : Path d → Vec d := fun γ => γ Δ
  have hev : Measurable ev := (continuous_eval_const Δ).measurable
  let μ := Renewal.killedSegmentLaw Δ R i P (a + x) ω
  let ν := Renewal.killedSegmentLaw Δ R i P' x ω'
  let η := cond (volume : Measure (Vec d)) (endpointBall i R (a + x))
  let η' := cond (volume : Measure (Vec d)) (endpointBall i R x)
  have : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure
    ((P (a + x, ω)).restrict _))
  have hset : p ⁻¹' {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R x} =
      {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R (a + x)} := by
    ext γ
    change (∀ t : ℝ≥0, t ≤ Δ → euclideanNorm (γ t - a - (x + (5 * R) • unitVector i)) < 6 * R) ↔ _
    have ha : ∀ t, γ t - a - (x + (5 * R) • unitVector i) =
        γ t - (a + x + (5 * R) • unitVector i) := by intro t; abel
    simp only [ha]
    rfl
  have hk : μ.map p = ν := by
    dsimp [μ, ν, Renewal.killedSegmentLaw]
    rw [← heq, p.restrict_map, hset]
  have hv : (volume : Measure (Vec d)).map q = volume :=
    (measurePreserving_add_right volume (-a)).map_eq
  have hB : q ⁻¹' endpointBall i R x = endpointBall i R (a + x) := by
    ext y
    change (euclideanNorm (y + -a - (x + (9 * R) • unitVector i)) < R) ↔ _
    have ha : y + -a - (x + (9 * R) • unitVector i) =
        y - (a + x + (9 * R) • unitVector i) := by abel
    rw [ha]
    rfl
  have hη : η.map q = η' := by
    have hmass : (volume : Measure (Vec d)) (endpointBall i R (a + x)) =
        volume (endpointBall i R x) := by
      rw [← hB, ← q.measurableEmbedding.map_apply, hv]
    dsimp [η, η', ProbabilityTheory.cond]
    rw [Measure.map_smul, hmass, ← hB, ← q.restrict_map, hv]
    exact q.measurable.aemeasurable
  have hend : (μ.map ev).map q = ν.map ev := by
    rw [← hk, Measure.map_map hev p.measurable, Measure.map_map q.measurable hev]
    rfl
  have hrn := q.measurableEmbedding.rnDeriv_map η (μ.map ev)
  rw [hη, hend] at hrn
  have hpath := ae_of_ae_map hev.aemeasurable hrn
  have hweight : (fun γ : Path d => (η'.rnDeriv (ν.map ev)) (ev (p γ))) =ᵐ[μ]
      (fun γ => (η.rnDeriv (μ.map ev)) (ev γ)) := by
    filter_upwards [hpath] with γ hγ
    change (η'.rnDeriv (ν.map ev)) (γ Δ - a) = (η.rnDeriv (μ.map ev)) (γ Δ)
    exact hγ
  change (μ.withDensity (fun γ => (η.rnDeriv (μ.map ev)) (ev γ))).map p =
    ν.withDensity (fun γ => (η'.rnDeriv (ν.map ev)) (ev γ))
  rw [withDensity_congr_ae hweight.symm]
  have ht : (μ.withDensity (fun γ => (η'.rnDeriv (ν.map ev)) (ev (p γ)))).map p =
      (μ.map p).withDensity (fun γ => (η'.rnDeriv (ν.map ev)) (ev γ)) := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply p.measurable hs,
      withDensity_apply _ (p.measurable hs), withDensity_apply _ hs]
    exact (setLIntegral_map (f := fun γ => (η'.rnDeriv (ν.map ev)) (ev γ))
      hs ((Measure.measurable_rnDeriv _ _).comp hev) p.measurable).symm
  simpa only [hk] using ht

/-- Transport all five integrability statements and both branch identities.
The path map is fixed by the shared kernel definition. The actual
`map_recenter_killedBridgeMixture` must discharge the explicit bridge-map hypothesis;
this support lemma does not assert the complete analytic coupling transport. -/
theorem sbxS5_oneIntervalKernelAt_of_recenter_maps {d : ℕ}
    (y x : Vec d) (η : FieldPair d) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hbridge : ∀ z : Vec d,
      (killedBridgeMixture Δ R i P z (translate (-y) η)).map (recenterPathEquiv y) =
        killedBridgeMixture Δ R i (sbxS9RecenteredPathLaws P y) (z - y) η)
    (hK : OneIntervalKernelAt Δ δ R i P K (y + x, translate (-y) η)) :
    OneIntervalKernelAt Δ δ R i (sbxS9RecenteredPathLaws P y)
      (sbxS9RecenteredCoupledLaws K y) (x, η) := by
  intro n H F hH hHb hF hFb hseg
  obtain ⟨CH, hCH⟩ := hHb
  obtain ⟨CF, hCF⟩ := hFb
  have h := hK n (fun z => H (recenterSample y z))
    (fun γ => F (recenterPathEquiv y γ))
    (measurable_finiteHistory_comp_recenter Δ n y H hH)
    ⟨CH, fun z => hCH _⟩ (hF.comp (recenterPathEquiv y).measurable)
    ⟨CF, fun γ => hCF _⟩ (by
      intro γ γ' heq
      apply hseg
      intro t ht
      change γ t - y = γ' t - y
      rw [heq t ht])
  have hpath (z : Vec d) :
      (∫ γ, F γ ∂sbxS9RecenteredPathLaws P y (z - y, η)) =
        ∫ γ, F (recenterPathEquiv y γ) ∂P (z, translate (-y) η) := by
    rw [sbxS5_analyticRecenterPaths_apply,
      show y + (z - y) = z by abel, integral_map_equiv]
  have hmix (z : Vec d) :
      (∫ γ, F γ ∂killedBridgeMixture Δ R i
        (sbxS9RecenteredPathLaws P y) (z - y) η) =
      ∫ γ, F (recenterPathEquiv y γ) ∂killedBridgeMixture Δ R i P z
        (translate (-y) η) := by
    rw [← hbridge z, integral_map_equiv]
  have hshift (z : CoupledSample d) (t : ℝ≥0) :
      pathTimeShift (recenterSample y z).1 t =
        recenterPathEquiv y (pathTimeShift z.1 t) := by
    ext u j
    rfl
  have hstart (z : CoupledSample d) (t : ℝ≥0) :
      (recenterSample y z).1 t = z.1 t - y := rfl
  have hbits (z : CoupledSample d) : (recenterSample y z).2 = z.2 := rfl
  rw [sbxS5_analyticRecenterCoupling_apply]
  simpa only [integrable_map_equiv, integral_map_equiv, Function.comp_def,
    recenterSampleEquiv_apply, hshift, hstart, hbits, hpath, hmix] using h

/-- The actual killed-bridge map discharges both one-interval branches,
including their five integrability conditions, without a bridge-map premise. -/
theorem sbxS5_oneIntervalKernelAt_recenter {d : ℕ}
    (y x : Vec d) (η : FieldPair d) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hprob : ∀ z : Vec d, IsProbabilityMeasure (P (z, translate (-y) η)))
    (hK : OneIntervalKernelAt Δ δ R i P K (y + x, translate (-y) η)) :
    OneIntervalKernelAt Δ δ R i (sbxS9RecenteredPathLaws P y)
      (sbxS9RecenteredCoupledLaws K y) (x, η) := by
  apply sbxS5_oneIntervalKernelAt_of_recenter_maps y x η Δ δ R i P K _ hK
  intro z
  have := hprob (y + (z - y))
  have heq := (sbxS5_analyticRecenterPaths_apply y (z - y) P η).symm
  have h := sbxS5_map_recenter_killedBridgeMixture Δ R i P
    (sbxS9RecenteredPathLaws P y) y (z - y) (translate (-y) η) η heq
  simpa only [show y + (z - y) = z by abel] using h

/-- The supplied all-start GMP witnesses and stationarity give the full
one-interval clause at the new origin and product-a.e. on one spatial good set. -/
theorem sbxS5_hasOneIntervalKernel_recenter {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (hK : HasOneIntervalKernel Q.measure Δ δ R i P K) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      HasOneIntervalKernel Q.measure Δ δ R i
        (sbxS9RecenteredPathLaws P y) (sbxS9RecenteredCoupledLaws K y) := by
  filter_upwards [sbxS5_recenter_input_ae Q hK.2] with y hy
  have hmp : MeasurePreserving (translate (-y)) Q.measure Q.measure :=
    ⟨EinsteinRelation.Probability.measurable_translate (-y), Q.stationary (-y)⟩
  have hprob := hmp.quasiMeasurePreserving.ae
    (sbxS5_probability_all_starts_of_gmp hd hΛ₀ Q lam h0 h1 P hP)
  constructor
  · filter_upwards [hy.1, hprob] with η hη hpη
    apply sbxS5_oneIntervalKernelAt_recenter y 0 η Δ δ R i P K hpη
    simpa only [add_zero] using hη
  · have hprod := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Vec d))) (ν := Q.measure)).ae hprob
    filter_upwards [hy.2, hprod] with xη hxη hpη
    exact sbxS5_oneIntervalKernelAt_recenter y xη.1 xη.2 Δ δ R i P K hpη hxη

/-- Seven clauses of the actual recentered coupling on a common spatial good
set. The GMP realization clause is a separate obligation: this theorem does
not assert `IsGMPCouplingV2` or the factorization independence result. -/
theorem sbxS5_seven_coupling_clauses_recenter {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0 h1 P K) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      HasProbabilityLaws Q.measure (sbxS9RecenteredCoupledLaws K y) ∧
      HasPathMarginals Q.measure (sbxS9RecenteredCoupledLaws K y)
        (sbxS9RecenteredPathLaws P y) ∧
      HasFreshBits Q.measure (regenDelta lam) δ (sbxS9RecenteredCoupledLaws K y) ∧
      HasDeterministicRestart Q.measure (regenDelta lam)
        (sbxS9RecenteredCoupledLaws K y) ∧
      HasSuccessfulBridgeSupport Q.measure (regenDelta lam) (forceCoord hd) (l / lam)
        (sbxS9RecenteredCoupledLaws K y) ∧
      HasUniformSuccessfulEndpoint Q.measure (regenDelta lam) δ (l / lam) (forceCoord hd)
        (sbxS9RecenteredCoupledLaws K y) ∧
      HasOneIntervalKernel Q.measure (regenDelta lam) δ (l / lam) (forceCoord hd)
        (sbxS9RecenteredPathLaws P y) (sbxS9RecenteredCoupledLaws K y) := by
  obtain ⟨hprob, hpath, hgmp, hfresh, hrestart, hsupport, hendpoint, hinterval⟩ := hK
  filter_upwards [sbxS9_five_coupling_clauses_recenter Q (regenDelta lam) δ (l / lam)
    (forceCoord hd) P K hprob hpath hfresh hrestart hsupport,
    sbxS5_hasUniformSuccessfulEndpoint_recenter Q (regenDelta lam) δ (l / lam)
      (forceCoord hd) K hendpoint,
    sbxS5_hasOneIntervalKernel_recenter hd hΛ₀ Q lam h0 h1 (regenDelta lam) δ (l / lam)
      (forceCoord hd) P K hgmp hinterval] with y halg hend hint
  exact ⟨halg.1, halg.2.1, halg.2.2.1, halg.2.2.2.1, halg.2.2.2.2, hend, hint⟩

#print axioms sbxS5_analyticRecenterPaths_apply
#print axioms sbxS5_analyticRecenterCoupling_apply
#print axioms sbxS5_endpointAverage_recenter
#print axioms sbxS5_uniformSuccessfulEndpointAt_recenter
#print axioms sbxS5_recenter_input_ae
#print axioms sbxS5_hasUniformSuccessfulEndpoint_recenter
#print axioms sbxS5_probability_all_starts_of_gmp
#print axioms sbxS5_map_recenter_killedBridgeMixture
#print axioms sbxS5_oneIntervalKernelAt_of_recenter_maps
#print axioms sbxS5_oneIntervalKernelAt_recenter
#print axioms sbxS5_hasOneIntervalKernel_recenter
#print axioms sbxS5_seven_coupling_clauses_recenter
#lint-
end EinsteinFull.Blueprint
