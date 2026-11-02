import EinsteinRelation.Regeneration.SpatialRecenterEquiv
import EinsteinRelation.Regeneration.RestrictedRecordShift
import EinsteinRelation.Regeneration.CouplingSpatialMaps
import EinsteinRelation.Regeneration.CoupledEnvironmentRegularity
import EinsteinRelation.Regeneration.CoupledEndpointSupport
import EinsteinRelation.Probability.EndpointDensityTransport
import EinsteinRelation.Regeneration.FiniteHistoryMeasureExt
import EinsteinRelation.Regeneration.FirstRegenerationEndpointFormula
import EinsteinFull.Frozen.RegenerationCoupling
import EinsteinFull.Frozen.RegenerationConditionedLaw
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Algebraic transport of the coupling under a fixed spatial recentering.

The origin clauses hold for volume-almost every recentering point. Their
proof uses the original product-a.e. clauses, rather than specializing an
exceptional spatial fibre. Source: `paper/main.tex:1510–1516`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.Regeneration

/-- The old starting point and environment corresponding to recentered data. -/
def sbxS9RecenterInput {d : ℕ} (a : Vec d) (p : Vec d × FieldPair d) :
    Vec d × FieldPair d :=
  (a + p.1, translate (-a) p.2)

/-- The fixed recentering is measurable in the actual input sigma algebra. -/
theorem sbxS9_measurable_recenterInput {d : ℕ} (a : Vec d) :
    Measurable (sbxS9RecenterInput a) :=
  (measurable_const.add measurable_fst).prodMk
    ((EinsteinRelation.Probability.measurable_translate (-a)).comp measurable_snd)

/-- Recenter both the input data and the actual path law. -/
def sbxS9RecenteredPathLaws {d : ℕ} (P : QuenchedPathLaws d) (a : Vec d) :
    QuenchedPathLaws d :=
  (P.comap (sbxS9RecenterInput a) (sbxS9_measurable_recenterInput a)).map
    (recenterPathEquiv a)

/-- Recenter the actual coupled law, retaining every Bernoulli coordinate. -/
def sbxS9RecenteredCoupledLaws {d : ℕ} (K : CoupledQuenchedLaws d) (a : Vec d) :
    CoupledQuenchedLaws d :=
  (K.comap (sbxS9RecenterInput a) (sbxS9_measurable_recenterInput a)).map
    (recenterSampleEquiv a)

@[simp] theorem sbxS9RecenteredPathLaws_apply {d : ℕ}
    (P : QuenchedPathLaws d) (a : Vec d) (p : Vec d × FieldPair d) :
    sbxS9RecenteredPathLaws P a p =
      (P (sbxS9RecenterInput a p)).map (recenterPathEquiv a) := by
  rw [sbxS9RecenteredPathLaws, Kernel.map_apply _ (recenterPathEquiv a).measurable,
    Kernel.comap_apply]

@[simp] theorem sbxS9RecenteredCoupledLaws_apply {d : ℕ}
    (K : CoupledQuenchedLaws d) (a : Vec d) (p : Vec d × FieldPair d) :
    sbxS9RecenteredCoupledLaws K a p =
      (K (sbxS9RecenterInput a p)).map (recenterSampleEquiv a) := by
  rw [sbxS9RecenteredCoupledLaws, Kernel.map_apply _ (recenterSampleEquiv a).measurable,
    Kernel.comap_apply]

/-- Stationarity and spatial Haar invariance preserve the product input law. -/
theorem sbxS9_measurePreserving_recenterInput {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q) (a : Vec d) :
    MeasurePreserving (sbxS9RecenterInput a)
      ((volume : Measure (Vec d)).prod Q) ((volume : Measure (Vec d)).prod Q) :=
  (measurePreserving_add_left (volume : Measure (Vec d)) a).prod
    ⟨EinsteinRelation.Probability.measurable_translate (-a), hQ (-a)⟩

/-- Product-a.e. information yields the new origin and product clauses on
one spatial good set; the predicate need not itself be measurable. -/
theorem sbxS9_ae_recenterInput {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    {p : Vec d × FieldPair d → Prop}
    (hp : ∀ᵐ q ∂((volume : Measure (Vec d)).prod Q), p q) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q, p (sbxS9RecenterInput a (0, η))) ∧
      ∀ᵐ q ∂((volume : Measure (Vec d)).prod Q), p (sbxS9RecenterInput a q) := by
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with a ha
  constructor
  · have hmp : MeasurePreserving (translate (-a)) Q Q :=
      ⟨EinsteinRelation.Probability.measurable_translate (-a), hQ (-a)⟩
    simpa only [sbxS9RecenterInput, add_zero] using hmp.quasiMeasurePreserving.ae ha
  · exact (sbxS9_measurePreserving_recenterInput Q hQ a).quasiMeasurePreserving.ae hp

/-- A probability fibre remains a probability fibre under the recentering. -/
theorem sbxS9_probability_recenter {d : ℕ} (K : CoupledQuenchedLaws d)
    (a : Vec d) (p : Vec d × FieldPair d)
    (h : IsProbabilityMeasure (K (sbxS9RecenterInput a p))) :
    IsProbabilityMeasure (sbxS9RecenteredCoupledLaws K a p) := by
  rw [sbxS9RecenteredCoupledLaws_apply]
  have := h
  infer_instance

/-- Taking the path marginal commutes with the two output recenterings. -/
theorem sbxS9_pathMarginal_recenter {d : ℕ}
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (a : Vec d) (p : Vec d × FieldPair d)
    (h : (K (sbxS9RecenterInput a p)).map Prod.fst = P (sbxS9RecenterInput a p)) :
    (sbxS9RecenteredCoupledLaws K a p).map Prod.fst =
      sbxS9RecenteredPathLaws P a p := by
  rw [sbxS9RecenteredCoupledLaws_apply, sbxS9RecenteredPathLaws_apply,
    Measure.map_map measurable_fst (recenterSampleEquiv a).measurable, ← h,
    Measure.map_map (recenterPathEquiv a).measurable measurable_fst]
  rfl

/-- Pulled-back finite-history tests prove the fresh-bit identity. -/
theorem sbxS9_freshBitsAt_recenter {d : ℕ} (Δ : ℝ≥0) (δ : ℝ)
    (K : CoupledQuenchedLaws d) (a : Vec d) (p : Vec d × FieldPair d)
    (h : FreshBitsAt Δ δ K (sbxS9RecenterInput a p)) :
    FreshBitsAt Δ δ (sbxS9RecenteredCoupledLaws K a) p := by
  intro n H hH hbH
  obtain ⟨B, hB⟩ := hbH
  have ht := h n (fun z => H (recenterSample a z))
    (measurable_finiteHistory_comp_recenter Δ n a H hH) ⟨B, fun z => hB _⟩
  simp only [sbxS9RecenteredCoupledLaws_apply, integral_map_equiv]
  convert ht using 1 <;> rfl

/-- Transport the deterministic restart identity with the same history pullback
and spatial conjugacy as `deterministicRestartAt_conjugate_spatial`. -/
theorem sbxS9_deterministicRestartAt_recenter {d : ℕ} (Δ : ℝ≥0)
    (K : CoupledQuenchedLaws d) (a : Vec d) (p : Vec d × FieldPair d)
    (h : DeterministicRestartAt Δ K (sbxS9RecenterInput a p)) :
    DeterministicRestartAt Δ (sbxS9RecenteredCoupledLaws K a) p := by
  intro n H Φ hH hbH hΦ hbΦ
  obtain ⟨B, hB⟩ := hbH
  obtain ⟨C, hC⟩ := hbΦ
  have ht := h n (fun z => H (recenterSample a z))
    (fun z => Φ (recenterSample a z))
    (measurable_finiteHistory_comp_recenter Δ n a H hH) ⟨B, fun z => hB _⟩
    (hΦ.comp (recenterSampleEquiv a).measurable) ⟨C, fun z => hC _⟩
  simp only [sbxS9RecenteredCoupledLaws_apply, integral_map_equiv]
  convert ht using 1
  · apply integral_congr_ae
    filter_upwards [] with z
    change H (recenterSample a z) *
      Φ (sampleTimeShift Δ (recenterSample a z) ((n : ℝ≥0) * Δ)) = _
    rw [sampleTimeShift_recenter]
  · apply integral_congr_ae
    filter_upwards [] with z
    change H (recenterSample a z) *
        (∫ z', Φ (recenterSample a z') ∂K
          (a + (z.1 ((n : ℝ≥0) * Δ) - a), translate (-a) p.2)) = _
    have hz : a + (z.1 ((n : ℝ≥0) * Δ) - a) = z.1 ((n : ℝ≥0) * Δ) := by abel
    rw [hz]
    rfl

/-- The successful-bridge support uses the unchanged Euclidean coupling region. -/
theorem sbxS9_successfulBridgeSupportAt_recenter {d : ℕ} (Δ : ℝ≥0)
    (i : Fin d) (R : ℝ) (K : CoupledQuenchedLaws d)
    (a : Vec d) (p : Vec d × FieldPair d)
    (h : SuccessfulBridgeSupportAt Δ i R K (sbxS9RecenterInput a p)) :
    SuccessfulBridgeSupportAt Δ i R (sbxS9RecenteredCoupledLaws K a) p := by
  unfold SuccessfulBridgeSupportAt
  rw [sbxS9RecenteredCoupledLaws_apply,
    (recenterSampleEquiv a).measurableEmbedding.ae_map_iff]
  filter_upwards [h] with z hz
  intro n hn t ht ht'
  exact (sub_mem_couplingRegion_iff i R a (z.1 t)
    (z.1 ((n : ℝ≥0) * Δ))).mpr (hz n hn t ht ht')

/-- Probability normalization, at the new origin and product-a.e. -/
theorem sbxS9_hasProbabilityLaws_recenter {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasProbabilityLaws Q (sbxS9RecenteredCoupledLaws K a) := by
  filter_upwards [sbxS9_ae_recenterInput Q hQ hK.2] with a ha
  constructor
  · filter_upwards [ha.1] with η hη
    exact sbxS9_probability_recenter K a (0, η) hη
  · filter_upwards [ha.2] with p hp
    exact sbxS9_probability_recenter K a p hp

/-- The exact path marginal, at the new origin and product-a.e. -/
theorem sbxS9_hasPathMarginals_recenter {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasPathMarginals Q K P) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasPathMarginals Q (sbxS9RecenteredCoupledLaws K a)
        (sbxS9RecenteredPathLaws P a) := by
  filter_upwards [sbxS9_ae_recenterInput Q hQ hK.2] with a ha
  constructor
  · filter_upwards [ha.1] with η hη
    exact sbxS9_pathMarginal_recenter P K a (0, η) hη
  · filter_upwards [ha.2] with p hp
    exact sbxS9_pathMarginal_recenter P K a p hp

/-- Fresh-bit identities, at the new origin and product-a.e. -/
theorem sbxS9_hasFreshBits_recenter {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (Δ : ℝ≥0) (δ : ℝ) (K : CoupledQuenchedLaws d)
    (hK : HasFreshBits Q Δ δ K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasFreshBits Q Δ δ (sbxS9RecenteredCoupledLaws K a) := by
  filter_upwards [sbxS9_ae_recenterInput Q hQ hK.2] with a ha
  constructor
  · filter_upwards [ha.1] with η hη
    exact sbxS9_freshBitsAt_recenter Δ δ K a (0, η) hη
  · filter_upwards [ha.2] with p hp
    exact sbxS9_freshBitsAt_recenter Δ δ K a p hp

/-- Deterministic restart, at the new origin and product-a.e. -/
theorem sbxS9_hasDeterministicRestart_recenter {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (Δ : ℝ≥0) (K : CoupledQuenchedLaws d)
    (hK : HasDeterministicRestart Q Δ K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasDeterministicRestart Q Δ (sbxS9RecenteredCoupledLaws K a) := by
  filter_upwards [sbxS9_ae_recenterInput Q hQ hK.2] with a ha
  constructor
  · filter_upwards [ha.1] with η hη
    exact sbxS9_deterministicRestartAt_recenter Δ K a (0, η) hη
  · filter_upwards [ha.2] with p hp
    exact sbxS9_deterministicRestartAt_recenter Δ K a p hp

/-- Successful-bridge support, at the new origin and product-a.e. -/
theorem sbxS9_hasSuccessfulBridgeSupport_recenter {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (Δ : ℝ≥0) (i : Fin d) (R : ℝ) (K : CoupledQuenchedLaws d)
    (hK : HasSuccessfulBridgeSupport Q Δ i R K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasSuccessfulBridgeSupport Q Δ i R (sbxS9RecenteredCoupledLaws K a) := by
  filter_upwards [sbxS9_ae_recenterInput Q hQ hK.2] with a ha
  constructor
  · filter_upwards [ha.1] with η hη
    exact sbxS9_successfulBridgeSupportAt_recenter Δ i R K a (0, η) hη
  · filter_upwards [ha.2] with p hp
    exact sbxS9_successfulBridgeSupportAt_recenter Δ i R K a p hp

/-- One common spatial good set for the five algebraic coupling clauses.
The measure and stationarity are those of the actual environment law. -/
theorem sbxS9_five_coupling_clauses_recenter {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hprob : HasProbabilityLaws Q.measure K)
    (hpath : HasPathMarginals Q.measure K P)
    (hfresh : HasFreshBits Q.measure Δ δ K)
    (hrestart : HasDeterministicRestart Q.measure Δ K)
    (hsupport : HasSuccessfulBridgeSupport Q.measure Δ i R K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasProbabilityLaws Q.measure (sbxS9RecenteredCoupledLaws K a) ∧
      HasPathMarginals Q.measure (sbxS9RecenteredCoupledLaws K a)
        (sbxS9RecenteredPathLaws P a) ∧
      HasFreshBits Q.measure Δ δ (sbxS9RecenteredCoupledLaws K a) ∧
      HasDeterministicRestart Q.measure Δ (sbxS9RecenteredCoupledLaws K a) ∧
      HasSuccessfulBridgeSupport Q.measure Δ i R (sbxS9RecenteredCoupledLaws K a) := by
  filter_upwards [sbxS9_hasProbabilityLaws_recenter Q.measure Q.stationary K hprob,
    sbxS9_hasPathMarginals_recenter Q.measure Q.stationary P K hpath,
    sbxS9_hasFreshBits_recenter Q.measure Q.stationary Δ δ K hfresh,
    sbxS9_hasDeterministicRestart_recenter Q.measure Q.stationary Δ K hrestart,
    sbxS9_hasSuccessfulBridgeSupport_recenter Q.measure Q.stationary Δ i R K hsupport]
    with a ha hb hc hd he
  exact ⟨ha, hb, hc, hd, he⟩

/-- The two literal bit branches determine the first history from the path
law at this fibre. Equality of the actual RN bridge measures follows by
unfolding their definition, including the endpoint density denominator. -/
theorem sbxS9_first_history_eq_of_path_fibre_eq {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (P P' : QuenchedPathLaws d)
    (K L : CoupledQuenchedLaws d) (p : Vec d × FieldPair d)
    [IsProbabilityMeasure (K p)] [IsProbabilityMeasure (L p)]
    (hs : ∀ᵐ z ∂K p, z.1 0 = p.1) (hs' : ∀ᵐ z ∂L p, z.1 0 = p.1)
    (ho : Renewal.OneIntervalKernelAt Δ δ R i P K p)
    (ho' : Renewal.OneIntervalKernelAt Δ δ R i P' L p)
    (hP : P p = P' p) (F : CoupledSample d → ℝ)
    (hF : Measurable[finiteHistorySigma Δ 1] F) (hb : BoundedRealTest F) :
    (∫ z, F z ∂K p) = ∫ z, F z ∂L p := by
  have hbridge : Renewal.killedBridgeMixture Δ R i P p.1 p.2 =
      Renewal.killedBridgeMixture Δ R i P' p.1 p.2 := by
    unfold Renewal.killedBridgeMixture Renewal.killedSegmentLaw
    rw [show P (p.1, p.2) = P' (p.1, p.2) from hP]
  exact integral_first_history_eq_of_oneInterval_integrals Δ δ R i P P' K L p p
    hs hs' ho ho' F hF hb (fun _ => by rw [hP]) (fun _ => by rw [hbridge])

/-- Deterministic restart propagates split-kernel uniqueness to every finite
history. Spatial exceptional sets are crossed only through the actual
positive-time endpoint density; the origin is retained separately. -/
theorem sbxS9_finite_histories_eq_of_path_laws_eq {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (x : Vec d) (ω : FieldPair d)
    (hs : ∀ y, ∀ᵐ γ ∂P (y, ω), γ 0 = y)
    (hs' : ∀ y, ∀ᵐ γ ∂P' (y, ω), γ 0 = y)
    (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
    (hx' : CoupledFibreRegular Δ δ R i P' L (x, ω))
    (hP : P (x, ω) = P' (x, ω))
    (hsp : ∀ᵐ y ∂(volume : Measure (Vec d)),
      CoupledFibreRegular Δ δ R i P K (y, ω) ∧
      CoupledFibreRegular Δ δ R i P' L (y, ω) ∧ P (y, ω) = P' (y, ω))
    (hdensity : ∀ n : ℕ, 1 ≤ n →
      (P (x, ω)).map (pathPosition ((n : ℝ≥0) * Δ)) ≪ (volume : Measure (Vec d))) :
    ∀ n : ℕ, 1 ≤ n → ∀ F : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ n] F → BoundedRealTest F →
      (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂L (x, ω) := by
  have hcompare : ∀ y,
      CoupledFibreRegular Δ δ R i P K (y, ω) →
      CoupledFibreRegular Δ δ R i P' L (y, ω) → P (y, ω) = P' (y, ω) →
      ∀ F : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ 1] F →
      BoundedRealTest F → (∫ z, F z ∂K (y, ω)) = ∫ z, F z ∂L (y, ω) := by
    intro y hy hy' hp F hF hb
    have := hy.1
    have := hy'.1
    have hsy := hs y
    have hsy' := hs' y
    rw [← hy.2.1] at hsy
    rw [← hy'.2.1] at hsy'
    exact sbxS9_first_history_eq_of_path_fibre_eq Δ δ R i P P' K L (y, ω)
      (ae_of_ae_map measurable_fst.aemeasurable hsy)
      (ae_of_ae_map measurable_fst.aemeasurable hsy')
      hy.2.2.2 hy'.2.2.2 hp F hF hb
  have := hx.1
  have := hx'.1
  have hhist := integral_supported_histories_eq_of_first_interval_eq Δ hΔ
    Set.univ isClosed_univ K L (x, ω) (x, ω) hx.2.2.1 hx'.2.2.1
    (fun F hF hb _ => hcompare x hx hx' hP F hF hb)
    (hsp.mono fun y hy => ⟨hy.1.1, hy.2.1.1,
      fun _ F hF hb _ => hcompare y hy.1 hy.2.1 hy.2.2 F hF hb⟩)
    (fun n hn => coupled_endpoint_density_of_path_marginal P K (x, ω)
      hx.2.1 _ (hdensity n hn))
    (fun n hn => coupled_endpoint_density_of_path_marginal P' L (x, ω)
      hx'.2.1 _ (hP ▸ hdensity n hn))
  exact fun n hn F hF hb => hhist n hn F hF hb (fun _ _ _ _ => Set.mem_univ _)

/-- Equality of the underlying path laws and the prescribed split/restart
contracts determines the complete coupled law on regular environments. -/
theorem sbxS9_coupled_law_eq_of_regular_path_laws_eq {d : ℕ}
    (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (x : Vec d) (ω : FieldPair d)
    (hg : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P' L ω)
    (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
    (hx' : CoupledFibreRegular Δ δ R i P' L (x, ω))
    (hP : P (x, ω) = P' (x, ω))
    (hPsp : ∀ᵐ y ∂(volume : Measure (Vec d)), P (y, ω) = P' (y, ω)) :
    K (x, ω) = L (x, ω) := by
  have hs : ∀ y, ∀ᵐ γ ∂P (y, ω), γ 0 = y := by
    obtain ⟨_, r, hr⟩ := hg.1
    intro y
    rw [hr y]
    exact r.pathLaw_starts_at y
  have hs' : ∀ y, ∀ᵐ γ ∂P' (y, ω), γ 0 = y := by
    obtain ⟨_, r, hr⟩ := hg'.1
    intro y
    rw [hr y]
    exact r.pathLaw_starts_at y
  have hsp : ∀ᵐ y ∂(volume : Measure (Vec d)),
      CoupledFibreRegular Δ δ R i P K (y, ω) ∧
      CoupledFibreRegular Δ δ R i P' L (y, ω) ∧ P (y, ω) = P' (y, ω) := by
    filter_upwards [hg.2.2.1, hg'.2.2.1, hPsp] with y hy hy' hp
    exact ⟨hy, hy', hp⟩
  have := hx.1
  have := hx'.1
  exact measure_eq_of_finite_history_integrals _ _ Δ hΔ
    (sbxS9_finite_histories_eq_of_path_laws_eq Δ hΔ δ R i P P' K L x ω
      hs hs' hx hx' hP hsp (fun n hn => hg.2.2.2 n hn x))

/-- Actual GMP couplings inherit equality of the underlying path kernels,
with the origin and product-a.e. spatial qualifiers both preserved. Path-law
equality is an explicit input, requiring its own producer. -/
theorem sbxS9_coupling_laws_eq_of_path_laws_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hL : IsRegenerationCoupling hd Q lam l δ h0.le h1 P' L)
    (hP : (∀ᵐ ω ∂Q.measure, P (0, ω) = P' (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, P p = P' p) :
    (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have hg := ae_coupledEnvironmentRegular hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  have hg' := ae_coupledEnvironmentRegular hd Q lam h0.le h1 P' L
    hL.1 hL.2.1 hL.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hL.2.2.2.2.1 hL.2.2.2.2.2.2.2
  have hPsp : ∀ᵐ ω ∂Q.measure,
      ∀ᵐ y ∂(volume : Measure (Vec d)), P (y, ω) = P' (y, ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := Q.measure)
        (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae hP.2)
  have hgood := (hg.and hg').and hPsp
  have hregularK : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P K p := by
    filter_upwards [hK.1.2, hK.2.1.2, hK.2.2.2.2.1.2,
      hK.2.2.2.2.2.2.2.2] with p hp hm hr ho
    exact ⟨hp, hm, hr, ho⟩
  have hregularL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P' L p := by
    filter_upwards [hL.1.2, hL.2.1.2, hL.2.2.2.2.1.2,
      hL.2.2.2.2.2.2.2.2] with p hp hm hr ho
    exact ⟨hp, hm, hr, ho⟩
  constructor
  · filter_upwards [hgood, hP.1] with ω hω hp
    exact sbxS9_coupled_law_eq_of_regular_path_laws_eq hd Λ₀ Q.ellipticity_parameter
      lam h0.le h1 (Renewal.regenDelta lam) hΔ δ (l / lam) (Renewal.forceCoord hd)
      P P' K L 0 ω hω.1.1 hω.1.2 hω.1.1.2.1 hω.1.2.2.1 hp hω.2
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hgood,
      hregularK, hregularL, hP.2] with p hp hk hl heq
    exact sbxS9_coupled_law_eq_of_regular_path_laws_eq hd Λ₀ Q.ellipticity_parameter
      lam h0.le h1 (Renewal.regenDelta lam) hΔ δ (l / lam) (Renewal.forceCoord hd)
      P P' K L p.1 p.2 hp.1.1 hp.1.2 hk hl heq hp.2

/-- In particular, the prescribed split contracts determine the coupling
over one fixed supplied path kernel, without a covariance premise. -/
theorem sbxS9_coupling_laws_eq_of_same_path_kernel {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hL : IsRegenerationCoupling hd Q lam l δ h0.le h1 P L) :
    (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p :=
  sbxS9_coupling_laws_eq_of_path_laws_eq hd Q lam h0 h1 l δ P P K L hK hL
    ⟨Filter.Eventually.of_forall fun _ => rfl, Filter.Eventually.of_forall fun _ => rfl⟩

/-- The literal killed-future means are independent of the split-coupling
version once the two actual path laws agree. The same spatial good set
works for every future test, since equality holds at the measure level. -/
theorem sbxS9_killed_future_means_eq_of_path_laws_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hL : IsRegenerationCoupling hd Q lam l δ h0.le h1 P' L)
    (hP : (∀ᵐ ω ∂Q.measure, P (0, ω) = P' (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, P p = P' p) :
    (∀ᵐ ω ∂Q.measure, ∀ Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ,
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z) ∂K (0, ω)) =
        ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z) ∂L (0, ω)) ∧
    ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      ∀ Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ,
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ (p, z) ∂K p) =
        ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ (p, z) ∂L p := by
  obtain ⟨h₀, hp⟩ :=
    sbxS9_coupling_laws_eq_of_path_laws_eq hd Q lam h0 h1 l δ P P' K L hK hL hP
  exact ⟨h₀.mono fun ω hω _ => by rw [hω], hp.mono fun p h _ => by rw [h]⟩

/-- The environment-averaged future means used in the source factorization
inherit the same comparison. Fubini is applied to the common good set before
choosing a future test, so no test-dependent spatial null set is introduced. -/
theorem sbxS9_averaged_killed_future_means_eq_of_path_laws_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hL : IsRegenerationCoupling hd Q lam l δ h0.le h1 P' L)
    (hP : (∀ᵐ ω ∂Q.measure, P (0, ω) = P' (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, P p = P' p) :
    (∀ Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ,
      (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z)
        ∂K (0, ω) ∂Q.measure) =
      ∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z)
        ∂L (0, ω) ∂Q.measure) ∧
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      ∀ Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ,
      (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z)
        ∂K (y, ω) ∂Q.measure) =
      ∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z)
        ∂L (y, ω) ∂Q.measure := by
  obtain ⟨h₀, hp⟩ :=
    sbxS9_killed_future_means_eq_of_path_laws_eq hd Q lam h0 h1 l δ P P' K L hK hL hP
  exact ⟨fun Φ => integral_congr_ae (h₀.mono fun _ h => h Φ),
    (Measure.ae_ae_of_ae_prod hp).mono fun _ h Φ =>
      integral_congr_ae (h.mono fun _ hω => hω Φ)⟩

/-- Finite-history uniqueness only needs one regular path law: equality
of the two path laws on each good fibre supplies the second starting-point
property. No realization of the second path kernel is required. -/
theorem sbxS9_finite_histories_eq_of_one_regular_path_law {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (x : Vec d) (ω : FieldPair d)
    (hs : ∀ y, ∀ᵐ γ ∂P (y, ω), γ 0 = y)
    (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
    (hx' : CoupledFibreRegular Δ δ R i P' L (x, ω))
    (hP : P (x, ω) = P' (x, ω))
    (hsp : ∀ᵐ y ∂(volume : Measure (Vec d)),
      CoupledFibreRegular Δ δ R i P K (y, ω) ∧
      CoupledFibreRegular Δ δ R i P' L (y, ω) ∧ P (y, ω) = P' (y, ω))
    (hdensity : ∀ n : ℕ, 1 ≤ n →
      (P (x, ω)).map (pathPosition ((n : ℝ≥0) * Δ)) ≪ (volume : Measure (Vec d))) :
    ∀ n : ℕ, 1 ≤ n → ∀ F : CoupledSample d → ℝ,
      Measurable[finiteHistorySigma Δ n] F → BoundedRealTest F →
      (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂L (x, ω) := by
  have hcompare : ∀ y,
      CoupledFibreRegular Δ δ R i P K (y, ω) →
      CoupledFibreRegular Δ δ R i P' L (y, ω) → P (y, ω) = P' (y, ω) →
      ∀ F : CoupledSample d → ℝ, Measurable[finiteHistorySigma Δ 1] F →
      BoundedRealTest F → (∫ z, F z ∂K (y, ω)) = ∫ z, F z ∂L (y, ω) := by
    intro y hy hy' hp F hF hb
    have := hy.1
    have := hy'.1
    have hsy := hs y
    have hsy' : ∀ᵐ γ ∂P' (y, ω), γ 0 = y := hp ▸ hs y
    rw [← hy.2.1] at hsy
    rw [← hy'.2.1] at hsy'
    exact sbxS9_first_history_eq_of_path_fibre_eq Δ δ R i P P' K L (y, ω)
      (ae_of_ae_map measurable_fst.aemeasurable hsy)
      (ae_of_ae_map measurable_fst.aemeasurable hsy')
      hy.2.2.2 hy'.2.2.2 hp F hF hb
  have := hx.1
  have := hx'.1
  have hhist := integral_supported_histories_eq_of_first_interval_eq Δ hΔ
    Set.univ isClosed_univ K L (x, ω) (x, ω) hx.2.2.1 hx'.2.2.1
    (fun F hF hb _ => hcompare x hx hx' hP F hF hb)
    (hsp.mono fun y hy => ⟨hy.1.1, hy.2.1.1,
      fun _ F hF hb _ => hcompare y hy.1 hy.2.1 hy.2.2 F hF hb⟩)
    (fun n hn => coupled_endpoint_density_of_path_marginal P K (x, ω)
      hx.2.1 _ (hdensity n hn))
    (fun n hn => coupled_endpoint_density_of_path_marginal P' L (x, ω)
      hx'.2.1 _ (hP ▸ hdensity n hn))
  exact fun n hn F hF hb => hhist n hn F hF hb (fun _ _ _ _ => Set.mem_univ _)

/-- A single actual GMP realization supplies the starts and endpoint
densities for comparison with any other prescribed split kernel. -/
theorem sbxS9_coupled_law_eq_of_one_regular_path_law {d : ℕ}
    (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (x : Vec d) (ω : FieldPair d)
    (hg : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hLsp : ∀ᵐ y ∂(volume : Measure (Vec d)),
      CoupledFibreRegular Δ δ R i P' L (y, ω))
    (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
    (hx' : CoupledFibreRegular Δ δ R i P' L (x, ω))
    (hP : P (x, ω) = P' (x, ω))
    (hPsp : ∀ᵐ y ∂(volume : Measure (Vec d)), P (y, ω) = P' (y, ω)) :
    K (x, ω) = L (x, ω) := by
  have hs : ∀ y, ∀ᵐ γ ∂P (y, ω), γ 0 = y := by
    obtain ⟨_, r, hr⟩ := hg.1
    intro y
    rw [hr y]
    exact r.pathLaw_starts_at y
  have hsp : ∀ᵐ y ∂(volume : Measure (Vec d)),
      CoupledFibreRegular Δ δ R i P K (y, ω) ∧
      CoupledFibreRegular Δ δ R i P' L (y, ω) ∧ P (y, ω) = P' (y, ω) := by
    filter_upwards [hg.2.2.1, hLsp, hPsp] with y hy hy' hp
    exact ⟨hy, hy', hp⟩
  have := hx.1
  have := hx'.1
  exact measure_eq_of_finite_history_integrals _ _ Δ hΔ
    (sbxS9_finite_histories_eq_of_one_regular_path_law Δ hΔ δ R i P P' K L x ω
      hs hx hx' hP hsp (fun n hn => hg.2.2.2 n hn x))

/-- The second kernel only needs its actual probability, marginal, restart
and one-interval clauses. Its GMP realization need not be transported:
the first path law supplies the starts and endpoint densities on the common
good set where the path laws agree. -/
theorem sbxS9_coupling_laws_eq_of_prescribed_split_clauses {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hprobL : HasProbabilityLaws Q.measure L)
    (hpathL : HasPathMarginals Q.measure L P')
    (hrestartL : HasDeterministicRestart Q.measure (Renewal.regenDelta lam) L)
    (honeL : Renewal.HasOneIntervalKernel Q.measure (Renewal.regenDelta lam)
      δ (l / lam) (Renewal.forceCoord hd) P' L)
    (hP : (∀ᵐ ω ∂Q.measure, P (0, ω) = P' (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, P p = P' p) :
    (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have hg := ae_coupledEnvironmentRegular hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  have hregularL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P' L p := by
    filter_upwards [hprobL.2, hpathL.2, hrestartL.2, honeL.2] with p hp hm hr ho
    exact ⟨hp, hm, hr, ho⟩
  have hPsp : ∀ᵐ ω ∂Q.measure,
      ∀ᵐ y ∂(volume : Measure (Vec d)), P (y, ω) = P' (y, ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := Q.measure)
        (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae hP.2)
  have hLsp : ∀ᵐ ω ∂Q.measure, ∀ᵐ y ∂(volume : Measure (Vec d)),
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P' L (y, ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := Q.measure)
        (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae hregularL)
  have hgood := (hg.and hLsp).and hPsp
  constructor
  · filter_upwards [hgood, hP.1, hprobL.1, hpathL.1, hrestartL.1, honeL.1]
      with ω hω hp hprob hpath hr ho
    exact sbxS9_coupled_law_eq_of_one_regular_path_law hd Λ₀ Q.ellipticity_parameter
      lam h0.le h1 (Renewal.regenDelta lam) hΔ δ (l / lam) (Renewal.forceCoord hd)
      P P' K L 0 ω hω.1.1 hω.1.2 hω.1.1.2.1 ⟨hprob, hpath, hr, ho⟩ hp hω.2
  · have hregularK : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
          (Renewal.forceCoord hd) P K p := by
      filter_upwards [hK.1.2, hK.2.1.2, hK.2.2.2.2.1.2,
        hK.2.2.2.2.2.2.2.2] with p hp hm hr ho
      exact ⟨hp, hm, hr, ho⟩
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hgood,
      hregularK, hregularL, hP.2] with p hp hk hl heq
    exact sbxS9_coupled_law_eq_of_one_regular_path_law hd Λ₀ Q.ellipticity_parameter
      lam h0.le h1 (Renewal.regenDelta lam) hΔ δ (l / lam) (Renewal.forceCoord hd)
      P P' K L p.1 p.2 hp.1.1 hp.1.2 hk hl heq hp.2

/-- Comparison of the actual averaged future means requires no GMP premise
for the second kernel beyond the first kernel's regularity and the separately
supplied equality of the path laws. -/
theorem sbxS9_averaged_killed_future_means_eq_of_prescribed_split_clauses
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hprobL : HasProbabilityLaws Q.measure L)
    (hpathL : HasPathMarginals Q.measure L P')
    (hrestartL : HasDeterministicRestart Q.measure (Renewal.regenDelta lam) L)
    (honeL : Renewal.HasOneIntervalKernel Q.measure (Renewal.regenDelta lam)
      δ (l / lam) (Renewal.forceCoord hd) P' L)
    (hP : (∀ᵐ ω ∂Q.measure, P (0, ω) = P' (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, P p = P' p) :
    (∀ Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ,
      (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z)
        ∂K (0, ω) ∂Q.measure) =
      ∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z)
        ∂L (0, ω) ∂Q.measure) ∧
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      ∀ Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ,
      (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z)
        ∂K (y, ω) ∂Q.measure) =
      ∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z)
        ∂L (y, ω) ∂Q.measure := by
  obtain ⟨h₀, hp⟩ := sbxS9_coupling_laws_eq_of_prescribed_split_clauses
    hd Q lam h0 h1 l δ P P' K L hK hprobL hpathL hrestartL honeL hP
  exact ⟨fun _ => integral_congr_ae (h₀.mono fun _ h => by dsimp only; rw [h]),
    (Measure.ae_ae_of_ae_prod hp).mono fun _ h _ =>
      integral_congr_ae (h.mono fun _ hω => by dsimp only; rw [hω])⟩

/-- Origin-a.e. equality respects the actual probability-fibre normalization,
including arbitrary exceptional non-probability fibres. -/
theorem sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (K L : CoupledQuenchedLaws d)
    (h : ∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) :
    annealedCoupledLaw Q K = annealedCoupledLaw Q L := by
  apply Measure.compProd_congr
  filter_upwards [h] with ω hω
  simp only [Probability.probabilityPart_apply, originCoupledLaw, Kernel.comap_apply]
  exact ite_congr (congrArg (fun μ : Measure (CoupledSample d) => μ Set.univ = 1) hω)
    (fun _ => hω) (fun _ => rfl)

/-- The literal no-return event has the same mass under equal origin laws. -/
theorem sbxS9_noReturn_mass_eq_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) (K L : CoupledQuenchedLaws d) (R : ℝ)
    (h : ∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) :
    annealedCoupledLaw Q K (regenerationNoReturn hd R) =
      annealedCoupledLaw Q L (regenerationNoReturn hd R) := by
  rw [sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq Q K L h]

/-- Transport the actual nonzero conditioning witness. -/
theorem sbxS9_noReturn_ne_zero_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) (K L : CoupledQuenchedLaws d) (R : ℝ)
    (h : ∀ᵐ ω ∂Q, K (0, ω) = L (0, ω))
    (hD : annealedCoupledLaw Q K (regenerationNoReturn hd R) ≠ 0) :
    annealedCoupledLaw Q L (regenerationNoReturn hd R) ≠ 0 := by
  rwa [← sbxS9_noReturn_mass_eq_of_origin_ae_eq hd Q K L R h]

/-- Equality of the frozen conditioned measures is independent of both
probability witnesses and both nonzero event-mass witnesses. -/
theorem sbxS9_regenerationConditionedLaw_eq_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K L : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hL : HasProbabilityLaws Q.measure L)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hD' : annealedCoupledLaw Q.measure L (regenerationNoReturn hd (l / lam)) ≠ 0)
    (h : ∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) :
    regenerationConditionedLaw hd Q lam l K hK hD =
      regenerationConditionedLaw hd Q lam l L hL hD' := by
  unfold regenerationConditionedLaw
  rw [sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq Q.measure K L h]

/-- Every fixed literal record, including both fields and all future coins,
has the same annealed distribution. -/
theorem sbxS9_annealed_record_law_eq_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) (lam l : ℝ) (K L : CoupledQuenchedLaws d)
    (h : ∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) (k : ℕ) :
    (annealedCoupledLaw Q K).map (regenerationRecord hd lam l k) =
      (annealedCoupledLaw Q L).map (regenerationRecord hd lam l k) := by
  rw [sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq Q K L h]

/-- Finite tuples of actual records can be compared jointly with the entire
physical environment. The indices need not be consecutive or distinct. -/
theorem sbxS9_annealed_joint_records_law_eq_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) (lam l : ℝ) (K L : CoupledQuenchedLaws d)
    (h : ∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) (n : ℕ) (ks : Fin n → ℕ) :
    (annealedCoupledLaw Q K).map
      (fun ωz => (ωz.1, fun j => regenerationRecord hd lam l (ks j) ωz)) =
    (annealedCoupledLaw Q L).map
      (fun ωz => (ωz.1, fun j => regenerationRecord hd lam l (ks j) ωz)) := by
  rw [sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq Q K L h]

/-- Conditioned record distributions use the actual frozen conditioning. -/
theorem sbxS9_conditioned_record_law_eq_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K L : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hL : HasProbabilityLaws Q.measure L)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hD' : annealedCoupledLaw Q.measure L (regenerationNoReturn hd (l / lam)) ≠ 0)
    (h : ∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) (k : ℕ) :
    (regenerationConditionedLaw hd Q lam l K hK hD).map
        (regenerationRecord hd lam l k) =
      (regenerationConditionedLaw hd Q lam l L hL hD').map
        (regenerationRecord hd lam l k) := by
  rw [sbxS9_regenerationConditionedLaw_eq_of_origin_ae_eq
    hd Q lam l K L hK hL hD hD' h]

/-- Conditioning preserves the joint law of the physical environment and
any finite tuple of the complete regeneration records. -/
theorem sbxS9_conditioned_joint_records_law_eq_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K L : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hL : HasProbabilityLaws Q.measure L)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hD' : annealedCoupledLaw Q.measure L (regenerationNoReturn hd (l / lam)) ≠ 0)
    (h : ∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) (n : ℕ) (ks : Fin n → ℕ) :
    (regenerationConditionedLaw hd Q lam l K hK hD).map
        (fun ωz => (ωz.1, fun j => regenerationRecord hd lam l (ks j) ωz)) =
      (regenerationConditionedLaw hd Q lam l L hL hD').map
        (fun ωz => (ωz.1, fun j => regenerationRecord hd lam l (ks j) ωz)) := by
  rw [sbxS9_regenerationConditionedLaw_eq_of_origin_ae_eq
    hd Q lam l K L hK hL hD hD' h]

/-- Equality of measures compares every mixed environment/record integral;
in particular this applies to bounded measurable local-environment tests. -/
theorem sbxS9_annealed_mixed_record_integral_eq_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) (lam l : ℝ) (K L : CoupledQuenchedLaws d)
    (h : ∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) (n : ℕ) (ks : Fin n → ℕ)
    (F : FieldPair d → ℝ)
    (Φ : (Fin n → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ) :
    (∫ ωz, F ωz.1 * Φ (fun j => regenerationRecord hd lam l (ks j) ωz)
      ∂annealedCoupledLaw Q K) =
    ∫ ωz, F ωz.1 * Φ (fun j => regenerationRecord hd lam l (ks j) ωz)
      ∂annealedCoupledLaw Q L := by
  rw [sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq Q K L h]

/-- Mixed local-environment and finite-record tests also agree under the
literal conditioned measures, for arbitrary corresponding witnesses. -/
theorem sbxS9_conditioned_mixed_record_integral_eq_of_origin_ae_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K L : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hL : HasProbabilityLaws Q.measure L)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hD' : annealedCoupledLaw Q.measure L (regenerationNoReturn hd (l / lam)) ≠ 0)
    (h : ∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) (n : ℕ) (ks : Fin n → ℕ)
    (F : FieldPair d → ℝ)
    (Φ : (Fin n → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ) :
    (∫ ωz, F ωz.1 * Φ (fun j => regenerationRecord hd lam l (ks j) ωz)
      ∂regenerationConditionedLaw hd Q lam l K hK hD) =
    ∫ ωz, F ωz.1 * Φ (fun j => regenerationRecord hd lam l (ks j) ωz)
      ∂regenerationConditionedLaw hd Q lam l L hL hD' := by
  rw [sbxS9_regenerationConditionedLaw_eq_of_origin_ae_eq
    hd Q lam l K L hK hL hD hD' h]

/-- The finite-record marginal follows without discarding any component
inside each individual regeneration record. -/
theorem sbxS9_annealed_records_law_eq_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) (lam l : ℝ) (K L : CoupledQuenchedLaws d)
    (h : ∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) (n : ℕ) (ks : Fin n → ℕ) :
    (annealedCoupledLaw Q K).map
      (fun ωz => fun j => regenerationRecord hd lam l (ks j) ωz) =
    (annealedCoupledLaw Q L).map
      (fun ωz => fun j => regenerationRecord hd lam l (ks j) ωz) := by
  rw [sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq Q K L h]

/-- The finite-record marginal under the frozen conditioned law. -/
theorem sbxS9_conditioned_records_law_eq_of_origin_ae_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K L : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hL : HasProbabilityLaws Q.measure L)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hD' : annealedCoupledLaw Q.measure L (regenerationNoReturn hd (l / lam)) ≠ 0)
    (h : ∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) (n : ℕ) (ks : Fin n → ℕ) :
    (regenerationConditionedLaw hd Q lam l K hK hD).map
        (fun ωz => fun j => regenerationRecord hd lam l (ks j) ωz) =
      (regenerationConditionedLaw hd Q lam l L hL hD').map
        (fun ωz => fun j => regenerationRecord hd lam l (ks j) ωz) := by
  rw [sbxS9_regenerationConditionedLaw_eq_of_origin_ae_eq
    hd Q lam l K L hK hL hD hD' h]

/-- Conditional same-node support: prescribed split clauses and separately
proved origin/product-a.e. path-law equality yield the literal annealed law.
This does not supply the path-law equality or an independence reduction. -/
theorem sbxS9_annealed_law_eq_of_split_clauses_and_path_laws_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hprobL : HasProbabilityLaws Q.measure L)
    (hpathL : HasPathMarginals Q.measure L P')
    (hrestartL : HasDeterministicRestart Q.measure (Renewal.regenDelta lam) L)
    (honeL : Renewal.HasOneIntervalKernel Q.measure (Renewal.regenDelta lam)
      δ (l / lam) (Renewal.forceCoord hd) P' L)
    (hP : (∀ᵐ ω ∂Q.measure, P (0, ω) = P' (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, P p = P' p) :
    annealedCoupledLaw Q.measure K = annealedCoupledLaw Q.measure L := by
  exact sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq Q.measure K L
    (sbxS9_coupling_laws_eq_of_prescribed_split_clauses
      hd Q lam h0 h1 l δ P P' K L hK hprobL hpathL hrestartL honeL hP).1

/-- The same conditional split comparison transports the actual event witness
and conditioned measure together, with no new premise on the independence root. -/
theorem sbxS9_conditioned_law_eq_of_split_clauses_and_path_laws_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P P' : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hprobL : HasProbabilityLaws Q.measure L)
    (hpathL : HasPathMarginals Q.measure L P')
    (hrestartL : HasDeterministicRestart Q.measure (Renewal.regenDelta lam) L)
    (honeL : Renewal.HasOneIntervalKernel Q.measure (Renewal.regenDelta lam)
      δ (l / lam) (Renewal.forceCoord hd) P' L)
    (hP : (∀ᵐ ω ∂Q.measure, P (0, ω) = P' (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, P p = P' p)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) :
    ∃ hD' : annealedCoupledLaw Q.measure L (regenerationNoReturn hd (l / lam)) ≠ 0,
      regenerationConditionedLaw hd Q lam l K hK.1 hD =
        regenerationConditionedLaw hd Q lam l L hprobL hD' := by
  have h := (sbxS9_coupling_laws_eq_of_prescribed_split_clauses
    hd Q lam h0 h1 l δ P P' K L hK hprobL hpathL hrestartL honeL hP).1
  have hD' := sbxS9_noReturn_ne_zero_of_origin_ae_eq hd Q.measure K L (l / lam) h hD
  exact ⟨hD', sbxS9_regenerationConditionedLaw_eq_of_origin_ae_eq
    hd Q lam l K L hK.1 hprobL hD hD' h⟩


/-- Probability clauses transfer separately at the origin and spatially a.e. -/
theorem sbxS9_hasProbabilityLaws_of_origin_product_ae_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (K L : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K)
    (h : (∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    HasProbabilityLaws Q L := by
  constructor
  · filter_upwards [hK.1, h.1] with ω hk heq
    exact heq ▸ hk
  · filter_upwards [hK.2, h.2] with p hk heq
    exact heq ▸ hk

/-- The original supplied path law is retained under a.e. coupling changes. -/
theorem sbxS9_hasPathMarginals_of_origin_product_ae_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : HasPathMarginals Q K P)
    (h : (∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    HasPathMarginals Q L P := by
  constructor
  · filter_upwards [hK.1, h.1] with ω hk heq
    rw [← heq]
    exact hk
  · filter_upwards [hK.2, h.2] with p hk heq
    rw [← heq]
    exact hk

/-- Fresh-bit integrals depend only on the current coupled fibre. -/
theorem sbxS9_hasFreshBits_of_origin_product_ae_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (δ : ℝ) (K L : CoupledQuenchedLaws d)
    (hK : HasFreshBits Q Δ δ K)
    (h : (∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    HasFreshBits Q Δ δ L := by
  constructor
  · filter_upwards [hK.1, h.1] with ω hk heq
    intro n H hH hbH
    simpa only [← heq] using hk n H hH hbH
  · filter_upwards [hK.2, h.2] with p hk heq
    intro n H hH hbH
    simpa only [← heq] using hk n H hH hbH

/-- Bridge support depends only on the current coupled fibre. -/
theorem sbxS9_hasSuccessfulBridgeSupport_of_origin_product_ae_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (i : Fin d) (R : ℝ)
    (K L : CoupledQuenchedLaws d) (hK : HasSuccessfulBridgeSupport Q Δ i R K)
    (h : (∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    HasSuccessfulBridgeSupport Q Δ i R L := by
  constructor
  · filter_upwards [hK.1, h.1] with ω hk heq
    change ∀ᵐ z ∂L (0, ω), _
    rw [← heq]
    exact hk
  · filter_upwards [hK.2, h.2] with p hk heq
    change ∀ᵐ z ∂L p, _
    rw [← heq]
    exact hk

/-- The uniform endpoint identity also depends only on the current fibre. -/
theorem sbxS9_hasUniformSuccessfulEndpoint_of_origin_product_ae_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (K L : CoupledQuenchedLaws d) (hK : HasUniformSuccessfulEndpoint Q Δ δ R i K)
    (h : (∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    HasUniformSuccessfulEndpoint Q Δ δ R i L := by
  constructor
  · filter_upwards [hK.1, h.1] with ω hk heq
    intro n H φ hH hbH hφ hbφ
    simpa only [← heq] using hk n H φ hH hbH hφ hbφ
  · filter_upwards [hK.2, h.2] with p hk heq
    intro n H φ hH hbH hφ hbφ
    simpa only [← heq] using hk n H φ hH hbH hφ hbφ

/-- In the one-interval clause the inner laws depend on the unchanged `P`.
Thus both integral identities and all integrability assertions transfer. -/
theorem sbxS9_hasOneIntervalKernel_of_origin_product_ae_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : Renewal.HasOneIntervalKernel Q Δ δ R i P K)
    (h : (∀ᵐ ω ∂Q, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    Renewal.HasOneIntervalKernel Q Δ δ R i P L := by
  constructor
  · filter_upwards [hK.1, h.1] with ω hk heq
    intro n H F hH hbH hF hbF hsegment
    simpa only [← heq] using hk n H F hH hbH hF hbF hsegment
  · filter_upwards [hK.2, h.2] with p hk heq
    intro n H F hH hbH hF hbF hsegment
    simpa only [← heq] using hk n H F hH hbH hF hbF hsegment

/-- Spatial null sets are avoided at positive grid times by the original
endpoint density. At zero the starting fibre equality is used explicitly. -/
theorem sbxS9_ae_restart_fibres_eq_of_start_and_endpoint_ac {d : ℕ}
    (Δ : ℝ≥0) (K L : CoupledQuenchedLaws d) (x : Vec d) (ω : FieldPair d)
    (hstart : ∀ᵐ z ∂K (x, ω), z.1 0 = x)
    (hdensity : ∀ n : ℕ, 1 ≤ n →
      (K (x, ω)).map (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) ≪
        (volume : Measure (Vec d)))
    (hx : K (x, ω) = L (x, ω))
    (hsp : ∀ᵐ y ∂(volume : Measure (Vec d)), K (y, ω) = L (y, ω)) (n : ℕ) :
    ∀ᵐ z ∂K (x, ω),
      K (z.1 ((n : ℝ≥0) * Δ), ω) = L (z.1 ((n : ℝ≥0) * Δ), ω) := by
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, zero_mul]
    filter_upwards [hstart] with z hz
    rw [hz]
    exact hx
  · exact ae_of_ae_map
      (((measurable_pathPosition ((n : ℝ≥0) * Δ)).comp measurable_fst).aemeasurable)
      ((hdensity n (by omega)).ae_le hsp)

/-- Comparing the actual nested restart integrals needs no extra
integrability premise: the inner measures agree at almost every endpoint. -/
theorem sbxS9_nested_restart_integral_eq_of_start_and_endpoint_ac {d : ℕ}
    (Δ : ℝ≥0) (K L : CoupledQuenchedLaws d) (x : Vec d) (ω : FieldPair d)
    (hstart : ∀ᵐ z ∂K (x, ω), z.1 0 = x)
    (hdensity : ∀ n : ℕ, 1 ≤ n →
      (K (x, ω)).map (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) ≪
        (volume : Measure (Vec d)))
    (hx : K (x, ω) = L (x, ω))
    (hsp : ∀ᵐ y ∂(volume : Measure (Vec d)), K (y, ω) = L (y, ω))
    (n : ℕ) (H Φ : CoupledSample d → ℝ) :
    (∫ z, H z * (∫ z', Φ z' ∂K (z.1 ((n : ℝ≥0) * Δ), ω)) ∂K (x, ω)) =
      ∫ z, H z * (∫ z', Φ z' ∂L (z.1 ((n : ℝ≥0) * Δ), ω)) ∂L (x, ω) := by
  rw [← hx]
  apply integral_congr_ae
  filter_upwards [sbxS9_ae_restart_fibres_eq_of_start_and_endpoint_ac
    Δ K L x ω hstart hdensity hx hsp n] with z hz
  rw [hz]

/-- A deterministic restart clause transfers using the actual original
path marginal, starts, and endpoint densities, rather than pointwise kernel equality. -/
theorem sbxS9_deterministicRestartAt_of_eq_and_path_endpoint_ac {d : ℕ}
    (Δ : ℝ≥0) (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (x : Vec d) (ω : FieldPair d)
    (hK : DeterministicRestartAt Δ K (x, ω))
    (hm : (K (x, ω)).map Prod.fst = P (x, ω))
    (hstart : ∀ᵐ γ ∂P (x, ω), γ 0 = x)
    (hdensity : ∀ n : ℕ, 1 ≤ n →
      (P (x, ω)).map (pathPosition ((n : ℝ≥0) * Δ)) ≪ (volume : Measure (Vec d)))
    (hx : K (x, ω) = L (x, ω))
    (hsp : ∀ᵐ y ∂(volume : Measure (Vec d)), K (y, ω) = L (y, ω)) :
    DeterministicRestartAt Δ L (x, ω) := by
  have hs : ∀ᵐ z ∂K (x, ω), z.1 0 = x :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hm]; exact hstart)
  have hdens : ∀ n : ℕ, 1 ≤ n →
      (K (x, ω)).map (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) ≪
        (volume : Measure (Vec d)) := fun n hn =>
    coupled_endpoint_density_of_path_marginal P K (x, ω) hm _ (hdensity n hn)
  intro n H Φ hH hbH hΦ hbΦ
  calc
    (∫ z, H z * Φ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂L (x, ω)) =
        ∫ z, H z * Φ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂K (x, ω) := by rw [hx]
    _ = ∫ z, H z * (∫ z', Φ z' ∂K (z.1 ((n : ℝ≥0) * Δ), ω)) ∂K (x, ω) :=
      hK n H Φ hH hbH hΦ hbΦ
    _ = ∫ z, H z * (∫ z', Φ z' ∂L (z.1 ((n : ℝ≥0) * Δ), ω)) ∂L (x, ω) :=
      sbxS9_nested_restart_integral_eq_of_start_and_endpoint_ac
        Δ K L x ω hs hdens hx hsp n H Φ

/-- The original GMP realization supplies starts and densities. Fubini is
used only on the spatial-a.e. equality; the origin equality stays separate. -/
theorem sbxS9_hasDeterministicRestart_of_origin_product_ae_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (h : (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p) :
    HasDeterministicRestart Q.measure (Renewal.regenDelta lam) L := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have hg := ae_coupledEnvironmentRegular hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  have hsp : ∀ᵐ ω ∂Q.measure,
      ∀ᵐ y ∂(volume : Measure (Vec d)), K (y, ω) = L (y, ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := Q.measure)
        (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae h.2)
  have htransfer : ∀ ω, CoupledEnvironmentRegular hd Λ₀ Q.ellipticity_parameter
      lam h0.le h1 (Renewal.regenDelta lam) δ (l / lam) (Renewal.forceCoord hd) P K ω →
      (∀ᵐ y ∂(volume : Measure (Vec d)), K (y, ω) = L (y, ω)) →
      ∀ x, (K (x, ω)).map Prod.fst = P (x, ω) →
      DeterministicRestartAt (Renewal.regenDelta lam) K (x, ω) →
      K (x, ω) = L (x, ω) →
      DeterministicRestartAt (Renewal.regenDelta lam) L (x, ω) := by
    intro ω hω hspω x hm hr heq
    have hs : ∀ᵐ γ ∂P (x, ω), γ 0 = x := by
      obtain ⟨_, r, hP⟩ := hω.1
      rw [hP x]
      exact r.pathLaw_starts_at x
    exact sbxS9_deterministicRestartAt_of_eq_and_path_endpoint_ac
      (Renewal.regenDelta lam) P K L x ω hr hm hs (fun n hn => hω.2.2.2 n hn x)
      heq hspω
  constructor
  · filter_upwards [hg, hsp, h.1] with ω hω hs heq
    exact htransfer ω hω hs 0 hω.2.1.2.1 hω.2.1.2.2.1 heq
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae (hg.and hsp),
      hK.2.1.2, hK.2.2.2.2.1.2, h.2] with p hp hm hr heq
    exact htransfer p.2 hp.1 hp.2 p.1 hm hr heq

/-- Full coupling stability for a.e. versions, retaining the original `P`
and its GMP realization. This helper does not produce the a.e. equalities. -/
theorem sbxS9_isRegenerationCoupling_of_origin_product_ae_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (h : (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p) :
    IsRegenerationCoupling hd Q lam l δ h0.le h1 P L := by
  exact ⟨sbxS9_hasProbabilityLaws_of_origin_product_ae_eq Q.measure K L hK.1 h,
    sbxS9_hasPathMarginals_of_origin_product_ae_eq Q.measure P K L hK.2.1 h,
    hK.2.2.1,
    sbxS9_hasFreshBits_of_origin_product_ae_eq Q.measure (Renewal.regenDelta lam)
      δ K L hK.2.2.2.1 h,
    sbxS9_hasDeterministicRestart_of_origin_product_ae_eq hd Q lam h0 h1 l δ P K L hK h,
    sbxS9_hasSuccessfulBridgeSupport_of_origin_product_ae_eq Q.measure
      (Renewal.regenDelta lam) (Renewal.forceCoord hd) (l / lam) K L hK.2.2.2.2.2.1 h,
    sbxS9_hasUniformSuccessfulEndpoint_of_origin_product_ae_eq Q.measure
      (Renewal.regenDelta lam) δ (l / lam) (Renewal.forceCoord hd)
      K L hK.2.2.2.2.2.2.1 h,
    sbxS9_hasOneIntervalKernel_of_origin_product_ae_eq Q.measure
      (Renewal.regenDelta lam) δ (l / lam) (Renewal.forceCoord hd)
      P K L hK.2.2.2.2.2.2.2 h⟩

/-- A version change transports the full coupling, the genuine no-return
witness, the conditioned law, and all finite records jointly with the environment. -/
theorem sbxS9_conditioned_records_of_coupling_version {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (h : (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) :
    ∃ hL : IsRegenerationCoupling hd Q lam l δ h0.le h1 P L,
      ∃ hD' : annealedCoupledLaw Q.measure L (regenerationNoReturn hd (l / lam)) ≠ 0,
        regenerationConditionedLaw hd Q lam l K hK.1 hD =
          regenerationConditionedLaw hd Q lam l L hL.1 hD' ∧
        ∀ (n : ℕ) (ks : Fin n → ℕ),
          (regenerationConditionedLaw hd Q lam l K hK.1 hD).map
              (fun ωz => (ωz.1, fun j => regenerationRecord hd lam l (ks j) ωz)) =
            (regenerationConditionedLaw hd Q lam l L hL.1 hD').map
              (fun ωz => (ωz.1, fun j => regenerationRecord hd lam l (ks j) ωz)) := by
  have hL := sbxS9_isRegenerationCoupling_of_origin_product_ae_eq
    hd Q lam h0 h1 l δ P K L hK h
  have hD' := sbxS9_noReturn_ne_zero_of_origin_ae_eq hd Q.measure K L (l / lam) h.1 hD
  refine ⟨hL, hD', ?_, ?_⟩
  · exact sbxS9_regenerationConditionedLaw_eq_of_origin_ae_eq
      hd Q lam l K L hK.1 hL.1 hD hD' h.1
  · exact fun n ks => sbxS9_conditioned_joint_records_law_eq_of_origin_ae_eq
      hd Q lam l K L hK.1 hL.1 hD hD' h.1 n ks

/-- The literal restriction defining the killed segment commutes with recentering.
No regularity or choice of a pointwise density is needed. -/
theorem sbxS9_killedSegmentLaw_recenter {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (a : Vec d) (p : Vec d × FieldPair d) :
    (Renewal.killedSegmentLaw Δ R i P (sbxS9RecenterInput a p).1
      (sbxS9RecenterInput a p).2).map (recenterPathEquiv a) =
      Renewal.killedSegmentLaw Δ R i (sbxS9RecenteredPathLaws P a) p.1 p.2 := by
  have hset : (recenterPathEquiv a) ⁻¹'
      {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R p.1} =
      {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ →
        γ t ∈ couplingRegion i R (a + p.1)} := by
    ext γ
    have hx : a + p.1 - a = p.1 := by abel
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    change (∀ t : ℝ≥0, t ≤ Δ → γ t - a ∈ couplingRegion i R p.1) ↔ _
    have hgeom : ∀ y : Vec d, y - a ∈ couplingRegion i R p.1 ↔
        y ∈ couplingRegion i R (a + p.1) := fun y => by
      simpa only [hx] using sub_mem_couplingRegion_iff i R a y (a + p.1)
    simp only [hgeom]
  unfold Renewal.killedSegmentLaw
  rw [sbxS9RecenteredPathLaws_apply, (recenterPathEquiv a).restrict_map, hset]
  rfl

/-- The killed endpoint measure is transported by the same Euclidean translation. -/
theorem sbxS9_killedEndpointLaw_recenter {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (a : Vec d) (p : Vec d × FieldPair d) :
    ((Renewal.killedSegmentLaw Δ R i P (sbxS9RecenterInput a p).1
      (sbxS9RecenterInput a p).2).map (fun γ : Path d => γ Δ)).map
        (MeasurableEquiv.addRight (-a)) =
      (Renewal.killedSegmentLaw Δ R i (sbxS9RecenteredPathLaws P a) p.1 p.2).map
        (fun γ : Path d => γ Δ) := by
  rw [← sbxS9_killedSegmentLaw_recenter Δ R i P a p,
    Measure.map_map (continuous_eval_const Δ).measurable (recenterPathEquiv a).measurable,
    Measure.map_map (MeasurableEquiv.addRight (-a)).measurable
      (continuous_eval_const Δ).measurable]
  rfl

/-- The actual endpoint RN densities agree only volume-almost everywhere.
The equality includes the zero-density case without division. -/
theorem sbxS9_killedEndpointDensity_recenter {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (a : Vec d) (p : Vec d × FieldPair d)
    [IsProbabilityMeasure (P (sbxS9RecenterInput a p))] :
    (fun y : Vec d =>
      ((Renewal.killedSegmentLaw Δ R i (sbxS9RecenteredPathLaws P a) p.1 p.2).map
        (fun γ : Path d => γ Δ)).rnDeriv volume (y - a)) =ᵐ[volume]
      ((Renewal.killedSegmentLaw Δ R i P (sbxS9RecenterInput a p).1
        (sbxS9RecenterInput a p).2).map (fun γ : Path d => γ Δ)).rnDeriv volume := by
  let q : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-a)
  have hv : (volume : Measure (Vec d)).map q = volume :=
    (measurePreserving_add_right volume (-a)).map_eq
  have : IsFiniteMeasure (Renewal.killedSegmentLaw Δ R i P
      (sbxS9RecenterInput a p).1 (sbxS9RecenterInput a p).2) :=
    inferInstanceAs (IsFiniteMeasure ((P (sbxS9RecenterInput a p)).restrict _))
  have hrn := q.measurableEmbedding.rnDeriv_map
    ((Renewal.killedSegmentLaw Δ R i P (sbxS9RecenterInput a p).1
      (sbxS9RecenterInput a p).2).map (fun γ : Path d => γ Δ)) volume
  rw [hv, sbxS9_killedEndpointLaw_recenter Δ R i P a p] at hrn
  exact hrn

/-- Conditioning and its exact mass denominator commute with a measurable
coordinate equivalence, including null conditioning sets. -/
theorem sbxS9_map_cond_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (s : Set β) :
    (ProbabilityTheory.cond μ (e ⁻¹' s)).map e = ProbabilityTheory.cond (μ.map e) s := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, e.restrict_map, e.measurableEmbedding.map_apply]
  exact e.measurable.aemeasurable

/-- Transport the literal RN bridge mixture, with no density representative
or nonzero-density premise. RN transport retains the singular and zero branches. -/
theorem sbxS9_killedBridgeMixture_recenter {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (hR : 0 < R) (i : Fin d) (P : QuenchedPathLaws d)
    (a : Vec d) (p : Vec d × FieldPair d)
    [IsProbabilityMeasure (P (sbxS9RecenterInput a p))] :
    (Renewal.killedBridgeMixture Δ R i P (sbxS9RecenterInput a p).1
      (sbxS9RecenterInput a p).2).map (recenterPathEquiv a) =
      Renewal.killedBridgeMixture Δ R i (sbxS9RecenteredPathLaws P a) p.1 p.2 := by
  let q : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-a)
  let μ := Renewal.killedSegmentLaw Δ R i P (sbxS9RecenterInput a p).1
    (sbxS9RecenterInput a p).2
  let η := ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R (a + p.1))
  have : IsFiniteMeasure μ :=
    inferInstanceAs (IsFiniteMeasure ((P (sbxS9RecenterInput a p)).restrict _))
  have : IsProbabilityMeasure η := cond_isProbabilityMeasure_of_finite
    (endpointBall_volume_pos i R hR (a + p.1)).ne'
    (endpointBall_volume_ne_top i R hR (a + p.1))
  have hB : q ⁻¹' endpointBall i R p.1 = endpointBall i R (a + p.1) := by
    ext y
    have hx : a + p.1 - a = p.1 := by abel
    change y - a ∈ endpointBall i R p.1 ↔ _
    simpa only [hx] using sub_mem_endpointBall_iff i R a y (a + p.1)
  have hv : (volume : Measure (Vec d)).map q = volume :=
    (measurePreserving_add_right volume (-a)).map_eq
  have hη : η.map q = ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R p.1) := by
    dsimp only [η]
    rw [← hB, sbxS9_map_cond_equiv, hv]
  have ht := EinsteinRelation.Probability.map_endpoint_rnDeriv
    (recenterPathEquiv a) q (fun γ : Path d => γ Δ) (fun γ : Path d => γ Δ)
    (continuous_eval_const Δ).measurable (continuous_eval_const Δ).measurable
    (fun _ => rfl) μ η
  rw [hη, show μ.map (recenterPathEquiv a) =
      Renewal.killedSegmentLaw Δ R i (sbxS9RecenteredPathLaws P a) p.1 p.2 from
        sbxS9_killedSegmentLaw_recenter Δ R i P a p] at ht
  exact ht

/-- All finite-history tests and both bit branches transport, including every
Bochner integrability conjunct. Only the supplied path kernel is recentered. -/
theorem sbxS9_oneIntervalKernelAt_recenter {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (a : Vec d) (p : Vec d × FieldPair d)
    (hprob : ∀ x : Vec d, IsProbabilityMeasure (P (x, translate (-a) p.2)))
    (h : Renewal.OneIntervalKernelAt Δ δ R i P K (sbxS9RecenterInput a p)) :
    Renewal.OneIntervalKernelAt Δ δ R i (sbxS9RecenteredPathLaws P a)
      (sbxS9RecenteredCoupledLaws K a) p := by
  intro n H F hH hbH hF hbF hseg
  obtain ⟨B, hB⟩ := hbH
  obtain ⟨C, hC⟩ := hbF
  have ht := h n (fun z => H (recenterSample a z))
    (fun γ => F (recenterPathEquiv a γ))
    (measurable_finiteHistory_comp_recenter Δ n a H hH) ⟨B, fun z => hB _⟩
    (hF.comp (recenterPathEquiv a).measurable) ⟨C, fun γ => hC _⟩
    (fun γ γ' heq => hseg _ _ (fun t ht => by
      change γ t - a = γ' t - a
      rw [heq t ht]))
  have hshift : ∀ y : Vec d, a + (y - a) = y := fun y => by abel
  have hPint : ∀ y : Vec d,
      (∫ γ, F γ ∂sbxS9RecenteredPathLaws P a (y - a, p.2)) =
        ∫ γ, F (recenterPathEquiv a γ) ∂P (y, translate (-a) p.2) := by
    intro y
    rw [sbxS9RecenteredPathLaws_apply, integral_map_equiv]
    simp only [sbxS9RecenterInput, hshift]
  have hBint : ∀ y : Vec d,
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i
        (sbxS9RecenteredPathLaws P a) (y - a) p.2) =
      ∫ γ, F (recenterPathEquiv a γ) ∂Renewal.killedBridgeMixture Δ R i
        P y (translate (-a) p.2) := by
    intro y
    have : IsProbabilityMeasure (P (sbxS9RecenterInput a (y - a, p.2))) :=
      hprob (a + (y - a))
    rw [← sbxS9_killedBridgeMixture_recenter Δ R hR i P a (y - a, p.2),
      integral_map_equiv]
    simp only [sbxS9RecenterInput, hshift]
  simp only [sbxS9RecenteredCoupledLaws_apply, integrable_map_equiv,
    integral_map_equiv]
  have htime : ∀ (γ : Path d) (t : ℝ≥0),
      pathTimeShift (recenterPath a γ) t = recenterPathEquiv a (pathTimeShift γ t) :=
    fun _ _ => rfl
  convert ht using 1 <;>
    simp only [Function.comp_def, recenterSampleEquiv_apply, recenterSample_fst,
      recenterSample_snd, recenterPath_apply, htime, hPint, hBint, sbxS9RecenterInput] <;> rfl

/-- One common spatial good set carries the origin and product-a.e.
one-interval clauses. Probability of all path fibres is an environment-a.e.
property of the supplied kernel, not a recentered process existence premise. -/
theorem sbxS9_hasOneIntervalKernel_recenter {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (Δ : ℝ≥0) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)))
    (h : Renewal.HasOneIntervalKernel Q Δ δ R i P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      Renewal.HasOneIntervalKernel Q Δ δ R i (sbxS9RecenteredPathLaws P a)
        (sbxS9RecenteredCoupledLaws K a) := by
  have hp : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q,
      (∀ x : Vec d, IsProbabilityMeasure (P (x, p.2))) ∧
        Renewal.OneIntervalKernelAt Δ δ R i P K p :=
    (Measure.quasiMeasurePreserving_snd.ae hprob).and h.2
  filter_upwards [sbxS9_ae_recenterInput Q hQ hp] with a ha
  constructor
  · filter_upwards [ha.1] with ω hω
    exact sbxS9_oneIntervalKernelAt_recenter Δ δ R hR i P K a (0, ω) hω.1 hω.2
  · filter_upwards [ha.2] with p hp
    exact sbxS9_oneIntervalKernelAt_recenter Δ δ R hR i P K a p hp.1 hp.2

/-- The actual coupling supplies every hypothesis of the six recentered
algebraic clauses. No GMP realization or uniform-endpoint clause for the
recentered law is claimed. These are direct structural inputs to split-law
uniqueness, whose path-law equality input remains separate. -/
theorem sbxS9_six_coupling_clauses_recenter {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasProbabilityLaws Q.measure (sbxS9RecenteredCoupledLaws K a) ∧
      HasPathMarginals Q.measure (sbxS9RecenteredCoupledLaws K a)
        (sbxS9RecenteredPathLaws P a) ∧
      HasFreshBits Q.measure (Renewal.regenDelta lam) δ (sbxS9RecenteredCoupledLaws K a) ∧
      HasDeterministicRestart Q.measure (Renewal.regenDelta lam)
        (sbxS9RecenteredCoupledLaws K a) ∧
      HasSuccessfulBridgeSupport Q.measure (Renewal.regenDelta lam)
        (Renewal.forceCoord hd) (l / lam) (sbxS9RecenteredCoupledLaws K a) ∧
      Renewal.HasOneIntervalKernel Q.measure (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) (sbxS9RecenteredPathLaws P a)
        (sbxS9RecenteredCoupledLaws K a) := by
  have hprob := isProbabilityMeasure_of_isGMPReducedKernel hd Q.ellipticity_parameter
    Q lam h0.le h1 P hK.2.2.1
  have hone := sbxS9_hasOneIntervalKernel_recenter Q.measure Q.stationary
    (Renewal.regenDelta lam) δ (l / lam) (div_pos hl h0) (Renewal.forceCoord hd)
    P K hprob hK.2.2.2.2.2.2.2
  filter_upwards [sbxS9_five_coupling_clauses_recenter Q (Renewal.regenDelta lam)
    δ (l / lam) (Renewal.forceCoord hd) P K hK.1 hK.2.1 hK.2.2.2.1
    hK.2.2.2.2.1 hK.2.2.2.2.2.1, hone] with a ha ho
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2, ho⟩

/-- Direct split-law comparison after the separately established path-law
covariance is supplied. All recentered split clauses used by uniqueness come
from the actual coupling. This conditional consumer supplies neither the missing
path-law covariance nor a GMP realization for the recentered kernel. -/
theorem sbxS9_recentered_coupling_laws_eq_of_path_laws_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      ((∀ᵐ ω ∂Q.measure, P (0, ω) = sbxS9RecenteredPathLaws P a (0, ω)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          P p = sbxS9RecenteredPathLaws P a p) →
      (∀ᵐ ω ∂Q.measure, K (0, ω) = sbxS9RecenteredCoupledLaws K a (0, ω)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          K p = sbxS9RecenteredCoupledLaws K a p := by
  filter_upwards [sbxS9_six_coupling_clauses_recenter hd Q lam h0 h1 l δ hl P K hK]
    with a ha
  intro hP
  exact sbxS9_coupling_laws_eq_of_prescribed_split_clauses hd Q lam h0 h1 l δ
    P (sbxS9RecenteredPathLaws P a) K (sbxS9RecenteredCoupledLaws K a)
    hK ha.1 ha.2.1 ha.2.2.2.1 ha.2.2.2.2.2 hP

/-- Zero recentering preserves both input coordinates. -/
@[simp] theorem sbxS9_recenterInput_zero {d : ℕ} (p : Vec d × FieldPair d) :
    sbxS9RecenterInput 0 p = p := by
  simp only [sbxS9RecenterInput, zero_add, neg_zero, translate_zero, Prod.mk.eta]

/-- The old input for two successive recenterings has the sum displacement. -/
theorem sbxS9_recenterInput_add {d : ℕ} (a b : Vec d)
    (p : Vec d × FieldPair d) :
    sbxS9RecenterInput a (sbxS9RecenterInput b p) =
      sbxS9RecenterInput (a + b) p := by
  simp only [sbxS9RecenterInput, translate_add, neg_add, add_assoc]

/-- Undoing an input recentering restores the starting point and both fields. -/
@[simp] theorem sbxS9_recenterInput_neg {d : ℕ} (a : Vec d)
    (p : Vec d × FieldPair d) :
    sbxS9RecenterInput (-a) (sbxS9RecenterInput a p) = p := by
  rw [sbxS9_recenterInput_add, neg_add_cancel, sbxS9_recenterInput_zero]

/-- The actual input recentering is an invertible measurable coordinate change. -/
def sbxS9RecenterInputEquiv {d : ℕ} (a : Vec d) :
    (Vec d × FieldPair d) ≃ᵐ (Vec d × FieldPair d) where
  toFun := sbxS9RecenterInput a
  invFun := sbxS9RecenterInput (-a)
  left_inv := sbxS9_recenterInput_neg a
  right_inv p := by
    rw [sbxS9_recenterInput_add, add_neg_cancel, sbxS9_recenterInput_zero]
  measurable_toFun := sbxS9_measurable_recenterInput a
  measurable_invFun := sbxS9_measurable_recenterInput (-a)

/-- Zero output recentering preserves the entire continuous path. -/
@[simp] theorem sbxS9_recenterPathEquiv_zero {d : ℕ} (γ : Path d) :
    recenterPathEquiv 0 γ = γ := by
  ext t i
  exact sub_zero _

/-- Successive output recenterings subtract the sum, in the map-composition order. -/
theorem sbxS9_recenterPathEquiv_add {d : ℕ} (a b : Vec d) (γ : Path d) :
    recenterPathEquiv b (recenterPathEquiv a γ) = recenterPathEquiv (a + b) γ := by
  ext t i
  change (γ t i - a i) - b i = γ t i - (a i + b i)
  exact sub_sub _ _ _

/-- The negative displacement is the inverse on actual paths. -/
@[simp] theorem sbxS9_recenterPathEquiv_neg {d : ℕ} (a : Vec d) (γ : Path d) :
    recenterPathEquiv (-a) (recenterPathEquiv a γ) = γ := by
  rw [sbxS9_recenterPathEquiv_add, add_neg_cancel, sbxS9_recenterPathEquiv_zero]

/-- Zero output recentering also preserves every coin coordinate. -/
theorem sbxS9_recenterSampleEquiv_zero {d : ℕ} (z : CoupledSample d) :
    recenterSampleEquiv 0 z = z := by
  exact Prod.ext (sbxS9_recenterPathEquiv_zero z.1) rfl

/-- The full path-and-coins output equivalences obey the same composition law. -/
theorem sbxS9_recenterSampleEquiv_add {d : ℕ} (a b : Vec d) (z : CoupledSample d) :
    recenterSampleEquiv b (recenterSampleEquiv a z) =
      recenterSampleEquiv (a + b) z := by
  exact Prod.ext (sbxS9_recenterPathEquiv_add a b z.1) rfl

/-- Reversing the displacement restores paths and all coins. -/
theorem sbxS9_recenterSampleEquiv_neg {d : ℕ} (a : Vec d)
    (z : CoupledSample d) :
    recenterSampleEquiv (-a) (recenterSampleEquiv a z) = z := by
  rw [sbxS9_recenterSampleEquiv_add, add_neg_cancel, sbxS9_recenterSampleEquiv_zero]

/-- Recentring by zero preserves the supplied path kernel, even exceptional fibres. -/
@[simp] theorem sbxS9_recenteredPathLaws_zero {d : ℕ} (P : QuenchedPathLaws d) :
    sbxS9RecenteredPathLaws P 0 = P := by
  apply Kernel.ext
  intro p
  rw [sbxS9RecenteredPathLaws_apply, sbxS9_recenterInput_zero]
  have he : (recenterPathEquiv (0 : Vec d) : Path d → Path d) = id :=
    funext sbxS9_recenterPathEquiv_zero
  rw [he, Measure.map_id]

/-- Kernel recentering composes by addition, with both input and output maps. -/
theorem sbxS9_recenteredPathLaws_add {d : ℕ} (P : QuenchedPathLaws d)
    (a b : Vec d) :
    sbxS9RecenteredPathLaws (sbxS9RecenteredPathLaws P a) b =
      sbxS9RecenteredPathLaws P (a + b) := by
  apply Kernel.ext
  intro p
  rw [sbxS9RecenteredPathLaws_apply, sbxS9RecenteredPathLaws_apply,
    sbxS9RecenteredPathLaws_apply, sbxS9_recenterInput_add,
    Measure.map_map (recenterPathEquiv b).measurable (recenterPathEquiv a).measurable]
  congr 1
  exact funext (sbxS9_recenterPathEquiv_add a b)

/-- Negative recentering restores the exact supplied path kernel. -/
@[simp] theorem sbxS9_recenteredPathLaws_neg {d : ℕ} (P : QuenchedPathLaws d)
    (a : Vec d) :
    sbxS9RecenteredPathLaws (sbxS9RecenteredPathLaws P a) (-a) = P := by
  rw [sbxS9_recenteredPathLaws_add, add_neg_cancel, sbxS9_recenteredPathLaws_zero]

/-- Zero recentering preserves the entire supplied coupled kernel. -/
@[simp] theorem sbxS9_recenteredCoupledLaws_zero {d : ℕ} (K : CoupledQuenchedLaws d) :
    sbxS9RecenteredCoupledLaws K 0 = K := by
  apply Kernel.ext
  intro p
  rw [sbxS9RecenteredCoupledLaws_apply, sbxS9_recenterInput_zero]
  have he : (recenterSampleEquiv (0 : Vec d) : CoupledSample d → CoupledSample d) = id :=
    funext sbxS9_recenterSampleEquiv_zero
  rw [he, Measure.map_id]

/-- The supplied coupled kernels obey the exact additive cocycle. -/
theorem sbxS9_recenteredCoupledLaws_add {d : ℕ} (K : CoupledQuenchedLaws d)
    (a b : Vec d) :
    sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) b =
      sbxS9RecenteredCoupledLaws K (a + b) := by
  apply Kernel.ext
  intro p
  rw [sbxS9RecenteredCoupledLaws_apply, sbxS9RecenteredCoupledLaws_apply,
    sbxS9RecenteredCoupledLaws_apply, sbxS9_recenterInput_add,
    Measure.map_map (recenterSampleEquiv b).measurable
      (recenterSampleEquiv a).measurable]
  congr 1
  exact funext (sbxS9_recenterSampleEquiv_add a b)

/-- Inverting the recentering restores the exact joint path-and-coins law. -/
@[simp] theorem sbxS9_recenteredCoupledLaws_neg {d : ℕ} (K : CoupledQuenchedLaws d)
    (a : Vec d) :
    sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) (-a) = K := by
  rw [sbxS9_recenteredCoupledLaws_add, add_neg_cancel, sbxS9_recenteredCoupledLaws_zero]

/-- Every fixed pair of recenterings preserves product-a.e. information.
This assertion has no origin-fibre specialization. -/
theorem sbxS9_ae_recenterInput_add {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    {p : Vec d × FieldPair d → Prop}
    (hp : ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, p q) (a b : Vec d) :
    ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q,
      p (sbxS9RecenterInput a (sbxS9RecenterInput b q)) :=
  (sbxS9_measurePreserving_recenterInput Q hQ b).quasiMeasurePreserving.ae
    ((sbxS9_measurePreserving_recenterInput Q hQ a).quasiMeasurePreserving.ae hp)

/-- A specified countable family of shifts has one common spatial good set,
and one common environment set at each such origin. No origin at a fixed
exceptional base point is inferred. -/
theorem sbxS9_ae_countable_recenterInput {d : ℕ} {ι : Type*} [Countable ι]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (shifts : ι → Vec d) {p : Vec d × FieldPair d → Prop}
    (hp : ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, p q) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q, ∀ j, p (sbxS9RecenterInput (a + shifts j) (0, η))) ∧
      ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q,
        ∀ j, p (sbxS9RecenterInput (a + shifts j) q) := by
  have hs : ∀ j, ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q, p (sbxS9RecenterInput (a + shifts j) (0, η))) ∧
      ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q,
        p (sbxS9RecenterInput (a + shifts j) q) := fun j =>
    (measurePreserving_add_right (volume : Measure (Vec d)) (shifts j)).quasiMeasurePreserving.ae
      (sbxS9_ae_recenterInput Q hQ hp)
  filter_upwards [ae_all_iff.mpr hs] with a ha
  exact ⟨ae_all_iff.mpr (fun j => (ha j).1), ae_all_iff.mpr (fun j => (ha j).2)⟩

/-- Countably many two-stage recenterings of path-law versions agree on
common origin and product sets. The right-hand side uses a single sum shift. -/
theorem sbxS9_countable_recenteredPathLaws_eq_of_product_ae_eq
    {d : ℕ} {ι : Type*} [Countable ι]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (shifts : ι → Vec d) (P P' : QuenchedPathLaws d)
    (h : ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, P q = P' q) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ ω ∂Q, ∀ j,
        sbxS9RecenteredPathLaws (sbxS9RecenteredPathLaws P a) (shifts j) (0, ω) =
          sbxS9RecenteredPathLaws P' (a + shifts j) (0, ω)) ∧
      ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, ∀ j,
        sbxS9RecenteredPathLaws (sbxS9RecenteredPathLaws P a) (shifts j) q =
          sbxS9RecenteredPathLaws P' (a + shifts j) q := by
  filter_upwards [sbxS9_ae_countable_recenterInput Q hQ shifts h] with a ha
  constructor
  · filter_upwards [ha.1] with ω hω
    intro j
    rw [sbxS9_recenteredPathLaws_add, sbxS9RecenteredPathLaws_apply,
      sbxS9RecenteredPathLaws_apply, hω j]
  · filter_upwards [ha.2] with q hq
    intro j
    rw [sbxS9_recenteredPathLaws_add, sbxS9RecenteredPathLaws_apply,
      sbxS9RecenteredPathLaws_apply, hq j]

/-- The same common versions retain all coins and every path coordinate.
This compares versions of supplied kernels; it asserts no physical covariance. -/
theorem sbxS9_countable_recenteredCoupledLaws_eq_of_product_ae_eq
    {d : ℕ} {ι : Type*} [Countable ι]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (shifts : ι → Vec d) (K L : CoupledQuenchedLaws d)
    (h : ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, K q = L q) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ ω ∂Q, ∀ j,
        sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) (shifts j) (0, ω) =
          sbxS9RecenteredCoupledLaws L (a + shifts j) (0, ω)) ∧
      ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, ∀ j,
        sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) (shifts j) q =
          sbxS9RecenteredCoupledLaws L (a + shifts j) q := by
  filter_upwards [sbxS9_ae_countable_recenterInput Q hQ shifts h] with a ha
  constructor
  · filter_upwards [ha.1] with ω hω
    intro j
    rw [sbxS9_recenteredCoupledLaws_add, sbxS9RecenteredCoupledLaws_apply,
      sbxS9RecenteredCoupledLaws_apply, hω j]
  · filter_upwards [ha.2] with q hq
    intro j
    rw [sbxS9_recenteredCoupledLaws_add, sbxS9RecenteredCoupledLaws_apply,
      sbxS9RecenteredCoupledLaws_apply, hq j]

/-- Probability fibres for a countable family share one spatial good set.
Two successive recenterings use their exact cocycle normal form. -/
theorem sbxS9_countable_hasProbabilityLaws_recenter {d : ℕ} {ι : Type*} [Countable ι]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (shifts : ι → Vec d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ j,
      HasProbabilityLaws Q
        (sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) (shifts j)) := by
  have hs : ∀ j, ∀ᵐ a ∂(volume : Measure (Vec d)),
      HasProbabilityLaws Q (sbxS9RecenteredCoupledLaws K (a + shifts j)) := fun j =>
    (measurePreserving_add_right (volume : Measure (Vec d)) (shifts j)).quasiMeasurePreserving.ae
      (sbxS9_hasProbabilityLaws_recenter Q hQ K hK)
  filter_upwards [ae_all_iff.mpr hs] with a ha j
  rw [sbxS9_recenteredCoupledLaws_add]
  exact ha j

/-- All exact finite histories agree on the same common environment and
product sets. The stopped history retains its literal path and coin data. -/
theorem sbxS9_countable_finite_histories_eq_of_product_ae_eq
    {d : ℕ} {ι : Type*} [Countable ι]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (shifts : ι → Vec d) (K L : CoupledQuenchedLaws d)
    (h : ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, K q = L q) (Δ : ℝ≥0) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ ω ∂Q, ∀ j n,
        (sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a)
          (shifts j) (0, ω)).map (Probability.stoppedHistorySample Δ n) =
        (sbxS9RecenteredCoupledLaws L (a + shifts j) (0, ω)).map
          (Probability.stoppedHistorySample Δ n)) ∧
      ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, ∀ j n,
        (sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a)
          (shifts j) q).map (Probability.stoppedHistorySample Δ n) =
        (sbxS9RecenteredCoupledLaws L (a + shifts j) q).map
          (Probability.stoppedHistorySample Δ n) := by
  filter_upwards [sbxS9_countable_recenteredCoupledLaws_eq_of_product_ae_eq
    Q hQ shifts K L h] with a ha
  constructor
  · filter_upwards [ha.1] with ω hω
    exact fun j n => congrArg
      (fun μ : Measure (CoupledSample d) => μ.map (Probability.stoppedHistorySample Δ n))
      (hω j)
  · filter_upwards [ha.2] with q hq
    exact fun j n => congrArg
      (fun μ : Measure (CoupledSample d) => μ.map (Probability.stoppedHistorySample Δ n))
      (hq j)

/-- Joint environment and finite-record comparisons are consistent with the
cocycle for every member of the chosen countable family on one spatial set. -/
theorem sbxS9_countable_annealed_joint_records_eq_of_product_ae_eq
    {d : ℕ} (hd : 2 ≤ d) {ι : Type*} [Countable ι]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (shifts : ι → Vec d) (lam l : ℝ) (K L : CoupledQuenchedLaws d)
    (h : ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, K q = L q) :
    ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ j,
      let K' := sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) (shifts j)
      let L' := sbxS9RecenteredCoupledLaws L (a + shifts j)
      annealedCoupledLaw Q K' = annealedCoupledLaw Q L' ∧
      ∀ (n : ℕ) (ks : Fin n → ℕ),
        (annealedCoupledLaw Q K').map
            (fun ωz => (ωz.1, fun k => regenerationRecord hd lam l (ks k) ωz)) =
          (annealedCoupledLaw Q L').map
            (fun ωz => (ωz.1, fun k => regenerationRecord hd lam l (ks k) ωz)) := by
  filter_upwards [sbxS9_countable_recenteredCoupledLaws_eq_of_product_ae_eq
    Q hQ shifts K L h] with a ha j
  have heq := ha.1.mono (fun _ hω => hω j)
  exact ⟨sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq Q _ _ heq,
    fun n ks => sbxS9_annealed_joint_records_law_eq_of_origin_ae_eq
      hd Q lam l _ _ heq n ks⟩

/-- On a common spatial set, the two-stage and sum-shift versions have
probability witnesses and identical conditioned joint records. A genuine
nonzero no-return witness is transported, never manufactured. -/
theorem sbxS9_countable_conditioned_joint_records_eq_of_product_ae_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} {ι : Type*} [Countable ι]
    (Q : EnvironmentLaw d Λ₀ r₀) (shifts : ι → Vec d) (lam l : ℝ)
    (K L : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q.measure K)
    (h : ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q.measure, K q = L q) :
    ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ j,
      let K' := sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) (shifts j)
      let L' := sbxS9RecenteredCoupledLaws L (a + shifts j)
      ∃ (hK' : HasProbabilityLaws Q.measure K') (hL' : HasProbabilityLaws Q.measure L'),
        ∀ hD : annealedCoupledLaw Q.measure K' (regenerationNoReturn hd (l / lam)) ≠ 0,
        ∃ hD' : annealedCoupledLaw Q.measure L' (regenerationNoReturn hd (l / lam)) ≠ 0,
          regenerationConditionedLaw hd Q lam l K' hK' hD =
            regenerationConditionedLaw hd Q lam l L' hL' hD' ∧
          ∀ (n : ℕ) (ks : Fin n → ℕ),
            (regenerationConditionedLaw hd Q lam l K' hK' hD).map
                (fun ωz => (ωz.1, fun k => regenerationRecord hd lam l (ks k) ωz)) =
              (regenerationConditionedLaw hd Q lam l L' hL' hD').map
                (fun ωz => (ωz.1, fun k => regenerationRecord hd lam l (ks k) ωz)) := by
  filter_upwards [sbxS9_countable_recenteredCoupledLaws_eq_of_product_ae_eq
    Q.measure Q.stationary shifts K L h,
    sbxS9_countable_hasProbabilityLaws_recenter Q.measure Q.stationary shifts K hK]
    with a ha hprob j
  let K' := sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) (shifts j)
  let L' := sbxS9RecenteredCoupledLaws L (a + shifts j)
  have heq : (∀ᵐ ω ∂Q.measure, K' (0, ω) = L' (0, ω)) ∧
      ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q.measure, K' q = L' q :=
    ⟨ha.1.mono (fun _ hω => hω j), ha.2.mono (fun _ hq => hq j)⟩
  have hK' : HasProbabilityLaws Q.measure K' := hprob j
  have hL' := sbxS9_hasProbabilityLaws_of_origin_product_ae_eq Q.measure K' L' hK' heq
  refine ⟨hK', hL', ?_⟩
  intro hD
  have hD' := sbxS9_noReturn_ne_zero_of_origin_ae_eq
    hd Q.measure K' L' (l / lam) heq.1 hD
  exact ⟨hD', sbxS9_regenerationConditionedLaw_eq_of_origin_ae_eq
    hd Q lam l K' L' hK' hL' hD hD' heq.1,
    fun n ks => sbxS9_conditioned_joint_records_law_eq_of_origin_ae_eq
      hd Q lam l K' L' hK' hL' hD hD' heq.1 n ks⟩

/-- The measurable input equivalence uses the literal recentering formula. -/
@[simp] theorem sbxS9RecenterInputEquiv_apply {d : ℕ} (a : Vec d)
    (p : Vec d × FieldPair d) :
    sbxS9RecenterInputEquiv a p = sbxS9RecenterInput a p := rfl

/-- Every two fixed shifts preserve spatial-product path-law version equality.
The origin comparison is supplied separately by the countable common-set result. -/
theorem sbxS9_recenteredPathLaws_add_eq_of_product_ae_eq {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (P P' : QuenchedPathLaws d)
    (h : ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, P q = P' q) (a b : Vec d) :
    ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q,
      sbxS9RecenteredPathLaws (sbxS9RecenteredPathLaws P a) b q =
        sbxS9RecenteredPathLaws P' (a + b) q := by
  filter_upwards [sbxS9_ae_recenterInput_add Q hQ h a b] with q hq
  rw [sbxS9_recenterInput_add] at hq
  rw [sbxS9_recenteredPathLaws_add, sbxS9RecenteredPathLaws_apply,
    sbxS9RecenteredPathLaws_apply, hq]

/-- Every two fixed shifts also preserve the full spatial-product coupled law. -/
theorem sbxS9_recenteredCoupledLaws_add_eq_of_product_ae_eq {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (K L : CoupledQuenchedLaws d)
    (h : ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q, K q = L q) (a b : Vec d) :
    ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q,
      sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) b q =
        sbxS9RecenteredCoupledLaws L (a + b) q := by
  filter_upwards [sbxS9_ae_recenterInput_add Q hQ h a b] with q hq
  rw [sbxS9_recenterInput_add] at hq
  rw [sbxS9_recenteredCoupledLaws_add, sbxS9RecenteredCoupledLaws_apply,
    sbxS9RecenteredCoupledLaws_apply, hq]

/-- Conditional same-node comparison on one countable common spatial set.
The path-law covariance remains an explicit antecedent for each shift; the
cocycle identifies the corresponding two-stage coupled law exactly. -/
theorem sbxS9_countable_recentered_coupling_laws_eq_of_path_laws_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} {ι : Type*} [Countable ι]
    (Q : EnvironmentLaw d Λ₀ r₀) (shifts : ι → Vec d)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ j,
      ((∀ᵐ ω ∂Q.measure, P (0, ω) =
          sbxS9RecenteredPathLaws (sbxS9RecenteredPathLaws P a) (shifts j) (0, ω)) ∧
        ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q.measure, P q =
          sbxS9RecenteredPathLaws (sbxS9RecenteredPathLaws P a) (shifts j) q) →
      (∀ᵐ ω ∂Q.measure, K (0, ω) =
          sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) (shifts j) (0, ω)) ∧
        ∀ᵐ q ∂(volume : Measure (Vec d)).prod Q.measure, K q =
          sbxS9RecenteredCoupledLaws (sbxS9RecenteredCoupledLaws K a) (shifts j) q := by
  have hs := fun j =>
    (measurePreserving_add_right (volume : Measure (Vec d)) (shifts j)).quasiMeasurePreserving.ae
      (sbxS9_recentered_coupling_laws_eq_of_path_laws_eq hd Q lam h0 h1 l δ hl P K hK)
  filter_upwards [ae_all_iff.mpr hs] with a ha j
  rw [sbxS9_recenteredPathLaws_add, sbxS9_recenteredCoupledLaws_add]
  exact ha j

/-- The actual input change is measurable jointly in the shift and input. -/
theorem sbxS9_measurable_joint_recenterInput {d : ℕ} :
    Measurable (fun q : Vec d × (Vec d × FieldPair d) =>
      sbxS9RecenterInput q.1 q.2) :=
  (measurable_fst.add measurable_snd.fst).prodMk
    (Probability.continuous_translate.measurable.comp
      (measurable_fst.neg.prodMk measurable_snd.snd))

/-- The entire continuous output path varies measurably with the shift. -/
theorem sbxS9_measurable_joint_recenterPath {d : ℕ} :
    Measurable (fun q : Vec d × Path d => recenterPathEquiv q.1 q.2) :=
  Probability.continuous_path_recenter.measurable

/-- Joint sample recentering retains the whole path and all coin coordinates. -/
theorem sbxS9_measurable_joint_recenterSample {d : ℕ} :
    Measurable (fun q : Vec d × CoupledSample d => recenterSampleEquiv q.1 q.2) :=
  measurable_recenterSample

/-- A jointly measurable output map gives a measurable family of pushforwards
of an s-finite supplied kernel. No covariance property is used. -/
theorem sbxS9_measurable_parameter_map {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel α β) [IsSFiniteKernel κ] (f : α × β → γ) (hf : Measurable f) :
    Measurable (fun a => (κ a).map (fun b => f (a, b))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm := Kernel.measurable_kernel_prodMk_left (κ := κ) (hs.preimage hf)
  convert hm using 1
  funext a
  exact Measure.map_apply (hf.comp measurable_prodMk_left) hs

/-- Joint measurability of the literal recentered path measures. S-finiteness
is a property of this supplied kernel, not an additional source premise. -/
theorem sbxS9_measurable_joint_recenteredPathLaws {d : ℕ}
    (P : QuenchedPathLaws d) [IsSFiniteKernel P] :
    Measurable (fun q : Vec d × (Vec d × FieldPair d) =>
      sbxS9RecenteredPathLaws P q.1 q.2) := by
  have hm := sbxS9_measurable_parameter_map
    (P.comap _ sbxS9_measurable_joint_recenterInput)
    (fun z => recenterPathEquiv z.1.1 z.2)
    (sbxS9_measurable_joint_recenterPath.comp (measurable_fst.fst.prodMk measurable_snd))
  simpa only [sbxS9RecenteredPathLaws_apply, Kernel.comap_apply] using hm

/-- Joint measurability of the supplied coupled-law recentering, including
all Bernoulli coordinates. -/
theorem sbxS9_measurable_joint_recenteredCoupledLaws {d : ℕ}
    (K : CoupledQuenchedLaws d) [IsSFiniteKernel K] :
    Measurable (fun q : Vec d × (Vec d × FieldPair d) =>
      sbxS9RecenteredCoupledLaws K q.1 q.2) := by
  have hm := sbxS9_measurable_parameter_map
    (K.comap _ sbxS9_measurable_joint_recenterInput)
    (fun z => recenterSampleEquiv z.1.1 z.2)
    (sbxS9_measurable_joint_recenterSample.comp (measurable_fst.fst.prodMk measurable_snd))
  simpa only [sbxS9RecenteredCoupledLaws_apply, Kernel.comap_apply] using hm

/-- Simultaneously measurable bounded observations of the recentered path
law; Bochner integration also permits nonintegrable measurable tests. -/
theorem sbxS9_measurable_joint_recenteredPathLaws_integral {d : ℕ}
    (P : QuenchedPathLaws d) [IsSFiniteKernel P]
    (F : Path d → ℝ) (hF : Measurable F) :
    Measurable (fun q : Vec d × (Vec d × FieldPair d) =>
      ∫ γ, F γ ∂sbxS9RecenteredPathLaws P q.1 q.2) := by
  let κ := P.comap _ sbxS9_measurable_joint_recenterInput
  have hf : Measurable (fun z : (Vec d × (Vec d × FieldPair d)) × Path d =>
      F (recenterPathEquiv z.1.1 z.2)) := hF.comp
    (sbxS9_measurable_joint_recenterPath.comp (measurable_fst.fst.prodMk measurable_snd))
  have hm := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  convert hm.measurable using 1
  funext q
  rw [sbxS9RecenteredPathLaws_apply]
  exact integral_map (recenterPathEquiv q.1).measurable.aemeasurable hF.aestronglyMeasurable

/-- The corresponding joint integral measurability keeps the complete sample. -/
theorem sbxS9_measurable_joint_recenteredCoupledLaws_integral {d : ℕ}
    (K : CoupledQuenchedLaws d) [IsSFiniteKernel K]
    (F : CoupledSample d → ℝ) (hF : Measurable F) :
    Measurable (fun q : Vec d × (Vec d × FieldPair d) =>
      ∫ z, F z ∂sbxS9RecenteredCoupledLaws K q.1 q.2) := by
  let κ := K.comap _ sbxS9_measurable_joint_recenterInput
  have hf : Measurable (fun z : (Vec d × (Vec d × FieldPair d)) × CoupledSample d =>
      F (recenterSampleEquiv z.1.1 z.2)) := hF.comp
    (sbxS9_measurable_joint_recenterSample.comp (measurable_fst.fst.prodMk measurable_snd))
  have hm := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  convert hm.measurable using 1
  funext q
  rw [sbxS9RecenteredCoupledLaws_apply]
  exact integral_map (recenterSampleEquiv q.1).measurable.aemeasurable hF.aestronglyMeasurable

/-- Stationarity proves preservation of the joint endpoint/environment
reference law even when the shift is the endpoint itself. -/
theorem sbxS9_measurePreserving_endpoint_recenterEnvironment {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q) :
    MeasurePreserving (fun p : Vec d × FieldPair d => (p.1, translate p.1 p.2))
      ((volume : Measure (Vec d)).prod Q) ((volume : Measure (Vec d)).prod Q) :=
  (MeasurePreserving.id (volume : Measure (Vec d))).skew_product
    Probability.continuous_translate.measurable (Filter.Eventually.of_forall hQ)

/-- Quenched endpoint absolute continuity yields absolute continuity of the
joint endpoint/environment law. The environmental marginal is retained. -/
theorem sbxS9_joint_endpoint_law_ac {d : ℕ} {α : Type*} [MeasurableSpace α]
    (Q : Measure (FieldPair d)) [SFinite Q]
    (κ : Kernel (FieldPair d) α) [IsSFiniteKernel κ]
    (e : α → Vec d) (he : Measurable e)
    (hdensity : ∀ᵐ ω ∂Q, (κ ω).map e ≪ (volume : Measure (Vec d))) :
    (Q.compProd κ).map (fun z => (e z.2, z.1)) ≪
      (volume : Measure (Vec d)).prod Q := by
  have hac : Q.compProd (κ.map e) ≪ Q.prod (volume : Measure (Vec d)) := by
    rw [← Measure.compProd_const]
    apply Measure.AbsolutelyContinuous.compProd_right
    simpa only [Kernel.map_apply _ he, Kernel.const_apply] using hdensity
  have hm := hac.map measurable_swap
  rw [Measure.prod_swap, Measure.compProd_map he,
    Measure.map_map measurable_swap (measurable_id.prodMap he)] at hm
  exact hm

/-- The stationary recentering of an absolutely continuous joint endpoint
law remains absolutely continuous with respect to the same joint reference. -/
theorem sbxS9_joint_recentered_endpoint_law_ac {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (μ : Measure (Vec d × FieldPair d))
    (hμ : μ ≪ (volume : Measure (Vec d)).prod Q) :
    μ.map (fun p => (p.1, translate p.1 p.2)) ≪
      (volume : Measure (Vec d)).prod Q := by
  have hm := sbxS9_measurePreserving_endpoint_recenterEnvironment Q hQ
  simpa only [hm.map_eq] using hμ.map hm.measurable

/-- Projection from a measure--kernel product preserves every environmental
a.e. assertion, including predicates whose measurability is not supplied. -/
theorem sbxS9_quasiMeasurePreserving_compProd_fst {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    Measure.QuasiMeasurePreserving Prod.fst (μ.compProd κ) μ := by
  refine ⟨measurable_fst, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply measurable_fst hs,
    Measure.compProd_apply (hs.preimage measurable_fst)]
  calc
    _ = ∫⁻ _a, (0 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr_ae
      have hnot : ∀ᵐ a ∂μ, a ∉ s := ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hs0)
      filter_upwards [hnot] with a ha
      have hempty : Prod.mk a ⁻¹' (Prod.fst ⁻¹' s) = (∅ : Set β) := by
        ext b
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        exact ha
      rw [hempty, measure_empty]
    _ = 0 := lintegral_zero

/-- The origin start support transfers from genuine quenched fibres to the
actual annealed law, with its probability-part normalization. -/
theorem sbxS9_annealed_start_at_zero {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hstart : ∀ᵐ ω ∂Q, ∀ᵐ z ∂K (0, ω), z.1 0 = 0) :
    ∀ᵐ z ∂annealedCoupledLaw Q K, z.2.1 0 = 0 := by
  apply Measure.ae_compProd_of_ae_ae
  · exact measurableSet_eq_fun
      ((measurable_pathPosition 0).comp measurable_snd.fst) measurable_const
  · filter_upwards [hprob, hstart] with ω hp hs
    let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
    exact hs

/-- Positive-time quenched endpoint densities supply the required joint
absolute continuity for the actual annealed coupling, without a global
s-finiteness assumption on the raw supplied kernel. -/
theorem sbxS9_annealed_joint_endpoint_law_ac {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (K : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (t : ℝ≥0)
    (hdensity : ∀ᵐ ω ∂Q,
      (K (0, ω)).map (fun z : CoupledSample d => z.1 t) ≪
        (volume : Measure (Vec d))) :
    (annealedCoupledLaw Q K).map (fun z => (z.2.1 t, z.1)) ≪
      (volume : Measure (Vec d)).prod Q := by
  apply sbxS9_joint_endpoint_law_ac Q (Probability.probabilityPart (originCoupledLaw K))
    (fun z => z.1 t) ((measurable_pathPosition t).comp measurable_fst)
  filter_upwards [hprob, hdensity] with ω hp hω
  let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
  exact hω

/-- A product-a.e. equality of actual coupled kernels can be evaluated at a
random endpoint only after proving absolute continuity of its joint law. -/
theorem sbxS9_ae_kernel_eq_at_joint_endpoint {d : ℕ} {α : Type*}
    [MeasurableSpace α] (Q : Measure (FieldPair d))
    (μ : Measure α) (e : α → Vec d × FieldPair d) (he : AEMeasurable e μ)
    (hac : μ.map e ≪ (volume : Measure (Vec d)).prod Q)
    (K L : CoupledQuenchedLaws d)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    ∀ᵐ z ∂μ, K (e z) = L (e z) :=
  ae_of_ae_map he (hac.ae_le hKL)

/-- Random recentering of the environment also transports product versions
because stationarity preserves the whole joint reference measure. -/
theorem sbxS9_ae_kernel_eq_at_recentered_joint_endpoint {d : ℕ} {α : Type*}
    [MeasurableSpace α] (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (μ : Measure α) (e : α → Vec d × FieldPair d) (he : Measurable e)
    (hac : μ.map e ≪ (volume : Measure (Vec d)).prod Q)
    (K L : CoupledQuenchedLaws d)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    ∀ᵐ z ∂μ, K ((e z).1, translate (e z).1 (e z).2) =
      L ((e z).1, translate (e z).1 (e z).2) := by
  have hm := sbxS9_measurePreserving_endpoint_recenterEnvironment Q hQ
  have ha := sbxS9_joint_recentered_endpoint_law_ac Q hQ (μ.map e) hac
  rw [Measure.map_map hm.measurable he] at ha
  exact sbxS9_ae_kernel_eq_at_joint_endpoint Q μ _ (hm.measurable.comp he).aemeasurable ha K L hKL

/-- One common annealed good set works for all grid times. Time zero uses
origin equality and start support; only positive times use endpoint density. -/
theorem sbxS9_annealed_ae_all_restart_fibres_eq {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (Δ : ℝ≥0)
    (K L : CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω)))
    (hstart : ∀ᵐ ω ∂Q, ∀ᵐ z ∂K (0, ω), z.1 0 = 0)
    (hdensity : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂Q,
      (K (0, ω)).map (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) ≪
        (volume : Measure (Vec d)))
    (hzero : ∀ᵐ ω ∂Q, K (0, ω) = L (0, ω))
    (hsp : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    ∀ᵐ z ∂annealedCoupledLaw Q K, ∀ n : ℕ,
      K (z.2.1 ((n : ℝ≥0) * Δ), z.1) =
        L (z.2.1 ((n : ℝ≥0) * Δ), z.1) := by
  apply ae_all_iff.mpr
  intro n
  by_cases hn : n = 0
  · have hz := (sbxS9_quasiMeasurePreserving_compProd_fst Q
        (Probability.probabilityPart (originCoupledLaw K))).ae hzero
    filter_upwards [sbxS9_annealed_start_at_zero Q K hprob hstart, hz] with z hs heq
    simpa only [hn, Nat.cast_zero, zero_mul, hs] using heq
  · exact sbxS9_ae_kernel_eq_at_joint_endpoint Q (annealedCoupledLaw Q K)
      (fun z => (z.2.1 ((n : ℝ≥0) * Δ), z.1))
      (((measurable_pathPosition _).comp measurable_snd.fst).prodMk measurable_fst).aemeasurable
      (sbxS9_annealed_joint_endpoint_law_ac Q K hprob _ (hdensity n (by omega))) K L hsp

/-- Nested bounded-test comparisons hold under any outer law absolutely
continuous with respect to the actual annealed law, including conditioning. -/
theorem sbxS9_nested_integral_eq_of_annealed_restart_fibres {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (K L : CoupledQuenchedLaws d)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ≪ annealedCoupledLaw Q K)
    (h : ∀ᵐ z ∂annealedCoupledLaw Q K, ∀ n : ℕ,
      K (z.2.1 ((n : ℝ≥0) * Δ), z.1) = L (z.2.1 ((n : ℝ≥0) * Δ), z.1))
    (n : ℕ) (H : FieldPair d × CoupledSample d → ℝ)
    (F : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ) :
    (∫ z, H z * (∫ z', F (z, z') ∂K (z.2.1 ((n : ℝ≥0) * Δ), z.1)) ∂μ) =
      ∫ z, H z * (∫ z', F (z, z') ∂L (z.2.1 ((n : ℝ≥0) * Δ), z.1)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [hμ.ae_le h] with z hz
  rw [hz n]

/-- The common restart good set survives the literal no-return conditioning. -/
theorem sbxS9_conditioned_ae_all_restart_fibres_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ) (Δ : ℝ≥0)
    (K L : CoupledQuenchedLaws d) (hprob : HasProbabilityLaws Q.measure K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (h : ∀ᵐ z ∂annealedCoupledLaw Q.measure K, ∀ n : ℕ,
      K (z.2.1 ((n : ℝ≥0) * Δ), z.1) = L (z.2.1 ((n : ℝ≥0) * Δ), z.1)) :
    ∀ᵐ z ∂regenerationConditionedLaw hd Q lam l K hprob hD, ∀ n : ℕ,
      K (z.2.1 ((n : ℝ≥0) * Δ), z.1) = L (z.2.1 ((n : ℝ≥0) * Δ), z.1) :=
  ProbabilityTheory.cond_absolutelyContinuous.ae_le h

/-- Conditioned nested integrals retain the actual environment, path and coins. -/
theorem sbxS9_conditioned_nested_integral_eq_of_restart_fibres {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ) (Δ : ℝ≥0)
    (K L : CoupledQuenchedLaws d) (hprob : HasProbabilityLaws Q.measure K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (h : ∀ᵐ z ∂annealedCoupledLaw Q.measure K, ∀ n : ℕ,
      K (z.2.1 ((n : ℝ≥0) * Δ), z.1) = L (z.2.1 ((n : ℝ≥0) * Δ), z.1))
    (n : ℕ) (H : FieldPair d × CoupledSample d → ℝ)
    (F : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ) :
    (∫ z, H z * (∫ z', F (z, z') ∂K (z.2.1 ((n : ℝ≥0) * Δ), z.1))
      ∂regenerationConditionedLaw hd Q lam l K hprob hD) =
      ∫ z, H z * (∫ z', F (z, z') ∂L (z.2.1 ((n : ℝ≥0) * Δ), z.1))
        ∂regenerationConditionedLaw hd Q lam l K hprob hD :=
  sbxS9_nested_integral_eq_of_annealed_restart_fibres Q.measure Δ K L
    (regenerationConditionedLaw hd Q lam l K hprob hD)
    ProbabilityTheory.cond_absolutelyContinuous h n H F

/-- The source recentering sends the old endpoint to the new origin with
exactly the translated physical environment. -/
theorem sbxS9_recenterInput_endpoint_origin {d : ℕ} (p : Vec d × FieldPair d) :
    sbxS9RecenterInput p.1 (0, translate p.1 p.2) = p := by
  simp only [sbxS9RecenterInput, add_zero, translate_add, neg_add_cancel, translate_zero,
    Prod.mk.eta]

/-- The output measure at this recentered origin is the literal pushforward
of the old endpoint fibre, without any path-law covariance assumption. -/
theorem sbxS9_recenteredCoupledLaws_endpoint_origin {d : ℕ}
    (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d) :
    sbxS9RecenteredCoupledLaws K p.1 (0, translate p.1 p.2) =
      (K p).map (recenterSampleEquiv p.1) := by
  rw [sbxS9RecenteredCoupledLaws_apply, sbxS9_recenterInput_endpoint_origin]

/-- The same exact input cancellation holds for the actual path measures. -/
theorem sbxS9_recenteredPathLaws_endpoint_origin {d : ℕ}
    (P : QuenchedPathLaws d) (p : Vec d × FieldPair d) :
    sbxS9RecenteredPathLaws P p.1 (0, translate p.1 p.2) =
      (P p).map (recenterPathEquiv p.1) := by
  rw [sbxS9RecenteredPathLaws_apply, sbxS9_recenterInput_endpoint_origin]

/-- Finite-dimensional observations commute with recentering while the
entire Bernoulli sequence, rather than a finite truncation, is retained. -/
theorem sbxS9_recenteredCoupledLaws_finite_observations {d n : ℕ}
    (K : CoupledQuenchedLaws d) (a : Vec d) (p : Vec d × FieldPair d)
    (times : Fin n → ℝ≥0) :
    (sbxS9RecenteredCoupledLaws K a p).map
        (fun z : CoupledSample d => ((fun j => z.1 (times j)), z.2)) =
      (K (sbxS9RecenterInput a p)).map
        (fun z : CoupledSample d => ((fun j => z.1 (times j) - a), z.2)) := by
  have hm : Measurable (fun z : CoupledSample d => ((fun j => z.1 (times j)), z.2)) :=
    (measurable_pi_iff.mpr (fun j =>
      (measurable_pathPosition (times j)).comp measurable_fst)).prodMk measurable_snd
  rw [sbxS9RecenteredCoupledLaws_apply,
    Measure.map_map hm (recenterSampleEquiv a).measurable]
  rfl

/-- Probability-part normalization gives a jointly measurable recentering
for every raw supplied path kernel, including exceptional infinite fibres. -/
theorem sbxS9_measurable_joint_probabilityPart_recenteredPathLaws {d : ℕ}
    (P : QuenchedPathLaws d) :
    Measurable (fun q : Vec d × (Vec d × FieldPair d) =>
      sbxS9RecenteredPathLaws (Probability.probabilityPart P) q.1 q.2) :=
  sbxS9_measurable_joint_recenteredPathLaws (Probability.probabilityPart P)

/-- The analogous normalized coupled family remains jointly measurable
without imposing global s-finiteness on the source coupling. -/
theorem sbxS9_measurable_joint_probabilityPart_recenteredCoupledLaws {d : ℕ}
    (K : CoupledQuenchedLaws d) :
    Measurable (fun q : Vec d × (Vec d × FieldPair d) =>
      sbxS9RecenteredCoupledLaws (Probability.probabilityPart K) q.1 q.2) :=
  sbxS9_measurable_joint_recenteredCoupledLaws (Probability.probabilityPart K)

/-- At each actual probability fibre the normalized jointly measurable
family equals the raw recentered law exactly. -/
theorem sbxS9_probabilityPart_recenteredCoupledLaws_eq {d : ℕ}
    (K : CoupledQuenchedLaws d) (a : Vec d) (p : Vec d × FieldPair d)
    (hp : IsProbabilityMeasure (K (sbxS9RecenterInput a p))) :
    sbxS9RecenteredCoupledLaws (Probability.probabilityPart K) a p =
      sbxS9RecenteredCoupledLaws K a p := by
  let : IsProbabilityMeasure (K (sbxS9RecenterInput a p)) := hp
  rw [sbxS9RecenteredCoupledLaws_apply, sbxS9RecenteredCoupledLaws_apply,
    Probability.probabilityPart_eq_of_isProbabilityMeasure]

/-- One common set transports all restart versions to their legitimate
random recentered origins, retaining the exact signs in both coordinate maps. -/
theorem sbxS9_ae_all_recentered_origin_restart_fibres_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (K L : CoupledQuenchedLaws d)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ≪ annealedCoupledLaw Q K)
    (h : ∀ᵐ z ∂annealedCoupledLaw Q K, ∀ n : ℕ,
      K (z.2.1 ((n : ℝ≥0) * Δ), z.1) = L (z.2.1 ((n : ℝ≥0) * Δ), z.1)) :
    ∀ᵐ z ∂μ, ∀ n : ℕ,
      sbxS9RecenteredCoupledLaws K (z.2.1 ((n : ℝ≥0) * Δ))
          (0, translate (z.2.1 ((n : ℝ≥0) * Δ)) z.1) =
        sbxS9RecenteredCoupledLaws L (z.2.1 ((n : ℝ≥0) * Δ))
          (0, translate (z.2.1 ((n : ℝ≥0) * Δ)) z.1) := by
  filter_upwards [hμ.ae_le h] with z hz n
  rw [sbxS9_recenteredCoupledLaws_endpoint_origin K
      (z.2.1 ((n : ℝ≥0) * Δ), z.1),
    sbxS9_recenteredCoupledLaws_endpoint_origin L
      (z.2.1 ((n : ℝ≥0) * Δ), z.1), hz n]

/-- The real GMP coupling supplies both starts and positive grid-time
densities for the annealed common version set. This is a consistency helper,
not an independence reduction or a construction of path-law covariance. -/
theorem sbxS9_annealed_ae_all_restart_fibres_eq_of_coupling {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (h : (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p) :
    ∀ᵐ z ∂annealedCoupledLaw Q.measure K, ∀ n : ℕ,
      K (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam), z.1) =
        L (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam), z.1) := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have hg := ae_coupledEnvironmentRegular hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  apply sbxS9_annealed_ae_all_restart_fibres_eq Q.measure
    (Renewal.regenDelta lam) K L hK.1.1 _ _ h.1 h.2
  · filter_upwards [hg] with ω hω
    refine ae_of_ae_map (p := fun γ : Path d => γ 0 = 0)
      measurable_fst.aemeasurable ?_
    rw [hω.2.1.2.1]
    obtain ⟨_, r, hr⟩ := hω.1
    rw [hr 0]
    exact r.pathLaw_starts_at 0
  · intro n hn
    filter_upwards [hg] with ω hω
    exact coupled_endpoint_density_of_path_marginal P K (0, ω) hω.2.1.2.1 _
      (hω.2.2.2 n hn 0)

/-- Finite joint records of the recentered restart sample have a measurable
family of laws. Normalization leaves all genuine probability fibres intact. -/
theorem sbxS9_measurable_recentered_restart_record_laws {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (K : CoupledQuenchedLaws d) (n : ℕ) (ks : Fin n → ℕ)
    (t : ℝ≥0) :
    Measurable (fun z : FieldPair d × CoupledSample d =>
      ((Probability.probabilityPart K) (z.2.1 t, z.1)).map
        (fun z' => (translate (z.2.1 t) z.1, fun j => regenerationRecord hd lam l (ks j)
          (translate (z.2.1 t) z.1, recenterSample (z.2.1 t) z')))) := by
  have he : Measurable (fun z : FieldPair d × CoupledSample d => (z.2.1 t, z.1)) :=
    ((measurable_pathPosition t).comp measurable_snd.fst).prodMk measurable_fst
  have henv : Measurable
      (fun z : (FieldPair d × CoupledSample d) × CoupledSample d =>
        translate (z.1.2.1 t) z.1.1) :=
    Probability.continuous_translate.measurable.comp (he.comp measurable_fst)
  have hsample : Measurable
      (fun z : (FieldPair d × CoupledSample d) × CoupledSample d =>
        recenterSample (z.1.2.1 t) z.2) :=
    measurable_recenterSample.comp ((he.comp measurable_fst).fst.prodMk measurable_snd)
  exact sbxS9_measurable_parameter_map ((Probability.probabilityPart K).comap _ he) _
    (henv.prodMk (measurable_pi_iff.mpr (fun j =>
      (measurable_cycleRecord hd lam l (ks j)).comp (henv.prodMk hsample))))

/-- Recentered finite-record mixtures, including their physical environments,
are unchanged by legitimate restart versions under any dominated outer law. -/
theorem sbxS9_recentered_restart_record_mixture_eq {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) (lam l : ℝ) (Δ : ℝ≥0)
    (K L : CoupledQuenchedLaws d) (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ≪ annealedCoupledLaw Q K)
    (h : ∀ᵐ z ∂annealedCoupledLaw Q K, ∀ m : ℕ,
      K (z.2.1 ((m : ℝ≥0) * Δ), z.1) = L (z.2.1 ((m : ℝ≥0) * Δ), z.1))
    (m n : ℕ) (ks : Fin n → ℕ) :
    μ.bind (fun z => ((Probability.probabilityPart K) (z.2.1 ((m : ℝ≥0) * Δ), z.1)).map
      (fun z' => (translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
        fun j => regenerationRecord hd lam l (ks j)
          (translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
            recenterSample (z.2.1 ((m : ℝ≥0) * Δ)) z')))) =
    μ.bind (fun z => ((Probability.probabilityPart L) (z.2.1 ((m : ℝ≥0) * Δ), z.1)).map
      (fun z' => (translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
        fun j => regenerationRecord hd lam l (ks j)
          (translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
            recenterSample (z.2.1 ((m : ℝ≥0) * Δ)) z')))) := by
  apply Measure.bind_congr_right
  filter_upwards [hμ.ae_le h] with z hz
  simp only [Probability.probabilityPart_apply, hz m]

/-- The concrete conditioned finite-record mixture uses the literal frozen
conditioned law; its joint measurability is supplied by the preceding helper. -/
theorem sbxS9_conditioned_recentered_restart_record_mixture_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ) (Δ : ℝ≥0)
    (K L : CoupledQuenchedLaws d) (hprob : HasProbabilityLaws Q.measure K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (h : ∀ᵐ z ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      K (z.2.1 ((m : ℝ≥0) * Δ), z.1) = L (z.2.1 ((m : ℝ≥0) * Δ), z.1))
    (m n : ℕ) (ks : Fin n → ℕ) :
    (regenerationConditionedLaw hd Q lam l K hprob hD).bind (fun z =>
      ((Probability.probabilityPart K) (z.2.1 ((m : ℝ≥0) * Δ), z.1)).map
      (fun z' => (translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
        fun j => regenerationRecord hd lam l (ks j)
          (translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
            recenterSample (z.2.1 ((m : ℝ≥0) * Δ)) z')))) =
    (regenerationConditionedLaw hd Q lam l K hprob hD).bind (fun z =>
      ((Probability.probabilityPart L) (z.2.1 ((m : ℝ≥0) * Δ), z.1)).map
      (fun z' => (translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
        fun j => regenerationRecord hd lam l (ks j)
          (translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
            recenterSample (z.2.1 ((m : ℝ≥0) * Δ)) z')))) :=
  sbxS9_recentered_restart_record_mixture_eq hd Q.measure lam l Δ K L
    (regenerationConditionedLaw hd Q lam l K hprob hD)
    ProbabilityTheory.cond_absolutelyContinuous h m n ks

/-- A countable measurable choice preserves branchwise a.e. equality under
its actual restricted branch measures. The exceptional sets may depend on the
index, but their countable union is null. -/
theorem sbxS9_ae_countable_select {α β ι : Type*} [MeasurableSpace α]
    [Countable ι] (μ : Measure α) (N : α → ι)
    (hN : ∀ i, MeasurableSet {z | N z = i}) (f g : ι → α → β)
    (h : ∀ i, f i =ᵐ[μ.restrict {z | N z = i}] g i) :
    (fun z => f (N z) z) =ᵐ[μ] (fun z => g (N z) z) := by
  have hall : ∀ᵐ z ∂μ, ∀ i, N z = i → f i z = g i z :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hN i)).mp (h i))
  filter_upwards [hall] with z hz
  exact hz (N z) rfl

/-- Countable selection is measurable when each branch and the index are
measurable; no continuity in the index is required. -/
theorem sbxS9_measurable_countable_select {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι]
    (N : α → ι) (hN : Measurable N) (f : ι → α → β)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun z => f (N z) z) := by
  have hm : Measurable (fun z : α × ι => f z.2 z.1) :=
    measurable_from_prod_countable_left (fun i => hf i)
  exact hm.comp (measurable_id.prodMk hN)

/-- Branchwise joint endpoint AC transports a countable family of genuine
coupled-kernel versions at a random index. The AC measures are restricted to
the selection events, rather than replacing the endpoint by a grid index. -/
theorem sbxS9_selected_kernel_eq_of_branch_joint_ac {d : ℕ} {α ι : Type*}
    [MeasurableSpace α] [Countable ι]
    (Q : Measure (FieldPair d)) (μ : Measure α) (N : α → ι)
    (hN : ∀ i, MeasurableSet {z | N z = i})
    (e : ι → α → Vec d × FieldPair d) (he : ∀ i, Measurable (e i))
    (K L : ι → CoupledQuenchedLaws d)
    (hac : ∀ i, (μ.restrict {z | N z = i}).map (e i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ i, ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K i p = L i p) :
    ∀ᵐ z ∂μ, K (N z) (e (N z) z) = L (N z) (e (N z) z) := by
  apply sbxS9_ae_countable_select μ N hN
    (fun i z => K i (e i z)) (fun i z => L i (e i z))
  intro i
  exact sbxS9_ae_kernel_eq_at_joint_endpoint Q _ (e i) (he i).aemeasurable
    (hac i) (K i) (L i) (hKL i)

/-- A singular zero branch uses its separately proved origin equality.
Only strictly positive branches consume joint endpoint AC. -/
theorem sbxS9_selected_kernel_eq_of_origin_and_branch_joint_ac {d : ℕ} {α : Type*}
    [MeasurableSpace α] (Q : Measure (FieldPair d)) (μ : Measure α)
    (N : α → ℕ) (hN : Measurable N)
    (e : ℕ → α → Vec d × FieldPair d) (he : ∀ n, Measurable (e n))
    (K L : ℕ → CoupledQuenchedLaws d)
    (hzero : ∀ᵐ z ∂μ.restrict {z | N z = 0}, K 0 (e 0 z) = L 0 (e 0 z))
    (hac : ∀ n, 1 ≤ n → (μ.restrict {z | N z = n}).map (e n) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ n, 1 ≤ n → ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q,
      K n p = L n p) :
    ∀ᵐ z ∂μ, K (N z) (e (N z) z) = L (N z) (e (N z) z) := by
  apply sbxS9_ae_countable_select μ N (fun n => measurableSet_eq_fun hN measurable_const)
    (fun n z => K n (e n z)) (fun n z => L n (e n z))
  intro n
  by_cases hn : n = 0
  · subst n
    exact hzero
  · exact sbxS9_ae_kernel_eq_at_joint_endpoint Q _ (e n) (he n).aemeasurable
      (hac n (by omega)) (K n) (L n) (hKL n (by omega))

/-- Every indexed kernel version has a legitimate common endpoint good set
under the actual annealed base law. Zero uses environmental origin equality. -/
theorem sbxS9_annealed_ae_all_indexed_restart_fibres_eq {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (Δ : ℝ≥0)
    (B : CoupledQuenchedLaws d) (K L : ℕ → CoupledQuenchedLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (B (0, ω)))
    (hstart : ∀ᵐ ω ∂Q, ∀ᵐ z ∂B (0, ω), z.1 0 = 0)
    (hdensity : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂Q,
      (B (0, ω)).map (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) ≪
        (volume : Measure (Vec d)))
    (hzero : ∀ᵐ ω ∂Q, K 0 (0, ω) = L 0 (0, ω))
    (hsp : ∀ n : ℕ, 1 ≤ n → ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q,
      K n p = L n p) :
    ∀ᵐ z ∂annealedCoupledLaw Q B, ∀ n : ℕ,
      K n (z.2.1 ((n : ℝ≥0) * Δ), z.1) =
        L n (z.2.1 ((n : ℝ≥0) * Δ), z.1) := by
  apply ae_all_iff.mpr
  intro n
  by_cases hn : n = 0
  · have hz := (sbxS9_quasiMeasurePreserving_compProd_fst Q
        (Probability.probabilityPart (originCoupledLaw B))).ae hzero
    filter_upwards [sbxS9_annealed_start_at_zero Q B hprob hstart, hz] with z hs heq
    simpa only [hn, Nat.cast_zero, zero_mul, hs] using heq
  · exact sbxS9_ae_kernel_eq_at_joint_endpoint Q (annealedCoupledLaw Q B)
      (fun z => (z.2.1 ((n : ℝ≥0) * Δ), z.1))
      (((measurable_pathPosition _).comp measurable_snd.fst).prodMk measurable_fst).aemeasurable
      (sbxS9_annealed_joint_endpoint_law_ac Q B hprob _ (hdensity n (by omega)))
      (K n) (L n) (hsp n (by omega))

/-- Selecting any countable grid index from the common good set is valid
under the annealed law and every absolutely continuous conditioning. -/
theorem sbxS9_selected_restart_fibres_eq {d : ℕ}
    (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (B : CoupledQuenchedLaws d)
    (K L : ℕ → CoupledQuenchedLaws d)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ≪ annealedCoupledLaw Q B)
    (h : ∀ᵐ z ∂annealedCoupledLaw Q B, ∀ n : ℕ,
      K n (z.2.1 ((n : ℝ≥0) * Δ), z.1) = L n (z.2.1 ((n : ℝ≥0) * Δ), z.1))
    (N : FieldPair d × CoupledSample d → ℕ) :
    ∀ᵐ z ∂μ, K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) =
      L (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) := by
  filter_upwards [hμ.ae_le h] with z hz
  exact hz (N z)

/-- The selected normalized restart law is measurable, retaining the
continuous endpoint in addition to the countable selection. -/
theorem sbxS9_measurable_selected_restart_law {d : ℕ} (Δ : ℝ≥0)
    (K : ℕ → CoupledQuenchedLaws d) (N : FieldPair d × CoupledSample d → ℕ)
    (hN : Measurable N) :
    Measurable (fun z : FieldPair d × CoupledSample d =>
      (Probability.probabilityPart (K (N z))) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)) := by
  apply sbxS9_measurable_countable_select N hN
    (fun n z => (Probability.probabilityPart (K n)) (z.2.1 ((n : ℝ≥0) * Δ), z.1))
  intro n
  exact (Probability.probabilityPart (K n)).measurable.comp
    (((measurable_pathPosition _).comp measurable_snd.fst).prodMk measurable_fst)

/-- A selected bounded nested test respects legitimate restart versions.
The equality also holds for total Bochner integrals without integrability
hypotheses; summing branches requires the integrability proved below. -/
theorem sbxS9_selected_nested_restart_integral_eq {d : ℕ} {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (N : α → ℕ)
    (e : ℕ → α → Vec d × FieldPair d) (K L : ℕ → CoupledQuenchedLaws d)
    (h : ∀ᵐ z ∂μ, K (N z) (e (N z) z) = L (N z) (e (N z) z))
    (H : α → ℝ) (F : α × CoupledSample d → ℝ) :
    (∫ z, H z * (∫ z', F (z, z') ∂K (N z) (e (N z) z)) ∂μ) =
      ∫ z, H z * (∫ z', F (z, z') ∂L (N z) (e (N z) z)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with z hz
  rw [hz]

/-- The selected mixture retains the entire outer sample, both fields and
all inner Bernoulli coordinates. Any measurable finite-record observation
can subsequently be pushed forward from this same full law. -/
theorem sbxS9_selected_joint_restart_law_eq {d : ℕ} {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (N : α → ℕ)
    (e : ℕ → α → Vec d × FieldPair d) (K L : ℕ → CoupledQuenchedLaws d)
    (h : ∀ᵐ z ∂μ, K (N z) (e (N z) z) = L (N z) (e (N z) z)) :
    μ.bind (fun z => ((Probability.probabilityPart (K (N z))) (e (N z) z)).map
      (fun z' => (z, z'))) =
    μ.bind (fun z => ((Probability.probabilityPart (L (N z))) (e (N z) z)).map
      (fun z' => (z, z'))) := by
  apply Measure.bind_congr_right
  filter_upwards [h] with z hz
  simp only [Probability.probabilityPart_apply, hz]

/-- The countably selected probability-part family is an actual measurable
kernel. Its zero fallback is retained on nongenuine probability fibres. -/
def sbxS9SelectedRestartKernel {d : ℕ} (Δ : ℝ≥0)
    (K : ℕ → CoupledQuenchedLaws d) (N : FieldPair d × CoupledSample d → ℕ)
    (hN : Measurable N) : Kernel (FieldPair d × CoupledSample d) (CoupledSample d) where
  toFun z := (Probability.probabilityPart (K (N z))) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)
  measurable' := sbxS9_measurable_selected_restart_law Δ K N hN

/-- The selected probability parts have a uniform mass bound of one. -/
theorem sbxS9_selected_restart_mass_le_one {d : ℕ} (Δ : ℝ≥0)
    (K : ℕ → CoupledQuenchedLaws d) (N : FieldPair d × CoupledSample d → ℕ)
    (hN : Measurable N) (z : FieldPair d × CoupledSample d) :
    sbxS9SelectedRestartKernel Δ K N hN z Set.univ ≤ 1 := by
  change (Probability.probabilityPart (K (N z))) _ Set.univ ≤ 1
  rw [Probability.probabilityPart_apply]
  split_ifs with hp
  · exact hp.le
  · exact bot_le

instance sbxS9SelectedRestartKernel_isFinite {d : ℕ} (Δ : ℝ≥0)
    (K : ℕ → CoupledQuenchedLaws d) (N : FieldPair d × CoupledSample d → ℕ)
    (hN : Measurable N) : IsFiniteKernel (sbxS9SelectedRestartKernel Δ K N hN) :=
  ⟨⟨1, ENNReal.one_lt_top, sbxS9_selected_restart_mass_le_one Δ K N hN⟩⟩

/-- Selected bounded nested observations are measurable in the full outer
sample, including all its Bernoulli coordinates. -/
theorem sbxS9_measurable_selected_nested_restart_test {d : ℕ} (Δ : ℝ≥0)
    (K : ℕ → CoupledQuenchedLaws d) (N : FieldPair d × CoupledSample d → ℕ)
    (hN : Measurable N) (H : FieldPair d × CoupledSample d → ℝ) (hH : Measurable H)
    (F : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ) (hF : Measurable F) :
    Measurable (fun z => H z * (∫ z', F (z, z') ∂sbxS9SelectedRestartKernel Δ K N hN z)) :=
  hH.mul (hF.stronglyMeasurable.integral_kernel_prod_right'
    (κ := sbxS9SelectedRestartKernel Δ K N hN)).measurable

/-- Bounded nested tests of the selected law are integrable under every
finite outer measure. The bound uses the proved mass bound, including the
zero fallback, so it does not require global probability fibres. -/
theorem sbxS9_integrable_selected_nested_restart_test {d : ℕ} (Δ : ℝ≥0)
    (K : ℕ → CoupledQuenchedLaws d) (N : FieldPair d × CoupledSample d → ℕ)
    (hN : Measurable N) (μ : Measure (FieldPair d × CoupledSample d)) [IsFiniteMeasure μ]
    (H : FieldPair d × CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (F : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ)
    (hF : Measurable F) (hbF : BoundedRealTest F) :
    Integrable (fun z => H z * (∫ z', F (z, z') ∂sbxS9SelectedRestartKernel Δ K N hN z)) μ := by
  obtain ⟨C, hC⟩ := hbH
  obtain ⟨D, hD⟩ := hbF
  apply Integrable.of_bound
    (sbxS9_measurable_selected_nested_restart_test Δ K N hN H hH F hF).aestronglyMeasurable
    (max C 0 * max D 0)
  apply Filter.Eventually.of_forall
  intro z
  have hmass : (sbxS9SelectedRestartKernel Δ K N hN z).real Set.univ ≤ 1 := by
    have ht := ENNReal.toReal_mono ENNReal.one_ne_top
      (sbxS9_selected_restart_mass_le_one Δ K N hN z)
    simpa only [measureReal_def, ENNReal.toReal_one] using ht
  have hint : ‖∫ z', F (z, z') ∂sbxS9SelectedRestartKernel Δ K N hN z‖ ≤ max D 0 := by
    calc
      _ ≤ max D 0 * (sbxS9SelectedRestartKernel Δ K N hN z).real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
          (fun z' => by simpa only [Real.norm_eq_abs] using (hD (z, z')).trans (le_max_left D 0)))
      _ ≤ max D 0 * 1 := mul_le_mul_of_nonneg_left hmass (le_max_right D 0)
      _ = max D 0 := mul_one _
  rw [norm_mul]
  exact mul_le_mul ((by simpa only [Real.norm_eq_abs] using (hC z).trans (le_max_left C 0)))
    hint (norm_nonneg _) (le_max_right C 0)

/-- Integrable selected tests have a countable branch sum, with
HasSum evidence. Every summand uses the original restricted branch measure. -/
theorem sbxS9_hasSum_integral_countable_select {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (N : α → ℕ) (hN : Measurable N) (f : ℕ → α → ℝ)
    (hf : Integrable (fun z => f (N z) z) μ) :
    HasSum (fun n => ∫ z in {z | N z = n}, f n z ∂μ)
      (∫ z, f (N z) z ∂μ) := by
  have hm : ∀ n, MeasurableSet {z | N z = n} :=
    fun _ => measurableSet_eq_fun hN measurable_const
  have hd : Pairwise (fun n m => Disjoint {z | N z = n} {z | N z = m}) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro z hn hm
    exact hnm (hn.symm.trans hm)
  have hcover : (⋃ n : ℕ, {z | N z = n}) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨N z, rfl⟩
  have hi : IntegrableOn (fun z => f (N z) z) (⋃ n : ℕ, {z | N z = n}) μ := by
    simpa only [hcover, IntegrableOn, Measure.restrict_univ] using hf
  have hs := hasSum_integral_iUnion hm hd hi
  have heq : (fun n => ∫ z in {z | N z = n}, f (N z) z ∂μ) =
      (fun n => ∫ z in {z | N z = n}, f n z ∂μ) := by
    funext n
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (hm n)] with z hz
    rw [hz]
  simpa only [heq, hcover, Measure.restrict_univ] using hs

/-- The branch expansion in particular justifies the literal infinite sum
rather than merely an equality of total, possibly nonintegrable integrals. -/
theorem sbxS9_integral_countable_select_eq_tsum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (N : α → ℕ) (hN : Measurable N) (f : ℕ → α → ℝ)
    (hf : Integrable (fun z => f (N z) z) μ) :
    (∫ z, f (N z) z ∂μ) = ∑' n, ∫ z in {z | N z = n}, f n z ∂μ :=
  (sbxS9_hasSum_integral_countable_select μ N hN f hf).tsum_eq.symm

/-- The literal first-regeneration time determines a measurable grid index.
The infinite-time fallback is zero and is handled by origin equality. -/
def sbxS9FirstRestartIndex {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (z : FieldPair d × CoupledSample d) : ℕ :=
  ⌊(firstRegenerationTime Δ lam R z.2 i).toReal / (Δ : ℝ)⌋₊

theorem sbxS9_measurable_firstRestartIndex {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) : Measurable (sbxS9FirstRestartIndex Δ lam R i) :=
  (((measurable_firstRegenerationTime Δ lam R i).comp measurable_snd).ennreal_toReal.div_const
    (Δ : ℝ)).nat_floor

/-- On a genuine regeneration slice the selected index is exactly the slice
number; no deterministic substitution is made for its continuous endpoint. -/
theorem sbxS9_firstRestartIndex_eq_of_slice {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d) (z : FieldPair d × CoupledSample d) (n : ℕ)
    (hn : firstRegenerationTime Δ lam R z.2 i = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    sbxS9FirstRestartIndex Δ lam R i z = n := by
  have hΔR : (Δ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hΔ)
  simp only [sbxS9FirstRestartIndex, hn, ENNReal.coe_toReal, NNReal.coe_mul,
    NNReal.coe_natCast, mul_div_cancel_right₀ _ hΔR, Nat.floor_natCast]

/-- The selector's fallback has the stipulated value at infinite time. -/
theorem sbxS9_firstRestartIndex_eq_zero_of_infinite {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (z : FieldPair d × CoupledSample d)
    (h : firstRegenerationTime Δ lam R z.2 i = ⊤) :
    sbxS9FirstRestartIndex Δ lam R i z = 0 := by
  simp only [sbxS9FirstRestartIndex, h, ENNReal.toReal_top, zero_div, Nat.floor_zero]

/-- A finite first regeneration time is recovered exactly from its selected
positive index and the unchanged deterministic grid spacing. -/
theorem sbxS9_firstRestartIndex_recovers_time {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d) (z : FieldPair d × CoupledSample d)
    (hfin : firstRegenerationTime Δ lam R z.2 i ≠ ⊤) :
    1 ≤ sbxS9FirstRestartIndex Δ lam R i z ∧
      firstRegenerationTime Δ lam R z.2 i =
        (((sbxS9FirstRestartIndex Δ lam R i z : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨m, hm⟩ := firstRegenerationTime_eq_succ_grid_of_ne_top Δ hΔ lam R z.2 i hfin
  rw [sbxS9_firstRestartIndex_eq_of_slice Δ hΔ lam R i z (m + 1) hm]
  exact ⟨by omega, hm⟩

/-- The selected first-regeneration endpoint is the literal endpoint on every
finite slice, and its selection events are measurable. -/
theorem sbxS9_measurable_firstRestart_selection_event {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (n : ℕ) :
    MeasurableSet {z | sbxS9FirstRestartIndex Δ lam R i z = n} :=
  measurableSet_eq_fun (sbxS9_measurable_firstRestartIndex Δ lam R i) measurable_const

/-- A selected countable version remains equal after literal recentering
at its continuously distributed endpoint and translating the environment. -/
theorem sbxS9_selected_recentered_origin_restart_fibres_eq {d : ℕ} {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (N : α → ℕ)
    (e : ℕ → α → Vec d × FieldPair d) (K L : ℕ → CoupledQuenchedLaws d)
    (h : ∀ᵐ z ∂μ, K (N z) (e (N z) z) = L (N z) (e (N z) z)) :
    ∀ᵐ z ∂μ,
      sbxS9RecenteredCoupledLaws (K (N z)) (e (N z) z).1
          (0, translate (e (N z) z).1 (e (N z) z).2) =
        sbxS9RecenteredCoupledLaws (L (N z)) (e (N z) z).1
          (0, translate (e (N z) z).1 (e (N z) z).2) := by
  filter_upwards [h] with z hz
  rw [sbxS9_recenteredCoupledLaws_endpoint_origin,
    sbxS9_recenteredCoupledLaws_endpoint_origin, hz]

/-- The selected recentered finite-record law is measurable. The original
outer sample is retained in its entirety alongside the recentered environment. -/
theorem sbxS9_measurable_selected_joint_restart_records {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (Δ : ℝ≥0) (K : ℕ → CoupledQuenchedLaws d)
    (N : FieldPair d × CoupledSample d → ℕ) (hN : Measurable N)
    (n : ℕ) (ks : Fin n → ℕ) :
    Measurable (fun z : FieldPair d × CoupledSample d =>
      ((Probability.probabilityPart (K (N z))) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)).map
        (fun z' => (z, translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
          fun j => regenerationRecord hd lam l (ks j)
            (translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
              recenterSample (z.2.1 ((N z : ℝ≥0) * Δ)) z')))) := by
  apply sbxS9_measurable_countable_select N hN
    (fun m z => ((Probability.probabilityPart (K m)) (z.2.1 ((m : ℝ≥0) * Δ), z.1)).map
      (fun z' => (z, translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
        fun j => regenerationRecord hd lam l (ks j)
          (translate (z.2.1 ((m : ℝ≥0) * Δ)) z.1,
            recenterSample (z.2.1 ((m : ℝ≥0) * Δ)) z'))))
  intro m
  let t : ℝ≥0 := (m : ℝ≥0) * Δ
  have he : Measurable (fun z : FieldPair d × CoupledSample d => (z.2.1 t, z.1)) :=
    ((measurable_pathPosition t).comp measurable_snd.fst).prodMk measurable_fst
  have henv : Measurable
      (fun z : (FieldPair d × CoupledSample d) × CoupledSample d =>
        translate (z.1.2.1 t) z.1.1) :=
    Probability.continuous_translate.measurable.comp (he.comp measurable_fst)
  have hs : Measurable
      (fun z : (FieldPair d × CoupledSample d) × CoupledSample d =>
        recenterSample (z.1.2.1 t) z.2) :=
    measurable_recenterSample.comp ((he.comp measurable_fst).fst.prodMk measurable_snd)
  exact sbxS9_measurable_parameter_map ((Probability.probabilityPart (K m)).comap _ he) _
    (measurable_fst.prodMk (henv.prodMk (measurable_pi_iff.mpr (fun j =>
      (measurable_cycleRecord hd lam l (ks j)).comp (henv.prodMk hs)))))

/-- Finite selected regeneration-record mixtures agree under any legitimate
selected version equality. The map retains the original and recentered fields,
the entire original path/coins, and every requested future record. -/
theorem sbxS9_selected_joint_restart_records_law_eq {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (Δ : ℝ≥0) (μ : Measure (FieldPair d × CoupledSample d))
    (N : FieldPair d × CoupledSample d → ℕ) (K L : ℕ → CoupledQuenchedLaws d)
    (h : ∀ᵐ z ∂μ, K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) =
      L (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)) (n : ℕ) (ks : Fin n → ℕ) :
    μ.bind (fun z =>
      ((Probability.probabilityPart (K (N z))) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)).map
        (fun z' => (z, translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
          fun j => regenerationRecord hd lam l (ks j)
            (translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
              recenterSample (z.2.1 ((N z : ℝ≥0) * Δ)) z')))) =
    μ.bind (fun z =>
      ((Probability.probabilityPart (L (N z))) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)).map
        (fun z' => (z, translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
          fun j => regenerationRecord hd lam l (ks j)
            (translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
              recenterSample (z.2.1 ((N z : ℝ≥0) * Δ)) z')))) := by
  apply Measure.bind_congr_right
  filter_upwards [h] with z hz
  simp only [Probability.probabilityPart_apply, hz]

/-- Mixed tests of the literal selected finite records obey the same
comparison, with arbitrary outer past observations. -/
theorem sbxS9_selected_mixed_restart_record_integral_eq {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (Δ : ℝ≥0) (μ : Measure (FieldPair d × CoupledSample d))
    (N : FieldPair d × CoupledSample d → ℕ) (K L : ℕ → CoupledQuenchedLaws d)
    (h : ∀ᵐ z ∂μ, K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) =
      L (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1))
    (n : ℕ) (ks : Fin n → ℕ) (H : FieldPair d × CoupledSample d → ℝ)
    (Φ : (FieldPair d × CoupledSample d) × FieldPair d ×
      (Fin n → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ) :
    (∫ z, H z * (∫ z', Φ (z, translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
      fun j => regenerationRecord hd lam l (ks j)
        (translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
          recenterSample (z.2.1 ((N z : ℝ≥0) * Δ)) z'))
      ∂K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)) ∂μ) =
    ∫ z, H z * (∫ z', Φ (z, translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
      fun j => regenerationRecord hd lam l (ks j)
        (translate (z.2.1 ((N z : ℝ≥0) * Δ)) z.1,
          recenterSample (z.2.1 ((N z : ℝ≥0) * Δ)) z'))
      ∂L (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with z hz
  rw [hz]

/-- Actual GMP coupling versions can be selected at the literal first
regeneration index. This consumes genuine origin/product equality and does
not infer physical path-law covariance from coupling algebra. -/
theorem sbxS9_firstRestart_versions_eq_of_coupling {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (h : (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p) :
    ∀ᵐ z ∂annealedCoupledLaw Q.measure K,
      let n := sbxS9FirstRestartIndex (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) z
      K (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam), z.1) =
        L (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam), z.1) := by
  filter_upwards [sbxS9_annealed_ae_all_restart_fibres_eq_of_coupling
    hd Q lam h0 h1 l δ P K L hK h] with z hz
  exact hz _

/-- The proved tail removes the selector fallback almost surely, identifying
the selected endpoint with the actual first-regeneration endpoint. -/
theorem sbxS9_first_regeneration_endpoint_versions_eq_of_tail {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ c C : ℝ) (hc : 0 < c)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (h : (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (htail : HasFirstRegenerationTail Q.measure (Renewal.regenDelta lam)
      lam (l / lam) c C (Renewal.forceCoord hd) K) :
    ∀ᵐ z ∂annealedCoupledLaw Q.measure K,
      K (z.2.1 (firstRegenerationTime (Renewal.regenDelta lam)
          lam (l / lam) z.2 (Renewal.forceCoord hd)).toNNReal, z.1) =
        L (z.2.1 (firstRegenerationTime (Renewal.regenDelta lam)
          lam (l / lam) z.2 (Renewal.forceCoord hd)).toNNReal, z.1) := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  filter_upwards [sbxS9_firstRestart_versions_eq_of_coupling hd Q lam h0 h1 l δ P K L hK h,
    firstRegenerationTime_ne_top_ae_of_tail Q.measure K (Renewal.regenDelta lam)
      lam (l / lam) c C hc h0 (Renewal.forceCoord hd) htail] with z hz hfin
  have ht := (sbxS9_firstRestartIndex_recovers_time (Renewal.regenDelta lam) hΔ
    lam (l / lam) (Renewal.forceCoord hd) z hfin).2
  rw [ht, ENNReal.toNNReal_coe]
  exact hz

/-- The selected common good set passes to the literal no-return conditioned
law with no change to its index, endpoint or branch kernel. -/
theorem sbxS9_conditioned_selected_restart_fibres_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ) (Δ : ℝ≥0)
    (B : CoupledQuenchedLaws d) (K L : ℕ → CoupledQuenchedLaws d)
    (hprob : HasProbabilityLaws Q.measure B)
    (hD : annealedCoupledLaw Q.measure B (regenerationNoReturn hd (l / lam)) ≠ 0)
    (h : ∀ᵐ z ∂annealedCoupledLaw Q.measure B, ∀ n : ℕ,
      K n (z.2.1 ((n : ℝ≥0) * Δ), z.1) = L n (z.2.1 ((n : ℝ≥0) * Δ), z.1))
    (N : FieldPair d × CoupledSample d → ℕ) :
    ∀ᵐ z ∂regenerationConditionedLaw hd Q lam l B hprob hD,
      K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) =
        L (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) :=
  sbxS9_selected_restart_fibres_eq Q.measure Δ B K L
    (regenerationConditionedLaw hd Q lam l B hprob hD)
    ProbabilityTheory.cond_absolutelyContinuous h N

/-- The probability-part selector is literally the supplied raw kernel on
every genuine probability fibre. -/
theorem sbxS9_selected_restart_eq_raw {d : ℕ} (Δ : ℝ≥0)
    (K : ℕ → CoupledQuenchedLaws d) (N : FieldPair d × CoupledSample d → ℕ)
    (hN : Measurable N) (z : FieldPair d × CoupledSample d)
    (hp : IsProbabilityMeasure (K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1))) :
    sbxS9SelectedRestartKernel Δ K N hN z = K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) := by
  let := hp
  exact Probability.probabilityPart_eq_of_isProbabilityMeasure (K (N z)) _

/-- The selected raw supplied family is a.e. measurable wherever its
probability fibres have been established, without imposing a global kernel
s-finiteness premise or changing any source-facing statement. -/
theorem sbxS9_aemeasurable_selected_raw_restart_law {d : ℕ} (Δ : ℝ≥0)
    (K : ℕ → CoupledQuenchedLaws d) (N : FieldPair d × CoupledSample d → ℕ)
    (hN : Measurable N) (μ : Measure (FieldPair d × CoupledSample d))
    (hp : ∀ᵐ z ∂μ, IsProbabilityMeasure (K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1))) :
    AEMeasurable (fun z => K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)) μ := by
  apply (sbxS9SelectedRestartKernel Δ K N hN).measurable.aemeasurable.congr
  filter_upwards [hp] with z hz
  exact sbxS9_selected_restart_eq_raw Δ K N hN z hz

/-- Genuine selected restart observations use exactly the original branch
measures. Normalization introduces no change to their joint pushforwards. -/
theorem sbxS9_selected_restart_observation_law_eq_raw {d : ℕ} {β : Type*}
    [MeasurableSpace β] (Δ : ℝ≥0) (K : ℕ → CoupledQuenchedLaws d)
    (N : FieldPair d × CoupledSample d → ℕ) (hN : Measurable N)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hp : ∀ᵐ z ∂μ, IsProbabilityMeasure (K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)))
    (R : (FieldPair d × CoupledSample d) → CoupledSample d → β) :
    μ.bind (fun z => (sbxS9SelectedRestartKernel Δ K N hN z).map (R z)) =
      μ.bind (fun z => (K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)).map (R z)) := by
  apply Measure.bind_congr_right
  filter_upwards [hp] with z hz
  rw [sbxS9_selected_restart_eq_raw Δ K N hN z hz]

/-- Bounded measurable nested restart tests have a summable expansion over
the actual countable selection events, with their original branch measures. -/
theorem sbxS9_hasSum_selected_nested_restart_test {d : ℕ} (Δ : ℝ≥0)
    (K : ℕ → CoupledQuenchedLaws d) (N : FieldPair d × CoupledSample d → ℕ)
    (hN : Measurable N) (μ : Measure (FieldPair d × CoupledSample d)) [IsFiniteMeasure μ]
    (H : FieldPair d × CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (F : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ)
    (hF : Measurable F) (hbF : BoundedRealTest F) :
    HasSum (fun m => ∫ z in {z | N z = m}, H z *
      (∫ z', F (z, z') ∂(Probability.probabilityPart (K m))
        (z.2.1 ((m : ℝ≥0) * Δ), z.1)) ∂μ)
      (∫ z, H z * (∫ z', F (z, z') ∂sbxS9SelectedRestartKernel Δ K N hN z) ∂μ) :=
  sbxS9_hasSum_integral_countable_select μ N hN
    (fun m z => H z * (∫ z', F (z, z') ∂(Probability.probabilityPart (K m))
      (z.2.1 ((m : ℝ≥0) * Δ), z.1)))
    (sbxS9_integrable_selected_nested_restart_test Δ K N hN μ H hH hbH F hF hbF)

/-- Restricting the original sample law preserves joint endpoint absolute
continuity, even when the restriction depends on the path and every coin. -/
theorem sbxS9_restricted_endpoint_law_ac {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    (e : α → β) (he : Measurable e) (s : Set α) (hac : μ.map e ≪ ν) :
    (μ.restrict s).map e ≪ ν :=
  ((Measure.absolutelyContinuous_restrict (μ := μ) (s := s)).map he).trans hac

/-- Push forward the actual restricted branches of a countable disjoint
decomposition. The endpoint map may differ between branches. -/
theorem sbxS9_map_countable_slices {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable ι]
    (μ : Measure α) (s : ι → Set α) (hs : ∀ j, MeasurableSet (s j))
    (hdisj : Pairwise (fun j k => Disjoint (s j) (s k)))
    (e : α → β) (he : Measurable e) (es : ι → α → β)
    (hes : ∀ j z, z ∈ s j → e z = es j z) :
    (μ.restrict (⋃ j, s j)).map e =
      Measure.sum (fun j => (μ.restrict (s j)).map (es j)) := by
  rw [Measure.restrict_iUnion hdisj hs, Measure.map_sum he.aemeasurable]
  congr 1
  funext j
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (hs j)] with z hz
  exact hes j z hz

/-- The joint endpoint with the original environment. At infinite time the
ENNReal conversion selects time zero; finite-part laws below exclude it. -/
def sbxS9FirstRegenerationEndpoint {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (z : FieldPair d × CoupledSample d) : Vec d × FieldPair d :=
  (z.2.1 (firstRegenerationTime Δ lam R z.2 i).toNNReal, z.1)

theorem sbxS9_measurable_firstRegenerationEndpoint {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) : Measurable (sbxS9FirstRegenerationEndpoint Δ lam R i) :=
  (measurable_path_eval.comp
    (((measurable_firstRegenerationTime Δ lam R i).comp measurable_snd).ennreal_toNNReal.prodMk
      measurable_snd.fst)).prodMk measurable_fst

/-- A genuine positive first-regeneration slice, retaining the whole outer
environment/path/coin sample rather than conditioning only on the endpoint. -/
def sbxS9FirstRegenerationSlice {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (n : ℕ) : Set (FieldPair d × CoupledSample d) :=
  {z | firstRegenerationTime Δ lam R z.2 i =
    ((((n + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}

theorem sbxS9_measurableSet_firstRegenerationSlice {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (n : ℕ) :
    MeasurableSet (sbxS9FirstRegenerationSlice Δ lam R i n) :=
  measurableSet_eq_fun ((measurable_firstRegenerationTime Δ lam R i).comp measurable_snd)
    measurable_const

/-- Positive grid slices are disjoint for the unchanged positive spacing. -/
theorem sbxS9_firstRegenerationSlice_pairwise_disjoint {d : ℕ} (Δ : ℝ≥0)
    (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d) :
    Pairwise (fun n m => Disjoint (sbxS9FirstRegenerationSlice Δ lam R i n)
      (sbxS9FirstRegenerationSlice Δ lam R i m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro z hn hm
  have hn' := sbxS9_firstRestartIndex_eq_of_slice Δ hΔ lam R i z (n + 1) hn
  have hm' := sbxS9_firstRestartIndex_eq_of_slice Δ hΔ lam R i z (m + 1) hm
  exact hnm (Nat.add_right_cancel (hn'.symm.trans hm'))

/-- The finite-time event is exactly the union of the genuine positive
slices. Neither zero nor infinite time is silently included. -/
theorem sbxS9_firstRegeneration_finite_eq_iUnion {d : ℕ} (Δ : ℝ≥0)
    (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d) :
    {z : FieldPair d × CoupledSample d | firstRegenerationTime Δ lam R z.2 i ≠ ⊤} =
      ⋃ n : ℕ, sbxS9FirstRegenerationSlice Δ lam R i n := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := firstRegenerationTime_eq_succ_grid_of_ne_top Δ hΔ lam R z.2 i hz
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · intro hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    exact hn.trans_ne ENNReal.coe_ne_top

/-- The literal random endpoint agrees with its deterministic grid endpoint
on the corresponding genuine first-regeneration event. -/
theorem sbxS9_firstRegenerationEndpoint_eq_on_slice {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (n : ℕ) (z : FieldPair d × CoupledSample d)
    (hz : z ∈ sbxS9FirstRegenerationSlice Δ lam R i n) :
    sbxS9FirstRegenerationEndpoint Δ lam R i z =
      (z.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ), z.1) := by
  change firstRegenerationTime Δ lam R z.2 i = _ at hz
  simp only [sbxS9FirstRegenerationEndpoint, hz, ENNReal.toNNReal_coe]

/-- The infinite-time fallback is explicitly the original time-zero
endpoint. No spatial absolute continuity is asserted for this branch. -/
theorem sbxS9_firstRegenerationEndpoint_eq_on_infinite {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (z : FieldPair d × CoupledSample d)
    (hz : firstRegenerationTime Δ lam R z.2 i = ⊤) :
    sbxS9FirstRegenerationEndpoint Δ lam R i z = (z.2.1 0, z.1) := by
  simp only [sbxS9FirstRegenerationEndpoint, hz, ENNReal.toNNReal_top]

/-- The finite first-regeneration endpoint/environment law is the sum of
the original grid-endpoint laws restricted to the genuine slices. -/
theorem sbxS9_finite_firstRegeneration_endpoint_law_eq_sum {d : ℕ} (Δ : ℝ≥0)
    (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (μ : Measure (FieldPair d × CoupledSample d)) :
    (μ.restrict {z | firstRegenerationTime Δ lam R z.2 i ≠ ⊤}).map
        (sbxS9FirstRegenerationEndpoint Δ lam R i) =
      Measure.sum (fun n : ℕ => (μ.restrict (sbxS9FirstRegenerationSlice Δ lam R i n)).map
        (fun z => (z.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ), z.1))) := by
  rw [sbxS9_firstRegeneration_finite_eq_iUnion Δ hΔ lam R i]
  exact sbxS9_map_countable_slices μ _
    (sbxS9_measurableSet_firstRegenerationSlice Δ lam R i)
    (sbxS9_firstRegenerationSlice_pairwise_disjoint Δ hΔ lam R i) _
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i) _
    (sbxS9_firstRegenerationEndpoint_eq_on_slice Δ lam R i)

/-- Deterministic positive-grid joint AC gives the finite first-regeneration
joint AC by restriction and a countable sum, with no stopped-process input. -/
theorem sbxS9_finite_firstRegeneration_endpoint_law_ac {d : ℕ} (Δ : ℝ≥0)
    (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d))
    (hac : ∀ n : ℕ, μ.map (fun z => (z.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ), z.1)) ≪
      (volume : Measure (Vec d)).prod Q) :
    (μ.restrict {z | firstRegenerationTime Δ lam R z.2 i ≠ ⊤}).map
      (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q := by
  rw [sbxS9_finite_firstRegeneration_endpoint_law_eq_sum Δ hΔ lam R i μ]
  apply Measure.absolutelyContinuous_sum_left
  intro n
  exact sbxS9_restricted_endpoint_law_ac μ _ _
    (((measurable_pathPosition _).comp measurable_snd.fst).prodMk measurable_fst) _ (hac n)

/-- Almost-sure finiteness removes the entire infinite-time branch. -/
theorem sbxS9_firstRegeneration_endpoint_law_ac_of_ae_finite {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d))
    (hac : (μ.restrict {z | firstRegenerationTime Δ lam R z.2 i ≠ ⊤}).map
      (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q)
    (hfin : ∀ᵐ z ∂μ, firstRegenerationTime Δ lam R z.2 i ≠ ⊤) :
    μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q := by
  have hr : μ.restrict {z | firstRegenerationTime Δ lam R z.2 i ≠ ⊤} = μ :=
    Measure.restrict_eq_self_of_ae_mem hfin
  rwa [hr] at hac

/-- Positive grid endpoints of the actual supplied coupling have a joint
law absolutely continuous with respect to volume times the environment law. -/
theorem sbxS9_grid_joint_endpoint_law_ac_of_coupling {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (n : ℕ) (hn : 1 ≤ n) :
    (annealedCoupledLaw Q.measure K).map
      (fun z => (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam), z.1)) ≪
      (volume : Measure (Vec d)).prod Q.measure := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have hg := ae_coupledEnvironmentRegular hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  apply sbxS9_annealed_joint_endpoint_law_ac Q.measure K hK.1.1
  filter_upwards [hg] with ω hω
  exact coupled_endpoint_density_of_path_marginal P K (0, ω) hω.2.1.2.1 _
    (hω.2.2.2 n hn 0)

/-- The genuine coupling proves joint AC for the finite first-regeneration
law, without a tail assumption or a new analytic premise. -/
theorem sbxS9_finite_firstRegeneration_endpoint_law_ac_of_coupling {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ((annealedCoupledLaw Q.measure K).restrict
      {z | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) z.2
        (Renewal.forceCoord hd) ≠ ⊤}).map
      (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure := by
  apply sbxS9_finite_firstRegeneration_endpoint_law_ac (Renewal.regenDelta lam)
    (Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2)))
  intro n
  exact sbxS9_grid_joint_endpoint_law_ac_of_coupling hd Q lam h0 h1 l δ P K hK
    (n + 1) (by omega)

/-- Any law dominated by the actual annealed law, including the literal
no-return conditioning, inherits first-regeneration joint AC once finite. -/
theorem sbxS9_firstRegeneration_endpoint_law_ac_of_coupling_and_ae_finite {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) (hμ : μ ≪ annealedCoupledLaw Q.measure K)
    (hfin : ∀ᵐ z ∂μ, firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) z.2
      (Renewal.forceCoord hd) ≠ ⊤) :
    μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure := by
  apply sbxS9_firstRegeneration_endpoint_law_ac_of_ae_finite
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) Q.measure μ _ hfin
  exact ((hμ.restrict _).map
    (sbxS9_measurable_firstRegenerationEndpoint _ _ _ _)).trans
      (sbxS9_finite_firstRegeneration_endpoint_law_ac_of_coupling hd Q lam h0 h1 l δ P K hK)

/-- The stated regeneration tail removes the infinite event under the
actual annealed law, so its full first-regeneration joint law has a density. -/
theorem sbxS9_firstRegeneration_endpoint_law_ac_of_coupling_and_tail {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ c C : ℝ) (hc : 0 < c)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (htail : HasFirstRegenerationTail Q.measure (Renewal.regenDelta lam)
      lam (l / lam) c C (Renewal.forceCoord hd) K) :
    (annealedCoupledLaw Q.measure K).map
      (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure :=
  sbxS9_firstRegeneration_endpoint_law_ac_of_coupling_and_ae_finite
    hd Q lam h0 h1 l δ P K hK _ Measure.AbsolutelyContinuous.rfl
    (firstRegenerationTime_ne_top_ae_of_tail Q.measure K (Renewal.regenDelta lam)
      lam (l / lam) c C hc h0 (Renewal.forceCoord hd) htail)

/-- Conditioning is performed on the original nonzero no-return event.
The conditioned first-regeneration law retains the original joint carrier. -/
theorem sbxS9_conditioned_firstRegeneration_endpoint_law_ac_of_tail {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ c C : ℝ) (hc : 0 < c)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (htail : HasFirstRegenerationTail Q.measure (Renewal.regenDelta lam)
      lam (l / lam) c C (Renewal.forceCoord hd) K) :
    (regenerationConditionedLaw hd Q lam l K hK.1 hD).map
      (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure :=
  (ProbabilityTheory.cond_absolutelyContinuous.map
    (sbxS9_measurable_firstRegenerationEndpoint _ _ _ _)).trans
      (sbxS9_firstRegeneration_endpoint_law_ac_of_coupling_and_tail
        hd Q lam h0 h1 l δ c C hc P K hK htail)

/-- Joint endpoint AC justifies recentering by that same random endpoint.
Stationarity is applied to the reference law before transporting versions. -/
theorem sbxS9_recentered_firstRegeneration_endpoint_law_ac {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (μ : Measure (FieldPair d × CoupledSample d))
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q) :
    μ.map (fun z => ((sbxS9FirstRegenerationEndpoint Δ lam R i z).1,
      translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1)) ≪
      (volume : Measure (Vec d)).prod Q := by
  have h := sbxS9_joint_recentered_endpoint_law_ac Q hQ _ hac
  rw [Measure.map_map (sbxS9_measurePreserving_endpoint_recenterEnvironment Q hQ).measurable
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i)] at h
  exact h

/-- One good set handles every member of a countable kernel family at the
literal first-regeneration endpoint and at its recentered environment. -/
theorem sbxS9_firstRegeneration_ae_all_endpoint_versions_eq {d : ℕ} {ι : Type*}
    [Countable ι] (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (μ : Measure (FieldPair d × CoupledSample d))
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (K L : ι → CoupledQuenchedLaws d)
    (hKL : ∀ j, ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K j p = L j p) :
    ∀ᵐ z ∂μ, ∀ j,
      K j (sbxS9FirstRegenerationEndpoint Δ lam R i z) =
        L j (sbxS9FirstRegenerationEndpoint Δ lam R i z) ∧
      K j ((sbxS9FirstRegenerationEndpoint Δ lam R i z).1,
          translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1) =
        L j ((sbxS9FirstRegenerationEndpoint Δ lam R i z).1,
          translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1) := by
  apply ae_all_iff.mpr
  intro j
  exact (sbxS9_ae_kernel_eq_at_joint_endpoint Q μ _
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).aemeasurable hac
    (K j) (L j) (hKL j)).and
    (sbxS9_ae_kernel_eq_at_recentered_joint_endpoint Q hQ μ _
      (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i) hac (K j) (L j) (hKL j))


/-- The exact scope dependency provides first-cycle finiteness at every
admissible scale under both original laws. No tail threshold is introduced. -/
theorem sbxS9_firstRegeneration_endpoint_law_ac_of_scope
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d)))) :
    μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure := by
  have hdom : μ ≪ annealedCoupledLaw Q.measure K := by
    rcases (show μ = annealedCoupledLaw Q.measure K ∨
        μ = regenerationConditionedLaw hd Q lam l K hK.1 hD from hμ) with rfl | rfl
    · exact Measure.AbsolutelyContinuous.rfl
    · exact ProbabilityTheory.cond_absolutelyContinuous
  apply sbxS9_firstRegeneration_endpoint_law_ac_of_coupling_and_ae_finite
    hd Q lam h0 h1 l δ P K hK μ hdom
  have hs := (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1).2.2 μ hμ
  filter_upwards [hs] with z hz
  obtain ⟨n, _, ht, _⟩ := hz
  have hne := ht.trans_ne ENNReal.coe_ne_top
  simpa only [EinsteinFull.regenerationTime, Regeneration.regenerationTime_one] using hne

/-- Every actual first-regeneration endpoint is a genuine probability fibre
once its joint law is absolutely continuous. -/
theorem sbxS9_firstRegeneration_probability_fibres {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d)) (K : CoupledQuenchedLaws d)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hp : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, IsProbabilityMeasure (K p)) :
    ∀ᵐ z ∂μ, IsProbabilityMeasure (K (sbxS9FirstRegenerationEndpoint Δ lam R i z)) :=
  ae_of_ae_map (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).aemeasurable
    (hac.ae_le hp)

/-- Legitimate endpoint versions give the same recentered origin fibres.
This is algebraic transport of versions and assumes no path-law covariance. -/
theorem sbxS9_firstRegeneration_recentered_origin_versions_eq {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d)) (K L : CoupledQuenchedLaws d)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    ∀ᵐ z ∂μ,
      K (sbxS9FirstRegenerationEndpoint Δ lam R i z) =
        L (sbxS9FirstRegenerationEndpoint Δ lam R i z) ∧
      sbxS9RecenteredCoupledLaws K (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
          (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1) =
        sbxS9RecenteredCoupledLaws L (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
          (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1) := by
  filter_upwards [sbxS9_ae_kernel_eq_at_joint_endpoint Q μ _
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).aemeasurable hac K L hKL]
    with z hz
  refine ⟨hz, ?_⟩
  change sbxS9RecenteredCoupledLaws K (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
      (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
        (sbxS9FirstRegenerationEndpoint Δ lam R i z).2) =
    sbxS9RecenteredCoupledLaws L (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
      (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
        (sbxS9FirstRegenerationEndpoint Δ lam R i z).2)
  rw [sbxS9_recenteredCoupledLaws_endpoint_origin K
      (sbxS9FirstRegenerationEndpoint Δ lam R i z),
    sbxS9_recenteredCoupledLaws_endpoint_origin L
      (sbxS9FirstRegenerationEndpoint Δ lam R i z), hz]

/-- Finite joint observations of the actual first restart have a measurable
family of laws. Both fields, the outer path and all coins remain present. -/
theorem sbxS9_measurable_firstRegeneration_joint_restart_records {d : ℕ}
    (hd : 2 ≤ d) (lam l : ℝ) (Δ : ℝ≥0) (K : CoupledQuenchedLaws d)
    (n : ℕ) (ks : Fin n → ℕ) :
    Measurable (fun z : FieldPair d × CoupledSample d =>
      ((Probability.probabilityPart K) (sbxS9FirstRegenerationEndpoint Δ lam (l / lam)
        (Renewal.forceCoord hd) z)).map
        (fun z' => (z, translate (sbxS9FirstRegenerationEndpoint Δ lam (l / lam)
            (Renewal.forceCoord hd) z).1 z.1,
          fun j => regenerationRecord hd lam l (ks j)
            (translate (sbxS9FirstRegenerationEndpoint Δ lam (l / lam)
                (Renewal.forceCoord hd) z).1 z.1,
              recenterSample (sbxS9FirstRegenerationEndpoint Δ lam (l / lam)
                (Renewal.forceCoord hd) z).1 z')))) := by
  let e := sbxS9FirstRegenerationEndpoint Δ lam (l / lam) (Renewal.forceCoord hd)
  have he : Measurable e := sbxS9_measurable_firstRegenerationEndpoint _ _ _ _
  have henv : Measurable
      (fun z : (FieldPair d × CoupledSample d) × CoupledSample d =>
        translate (e z.1).1 z.1.1) :=
    Probability.continuous_translate.measurable.comp (he.comp measurable_fst)
  have hs : Measurable
      (fun z : (FieldPair d × CoupledSample d) × CoupledSample d =>
        recenterSample (e z.1).1 z.2) :=
    measurable_recenterSample.comp ((he.comp measurable_fst).fst.prodMk measurable_snd)
  exact sbxS9_measurable_parameter_map ((Probability.probabilityPart K).comap e he) _
    (measurable_fst.prodMk (henv.prodMk (measurable_pi_iff.mpr (fun j =>
      (measurable_cycleRecord hd lam l (ks j)).comp (henv.prodMk hs)))))

/-- Arbitrary measurable observations, including complete recentered records,
have the same mixture under legitimate first-endpoint kernel versions. -/
theorem sbxS9_firstRegeneration_restart_observation_law_eq {d : ℕ} {β : Type*}
    [MeasurableSpace β] (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d)) (μ : Measure (FieldPair d × CoupledSample d))
    (K L : CoupledQuenchedLaws d)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p)
    (F : (FieldPair d × CoupledSample d) → CoupledSample d → β) :
    μ.bind (fun z => (K (sbxS9FirstRegenerationEndpoint Δ lam R i z)).map (F z)) =
      μ.bind (fun z => (L (sbxS9FirstRegenerationEndpoint Δ lam R i z)).map (F z)) := by
  apply Measure.bind_congr_right
  filter_upwards [sbxS9_ae_kernel_eq_at_joint_endpoint Q μ _
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).aemeasurable hac K L hKL]
    with z hz
  rw [hz]

/-- Nested tests at the first regeneration endpoint keep the complete outer
sample, and may observe every coordinate of the new sample. -/
theorem sbxS9_firstRegeneration_nested_restart_integral_eq {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d)) (K L : CoupledQuenchedLaws d)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p)
    (H : FieldPair d × CoupledSample d → ℝ)
    (F : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ) :
    (∫ z, H z * (∫ z', F (z, z') ∂K (sbxS9FirstRegenerationEndpoint Δ lam R i z)) ∂μ) =
      ∫ z, H z * (∫ z', F (z, z') ∂L (sbxS9FirstRegenerationEndpoint Δ lam R i z)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [sbxS9_ae_kernel_eq_at_joint_endpoint Q μ _
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).aemeasurable hac K L hKL]
    with z hz
  rw [hz]

/-- The literal finite-record observation retains the original full sample,
the translated physical field, and all requested recentered future records. -/
theorem sbxS9_firstRegeneration_joint_restart_records_law_eq {d : ℕ}
    (hd : 2 ≤ d) (lam l : ℝ) (Δ : ℝ≥0) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d)) (K L : CoupledQuenchedLaws d)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam (l / lam)
      (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p)
    (n : ℕ) (ks : Fin n → ℕ) :
    let e := sbxS9FirstRegenerationEndpoint Δ lam (l / lam) (Renewal.forceCoord hd)
    let F := fun z : FieldPair d × CoupledSample d => fun z' : CoupledSample d =>
      (z, translate (e z).1 z.1, fun j => regenerationRecord hd lam l (ks j)
        (translate (e z).1 z.1, recenterSample (e z).1 z'))
    μ.bind (fun z => (K (e z)).map (F z)) =
      μ.bind (fun z => (L (e z)).map (F z)) :=
  sbxS9_firstRegeneration_restart_observation_law_eq Δ lam (l / lam)
    (Renewal.forceCoord hd) Q μ K L hac hKL _

/-- Bounded measurable nested tests of the raw supplied first-endpoint law
are integrable under a finite outer law whenever its fibres are probabilities.
The measurable probability part is removed a.e., rather than imposed globally. -/
theorem sbxS9_integrable_firstRegeneration_nested_restart_test {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (μ : Measure (FieldPair d × CoupledSample d)) [IsFiniteMeasure μ]
    (K : CoupledQuenchedLaws d)
    (hp : ∀ᵐ z ∂μ, IsProbabilityMeasure (K (sbxS9FirstRegenerationEndpoint Δ lam R i z)))
    (H : FieldPair d × CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (F : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ)
    (hF : Measurable F) (hbF : BoundedRealTest F) :
    Integrable (fun z => H z *
      (∫ z', F (z, z') ∂K (sbxS9FirstRegenerationEndpoint Δ lam R i z))) μ := by
  let e := sbxS9FirstRegenerationEndpoint Δ lam R i
  have he : Measurable e := sbxS9_measurable_firstRegenerationEndpoint _ _ _ _
  let κ := (Probability.probabilityPart K).comap e he
  have hm : Measurable (fun z => H z * (∫ z', F (z, z') ∂κ z)) :=
    hH.mul (hF.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hsame : (fun z => H z * (∫ z', F (z, z') ∂κ z)) =ᵐ[μ]
      (fun z => H z * (∫ z', F (z, z') ∂K (e z))) := by
    filter_upwards [hp] with z hz
    let : IsProbabilityMeasure (K (e z)) := hz
    change H z * (∫ z', F (z, z') ∂Probability.probabilityPart K (e z)) = _
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
  obtain ⟨C, hC⟩ := hbH
  obtain ⟨D, hD⟩ := hbF
  apply Integrable.congr (Integrable.of_bound hm.aestronglyMeasurable
    (max C 0 * max D 0) ?_) hsame
  filter_upwards [hp] with z hz
  let : IsProbabilityMeasure (K (e z)) := hz
  change ‖H z * (∫ z', F (z, z') ∂Probability.probabilityPart K (e z))‖ ≤ _
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
  have hint : ‖∫ z', F (z, z') ∂K (e z)‖ ≤ max D 0 := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
        (fun z' => by simpa only [Real.norm_eq_abs] using
          (hD (z, z')).trans (le_max_left D 0))) :
        ‖∫ z', F (z, z') ∂K (e z)‖ ≤ max D 0 * (K (e z)).real Set.univ)
  rw [norm_mul]
  have hbound : ‖H z‖ ≤ max C 0 := by
    simpa only [Real.norm_eq_abs] using (hC z).trans (le_max_left C 0)
  exact mul_le_mul hbound hint (norm_nonneg _) (le_max_right C 0)

/-- Positive grid spacing excludes time zero for every sample, including
those whose first regeneration time is infinite. -/
theorem sbxS9_firstRegenerationTime_ne_zero {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d) (z : CoupledSample d) :
    firstRegenerationTime Δ lam R z i ≠ 0 := by
  intro hz
  have hb := delta_le_firstRegenerationTime Δ lam R z i
  rw [hz] at hb
  exact (not_le_of_gt hΔ) (ENNReal.coe_le_coe.mp hb)


/-- The stationary endpoint recentering is valid under each of the two
actual laws in the exact scope dependency, including all admissible scales. -/
theorem sbxS9_recentered_firstRegeneration_endpoint_law_ac_of_scope
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d)))) :
    μ.map (fun z =>
      ((sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) z).1,
        translate (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) z).1 z.1)) ≪
      (volume : Measure (Vec d)).prod Q.measure :=
  sbxS9_recentered_firstRegeneration_endpoint_law_ac Q.measure Q.stationary _ _ _ _ μ
    (sbxS9_firstRegeneration_endpoint_law_ac_of_scope hscope hd Q lam h0 h1
      l δ hl hsep hδ0 hδ1 P K hK hD μ hμ)

/-- Concrete first-regeneration finite-record comparison for either actual
law. It consumes only a legitimate spatial version equality after deriving
endpoint AC from the supplied coupling and exact scope dependency. -/
theorem sbxS9_firstRegeneration_joint_records_eq_of_scope
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d))))
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (n : ℕ) (ks : Fin n → ℕ) :
    let e := sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd)
    let F := fun z : FieldPair d × CoupledSample d => fun z' : CoupledSample d =>
      (z, translate (e z).1 z.1, fun j => regenerationRecord hd lam l (ks j)
        (translate (e z).1 z.1, recenterSample (e z).1 z'))
    μ.bind (fun z => (K (e z)).map (F z)) =
      μ.bind (fun z => (L (e z)).map (F z)) :=
  sbxS9_firstRegeneration_joint_restart_records_law_eq hd lam l _ Q.measure μ K L
    (sbxS9_firstRegeneration_endpoint_law_ac_of_scope hscope hd Q lam h0 h1
      l δ hl hsep hδ0 hδ1 P K hK hD μ hμ) hKL n ks

/-- Concrete mixed record tests at the first restart obey the same version
comparison under both original laws, retaining the entire original sample. -/
theorem sbxS9_firstRegeneration_mixed_record_integral_eq_of_scope
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d))))
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (n : ℕ) (ks : Fin n → ℕ) (H : FieldPair d × CoupledSample d → ℝ)
    (Φ : (FieldPair d × CoupledSample d) × FieldPair d ×
      (Fin n → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ) :
    let e := sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd)
    let F := fun z : FieldPair d × CoupledSample d => fun z' : CoupledSample d =>
      Φ (z, translate (e z).1 z.1, fun j => regenerationRecord hd lam l (ks j)
        (translate (e z).1 z.1, recenterSample (e z).1 z'))
    (∫ z, H z * (∫ z', F z z' ∂K (e z)) ∂μ) =
      ∫ z, H z * (∫ z', F z z' ∂L (e z)) ∂μ := by
  let e := sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
    (Renewal.forceCoord hd)
  exact sbxS9_firstRegeneration_nested_restart_integral_eq _ lam (l / lam)
    (Renewal.forceCoord hd) Q.measure μ K L
    (sbxS9_firstRegeneration_endpoint_law_ac_of_scope hscope hd Q lam h0 h1
      l δ hl hsep hδ0 hδ1 P K hK hD μ hμ) hKL H (fun w =>
        Φ (w.1, translate (e w.1).1 w.1.1, fun j => regenerationRecord hd lam l (ks j)
          (translate (e w.1).1 w.1.1, recenterSample (e w.1).1 w.2)))

/-- The actual endpoint kernel, with its sample recentered, is exactly the
algebraically recentered kernel at the translated origin. This is a pushforward
identity, not covariance of the original supplied path laws. -/
theorem sbxS9_firstRegeneration_nested_integral_recentered_origin {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (μ : Measure (FieldPair d × CoupledSample d)) (K : CoupledQuenchedLaws d)
    (H : FieldPair d × CoupledSample d → ℝ)
    (F : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ) :
    (∫ z, H z * (∫ z', F (z, recenterSample
        (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z')
      ∂K (sbxS9FirstRegenerationEndpoint Δ lam R i z)) ∂μ) =
      ∫ z, H z * (∫ z', F (z, z')
        ∂sbxS9RecenteredCoupledLaws K (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
          (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [] with z
  change H z * (∫ z', F (z, recenterSample
      (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z')
      ∂K (sbxS9FirstRegenerationEndpoint Δ lam R i z)) =
    H z * (∫ z', F (z, z')
      ∂sbxS9RecenteredCoupledLaws K (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
        (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
          (sbxS9FirstRegenerationEndpoint Δ lam R i z).2))
  simp only [sbxS9_recenteredCoupledLaws_endpoint_origin, integral_map_equiv,
    recenterSampleEquiv_apply]

/-- The recentered-origin identity specialized to complete first-regeneration
record tests retains both environments, the original path and all coins. -/
theorem sbxS9_firstRegeneration_mixed_record_integral_recentered_origin {d : ℕ}
    (hd : 2 ≤ d) (lam l : ℝ) (Δ : ℝ≥0)
    (μ : Measure (FieldPair d × CoupledSample d)) (K : CoupledQuenchedLaws d)
    (n : ℕ) (ks : Fin n → ℕ) (H : FieldPair d × CoupledSample d → ℝ)
    (Φ : (FieldPair d × CoupledSample d) × FieldPair d ×
      (Fin n → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ) :
    let e := sbxS9FirstRegenerationEndpoint Δ lam (l / lam) (Renewal.forceCoord hd)
    let F := fun z : FieldPair d × CoupledSample d => fun z' : CoupledSample d =>
      Φ (z, translate (e z).1 z.1, fun j => regenerationRecord hd lam l (ks j)
        (translate (e z).1 z.1, z'))
    (∫ z, H z * (∫ z', F z (recenterSample (e z).1 z') ∂K (e z)) ∂μ) =
      ∫ z, H z * (∫ z', F z z' ∂sbxS9RecenteredCoupledLaws K (e z).1
        (0, translate (e z).1 z.1)) ∂μ := by
  let e := sbxS9FirstRegenerationEndpoint Δ lam (l / lam) (Renewal.forceCoord hd)
  exact sbxS9_firstRegeneration_nested_integral_recentered_origin Δ lam (l / lam)
    (Renewal.forceCoord hd) μ K H (fun w =>
      Φ (w.1, translate (e w.1).1 w.1.1, fun j => regenerationRecord hd lam l (ks j)
        (translate (e w.1).1 w.1.1, w.2)))

/-- A density on the original sample, after its literal event restriction.
No coordinate of the path or Bernoulli sample is discarded. -/
def sbxS9WeightedRestriction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (w : α → ℝ) : Measure α :=
  (μ.restrict s).withDensity (fun z => ENNReal.ofReal (w z))

/-- Weighting and restriction are both dominated by the original sample law. -/
theorem sbxS9_weightedRestriction_ac {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (w : α → ℝ) :
    sbxS9WeightedRestriction μ s w ≪ μ :=
  (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

/-- An integrable nonnegative sample density gives a finite restricted law,
even when the original measure itself is not finite. -/
theorem sbxS9_weightedRestriction_isFinite {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (w : α → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ z ∂μ, 0 ≤ w z) : IsFiniteMeasure (sbxS9WeightedRestriction μ s w) := by
  apply isFiniteMeasure_withDensity
  exact ((hasFiniteIntegral_iff_ofReal (ae_restrict_of_ae hw0)).mp
    hw.restrict.hasFiniteIntegral).ne

/-- The actual density is AE measurable for the restricted sample law. -/
theorem sbxS9_weightedRestriction_density_aemeasurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (w : α → ℝ) (hw : Integrable w μ) :
    AEMeasurable (fun z => ENNReal.ofReal (w z)) (μ.restrict s) :=
  hw.restrict.aestronglyMeasurable.aemeasurable.ennreal_ofReal

/-- Integrability under the weighted law is exactly integrability of the
signed observation multiplied by the original nonnegative density. -/
theorem sbxS9_integrable_weightedRestriction_iff {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (w : α → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ z ∂μ, 0 ≤ w z) (f : α → ℝ) :
    Integrable f (sbxS9WeightedRestriction μ s w) ↔
      Integrable (fun z => w z * f z) (μ.restrict s) := by
  rw [sbxS9WeightedRestriction,
    integrable_withDensity_iff_integrable_smul₀'
      (sbxS9_weightedRestriction_density_aemeasurable μ s w hw)
      (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [ae_restrict_of_ae hw0] with z hz
  rw [ENNReal.toReal_ofReal hz, smul_eq_mul]

/-- Signed weighted integrals retain their literal restriction event. -/
theorem sbxS9_integral_weightedRestriction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (w : α → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ z ∂μ, 0 ≤ w z) (f : α → ℝ) :
    (∫ z, f z ∂sbxS9WeightedRestriction μ s w) = ∫ z in s, w z * f z ∂μ := by
  rw [sbxS9WeightedRestriction, integral_withDensity_eq_integral_toReal_smul₀
    (sbxS9_weightedRestriction_density_aemeasurable μ s w hw)
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hw0] with z hz
  rw [ENNReal.toReal_ofReal hz, smul_eq_mul]

/-- Domination is pushed through the actual endpoint map. -/
theorem sbxS9_weighted_endpoint_law_ac {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    (e : α → β) (he : Measurable e) (s : Set α) (w : α → ℝ)
    (hac : μ.map e ≪ ν) : (sbxS9WeightedRestriction μ s w).map e ≪ ν :=
  ((sbxS9_weightedRestriction_ac μ s w).map he).trans hac

/-- Bounded environment observations may multiply an integrable density.
This applies in particular to the bounded local-field tests of the source. -/
theorem sbxS9_integrable_density_mul_environment {d : ℕ}
    (μ : Measure (FieldPair d × CoupledSample d))
    (w : FieldPair d × CoupledSample d → ℝ) (hw : Integrable w μ)
    (B : FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    Integrable (fun z => w z * B z.1) μ := by
  obtain ⟨C, hC⟩ := hbB
  exact hw.mul_bdd (hB.comp measurable_fst).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs] using hC z.1))

/-- Every integrable bounded-environment-weighted no-return law is finite.
The weight and no-return event are evaluated on the same original sample. -/
theorem sbxS9_weighted_noReturn_isFinite {d : ℕ} (hd : 2 ≤ d) (R : ℝ)
    (μ : Measure (FieldPair d × CoupledSample d))
    (w : FieldPair d × CoupledSample d → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ z ∂μ, 0 ≤ w z) (B : FieldPair d → ℝ) (hB : Measurable B)
    (hbB : BoundedRealTest B) (hB0 : ∀ ω, 0 ≤ B ω) :
    IsFiniteMeasure (sbxS9WeightedRestriction μ (regenerationNoReturn hd R)
      (fun z => w z * B z.1)) := by
  apply sbxS9_weightedRestriction_isFinite
    μ (regenerationNoReturn hd R) (fun z => w z * B z.1)
    (sbxS9_integrable_density_mul_environment μ w hw B hB hbB)
  filter_upwards [hw0] with z hz
  exact mul_nonneg hz (hB0 z.1)

/-- Actual first-regeneration endpoint AC survives every sample density and
restriction, including the source no-return event. -/
theorem sbxS9_weighted_firstRegeneration_endpoint_law_ac {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d))
    (s : Set (FieldPair d × CoupledSample d))
    (w : FieldPair d × CoupledSample d → ℝ)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q) :
    (sbxS9WeightedRestriction μ s w).map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q :=
  sbxS9_weighted_endpoint_law_ac μ _ _
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i) s w hac

/-- Stationarity is used only on the joint reference measure, after weighted
endpoint domination has been proved. -/
theorem sbxS9_weighted_recentered_firstRegeneration_endpoint_law_ac {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (μ : Measure (FieldPair d × CoupledSample d))
    (s : Set (FieldPair d × CoupledSample d))
    (w : FieldPair d × CoupledSample d → ℝ)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q) :
    (sbxS9WeightedRestriction μ s w).map (fun z =>
      ((sbxS9FirstRegenerationEndpoint Δ lam R i z).1,
        translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1)) ≪
      (volume : Measure (Vec d)).prod Q :=
  sbxS9_recentered_firstRegeneration_endpoint_law_ac Q hQ Δ lam R i _
    (sbxS9_weighted_firstRegeneration_endpoint_law_ac Δ lam R i Q μ s w hac)

/-- The full joint law of an outer sample and its restart is the literal
mixture of the fibre laws; this identity precedes signed integration. -/
theorem sbxS9_map_compProd_eq_bind {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (F : α × β → γ) (hF : Measurable F) :
    (μ ⊗ₘ κ).map F = μ.bind (fun z => (κ z).map (fun z' => F (z, z'))) := by
  ext s hs
  rw [Measure.map_apply hF hs, Measure.compProd_apply (hF hs),
    Measure.bind_apply hs (sbxS9_measurable_parameter_map κ _ hF).aemeasurable]
  apply lintegral_congr
  intro z
  exact (Measure.map_apply
    (show Measurable (fun z' => F (z, z')) from hF.comp measurable_prodMk_left) hs).symm

/-- Equality of genuine joint pushforwards transfers signed integrability
before their nested integrals are formed. -/
theorem sbxS9_integrable_joint_observation_transport {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (κ η : Kernel α β)
    (F : α × β → γ) (hF : Measurable F)
    (hlaw : (μ ⊗ₘ κ).map F = (μ ⊗ₘ η).map F)
    (Φ : γ → ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ ((μ ⊗ₘ κ).map F)) :
    Integrable Φ ((μ ⊗ₘ η).map F) ∧
      Integrable (fun z => Φ (F z)) (μ ⊗ₘ κ) ∧
      Integrable (fun z => Φ (F z)) (μ ⊗ₘ η) := by
  have hj : Integrable Φ ((μ ⊗ₘ η).map F) := hlaw ▸ hi
  exact ⟨hj, (integrable_map_measure hΦ.aestronglyMeasurable hF.aemeasurable).mp hi,
    (integrable_map_measure hΦ.aestronglyMeasurable hF.aemeasurable).mp hj⟩

/-- Signed integrable full-sample observations admit nested integration.
No uniform bound on the observation is needed. -/
theorem sbxS9_integrable_joint_nested_test {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (f : α × β → ℝ) (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun z => ∫ z', f (z, z') ∂κ z) μ := by
  have hm := hf.aestronglyMeasurable.integral_kernel_compProd
  have hn := ((Measure.integrable_compProd_iff hf.aestronglyMeasurable).mp hf).2
  exact hn.mono hm (Filter.Eventually.of_forall (fun z =>
    (norm_integral_le_integral_norm _).trans_eq
      (Real.norm_of_nonneg (integral_nonneg (fun z' => norm_nonneg (f (z, z'))))).symm))

/-- Nested signed integration is justified on both actual joint laws. -/
theorem sbxS9_integral_joint_observation_transport {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SFinite μ] (κ η : Kernel α β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (F : α × β → γ) (hF : Measurable F)
    (hlaw : (μ ⊗ₘ κ).map F = (μ ⊗ₘ η).map F)
    (Φ : γ → ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ ((μ ⊗ₘ κ).map F)) :
    (∫ z, ∫ z', Φ (F (z, z')) ∂κ z ∂μ) =
      ∫ z, ∫ z', Φ (F (z, z')) ∂η z ∂μ := by
  obtain ⟨_, hiκ, hiη⟩ :=
    sbxS9_integrable_joint_observation_transport μ κ η F hF hlaw Φ hΦ hi
  rw [← Measure.integral_compProd hiκ, ← Measure.integral_compProd hiη,
    ← integral_map hF.aemeasurable hΦ.aestronglyMeasurable,
    ← integral_map hF.aemeasurable hΦ.aestronglyMeasurable, hlaw]

/-- A complete finite record observation at an actual sample endpoint.
The outer environment, path and every coin remain in the first component. -/
def sbxS9RestartRecordsMap {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (e : FieldPair d × CoupledSample d → Vec d × FieldPair d)
    (n : ℕ) (ks : Fin n → ℕ)
    (w : (FieldPair d × CoupledSample d) × CoupledSample d) :
    (FieldPair d × CoupledSample d) × FieldPair d ×
      (Fin n → FutureState d (Renewal.forceCoord hd) (l / lam)) :=
  (w.1, translate (e w.1).1 w.1.1, fun j => regenerationRecord hd lam l (ks j)
    (translate (e w.1).1 w.1.1, recenterSample (e w.1).1 w.2))

/-- Joint measurability retains the endpoint, the full outer sample and all
future records without specializing a spatial exceptional fibre. -/
theorem sbxS9_measurable_restartRecordsMap {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (e : FieldPair d × CoupledSample d → Vec d × FieldPair d) (he : Measurable e)
    (n : ℕ) (ks : Fin n → ℕ) : Measurable (sbxS9RestartRecordsMap hd lam l e n ks) := by
  have henv : Measurable
      (fun z : (FieldPair d × CoupledSample d) × CoupledSample d =>
        translate (e z.1).1 z.1.1) :=
    Probability.continuous_translate.measurable.comp
      ((he.comp measurable_fst).fst.prodMk measurable_fst.fst)
  have hs : Measurable
      (fun z : (FieldPair d × CoupledSample d) × CoupledSample d =>
        recenterSample (e z.1).1 z.2) :=
    measurable_recenterSample.comp ((he.comp measurable_fst).fst.prodMk measurable_snd)
  exact measurable_fst.prodMk (henv.prodMk (measurable_pi_iff.mpr (fun j =>
    (measurable_cycleRecord hd lam l (ks j)).comp (henv.prodMk hs))))

/-- Selected version equality gives equality of the full sample/restart
joint measures, before any record observation or signed integration. -/
theorem sbxS9_selected_restart_compProd_eq {d : ℕ} (Δ : ℝ≥0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (N : FieldPair d × CoupledSample d → ℕ) (hN : Measurable N)
    (K L : ℕ → CoupledQuenchedLaws d)
    (h : ∀ᵐ z ∂μ, K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) =
      L (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)) :
    μ ⊗ₘ sbxS9SelectedRestartKernel Δ K N hN =
      μ ⊗ₘ sbxS9SelectedRestartKernel Δ L N hN := by
  apply Measure.compProd_congr
  filter_upwards [h] with z hz
  change Probability.probabilityPart (K (N z)) _ = Probability.probabilityPart (L (N z)) _
  simp only [Probability.probabilityPart_apply, hz]

/-- Signed integrable observations of literal selected finite record tuples
transfer to the other version and have integrable nested expectations on
both sides. An unbounded past test is allowed inside the joint observation. -/
theorem sbxS9_integrable_selected_restart_records {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (Δ : ℝ≥0) (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (N : FieldPair d × CoupledSample d → ℕ) (hN : Measurable N)
    (K L : ℕ → CoupledQuenchedLaws d)
    (h : ∀ᵐ z ∂μ, K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) =
      L (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1))
    (n : ℕ) (ks : Fin n → ℕ)
    (Φ : (FieldPair d × CoupledSample d) × FieldPair d ×
      (Fin n → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ)
    (hΦ : Measurable Φ)
    (hi : Integrable Φ ((μ ⊗ₘ sbxS9SelectedRestartKernel Δ K N hN).map
      (sbxS9RestartRecordsMap hd lam l
        (fun z => (z.2.1 ((N z : ℝ≥0) * Δ), z.1)) n ks))) :
    let F := sbxS9RestartRecordsMap hd lam l
      (fun z => (z.2.1 ((N z : ℝ≥0) * Δ), z.1)) n ks
    Integrable Φ ((μ ⊗ₘ sbxS9SelectedRestartKernel Δ L N hN).map F) ∧
      Integrable (fun z => ∫ z', Φ (F (z, z')) ∂sbxS9SelectedRestartKernel Δ K N hN z) μ ∧
      Integrable (fun z => ∫ z', Φ (F (z, z')) ∂sbxS9SelectedRestartKernel Δ L N hN z) μ ∧
      (∫ z, ∫ z', Φ (F (z, z')) ∂sbxS9SelectedRestartKernel Δ K N hN z ∂μ) =
        ∫ z, ∫ z', Φ (F (z, z')) ∂sbxS9SelectedRestartKernel Δ L N hN z ∂μ := by
  let e := fun z : FieldPair d × CoupledSample d =>
    (z.2.1 ((N z : ℝ≥0) * Δ), z.1)
  have he : Measurable e := sbxS9_measurable_countable_select N hN
    (fun m z => (z.2.1 ((m : ℝ≥0) * Δ), z.1))
    (fun m => ((measurable_pathPosition ((m : ℝ≥0) * Δ)).comp
      measurable_snd.fst).prodMk measurable_fst)
  let F := sbxS9RestartRecordsMap hd lam l e n ks
  have hF : Measurable F := sbxS9_measurable_restartRecordsMap hd lam l e he n ks
  have hlaw := congrArg (fun ν => ν.map F)
    (sbxS9_selected_restart_compProd_eq Δ μ N hN K L h)
  obtain ⟨hj, hiK, hiL⟩ := sbxS9_integrable_joint_observation_transport μ
    (sbxS9SelectedRestartKernel Δ K N hN) (sbxS9SelectedRestartKernel Δ L N hN)
    F hF hlaw Φ hΦ hi
  exact ⟨hj, sbxS9_integrable_joint_nested_test μ _ _ hiK,
    sbxS9_integrable_joint_nested_test μ _ _ hiL,
    sbxS9_integral_joint_observation_transport μ _ _ F hF hlaw Φ hΦ hi⟩

/-- Probability-part normalization disappears only on the proved genuine
selected fibres. Signed integrability is inherited from the full joint law. -/
theorem sbxS9_integrable_selected_raw_nested_test {d : ℕ} (Δ : ℝ≥0)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (K : ℕ → CoupledQuenchedLaws d)
    (N : FieldPair d × CoupledSample d → ℕ) (hN : Measurable N)
    (hp : ∀ᵐ z ∂μ, IsProbabilityMeasure (K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)))
    (f : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ)
    (hf : Integrable f (μ ⊗ₘ sbxS9SelectedRestartKernel Δ K N hN)) :
    Integrable (fun z => ∫ z', f (z, z')
      ∂K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)) μ := by
  apply (sbxS9_integrable_joint_nested_test μ _ f hf).congr
  filter_upwards [hp] with z hz
  rw [sbxS9_selected_restart_eq_raw Δ K N hN z hz]

/-- A signed integrable selected observation has a genuine countable
branch expansion, with every original branch measure and no boundedness premise. -/
theorem sbxS9_hasSum_integrable_selected_raw_nested_test {d : ℕ} (Δ : ℝ≥0)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (K : ℕ → CoupledQuenchedLaws d)
    (N : FieldPair d × CoupledSample d → ℕ) (hN : Measurable N)
    (hp : ∀ᵐ z ∂μ, IsProbabilityMeasure (K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1)))
    (f : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ)
    (hf : Integrable f (μ ⊗ₘ sbxS9SelectedRestartKernel Δ K N hN)) :
    HasSum (fun m => ∫ z in {z | N z = m},
      (∫ z', f (z, z') ∂K m (z.2.1 ((m : ℝ≥0) * Δ), z.1)) ∂μ)
      (∫ z, ∫ z', f (z, z') ∂K (N z) (z.2.1 ((N z : ℝ≥0) * Δ), z.1) ∂μ) :=
  sbxS9_hasSum_integral_countable_select μ N hN
    (fun m z => ∫ z', f (z, z') ∂K m (z.2.1 ((m : ℝ≥0) * Δ), z.1))
    (sbxS9_integrable_selected_raw_nested_test Δ μ K N hN hp f hf)

/-- A single common event survives weighting for every grid restart.
The zero grid branch still uses the separately supplied origin equality. -/
theorem sbxS9_weighted_ae_all_restart_fibres_eq_of_coupling {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (h : (∀ᵐ ω ∂Q.measure, K (0, ω) = L (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (s : Set (FieldPair d × CoupledSample d))
    (w : FieldPair d × CoupledSample d → ℝ) :
    ∀ᵐ z ∂sbxS9WeightedRestriction (annealedCoupledLaw Q.measure K) s w, ∀ n : ℕ,
      K (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam), z.1) =
        L (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam), z.1) ∧
      sbxS9RecenteredCoupledLaws K (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam))
          (0, translate (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam)) z.1) =
        sbxS9RecenteredCoupledLaws L (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam))
          (0, translate (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam)) z.1) := by
  have hgood := (sbxS9_weightedRestriction_ac (annealedCoupledLaw Q.measure K) s w).ae_le
    (sbxS9_annealed_ae_all_restart_fibres_eq_of_coupling hd Q lam h0 h1 l δ P K L hK h)
  filter_upwards [hgood] with z hz n
  refine ⟨hz n, ?_⟩
  rw [sbxS9_recenteredCoupledLaws_endpoint_origin K
      (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam), z.1),
    sbxS9_recenteredCoupledLaws_endpoint_origin L
      (z.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam), z.1), hz n]

/-- One weighted good event handles every countable endpoint version and
its algebraically recentered origin. No random-shift stationarity is asserted. -/
theorem sbxS9_weighted_firstRegeneration_ae_all_versions_eq {d : ℕ} {ι : Type*}
    [Countable ι] (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (μ : Measure (FieldPair d × CoupledSample d))
    (s : Set (FieldPair d × CoupledSample d))
    (w : FieldPair d × CoupledSample d → ℝ)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (K L : ι → CoupledQuenchedLaws d)
    (hKL : ∀ j, ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K j p = L j p) :
    ∀ᵐ z ∂sbxS9WeightedRestriction μ s w, ∀ j,
      K j (sbxS9FirstRegenerationEndpoint Δ lam R i z) =
        L j (sbxS9FirstRegenerationEndpoint Δ lam R i z) ∧
      K j ((sbxS9FirstRegenerationEndpoint Δ lam R i z).1,
          translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1) =
        L j ((sbxS9FirstRegenerationEndpoint Δ lam R i z).1,
          translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1) ∧
      sbxS9RecenteredCoupledLaws (K j) (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
          (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1) =
        sbxS9RecenteredCoupledLaws (L j) (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
          (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1 z.1) := by
  have hg := (sbxS9_weightedRestriction_ac μ s w).ae_le
    (sbxS9_firstRegeneration_ae_all_endpoint_versions_eq Q hQ Δ lam R i μ hac K L hKL)
  filter_upwards [hg] with z hz j
  refine ⟨(hz j).1, (hz j).2, ?_⟩
  change sbxS9RecenteredCoupledLaws (K j) (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
      (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
        (sbxS9FirstRegenerationEndpoint Δ lam R i z).2) =
    sbxS9RecenteredCoupledLaws (L j) (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
      (0, translate (sbxS9FirstRegenerationEndpoint Δ lam R i z).1
        (sbxS9FirstRegenerationEndpoint Δ lam R i z).2)
  rw [sbxS9_recenteredCoupledLaws_endpoint_origin (K j)
      (sbxS9FirstRegenerationEndpoint Δ lam R i z),
    sbxS9_recenteredCoupledLaws_endpoint_origin (L j)
      (sbxS9FirstRegenerationEndpoint Δ lam R i z), (hz j).1]

/-- The measurable finite restart kernel at the actual first endpoint.
Its probability part will be removed only on the established good fibres. -/
def sbxS9FirstRegenerationRestartKernel {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) : Kernel (FieldPair d × CoupledSample d) (CoupledSample d) :=
  (Probability.probabilityPart K).comap (sbxS9FirstRegenerationEndpoint Δ lam R i)
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i)

instance sbxS9FirstRegenerationRestartKernel_isFinite {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d) :
    IsFiniteKernel (sbxS9FirstRegenerationRestartKernel Δ lam R i K) :=
  inferInstanceAs (IsFiniteKernel ((Probability.probabilityPart K).comap _ _))

/-- The actual first restart kernel agrees with its supplied raw fibre
wherever that fibre has been proved to be a probability. -/
theorem sbxS9_firstRegeneration_restart_eq_raw {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d)
    (z : FieldPair d × CoupledSample d)
    (hp : IsProbabilityMeasure (K (sbxS9FirstRegenerationEndpoint Δ lam R i z))) :
    sbxS9FirstRegenerationRestartKernel Δ lam R i K z =
      K (sbxS9FirstRegenerationEndpoint Δ lam R i z) := by
  let := hp
  exact Probability.probabilityPart_eq_of_isProbabilityMeasure K _

/-- The infinite-time branch remains the original time-zero endpoint;
normalization does not invent an endpoint density there. -/
theorem sbxS9_firstRegeneration_restart_eq_at_infinite {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d)
    (z : FieldPair d × CoupledSample d)
    (ht : firstRegenerationTime Δ lam R z.2 i = ⊤) :
    sbxS9FirstRegenerationRestartKernel Δ lam R i K z =
      Probability.probabilityPart K (z.2.1 0, z.1) := by
  change Probability.probabilityPart K (sbxS9FirstRegenerationEndpoint Δ lam R i z) = _
  rw [sbxS9_firstRegenerationEndpoint_eq_on_infinite Δ lam R i z ht]

/-- Actual endpoint AC yields equality of the full probability-part joint
laws before signed finite-record transport. -/
theorem sbxS9_firstRegeneration_restart_compProd_eq {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d)) (K L : CoupledQuenchedLaws d)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K =
      μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i L := by
  apply Measure.compProd_congr
  filter_upwards [sbxS9_ae_kernel_eq_at_joint_endpoint Q μ _
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).aemeasurable hac K L hKL]
    with z hz
  change Probability.probabilityPart K _ = Probability.probabilityPart L _
  simp only [Probability.probabilityPart_apply, hz]

/-- Signed integrable finite-record observations at the literal first
regeneration endpoint have integrable nested expectations under both versions. -/
theorem sbxS9_integrable_firstRegeneration_restart_records {d : ℕ}
    (hd : 2 ≤ d) (lam l : ℝ) (Δ : ℝ≥0) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (K L : CoupledQuenchedLaws d)
    (hac : μ.map (sbxS9FirstRegenerationEndpoint Δ lam (l / lam)
      (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p)
    (n : ℕ) (ks : Fin n → ℕ)
    (Φ : (FieldPair d × CoupledSample d) × FieldPair d ×
      (Fin n → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ)
    (hΦ : Measurable Φ)
    (hi : Integrable Φ ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam (l / lam)
      (Renewal.forceCoord hd) K).map (sbxS9RestartRecordsMap hd lam l
        (sbxS9FirstRegenerationEndpoint Δ lam (l / lam) (Renewal.forceCoord hd)) n ks))) :
    let F := sbxS9RestartRecordsMap hd lam l
      (sbxS9FirstRegenerationEndpoint Δ lam (l / lam) (Renewal.forceCoord hd)) n ks
    let κ := sbxS9FirstRegenerationRestartKernel Δ lam (l / lam) (Renewal.forceCoord hd)
    Integrable Φ ((μ ⊗ₘ κ L).map F) ∧
      Integrable (fun z => ∫ z', Φ (F (z, z')) ∂κ K z) μ ∧
      Integrable (fun z => ∫ z', Φ (F (z, z')) ∂κ L z) μ ∧
      (∫ z, ∫ z', Φ (F (z, z')) ∂κ K z ∂μ) = ∫ z, ∫ z', Φ (F (z, z')) ∂κ L z ∂μ := by
  let F := sbxS9RestartRecordsMap hd lam l
    (sbxS9FirstRegenerationEndpoint Δ lam (l / lam) (Renewal.forceCoord hd)) n ks
  have hF : Measurable F := sbxS9_measurable_restartRecordsMap hd lam l _
    (sbxS9_measurable_firstRegenerationEndpoint _ _ _ _) n ks
  let κ := sbxS9FirstRegenerationRestartKernel Δ lam (l / lam) (Renewal.forceCoord hd)
  have hlaw := congrArg (fun ν => ν.map F)
    (sbxS9_firstRegeneration_restart_compProd_eq Δ lam (l / lam)
      (Renewal.forceCoord hd) Q μ K L hac hKL)
  obtain ⟨hj, hiK, hiL⟩ :=
    sbxS9_integrable_joint_observation_transport μ (κ K) (κ L) F hF hlaw Φ hΦ hi
  exact ⟨hj, sbxS9_integrable_joint_nested_test μ _ _ hiK,
    sbxS9_integrable_joint_nested_test μ _ _ hiL,
    sbxS9_integral_joint_observation_transport μ _ _ F hF hlaw Φ hΦ hi⟩

/-- Genuine endpoint probability fibres remove the fallback also for signed
unbounded joint tests, after their integrability has been proved. -/
theorem sbxS9_integrable_firstRegeneration_raw_nested_test {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ] (K : CoupledQuenchedLaws d)
    (hp : ∀ᵐ z ∂μ, IsProbabilityMeasure (K (sbxS9FirstRegenerationEndpoint Δ lam R i z)))
    (f : (FieldPair d × CoupledSample d) × CoupledSample d → ℝ)
    (hf : Integrable f (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K)) :
    Integrable (fun z => ∫ z', f (z, z') ∂K (sbxS9FirstRegenerationEndpoint Δ lam R i z)) μ := by
  apply (sbxS9_integrable_joint_nested_test μ _ f hf).congr
  filter_upwards [hp] with z hz
  rw [sbxS9_firstRegeneration_restart_eq_raw Δ lam R i K z hz]

/-- Exact scope plus an integrable nonnegative density and a bounded
nonnegative environment weight gives a finite no-return endpoint law. The
joint reference AC holds both before and after translating the environment. -/
theorem sbxS9_weighted_noReturn_endpoint_control_of_scope
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d))))
    (w : FieldPair d × CoupledSample d → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ z ∂μ, 0 ≤ w z) (B : FieldPair d → ℝ) (hB : Measurable B)
    (hbB : BoundedRealTest B) (hB0 : ∀ ω, 0 ≤ B ω) :
    let ν := sbxS9WeightedRestriction μ (regenerationNoReturn hd (l / lam))
      (fun z => w z * B z.1)
    let e := sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd)
    IsFiniteMeasure ν ∧ IsFiniteMeasure (ν.map e) ∧
      AEMeasurable (fun z => ENNReal.ofReal (w z * B z.1))
        (μ.restrict (regenerationNoReturn hd (l / lam))) ∧
      ν.map e ≪ (volume : Measure (Vec d)).prod Q.measure ∧
      ν.map (fun z => ((e z).1, translate (e z).1 z.1)) ≪
        (volume : Measure (Vec d)).prod Q.measure := by
  let ν := sbxS9WeightedRestriction μ (regenerationNoReturn hd (l / lam))
    (fun z => w z * B z.1)
  let e := sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
    (Renewal.forceCoord hd)
  have hfinite : IsFiniteMeasure ν :=
    sbxS9_weighted_noReturn_isFinite hd (l / lam) μ w hw hw0 B hB hbB hB0
  let := hfinite
  have hac := sbxS9_weighted_firstRegeneration_endpoint_law_ac
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) Q.measure μ
    (regenerationNoReturn hd (l / lam)) (fun z => w z * B z.1)
    (sbxS9_firstRegeneration_endpoint_law_ac_of_scope hscope hd Q lam h0 h1
      l δ hl hsep hδ0 hδ1 P K hK hD μ hμ)
  exact ⟨hfinite, inferInstance,
    sbxS9_weightedRestriction_density_aemeasurable μ _ _
      (sbxS9_integrable_density_mul_environment μ w hw B hB hbB), hac,
    sbxS9_recentered_firstRegeneration_endpoint_law_ac Q.measure Q.stationary
      _ _ _ _ ν hac⟩

/-- Under either original scope law, weighted signed finite-record tests
have integrable raw nested expectations in both legitimate versions. The
joint integrability transfer occurs before normalization is removed. -/
theorem sbxS9_weighted_firstRegeneration_integrable_records_of_scope
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d))))
    (s : Set (FieldPair d × CoupledSample d))
    (w : FieldPair d × CoupledSample d → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ z ∂μ, 0 ≤ w z)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (n : ℕ) (ks : Fin n → ℕ)
    (Φ : (FieldPair d × CoupledSample d) × FieldPair d ×
      (Fin n → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ)
    (hΦ : Measurable Φ)
    (hi : Integrable Φ (((sbxS9WeightedRestriction μ s w) ⊗ₘ
      sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) K).map (sbxS9RestartRecordsMap hd lam l
          (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
            (Renewal.forceCoord hd)) n ks))) :
    let ν := sbxS9WeightedRestriction μ s w
    let e := sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd)
    let F := sbxS9RestartRecordsMap hd lam l e n ks
    Integrable Φ ((ν ⊗ₘ sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam)
      lam (l / lam) (Renewal.forceCoord hd) L).map F) ∧
      Integrable (fun z => ∫ z', Φ (F (z, z')) ∂K (e z)) ν ∧
      Integrable (fun z => ∫ z', Φ (F (z, z')) ∂L (e z)) ν ∧
      (∫ z, ∫ z', Φ (F (z, z')) ∂K (e z) ∂ν) =
        ∫ z, ∫ z', Φ (F (z, z')) ∂L (e z) ∂ν := by
  let ν := sbxS9WeightedRestriction μ s w
  let : IsFiniteMeasure ν := sbxS9_weightedRestriction_isFinite μ s w hw hw0
  let e := sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam (l / lam)
    (Renewal.forceCoord hd)
  let F := sbxS9RestartRecordsMap hd lam l e n ks
  let κ := sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam) lam (l / lam)
    (Renewal.forceCoord hd)
  have hac := sbxS9_weighted_firstRegeneration_endpoint_law_ac
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) Q.measure μ s w
    (sbxS9_firstRegeneration_endpoint_law_ac_of_scope hscope hd Q lam h0 h1
      l δ hl hsep hδ0 hδ1 P K hK hD μ hμ)
  obtain ⟨hj, hiK, hiL, heq⟩ := sbxS9_integrable_firstRegeneration_restart_records
    hd lam l (Renewal.regenDelta lam) Q.measure ν K L hac hKL n ks Φ hΦ hi
  have hprobK := sbxS9_firstRegeneration_probability_fibres (Renewal.regenDelta lam)
    lam (l / lam) (Renewal.forceCoord hd) Q.measure ν K hac hK.1.2
  have hprobL := sbxS9_firstRegeneration_probability_fibres (Renewal.regenDelta lam)
    lam (l / lam) (Renewal.forceCoord hd) Q.measure ν L hac (by
      filter_upwards [hK.1.2, hKL] with p hp he
      rw [← he]
      exact hp)
  have hsameK : (fun z => ∫ z', Φ (F (z, z')) ∂κ K z) =ᵐ[ν]
      (fun z => ∫ z', Φ (F (z, z')) ∂K (e z)) := by
    filter_upwards [hprobK] with z hz
    rw [sbxS9_firstRegeneration_restart_eq_raw _ _ _ _ K z hz]
  have hsameL : (fun z => ∫ z', Φ (F (z, z')) ∂κ L z) =ᵐ[ν]
      (fun z => ∫ z', Φ (F (z, z')) ∂L (e z)) := by
    filter_upwards [hprobL] with z hz
    rw [sbxS9_firstRegeneration_restart_eq_raw _ _ _ _ L z hz]
  exact ⟨hj, hiK.congr hsameK, hiL.congr hsameL,
    (integral_congr_ae hsameK).symm.trans (heq.trans (integral_congr_ae hsameL))⟩

#print axioms sbxS9WeightedRestriction
#print axioms sbxS9_weightedRestriction_ac
#print axioms sbxS9_weightedRestriction_isFinite
#print axioms sbxS9_weightedRestriction_density_aemeasurable
#print axioms sbxS9_integrable_weightedRestriction_iff
#print axioms sbxS9_integral_weightedRestriction
#print axioms sbxS9_weighted_endpoint_law_ac
#print axioms sbxS9_integrable_density_mul_environment
#print axioms sbxS9_weighted_noReturn_isFinite
#print axioms sbxS9_weighted_firstRegeneration_endpoint_law_ac
#print axioms sbxS9_weighted_recentered_firstRegeneration_endpoint_law_ac
#print axioms sbxS9_map_compProd_eq_bind
#print axioms sbxS9_integrable_joint_observation_transport
#print axioms sbxS9_integrable_joint_nested_test
#print axioms sbxS9_integral_joint_observation_transport
#print axioms sbxS9RestartRecordsMap
#print axioms sbxS9_measurable_restartRecordsMap
#print axioms sbxS9_selected_restart_compProd_eq
#print axioms sbxS9_integrable_selected_restart_records
#print axioms sbxS9_integrable_selected_raw_nested_test
#print axioms sbxS9_hasSum_integrable_selected_raw_nested_test
#print axioms sbxS9_weighted_ae_all_restart_fibres_eq_of_coupling
#print axioms sbxS9_weighted_firstRegeneration_ae_all_versions_eq
#print axioms sbxS9FirstRegenerationRestartKernel
#print axioms sbxS9FirstRegenerationRestartKernel_isFinite
#print axioms sbxS9_firstRegeneration_restart_eq_raw
#print axioms sbxS9_firstRegeneration_restart_eq_at_infinite
#print axioms sbxS9_firstRegeneration_restart_compProd_eq
#print axioms sbxS9_integrable_firstRegeneration_restart_records
#print axioms sbxS9_integrable_firstRegeneration_raw_nested_test
#print axioms sbxS9_weighted_noReturn_endpoint_control_of_scope
#print axioms sbxS9_weighted_firstRegeneration_integrable_records_of_scope

#print axioms sbxS9_firstRegeneration_nested_integral_recentered_origin
#print axioms sbxS9_firstRegeneration_mixed_record_integral_recentered_origin

#print axioms sbxS9_firstRegenerationTime_ne_zero
#print axioms sbxS9_recentered_firstRegeneration_endpoint_law_ac_of_scope
#print axioms sbxS9_firstRegeneration_joint_records_eq_of_scope
#print axioms sbxS9_firstRegeneration_mixed_record_integral_eq_of_scope

#print axioms sbxS9_firstRegeneration_endpoint_law_ac_of_scope
#print axioms sbxS9_firstRegeneration_probability_fibres
#print axioms sbxS9_firstRegeneration_recentered_origin_versions_eq
#print axioms sbxS9_measurable_firstRegeneration_joint_restart_records
#print axioms sbxS9_firstRegeneration_restart_observation_law_eq
#print axioms sbxS9_firstRegeneration_nested_restart_integral_eq
#print axioms sbxS9_firstRegeneration_joint_restart_records_law_eq
#print axioms sbxS9_integrable_firstRegeneration_nested_restart_test

#print axioms sbxS9_grid_joint_endpoint_law_ac_of_coupling
#print axioms sbxS9_finite_firstRegeneration_endpoint_law_ac_of_coupling
#print axioms sbxS9_firstRegeneration_endpoint_law_ac_of_coupling_and_ae_finite
#print axioms sbxS9_firstRegeneration_endpoint_law_ac_of_coupling_and_tail
#print axioms sbxS9_conditioned_firstRegeneration_endpoint_law_ac_of_tail
#print axioms sbxS9_recentered_firstRegeneration_endpoint_law_ac
#print axioms sbxS9_firstRegeneration_ae_all_endpoint_versions_eq

#print axioms sbxS9_restricted_endpoint_law_ac
#print axioms sbxS9_map_countable_slices
#print axioms sbxS9FirstRegenerationEndpoint
#print axioms sbxS9_measurable_firstRegenerationEndpoint
#print axioms sbxS9FirstRegenerationSlice
#print axioms sbxS9_measurableSet_firstRegenerationSlice
#print axioms sbxS9_firstRegenerationSlice_pairwise_disjoint
#print axioms sbxS9_firstRegeneration_finite_eq_iUnion
#print axioms sbxS9_firstRegenerationEndpoint_eq_on_slice
#print axioms sbxS9_firstRegenerationEndpoint_eq_on_infinite
#print axioms sbxS9_finite_firstRegeneration_endpoint_law_eq_sum
#print axioms sbxS9_finite_firstRegeneration_endpoint_law_ac
#print axioms sbxS9_firstRegeneration_endpoint_law_ac_of_ae_finite

#print axioms sbxS9_selected_restart_eq_raw
#print axioms sbxS9_aemeasurable_selected_raw_restart_law
#print axioms sbxS9_selected_restart_observation_law_eq_raw
#print axioms sbxS9_hasSum_selected_nested_restart_test

#print axioms sbxS9_selected_recentered_origin_restart_fibres_eq
#print axioms sbxS9_measurable_selected_joint_restart_records
#print axioms sbxS9_selected_joint_restart_records_law_eq
#print axioms sbxS9_selected_mixed_restart_record_integral_eq
#print axioms sbxS9_firstRestart_versions_eq_of_coupling
#print axioms sbxS9_first_regeneration_endpoint_versions_eq_of_tail
#print axioms sbxS9_conditioned_selected_restart_fibres_eq

#print axioms sbxS9SelectedRestartKernel
#print axioms sbxS9_selected_restart_mass_le_one
#print axioms sbxS9SelectedRestartKernel_isFinite
#print axioms sbxS9_measurable_selected_nested_restart_test
#print axioms sbxS9_integrable_selected_nested_restart_test
#print axioms sbxS9_hasSum_integral_countable_select
#print axioms sbxS9_integral_countable_select_eq_tsum
#print axioms sbxS9FirstRestartIndex
#print axioms sbxS9_measurable_firstRestartIndex
#print axioms sbxS9_firstRestartIndex_eq_of_slice
#print axioms sbxS9_firstRestartIndex_eq_zero_of_infinite
#print axioms sbxS9_firstRestartIndex_recovers_time
#print axioms sbxS9_measurable_firstRestart_selection_event

#print axioms sbxS9_ae_countable_select
#print axioms sbxS9_measurable_countable_select
#print axioms sbxS9_selected_kernel_eq_of_branch_joint_ac
#print axioms sbxS9_selected_kernel_eq_of_origin_and_branch_joint_ac
#print axioms sbxS9_annealed_ae_all_indexed_restart_fibres_eq
#print axioms sbxS9_selected_restart_fibres_eq
#print axioms sbxS9_measurable_selected_restart_law
#print axioms sbxS9_selected_nested_restart_integral_eq
#print axioms sbxS9_selected_joint_restart_law_eq

#print axioms sbxS9_recenterInput_endpoint_origin
#print axioms sbxS9_recenteredCoupledLaws_endpoint_origin
#print axioms sbxS9_recenteredPathLaws_endpoint_origin
#print axioms sbxS9_recenteredCoupledLaws_finite_observations
#print axioms sbxS9_measurable_joint_probabilityPart_recenteredPathLaws
#print axioms sbxS9_measurable_joint_probabilityPart_recenteredCoupledLaws
#print axioms sbxS9_probabilityPart_recenteredCoupledLaws_eq
#print axioms sbxS9_ae_all_recentered_origin_restart_fibres_eq
#print axioms sbxS9_annealed_ae_all_restart_fibres_eq_of_coupling
#print axioms sbxS9_measurable_recentered_restart_record_laws
#print axioms sbxS9_recentered_restart_record_mixture_eq
#print axioms sbxS9_conditioned_recentered_restart_record_mixture_eq

#print axioms sbxS9_quasiMeasurePreserving_compProd_fst
#print axioms sbxS9_annealed_start_at_zero
#print axioms sbxS9_annealed_joint_endpoint_law_ac
#print axioms sbxS9_ae_kernel_eq_at_joint_endpoint
#print axioms sbxS9_ae_kernel_eq_at_recentered_joint_endpoint
#print axioms sbxS9_annealed_ae_all_restart_fibres_eq
#print axioms sbxS9_nested_integral_eq_of_annealed_restart_fibres
#print axioms sbxS9_conditioned_ae_all_restart_fibres_eq
#print axioms sbxS9_conditioned_nested_integral_eq_of_restart_fibres

#print axioms sbxS9_measurable_joint_recenterInput
#print axioms sbxS9_measurable_joint_recenterPath
#print axioms sbxS9_measurable_joint_recenterSample
#print axioms sbxS9_measurable_parameter_map
#print axioms sbxS9_measurable_joint_recenteredPathLaws
#print axioms sbxS9_measurable_joint_recenteredCoupledLaws
#print axioms sbxS9_measurable_joint_recenteredPathLaws_integral
#print axioms sbxS9_measurable_joint_recenteredCoupledLaws_integral
#print axioms sbxS9_measurePreserving_endpoint_recenterEnvironment
#print axioms sbxS9_joint_endpoint_law_ac
#print axioms sbxS9_joint_recentered_endpoint_law_ac

#print axioms sbxS9RecenterInputEquiv_apply
#print axioms sbxS9_recenteredPathLaws_add_eq_of_product_ae_eq
#print axioms sbxS9_recenteredCoupledLaws_add_eq_of_product_ae_eq
#print axioms sbxS9_countable_recentered_coupling_laws_eq_of_path_laws_eq
#print axioms sbxS9_countable_hasProbabilityLaws_recenter
#print axioms sbxS9_countable_finite_histories_eq_of_product_ae_eq
#print axioms sbxS9_countable_annealed_joint_records_eq_of_product_ae_eq
#print axioms sbxS9_countable_conditioned_joint_records_eq_of_product_ae_eq
#print axioms sbxS9_recenterInput_zero
#print axioms sbxS9_recenterInput_add
#print axioms sbxS9_recenterInput_neg
#print axioms sbxS9RecenterInputEquiv
#print axioms sbxS9_recenterPathEquiv_zero
#print axioms sbxS9_recenterPathEquiv_add
#print axioms sbxS9_recenterPathEquiv_neg
#print axioms sbxS9_recenterSampleEquiv_zero
#print axioms sbxS9_recenterSampleEquiv_add
#print axioms sbxS9_recenterSampleEquiv_neg
#print axioms sbxS9_recenteredPathLaws_zero
#print axioms sbxS9_recenteredPathLaws_add
#print axioms sbxS9_recenteredPathLaws_neg
#print axioms sbxS9_recenteredCoupledLaws_zero
#print axioms sbxS9_recenteredCoupledLaws_add
#print axioms sbxS9_recenteredCoupledLaws_neg
#print axioms sbxS9_ae_recenterInput_add
#print axioms sbxS9_ae_countable_recenterInput
#print axioms sbxS9_countable_recenteredPathLaws_eq_of_product_ae_eq
#print axioms sbxS9_countable_recenteredCoupledLaws_eq_of_product_ae_eq

#print axioms sbxS9_recentered_coupling_laws_eq_of_path_laws_eq
#print axioms sbxS9_hasOneIntervalKernel_recenter
#print axioms sbxS9_six_coupling_clauses_recenter
#print axioms sbxS9_killedSegmentLaw_recenter
#print axioms sbxS9_killedEndpointLaw_recenter
#print axioms sbxS9_killedEndpointDensity_recenter
#print axioms sbxS9_map_cond_equiv
#print axioms sbxS9_killedBridgeMixture_recenter
#print axioms sbxS9_oneIntervalKernelAt_recenter

#print axioms sbxS9_coupling_laws_eq_of_prescribed_split_clauses
#print axioms sbxS9_averaged_killed_future_means_eq_of_prescribed_split_clauses
#print axioms sbxS9_finite_histories_eq_of_one_regular_path_law
#print axioms sbxS9_coupled_law_eq_of_one_regular_path_law
#print axioms sbxS9_first_history_eq_of_path_fibre_eq
#print axioms sbxS9_finite_histories_eq_of_path_laws_eq
#print axioms sbxS9_coupled_law_eq_of_regular_path_laws_eq
#print axioms sbxS9_coupling_laws_eq_of_path_laws_eq
#print axioms sbxS9_coupling_laws_eq_of_same_path_kernel
#print axioms sbxS9_killed_future_means_eq_of_path_laws_eq
#print axioms sbxS9_averaged_killed_future_means_eq_of_path_laws_eq

#print axioms sbxS9RecenterInput
#print axioms sbxS9_measurable_recenterInput
#print axioms sbxS9RecenteredPathLaws
#print axioms sbxS9RecenteredCoupledLaws
#print axioms sbxS9RecenteredPathLaws_apply
#print axioms sbxS9RecenteredCoupledLaws_apply
#print axioms sbxS9_measurePreserving_recenterInput
#print axioms sbxS9_ae_recenterInput
#print axioms sbxS9_probability_recenter
#print axioms sbxS9_pathMarginal_recenter
#print axioms sbxS9_freshBitsAt_recenter
#print axioms sbxS9_deterministicRestartAt_recenter
#print axioms sbxS9_successfulBridgeSupportAt_recenter
#print axioms sbxS9_hasProbabilityLaws_recenter
#print axioms sbxS9_hasPathMarginals_recenter
#print axioms sbxS9_hasFreshBits_recenter
#print axioms sbxS9_hasDeterministicRestart_recenter
#print axioms sbxS9_hasSuccessfulBridgeSupport_recenter
#print axioms sbxS9_five_coupling_clauses_recenter

#print axioms sbxS9_annealedCoupledLaw_eq_of_origin_ae_eq
#print axioms sbxS9_noReturn_mass_eq_of_origin_ae_eq
#print axioms sbxS9_noReturn_ne_zero_of_origin_ae_eq
#print axioms sbxS9_regenerationConditionedLaw_eq_of_origin_ae_eq
#print axioms sbxS9_annealed_record_law_eq_of_origin_ae_eq
#print axioms sbxS9_annealed_joint_records_law_eq_of_origin_ae_eq
#print axioms sbxS9_conditioned_record_law_eq_of_origin_ae_eq
#print axioms sbxS9_conditioned_joint_records_law_eq_of_origin_ae_eq
#print axioms sbxS9_annealed_mixed_record_integral_eq_of_origin_ae_eq
#print axioms sbxS9_conditioned_mixed_record_integral_eq_of_origin_ae_eq

#print axioms sbxS9_annealed_law_eq_of_split_clauses_and_path_laws_eq
#print axioms sbxS9_conditioned_law_eq_of_split_clauses_and_path_laws_eq

#print axioms sbxS9_annealed_records_law_eq_of_origin_ae_eq
#print axioms sbxS9_conditioned_records_law_eq_of_origin_ae_eq

#print axioms sbxS9_hasProbabilityLaws_of_origin_product_ae_eq
#print axioms sbxS9_hasPathMarginals_of_origin_product_ae_eq
#print axioms sbxS9_hasFreshBits_of_origin_product_ae_eq
#print axioms sbxS9_hasSuccessfulBridgeSupport_of_origin_product_ae_eq
#print axioms sbxS9_hasUniformSuccessfulEndpoint_of_origin_product_ae_eq
#print axioms sbxS9_hasOneIntervalKernel_of_origin_product_ae_eq
#print axioms sbxS9_ae_restart_fibres_eq_of_start_and_endpoint_ac
#print axioms sbxS9_nested_restart_integral_eq_of_start_and_endpoint_ac
#print axioms sbxS9_deterministicRestartAt_of_eq_and_path_endpoint_ac
#print axioms sbxS9_hasDeterministicRestart_of_origin_product_ae_eq
#print axioms sbxS9_isRegenerationCoupling_of_origin_product_ae_eq
#print axioms sbxS9_conditioned_records_of_coupling_version


/-- The second endpoint uses the original environment and the first restart
sample, retaining the complete original sample in the domain. -/
def sbxS9SecondRestartEndpoint {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (z : (FieldPair d × CoupledSample d) × CoupledSample d) : Vec d × FieldPair d :=
  sbxS9FirstRegenerationEndpoint Δ lam R i (z.1.1, z.2)

theorem sbxS9_measurable_secondRestartEndpoint {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) : Measurable (sbxS9SecondRestartEndpoint Δ lam R i) :=
  (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

/-- A second measurable restart at the literal endpoint of the first restart. -/
def sbxS9SecondRestartKernel {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) :
    Kernel ((FieldPair d × CoupledSample d) × CoupledSample d) (CoupledSample d) :=
  (Probability.probabilityPart K).comap (sbxS9SecondRestartEndpoint Δ lam R i)
    (sbxS9_measurable_secondRestartEndpoint Δ lam R i)

instance sbxS9SecondRestartKernel_isFinite {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (K : CoupledQuenchedLaws d) :
    IsFiniteKernel (sbxS9SecondRestartKernel Δ lam R i K) :=
  inferInstanceAs (IsFiniteKernel ((Probability.probabilityPart K).comap _ _))

/-- The normalized second restart is the supplied law on probability fibres. -/
theorem sbxS9_secondRestart_eq_raw {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (K : CoupledQuenchedLaws d)
    (z : (FieldPair d × CoupledSample d) × CoupledSample d)
    (hp : IsProbabilityMeasure (K (sbxS9SecondRestartEndpoint Δ lam R i z))) :
    sbxS9SecondRestartKernel Δ lam R i K z =
      K (sbxS9SecondRestartEndpoint Δ lam R i z) := by
  let := hp
  exact Probability.probabilityPart_eq_of_isProbabilityMeasure K _

/-- Fubini transports almost-everywhere fibrewise endpoint absolute
continuity to the actual joint endpoint law. -/
theorem sbxS9_joint_endpoint_ac_of_fibre_ac {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (F : α × β → γ) (hF : Measurable F) (ν : Measure γ)
    (h : ∀ᵐ z ∂μ, (κ z).map (fun z' => F (z, z')) ≪ ν) :
    (μ ⊗ₘ κ).map F ≪ ν := by
  rw [sbxS9_map_compProd_eq_bind μ κ F hF]
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hν
  rw [Measure.bind_apply hs (sbxS9_measurable_parameter_map κ _ hF).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [h] with z hz
  exact hz hν

/-- Endpoint absolute continuity transports the second supplied kernel version
on the complete first-stage joint law. -/
theorem sbxS9_secondRestart_compProd_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (Q : Measure (FieldPair d))
    (ν : Measure ((FieldPair d × CoupledSample d) × CoupledSample d))
    (K L : CoupledQuenchedLaws d)
    (hac : ν.map (sbxS9SecondRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    ν ⊗ₘ sbxS9SecondRestartKernel Δ lam R i K =
      ν ⊗ₘ sbxS9SecondRestartKernel Δ lam R i L := by
  apply Measure.compProd_congr
  filter_upwards [ae_of_ae_map
    (sbxS9_measurable_secondRestartEndpoint Δ lam R i).aemeasurable (hac.ae_le hKL)]
    with z hz
  change Probability.probabilityPart K _ = Probability.probabilityPart L _
  simp only [Probability.probabilityPart_apply, hz]

/-- Both restart versions have the same full two-stage joint law, provided
both actual endpoint laws have the required absolute continuity. -/
theorem sbxS9_twoRestart_joint_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d)) (K L : CoupledQuenchedLaws d)
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hac₂ : (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K).map
      (sbxS9SecondRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K) ⊗ₘ
        sbxS9SecondRestartKernel Δ lam R i K =
      (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i L) ⊗ₘ
        sbxS9SecondRestartKernel Δ lam R i L := by
  rw [sbxS9_secondRestart_compProd_eq Δ lam R i Q _ K L hac₂ hKL,
    sbxS9_firstRegeneration_restart_compProd_eq Δ lam R i Q μ K L hac₁ hKL]


/-- The complete two-stage sample together with both endpoint-translated
environments. Both path and coin records remain in the retained sample. -/
def sbxS9TwoRestartRecordsMap {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (z : ((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d) :=
  (z, (translate (sbxS9FirstRegenerationEndpoint Δ lam R i z.1.1).1 z.1.1.1,
    translate (sbxS9SecondRestartEndpoint Δ lam R i z.1).1 z.1.1.1))

theorem sbxS9_measurable_twoRestartRecordsMap {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) : Measurable (sbxS9TwoRestartRecordsMap Δ lam R i) := by
  have hω : Measurable (fun z : ((FieldPair d × CoupledSample d) × CoupledSample d) ×
      CoupledSample d => z.1.1.1) := measurable_fst.fst.fst
  have h₁ : Measurable (fun z : ((FieldPair d × CoupledSample d) × CoupledSample d) ×
      CoupledSample d => sbxS9FirstRegenerationEndpoint Δ lam R i z.1.1) :=
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).comp measurable_fst.fst
  have h₂ : Measurable (fun z : ((FieldPair d × CoupledSample d) × CoupledSample d) ×
      CoupledSample d => sbxS9SecondRestartEndpoint Δ lam R i z.1) :=
    (sbxS9_measurable_secondRestartEndpoint Δ lam R i).comp measurable_fst
  exact measurable_id.prodMk ((Probability.continuous_translate.measurable.comp
    (h₁.fst.prodMk hω)).prodMk (Probability.continuous_translate.measurable.comp
      (h₂.fst.prodMk hω)))

/-- Signed observations of any measurable complete two-stage record transfer
across the equal full joint laws after integrability is established. -/
theorem sbxS9_twoRestart_integrable_record_transport {d : ℕ} {γ : Type*}
    [MeasurableSpace γ] (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d)) (μ : Measure (FieldPair d × CoupledSample d))
    (K L : CoupledQuenchedLaws d)
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hac₂ : (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K).map
      (sbxS9SecondRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p)
    (F : ((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d → γ)
    (Φ : γ → ℝ)
    (hi : Integrable Φ (((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i K).map F)) :
    Integrable Φ (((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i L) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i L).map F) := by
  rw [← sbxS9_twoRestart_joint_eq Δ lam R i Q μ K L hac₁ hac₂ hKL]
  exact hi

#print axioms sbxS9SecondRestartEndpoint
#print axioms sbxS9_measurable_secondRestartEndpoint
#print axioms sbxS9SecondRestartKernel
#print axioms sbxS9SecondRestartKernel_isFinite
#print axioms sbxS9_secondRestart_eq_raw
#print axioms sbxS9_joint_endpoint_ac_of_fibre_ac
#print axioms sbxS9_secondRestart_compProd_eq
#print axioms sbxS9_twoRestart_joint_eq
#print axioms sbxS9TwoRestartRecordsMap
#print axioms sbxS9_measurable_twoRestartRecordsMap
#print axioms sbxS9_twoRestart_integrable_record_transport


/-- A spatially absolutely continuous endpoint on almost every restart
fibre yields a joint endpoint/environment density when the outer environment
marginal is dominated by the reference environment law. -/
theorem sbxS9_joint_endpoint_ac_of_spatial_fibre_ac {d : ℕ} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (Q : Measure (FieldPair d)) [SFinite Q]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (e : α → FieldPair d) (he : Measurable e)
    (f : α × β → Vec d) (hf : Measurable f)
    (hμ : μ.map e ≪ Q)
    (hdensity : ∀ᵐ z ∂μ, (κ z).map (fun b => f (z, b)) ≪
      (volume : Measure (Vec d))) :
    (μ ⊗ₘ κ).map (fun z => (f z, e z.1)) ≪
      (volume : Measure (Vec d)).prod Q := by
  let F : α × β → Vec d × FieldPair d := fun z => (f z, e z.1)
  have hF : Measurable F := hf.prodMk (he.comp measurable_fst)
  change (μ ⊗ₘ κ).map F ≪ _
  rw [sbxS9_map_compProd_eq_bind μ κ F hF]
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  have hswap : (Q.prod (volume : Measure (Vec d))) (Prod.swap ⁻¹' s) = 0 := by
    rw [← Measure.map_apply measurable_swap hs, Measure.prod_swap]
    exact hs0
  have hsection : ∀ᵐ ω ∂Q, (volume : Measure (Vec d))
      ((fun x => (x, ω)) ⁻¹' s) = 0 := by
    filter_upwards [Measure.measure_ae_null_of_prod_null hswap] with ω hω
    simpa only [Set.preimage_preimage, Function.comp_def, Prod.swap_prod_mk, Pi.zero_apply] using hω
  have houter : ∀ᵐ z ∂μ, (volume : Measure (Vec d))
      ((fun x => (x, e z)) ⁻¹' s) = 0 :=
    ae_of_ae_map he.aemeasurable (hμ.ae_le hsection)
  rw [Measure.bind_apply hs (sbxS9_measurable_parameter_map κ _ hF).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [houter, hdensity] with z hz hdz
  change (Measure.map (F ∘ Prod.mk z) (κ z)) s = 0
  rw [Measure.map_apply (hF.comp measurable_prodMk_left) hs]
  have hm := hdz hz
  change (Measure.map (f ∘ Prod.mk z) (κ z)) ((fun x => (x, e z)) ⁻¹' s) = 0 at hm
  rw [Measure.map_apply (hf.comp measurable_prodMk_left)
    (measurable_prodMk_right hs)] at hm
  exact hm


/-- First endpoint joint AC supplies the environmental marginal for the
second endpoint. Spatial density is required only on the actual restart fibres. -/
theorem sbxS9_secondRestart_endpoint_ac_of_spatial_fibre_ac {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d)) [SFinite Q]
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (K : CoupledQuenchedLaws d)
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hdensity : ∀ᵐ z ∂μ,
      (sbxS9FirstRegenerationRestartKernel Δ lam R i K z).map
        (fun b => (sbxS9FirstRegenerationEndpoint Δ lam R i (z.1, b)).1) ≪
          (volume : Measure (Vec d))) :
    (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K).map
      (sbxS9SecondRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q := by
  have henv : μ.map Prod.fst ≪ Q := by
    have h := (hac₁.map measurable_snd).trans
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d)))
        (ν := Q)).absolutelyContinuous
    rw [Measure.map_map measurable_snd
      (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i)] at h
    exact h
  have hf : Measurable (fun z : (FieldPair d × CoupledSample d) × CoupledSample d =>
      (sbxS9SecondRestartEndpoint Δ lam R i z).1) :=
    (sbxS9_measurable_secondRestartEndpoint Δ lam R i).fst
  exact sbxS9_joint_endpoint_ac_of_spatial_fibre_ac Q μ
    (sbxS9FirstRegenerationRestartKernel Δ lam R i K) Prod.fst measurable_fst
    _ hf henv hdensity


/-- One common event handles a countable family of second-stage versions
and removes normalization only on established probability fibres. -/
theorem sbxS9_secondRestart_ae_all_versions_and_probability {d : ℕ} {ι : Type*}
    [Countable ι] (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d))
    (ν : Measure ((FieldPair d × CoupledSample d) × CoupledSample d))
    (K L : ι → CoupledQuenchedLaws d)
    (hac : ν.map (sbxS9SecondRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ j, ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K j p = L j p)
    (hp : ∀ j, ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, IsProbabilityMeasure (K j p)) :
    ∀ᵐ z ∂ν, ∀ j,
      K j (sbxS9SecondRestartEndpoint Δ lam R i z) =
        L j (sbxS9SecondRestartEndpoint Δ lam R i z) ∧
      IsProbabilityMeasure (K j (sbxS9SecondRestartEndpoint Δ lam R i z)) ∧
      sbxS9SecondRestartKernel Δ lam R i (K j) z =
        K j (sbxS9SecondRestartEndpoint Δ lam R i z) := by
  apply ae_all_iff.mpr
  intro j
  have hm : AEMeasurable (sbxS9SecondRestartEndpoint Δ lam R i) ν :=
    (sbxS9_measurable_secondRestartEndpoint Δ lam R i).aemeasurable
  filter_upwards [ae_of_ae_map hm (hac.ae_le (hKL j)),
    ae_of_ae_map hm (hac.ae_le (hp j))] with z hz hprob
  exact ⟨hz, hprob, sbxS9_secondRestart_eq_raw Δ lam R i (K j) z hprob⟩


/-- Spatial density on the finite first-regeneration branch follows from
positive-grid spatial densities on the same sample law. -/
theorem sbxS9_finite_firstRegeneration_spatial_endpoint_ac {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hac : ∀ n : ℕ, μ.map (fun z => z.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ≪
      (volume : Measure (Vec d))) :
    (μ.restrict {z | firstRegenerationTime Δ lam R z.2 i ≠ ⊤}).map
      (fun z => (sbxS9FirstRegenerationEndpoint Δ lam R i z).1) ≪
      (volume : Measure (Vec d)) := by
  rw [sbxS9_firstRegeneration_finite_eq_iUnion Δ hΔ lam R i]
  rw [sbxS9_map_countable_slices μ _
    (sbxS9_measurableSet_firstRegenerationSlice Δ lam R i)
    (sbxS9_firstRegenerationSlice_pairwise_disjoint Δ hΔ lam R i) _
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).fst
    (fun n z => z.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ))
    (fun n z hz => congrArg Prod.fst
      (sbxS9_firstRegenerationEndpoint_eq_on_slice Δ lam R i n z hz))]
  apply Measure.absolutelyContinuous_sum_left
  intro n
  exact sbxS9_restricted_endpoint_law_ac μ _ _
    ((measurable_pathPosition _).comp measurable_snd.fst) _ (hac n)

/-- The spatial endpoint has a density when the infinite branch is null. -/
theorem sbxS9_firstRegeneration_spatial_endpoint_ac_of_ae_finite {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hac : ∀ n : ℕ, μ.map (fun z => z.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ≪
      (volume : Measure (Vec d)))
    (hfin : ∀ᵐ z ∂μ, firstRegenerationTime Δ lam R z.2 i ≠ ⊤) :
    μ.map (fun z => (sbxS9FirstRegenerationEndpoint Δ lam R i z).1) ≪
      (volume : Measure (Vec d)) := by
  have h := sbxS9_finite_firstRegeneration_spatial_endpoint_ac Δ hΔ lam R i μ hac
  have hr : μ.restrict {z | firstRegenerationTime Δ lam R z.2 i ≠ ⊤} = μ :=
    Measure.restrict_eq_self_of_ae_mem hfin
  rwa [hr] at h


/-- Signed integrals of the complete two-restart record agree under the
transported kernel versions. -/
theorem sbxS9_twoRestart_record_integral_eq {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d)) (K L : CoupledQuenchedLaws d)
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hac₂ : (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K).map
      (sbxS9SecondRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p)
    (Φ : (((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d) ×
      (FieldPair d × FieldPair d) → ℝ) :
    (∫ z, Φ z ∂(((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i K).map (sbxS9TwoRestartRecordsMap Δ lam R i))) =
    ∫ z, Φ z ∂(((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i L) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i L).map (sbxS9TwoRestartRecordsMap Δ lam R i)) := by
  rw [sbxS9_twoRestart_joint_eq Δ lam R i Q μ K L hac₁ hac₂ hKL]


/-- Positive-grid density and finite regeneration on the actual selected
restart fibres yield the joint second-endpoint density. -/
theorem sbxS9_secondRestart_endpoint_ac_of_grid_fibres {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d)) [SFinite Q]
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (K : CoupledQuenchedLaws d)
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hgrid : ∀ᵐ z ∂μ, ∀ n : ℕ,
      (sbxS9FirstRegenerationRestartKernel Δ lam R i K z).map
        (fun b => b.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ≪ (volume : Measure (Vec d)))
    (hfin : ∀ᵐ z ∂μ, ∀ᵐ b ∂(sbxS9FirstRegenerationRestartKernel Δ lam R i K z),
      firstRegenerationTime Δ lam R b i ≠ ⊤) :
    (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K).map
      (sbxS9SecondRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q := by
  apply sbxS9_secondRestart_endpoint_ac_of_spatial_fibre_ac Δ lam R i Q μ K hac₁
  filter_upwards [hgrid, hfin] with z hg hf
  let ν := (sbxS9FirstRegenerationRestartKernel Δ lam R i K z).map (Prod.mk z.1)
  have hνgrid : ∀ n : ℕ, ν.map (fun w => w.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ≪
      (volume : Measure (Vec d)) := by
    intro n
    dsimp only [ν]
    rw [Measure.map_map (show Measurable (fun w : FieldPair d × CoupledSample d =>
      w.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) from
        (measurable_pathPosition _).comp measurable_snd.fst) measurable_prodMk_left]
    exact hg n
  have hνfin : ∀ᵐ w ∂ν, firstRegenerationTime Δ lam R w.2 i ≠ ⊤ := by
    dsimp only [ν]
    apply (ae_map_iff measurable_prodMk_left.aemeasurable
      (measurableSet_eq_fun ((measurable_firstRegenerationTime Δ lam R i).comp
        measurable_snd) measurable_const).compl).2
    exact hf
  have h := sbxS9_firstRegeneration_spatial_endpoint_ac_of_ae_finite
    Δ hΔ lam R i ν hνgrid hνfin
  dsimp only [ν] at h
  rw [Measure.map_map (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).fst
    measurable_prodMk_left] at h
  exact h

#print axioms sbxS9_secondRestart_endpoint_ac_of_grid_fibres

#print axioms sbxS9_twoRestart_record_integral_eq

#print axioms sbxS9_finite_firstRegeneration_spatial_endpoint_ac
#print axioms sbxS9_firstRegeneration_spatial_endpoint_ac_of_ae_finite

#print axioms sbxS9_joint_endpoint_ac_of_spatial_fibre_ac
#print axioms sbxS9_secondRestart_endpoint_ac_of_spatial_fibre_ac
#print axioms sbxS9_secondRestart_ae_all_versions_and_probability

/-- The third endpoint retains the initial environment and reads the second
restart sample, including its infinite-time branch. -/
def sbxS9ThirdRestartEndpoint {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (z : ((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d) :
    Vec d × FieldPair d :=
  sbxS9FirstRegenerationEndpoint Δ lam R i (z.1.1.1, z.2)

theorem sbxS9_measurable_thirdRestartEndpoint {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) : Measurable (sbxS9ThirdRestartEndpoint Δ lam R i) :=
  (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).comp
    (measurable_fst.fst.fst.prodMk measurable_snd)

/-- The third literal restart, normalized on all fibres. -/
def sbxS9ThirdRestartKernel {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) :
    Kernel (((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d)
      (CoupledSample d) :=
  (Probability.probabilityPart K).comap (sbxS9ThirdRestartEndpoint Δ lam R i)
    (sbxS9_measurable_thirdRestartEndpoint Δ lam R i)

instance sbxS9ThirdRestartKernel_isFinite {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (K : CoupledQuenchedLaws d) :
    IsFiniteKernel (sbxS9ThirdRestartKernel Δ lam R i K) :=
  inferInstanceAs (IsFiniteKernel ((Probability.probabilityPart K).comap _ _))

theorem sbxS9_thirdRestart_eq_raw {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (K : CoupledQuenchedLaws d)
    (z : ((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d)
    (hp : IsProbabilityMeasure (K (sbxS9ThirdRestartEndpoint Δ lam R i z))) :
    sbxS9ThirdRestartKernel Δ lam R i K z = K (sbxS9ThirdRestartEndpoint Δ lam R i z) := by
  let := hp
  exact Probability.probabilityPart_eq_of_isProbabilityMeasure K _

/-- Third-stage versions agree on the actual preceding joint measure. -/
theorem sbxS9_thirdRestart_compProd_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (Q : Measure (FieldPair d))
    (ν : Measure (((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d))
    (K L : CoupledQuenchedLaws d)
    (hac : ν.map (sbxS9ThirdRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    ν ⊗ₘ sbxS9ThirdRestartKernel Δ lam R i K =
      ν ⊗ₘ sbxS9ThirdRestartKernel Δ lam R i L := by
  apply Measure.compProd_congr
  filter_upwards [ae_of_ae_map
    (sbxS9_measurable_thirdRestartEndpoint Δ lam R i).aemeasurable (hac.ae_le hKL)]
    with z hz
  change Probability.probabilityPart K _ = Probability.probabilityPart L _
  simp only [Probability.probabilityPart_apply, hz]

/-- Three complete nested restart laws agree when each actual endpoint law
is absolutely continuous with respect to the spatial-environment product. -/
theorem sbxS9_threeRestart_joint_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (Q : Measure (FieldPair d))
    (μ : Measure (FieldPair d × CoupledSample d)) (K L : CoupledQuenchedLaws d)
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hac₂ : (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K).map
      (sbxS9SecondRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q)
    (hac₃ : ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i K).map (sbxS9ThirdRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i K) ⊗ₘ sbxS9ThirdRestartKernel Δ lam R i K =
    ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i L) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i L) ⊗ₘ sbxS9ThirdRestartKernel Δ lam R i L := by
  rw [sbxS9_thirdRestart_compProd_eq Δ lam R i Q _ K L hac₃ hKL,
    sbxS9_twoRestart_joint_eq Δ lam R i Q μ K L hac₁ hac₂ hKL]

/-- One common event handles every countable third-stage version and
removes normalization on its established probability fibres. -/
theorem sbxS9_thirdRestart_ae_all_versions_and_probability {d : ℕ} {ι : Type*}
    [Countable ι] (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d))
    (ν : Measure (((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d))
    (K L : ι → CoupledQuenchedLaws d)
    (hac : ν.map (sbxS9ThirdRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ j, ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K j p = L j p)
    (hp : ∀ j, ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, IsProbabilityMeasure (K j p)) :
    ∀ᵐ z ∂ν, ∀ j,
      K j (sbxS9ThirdRestartEndpoint Δ lam R i z) =
        L j (sbxS9ThirdRestartEndpoint Δ lam R i z) ∧
      IsProbabilityMeasure (K j (sbxS9ThirdRestartEndpoint Δ lam R i z)) ∧
      sbxS9ThirdRestartKernel Δ lam R i (K j) z =
        K j (sbxS9ThirdRestartEndpoint Δ lam R i z) := by
  apply ae_all_iff.mpr
  intro j
  have hm : AEMeasurable (sbxS9ThirdRestartEndpoint Δ lam R i) ν :=
    (sbxS9_measurable_thirdRestartEndpoint Δ lam R i).aemeasurable
  filter_upwards [ae_of_ae_map hm (hac.ae_le (hKL j)),
    ae_of_ae_map hm (hac.ae_le (hp j))] with z hz hprob
  exact ⟨hz, hprob, sbxS9_thirdRestart_eq_raw Δ lam R i (K j) z hprob⟩

#print axioms sbxS9ThirdRestartEndpoint
#print axioms sbxS9_measurable_thirdRestartEndpoint
#print axioms sbxS9ThirdRestartKernel
#print axioms sbxS9ThirdRestartKernel_isFinite
#print axioms sbxS9_thirdRestart_eq_raw
#print axioms sbxS9_thirdRestart_compProd_eq
#print axioms sbxS9_threeRestart_joint_eq
#print axioms sbxS9_thirdRestart_ae_all_versions_and_probability

/-- All samples and the three literal endpoint translations are retained. -/
def sbxS9ThreeRestartRecordsMap {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (z : (((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d) ×
      CoupledSample d) :=
  (z, ((sbxS9TwoRestartRecordsMap Δ lam R i z.1).2,
    translate (sbxS9ThirdRestartEndpoint Δ lam R i z.1).1 z.1.1.1.1))

theorem sbxS9_measurable_threeRestartRecordsMap {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) : Measurable (sbxS9ThreeRestartRecordsMap Δ lam R i) := by
  have hω : Measurable (fun z : (((FieldPair d × CoupledSample d) × CoupledSample d) ×
      CoupledSample d) × CoupledSample d => z.1.1.1.1) := measurable_fst.fst.fst.fst
  have h₃ : Measurable (fun z : (((FieldPair d × CoupledSample d) × CoupledSample d) ×
      CoupledSample d) × CoupledSample d => sbxS9ThirdRestartEndpoint Δ lam R i z.1) :=
    (sbxS9_measurable_thirdRestartEndpoint Δ lam R i).comp measurable_fst
  exact measurable_id.prodMk (((sbxS9_measurable_twoRestartRecordsMap Δ lam R i).comp
    measurable_fst).snd.prodMk (Probability.continuous_translate.measurable.comp
      (h₃.fst.prodMk hω)))

/-- Signed measurable observations transfer along the three-stage joint law. -/
theorem sbxS9_threeRestart_record_integral_eq {d : ℕ} {γ : Type*}
    [MeasurableSpace γ] (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d)) (μ : Measure (FieldPair d × CoupledSample d))
    (K L : CoupledQuenchedLaws d)
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hac₂ : (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K).map
      (sbxS9SecondRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q)
    (hac₃ : ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i K).map (sbxS9ThirdRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p)
    (F : (((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d) ×
      CoupledSample d → γ) (Φ : γ → ℝ) :
    (∫ z, Φ z ∂((((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i K) ⊗ₘ sbxS9ThirdRestartKernel Δ lam R i K).map F)) =
    ∫ z, Φ z ∂((((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i L) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i L) ⊗ₘ sbxS9ThirdRestartKernel Δ lam R i L).map F) := by
  rw [sbxS9_threeRestart_joint_eq Δ lam R i Q μ K L hac₁ hac₂ hac₃ hKL]

#print axioms sbxS9ThreeRestartRecordsMap
#print axioms sbxS9_measurable_threeRestartRecordsMap
#print axioms sbxS9_threeRestart_record_integral_eq

/-- A single event on the two-restart history handles countably many versions
and raw probability fibres at all three literal restart endpoints. -/
theorem sbxS9_threeRestart_ae_all_versions_and_probability {d : ℕ} {ι : Type*}
    [Countable ι] (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d)) (μ : Measure (FieldPair d × CoupledSample d))
    [SFinite μ] (J : CoupledQuenchedLaws d) (K L : ι → CoupledQuenchedLaws d)
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hac₂ : (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i J).map
      (sbxS9SecondRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q)
    (hac₃ : ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i J) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i J).map (sbxS9ThirdRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ j, ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K j p = L j p)
    (hp : ∀ j, ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, IsProbabilityMeasure (K j p)) :
    ∀ᵐ z ∂((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i J) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i J), ∀ j,
      (K j (sbxS9FirstRegenerationEndpoint Δ lam R i z.1.1) =
          L j (sbxS9FirstRegenerationEndpoint Δ lam R i z.1.1) ∧
       IsProbabilityMeasure (K j (sbxS9FirstRegenerationEndpoint Δ lam R i z.1.1)) ∧
       sbxS9FirstRegenerationRestartKernel Δ lam R i (K j) z.1.1 =
          K j (sbxS9FirstRegenerationEndpoint Δ lam R i z.1.1)) ∧
      (K j (sbxS9SecondRestartEndpoint Δ lam R i z.1) =
          L j (sbxS9SecondRestartEndpoint Δ lam R i z.1) ∧
       IsProbabilityMeasure (K j (sbxS9SecondRestartEndpoint Δ lam R i z.1)) ∧
       sbxS9SecondRestartKernel Δ lam R i (K j) z.1 =
          K j (sbxS9SecondRestartEndpoint Δ lam R i z.1)) ∧
      (K j (sbxS9ThirdRestartEndpoint Δ lam R i z) =
          L j (sbxS9ThirdRestartEndpoint Δ lam R i z) ∧
       IsProbabilityMeasure (K j (sbxS9ThirdRestartEndpoint Δ lam R i z)) ∧
       sbxS9ThirdRestartKernel Δ lam R i (K j) z =
          K j (sbxS9ThirdRestartEndpoint Δ lam R i z)) := by
  have hfirst : ∀ᵐ z ∂μ, ∀ j,
      K j (sbxS9FirstRegenerationEndpoint Δ lam R i z) =
          L j (sbxS9FirstRegenerationEndpoint Δ lam R i z) ∧
      IsProbabilityMeasure (K j (sbxS9FirstRegenerationEndpoint Δ lam R i z)) ∧
      sbxS9FirstRegenerationRestartKernel Δ lam R i (K j) z =
          K j (sbxS9FirstRegenerationEndpoint Δ lam R i z) := by
    apply ae_all_iff.mpr
    intro j
    have hm : AEMeasurable (sbxS9FirstRegenerationEndpoint Δ lam R i) μ :=
      (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).aemeasurable
    filter_upwards [ae_of_ae_map hm (hac₁.ae_le (hKL j)),
      ae_of_ae_map hm (hac₁.ae_le (hp j))] with z hz hprob
    exact ⟨hz, hprob, sbxS9_firstRegeneration_restart_eq_raw Δ lam R i (K j) z hprob⟩
  have hfirst' := (sbxS9_quasiMeasurePreserving_compProd_fst μ
    (sbxS9FirstRegenerationRestartKernel Δ lam R i J)).ae hfirst
  have hfirst'' := (sbxS9_quasiMeasurePreserving_compProd_fst
    (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i J)
    (sbxS9SecondRestartKernel Δ lam R i J)).ae hfirst'
  have hsecond := sbxS9_secondRestart_ae_all_versions_and_probability Δ lam R i Q
    (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i J) K L hac₂ hKL hp
  have hsecond' := (sbxS9_quasiMeasurePreserving_compProd_fst
    (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i J)
    (sbxS9SecondRestartKernel Δ lam R i J)).ae hsecond
  have hthird := sbxS9_thirdRestart_ae_all_versions_and_probability Δ lam R i Q
    ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i J) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i J) K L hac₃ hKL hp
  filter_upwards [hfirst'', hsecond', hthird] with z h₁ h₂ h₃ j
  exact ⟨h₁ j, h₂ j, h₃ j⟩

#print axioms sbxS9_threeRestart_ae_all_versions_and_probability

/-- Equality of three-stage joint laws transports integrable signed tests
through all three nested integrals. -/
theorem sbxS9_threeStage_nested_integral_eq {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) [SFinite μ] (κ κ' : Kernel α β)
    (η η' : Kernel (α × β) γ) (θ θ' : Kernel ((α × β) × γ) δ)
    [IsSFiniteKernel κ] [IsSFiniteKernel κ'] [IsSFiniteKernel η]
    [IsSFiniteKernel η'] [IsSFiniteKernel θ] [IsSFiniteKernel θ']
    (hjoint : ((μ ⊗ₘ κ) ⊗ₘ η) ⊗ₘ θ = ((μ ⊗ₘ κ') ⊗ₘ η') ⊗ₘ θ')
    (f : ((α × β) × γ) × δ → ℝ) (hf : Integrable f (((μ ⊗ₘ κ) ⊗ₘ η) ⊗ₘ θ)) :
    (∫ a, ∫ b, ∫ c, ∫ e, f (((a, b), c), e) ∂θ ((a, b), c) ∂η (a, b) ∂κ a ∂μ) =
      ∫ a, ∫ b, ∫ c, ∫ e, f (((a, b), c), e) ∂θ' ((a, b), c) ∂η' (a, b) ∂κ' a ∂μ := by
  have hf' : Integrable f (((μ ⊗ₘ κ') ⊗ₘ η') ⊗ₘ θ') := hjoint ▸ hf
  have hθ := sbxS9_integrable_joint_nested_test ((μ ⊗ₘ κ) ⊗ₘ η) θ f hf
  have hθ' := sbxS9_integrable_joint_nested_test ((μ ⊗ₘ κ') ⊗ₘ η') θ' f hf'
  have hη := sbxS9_integrable_joint_nested_test (μ ⊗ₘ κ) η _ hθ
  have hη' := sbxS9_integrable_joint_nested_test (μ ⊗ₘ κ') η' _ hθ'
  rw [← Measure.integral_compProd hη, ← Measure.integral_compProd hθ,
    ← Measure.integral_compProd hf, ← Measure.integral_compProd hη',
    ← Measure.integral_compProd hθ', ← Measure.integral_compProd hf', hjoint]

#print axioms sbxS9_threeStage_nested_integral_eq

/-- Signed integrable observations of the literal three-restart history
have equal nested integrals for the two kernel versions. -/
theorem sbxS9_threeRestart_nested_integral_eq {d : ℕ} {γ : Type*}
    [MeasurableSpace γ] (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d)) (μ : Measure (FieldPair d × CoupledSample d))
    [SFinite μ] (K L : CoupledQuenchedLaws d)
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hac₂ : (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K).map
      (sbxS9SecondRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q)
    (hac₃ : ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i K).map (sbxS9ThirdRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p)
    (F : (((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d) ×
      CoupledSample d → γ) (hF : Measurable F) (Φ : γ → ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ ((((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel Δ lam R i K) ⊗ₘ
      sbxS9SecondRestartKernel Δ lam R i K) ⊗ₘ sbxS9ThirdRestartKernel Δ lam R i K).map F)) :
    (∫ a, ∫ b, ∫ c, ∫ e, Φ (F (((a, b), c), e))
      ∂sbxS9ThirdRestartKernel Δ lam R i K ((a, b), c)
      ∂sbxS9SecondRestartKernel Δ lam R i K (a, b)
      ∂sbxS9FirstRegenerationRestartKernel Δ lam R i K a ∂μ) =
    ∫ a, ∫ b, ∫ c, ∫ e, Φ (F (((a, b), c), e))
      ∂sbxS9ThirdRestartKernel Δ lam R i L ((a, b), c)
      ∂sbxS9SecondRestartKernel Δ lam R i L (a, b)
      ∂sbxS9FirstRegenerationRestartKernel Δ lam R i L a ∂μ := by
  exact sbxS9_threeStage_nested_integral_eq μ _ _ _ _ _ _
    (sbxS9_threeRestart_joint_eq Δ lam R i Q μ K L hac₁ hac₂ hac₃ hKL)
    (fun z => Φ (F z))
    ((integrable_map_measure hΦ.aestronglyMeasurable hF.aemeasurable).mp hi)

#print axioms sbxS9_threeRestart_nested_integral_eq

/-- The second endpoint supplies the environment marginal needed to prove
third-endpoint joint absolute continuity from the actual spatial fibres. -/
theorem sbxS9_thirdRestart_endpoint_ac_of_spatial_fibre_ac {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (Q : Measure (FieldPair d)) [SFinite Q]
    (ν : Measure ((FieldPair d × CoupledSample d) × CoupledSample d)) [SFinite ν]
    (K : CoupledQuenchedLaws d)
    (hac₂ : ν.map (sbxS9SecondRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hdensity : ∀ᵐ z ∂ν,
      (sbxS9SecondRestartKernel Δ lam R i K z).map
        (fun b => (sbxS9FirstRegenerationEndpoint Δ lam R i (z.1.1, b)).1) ≪
          (volume : Measure (Vec d))) :
    (ν ⊗ₘ sbxS9SecondRestartKernel Δ lam R i K).map
      (sbxS9ThirdRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q := by
  have henv : ν.map (fun z => z.1.1) ≪ Q := by
    have h := (hac₂.map measurable_snd).trans
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d)))
        (ν := Q)).absolutelyContinuous
    rw [Measure.map_map measurable_snd
      (sbxS9_measurable_secondRestartEndpoint Δ lam R i)] at h
    exact h
  have hf : Measurable (fun z : ((FieldPair d × CoupledSample d) × CoupledSample d) ×
      CoupledSample d => (sbxS9ThirdRestartEndpoint Δ lam R i z).1) :=
    (sbxS9_measurable_thirdRestartEndpoint Δ lam R i).fst
  exact sbxS9_joint_endpoint_ac_of_spatial_fibre_ac Q ν
    (sbxS9SecondRestartKernel Δ lam R i K) (fun z => z.1.1) measurable_fst.fst
    _ hf henv hdensity

#print axioms sbxS9_thirdRestart_endpoint_ac_of_spatial_fibre_ac

/-- Positive-grid densities and almost-sure finite regeneration on the
second restart fibres yield third-endpoint joint absolute continuity. -/
theorem sbxS9_thirdRestart_endpoint_ac_of_grid_fibres {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d)) [SFinite Q]
    (ν : Measure ((FieldPair d × CoupledSample d) × CoupledSample d)) [SFinite ν]
    (K : CoupledQuenchedLaws d)
    (hac₂ : ν.map (sbxS9SecondRestartEndpoint Δ lam R i) ≪
      (volume : Measure (Vec d)).prod Q)
    (hgrid : ∀ᵐ z ∂ν, ∀ n : ℕ,
      (sbxS9SecondRestartKernel Δ lam R i K z).map
        (fun b => b.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ≪ (volume : Measure (Vec d)))
    (hfin : ∀ᵐ z ∂ν, ∀ᵐ b ∂(sbxS9SecondRestartKernel Δ lam R i K z),
      firstRegenerationTime Δ lam R b i ≠ ⊤) :
    (ν ⊗ₘ sbxS9SecondRestartKernel Δ lam R i K).map
      (sbxS9ThirdRestartEndpoint Δ lam R i) ≪ (volume : Measure (Vec d)).prod Q := by
  apply sbxS9_thirdRestart_endpoint_ac_of_spatial_fibre_ac Δ lam R i Q ν K hac₂
  filter_upwards [hgrid, hfin] with z hg hf
  let ρ := (sbxS9SecondRestartKernel Δ lam R i K z).map (Prod.mk z.1.1)
  have hρgrid : ∀ n : ℕ, ρ.map (fun w => w.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ≪
      (volume : Measure (Vec d)) := by
    intro n
    dsimp only [ρ]
    rw [Measure.map_map (show Measurable (fun w : FieldPair d × CoupledSample d =>
      w.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) from
        (measurable_pathPosition _).comp measurable_snd.fst) measurable_prodMk_left]
    exact hg n
  have hρfin : ∀ᵐ w ∂ρ, firstRegenerationTime Δ lam R w.2 i ≠ ⊤ := by
    dsimp only [ρ]
    apply (ae_map_iff measurable_prodMk_left.aemeasurable
      (measurableSet_eq_fun ((measurable_firstRegenerationTime Δ lam R i).comp
        measurable_snd) measurable_const).compl).2
    exact hf
  have h := sbxS9_firstRegeneration_spatial_endpoint_ac_of_ae_finite
    Δ hΔ lam R i ρ hρgrid hρfin
  dsimp only [ρ] at h
  rw [Measure.map_map (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).fst
    measurable_prodMk_left] at h
  exact h

#print axioms sbxS9_thirdRestart_endpoint_ac_of_grid_fibres

/-- Actual regular coupling fibres provide all positive-grid densities at any
measurably selected endpoint whose law is spatial-environment absolutely continuous. -/
theorem sbxS9_selected_endpoint_probability_and_grid {d : ℕ} {α : Type*}
    [MeasurableSpace α] (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure α) (e : α → Vec d × FieldPair d) (he : Measurable e)
    (hac : μ.map e ≪ (volume : Measure (Vec d)).prod Q.measure) :
    ∀ᵐ z ∂μ, IsProbabilityMeasure (K (e z)) ∧ ∀ n : ℕ,
      (K (e z)).map (fun b => b.1 (((n + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam)) ≪
        (volume : Measure (Vec d)) := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have hg := ae_coupledEnvironmentRegular hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  have hgood : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      IsProbabilityMeasure (K p) ∧ ∀ n : ℕ,
        (K p).map (fun b => b.1 (((n + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam)) ≪
          (volume : Measure (Vec d)) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hg, hK.1.2, hK.2.1.2]
      with p hω hp hm
    refine ⟨hp, fun n => ?_⟩
    exact coupled_endpoint_density_of_path_marginal P K p hm _
      (hω.2.2.2 (n + 1) (by omega) p.1)
  exact ae_of_ae_map he.aemeasurable (hac.ae_le hgood)

#print axioms sbxS9_selected_endpoint_probability_and_grid

/-- The actual coupling supplies the grid-density input for the second
endpoint; finiteness is retained on the selected restart fibres. -/
theorem sbxS9_secondRestart_endpoint_ac_of_coupling_and_finite {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ z ∂μ, ∀ᵐ b ∂(sbxS9FirstRegenerationRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K z),
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤) :
    (μ ⊗ₘ sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd) K).map
      (sbxS9SecondRestartEndpoint (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  apply sbxS9_secondRestart_endpoint_ac_of_grid_fibres _ hΔ lam (l / lam)
    (Renewal.forceCoord hd) Q.measure μ K hac ?_ hfin
  filter_upwards [sbxS9_selected_endpoint_probability_and_grid hd Q lam h0 h1 l δ P K
    hK μ _ (sbxS9_measurable_firstRegenerationEndpoint _ _ _ _) hac] with z hz
  rw [sbxS9_firstRegeneration_restart_eq_raw _ _ _ _ K z hz.1]
  exact hz.2

/-- The same actual-coupling grid input applies at the next restart, with
finiteness stated under that selected fibre. -/
theorem sbxS9_thirdRestart_endpoint_ac_of_coupling_and_finite {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (ν : Measure ((FieldPair d × CoupledSample d) × CoupledSample d)) [SFinite ν]
    (hac : ν.map (sbxS9SecondRestartEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ z ∂ν, ∀ᵐ b ∂(sbxS9SecondRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K z),
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤) :
    (ν ⊗ₘ sbxS9SecondRestartKernel (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd) K).map
      (sbxS9ThirdRestartEndpoint (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  apply sbxS9_thirdRestart_endpoint_ac_of_grid_fibres _ hΔ lam (l / lam)
    (Renewal.forceCoord hd) Q.measure ν K hac ?_ hfin
  filter_upwards [sbxS9_selected_endpoint_probability_and_grid hd Q lam h0 h1 l δ P K
    hK ν _ (sbxS9_measurable_secondRestartEndpoint _ _ _ _) hac] with z hz
  rw [sbxS9_secondRestart_eq_raw _ _ _ _ K z hz.1]
  exact hz.2

#print axioms sbxS9_secondRestart_endpoint_ac_of_coupling_and_finite
#print axioms sbxS9_thirdRestart_endpoint_ac_of_coupling_and_finite

/-- Signed observations of three actual coupling restarts transport across
kernel versions when both selected restart fibres regenerate almost surely. -/
theorem sbxS9_threeRestart_nested_integral_eq_of_coupling_and_finite {d : ℕ} {γ : Type*}
    [MeasurableSpace γ] (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin₂ : ∀ᵐ z ∂μ, ∀ᵐ b ∂(sbxS9FirstRegenerationRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K z),
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤)
    (hfin₃ : ∀ᵐ z ∂(μ ⊗ₘ sbxS9FirstRegenerationRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K),
      ∀ᵐ b ∂(sbxS9SecondRestartKernel (Renewal.regenDelta lam) lam
        (l / lam) (Renewal.forceCoord hd) K z),
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (F : (((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d) ×
      CoupledSample d → γ) (hF : Measurable F) (Φ : γ → ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ ((((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K) ⊗ₘ
      sbxS9SecondRestartKernel (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) K) ⊗ₘ sbxS9ThirdRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K).map F)) :
    (∫ a, ∫ b, ∫ c, ∫ e, Φ (F (((a, b), c), e))
      ∂sbxS9ThirdRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K ((a, b), c)
      ∂sbxS9SecondRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K (a, b)
      ∂sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K a ∂μ) =
    ∫ a, ∫ b, ∫ c, ∫ e, Φ (F (((a, b), c), e))
      ∂sbxS9ThirdRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) L ((a, b), c)
      ∂sbxS9SecondRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) L (a, b)
      ∂sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) L a ∂μ := by
  have hac₂ := sbxS9_secondRestart_endpoint_ac_of_coupling_and_finite
    hd Q lam h0 h1 l δ P K hK μ hac₁ hfin₂
  have hac₃ := sbxS9_thirdRestart_endpoint_ac_of_coupling_and_finite
    hd Q lam h0 h1 l δ P K hK _ hac₂ hfin₃
  exact sbxS9_threeRestart_nested_integral_eq _ _ _ _ Q.measure μ K L
    hac₁ hac₂ hac₃ hKL F hF Φ hΦ hi

#print axioms sbxS9_threeRestart_nested_integral_eq_of_coupling_and_finite

/-- A product-almost-everywhere fibre property transfers to any measurable
endpoint selection whose law is absolutely continuous with respect to that product. -/
theorem sbxS9_selected_endpoint_ae_finite {d : ℕ} {α : Type*}
    [MeasurableSpace α] (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (μ : Measure α) (e : α → Vec d × FieldPair d) (he : Measurable e)
    (hac : μ.map e ≪ (volume : Measure (Vec d)).prod Q)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, ∀ᵐ b ∂K p,
      firstRegenerationTime Δ lam R b i ≠ ⊤) :
    ∀ᵐ z ∂μ, ∀ᵐ b ∂K (e z), firstRegenerationTime Δ lam R b i ≠ ⊤ :=
  ae_of_ae_map he.aemeasurable (hac.ae_le hfin)

/-- The single product-a.e. finiteness input supplies finiteness on the
first normalized restart fibres of the actual coupling. -/
theorem sbxS9_firstRestart_ae_finite_of_product_ae {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hac : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤) :
    ∀ᵐ z ∂μ, ∀ᵐ b ∂(sbxS9FirstRegenerationRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K z),
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤ := by
  filter_upwards [sbxS9_selected_endpoint_probability_and_grid hd Q lam h0 h1 l δ P K
    hK μ _ (sbxS9_measurable_firstRegenerationEndpoint _ _ _ _) hac,
    sbxS9_selected_endpoint_ae_finite _ _ _ _ Q.measure K μ _
      (sbxS9_measurable_firstRegenerationEndpoint _ _ _ _) hac hfin] with z hp hf
  rw [sbxS9_firstRegeneration_restart_eq_raw _ _ _ _ K z hp.1]
  exact hf

/-- The same product-a.e. finiteness input applies to the second normalized
restart fibres whenever their selected endpoint has the required density. -/
theorem sbxS9_secondRestart_ae_finite_of_product_ae {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (ν : Measure ((FieldPair d × CoupledSample d) × CoupledSample d))
    (hac : ν.map (sbxS9SecondRestartEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤) :
    ∀ᵐ z ∂ν, ∀ᵐ b ∂(sbxS9SecondRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K z),
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤ := by
  filter_upwards [sbxS9_selected_endpoint_probability_and_grid hd Q lam h0 h1 l δ P K
    hK ν _ (sbxS9_measurable_secondRestartEndpoint _ _ _ _) hac,
    sbxS9_selected_endpoint_ae_finite _ _ _ _ Q.measure K ν _
      (sbxS9_measurable_secondRestartEndpoint _ _ _ _) hac hfin] with z hp hf
  rw [sbxS9_secondRestart_eq_raw _ _ _ _ K z hp.1]
  exact hf

#print axioms sbxS9_selected_endpoint_ae_finite
#print axioms sbxS9_firstRestart_ae_finite_of_product_ae
#print axioms sbxS9_secondRestart_ae_finite_of_product_ae

/-- One product-a.e. finiteness input supplies the selected-fibre hypotheses
for signed observations of the complete three-restart history. -/
theorem sbxS9_threeRestart_nested_integral_eq_of_coupling_and_product_finite {d : ℕ} {γ : Type*}
    [MeasurableSpace γ] (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (F : (((FieldPair d × CoupledSample d) × CoupledSample d) × CoupledSample d) ×
      CoupledSample d → γ) (hF : Measurable F) (Φ : γ → ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ ((((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K) ⊗ₘ
      sbxS9SecondRestartKernel (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) K) ⊗ₘ sbxS9ThirdRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K).map F)) :
    (∫ a, ∫ b, ∫ c, ∫ e, Φ (F (((a, b), c), e))
      ∂sbxS9ThirdRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K ((a, b), c)
      ∂sbxS9SecondRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K (a, b)
      ∂sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K a ∂μ) =
    ∫ a, ∫ b, ∫ c, ∫ e, Φ (F (((a, b), c), e))
      ∂sbxS9ThirdRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) L ((a, b), c)
      ∂sbxS9SecondRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) L (a, b)
      ∂sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) L a ∂μ := by
  have hfin₂ := sbxS9_firstRestart_ae_finite_of_product_ae
    hd Q lam h0 h1 l δ P K hK μ hac₁ hfin
  have hac₂ := sbxS9_secondRestart_endpoint_ac_of_coupling_and_finite
    hd Q lam h0 h1 l δ P K hK μ hac₁ hfin₂
  have hfin₃ := sbxS9_secondRestart_ae_finite_of_product_ae
    hd Q lam h0 h1 l δ P K hK _ hac₂ hfin
  exact sbxS9_threeRestart_nested_integral_eq_of_coupling_and_finite
    hd Q lam h0 h1 l δ P K L hK μ hac₁ hfin₂ hfin₃ hKL F hF Φ hΦ hi

#print axioms sbxS9_threeRestart_nested_integral_eq_of_coupling_and_product_finite


/-- The full three-restart joint law is independent of the coupling version
under product-almost-everywhere regeneration finiteness. This also transports
all measurable finite-history events without an integrability hypothesis. -/
theorem sbxS9_threeRestart_joint_eq_of_coupling_and_product_finite {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac₁ : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p) :
    ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd) K) ⊗ₘ sbxS9SecondRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K) ⊗ₘ
      sbxS9ThirdRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) K =
    ((μ ⊗ₘ sbxS9FirstRegenerationRestartKernel (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd) L) ⊗ₘ sbxS9SecondRestartKernel
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) L) ⊗ₘ
      sbxS9ThirdRestartKernel (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) L := by
  have hfin₂ := sbxS9_firstRestart_ae_finite_of_product_ae
    hd Q lam h0 h1 l δ P K hK μ hac₁ hfin
  have hac₂ := sbxS9_secondRestart_endpoint_ac_of_coupling_and_finite
    hd Q lam h0 h1 l δ P K hK μ hac₁ hfin₂
  have hfin₃ := sbxS9_secondRestart_ae_finite_of_product_ae
    hd Q lam h0 h1 l δ P K hK _ hac₂ hfin
  have hac₃ := sbxS9_thirdRestart_endpoint_ac_of_coupling_and_finite
    hd Q lam h0 h1 l δ P K hK _ hac₂ hfin₃
  exact sbxS9_threeRestart_joint_eq _ _ _ _ Q.measure μ K L hac₁ hac₂ hac₃ hKL

#print axioms sbxS9_threeRestart_joint_eq_of_coupling_and_product_finite


/-- Restart at a measurable endpoint selected from an arbitrary history. -/
def sbxS9HistoryRestartKernel {d : ℕ} {α : Type*} [MeasurableSpace α]
    (K : CoupledQuenchedLaws d) (e : α → Vec d × FieldPair d) (he : Measurable e) :
    Kernel α (CoupledSample d) := (Probability.probabilityPart K).comap e he

instance sbxS9HistoryRestartKernel_isFinite {d : ℕ} {α : Type*} [MeasurableSpace α]
    (K : CoupledQuenchedLaws d) (e : α → Vec d × FieldPair d) (he : Measurable e) :
    IsFiniteKernel (sbxS9HistoryRestartKernel K e he) :=
  inferInstanceAs (IsFiniteKernel ((Probability.probabilityPart K).comap e he))

/-- A single step for an arbitrary history: actual coupling grid densities and
product-a.e. finite regeneration propagate joint endpoint density. -/
theorem sbxS9_historyRestart_endpoint_ac_of_coupling_and_product_finite
    {d : ℕ} {α : Type*} [MeasurableSpace α]
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure α) [SFinite μ] (e : α → Vec d × FieldPair d) (he : Measurable e)
    (hac : μ.map e ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤) :
    (μ ⊗ₘ sbxS9HistoryRestartKernel K e he).map
      (fun z => sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
        (l / lam) (Renewal.forceCoord hd) ((e z.1).2, z.2)) ≪
      (volume : Measure (Vec d)).prod Q.measure := by
  let Δ := Renewal.regenDelta lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have henv : μ.map (fun z => (e z).2) ≪ Q.measure := by
    have h := (hac.map measurable_snd).trans
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d)))
        (ν := Q.measure)).absolutelyContinuous
    rw [Measure.map_map measurable_snd he] at h
    exact h
  have hf : Measurable (fun z : α × CoupledSample d =>
      (sbxS9FirstRegenerationEndpoint Δ lam (l / lam) i ((e z.1).2, z.2)).1) :=
    (sbxS9_measurable_firstRegenerationEndpoint Δ lam (l / lam) i).fst.comp
      ((he.snd.comp measurable_fst).prodMk measurable_snd)
  apply sbxS9_joint_endpoint_ac_of_spatial_fibre_ac Q.measure μ
    (sbxS9HistoryRestartKernel K e he) (fun z => (e z).2) he.snd _ hf henv
  filter_upwards [sbxS9_selected_endpoint_probability_and_grid hd Q lam h0 h1 l δ P K
    hK μ e he hac, sbxS9_selected_endpoint_ae_finite Δ lam (l / lam) i
      Q.measure K μ e he hac hfin] with z hg hfinite
  have hk : sbxS9HistoryRestartKernel K e he z = K (e z) := by
    let := hg.1
    exact Probability.probabilityPart_eq_of_isProbabilityMeasure K _
  rw [hk]
  let ν := (K (e z)).map (Prod.mk (e z).2)
  have hνgrid : ∀ n : ℕ, ν.map (fun w => w.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ≪
      (volume : Measure (Vec d)) := by
    intro n
    dsimp only [ν]
    rw [Measure.map_map (show Measurable (fun w : FieldPair d × CoupledSample d =>
      w.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) from
        (measurable_pathPosition _).comp measurable_snd.fst) measurable_prodMk_left]
    exact hg.2 n
  have hνfin : ∀ᵐ w ∂ν, firstRegenerationTime Δ lam (l / lam) w.2 i ≠ ⊤ := by
    dsimp only [ν]
    apply (ae_map_iff measurable_prodMk_left.aemeasurable
      (measurableSet_eq_fun ((measurable_firstRegenerationTime Δ lam (l / lam) i).comp
        measurable_snd) measurable_const).compl).2
    exact hfinite
  have h := sbxS9_firstRegeneration_spatial_endpoint_ac_of_ae_finite
    Δ hΔ lam (l / lam) i ν hνgrid hνfin
  dsimp only [ν] at h
  rw [Measure.map_map (sbxS9_measurable_firstRegenerationEndpoint Δ lam (l / lam) i).fst
    measurable_prodMk_left] at h
  exact h

#print axioms sbxS9_historyRestart_endpoint_ac_of_coupling_and_product_finite


/-- At any measurable selected endpoint, a.e. equal coupling versions
produce the same joint law for the complete history and next sample. -/
theorem sbxS9_historyRestart_compProd_eq {d : ℕ} {α : Type*} [MeasurableSpace α]
    (Q : Measure (FieldPair d)) (μ : Measure α) (K L : CoupledQuenchedLaws d)
    (e : α → Vec d × FieldPair d) (he : Measurable e)
    (hac : μ.map e ≪ (volume : Measure (Vec d)).prod Q)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, K p = L p) :
    μ ⊗ₘ sbxS9HistoryRestartKernel K e he = μ ⊗ₘ sbxS9HistoryRestartKernel L e he := by
  apply Measure.compProd_congr
  filter_upwards [ae_of_ae_map he.aemeasurable (hac.ae_le hKL)] with z hz
  change Probability.probabilityPart K (e z) = Probability.probabilityPart L (e z)
  simp only [Probability.probabilityPart_apply, hz]

#print axioms sbxS9HistoryRestartKernel
#print axioms sbxS9HistoryRestartKernel_isFinite
#print axioms sbxS9_historyRestart_compProd_eq


/-- Complete nested histories, including the initial environment and sample. -/
def sbxS9RestartHistory (d : ℕ) : ℕ → Type
  | 0 => FieldPair d × CoupledSample d
  | n + 1 => sbxS9RestartHistory d n × CoupledSample d

instance sbxS9RestartHistoryMeasurableSpace (d n : ℕ) :
    MeasurableSpace (sbxS9RestartHistory d n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace (FieldPair d × CoupledSample d))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSpace (sbxS9RestartHistory d n × CoupledSample d))

/-- The endpoint selected from the latest sample, retaining the original field. -/
def sbxS9RestartHistoryEndpoint {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) :
    (n : ℕ) → sbxS9RestartHistory d n → Vec d × FieldPair d
  | 0 => sbxS9FirstRegenerationEndpoint Δ lam R i
  | n + 1 => fun z => sbxS9FirstRegenerationEndpoint Δ lam R i
      ((sbxS9RestartHistoryEndpoint Δ lam R i n z.1).2, z.2)

theorem sbxS9_measurable_restartHistoryEndpoint {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (n : ℕ) : Measurable (sbxS9RestartHistoryEndpoint Δ lam R i n) := by
  induction n with
  | zero => exact sbxS9_measurable_firstRegenerationEndpoint Δ lam R i
  | succ n ih =>
    exact (sbxS9_measurable_firstRegenerationEndpoint Δ lam R i).comp
      ((ih.snd.comp measurable_fst).prodMk measurable_snd)

/-- Iterated actual restart law, normalized on all fibres. -/
def sbxS9RestartHistoryLaw {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (μ : Measure (FieldPair d × CoupledSample d)) (K : CoupledQuenchedLaws d) :
    (n : ℕ) → Measure (sbxS9RestartHistory d n)
  | 0 => μ
  | n + 1 => sbxS9RestartHistoryLaw Δ lam R i μ K n ⊗ₘ
      sbxS9HistoryRestartKernel K (sbxS9RestartHistoryEndpoint Δ lam R i n)
        (sbxS9_measurable_restartHistoryEndpoint Δ lam R i n)

instance sbxS9RestartHistoryLawSFinite {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ] (K : CoupledQuenchedLaws d)
    (n : ℕ) : SFinite (sbxS9RestartHistoryLaw Δ lam R i μ K n) := by
  induction n with
  | zero => exact inferInstanceAs (SFinite μ)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (SFinite (sbxS9RestartHistoryLaw Δ lam R i μ K n ⊗ₘ
      sbxS9HistoryRestartKernel K (sbxS9RestartHistoryEndpoint Δ lam R i n)
        (sbxS9_measurable_restartHistoryEndpoint Δ lam R i n)))

/-- Endpoint density at every finite restart depth. -/
theorem sbxS9_restartHistory_endpoint_ac {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤) (n : ℕ) :
    (sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K n).map
      (sbxS9RestartHistoryEndpoint (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) n) ≪ (volume : Measure (Vec d)).prod Q.measure := by
  induction n with
  | zero => exact hac
  | succ n ih =>
    exact sbxS9_historyRestart_endpoint_ac_of_coupling_and_product_finite
      hd Q lam h0 h1 l δ P K hK _ _ _ ih hfin

/-- All finite restart-history laws agree for product-a.e. equal versions. -/
theorem sbxS9_restartHistory_law_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p) (n : ℕ) :
    sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K n = sbxS9RestartHistoryLaw (Renewal.regenDelta lam)
      lam (l / lam) (Renewal.forceCoord hd) μ L n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change _ ⊗ₘ sbxS9HistoryRestartKernel K _ _ = _ ⊗ₘ sbxS9HistoryRestartKernel L _ _
    rw [sbxS9_historyRestart_compProd_eq Q.measure _ K L _ _
      (sbxS9_restartHistory_endpoint_ac hd Q lam h0 h1 l δ P K hK μ hac hfin n) hKL, ih]

#print axioms sbxS9RestartHistory
#print axioms sbxS9RestartHistoryMeasurableSpace
#print axioms sbxS9RestartHistoryEndpoint
#print axioms sbxS9_measurable_restartHistoryEndpoint
#print axioms sbxS9RestartHistoryLaw
#print axioms sbxS9RestartHistoryLawSFinite
#print axioms sbxS9_restartHistory_endpoint_ac
#print axioms sbxS9_restartHistory_law_eq


/-- The complete previous history and the recentered future record tuple at
its selected endpoint. The restart sample retains its path and all coins. -/
def sbxS9HistoryRecordsMap {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (n m : ℕ) (ks : Fin m → ℕ) (z : sbxS9RestartHistory d (n + 1)) :
    sbxS9RestartHistory d n × FieldPair d ×
      (Fin m → FutureState d (Renewal.forceCoord hd) (l / lam)) :=
  let e := sbxS9RestartHistoryEndpoint (Renewal.regenDelta lam) lam (l / lam)
    (Renewal.forceCoord hd) n z.1
  (z.1, translate e.1 e.2, fun j => regenerationRecord hd lam l (ks j)
    (translate e.1 e.2, recenterSample e.1 z.2))

theorem sbxS9_measurable_historyRecordsMap {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (n m : ℕ) (ks : Fin m → ℕ) : Measurable (sbxS9HistoryRecordsMap hd lam l n m ks) := by
  let e := sbxS9RestartHistoryEndpoint (Renewal.regenDelta lam) lam (l / lam)
    (Renewal.forceCoord hd) n
  have he : Measurable e := sbxS9_measurable_restartHistoryEndpoint _ _ _ _ n
  have henv : Measurable (fun z : sbxS9RestartHistory d (n + 1) =>
      translate (e z.1).1 (e z.1).2) :=
    Probability.continuous_translate.measurable.comp ((he.comp measurable_fst).fst.prodMk
      (he.comp measurable_fst).snd)
  have hs : Measurable (fun z : sbxS9RestartHistory d (n + 1) =>
      recenterSample (e z.1).1 z.2) :=
    measurable_recenterSample.comp ((he.comp measurable_fst).fst.prodMk measurable_snd)
  exact measurable_fst.prodMk (henv.prodMk (measurable_pi_iff.mpr (fun j =>
    (measurable_cycleRecord hd lam l (ks j)).comp (henv.prodMk hs))))

/-- Every finite tuple of future records has the same signed test integrals
under almost-everywhere equal versions of the coupling. -/
theorem sbxS9_historyRecords_integral_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (n m : ℕ) (ks : Fin m → ℕ)
    (Φ : sbxS9RestartHistory d n × FieldPair d ×
      (Fin m → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ) :
    (∫ z, Φ z ∂((sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K (n + 1)).map (sbxS9HistoryRecordsMap hd lam l n m ks))) =
    ∫ z, Φ z ∂((sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ L (n + 1)).map (sbxS9HistoryRecordsMap hd lam l n m ks)) := by
  rw [sbxS9_restartHistory_law_eq hd Q lam h0 h1 l δ P K L hK μ hac hfin hKL (n + 1)]

#print axioms sbxS9HistoryRecordsMap
#print axioms sbxS9_measurable_historyRecordsMap
#print axioms sbxS9_historyRecords_integral_eq

/-- Finiteness of every regeneration time in a finite restart history. -/
def sbxS9HistoryFinite {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) :
    (n : ℕ) → sbxS9RestartHistory d n → Prop
  | 0 => fun z => firstRegenerationTime Δ lam R z.2 i ≠ ⊤
  | n + 1 => fun z => sbxS9HistoryFinite Δ lam R i n z.1 ∧
      firstRegenerationTime Δ lam R z.2 i ≠ ⊤

theorem sbxS9_measurableSet_historyFinite {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) : MeasurableSet {z | sbxS9HistoryFinite Δ lam R i n z} := by
  induction n with
  | zero =>
    exact (measurableSet_eq_fun ((measurable_firstRegenerationTime Δ lam R i).comp
      measurable_snd) measurable_const).compl
  | succ n ih =>
    exact (ih.preimage measurable_fst).inter
      (measurableSet_eq_fun ((measurable_firstRegenerationTime Δ lam R i).comp
        measurable_snd) measurable_const).compl

/-- Product-a.e. finiteness propagates to every sample in a finite actual
restart history, including the original sample. -/
theorem sbxS9_restartHistory_ae_finite {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hbase : ∀ᵐ z ∂μ, firstRegenerationTime (Renewal.regenDelta lam) lam
      (l / lam) z.2 (Renewal.forceCoord hd) ≠ ⊤)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤) (n : ℕ) :
    ∀ᵐ z ∂sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K n,
      sbxS9HistoryFinite (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) n z := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
    let e := sbxS9RestartHistoryEndpoint (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) n
    let ν := sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K n
    have he : Measurable e := sbxS9_measurable_restartHistoryEndpoint _ _ _ _ n
    have hc := sbxS9_restartHistory_endpoint_ac hd Q lam h0 h1 l δ P K hK μ hac hfin n
    have hp := sbxS9_selected_endpoint_probability_and_grid hd Q lam h0 h1 l δ P K
      hK ν e he hc
    have hf := sbxS9_selected_endpoint_ae_finite (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) Q.measure K ν e he hc hfin
    apply Measure.ae_compProd_of_ae_ae (sbxS9_measurableSet_historyFinite _ _ _ _ (n + 1))
    filter_upwards [ih, hp, hf] with z hz hprob hfinite
    let : IsProbabilityMeasure (K (e z)) := hprob.1
    change ∀ᵐ b ∂Probability.probabilityPart K (e z),
      sbxS9HistoryFinite _ _ _ _ n z ∧ firstRegenerationTime _ _ _ b _ ≠ ⊤
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
    filter_upwards [hfinite] with b hb
    exact ⟨hz, hb⟩

#print axioms sbxS9HistoryFinite
#print axioms sbxS9_measurableSet_historyFinite
#print axioms sbxS9_restartHistory_ae_finite

/-- At both source-specified initial laws, finite restart histories use only
finite regeneration times when the supplied restart fibres are product-a.e. finite. -/
theorem sbxS9_restartHistory_ae_finite_of_scope
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d))))
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤) (n : ℕ) :
    ∀ᵐ z ∂sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K n,
      sbxS9HistoryFinite (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) n z := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure μ := by
    rcases (show μ = annealedCoupledLaw Q.measure K ∨
        μ = regenerationConditionedLaw hd Q lam l K hK.1 hD from hμ) with rfl | rfl
    · infer_instance
    · exact ProbabilityTheory.cond_isProbabilityMeasure hD
  have hac := sbxS9_firstRegeneration_endpoint_law_ac_of_scope hscope hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hD μ hμ
  have hbase : ∀ᵐ z ∂μ, firstRegenerationTime (Renewal.regenDelta lam) lam
      (l / lam) z.2 (Renewal.forceCoord hd) ≠ ⊤ := by
    have hs := (hscope d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD 1).2.2 μ hμ
    filter_upwards [hs] with z hz
    obtain ⟨m, _, ht, _⟩ := hz
    have hne := ht.trans_ne ENNReal.coe_ne_top
    simpa only [EinsteinFull.regenerationTime, Regeneration.regenerationTime_one] using hne
  exact sbxS9_restartHistory_ae_finite hd Q lam h0 h1 l δ P K hK μ hac hbase hfin n

#print axioms sbxS9_restartHistory_ae_finite_of_scope

/-- The finite-record law can be computed on finite histories, including the
last restart sample, and is independent of the product-a.e. kernel version. -/
theorem sbxS9_finite_historyRecords_law_eq_of_scope
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d))))
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (n m : ℕ) (ks : Fin m → ℕ) :
    ((sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K (n + 1)).restrict
        {z | sbxS9HistoryFinite (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n + 1) z}).map (sbxS9HistoryRecordsMap hd lam l n m ks) =
    (sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ L (n + 1)).map (sbxS9HistoryRecordsMap hd lam l n m ks) := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure μ := by
    rcases (show μ = annealedCoupledLaw Q.measure K ∨
        μ = regenerationConditionedLaw hd Q lam l K hK.1 hD from hμ) with rfl | rfl
    · infer_instance
    · exact ProbabilityTheory.cond_isProbabilityMeasure hD
  have hac := sbxS9_firstRegeneration_endpoint_law_ac_of_scope hscope hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hD μ hμ
  have hf := sbxS9_restartHistory_ae_finite_of_scope hscope hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK hD μ hμ hfin (n + 1)
  have hr : (sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K (n + 1)).restrict
        {z | sbxS9HistoryFinite (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n + 1) z} =
      sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) μ K (n + 1) :=
    Measure.restrict_eq_self_of_ae_mem hf
  rw [hr,
    sbxS9_restartHistory_law_eq hd Q lam h0 h1 l δ P K L hK μ hac hfin hKL (n + 1)]

#print axioms sbxS9_finite_historyRecords_law_eq_of_scope

/-- Nested tests of any finite recentered record tuple at an arbitrary restart
history use the same raw supplied kernel for product-a.e. equal versions. -/
theorem sbxS9_historyRecords_nested_integral_eq {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (n m : ℕ) (ks : Fin m → ℕ)
    (H : sbxS9RestartHistory d n → ℝ)
    (Φ : sbxS9RestartHistory d n × FieldPair d ×
      (Fin m → FutureState d (Renewal.forceCoord hd) (l / lam)) → ℝ) :
    let e := sbxS9RestartHistoryEndpoint (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) n
    let ν := sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K n
    (∫ z, H z * (∫ b, Φ (sbxS9HistoryRecordsMap hd lam l n m ks (z, b)) ∂K (e z)) ∂ν) =
      ∫ z, H z * (∫ b, Φ (sbxS9HistoryRecordsMap hd lam l n m ks (z, b)) ∂L (e z)) ∂ν := by
  dsimp only
  apply integral_congr_ae
  filter_upwards [sbxS9_ae_kernel_eq_at_joint_endpoint Q.measure _ _
    (sbxS9_measurable_restartHistoryEndpoint _ _ _ _ n).aemeasurable
    (sbxS9_restartHistory_endpoint_ac hd Q lam h0 h1 l δ P K hK μ hac hfin n)
    K L hKL] with z hz
  rw [hz]

#print axioms sbxS9_historyRecords_nested_integral_eq

/-- Conditional boundary between original records and nested restarts. The
history realization and the pathwise record identification are the missing
inputs; this theorem transports the identified tuple across kernel versions. -/
theorem sbxS9_original_records_law_eq_restart_of_identification {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K L : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (μ : Measure (FieldPair d × CoupledSample d)) [SFinite μ]
    (hac : μ.map (sbxS9FirstRegenerationEndpoint (Renewal.regenDelta lam) lam
      (l / lam) (Renewal.forceCoord hd)) ≪ (volume : Measure (Vec d)).prod Q.measure)
    (hfin : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤)
    (hKL : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, K p = L p)
    (n m : ℕ) (ks : Fin m → ℕ)
    (T : FieldPair d × CoupledSample d → sbxS9RestartHistory d (n + 1))
    (hT : Measurable T)
    (hident : μ.map T = sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K (n + 1))
    (hrecords : ∀ᵐ q ∂μ, (fun j => regenerationRecord hd lam l (ks j) q) =
      (sbxS9HistoryRecordsMap hd lam l n m ks (T q)).2.2) :
    μ.map (fun q => fun j => regenerationRecord hd lam l (ks j) q) =
      (sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) μ L (n + 1)).map
        (fun z => (sbxS9HistoryRecordsMap hd lam l n m ks z).2.2) := by
  have hf : Measurable (fun z => (sbxS9HistoryRecordsMap hd lam l n m ks z).2.2) :=
    (sbxS9_measurable_historyRecordsMap hd lam l n m ks).snd.snd
  calc
    _ = μ.map (fun q => (sbxS9HistoryRecordsMap hd lam l n m ks (T q)).2.2) :=
      Measure.map_congr hrecords
    _ = (μ.map T).map (fun z => (sbxS9HistoryRecordsMap hd lam l n m ks z).2.2) :=
      (Measure.map_map hf hT).symm
    _ = _ := by rw [hident, sbxS9_restartHistory_law_eq hd Q lam h0 h1 l δ P K L hK μ hac hfin hKL (n + 1)]

#print axioms sbxS9_original_records_law_eq_restart_of_identification

/-- The joint set where the first regeneration time is infinite. -/
def sbxS9RegenerationBadSet {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) :
    Set ((Vec d × FieldPair d) × CoupledSample d) :=
  {z | firstRegenerationTime Δ lam R z.2 i = ⊤}

theorem sbxS9_measurableSet_regenerationBadSet {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) : MeasurableSet (sbxS9RegenerationBadSet Δ lam R i) :=
  measurableSet_eq_fun ((measurable_firstRegenerationTime Δ lam R i).comp
    measurable_snd) measurable_const

/-- Joint nullity for the normalized kernel implies finiteness for the original
kernel on its probability fibres. -/
theorem sbxS9_rawKernel_ae_finite_of_joint_nullity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hnull : ((volume : Measure (Vec d)).prod Q.measure ⊗ₘ
      Probability.probabilityPart K)
        (sbxS9RegenerationBadSet (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd)) = 0) :
    ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, ∀ᵐ b ∂K p,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) b
        (Renewal.forceCoord hd) ≠ ⊤ := by
  have hjoint : ∀ᵐ z ∂((volume : Measure (Vec d)).prod Q.measure ⊗ₘ
      Probability.probabilityPart K),
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) z.2
        (Renewal.forceCoord hd) ≠ ⊤ := by
    apply ae_iff.mpr
    simpa only [not_not, sbxS9RegenerationBadSet] using hnull
  have hf := Measure.ae_ae_of_ae_compProd hjoint
  filter_upwards [hf, hK.1.2] with p hp hprob
  let : IsProbabilityMeasure (K p) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure] at hp
  exact hp

/-- Conditional finite-history consumer for normalized joint nullity. -/
theorem sbxS9_restartHistory_ae_finite_of_joint_nullity
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d))
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d))))
    (hnull : ((volume : Measure (Vec d)).prod Q.measure ⊗ₘ
      Probability.probabilityPart K)
        (sbxS9RegenerationBadSet (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd)) = 0) (n : ℕ) :
    ∀ᵐ z ∂sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) μ K n,
      sbxS9HistoryFinite (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) n z := by
  exact sbxS9_restartHistory_ae_finite_of_scope hscope hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK hD μ hμ
    (sbxS9_rawKernel_ae_finite_of_joint_nullity hd Q lam h0 h1 l δ P K hK hnull) n

/-- Joint nullity yields finite histories at both source initial laws, at every
finite restart depth. -/
theorem sbxS9_both_restartHistories_ae_finite_of_joint_nullity
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hnull : ((volume : Measure (Vec d)).prod Q.measure ⊗ₘ
      Probability.probabilityPart K)
        (sbxS9RegenerationBadSet (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd)) = 0) :
    ∀ n : ℕ, ∀ μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × CoupledSample d))),
      ∀ᵐ z ∂sbxS9RestartHistoryLaw (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) μ K n,
        sbxS9HistoryFinite (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) n z := by
  intro n μ hμ
  exact sbxS9_restartHistory_ae_finite_of_joint_nullity hscope hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hD μ hμ hnull n

#print axioms sbxS9RegenerationBadSet
#print axioms sbxS9_measurableSet_regenerationBadSet
#print axioms sbxS9_rawKernel_ae_finite_of_joint_nullity
#print axioms sbxS9_restartHistory_ae_finite_of_joint_nullity
#print axioms sbxS9_both_restartHistories_ae_finite_of_joint_nullity

/-- The actual physical environment and coupled sample restarted at an iterate. -/
def sbxS9PhysicalRestart {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (k : ℕ) (q : FieldPair d × CoupledSample d) : FieldPair d × CoupledSample d :=
  let t := (Regeneration.regenerationTime Δ lam R q.2 i k).toNNReal
  let a := q.2.1 t
  (translate a q.1, recenterSample a (sampleTimeShift Δ q.2 t))

/-- The restart map retains the actual field, path and Bernoulli sequence. -/
theorem sbxS9_measurable_physicalRestart {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (k : ℕ) : Measurable (sbxS9PhysicalRestart Δ lam R i k) := by
  exact (measurable_regeneration_environment Δ lam R i k).prodMk
    ((measurable_regeneration_recentered_sample Δ lam R i k).comp measurable_snd)

/-- At restart index zero, the restarted clock starts at zero and the
original clock retains its index. -/
theorem sbxS9_physicalRestart_time_zero {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (k : ℕ) (q : FieldPair d × CoupledSample d)
    : Regeneration.regenerationTime Δ lam R (sbxS9PhysicalRestart Δ lam R i k q).2 i 0 ≠ ⊤ ∧
    Regeneration.regenerationTime Δ lam R q.2 i (k + 0) =
      Regeneration.regenerationTime Δ lam R q.2 i k +
        Regeneration.regenerationTime Δ lam R (sbxS9PhysicalRestart Δ lam R i k q).2 i 0 := by
  simp [Regeneration.regenerationTime]

#print axioms sbxS9_physicalRestart_time_zero
/-- A finite regeneration time has the exact additive absolute coin index. -/
theorem sbxS9_regeneration_gridIndex_add {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d) (k : ℕ) (z : CoupledSample d)
    (hk : Regeneration.regenerationTime Δ lam R z i k ≠ ⊤) (u : ℝ≥0) :
    gridIndex Δ ((Regeneration.regenerationTime Δ lam R z i k).toNNReal + u) =
      gridIndex Δ (Regeneration.regenerationTime Δ lam R z i k).toNNReal + gridIndex Δ u := by
  obtain ⟨n, hn⟩ := regenerationTime_mem_grid Δ hΔ lam R z i k hk
  simp only [hn, ENNReal.toNNReal_coe]
  rw [gridIndex_grid_add Δ hΔ n u, gridIndex_mul Δ hΔ n]

#print axioms sbxS9_regeneration_gridIndex_add
/-- One restart step corresponds to the next original regeneration index. -/
theorem sbxS9_physicalRestart_time_one {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (k : ℕ) (q : FieldPair d × CoupledSample d)
    (hk : Regeneration.regenerationTime Δ lam R q.2 i k ≠ ⊤)
    (hnext : Regeneration.regenerationTime Δ lam R q.2 i (k + 1) ≠ ⊤) :
    Regeneration.regenerationTime Δ lam R (sbxS9PhysicalRestart Δ lam R i k q).2 i 1 ≠ ⊤ ∧
    Regeneration.regenerationTime Δ lam R q.2 i (k + 1) =
      Regeneration.regenerationTime Δ lam R q.2 i k +
        Regeneration.regenerationTime Δ lam R (sbxS9PhysicalRestart Δ lam R i k q).2 i 1 := by
  have heq : Regeneration.regenerationTime Δ lam R (sbxS9PhysicalRestart Δ lam R i k q).2 i 1 =
      firstRegenerationTime Δ lam R
        (sampleTimeShift Δ q.2 (Regeneration.regenerationTime Δ lam R q.2 i k).toNNReal) i := by
    rw [Regeneration.regenerationTime_one]
    exact firstRegenerationTime_recenterSample Δ lam R i _ _
  have hstep := regenerationTime_succ_eq Δ lam R q.2 i k hk
  constructor
  · intro h
    apply hnext
    rw [hstep, ← heq, h, add_top]
  · rw [hstep, heq]

#print axioms sbxS9_physicalRestart_time_one
/-- Coupled time shifts compose at an original grid time, including coins. -/
theorem sbxS9_sampleTimeShift_grid_add {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (z : CoupledSample d) (n : ℕ) (u : ℝ≥0) :
    sampleTimeShift Δ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) u =
      sampleTimeShift Δ z ((n : ℝ≥0) * Δ + u) := by
  apply Prod.ext
  · ext s x
    change z.1 ((n : ℝ≥0) * Δ + (u + s)) x = z.1 (((n : ℝ≥0) * Δ + u) + s) x
    rw [add_assoc]
  · funext a
    change z.2 (gridIndex Δ ((n : ℝ≥0) * Δ) + (gridIndex Δ u + a)) =
      z.2 (gridIndex Δ ((n : ℝ≥0) * Δ + u) + a)
    rw [gridIndex_grid_add Δ hΔ n u, gridIndex_mul Δ hΔ n, Nat.add_assoc]

#print axioms sbxS9_sampleTimeShift_grid_add
#print axioms sbxS9PhysicalRestart
#print axioms sbxS9_measurable_physicalRestart

#lint-

end EinsteinFull.Blueprint
