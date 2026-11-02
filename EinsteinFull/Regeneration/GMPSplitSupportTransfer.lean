import EinsteinFull.Regeneration.GMPSplitEndpointTransfer
import EinsteinRelation.Probability.PathMaps

/-! # Successful split paths on every deterministic interval

The literal source first-coin support and current-coin path restart imply the
actual simultaneous all-grid-interval support. The path marginal's starting
point is used explicitly. This constructs no joint environment kernel.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP

/-- Staying in the open Euclidean coupling ball throughout a compact time
interval is measurable, with its center equal to the path's starting point.
Compact-open topology preserves the strict boundary convention. -/
theorem measurableSet_source_split_support {d : ℕ} (Δ : ℝ≥0) (i : Fin d) (R : ℝ) :
    MeasurableSet {γ : Path d |
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R (γ 0)} := by
  have hnorm : Continuous (fun v : Vec d => euclideanNorm v) := by
    have hs : Continuous (fun v : Vec d => ∑ j, v j * v j) := by
      exact continuous_finset_sum _ (fun j _ => (continuous_apply j).mul (continuous_apply j))
    exact Real.continuous_sqrt.comp hs
  have hU : IsOpen (couplingRegion i R (0 : Vec d)) := by
    exact isOpen_lt
      (hnorm.comp (continuous_id.sub continuous_const)) continuous_const
  have hT : Continuous (fun γ : Path d =>
      (⟨fun t => γ t - γ 0, γ.continuous.sub continuous_const⟩ : Path d)) :=
    EinsteinRelation.Probability.continuous_path_recenter.comp
      ((continuous_eval_const 0).prodMk continuous_id)
  have ho := (ContinuousMap.isOpen_setOf_mapsTo (K := Set.Icc (0 : ℝ≥0) Δ) isCompact_Icc hU).preimage hT
  convert ho.measurableSet using 1
  ext γ
  change (∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R (γ 0)) ↔
    Set.MapsTo (fun t => γ t - γ 0) (Set.Icc 0 Δ) (couplingRegion i R 0)
  have heq (t : ℝ≥0) :
      γ t - γ 0 - ((0 : Vec d) + (5 * R) • unitVector i) =
        γ t - (γ 0 + (5 * R) • unitVector i) := by abel
  constructor
  · intro h t ht
    change euclideanNorm (γ t - γ 0 - ((0 : Vec d) + (5 * R) • unitVector i)) < 6 * R
    rw [heq]
    exact h t ht.2
  · intro h t ht
    have hv := h (Set.mem_Icc.mpr ⟨bot_le, ht⟩)
    change euclideanNorm (γ t - γ 0 - ((0 : Vec d) + (5 * R) • unitVector i)) < 6 * R at hv
    rw [heq] at hv
    exact hv

/-- The source's successful conditional path law begins at its displayed
spatial point, by absolute continuity of conditioning and the path marginal. -/
theorem source_split_conditional_starts_at {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    {K : Vec d → Measure (CoupledSample d)}
    (hK : IsSourceSplitCoupling P Δ δ R i K)
    (hstart : ∀ x, ∀ᵐ γ ∂P x, γ 0 = x) (x : Vec d) (b : Bool) :
    ∀ᵐ γ ∂conditionalPathLaw K x b, γ 0 = x := by
  have h := ae_of_ae_map measurable_fst.aemeasurable
    (by rw [(hK x).2.1]; exact hstart x)
  apply (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_eq_fun (measurable_pathPosition 0) measurable_const)).2
  exact ProbabilityTheory.cond_absolutelyContinuous.ae_le h

/-- Source current-coin path restart transports successful support to EVERY
split interval on ONE full-measure event, with the actual starting position
and the source strict Euclidean tube throughout the closed time interval. -/
theorem source_split_successful_bridge_support {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    (K : CoupledQuenchedLaws d) (ω : FieldPair d)
    (hK : IsSourceSplitCoupling P Δ δ R i (fun x => K (x, ω)))
    (hstart : ∀ x, ∀ᵐ γ ∂P x, γ 0 = x) (x : Vec d) :
    SuccessfulBridgeSupportAt Δ i R K (x, ω) := by
  classical
  let S : Set (Path d) := {γ | ∀ t : ℝ≥0, t ≤ Δ →
    γ t ∈ couplingRegion i R (γ 0)}
  have hS : MeasurableSet S := measurableSet_source_split_support Δ i R
  let F : Path d → ℝ := Sᶜ.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hS.compl
  have hFbound : ∀ γ, |F γ| ≤ 1 := by
    intro γ
    by_cases hγ : γ ∈ S <;> simp [F, hγ]
  have hbF : BoundedRealTest F := ⟨1, hFbound⟩
  have hFzero (y : Vec d) :
      (∫ γ, F γ ∂conditionalPathLaw (fun y => K (y, ω)) y true) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [source_split_conditional_starts_at hK hstart y true,
      (hK y).2.2.2.2.2.1] with γ hγ₀ hγ
    have hmem : γ ∈ S := by simpa only [S, Set.mem_setOf_eq, hγ₀] using hγ
    simp [F, hmem]
  have hall : ∀ n : ℕ, ∀ᵐ z ∂K (x, ω),
      z.2 n = true → pathTimeShift z.1 ((n : ℝ≥0) * Δ) ∈ S := by
    intro n
    let χ : CoupledSample d → ℝ := fun z => if z.2 n = true then 1 else 0
    have hχ : @Measurable (CoupledSample d) ℝ
        (currentCoinHistory Δ n) inferInstance χ := by
      have hc : @Measurable (CoupledSample d) Bool
          (currentCoinHistory Δ n) inferInstance (fun z => z.2 n) :=
        Measurable.of_comap_le le_sup_right
      exact measurable_const.ite (measurableSet_eq_fun hc measurable_const) measurable_const
    have hbχ : BoundedRealTest χ := by
      refine ⟨1, fun z => ?_⟩
      simp only [χ]
      split <;> norm_num
    have hr := ((hK x).2.2.2.2.1 n χ F hχ hbχ hF hbF).2
    have hrzero : (∫ z, χ z * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))
        ∂K (x, ω)) = 0 := by
      rw [hr]
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall fun z => by
        by_cases hz : z.2 n = true
        · simp only [hz, hFzero, mul_zero, Pi.zero_apply]
        · simp [χ, hz]
    letI : IsProbabilityMeasure (K (x, ω)) := (hK x).1
    have hmeas : Measurable (fun z : CoupledSample d =>
        χ z * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) :=
      (hχ.mono (sup_le
        (EinsteinRelation.Probability.finiteHistorySigma_le Δ n)
        (Measurable.comap_le ((measurable_pi_apply n).comp measurable_snd))) le_rfl).mul
        (hF.comp (EinsteinRelation.Probability.continuous_path_time_shift.measurable.comp
          (measurable_const.prodMk measurable_fst)))
    have hint : Integrable (fun z : CoupledSample d =>
        χ z * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ))) (K (x, ω)) := by
      apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun z => by
        by_cases hz : z.2 n = true
        · simpa [χ, hz, Real.norm_eq_abs] using hFbound
            (pathTimeShift z.1 ((n : ℝ≥0) * Δ))
        · simp [χ, hz]
    have hnonneg : 0 ≤ fun z : CoupledSample d =>
        χ z * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) := by
      intro z
      apply mul_nonneg
      · simp only [χ]; split <;> norm_num
      · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hae := (integral_eq_zero_iff_of_nonneg hnonneg hint).1 hrzero
    filter_upwards [hae] with z hz hbit
    by_contra hbad
    have hone : χ z * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) = 1 := by
      simp [χ, hbit, F, hbad]
    rw [hone] at hz
    norm_num at hz
  filter_upwards [ae_all_iff.2 hall] with z hz
  intro n hbit t ht₀ ht₁
  have hu : t - (n : ℝ≥0) * Δ ≤ Δ := by
    have h := tsub_le_tsub_right ht₁ ((n : ℝ≥0) * Δ)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_left] using h
  have h := hz n hbit (t - (n : ℝ≥0) * Δ) hu
  simpa only [pathTimeShift, ContinuousMap.coe_mk, add_zero,
    add_tsub_cancel_of_le ht₀] using h

/-- The full successful-bridge predicate retains the actual origin clause and
product-a.e. starting-point clause once the joint kernel exists. -/
theorem source_split_joint_bridge_support {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (P : QuenchedPathLaws d)
    {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d} (K : CoupledQuenchedLaws d)
    (hK : ∀ᵐ ω ∂Q,
      IsSourceSplitCoupling (fun x => P (x, ω)) Δ δ R i (fun x => K (x, ω)))
    (hstart : ∀ᵐ ω ∂Q, ∀ x, ∀ᵐ γ ∂P (x, ω), γ 0 = x) :
    HasSuccessfulBridgeSupport Q Δ i R K := by
  have hp : ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q),
      IsSourceSplitCoupling (fun x => P (x, xω.2)) Δ δ R i
        (fun x => K (x, xω.2)) ∧
      ∀ x, ∀ᵐ γ ∂P (x, xω.2), γ 0 = x :=
    Measure.quasiMeasurePreserving_snd.ae (hK.and hstart)
  constructor
  · filter_upwards [hK, hstart] with ω h h₀
    exact source_split_successful_bridge_support K ω h h₀ 0
  · filter_upwards [hp] with xω h
    exact source_split_successful_bridge_support K xω.2 h.1 h.2 xω.1

/-- For the actual reduced GMP process, the source split construction gives
all five probability, marginal, fresh-bit, successful-support and endpoint
clauses. Full joint path/coin restart and the canonical bridge formula are
separate internal obligations. -/
theorem source_split_reduced_kernel_properties {d : ℕ} (hd : 2 ≤ d)
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) {lam l δ : ℝ}
    (h₀ : 0 < lam) (h₁ : lam ≤ 1) (hl : 1 ≤ l) (hδ : 0 ≤ δ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀.le h₁ P)
    (hK : ∀ᵐ ω ∂Q.measure,
      IsSourceSplitCoupling (fun x => P (x, ω)) (Renewal.regenDelta lam)
        δ (l / lam) (Renewal.forceCoord hd) (fun x => K (x, ω))) :
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      HasFreshBits Q.measure (Renewal.regenDelta lam) δ K ∧
      HasSuccessfulBridgeSupport Q.measure (Renewal.regenDelta lam)
        (Renewal.forceCoord hd) (l / lam) K ∧
      HasUniformSuccessfulEndpoint Q.measure (Renewal.regenDelta lam)
        δ (l / lam) (Renewal.forceCoord hd) K := by
  have hstart : ∀ᵐ ω ∂Q.measure, ∀ x, ∀ᵐ γ ∂P (x, ω), γ 0 = x := by
    filter_upwards [hP] with ω hω
    obtain ⟨_, r, hr⟩ := hω
    intro x
    rw [hr x]
    exact r.pathLaw_starts_at x
  have hR : 0 < l / lam := div_pos (lt_of_lt_of_le zero_lt_one hl) h₀
  obtain ⟨hp, hm, hb, he⟩ := source_split_joint_kernel_properties Q.measure P K hK hδ hR
  exact ⟨hp, hm, hb, source_split_joint_bridge_support Q.measure P K hK hstart, he⟩

end EinsteinFull.Regeneration
