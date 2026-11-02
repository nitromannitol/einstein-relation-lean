import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.Work.W1.RegenerationReuseSupport
import EinsteinRelation.Regeneration.SpatialRecenterEquiv
import EinsteinRelation.Regeneration.KilledFutureConditionalMean
import EinsteinRelation.Regeneration.RecenterNoBacktracking

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- Both literal objects are measurable, including on the infinite-time branch. -/
theorem c19_clean_coupling_scope_measurable {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (k : ℕ) :
    Measurable (regenerationTime hd lam l k) ∧
      Measurable (regenerationRecord hd lam l k) :=
  ⟨measurable_regenerationTime hd lam l k, measurable_regenerationRecord hd lam l k⟩

/-- Pointwise characterization of finite iterates, retaining the exact `2*k`
bound and both restricted reduced fields in the record. -/
theorem c19_clean_coupling_scope_finite_iff_grid_record {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l) (k : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) :
    regenerationTime hd lam l k q.2 ≠ ⊤ ↔
      ∃ n : ℕ, 2 * k ≤ n ∧
        regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
        regenerationRecord hd lam l k q =
          Regeneration.futureRecord (Regeneration.Renewal.regenDelta lam) (l / lam)
            q.1 q.2 (Regeneration.Renewal.forceCoord hd)
            ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) := by
  constructor
  · intro hfin
    have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
      Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hlam))
    obtain ⟨n, hn⟩ := Regeneration.regenerationTime_mem_grid _ hΔ lam (l / lam)
      q.2 (Regeneration.Renewal.forceCoord hd) k hfin
    change regenerationTime hd lam l k q.2 = _ at hn
    have hb := Regeneration.nat_two_step_le_regenerationTime _ hΔ lam (l / lam)
      hlam (div_pos hl hlam) q.2 (Regeneration.Renewal.forceCoord hd) k
    change (k : ℝ≥0∞) * (2 * (Regeneration.Renewal.regenDelta lam : ℝ≥0∞)) ≤
      regenerationTime hd lam l k q.2 at hb
    rw [hn] at hb
    have hb' : ((2 * k : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam ≤
        (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam := by
      have hb'' : ((2 * k : ℕ) : ℝ≥0∞) *
          (Regeneration.Renewal.regenDelta lam : ℝ≥0∞) ≤
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm]
          using hb
      exact_mod_cast hb''
    have hkn : 2 * k ≤ n := by
      exact_mod_cast (mul_le_mul_iff_left₀ hΔ).mp hb'
    refine ⟨n, hkn, hn, ?_⟩
    change Regeneration.futureRecord _ _ q.1 q.2 _
      (regenerationTime hd lam l k q.2).toNNReal = _
    rw [hn, ENNReal.toNNReal_coe]
  · rintro ⟨n, _, hn, _⟩
    rw [hn]
    exact ENNReal.coe_ne_top

/-- Under any measure, the finite-grid/record conclusion is equivalent to
almost-everywhere finiteness; this equivalence supplies no finiteness premise. -/
theorem c19_clean_coupling_scope_ae_finite_iff_grid_record {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l) (k : ℕ)
    (ρ : Measure (FieldPair d × Regeneration.CoupledSample d)) :
    (∀ᵐ q ∂ρ, regenerationTime hd lam l k q.2 ≠ ⊤) ↔
      ∀ᵐ q ∂ρ, ∃ n : ℕ, 2 * k ≤ n ∧
        regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
        regenerationRecord hd lam l k q =
          Regeneration.futureRecord (Regeneration.Renewal.regenDelta lam) (l / lam)
            q.1 q.2 (Regeneration.Renewal.forceCoord hd)
            ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) :=
  Filter.eventually_congr (Filter.Eventually.of_forall fun q =>
    c19_clean_coupling_scope_finite_iff_grid_record hd lam l hlam hl k q)

/-- The two-law finiteness obligation is exactly its annealed part, since the
literal D-conditioned law is absolutely continuous with respect to that law. -/
theorem c19_clean_coupling_scope_both_laws_finite_iff {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) (k : ℕ) :
    (∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      ∀ᵐ q ∂ρ, regenerationTime hd lam l k q.2 ≠ ⊤) ↔
      ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
        regenerationTime hd lam l k q.2 ≠ ⊤ := by
  constructor
  · intro h
    exact h _ (Set.mem_insert _ _)
  · intro h ρ hρ
    rcases Set.mem_insert_iff.mp hρ with hρ | hρ
    · subst ρ
      exact h
    · have hρ' := Set.mem_singleton_iff.mp hρ
      subst ρ
      exact (regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK hD).ae_le h

/-- Assemble the scope statement from the exact all-cycle finiteness producer.
This is support only until the producer is proved. -/
theorem c19_s3_clean_scope_assembly
    (hfinite : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt)
      {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ k : ℕ, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
        regenerationTime hd lam l k q.2 ≠ ⊤)
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  dsimp only
  intro k
  refine ⟨(c19_clean_coupling_scope_measurable hd lam l k).1,
    (c19_clean_coupling_scope_measurable hd lam l k).2, ?_⟩
  intro ρ hρ
  apply (c19_clean_coupling_scope_ae_finite_iff_grid_record hd lam l h0 hl k ρ).mp
  exact (c19_clean_coupling_scope_both_laws_finite_iff hd Q lam l K hK.1 hD k).mpr
    (hfinite htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD k) ρ hρ


/-- The future record commutes with recentering. -/
theorem c19_clean_spatialFutureRecord_recenter {d : ℕ} (R : ℝ) (i : Fin d)
    (y : Vec d) (ω : FieldPair d) (z : CoupledSample d) :
    spatialFutureRecord R i (0, translate y ω) (recenterSample y z) =
      spatialFutureRecord R i (y, ω) z := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    simp only [spatialFutureRecord, recenterSample, ContinuousMap.coe_mk, sub_zero]
  · apply Prod.ext
    · rfl
    · funext x
      simp only [spatialFutureRecord, reduce_translate, translate_zero]

/-- The killed test commutes with recentering. -/
theorem c19_clean_killedFutureTest_recenter_origin {d : ℕ} (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (y : Vec d) (ω : FieldPair d) (z : CoupledSample d) :
    killedFutureTest R i Φ ((0, translate y ω), recenterSample y z) =
      killedFutureTest R i Φ ((y, ω), z) := by
  unfold killedFutureTest
  rw [noBacktracking_recenterSample_iff, c19_clean_spatialFutureRecord_recenter]

/-- Transport the future-kernel local version using supplied spatial covariance. -/
theorem c19_s3_clean_future_one_of_future_kernel
    (hFutureKernel : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hcov : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      (K p).map (recenterSample p.1) = K (0, translate p.1 p.2)) :
    ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ B : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | y (Renewal.forceCoord hd) - 2 * (l / lam) ≤
        x (Renewal.forceCoord hd)}] B ∧
      (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) =ᵐ[Q.measure] B := by
  obtain ⟨B, hB, hBo⟩ := hFutureKernel d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hcov] with y hy
  have hmap : ∀ᵐ ω ∂Measure.map (translate y) Q.measure,
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ))
        ((0, ω), z) ∂K (0, ω)) = B ω := by
    rw [Q.stationary y]
    exact hBo
  have ht := ae_of_ae_map (Probability.measurable_translate y).aemeasurable hmap
  refine ⟨fun ω => B (translate y ω), ?_, ?_⟩
  · apply (hB.comp (Probability.measurable_translate_local y _)).mono
      (Probability.localSigma_mono ?_) le_rfl
    rintro x ⟨z, hz, rfl⟩
    change -2 * (l / lam) ≤ z (Renewal.forceCoord hd) at hz
    change y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ (y + z) (Renewal.forceCoord hd)
    simp only [Pi.add_apply]
    linarith
  · filter_upwards [hy, ht] with ω hc hb
    have hmrec : Measurable (recenterSample y) :=
      measurable_recenterSample.comp (measurable_const.prodMk measurable_id)
    have hmtest : Measurable (fun z => killedFutureTest (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) ((0, translate y ω), z)) :=
      (measurable_killedFutureTest (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ))
        measurable_const).comp (measurable_const.prodMk measurable_id)
    rw [← hb, ← hc, integral_map hmrec.aemeasurable hmtest.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
      (c19_clean_killedFutureTest_recenter_origin (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) y ω z).symm)

end EinsteinFull.Blueprint
