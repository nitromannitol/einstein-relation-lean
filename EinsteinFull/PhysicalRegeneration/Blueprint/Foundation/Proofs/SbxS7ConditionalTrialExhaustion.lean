import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation
namespace ConditionalTrialExhaustion
end ConditionalTrialExhaustion
open scoped Function
namespace ConditionalTrialExhaustion
end ConditionalTrialExhaustion
namespace ConditionalTrialExhaustion
end ConditionalTrialExhaustion
open Regeneration in
/-- The physical-kernel version of
`EinsteinFull.Blueprint.coupling_scope_joint_history_success_endpoint`. -/
theorem coupling_scope_joint_history_success_endpoint_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (m : ℕ) (H : FieldPair d × CoupledSample d → ℝ)
    (hH : @Measurable (FieldPair d × CoupledSample d) ℝ
      (MeasurableSpace.prod inferInstance (finiteHistorySigma Δ m)) inferInstance H)
    (hbH : BoundedRealTest H)
    (Ψ : (Vec d × FieldPair d) × CoupledSample d → ℝ)
    (hΨ : Measurable Ψ) (hbΨ : BoundedRealTest Ψ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B)
    (hBeq : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      B xω = ∫ w, Ψ (xω, w) ∂K xω) :
    (∫ q, H q * (if q.2.2 m = true then (1 : ℝ) else 0) *
      Ψ ((q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), q.1),
        sampleTimeShift Δ q.2 (((m + 1 : ℕ) : ℝ≥0) * Δ))
      ∂annealedCoupledLaw Q.measure K) =
      ∫ ω, δ * ∫ z, H (ω, z) * endpointAverage i R (z.1 ((m : ℝ≥0) * Δ))
        (fun y => B (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  let t : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * Δ
  have ht : 0 < t := mul_pos (by positivity) hΔ
  have hprob := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae_phys hd Q lam h0 h1 P K hK hpath hP t ht _ hK.2)
  have hversion := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae_phys hd Q lam h0 h1 P K hK hpath hP t ht _ hBeq)
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    H q * (if q.2.2 m = true then 1 else 0) *
      Ψ ((q.2.1 t, q.1), sampleTimeShift Δ q.2 t)
  have hHfull : Measurable H :=
    hH.mono (sup_le_sup le_rfl
      (MeasurableSpace.comap_mono (Probability.finiteHistorySigma_le Δ m))) le_rfl
  have hF : Measurable F := by
    exact (hHfull.mul
      (Measurable.ite (((measurable_pi_apply m).comp measurable_snd.snd)
        (measurableSet_singleton true)) measurable_const measurable_const)).mul
      (hΨ.comp (((((continuous_eval_const t).measurable.comp measurable_snd.fst)).prodMk
        measurable_fst).prodMk ((measurable_sampleTimeShift Δ).comp
          (measurable_const.prodMk measurable_snd))))
  have hbF : BoundedRealTest F := by
    obtain ⟨CH, hCH⟩ := hbH
    obtain ⟨CP, hCP⟩ := hbΨ
    refine ⟨max CH 0 * max CP 0, fun q => ?_⟩
    dsimp [F]
    by_cases hq : q.2.2 m = true
    · simp only [hq, ↓reduceIte, mul_one, abs_mul]
      exact mul_le_mul ((hCH _).trans (le_max_left _ _))
        ((hCP _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · simpa [hq] using
        (mul_nonneg (le_max_right CH (0 : ℝ)) (le_max_right CP (0 : ℝ)))
  change (∫ q, F q ∂annealedCoupledLaw Q.measure K) = _
  rw [integral_annealedCoupledLaw Q.measure K hK F hF hbF]
  apply integral_congr_ae
  filter_upwards [hK.1, hRestart.1, hUniform.1, hprob, hversion] with ω hω hr hu hp hv
  have := hω
  exact integral_future_eq_uniformEndpointAverage Δ δ R i K (0, ω) hr hu m hp (fun z => H (ω, z)) (hH.comp measurable_prodMk_left)
    (by obtain ⟨C, hC⟩ := hbH; exact ⟨C, fun z => hC (ω, z)⟩)
    (fun q => Ψ ((q.1, ω), q.2))
    (hΨ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
    (by obtain ⟨C, hC⟩ := hbΨ; exact ⟨C, fun q => hC _⟩)
    (fun y => B (y, ω)) (hB.comp measurable_prodMk_right)
    (by obtain ⟨C, hC⟩ := hbB; exact ⟨C, fun y => hC _⟩) hv

/-- The physical-kernel version of
`EinsteinFull.Blueprint.coupling_scope_joint_burn_success_killed_future_uniform`. -/
theorem coupling_scope_joint_burn_success_killed_future_uniform_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      ∀ (H : FieldPair d × Regeneration.CoupledSample d → ℝ),
      @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
        (MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)))
        inferInstance H → Regeneration.BoundedRealTest H →
      (∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) *
        (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
        Regeneration.killedFutureTest R i Φ
          ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
            Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ ω, δ * ∫ z, (H (ω, z) * A.indicator (fun _ => (1 : ℝ)) z) *
        Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => B (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨C, _, B, hB, hbB, _, hBp⟩ :=
    Regeneration.exists_globally_bounded_measurable_killed_future_version
      Q.measure K hK.1 R i Φ hΦ hbΦ
  have hBp' : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p := by
    filter_upwards [hBp] with p hp
    simpa only [Regeneration.killedFutureTest, Regeneration.spatialFutureRecord] using hp
  refine ⟨B, hB, ⟨C, hbB⟩, hBp', ?_⟩
  intro H hH hbH
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    H q * A.indicator (fun _ => 1) q.2
  have hG : @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
      (MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)))
      inferInstance G := by
    have hA := coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h₀ hR m i J N k
    exact hH.mul ((measurable_const.indicator hA).comp measurable_snd)
  have hbG : Regeneration.BoundedRealTest G := by
    obtain ⟨D, hD⟩ := hbH
    refine ⟨max D 0, fun q => ?_⟩
    by_cases hq : q.2 ∈ A
    · simpa [G, Set.indicator_of_mem hq] using (hD q).trans (le_max_left D 0)
    · simp [G, Set.indicator_of_notMem hq]
  exact coupling_scope_joint_history_success_endpoint_phys hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1 Δ hΔ δ R i hK.2.2.2.2.1
    hK.2.2.2.2.2.2.1 (m + k) G hG hbG
    (Regeneration.killedFutureTest R i Φ)
    (Regeneration.measurable_killedFutureTest R i Φ hΦ)
    (Regeneration.boundedRealTest_killedFutureTest R i Φ hbΦ) B hB ⟨C, hbB⟩ hBp'

/-- The physical-kernel version of
`EinsteinFull.Blueprint.coupling_scope_joint_burn_success_killed_future_annealed`. -/
theorem coupling_scope_joint_burn_success_killed_future_annealed_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      ∀ (H : FieldPair d × Regeneration.CoupledSample d → ℝ),
      @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
        (MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)))
        inferInstance H → Regeneration.BoundedRealTest H →
      (∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) *
        (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
        Regeneration.killedFutureTest R i Φ
          ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
            Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) *
        (δ * Regeneration.endpointAverage i R (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => B (y, q.1))) ∂Regeneration.annealedCoupledLaw Q.measure K := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨B, hB, hbB, hBp, hdis⟩ :=
    coupling_scope_joint_burn_success_killed_future_uniform_phys hd Q lam h₀ h₁ l δ hl P K hK
      m J N k Φ hΦ hbΦ
  refine ⟨B, hB, hbB, hBp, ?_⟩
  intro H hH hbH
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    H q * A.indicator (fun _ => 1) q.2
  have hHfull : Measurable H := hH.mono (sup_le_sup le_rfl
    (MeasurableSpace.comap_mono (Probability.finiteHistorySigma_le Δ (m + k)))) le_rfl
  have hA := coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
    Δ hΔ lam R h₀ hR m i J N k
  have hAfull : MeasurableSet A := Probability.finiteHistorySigma_le Δ (m + k) A hA
  have hG : Measurable G := hHfull.mul ((measurable_const.indicator hAfull).comp measurable_snd)
  have hbG : Regeneration.BoundedRealTest G := by
    obtain ⟨D, hD⟩ := hbH
    refine ⟨max D 0, fun q => ?_⟩
    by_cases hq : q.2 ∈ A
    · simpa [G, Set.indicator_of_mem hq] using (hD q).trans (le_max_left D 0)
    · simp [G, Set.indicator_of_notMem hq]
  exact (hdis H hH hbH).trans
    (coupling_scope_integral_mul_endpoint_kernel Q.measure K hK.1 i R hR
      (((m + k : ℕ) : ℝ≥0) * Δ) δ B hB hbB G hG hbG).symm

/-- The physical-kernel version of
`EinsteinFull.Blueprint.coupling_scope_burn_future_setIntegral_kernel`. -/
theorem coupling_scope_burn_future_setIntegral_kernel_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      ∀ s : Set (FieldPair d × Regeneration.CoupledSample d),
      MeasurableSet[couplingScopeAnnealedHistory Δ (m + k)] s →
      (∫ q in s ∩ {q | q.2 ∈ A},
        (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
        Regeneration.killedFutureTest R i Φ
          ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
            Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ q in s ∩ {q | q.2 ∈ A},
        δ * Regeneration.endpointAverage i R (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => B (y, q.1)) ∂Regeneration.annealedCoupledLaw Q.measure K := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨B, hB, hbB, hBp, hdis⟩ :=
    coupling_scope_joint_burn_success_killed_future_annealed_phys hd Q lam h₀ h₁ l δ hl P K hK
      m J N k Φ hΦ hbΦ
  refine ⟨B, hB, hbB, hBp, ?_⟩
  intro s hs
  have hle : couplingScopeAnnealedHistory (d := d) Δ (m + k) ≤
      MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)) :=
    measurable_snd.comap_le
  have hS : MeasurableSet s := coupling_scope_annealed_history_le Δ (m + k) s hs
  have hA := coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
    Δ hΔ lam R h₀ hR m i J N k
  have hAfull : MeasurableSet A := Probability.finiteHistorySigma_le Δ (m + k) A hA
  have hSA : MeasurableSet (s ∩ {q : FieldPair d × Regeneration.CoupledSample d | q.2 ∈ A}) :=
    hS.inter (hAfull.preimage measurable_snd)
  let H : FieldPair d × Regeneration.CoupledSample d → ℝ := s.indicator (fun _ => 1)
  have hH : @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
      (MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)))
      inferInstance H := measurable_const.indicator (hle s hs)
  have hbH : Regeneration.BoundedRealTest H := by
    refine ⟨1, fun q => ?_⟩
    by_cases hq : q ∈ s <;> simp [H, hq]
  have hh := hdis H hH hbH
  let f : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    (if q.2.2 (m + k) = true then 1 else 0) *
      Regeneration.killedFutureTest R i Φ
        ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
          Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))
  let g : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    δ * Regeneration.endpointAverage i R (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
      (fun y => B (y, q.1))
  have hL : (fun q => (H q * A.indicator (fun _ => (1 : ℝ)) q.2) * f q) =
      (s ∩ {q | q.2 ∈ A}).indicator f := by
    funext q
    by_cases hs' : q ∈ s <;> by_cases ha' : q.2 ∈ A <;>
      simp [H, hs', ha', Set.indicator_of_mem, Set.indicator_of_notMem]
  have hG : (fun q => (H q * A.indicator (fun _ => (1 : ℝ)) q.2) * g q) =
      (s ∩ {q | q.2 ∈ A}).indicator g := by
    funext q
    by_cases hs' : q ∈ s <;> by_cases ha' : q.2 ∈ A <;>
      simp [H, hs', ha', Set.indicator_of_mem, Set.indicator_of_notMem]
  have hh' : (∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) * f q
      ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) * g q
      ∂Regeneration.annealedCoupledLaw Q.measure K := by
    simpa only [f, g, mul_assoc] using hh
  rw [hL, hG, integral_indicator hSA, integral_indicator hSA] at hh'
  exact hh'

/-- The physical-kernel version of
`EinsteinFull.Blueprint.coupling_scope_burn_future_condExp_kernel`. -/
theorem coupling_scope_burn_future_condExp_kernel_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      ∀ᵐ q ∂μ, q.2 ∈ A →
        (μ[fun q => (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
          Regeneration.killedFutureTest R i Φ
            ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
              Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ)) | (couplingScopeAnnealedHistory (d := d) Δ (m + k))]) q =
        (μ[fun q => δ * Regeneration.endpointAverage i R
          (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) | (couplingScopeAnnealedHistory (d := d) Δ (m + k))]) q := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let A : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
  let t : ℝ≥0 := (((m + k + 1 : ℕ) : ℝ≥0) * Δ)
  let f : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    (if q.2.2 (m + k) = true then 1 else 0) *
      Regeneration.killedFutureTest R i Φ
        ((q.2.1 t, q.1), Regeneration.sampleTimeShift Δ q.2 t)
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  let : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hH := coupling_scope_annealed_history_le (d := d) Δ (m + k)
  have hA : MeasurableSet[(couplingScopeAnnealedHistory (d := d) Δ (m + k))] A :=
    (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h₀ hR m i J N k).preimage (Measurable.of_comap_le le_rfl)
  have hA' : MeasurableSet A := hH A hA
  have hfm : Measurable f := by
    exact (Measurable.ite (((measurable_pi_apply (m + k)).comp measurable_snd.snd)
      (measurableSet_singleton true)) measurable_const measurable_const).mul
      ((Regeneration.measurable_killedFutureTest R i Φ hΦ).comp
        ((((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk measurable_fst).prodMk
          ((Regeneration.measurable_sampleTimeShift Δ).comp
            (measurable_const.prodMk measurable_snd))))
  obtain ⟨C, hC⟩ := Regeneration.boundedRealTest_killedFutureTest R i Φ hbΦ
  have hf : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable (max C 0) (by
    filter_upwards with q
    by_cases hq : q.2.2 (m + k) = true
    · simpa [f, hq, Real.norm_eq_abs] using (hC _).trans (le_max_left C 0)
    · simp [f, hq, le_max_right C 0])
  obtain ⟨B, hB, hbB, hBp, hdis⟩ :=
    coupling_scope_burn_future_setIntegral_kernel_phys hd Q lam h₀ h₁ l δ hl P K hK m J N k Φ hΦ hbΦ
  refine ⟨B, hB, hbB, hBp, ?_⟩
  let g : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    δ * Regeneration.endpointAverage i R (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
      (fun y => B (y, q.1))
  have hg : Integrable g μ := (coupling_scope_endpoint_kernel_integrable Q.measure K hK.1
    i R hR (((m + k : ℕ) : ℝ≥0) * Δ) δ B hB hbB).2
  have heq : A.indicator (μ[g | (couplingScopeAnnealedHistory (d := d) Δ (m + k))]) =ᵐ[μ] μ[A.indicator f | (couplingScopeAnnealedHistory (d := d) Δ (m + k))] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hH (hf.indicator hA')
    · intro s hs hfin
      exact (integrable_condExp.indicator hA').integrableOn
    · intro s hs hfin
      rw [setIntegral_indicator hA', setIntegral_indicator hA']
      rw [setIntegral_condExp hH hg (hs.inter hA)]
      exact (hdis s hs).symm
    · have hm : StronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)]
          (μ[g | couplingScopeAnnealedHistory Δ (m + k)]) := stronglyMeasurable_condExp
      exact (hm.indicator hA).aestronglyMeasurable
  have hind := condExp_indicator hf hA
  filter_upwards [heq, hind] with q hq hi hqa
  have hqa' : q ∈ A := hqa
  have h := hq.trans hi
  simpa only [Set.indicator_of_mem hqa'] using h.symm

/-- The physical-kernel version of
`EinsteinFull.Blueprint.coupling_scope_burn_success_condExp_endpoint_kernel`. -/
theorem coupling_scope_burn_success_condExp_endpoint_kernel_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => 1) (p, z) ∂K p) ∧
      ∀ᵐ q ∂μ, q.2 ∈ A →
        (μ[({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
            couplingScopeAnnealedHistory Δ (m + k)]) q =
        (μ[fun q => δ * Regeneration.endpointAverage i R
          (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) |
            couplingScopeAnnealedHistory Δ (m + k)]) q := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  obtain ⟨B, hB, hbB, hBp, hcond⟩ :=
    coupling_scope_burn_future_condExp_kernel_phys hd Q lam h₀ h₁ l δ hl P K hK m J N k
      (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
  refine ⟨B, hB, hbB, hBp, ?_⟩
  have hpath (z : Regeneration.CoupledSample d) :
      Regeneration.pathTimeShift
        (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1
          (((k + 1 : ℕ) : ℝ≥0) * Δ) =
      Regeneration.pathTimeShift z.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ) := by
    ext t j
    simp only [Regeneration.sampleTimeShift, Regeneration.pathTimeShift, ContinuousMap.coe_mk]
    push_cast
    ring
  have hf : (fun q : FieldPair d × Regeneration.CoupledSample d =>
      (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
      Regeneration.killedFutureTest R i (fun _ => 1)
        ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
          Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))) =
      ({p : FieldPair d × Regeneration.CoupledSample d |
        p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift
            (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
              (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) := by
    funext q
    rw [Regeneration.killedFutureTest_sampleTimeShift]
    simp only [hpath]
    by_cases hc : q.2.2 (m + k) = true <;>
      by_cases hn : Regeneration.NoBacktracking R
        (Regeneration.pathTimeShift q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ)) i <;>
      simp only [Nat.cast_add, Nat.cast_one] at hn <;>
      simp [hc, hn, Set.indicator_of_mem, Set.indicator_of_notMem]
  rw [hf] at hcond
  exact hcond

/-- The physical-kernel version of
`EinsteinFull.Blueprint.coupling_scope_burn_success_integrable_history_endpoint_kernel`. -/
theorem coupling_scope_burn_success_integrable_history_endpoint_kernel_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => 1) (p, z) ∂K p) ∧
      ∀ w : FieldPair d × Regeneration.CoupledSample d → ℝ,
      Integrable w μ → AEStronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)] w μ →
      (∫ q in {q | q.2 ∈ A}, w q *
        ({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) q ∂μ) =
      ∫ q in {q | q.2 ∈ A}, w q *
        (μ[fun q => δ * Regeneration.endpointAverage i R
          (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) |
            couplingScopeAnnealedHistory Δ (m + k)]) q ∂μ := by
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨B, hB, hbB, hBp, hcond⟩ :=
    coupling_scope_burn_success_condExp_endpoint_kernel_phys hd Q lam h₀ h₁ l δ hl P K hK m J N k
  refine ⟨B, hB, hbB, hBp, ?_⟩
  intro w hw hwm
  apply coupling_scope_success_integrable_history_on_burn Q.measure K hK.1 Δ hΔ lam R h₀ hR
    m i J N k _ w hw hwm
  filter_upwards [hcond] with q hq hqa
  exact (hq hqa).symm

open EinsteinRelation.Regeneration ProbabilityTheory
end EinsteinFull.Blueprint
