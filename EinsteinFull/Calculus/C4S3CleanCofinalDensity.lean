import EinsteinFull.Calculus.C6S3OneScaleCouplingFactory
import EinsteinFull.Calculus.C19S3ExcursionsFromCofinalCouplings
import EinsteinFull.Calculus.C1S3FiniteRegenerationExcursion
import EinsteinFull.Regeneration.KilledBridgeNormalization
import EinsteinRelation.Regeneration.EndpointAverageFubini

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- The explicit cofinal input bounds the actual supplied killed event on the
translated endpoint ball, uniformly in the starting point and almost every field. -/
theorem c4_cofinal_minorization_and_coupling_of_endpoint_density {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P)
    (lower : ∀ B : ℝ, ∃ L : ℝ, B ≤ L ∧ 0 < L ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
        ∀ A : Set (Vec d), MeasurableSet A →
          ENNReal.ofReal c * volume (endpointBall (Renewal.forceCoord hd) (L / lam) x ∩ A) ≤
          P (x, ω) {γ | (∀ t : ℝ≥0, t ≤ Renewal.regenDelta lam →
            γ t ∈ couplingRegion (Renewal.forceCoord hd) (L / lam) x) ∧
            γ (Renewal.regenDelta lam) ∈ A}) :
    ∀ B : ℝ, ∃ L : ℝ, B ≤ L ∧ 0 < L ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      (∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
        ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (L / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L / lam)
          (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) ∧
      ∃ K : CoupledQuenchedLaws d, IsRegenerationCoupling hd Q lam L δ h0.le h1 P K := by
  intro B
  obtain ⟨L, hBL, hL, c, hc, hbound⟩ := lower B
  let i := Renewal.forceCoord hd
  let R := L / lam
  have hR : 0 < R := div_pos hL h0
  let v := (volume (endpointBall i R (0 : Vec d))).toReal
  have hv : 0 < v := ENNReal.toReal_pos (endpointBall_volume_pos i R hR 0).ne'
    (endpointBall_volume_ne_top i R hR 0)
  let δ := min (c * v) (1 / 2)
  have hδ : 0 < δ := lt_min (mul_pos hc hv) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hv' : ENNReal.ofReal v = volume (endpointBall i R (0 : Vec d)) :=
    ENNReal.ofReal_toReal (endpointBall_volume_ne_top i R hR 0)
  have hδv : ENNReal.ofReal δ ≤ ENNReal.ofReal c * volume (endpointBall i R 0) := by
    rw [← hv', ← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hminor : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d))
        (endpointBall i R x) ≤
      (Renewal.killedSegmentLaw (Renewal.regenDelta lam) R i P x ω).map
        (fun γ : Path d => γ (Renewal.regenDelta lam)) := by
    filter_upwards [hbound] with ω hω
    intro x
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, smul_eq_mul, ProbabilityTheory.cond_apply' hA,
      endpointBall_volume_eq i R x,
      Measure.map_apply (continuous_eval_const _).measurable hA]
    change _ ≤ (P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta lam →
      γ t ∈ couplingRegion i R x} ((fun γ : Path d => γ (Renewal.regenDelta lam)) ⁻¹' A)
    rw [Measure.restrict_apply ((continuous_eval_const _).measurable hA)]
    have hv0 : volume (endpointBall i R (0 : Vec d)) ≠ 0 :=
      (endpointBall_volume_pos i R hR 0).ne'
    have hvtop := endpointBall_volume_ne_top i R hR 0
    calc
      _ ≤ (ENNReal.ofReal c * volume (endpointBall i R 0)) *
          (volume (endpointBall i R 0))⁻¹ * volume (endpointBall i R x ∩ A) := by
            simpa only [mul_assoc, mul_comm, mul_left_comm] using
              (mul_le_mul_right hδv ((volume (endpointBall i R 0))⁻¹ *
                volume (endpointBall i R x ∩ A)))
      _ = ENNReal.ofReal c * volume (endpointBall i R x ∩ A) := by
            calc
              _ = ENNReal.ofReal c * (volume (endpointBall i R 0) *
                  (volume (endpointBall i R 0))⁻¹) * volume (endpointBall i R x ∩ A) := by ac_rfl
              _ = _ := by rw [ENNReal.mul_inv_cancel hv0 hvtop, mul_one]
      _ ≤ _ := by simpa only [Set.preimage, Set.inter_comm, Set.ofPred_and] using hω x A hA
  obtain ⟨K, hK⟩ := c6_s3_coupling_of_ae_endpoint_minorization hd Q lam h0 h1 P hP L δ hL hδ hδ1 hminor
  exact ⟨L, hBL, hL, δ, hδ, hδ1, hminor, K, hK⟩


theorem c4_s3_unbounded_of_genuinely_cofinal_couplings
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (c1_s3_excursion_of_finite_first_regeneration : ∀ {d : ℕ} (Δ : ℝ≥0) (_hΔ : 0 < Δ) (lam R : ℝ)
      (_hlam : 0 < lam) (_hR : 0 < R) (z : CoupledSample d) (i : Fin d),
      firstRegenerationTime Δ lam R z i ≠ ⊤ →
      ∃ t : ℝ≥0, 2 * R ≤ z.1 t i - z.1 0 i)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hSplits : ∀ B : ℝ, ∃ L : ℝ, B ≤ L ∧ 0 < L ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ K : CoupledQuenchedLaws d, IsRegenerationCoupling hd Q lam L δ h0.le h1 P K)
    (l δ : ℝ)
    (K : CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
  obtain ⟨L₀, hL₀, _, htail⟩ := htails d hd Λ₀ r₀
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  have hall : ∀ n : ℕ, ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      ∃ t : ℝ≥0, (n : ℝ) < q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
    intro n
    let B : ℝ := L₀ + ((n : ℝ) + 1) * lam
    obtain ⟨L, hBL, hL, δ', hδ'0, hδ'1, K', hK'⟩ := hSplits B
    have hLge : L₀ ≤ L := by
      dsimp [B] at hBL
      have hnonneg : 0 ≤ ((n : ℝ) + 1) * lam := mul_nonneg (by positivity) h0.le
      linarith
    have hn : (n : ℝ) < 2 * (L / lam) := by
      have hbound : (n : ℝ) + 1 ≤ L / lam := by
        apply (le_div_iff₀ h0).2
        dsimp [B] at hBL
        linarith
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨c, C, a, M, hc, _, _, _, _, htail'⟩ := htail L hLge δ' hδ'0 hδ'1
    obtain ⟨_, _, htail'', _, _⟩ := htail' Q lam h0 h1 P K' hK'
    have ht : HasFirstRegenerationTail Q.measure (Renewal.regenDelta lam)
        lam (L / lam) c C (Renewal.forceCoord hd) K' := by
      intro t ht
      simpa only [EinsteinFull.regenerationTime, Regeneration.regenerationTime_one] using htail'' t ht
    have hfin := firstRegenerationTime_ne_top_ae_of_tail Q.measure K'
      (Renewal.regenDelta lam) lam (L / lam) c C hc h0 (Renewal.forceCoord hd) ht
    have hev : ∀ᵐ q ∂annealedCoupledLaw Q.measure K',
        q.2.1 ∈ {γ : Path d | ∃ t : ℝ≥0, (n : ℝ) < γ t (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd)} := by
      filter_upwards [hfin] with q hq
      obtain ⟨t, ht⟩ := c1_s3_excursion_of_finite_first_regeneration
        (Renewal.regenDelta lam) hΔ lam (L / lam) h0 (div_pos hL h0) q.2
        (Renewal.forceCoord hd) hq
      exact ⟨t, hn.trans_le ht⟩
    exact c19_s3_transfer_path_event Q.measure P K' K hK'.1 hK.1
      hK'.2.1 hK.2.1 _ (c19_s3_measurableSet_excursion _ _) hev
  filter_upwards [ae_all_iff.mpr hall] with q hq
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt B
  obtain ⟨t, ht⟩ := hq n
  exact ⟨t, le_of_lt (hn.trans ht)⟩



/-- A cofinal family of endpoint estimates yields one conull event and couplings
at a sequence of genuinely cofinal scales, with a separate constant at each scale. -/
theorem c4_s3_cofinal_minorization_common_couplings
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P)
    (L₀ : ℝ)
    (hminor : ∀ B : ℝ, ∃ L : ℝ, B ≤ L ∧ 0 < L ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (L / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L / lam)
          (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) :
    ∃ L δ : ℕ → ℝ, (∀ n : ℕ, L₀ + (n : ℝ) ≤ L n ∧ 0 < L n ∧ 0 < δ n ∧ δ n < 1) ∧
      (∀ᵐ ω ∂Q.measure, ∀ n : ℕ, ∀ x : Vec d,
        ENNReal.ofReal (δ n) • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (L n / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L n / lam)
          (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) ∧
      ∀ n : ℕ, ∃ K : CoupledQuenchedLaws d,
        IsRegenerationCoupling hd Q lam (L n) (δ n) h0.le h1 P K := by
  have hall : ∀ n : ℕ, ∃ L : ℝ, L₀ + (n : ℝ) ≤ L ∧ 0 < L ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (L / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L / lam)
          (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam)) :=
    fun n => hminor (L₀ + (n : ℝ))
  choose L hL hpos δ hδ0 hδ1 hae using hall
  have hcommon := ae_all_iff.mpr hae
  refine ⟨L, δ, fun n => ⟨hL n, hpos n, hδ0 n, hδ1 n⟩, hcommon, ?_⟩
  intro n
  apply c6_s3_coupling_of_ae_endpoint_minorization hd Q lam h0 h1 P hP
  · exact hpos n
  · exact hδ0 n
  · exact hδ1 n
  · exact hae n


/-- Cofinal killed endpoint bounds produce a common-event family of couplings. -/
theorem c4_cofinal_family_of_endpoint_density {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P)
    (lower : ∀ B : ℝ, ∃ L : ℝ, B ≤ L ∧ 0 < L ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
        ∀ A : Set (Vec d), MeasurableSet A →
          ENNReal.ofReal c * volume (endpointBall (Renewal.forceCoord hd) (L / lam) x ∩ A) ≤
          P (x, ω) {γ | (∀ t : ℝ≥0, t ≤ Renewal.regenDelta lam →
            γ t ∈ couplingRegion (Renewal.forceCoord hd) (L / lam) x) ∧
            γ (Renewal.regenDelta lam) ∈ A}) :
    ∀ L₀ : ℝ, ∃ L δ : ℕ → ℝ,
      (∀ n : ℕ, L₀ + (n : ℝ) ≤ L n ∧ 0 < L n ∧ 0 < δ n ∧ δ n < 1) ∧
      (∀ᵐ ω ∂Q.measure, ∀ n : ℕ, ∀ x : Vec d,
        ENNReal.ofReal (δ n) • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (L n / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L n / lam)
          (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) ∧
      ∀ n, ∃ K : CoupledQuenchedLaws d,
        IsRegenerationCoupling hd Q lam (L n) (δ n) h0.le h1 P K := by
  intro L₀
  apply c4_s3_cofinal_minorization_common_couplings hd Q lam h0 h1 P hP L₀
  intro B
  obtain ⟨L, hBL, hL, δ, hδ0, hδ1, hminor, _, _⟩ :=
    c4_cofinal_minorization_and_coupling_of_endpoint_density hd Q lam h0 h1 P hP lower B
  exact ⟨L, hBL, hL, δ, hδ0, hδ1, hminor⟩

/-- Direct cofinal-density consumer for the unbounded excursion step. -/
theorem c4_unbounded_of_cofinal_endpoint_density
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P)
    (lower : ∀ B : ℝ, ∃ L : ℝ, B ≤ L ∧ 0 < L ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
        ∀ A : Set (Vec d), MeasurableSet A →
          ENNReal.ofReal c * volume (endpointBall (Renewal.forceCoord hd) (L / lam) x ∩ A) ≤
          P (x, ω) {γ | (∀ t : ℝ≥0, t ≤ Renewal.regenDelta lam →
            γ t ∈ couplingRegion (Renewal.forceCoord hd) (L / lam) x) ∧
            γ (Renewal.regenDelta lam) ∈ A})
    (l δ : ℝ) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
  apply c4_s3_unbounded_of_genuinely_cofinal_couplings htails
    c1_s3_excursion_of_finite_first_regeneration hd Q lam h0 h1 P ?_ l δ K hK
  intro B
  obtain ⟨L, δs, hscales, _, hKs⟩ :=
    c4_cofinal_family_of_endpoint_density hd Q lam h0 h1 P hP lower B
  obtain ⟨K', hK'⟩ := hKs 0
  exact ⟨L 0, by simpa using (hscales 0).1, (hscales 0).2.1,
    δs 0, (hscales 0).2.2.1, (hscales 0).2.2.2, K', hK'⟩

end EinsteinFull.Blueprint
