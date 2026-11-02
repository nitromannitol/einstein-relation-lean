import EinsteinFull.Blueprint.G1.Proofs.S3KFactorCore

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion)

/-! # `rt:k-factor`: locality and the product identity for the `k`-slice -/

open scoped Classical in
/-- The quenched past factor with the selected prebridge tuple event. -/
noncomputable def AyK {d : ℕ} (K : Regeneration.CoupledQuenchedLaws d) (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (k n : ℕ) (b : Bool) (y : Vec d) (ω : FieldPair d) : ℝ :=
  ∫ z, Gk Δ lam R i k n b z *
    (if y ∈ Regeneration.endpointBall i R (z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ)) then (1 : ℝ) else 0)
    ∂K (0, ω)

/-- The quenched geometry of the prebridge tuple events. -/
theorem geometry_quenched {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ z ∂K (0, ω), ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n →
      z ∈ tupleUnionS (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n →
      ∀ y ∈ Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam)
          (z.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)),
        10 * (k : ℝ) * (l / lam) ≤ y (Regeneration.Renewal.forceCoord hd) ∧
        ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam →
          z.1 u (Regeneration.Renewal.forceCoord hd) ≤
            y (Regeneration.Renewal.forceCoord hd) - 7 * (l / lam) := by
  have hg := hgeom d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  dsimp only at hg
  have h := Regeneration.ae_quenched_of_annealed Q.measure K hK.1 (p := fun q =>
    ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n →
      q.2 ∈ tupleUnionS (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n →
      ∀ y ∈ Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam)
          (q.2.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)),
        10 * (k : ℝ) * (l / lam) ≤ y (Regeneration.Renewal.forceCoord hd) ∧
        ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam →
          q.2.1 u (Regeneration.Renewal.forceCoord hd) ≤
            y (Regeneration.Renewal.forceCoord hd) - 7 * (l / lam))
    (by
      filter_upwards [hg] with q hq k n hk hn hΓ y hy
      exact (hq k n hk hn hΓ).2 y hy)
  exact h

theorem AyK_support {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt) (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (b : Bool) (y : Vec d)
    (hy : y (Regeneration.Renewal.forceCoord hd) < 10 * (k : ℝ) * (l / lam)) :
    ∀ᵐ ω ∂Q.measure, AyK K (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) k n b y ω = 0 := by
  classical
  filter_upwards [geometry_quenched hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hgeom] with ω hω
  unfold AyK
  apply integral_eq_zero_of_ae
  filter_upwards [hω] with z hz
  by_cases hG : Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) k n b z = 0
  · simp [hG]
  · have hΓ := Gk_ne_zero_mem _ _ _ _ _ _ _ z hG
    by_cases hb : y ∈ Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam)
        (z.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
    · exact absurd ((hz k n hk hn hΓ y hb).1) (not_le.mpr hy)
    · simp only [if_neg hb, mul_zero, Pi.zero_apply]

theorem AyK_local {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt) (k n : ℕ) (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) (b : Bool) (y : Vec d) :
    ∃ A' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
        y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] A' ∧
      (fun ω => AyK K (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n b y ω) =ᵐ[Q.measure] A' := by
  classical
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let v : ℝ := y i - 7 * R
  let ballS : Set (CoupledSample d) :=
    {z | y ∈ Regeneration.endpointBall i R (z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ))}
  let belowS : Set (CoupledSample d) :=
    {z | ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ → z.1 u i ≤ v}
  let Sy : Set (CoupledSample d) := (GsetK Δ lam R i k n b ∩ ballS) ∩ belowS
  have hSy : @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ (n - 1)) Sy := by
    refine @MeasurableSet.inter _ (finiteHistorySigma Δ (n - 1)) _ _ ?_ ?_
    · exact @MeasurableSet.inter _ (finiteHistorySigma Δ (n - 1)) _ _
        (measurableSet_GsetK Δ hΔ lam R hR i k n b)
        (Regeneration.measurableSet_endpointBall_past Δ R i (n - 1) y)
    · exact measurableSet_forall_mem_finiteHistory (d := d) Δ (n - 1) {x : Vec d | x i ≤ v}
        (Or.inr (isClosed_le (continuous_apply i) continuous_const))
  let H : CoupledSample d → ℝ := Sy.indicator (fun _ => (1 : ℝ))
  have hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n - 1)) inferInstance H :=
    Measurable.indicator measurable_const hSy
  have hbH : Regeneration.BoundedRealTest H := ⟨1, fun z => by
    by_cases hz : z ∈ Sy <;> simp [H, hz]⟩
  have hsupp : ∀ z : CoupledSample d,
      (¬ ∀ t : ℝ≥0, t ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ → z.1 t i ≤ v) → H z = 0 := by
    intro z hz
    have : z ∉ Sy := fun h => hz h.2
    simp [H, this]
  obtain ⟨A, hA, hAe⟩ := hpast d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
    (n - 1) v H hH hbH hsupp
  have hv : {x : Vec d | x i ≤ v + 3 * R} = {x : Vec d | x i ≤ y i - 4 * R} := by
    ext x
    simp only [Set.mem_setOf_eq, v]
    constructor <;> intro h <;> linarith
  rw [hv] at hA
  refine ⟨A, hA, ?_⟩
  refine Filter.EventuallyEq.trans ?_ hAe
  filter_upwards [geometry_quenched hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hgeom]
    with ω hω
  unfold AyK
  apply integral_congr_ae
  filter_upwards [hω] with z hz
  by_cases hzG : z ∈ GsetK Δ lam R i k n b
  · have e1 : Gk Δ lam R i k n b z = 1 := by simp only [Gk, Set.indicator_of_mem hzG]
    by_cases hb : y ∈ Regeneration.endpointBall i R (z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ))
    · have hbelow : z ∈ belowS := fun u hu => (hz k n hk hn hzG.1 y hb).2 u hu
      have hzSy : z ∈ Sy := ⟨⟨hzG, hb⟩, hbelow⟩
      have e2 : H z = 1 := by simp only [H, Set.indicator_of_mem hzSy]
      rw [e1, e2, if_pos hb, mul_one]
    · have hzSy : z ∉ Sy := fun h => hb h.1.2
      have e2 : H z = 0 := by simp only [H, Set.indicator_of_notMem hzSy]
      rw [e1, e2, if_neg hb, mul_zero]
  · have hzSy : z ∉ Sy := fun h => hzG h.1.1
    have e1 : Gk Δ lam R i k n b z = 0 := by simp only [Gk, Set.indicator_of_notMem hzG]
    have e2 : H z = 0 := by simp only [H, Set.indicator_of_notMem hzSy]
    rw [e1, e2, zero_mul]

/-- The independence of the past and future factors, for a.e. endpoint. -/
theorem factor_ae_y {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) (b : Bool)
    (F : FieldPair d → ℝ)
    (hFloc : Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
      (10 * (k : ℝ) - 4) * (l / lam)}] F)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, F ω * AyK K (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n b y ω *
        (∫ z, Regeneration.killedFutureTest (l / lam) (Regeneration.Renewal.forceCoord hd) Φ
          ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
        (∫ ω, F ω * AyK K (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n b y ω ∂Q.measure) *
        ∫ q in regenerationNoReturn hd (l / lam),
          Φ (regenerationRecord hd lam l 0 q) ∂Regeneration.annealedCoupledLaw Q.measure K := by
  have hR : 0 < l / lam := div_pos hl h₀
  have hlR : l ≤ l / lam := by
    rw [le_div_iff₀ h₀]
    nlinarith
  have hgap : r₀ < 2 * (l / lam) := by linarith
  have hind := (hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD Φ hΦ hbΦ).1
    (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩ 2 le_rfl
    (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩
  obtain ⟨-, -, hb', hc, -⟩ := hind
  filter_upwards [hb', hc] with y hby hcy
  have hcy' : (∫ ω, (∫ z, Regeneration.killedFutureTest (l / lam)
      (Regeneration.Renewal.forceCoord hd) Φ ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
      ∫ q in regenerationNoReturn hd (l / lam),
        Φ (regenerationRecord hd lam l 0 q) ∂Regeneration.annealedCoupledLaw Q.measure K := hcy
  by_cases hy : y (Regeneration.Renewal.forceCoord hd) < 10 * (k : ℝ) * (l / lam)
  · have hA0 := AyK_support hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hgeom k n hk hn b y hy
    have e1 : (fun ω => F ω * AyK K (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n b y ω *
        (∫ z, Regeneration.killedFutureTest (l / lam) (Regeneration.Renewal.forceCoord hd) Φ
          ((y, ω), z) ∂K (y, ω))) =ᵐ[Q.measure] 0 := by
      filter_upwards [hA0] with ω hω
      simp [hω]
    have e2 : (fun ω => F ω * AyK K (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n b y ω) =ᵐ[Q.measure] 0 := by
      filter_upwards [hA0] with ω hω
      simp [hω]
    rw [integral_congr_ae e1, integral_congr_ae e2]
    simp
  · have hy' : 10 * (k : ℝ) * (l / lam) ≤ y (Regeneration.Renewal.forceCoord hd) :=
      not_lt.mp hy
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h10 : 10 * (l / lam) ≤ y (Regeneration.Renewal.forceCoord hd) := by
      nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hk1)]
    obtain ⟨⟨_A', B', _hA', hB', _hAe, hBe⟩, -⟩ := hby h10
    obtain ⟨A'', hA'', hAe⟩ := AyK_local hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hgeom hpast
      k n hk hn b y
    have hF' : Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
        y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] F :=
      hFloc.mono (Probability.localSigma_mono (fun x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        nlinarith)) le_rfl
    have hprod := Regeneration.integral_mul_eq_of_corrected_halfSpace_versions Q
      (Regeneration.Renewal.forceCoord hd) (y (Regeneration.Renewal.forceCoord hd)) (l / lam)
      hgap
      (fun ω => F ω * AyK K (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n b y ω)
      (fun ω => ∫ z, Regeneration.killedFutureTest (l / lam)
        (Regeneration.Renewal.forceCoord hd) Φ ((y, ω), z) ∂K (y, ω))
      (fun ω => F ω * A'' ω) B' (hF'.fun_mul hA'')
      hB'
      (by filter_upwards [hAe] with ω hω; simp [hω])
      hBe
    rw [hprod, hcy']

end EinsteinFull.Blueprint
