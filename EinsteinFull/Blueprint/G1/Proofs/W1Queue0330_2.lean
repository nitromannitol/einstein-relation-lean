import EinsteinFull.Blueprint.G1.node_rt_u3A_global_u2D_geometry
import EinsteinFull.Blueprint.G1.node_rt_u3A_prebridge_u2D_k
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinRelation.Regeneration.OneIntervalBridgeSupport
import EinsteinRelation.Regeneration.KilledFutureConditionalMean
import EinsteinRelation.Regeneration.ForcedBitGeometry

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- A successful interval gains at least eight radii in the force coordinate.
This is a consequence of the actual one-interval law, including its integrability
clauses, rather than an additional support hypothesis. -/
private theorem successful_endpoint_gain {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (xω : Vec d × FieldPair d)
    (hone : Renewal.OneIntervalKernelAt Δ δ R i P K xω)
    (hstart : ∀ x : Vec d, ∀ᵐ γ ∂P (x, xω.2), γ 0 = x) :
    ∀ᵐ z ∂K xω, ∀ n : ℕ, z.2 n = true →
      z.1 ((n : ℝ≥0) * Δ) i + 8 * R ≤ z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ) i := by
  classical
  apply ae_all_iff.mpr
  intro n
  let F : Path d → ℝ := fun γ => if γ Δ i < γ 0 i + 8 * R then 1 else 0
  have hF : Measurable F := Measurable.ite
    (measurableSet_lt ((measurable_pi_apply i).comp (continuous_eval_const Δ).measurable)
      (((measurable_pi_apply i).comp (continuous_eval_const 0).measurable).add_const _))
    measurable_const measurable_const
  have hbF : BoundedRealTest F := ⟨1, fun γ => by
    dsimp only [F]; split_ifs <;> norm_num⟩
  have hseg : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ' := by
    intro γ γ' h
    dsimp only [F]
    rw [h Δ le_rfl, h 0 zero_le]
  have hzero (x : Vec d) : (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P x xω.2) = 0 := by
    have hs : ∀ᵐ γ ∂Renewal.killedBridgeMixture Δ R i P x xω.2, γ 0 = x :=
      (withDensity_absolutelyContinuous _ _).ae_le
        (ae_restrict_of_ae (hstart x))
    apply integral_eq_zero_of_ae
    filter_upwards [hs, ae_killedBridgeMixture_endpoint_mem Δ R i P x xω.2] with γ hγ hb
    change F γ = 0
    have hg := (endpointBall_coordinate_bounds i R x (γ Δ) hb).1
    simp only [F, hγ, not_lt.mpr hg.le, ↓reduceIte]
  obtain ⟨hint, _, heq, _⟩ := hone n (fun _ => 1) F measurable_const
    ⟨1, fun _ => by norm_num⟩ hF hbF hseg
  simp_rw [hzero] at heq
  simp only [mul_zero, integral_zero] at heq
  have hnneg : ∀ z : CoupledSample d,
      0 ≤ (1 : ℝ) * (if z.2 n = true then 1 else 0) * F (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) := by
    intro z
    dsimp only [F]
    split_ifs <;> norm_num
  have haz := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnneg) hint).mp heq
  filter_upwards [haz] with z hz
  intro hb
  simp only [hb, ↓reduceIte, one_mul] at hz
  have ht : (n : ℝ≥0) * Δ + Δ = ((n + 1 : ℕ) : ℝ≥0) * Δ := by
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  change (if z.1 ((n : ℝ≥0) * Δ + Δ) i <
    z.1 ((n : ℝ≥0) * Δ + 0) i + 8 * R then (1 : ℝ) else 0) = 0 at hz
  rw [ht, add_zero] at hz
  split_ifs at hz with h
  · norm_num at hz
  · exact le_of_not_gt h

/-- Common full-measure event for every successful grid interval. -/
private theorem ae_successful_geometry {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ n : ℕ, q.2.2 n = true →
      coordinateMaximum (pathTimeShift q.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam))
        (Renewal.forceCoord hd) (Renewal.regenDelta lam) ≤ 11 * (l / lam) ∧
      q.2.1 ((n : ℝ≥0) * Renewal.regenDelta lam) (Renewal.forceCoord hd) +
        8 * (l / lam) ≤
        q.2.1 (((n + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) (Renewal.forceCoord hd) := by
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hev (u : ℝ≥0) : Measurable (fun q : FieldPair d × CoupledSample d => q.2.1 u i) :=
    (measurable_pi_apply i).comp ((continuous_eval_const u).measurable.comp measurable_snd.fst)
  have hm : MeasurableSet {q : FieldPair d × CoupledSample d | ∀ n : ℕ,
      q.2.2 n = true →
      coordinateMaximum (pathTimeShift q.2.1 ((n : ℝ≥0) * Δ)) i Δ ≤ 11 * R ∧
      q.2.1 ((n : ℝ≥0) * Δ) i + 8 * R ≤ q.2.1 (((n + 1 : ℕ) : ℝ≥0) * Δ) i} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.imp
    · exact measurableSet_eq_fun
        ((measurable_pi_apply n).comp measurable_snd.snd) measurable_const
    · apply MeasurableSet.inter
      · exact measurableSet_le
          ((measurable_coordinateMaximum i).comp (measurable_const.prodMk
            (((measurable_sampleTimeShift Δ).comp
              (measurable_const.prodMk measurable_snd)).fst))) measurable_const
      · exact measurableSet_le ((hev ((n : ℝ≥0) * Δ)).add_const (8 * R))
          (hev (((n + 1 : ℕ) : ℝ≥0) * Δ))
  apply Measure.ae_compProd_of_ae_ae hm
  filter_upwards [hK.1.1, hK.2.2.1, hK.2.2.2.2.2.1.1, hK.2.2.2.2.2.2.2.1]
    with ω hp hP hb hone
  haveI : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  obtain ⟨_, r, hr⟩ := hP
  have hs : ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x := by
    intro x
    rw [hr x]
    exact r.pathLaw_starts_at x
  have he := successful_endpoint_gain Δ R δ i P K (0, ω) hone hs
  filter_upwards [hb, he] with z hz he
  intro n hn
  refine ⟨?_, he n hn⟩
  apply coordinateMaximum_le
  intro t ht
  have hs := hz n hn (((n : ℝ≥0) * Δ) + t)
    (le_add_of_nonneg_right zero_le) ?_
  · have hg := (couplingRegion_coordinate_bounds i R _ _ hs).2
    change z.1 ((n : ℝ≥0) * Δ + t) i - z.1 ((n : ℝ≥0) * Δ + 0) i ≤ 11 * R
    rw [add_zero]
    linarith
  · calc
      (n : ℝ≥0) * Δ + t ≤ (n : ℝ≥0) * Δ + Δ := add_le_add_right ht.2 _
      _ = ((n + 1 : ℕ) : ℝ≥0) * Δ := by
        simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- Deterministic induction across a literal tuple of prebridge events. -/
private theorem tuple_geometry {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (z : CoupledSample d)
    (hfirst : ∀ m : ℕ, 2 ≤ m → z ∈ forcedBitTrialEvent Δ lam R i (m - 1) →
      2 * R ≤ z.1 (((m - 1 : ℕ) : ℝ≥0) * Δ) i ∧
      ∀ u : ℝ≥0, u ≤ ((m - 1 : ℕ) : ℝ≥0) * Δ →
        z.1 u i ≤ z.1 (((m - 1 : ℕ) : ℝ≥0) * Δ) i + R)
    (hb : ∀ m : ℕ, z.2 m = true →
      coordinateMaximum (pathTimeShift z.1 ((m : ℝ≥0) * Δ)) i Δ ≤ 11 * R ∧
      z.1 ((m : ℝ≥0) * Δ) i + 8 * R ≤ z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) i)
    (k n : ℕ) (hk : 1 ≤ k) (a : Fin (k + 1) → ℕ)
    (ha0 : a 0 = 0) (han : a (Fin.last k) = n)
    (hsep : ∀ j : Fin k, a j.castSucc + 2 ≤ a j.succ)
    (htrial : ∀ j : Fin k,
      sampleTimeShift Δ z ((a j.castSucc : ℝ≥0) * Δ) ∈
        forcedBitTrialEvent Δ lam R i (a j.succ - a j.castSucc - 1))
    (hbit : ∀ j : Fin k, j.val + 1 < k → z.2 (a j.succ - 1) = true) :
    (∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
      z.1 u i ≤ z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ) i + R) ∧
    ∀ y ∈ endpointBall i R (z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ)),
      10 * (k : ℝ) * R ≤ y i ∧
      ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ → z.1 u i ≤ y i - 7 * R := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let s (j : Fin (k + 1)) : ℝ≥0 := (a j.castSucc : ℝ≥0) * Δ
  let t (j : Fin (k + 1)) : ℝ≥0 := ((a j.succ - 1 : ℕ) : ℝ≥0) * Δ
  have hlocal (j : Fin (k + 1)) :
      s j ≤ t j ∧ 2 * R ≤ z.1 (t j) i - z.1 (s j) i ∧
      ∀ u : ℝ≥0, s j ≤ u → u ≤ t j → z.1 u i ≤ z.1 (t j) i + R := by
    have hs := hsep j
    let m := a j.succ - a j.castSucc - 1
    have ha : a j.castSucc + m = a j.succ - 1 := by dsimp only [m]; omega
    have htime : s j + (m : ℝ≥0) * Δ = t j := by
      dsimp only [s, t]
      rw [← add_mul, ← Nat.cast_add, ha]
    have hst : s j ≤ t j := htime ▸ le_add_of_nonneg_right zero_le
    have hg := forcedBitTrialEvent_geometry Δ hΔ lam R hlam hR i m
      (sampleTimeShift Δ z (s j)) (htrial j)
    have hheight : 2 * R ≤ z.1 (t j) i - z.1 (s j) i := by
      have hh := hg.2
      change 2 * R ≤ z.1 (s j + (m : ℝ≥0) * Δ) i - z.1 (s j + 0) i at hh
      simpa only [htime, add_zero] using hh
    refine ⟨hst, hheight, ?_⟩
    intro u hsu hut
    have hu : u - s j ≤ (m : ℝ≥0) * Δ := by
      apply (tsub_le_iff_right).mpr
      simpa only [add_comm, htime] using hut
    have hd := displacement_le_coordinateMaximum
      (sampleTimeShift Δ z (s j)).1 i (u - s j) ((m : ℝ≥0) * Δ) hu
    have hmax := hg.1
    change z.1 (s j + (u - s j)) i - z.1 (s j + 0) i ≤ _ at hd
    change _ ≤ z.1 (s j + (m : ℝ≥0) * Δ) i - z.1 (s j + 0) i + R at hmax
    rw [add_tsub_cancel_of_le hsu, add_zero] at hd
    rw [htime, add_zero] at hmax
    linarith
  have hind (j : Fin (k + 1)) :
      10 * (j.val : ℝ) * R + 2 * R ≤ z.1 (t j) i ∧
      ∀ u : ℝ≥0, u ≤ t j → z.1 u i ≤ z.1 (t j) i + R := by
    induction j using Fin.induction with
    | zero =>
      have hn0 : 2 ≤ a (0 : Fin (k + 1)).succ := by
        have hs := hsep (0 : Fin (k + 1))
        simpa only [Fin.castSucc_zero, ha0, zero_add] using hs
      have htr : z ∈ forcedBitTrialEvent Δ lam R i (a (0 : Fin (k + 1)).succ - 1) := by
        simpa only [Fin.castSucc_zero, ha0, Nat.cast_zero, zero_mul,
          sampleTimeShift_zero, Nat.sub_zero] using htrial (0 : Fin (k + 1))
      have hbase := hfirst _ hn0 htr
      exact ⟨by simpa only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, zero_add]
        using hbase.1, hbase.2⟩
    | succ j ih =>
      have heq : j.castSucc.succ = j.succ.castSucc := by ext; rfl
      have hapos : 1 ≤ a j.castSucc.succ := by have := hsep j.castSucc; omega
      have htend : ((a j.castSucc.succ - 1 + 1 : ℕ) : ℝ≥0) * Δ = s j.succ := by
        rw [Nat.sub_add_cancel hapos, heq]
      have hprev : t j.castSucc + Δ = s j.succ := by
        dsimp only [t]
        calc
          _ = ((a j.castSucc.succ - 1 + 1 : ℕ) : ℝ≥0) * Δ := by
            simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          _ = _ := htend
      have hcoin := hbit j.castSucc (by have := j.isLt; simp only [Fin.val_castSucc]; omega)
      obtain ⟨hmax, hgain⟩ := hb (a j.castSucc.succ - 1) hcoin
      rw [htend] at hgain
      change z.1 (t j.castSucc) i + 8 * R ≤ z.1 (s j.succ) i at hgain
      have hloc := hlocal j.succ
      refine ⟨?_, ?_⟩
      · simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at ih ⊢
        nlinarith only [ih.1, hgain, hloc.2.1]
      · intro u hu
        by_cases hsu : s j.succ ≤ u
        · exact hloc.2.2 u hsu hu
        · by_cases htu : u ≤ t j.castSucc
          · have hp := ih.2 u htu
            linarith only [hp, hgain, hloc.2.1, hR]
          · have hu0 : t j.castSucc ≤ u := le_of_not_ge htu
            have huΔ : u - t j.castSucc ≤ Δ := by
              apply (tsub_le_iff_right).mpr
              rw [add_comm, hprev]
              exact le_of_not_ge hsu
            have hd := displacement_le_coordinateMaximum
              (pathTimeShift z.1 (t j.castSucc)) i (u - t j.castSucc) Δ huΔ
            change z.1 (t j.castSucc + (u - t j.castSucc)) i -
              z.1 (t j.castSucc + 0) i ≤ _ at hd
            rw [add_tsub_cancel_of_le hu0, add_zero] at hd
            change coordinateMaximum (pathTimeShift z.1 (t j.castSucc)) i Δ ≤ 11 * R at hmax
            linarith only [hd, hmax, hgain, hloc.2.1]
  let last : Fin (k + 1) := ⟨k, by omega⟩
  have hlast : last.succ = Fin.last (k + 1) := by ext; rfl
  have htlast : t last = ((n - 1 : ℕ) : ℝ≥0) * Δ := by dsimp only [t]; rw [hlast, han]
  have hh := hind last
  rw [htlast] at hh
  refine ⟨hh.2, ?_⟩
  intro y hy
  have hy' := (endpointBall_coordinate_bounds i R _ y hy).1
  refine ⟨?_, fun u hu => ?_⟩
  · have hlastval : (last.val : ℝ) = ((k + 1 : ℕ) : ℝ) - 1 := by
      dsimp only [last]
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [hlastval] at hh
    nlinarith only [hh.1, hy']
  · have hu' := hh.2 u hu
    linarith only [hu', hy']

/-- Global prebridge geometry, with exactly the prescribed graph dependencies. -/
theorem node_rt_u3A_global_u2D_geometry_of_deps
    (hprebridge : node_rt_u3A_prebridge_u2D_kStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt) :
    node_rt_u3A_global_u2D_geometryStmt := by
  intro d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  dsimp only
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro n
  by_cases hk : 1 ≤ k
  · by_cases hn : 2 * k ≤ n
    · have hΓ := (hprebridge d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn).1
      have hΓm := (Probability.finiteHistorySigma_le (d := d) (Renewal.regenDelta lam) (n - 1)) _ hΓ
      refine ((ae_restrict_iff' (hΓm.preimage measurable_snd)).mp ?_).mono
        (fun q h _ _ => h)
      filter_upwards [ae_restrict_of_ae (ae_successful_geometry hd Q lam h₀ h₁ l δ P K hK),
        ae_restrict_of_ae (ae_origin_start_of_isGMPReducedKernel hd Q lam h₀.le h₁ P K
          hK.1 hK.2.1 hK.2.2.1), ae_restrict_mem (hΓm.preimage measurable_snd)]
        with q hq hz0 hΓq
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hΓq
      rcases ha with ⟨ha0, han, hsep', htrial, hbit, _hsurvival⟩
      have hfirst (m : ℕ) (hm : 2 ≤ m)
          (htr : q.2 ∈ forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
            (Renewal.forceCoord hd) (m - 1)) :=
        ((hslices d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK m hm).2.2
          q.2 hz0 htr)
      exact tuple_geometry (Renewal.regenDelta lam) hΔ lam (l / lam) h₀ hR
        (Renewal.forceCoord hd) q.2 (fun m hm ht => ⟨(hfirst m hm ht).1, (hfirst m hm ht).2.1⟩)
        hq k n hk (fun j => (a j).val) ha0 han hsep' htrial hbit
    · exact Filter.Eventually.of_forall (fun _ _ hn' => (hn hn').elim)
  · exact Filter.Eventually.of_forall (fun _ hk' => (hk hk').elim)

end EinsteinFull.Blueprint
