import EinsteinFull.Work.W1.GMPFullPastRestartSupport
import EinsteinFull.Calculus.C13TubeBlockMeasurability

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull
open EinsteinRelation
noncomputable section

/-- Chain conditional tube bounds along the actual deterministic GMP restart. -/
theorem c16_finite_tube_chain {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
 (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
 (N : ℕ) (tau : ℝ≥0) (eta : ℝ) (heta : 0 ≤ eta) (x₀ : Vec d)
 (A : ℕ → Set (Vec d)) (piece E : ℕ → Set (Path d))
 (hpiece : ∀ n, MeasurableSet (piece n)) (hpast : ∀ n : ℕ, MeasurableSet[gmpPastSigma ((n : ℝ≥0) * tau)] (E n))
 (hzero : E 0 = Set.univ)
 (hsucc : ∀ n, E (n+1) = E n ∩ (gmpShiftPath ((n : ℝ≥0) * tau)) ⁻¹' piece n)
 (hentrance : ∀ n, n < N → ∀ᵐ Y ∂G.pathLaw x₀, Y ∈ E n → Y ((n : ℝ≥0) * tau) ∈ A n)
 (hstep : ∀ n, n < N → ∀ x ∈ A n, ENNReal.ofReal eta ≤ G.pathLaw x (piece n)) :
 ENNReal.ofReal (eta ^ N) ≤ G.pathLaw x₀ (E N) := by
  letI := G.pathLaw_isMarkovKernel
  have hchain : ∀ n, n < N → ENNReal.ofReal eta * G.pathLaw x₀ (E n) ≤ G.pathLaw x₀ (E (n+1)) := by
    intro n hn
    let s : ℝ≥0 := (n : ℝ≥0) * tau
    have he := congrArg (fun K : Kernel (Vec d) (Path d) => K x₀ (piece n))
      (gmpPathLaw_restrict_past_map_shift G s (E n) (hpast n))
    rw [Kernel.map_apply _ (measurable_gmpShiftPath _),
      Measure.map_apply (measurable_gmpShiftPath _) (hpiece n),
      Kernel.comp_apply' _ _ _ (hpiece n),
      Kernel.map_apply _ (measurable_pathPosition _),
      lintegral_map (G.pathLaw.measurable_coe (hpiece n)) (measurable_pathPosition _)] at he
    rw [Kernel.restrict_apply] at he
    rw [Measure.restrict_apply ((hpiece n).preimage (measurable_gmpShiftPath _)), Set.inter_comm, ← hsucc n] at he
    rw [he, ← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae (hentrance n hn), ae_restrict_mem (gmpPastSigma_le s (E n) (hpast n))] with Y hY hYE
    exact hstep n hn (Y s) (hY hYE)
  have hind : ∀ n, n ≤ N → ENNReal.ofReal (eta ^ n) ≤ G.pathLaw x₀ (E n) := by
    intro n hn
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
      have hn' : n < N := by omega
      calc
        ENNReal.ofReal (eta ^ (n+1)) = ENNReal.ofReal eta * ENNReal.ofReal (eta ^ n) := by
          rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg heta _), mul_comm]
        _ ≤ ENNReal.ofReal eta * G.pathLaw x₀ (E n) := by gcongr; exact ih (by omega)
        _ ≤ G.pathLaw x₀ (E (n+1)) := hchain n hn'
  exact hind N le_rfl


/-- Blockwise control and mesh oscillation imply containment in the full tube. -/
theorem c16_scaled_blocks_subset_tube {d : ℕ} (N : ℕ) (hN : 0 < N)
 (lam h eps : ℝ) (hlam : 0 < lam) (hh : 0 < h) (heps : 0 < eps)
 (gamma : ℝ → Vec d)
 (hosc : ∀ k : ℕ, k < N → ∀ u : ℝ, (k:ℝ)*h ≤ u → u ≤ (k+1:ℕ)*h → euclideanNorm (gamma u - gamma ((k:ℝ)*h)) ≤ eps/16)
 (Y : Path d)
 (hblocks : ∀ k : ℕ, k < N → ∀ s : ℝ≥0, (s:ℝ) ≤ h/lam^2 →
 euclideanNorm (lam • Y (((k:ℝ)*h/lam^2).toNNReal+s) - gamma ((k:ℝ)*h)) < eps/2) :
 ∀ u : ℝ≥0, (u:ℝ) ≤ (N:ℝ)*h → euclideanNorm (lam • Y ((u:ℝ)/lam^2).toNNReal - gamma (u:ℝ)) < eps := by
  have mesh : ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 ≤ t → t ≤ (n:ℝ)*h →
      ∃ k : ℕ, k < n ∧ (k:ℝ)*h ≤ t ∧ t ≤ ((k+1:ℕ):ℝ)*h := by
    intro n hn t ht htn
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact ⟨0, by omega, by simpa using ht, by simpa using htn⟩
      · by_cases ht' : t ≤ (n:ℝ)*h
        · obtain ⟨k, hk, hkt, htk⟩ := ih (by omega) ht'
          exact ⟨k, by omega, hkt, htk⟩
        · exact ⟨n, by omega, le_of_lt (lt_of_not_ge ht'), by simpa using htn⟩
  intro u hu
  obtain ⟨k, hk, hku, huk⟩ := mesh N hN u u.coe_nonneg hu
  have hl2 : 0 < lam^2 := sq_pos_of_pos hlam
  have hk0 : 0 ≤ (k:ℝ)*h := mul_nonneg (Nat.cast_nonneg _) hh.le
  have hd0 : 0 ≤ (u:ℝ)/lam^2 - (k:ℝ)*h/lam^2 := by
    exact sub_nonneg.mpr (div_le_div_of_nonneg_right hku hl2.le)
  let s : ℝ≥0 := ((u:ℝ)/lam^2 - (k:ℝ)*h/lam^2).toNNReal
  have hs : (s:ℝ) ≤ h/lam^2 := by
    dsimp [s]
    rw [max_eq_left hd0]
    have : (u:ℝ) - (k:ℝ)*h ≤ h := by push_cast at huk; nlinarith
    have := div_le_div_of_nonneg_right this hl2.le
    rw [sub_div] at this
    exact this
  have ht : ((k:ℝ)*h/lam^2).toNNReal + s = ((u:ℝ)/lam^2).toNNReal := by
    apply NNReal.eq
    dsimp only [s]
    simp only [NNReal.coe_add, Real.coe_toNNReal _ (div_nonneg hk0 hl2.le),
      Real.coe_toNNReal _ hd0, Real.coe_toNNReal _ (div_nonneg u.coe_nonneg hl2.le)]
    ring
  have hb := hblocks k hk s hs
  rw [ht] at hb
  have ho := hosc k hk u hku huk
  have htri := TimeChange.euclideanNorm_add_le
    (lam • Y ((u:ℝ)/lam^2).toNNReal - gamma ((k:ℝ)*h))
    (gamma ((k:ℝ)*h) - gamma (u:ℝ))
  have heq : (lam • Y ((u:ℝ)/lam^2).toNNReal - gamma ((k:ℝ)*h)) +
      (gamma ((k:ℝ)*h) - gamma (u:ℝ)) = lam • Y ((u:ℝ)/lam^2).toNNReal - gamma (u:ℝ) := by abel
  rw [heq] at htri
  have hsym : euclideanNorm (gamma ((k:ℝ)*h) - gamma (u:ℝ)) =
      euclideanNorm (gamma (u:ℝ) - gamma ((k:ℝ)*h)) := by
    rw [← neg_sub (gamma (u:ℝ)) (gamma ((k:ℝ)*h))]
    have hn := TimeChange.euclideanNorm_smul (-1 : ℝ) (gamma (u:ℝ) - gamma ((k:ℝ)*h))
    simpa using hn
  rw [hsym] at htri
  linarith

/-- Combine deterministic tube containment with the finite GMP probability chain. -/
@[nolint unusedArguments]
theorem c16_actual_finite_tube_probability {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
 (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
 (N : ℕ) (tau : ℝ≥0) (eta : ℝ) (heta : 0 ≤ eta) (x₀ : Vec d)
 (A : ℕ → Set (Vec d)) (piece E : ℕ → Set (Path d))
 (hpiece : ∀ n, MeasurableSet (piece n)) (hpast : ∀ n : ℕ, MeasurableSet[gmpPastSigma ((n : ℝ≥0) * tau)] (E n))
 (hzero : E 0 = Set.univ)
 (hsucc : ∀ n, E (n+1) = E n ∩ (gmpShiftPath ((n : ℝ≥0) * tau)) ⁻¹' piece n)
 (hentrance : ∀ n, n < N → ∀ᵐ Y ∂G.pathLaw x₀, Y ∈ E n → Y ((n : ℝ≥0) * tau) ∈ A n)
 (hstep : ∀ n, n < N → ∀ x ∈ A n, ENNReal.ofReal eta ≤ G.pathLaw x (piece n))
 (hN : 0 < N) (h eps : ℝ) (hlam : 0 < lam) (hh : 0 < h) (heps : 0 < eps)
 (htau : tau = (h/lam^2).toNNReal) (gamma : ℝ → Vec d)
 (hosc : ∀ k : ℕ, k < N → ∀ u : ℝ, (k:ℝ)*h ≤ u → u ≤ (k+1:ℕ)*h → euclideanNorm (gamma u - gamma ((k:ℝ)*h)) ≤ eps/16)
 (hblocks : ∀ Y ∈ E N, ∀ k : ℕ, k < N → ∀ s : ℝ≥0, (s:ℝ) ≤ h/lam^2 → euclideanNorm (lam • Y (((k:ℝ)*h/lam^2).toNNReal+s) - gamma ((k:ℝ)*h)) < eps/2) :
 ENNReal.ofReal (eta ^ N) ≤ G.pathLaw x₀ {Y | ∀ u : ℝ≥0, (u:ℝ) ≤ (N:ℝ)*h → euclideanNorm (lam • Y ((u:ℝ)/lam^2).toNNReal - gamma (u:ℝ)) < eps} := by
  calc
    ENNReal.ofReal (eta ^ N) ≤ G.pathLaw x₀ (E N) :=
      c16_finite_tube_chain G N tau eta heta x₀ A piece E hpiece hpast hzero hsucc hentrance hstep
    _ ≤ _ := measure_mono (fun Y hY =>
      c16_scaled_blocks_subset_tube N hN lam h eps hlam hh heps gamma hosc Y (hblocks Y hY))

/-- A finite prefix of events gains precisely the next event at a successor. -/
theorem c16_finite_prefix_succ {α : Type*} (B : ℕ → Set α) (n : ℕ) :
    (⋂ k < n + 1, B k) = (⋂ k < n, B k) ∩ B n := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro hx
    exact ⟨fun k hk => hx k (by omega), hx n (by omega)⟩
  · rintro ⟨hx, hn⟩ k hk
    by_cases hkn : k = n
    · simpa only [hkn] using hn
    · exact hx k (by omega)

/-- Each event in a finite prefix holds on that prefix. -/
theorem c16_finite_prefix_extract {α : Type*} (B : ℕ → Set α) (n k : ℕ)
    (hk : k < n) : (⋂ j < n, B j) ⊆ B k := by
  intro x hx
  exact (Set.mem_iInter.mp (Set.mem_iInter.mp hx k) hk)

/-- The last block supplies the entrance condition at the next mesh point. -/
theorem c16_prefix_endpoint {d : ℕ} (lam eps : ℝ) (tau : ℝ≥0)
    (c : ℕ → Vec d) (n : ℕ) (Y : Path d)
    (hY : ∀ k : ℕ, k < n + 1 →
      (∀ s : ℝ≥0, s ≤ tau →
        euclideanNorm (lam • Y ((k : ℝ≥0) * tau + s) - c k) < eps / 2) ∧
      euclideanNorm (lam • Y ((k : ℝ≥0) * tau + tau) - c (k + 1)) < eps / 16) :
    euclideanNorm (lam • Y (((n + 1 : ℕ) : ℝ≥0) * tau) - c (n + 1)) < eps / 16 := by
  have h := (hY n (by omega)).2
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h

/-- The scaled mesh time agrees with repeated addition of the block duration. -/
theorem c16_scaled_mesh_time (lam h : ℝ) (hlam : 0 < lam) (hh : 0 < h)
    (k : ℕ) :
    (k : ℝ≥0) * (h / lam ^ 2).toNNReal =
      (((k : ℝ) * h) / lam ^ 2).toNNReal := by
  have hl : 0 ≤ lam ^ 2 := (sq_pos_of_pos hlam).le
  have hk : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_natCast,
    Real.coe_toNNReal _ (div_nonneg hh.le hl), Real.coe_toNNReal _ (div_nonneg hk hl)]
  ring

/-- A uniform one-block estimate yields the concrete finite tube bound. -/
theorem c16_concrete_block_tube_probability {d : ℕ} {hd : 2≤d} {L : ℝ} {hL : 1≤L} {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0≤lam} {h₁ : lam≤1}
 (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
 (N : ℕ) (hN : 0<N) (h eps eta : ℝ) (hlam : 0<lam) (hh : 0<h) (heps : 0<eps) (heta : 0≤eta)
 (gamma : ℝ → Vec d) (x₀ : Vec d) (hstart : euclideanNorm (lam • x₀-gamma 0)<eps/16)
 (hosc : ∀ k : ℕ, k<N → ∀ u : ℝ, (k:ℝ)*h≤u → u≤(k+1:ℕ)*h → euclideanNorm (gamma u-gamma ((k:ℝ)*h))≤eps/16) :
 let tau : ℝ≥0 := (h/lam^2).toNNReal
 let c : ℕ → Vec d := fun k => gamma ((k:ℝ)*h)
 let piece : ℕ → Set (Path d) := fun k => {Y | (∀ s : ℝ≥0, s≤tau → euclideanNorm (lam • Y s-c k)<eps/2) ∧ euclideanNorm (lam • Y tau-c (k+1))<eps/16}
 (∀ k : ℕ, k<N → ∀ x : Vec d, euclideanNorm (lam • x-c k)<eps/16 → ENNReal.ofReal eta≤G.pathLaw x (piece k)) →
 ENNReal.ofReal (eta^N)≤G.pathLaw x₀ {Y | ∀ u : ℝ≥0, (u:ℝ)≤(N:ℝ)*h → euclideanNorm (lam • Y ((u:ℝ)/lam^2).toNNReal-gamma (u:ℝ))<eps} := by
  dsimp only
  intro hstep
  let tau : ℝ≥0 := (h / lam ^ 2).toNNReal
  let c : ℕ → Vec d := fun k => gamma ((k : ℝ) * h)
  let piece : ℕ → Set (Path d) := fun k => {Y | (∀ s : ℝ≥0, s ≤ tau → euclideanNorm (lam • Y s - c k) < eps / 2) ∧ euclideanNorm (lam • Y tau - c (k+1)) < eps / 16}
  let E : ℕ → Set (Path d) := fun n => {Y | ∀ k : ℕ, k < n → gmpShiftPath ((k : ℝ≥0) * tau) Y ∈ piece k}
  let A : ℕ → Set (Vec d) := fun n => {x | euclideanNorm (lam • x - c n) < eps / 16}
  apply c16_actual_finite_tube_probability G N tau eta heta x₀ A piece E
  · intro n
    exact c13_tube_block_measurable lam eps tau (c n) (c (n+1))
  · exact c13_finite_block_prefix_past lam eps tau c
  · ext Y
    simp [E]
  · intro n
    ext Y
    simp only [E, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro hY
      exact ⟨fun k hk => hY k (by omega), hY n (by omega)⟩
    · rintro ⟨hY, hn⟩ k hk
      by_cases hkn : k = n
      · simpa only [hkn] using hn
      · exact hY k (by omega)
  · intro n hn
    cases n with
    | zero =>
      filter_upwards [G.pathLaw_starts_at x₀] with Y hY
      intro _
      change Y 0 = x₀ at hY
      simpa [A, c, hY] using hstart
    | succ n =>
      filter_upwards with Y
      intro hY
      have h := (hY n (by omega)).2
      simpa only [A, Set.mem_ofPred_eq, gmpShiftPath, ContinuousMap.coe_mk,
        Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h
  · exact hstep
  · exact hN
  · exact hlam
  · exact hh
  · exact heps
  · rfl
  · exact hosc
  · intro Y hY k hk s hs
    have hs' : s ≤ tau := by
      apply NNReal.coe_le_coe.mp
      simpa only [tau, Real.coe_toNNReal _ (div_nonneg hh.le (sq_pos_of_pos hlam).le)] using hs
    have hb := (hY k hk).1 s hs'
    have htime : (k : ℝ≥0) * tau = (((k : ℝ) * h) / lam ^ 2).toNNReal :=
      c16_scaled_mesh_time lam h hlam hh k
    simpa only [piece, Set.mem_ofPred_eq, gmpShiftPath, ContinuousMap.coe_mk,
      c, htime] using hb


/-- Rescaling time maps the source block interval exactly onto the raw interval. -/
theorem c16_source_piece_eq_raw_time {d : ℕ} (lam h eps : ℝ)
    (hlam : 0 < lam) (hh : 0 < h) (c cnext : Vec d) :
    {Y : Path d | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
      euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - c) < eps / 2) ∧
      euclideanNorm (lam • Y (h / lam ^ 2).toNNReal - cnext) < eps / 16} =
    {Y : Path d | (∀ s : ℝ≥0, s ≤ (h / lam ^ 2).toNNReal →
      euclideanNorm (lam • Y s - c) < eps / 2) ∧
      euclideanNorm (lam • Y (h / lam ^ 2).toNNReal - cnext) < eps / 16} := by
  have hl : 0 < lam ^ 2 := sq_pos_of_pos hlam
  ext Y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨htube, hend⟩
    refine ⟨?_, hend⟩
    intro s hs
    let u : ℝ≥0 := (lam ^ 2 * (s : ℝ)).toNNReal
    have hu : (u : ℝ) ≤ h := by
      have hs' : (s : ℝ) ≤ h / lam ^ 2 := by
        exact le_trans (NNReal.coe_le_coe.mpr hs)
          (le_of_eq (Real.coe_toNNReal _ (div_nonneg hh.le hl.le)))
      change ((lam ^ 2 * (s : ℝ)).toNNReal : ℝ) ≤ h
      rw [Real.coe_toNNReal _ (mul_nonneg hl.le s.coe_nonneg)]
      have hs'' := (le_div_iff₀ hl).mp hs'
      simpa only [mul_comm] using hs''
    have htime : ((u : ℝ) / lam ^ 2).toNNReal = s := by
      apply NNReal.eq
      change (((((lam ^ 2 * (s : ℝ)).toNNReal : ℝ) / lam ^ 2).toNNReal : ℝ)) = (s : ℝ)
      rw [Real.coe_toNNReal _ (mul_nonneg hl.le s.coe_nonneg)]
      rw [Real.coe_toNNReal _ (div_nonneg (mul_nonneg hl.le s.coe_nonneg) hl.le)]
      field_simp
    simpa only [htime] using htube u hu
  · rintro ⟨htube, hend⟩
    refine ⟨?_, hend⟩
    intro u hu
    apply htube
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (div_nonneg u.coe_nonneg hl.le),
      Real.coe_toNNReal _ (div_nonneg hh.le hl.le)]
    exact div_le_div_of_nonneg_right hu hl.le

/-- The concrete tube estimate with the source's rescaled-time block events. -/
theorem c16_source_block_tube_probability {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (N : ℕ) (hN : 0 < N) (h eps eta : ℝ) (hlam : 0 < lam) (hh : 0 < h) (heps : 0 < eps) (heta : 0 ≤ eta)
    (gamma : ℝ → Vec d) (x₀ : Vec d) (hstart : euclideanNorm (lam • x₀ - gamma 0) < eps / 16)
    (hosc : ∀ k : ℕ, k < N → ∀ u : ℝ, (k : ℝ) * h ≤ u → u ≤ (k+1 : ℕ) * h → euclideanNorm (gamma u - gamma ((k : ℝ) * h)) ≤ eps / 16)
    (hstep : ∀ k : ℕ, k < N → ∀ x : Vec d, euclideanNorm (lam • x - gamma ((k : ℝ) * h)) < eps / 16 →
      ENNReal.ofReal eta ≤ G.pathLaw x {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - gamma ((k : ℝ) * h)) < eps / 2) ∧
        euclideanNorm (lam • Y (h / lam ^ 2).toNNReal - gamma (((k+1 : ℕ) : ℝ) * h)) < eps / 16}) :
    ENNReal.ofReal (eta ^ N) ≤ G.pathLaw x₀ {Y | ∀ u : ℝ≥0, (u : ℝ) ≤ (N : ℝ) * h →
      euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - gamma (u : ℝ)) < eps} := by
  apply c16_concrete_block_tube_probability G N hN h eps eta hlam hh heps heta gamma x₀ hstart hosc
  intro k hk x hx
  have hs := hstep k hk x hx
  rw [c16_source_piece_eq_raw_time lam h eps hlam hh (gamma ((k : ℝ) * h))
    (gamma (((k+1 : ℕ) : ℝ) * h))] at hs
  exact hs

/-- Assemble the supplied quenched one-step estimates into a finite tube bound. -/
theorem c16_quenched_actual_tube_of_steps {d : ℕ} (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (lam : ℝ) (hlam : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam hlam.le h₁ P)
    (N : ℕ) (hN : 0 < N) (h eps eta : ℝ) (hh : 0 < h) (heps : 0 < eps) (heta : 0 ≤ eta)
    (gamma : ℝ → Vec d) (hzero : gamma 0 = 0)
    (hosc : ∀ k : ℕ, k < N → ∀ u : ℝ, (k : ℝ) * h ≤ u → u ≤ (k+1 : ℕ) * h →
      euclideanNorm (gamma u - gamma ((k : ℝ) * h)) ≤ eps / 16)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < N → ∀ x : Vec d,
      euclideanNorm (x - gamma ((k : ℝ) * h)) < eps / 16 →
      ENNReal.ofReal eta ≤ P (lam⁻¹ • x, ω) {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - gamma ((k : ℝ) * h)) < eps / 2) ∧
        euclideanNorm (lam • Y (h / lam ^ 2).toNNReal - gamma (((k+1 : ℕ) : ℝ) * h)) < eps / 16}) :
    ∀ᵐ ω ∂Q.measure, ENNReal.ofReal (eta ^ N) ≤ P (0, ω) {Y | ∀ u : ℝ≥0,
      (u : ℝ) ≤ (N : ℝ) * h → euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - gamma (u : ℝ)) < eps} := by
  filter_upwards [hP, hstep] with ω hreal hstepω
  obtain ⟨hω, G, hG⟩ := hreal
  rw [hG 0]
  apply c16_source_block_tube_probability G N hN h eps eta hlam hh heps heta gamma 0
  · have hn : euclideanNorm (0 : Vec d) = 0 := by
      unfold euclideanNorm euclideanSq dot
      simp
    simpa [hzero, hn] using (show (0 : ℝ) < eps / 16 by positivity)
  · exact hosc
  · intro k hk x hx
    have hs := hstepω k hk (lam • x) hx
    have hscale : lam⁻¹ • (lam • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hlam), one_smul]
    rw [hscale, hG x] at hs
    exact hs

end
end EinsteinFull
