import EinsteinFull.Frozen.RegenerationCoupling
import EinsteinFull.Calculus.FellerRegularSet
import EinsteinFull.Work.W1.GMPFullPastRestartSupport

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- A strict Euclidean tube on a complete compact time block, with a strict
endpoint constraint, is a Borel event on the continuous path space. -/
theorem c13_tube_block_measurable {d : ℕ} (lam eps : ℝ) (T : ℝ≥0) (c cnext : Vec d) :
    MeasurableSet {Y : Path d | (∀ s : ℝ≥0, s ≤ T → euclideanNorm (lam • Y s - c) < eps / 2) ∧ euclideanNorm (lam • Y T - cnext) < eps / 16} := by
  let F : Path d → C(ℝ≥0, ℝ) := fun Y =>
    ⟨fun s => euclideanNorm (lam • Y s - c),
      (Calculus.Feller.continuous_euclideanNorm d).comp
        ((continuous_const.fun_smul Y.continuous).sub continuous_const)⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (Calculus.Feller.continuous_euclideanNorm d).comp
      ((continuous_const.fun_smul continuous_eval).sub continuous_const)
  have hblock := (ContinuousMap.isOpen_setOfPred_mapsTo
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) T))
    (isOpen_Iio : IsOpen (Set.Iio (eps / 2)))).preimage hF
  have hend : Continuous (fun Y : Path d => euclideanNorm (lam • Y T - cnext)) :=
    (Calculus.Feller.continuous_euclideanNorm d).comp
      ((continuous_const.fun_smul (continuous_eval_const T)).sub continuous_const)
  have heq : {Y : Path d | (∀ s : ℝ≥0, s ≤ T →
      euclideanNorm (lam • Y s - c) < eps / 2) ∧
      euclideanNorm (lam • Y T - cnext) < eps / 16} =
      (F ⁻¹' {f | Set.MapsTo f (Set.Icc 0 T) (Set.Iio (eps / 2))}) ∩
        {Y | euclideanNorm (lam • Y T - cnext) < eps / 16} := by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.MapsTo, Set.mem_Icc, Set.mem_Iio, F, ContinuousMap.coe_mk, zero_le, true_and]
  rw [heq]
  exact hblock.measurableSet.inter (hend.measurable measurableSet_Iio)


/-- The tube block depends only on the path through its endpoint. -/
theorem c13_tube_block_past_measurable {d : ℕ} (lam eps : ℝ) (T : ℝ≥0) (c cnext : Vec d) :
    MeasurableSet[gmpPastSigma T] {Y : Path d | (∀ s : ℝ≥0, s ≤ T → euclideanNorm (lam • Y s - c) < eps / 2) ∧ euclideanNorm (lam • Y T - cnext) < eps / 16} := by
  rw [← comap_gmpPrefixPath_eq_gmpPastSigma]
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨_, c13_tube_block_measurable lam eps T c cnext, ?_⟩
  ext Y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, gmpPrefixPath, ContinuousMap.coe_mk,
    min_self]
  constructor <;> intro h <;> refine ⟨?_, h.2⟩ <;> intro s hs
  · simpa only [min_eq_left hs] using h.1 s hs
  · simpa only [min_eq_left hs] using h.1 s hs


/-- Rescaling time identifies the source and raw finite-prefix tube events. -/
theorem c13_source_prefix_eq_raw_prefix {d : ℕ} (lam h eps : ℝ) (hlam : 0 < lam)
    (hh : 0 < h) (c : ℕ → Vec d) (n : ℕ) :
    {Y : Path d | ∀ k : ℕ, k < n →
      (∀ u : ℝ≥0, (u : ℝ) ≤ h → euclideanNorm
        (lam • Y (((k : ℝ) * h + (u : ℝ)) / lam ^ 2).toNNReal - c k) < eps / 2) ∧
      euclideanNorm (lam • Y ((((k + 1 : ℕ) : ℝ) * h) / lam ^ 2).toNNReal - c (k + 1)) < eps / 16} =
    {Y : Path d | ∀ k : ℕ, k < n →
      (∀ s : ℝ≥0, s ≤ (h / lam ^ 2).toNNReal → euclideanNorm
        (lam • Y (((k : ℝ) * h / lam ^ 2).toNNReal + s) - c k) < eps / 2) ∧
      euclideanNorm (lam • Y ((((k + 1 : ℕ) : ℝ) * h) / lam ^ 2).toNNReal - c (k + 1)) < eps / 16} := by
  have hl : 0 < lam ^ 2 := sq_pos_of_pos hlam
  have htime (k : ℕ) (u : ℝ≥0) :
      (((k : ℝ) * h + (u : ℝ)) / lam ^ 2).toNNReal =
        (((k : ℝ) * h) / lam ^ 2).toNNReal + ((u : ℝ) / lam ^ 2).toNNReal := by
    have hk : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh.le
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ (div_nonneg hk hl.le),
      Real.coe_toNNReal _ (div_nonneg u.coe_nonneg hl.le),
      Real.coe_toNNReal _ (div_nonneg (add_nonneg hk u.coe_nonneg) hl.le)]
    ring
  ext Y
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hsource k hk
    obtain ⟨htube, hend⟩ := hsource k hk
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
    have hu_time : ((u : ℝ) / lam ^ 2).toNNReal = s := by
      apply NNReal.eq
      change (((((lam ^ 2 * (s : ℝ)).toNNReal : ℝ) / lam ^ 2).toNNReal : ℝ)) = (s : ℝ)
      rw [Real.coe_toNNReal _ (mul_nonneg hl.le s.coe_nonneg)]
      rw [Real.coe_toNNReal _ (div_nonneg (mul_nonneg hl.le s.coe_nonneg) hl.le)]
      field_simp
    simpa only [htime, hu_time] using htube u hu
  · intro hraw k hk
    obtain ⟨htube, hend⟩ := hraw k hk
    refine ⟨?_, hend⟩
    intro u hu
    have hu' : ((u : ℝ) / lam ^ 2).toNNReal ≤ (h / lam ^ 2).toNNReal := by
      apply Real.toNNReal_le_toNNReal
      exact div_le_div_of_nonneg_right hu hl.le
    simpa only [htime] using htube ((u : ℝ) / lam ^ 2).toNNReal hu'

/-- The rescaled block event is measurable in the natural past at its endpoint. -/
@[nolint unusedArguments]
theorem c13_source_rescaled_block_past {d : ℕ} (lam h eps : ℝ) (hlam : 0 < lam)
    (hh : 0 < h) (k : ℕ) (c cnext : Vec d) :
    MeasurableSet[gmpPastSigma (((k+1:ℕ):ℝ)*h/lam^2).toNNReal] {Y : Path d |
      (∀ u : ℝ≥0, (u:ℝ) ≤ h → euclideanNorm
        (lam • Y (((k:ℝ)*h+(u:ℝ))/lam^2).toNNReal-c)<eps/2) ∧
      euclideanNorm (lam • Y ((((k+1:ℕ):ℝ)*h)/lam^2).toNNReal-cnext)<eps/16} := by
  let t : ℝ≥0 → ℝ≥0 := fun u => (((k : ℝ) * h + (u : ℝ)) / lam ^ 2).toNNReal
  have ht : Continuous t := continuous_real_toNNReal.comp
    ((continuous_const.add continuous_subtype_val).div_const _)
  let F : Path d → Path d := fun Y => ⟨fun u => Y (t u), Y.continuous.comp ht⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_fst.eval (ht.comp continuous_snd)
  have htime : t h.toNNReal = (((k + 1 : ℕ) : ℝ) * h / lam ^ 2).toNNReal := by
    dsimp [t]
    rw [max_eq_left hh.le]
    congr 1
    push_cast
    ring
  let E : Set (Path d) := {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
      euclideanNorm (lam • Y (t u) - c) < eps / 2) ∧
      euclideanNorm (lam • Y (t h.toNNReal) - cnext) < eps / 16}
  have hE : MeasurableSet E := by
    have heq : E = F ⁻¹' {Y | (∀ u : ℝ≥0, u ≤ h.toNNReal →
        euclideanNorm (lam • Y u - c) < eps / 2) ∧
        euclideanNorm (lam • Y h.toNNReal - cnext) < eps / 16} := by
      ext Y
      simp only [E, Set.mem_setOf_eq, Set.mem_preimage, F, ContinuousMap.coe_mk,
        ← NNReal.coe_le_coe, Real.coe_toNNReal _ hh.le]
    rw [heq]
    exact (c13_tube_block_measurable lam eps h.toNNReal c cnext).preimage hF.measurable
  have hbound : ∀ u : ℝ≥0, (u : ℝ) ≤ h → t u ≤ t h.toNNReal := by
    intro u hu
    apply Real.toNNReal_le_toNNReal
    apply div_le_div_of_nonneg_right _ (sq_nonneg lam)
    rw [Real.coe_toNNReal _ hh.le]
    linarith
  rw [← htime]
  change MeasurableSet[gmpPastSigma (t h.toNNReal)] E
  rw [← comap_gmpPrefixPath_eq_gmpPastSigma]
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨E, hE, ?_⟩
  ext Y
  simp only [Set.mem_preimage, E, Set.mem_setOf_eq, gmpPrefixPath, ContinuousMap.coe_mk,
    min_self]
  constructor <;> intro hy <;> refine ⟨?_, hy.2⟩ <;> intro u hu
  · simpa only [min_eq_left (hbound u hu)] using hy.1 u hu
  · simpa only [min_eq_left (hbound u hu)] using hy.1 u hu

/-- A finite family of rescaled tube blocks is measurable by its final endpoint. -/
theorem c13_source_rescaled_finite_prefix_past {d : ℕ} (lam h eps : ℝ)
    (hlam : 0 < lam) (hh : 0 < h) (c : ℕ → Vec d) (n : ℕ) :
    MeasurableSet[gmpPastSigma (((n : ℝ) * h) / lam ^ 2).toNNReal]
      {Y : Path d | ∀ k : ℕ, k < n →
        (∀ u : ℝ≥0, (u : ℝ) ≤ h → euclideanNorm
          (lam • Y (((k : ℝ) * h + (u : ℝ)) / lam ^ 2).toNNReal - c k) < eps / 2) ∧
        euclideanNorm (lam • Y ((((k + 1 : ℕ) : ℝ) * h) / lam ^ 2).toNNReal -
          c (k + 1)) < eps / 16} := by
  have hmono : ∀ {s t : ℝ≥0}, s ≤ t →
      gmpPastSigma (d := d) s ≤ gmpPastSigma t := by
    intro s t hst
    unfold gmpPastSigma
    apply iSup_le
    intro u
    exact le_iSup_of_le ⟨u.val, le_trans u.property hst⟩ le_rfl
  have heq : {Y : Path d | ∀ k : ℕ, k < n →
        (∀ u : ℝ≥0, (u : ℝ) ≤ h → euclideanNorm
          (lam • Y (((k : ℝ) * h + (u : ℝ)) / lam ^ 2).toNNReal - c k) < eps / 2) ∧
        euclideanNorm (lam • Y ((((k + 1 : ℕ) : ℝ) * h) / lam ^ 2).toNNReal -
          c (k + 1)) < eps / 16} =
      ⋂ k : ℕ, ⋂ (_ : k < n), {Y : Path d |
        (∀ u : ℝ≥0, (u : ℝ) ≤ h → euclideanNorm
          (lam • Y (((k : ℝ) * h + (u : ℝ)) / lam ^ 2).toNNReal - c k) < eps / 2) ∧
        euclideanNorm (lam • Y ((((k + 1 : ℕ) : ℝ) * h) / lam ^ 2).toNNReal -
          c (k + 1)) < eps / 16} := by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro hk
  have ht : (((k + 1 : ℕ) : ℝ) * h / lam ^ 2).toNNReal ≤
      (((n : ℝ) * h) / lam ^ 2).toNNReal := by
    apply Real.toNNReal_le_toNNReal
    apply div_le_div_of_nonneg_right _ (sq_nonneg lam)
    apply mul_le_mul_of_nonneg_right _ hh.le
    exact_mod_cast Nat.succ_le_of_lt hk
  exact hmono ht _ (c13_source_rescaled_block_past lam h eps hlam hh k (c k) (c (k + 1)))

/-- A finite sequence of tube blocks is measurable by the end of the sequence. -/
theorem c13_finite_block_prefix_past {d : ℕ} (lam eps : ℝ) (tau : ℝ≥0) (c : ℕ → Vec d) :
    let piece : ℕ → Set (Path d) := fun k => {Y | (∀ s : ℝ≥0, s ≤ tau → euclideanNorm (lam • Y s - c k) < eps/2) ∧ euclideanNorm (lam • Y tau-c (k+1)) < eps/16}
    let E : ℕ → Set (Path d) := fun n => {Y | ∀ k : ℕ, k<n → gmpShiftPath ((k:ℝ≥0)*tau) Y ∈ piece k}
    ∀ n : ℕ, MeasurableSet[gmpPastSigma ((n:ℝ≥0)*tau)] (E n) := by
  dsimp only
  intro n
  let E : Set (Path d) := {Y | ∀ k : ℕ, k < n →
    gmpShiftPath ((k : ℝ≥0) * tau) Y ∈
      {Y | (∀ s : ℝ≥0, s ≤ tau → euclideanNorm (lam • Y s - c k) < eps / 2) ∧
        euclideanNorm (lam • Y tau - c (k+1)) < eps / 16}}
  have hE : MeasurableSet E := by
    have hset : E = (⋂ k : ℕ, ⋂ (_ : k < n),
      (gmpShiftPath ((k : ℝ≥0) * tau)) ⁻¹'
        {Y | (∀ s : ℝ≥0, s ≤ tau → euclideanNorm (lam • Y s - c k) < eps / 2) ∧
          euclideanNorm (lam • Y tau - c (k+1)) < eps / 16}) := by
      ext Y
      simp [E]
    rw [hset]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (c13_tube_block_measurable lam eps tau (c k) (c (k+1))).preimage
        (measurable_gmpShiftPath _)
  change MeasurableSet[gmpPastSigma ((n : ℝ≥0) * tau)] E
  rw [← comap_gmpPrefixPath_eq_gmpPastSigma]
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨E, hE, ?_⟩
  ext Y
  simp only [Set.mem_preimage, E, Set.mem_setOf_eq, gmpShiftPath, gmpPrefixPath,
    ContinuousMap.coe_mk]
  have hbound : ∀ k : ℕ, k < n → ∀ s : ℝ≥0, s ≤ tau →
      (k : ℝ≥0) * tau + s ≤ (n : ℝ≥0) * tau := by
    intro k hk s hs
    have hkn : (k : ℝ≥0) + 1 ≤ (n : ℝ≥0) := by
      exact_mod_cast Nat.succ_le_of_lt hk
    calc
      (k : ℝ≥0) * tau + s ≤ (k : ℝ≥0) * tau + tau := add_le_add_right hs _
      _ = ((k : ℝ≥0) + 1) * tau := by rw [add_mul, one_mul]
      _ ≤ (n : ℝ≥0) * tau := by simpa only [mul_comm] using mul_le_mul_right hkn tau
  constructor <;> intro h k hk <;> have hb := hbound k hk
  · refine ⟨?_, ?_⟩
    · intro s hs
      simpa only [min_eq_left (hb s hs)] using (h k hk).1 s hs
    · simpa only [min_eq_left (hb tau le_rfl)] using (h k hk).2
  · refine ⟨?_, ?_⟩
    · intro s hs
      simpa only [min_eq_left (hb s hs)] using (h k hk).1 s hs
    · simpa only [min_eq_left (hb tau le_rfl)] using (h k hk).2

/-- Each nonempty finite sequence of tube blocks ends in its next entrance ball. -/
theorem c13_finite_block_prefix_entrance {d : ℕ} (lam eps : ℝ) (tau : ℝ≥0) (c : ℕ → Vec d) :
    let piece : ℕ → Set (Path d) := fun k => {Y | (∀ s : ℝ≥0, s ≤ tau → euclideanNorm (lam • Y s - c k) < eps/2) ∧ euclideanNorm (lam • Y tau-c (k+1)) < eps/16}
    let E : ℕ → Set (Path d) := fun n => {Y | ∀ k : ℕ, k<n → gmpShiftPath ((k:ℝ≥0)*tau) Y ∈ piece k}
    ∀ n : ℕ, 0<n → ∀ Y ∈ E n, euclideanNorm (lam • Y ((n:ℝ≥0)*tau)-c n)<eps/16 := by
  dsimp only
  intro n hn Y hY
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := (hY k (Nat.lt_succ_self k)).2
  simpa only [gmpShiftPath, ContinuousMap.coe_mk, Nat.cast_succ, add_mul, one_mul] using h

end EinsteinFull
