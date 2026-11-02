import EinsteinFull.Calculus.ParabolicBridgeMolShift

/-!
# The delayed kernel and the adjoint time average

`ker ε r = tmoll ε (r - 2ε)` is supported in `[ε, 3ε]`, so that
`MolS ε F (y, t) = ∫ ker (t - s) F (y, s) ds` only uses `F` at times `s ∈ [t - 3ε, t - ε]`.
`Tcv Ψ (y, s) = ∫ ker u Ψ (y, s + u) du` is the adjoint time average:
`∫ MolS H · Ψ = ∫ H · Tcv Ψ`.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ} {ε : ℝ} {hε : 0 < ε}

/-- The delayed kernel. -/
def ker (ε : ℝ) (hε : 0 < ε) (r : ℝ) : ℝ := tmoll ε hε (r - 2 * ε)

theorem ker_nonneg (r : ℝ) : 0 ≤ ker ε hε r := tmoll_nonneg _

theorem ker_continuous : Continuous (ker ε hε) :=
  tmoll_continuous.comp (continuous_id.sub continuous_const)

theorem ker_integrable : Integrable (ker ε hε) volume :=
  tmoll_integrable.comp_sub_right (2 * ε)

theorem ker_integral : ∫ r, ker ε hε r = 1 := by
  unfold ker
  rw [integral_sub_right_eq_self (fun r => tmoll ε hε r) (2 * ε)]
  exact tmoll_integral

theorem ker_eq_zero {r : ℝ} (h : r ≤ ε ∨ 3 * ε ≤ r) : ker ε hε r = 0 := by
  apply tmoll_eq_zero
  rcases h with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem ker_hasCompactSupport : HasCompactSupport (ker ε hε) :=
  tmoll_hasCompactSupport.comp_homeomorph (Homeomorph.subRight (2 * ε))

theorem ker_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ r, |ker ε hε r| ≤ B := by
  obtain ⟨B, hB⟩ := ker_continuous.bounded_above_of_compact_support
    (ker_hasCompactSupport (ε := ε) (hε := hε))
  exact ⟨B, (norm_nonneg _).trans (hB 0), fun r => by simpa using hB r⟩

theorem MolS_eq (F : Vec d × ℝ → ℝ) (z : Vec d × ℝ) :
    MolS ε hε F z = ∫ s, ker ε hε (z.2 - s) * F (z.1, s) := by
  rw [MolS_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show tmoll ε hε (z.2 - 2 * ε - s) * F (z.1, s) = tmoll ε hε (z.2 - s - 2 * ε) * F (z.1, s)
  rw [sub_right_comm z.2 (2 * ε) s]

theorem integrable_ker_slice (F : Vec d × ℝ → ℝ) (hF : Measurable F) (y : Vec d)
    (hy : ∫⁻ t : ℝ, ‖F (y, t)‖ₑ ^ (2 : ℝ) < ⊤) (t : ℝ) :
    Integrable (fun s => ker ε hε (t - s) * F (y, s)) volume := by
  refine (integrable_slice_mol (ε := ε) (hε := hε) F hF y hy (t - 2 * ε)).congr
    (Filter.Eventually.of_forall fun s => ?_)
  show tmoll ε hε (t - 2 * ε - s) * F (y, s) = tmoll ε hε (t - s - 2 * ε) * F (y, s)
  rw [sub_right_comm t (2 * ε) s]

theorem hasCompactSupport_slice (Ψ : Vec d × ℝ → ℝ) (hc : HasCompactSupport Ψ) (y : Vec d) :
    HasCompactSupport fun t => Ψ (y, t) := by
  have hK : IsCompact (Prod.snd '' tsupport Ψ) :=
    (show IsCompact (tsupport Ψ) from hc).image continuous_snd
  show IsCompact (tsupport fun t => Ψ (y, t))
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  intro t ht
  exact ⟨(y, t), subset_tsupport Ψ ht, rfl⟩

/-- The adjoint time average. -/
def Tcv (ε : ℝ) (hε : 0 < ε) (Ψ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  ∫ u, ker ε hε u * Ψ (z.1, z.2 + u)

theorem Tcv_continuous (Ψ : Vec d × ℝ → ℝ) (hΨ : Continuous Ψ) (hc : HasCompactSupport Ψ) :
    Continuous (Tcv ε hε Ψ) := by
  obtain ⟨C, hC⟩ := hΨ.bounded_above_of_compact_support hc
  unfold Tcv
  refine continuous_of_dominated (bound := fun u => ‖ker ε hε u‖ * C) ?_ ?_ ?_ ?_
  · intro z
    exact (ker_continuous.mul
      (hΨ.comp (continuous_const.prodMk (continuous_const.add continuous_id)))).aestronglyMeasurable
  · intro z
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · exact ker_integrable.norm.mul_const _
  · refine Filter.Eventually.of_forall fun u => ?_
    exact continuous_const.mul
      (hΨ.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)))

theorem Tcv_norm_le (Ψ : Vec d × ℝ → ℝ) {C : ℝ} (hC : ∀ x, ‖Ψ x‖ ≤ C) (z : Vec d × ℝ) :
    ‖Tcv ε hε Ψ z‖ ≤ C := by
  unfold Tcv
  refine (norm_integral_le_of_norm_le
    ((ker_integrable (ε := ε) (hε := hε)).norm.mul_const C)
    (Filter.Eventually.of_forall fun u => ?_)).trans ?_
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · rw [integral_mul_const]
    have : ∫ u, ‖ker ε hε u‖ = 1 := by
      rw [← ker_integral (ε := ε) (hε := hε)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (ker_nonneg u)])
    rw [this, one_mul]

/-- Adjointness of the delayed mollification and the adjoint time average. -/
theorem integral_MolS_mul (H Ψ : Vec d × ℝ → ℝ) (hHm : Measurable H)
    (hH1 : Integrable H volume) (hH2 : MemLp H 2 volume) (hΨ : Continuous Ψ)
    (hc : HasCompactSupport Ψ) :
    ∫ z, MolS ε hε H z * Ψ z = ∫ z, H z * Tcv ε hε Ψ z := by
  have hΨ2 : MemLp Ψ 2 volume := hΨ.memLp_of_hasCompactSupport hc
  have hMS2 : MemLp (MolS ε hε H) 2 volume := (eLpNorm_MolS_le H hHm).trans_lt hH2
  have hf1 : Integrable (fun z => MolS ε hε H z * Ψ z) volume := hMS2.integrable_mul hΨ2
  have hTc : Continuous (Tcv ε hε Ψ) := Tcv_continuous Ψ hΨ hc
  obtain ⟨C, hC⟩ := hΨ.bounded_above_of_compact_support hc
  have hf2 : Integrable (fun z => H z * Tcv ε hε Ψ z) volume :=
    hH1.mul_bdd (c := C) hTc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => Tcv_norm_le Ψ hC z)
  have hay : ∀ᵐ y : Vec d, Integrable (fun s => H (y, s)) volume := by
    have h := hH1
    rw [Measure.volume_eq_prod] at h
    exact h.prod_right_ae
  obtain ⟨B, hB0, hB⟩ := ker_bound (ε := ε) (hε := hε)
  rw [Measure.volume_eq_prod] at hf1 hf2 ⊢
  rw [integral_prod _ hf1, integral_prod _ hf2]
  refine integral_congr_ae ?_
  filter_upwards [hay] with y hHy
  have hΨy : Integrable (fun t => Ψ (y, t)) volume :=
    (hΨ.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (hasCompactSupport_slice Ψ hc y)
  have e1 : ∀ t : ℝ, MolS ε hε H (y, t) * Ψ (y, t) =
      ∫ s, ker ε hε (t - s) * H (y, s) * Ψ (y, t) := by
    intro t
    rw [MolS_eq, ← integral_mul_const]
  simp_rw [e1]
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ker ε hε (p.1 - p.2) * H (y, p.2) * Ψ (y, p.1))
      (volume.prod volume) :=
    (((ker_continuous.measurable.comp (measurable_fst.sub measurable_snd)).mul
      (hHm.comp (measurable_const.prodMk measurable_snd))).mul
      (hΨ.measurable.comp (measurable_const.prodMk measurable_fst))).aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun t s : ℝ =>
      ker ε hε (t - s) * H (y, s) * Ψ (y, t)) (volume.prod volume) := by
    refine Integrable.mono' (g := fun p : ℝ × ℝ => B * (‖Ψ (y, p.1)‖ * ‖H (y, p.2)‖))
      ((hΨy.norm.mul_prod hHy.norm).const_mul B) hmeas (Filter.Eventually.of_forall fun p => ?_)
    show ‖ker ε hε (p.1 - p.2) * H (y, p.2) * Ψ (y, p.1)‖ ≤ B * (‖Ψ (y, p.1)‖ * ‖H (y, p.2)‖)
    rw [norm_mul, norm_mul]
    calc ‖ker ε hε (p.1 - p.2)‖ * ‖H (y, p.2)‖ * ‖Ψ (y, p.1)‖
        = ‖ker ε hε (p.1 - p.2)‖ * (‖Ψ (y, p.1)‖ * ‖H (y, p.2)‖) := by ring
      _ ≤ B * (‖Ψ (y, p.1)‖ * ‖H (y, p.2)‖) :=
        mul_le_mul_of_nonneg_right (by simpa using hB (p.1 - p.2))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  beta_reduce
  have e2 : ∫ t, ker ε hε (t - s) * H (y, s) * Ψ (y, t) =
      H (y, s) * ∫ t, ker ε hε (t - s) * Ψ (y, t) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  rw [e2]
  congr 1
  have h3 := integral_add_left_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => ker ε hε (t - s) * Ψ (y, t)) s
  simp only [add_sub_cancel_left] at h3
  exact h3.symm

end EinsteinFull.ParabolicBridge
