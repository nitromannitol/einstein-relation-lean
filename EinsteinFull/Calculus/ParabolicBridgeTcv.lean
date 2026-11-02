import EinsteinFull.Calculus.ParabolicBridgeKernel

/-!
# Regularity and support of the adjoint time average
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ} {ε : ℝ} {hε : 0 < ε}

theorem Tcv_exists_of_ne_zero (Ψ : Vec d × ℝ → ℝ) (K : Set (Vec d × ℝ))
    (hK : ∀ z, Ψ z ≠ 0 → z ∈ K) (z : Vec d × ℝ) (hz : Tcv ε hε Ψ z ≠ 0) :
    ∃ u ∈ Icc ε (3 * ε), (z.1, z.2 + u) ∈ K := by
  by_contra hcon
  push_neg at hcon
  apply hz
  unfold Tcv
  have h : (fun u => ker ε hε u * Ψ (z.1, z.2 + u)) = fun _ => 0 := by
    funext u
    by_cases hu : u ∈ Icc ε (3 * ε)
    · have h0 : Ψ (z.1, z.2 + u) = 0 := by
        by_contra hne
        exact hcon u hu (hK _ hne)
      rw [h0, mul_zero]
    · have h0 : ker ε hε u = 0 := by
        apply ker_eq_zero
        by_contra h'
        push_neg at h'
        exact hu ⟨h'.1.le, h'.2.le⟩
      rw [h0, zero_mul]
  rw [h]
  simp

theorem hasFDerivAt_shift (Ψ : Vec d × ℝ → ℝ) (hΨ : Differentiable ℝ Ψ) (u : ℝ)
    (z : Vec d × ℝ) :
    HasFDerivAt (fun x : Vec d × ℝ => Ψ (x.1, x.2 + u)) (fderiv ℝ Ψ (z.1, z.2 + u)) z := by
  have h1 : HasFDerivAt (fun x : Vec d × ℝ => (x.1, x.2 + u))
      (ContinuousLinearMap.id ℝ (Vec d × ℝ)) z := by
    have h : (fun x : Vec d × ℝ => (x.1, x.2 + u)) = fun x => x + (0, u) := by
      funext x
      ext <;> simp
    rw [h]
    exact (hasFDerivAt_id z).add_const _
  have := (hΨ (z.1, z.2 + u)).hasFDerivAt.comp z h1
  rw [ContinuousLinearMap.comp_id] at this
  exact this

theorem Tcv_hasFDerivAt (Ψ : Vec d × ℝ → ℝ) (hΨ : ContDiff ℝ 1 Ψ) (hc : HasCompactSupport Ψ)
    (z : Vec d × ℝ) :
    HasFDerivAt (Tcv ε hε Ψ) (∫ u, ker ε hε u • fderiv ℝ Ψ (z.1, z.2 + u)) z := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ Ψ) := hΨ.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hΨ.continuous.bounded_above_of_compact_support hc
  obtain ⟨D, hD⟩ := hfc.bounded_above_of_compact_support (hc.fderiv ℝ)
  have hshift : ∀ x : Vec d × ℝ, Continuous fun u : ℝ => (x.1, x.2 + u) := fun x =>
    continuous_const.prodMk (continuous_const.add continuous_id)
  unfold Tcv
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (x : Vec d × ℝ) (u : ℝ) => ker ε hε u * Ψ (x.1, x.2 + u))
    (F' := fun (x : Vec d × ℝ) (u : ℝ) => ker ε hε u • fderiv ℝ Ψ (x.1, x.2 + u))
    (bound := fun u => ‖ker ε hε u‖ * D) (s := univ) univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      (ker_continuous.mul (hΨ.continuous.comp (hshift x))).aestronglyMeasurable
  · exact ker_integrable.mul_bdd (c := C)
      (hΨ.continuous.comp (hshift z)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => hC _)
  · exact (ker_continuous.smul (hfc.comp (hshift z))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u x _ => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hD _) (norm_nonneg _)
  · exact ker_integrable.norm.mul_const _
  · exact Filter.Eventually.of_forall fun u x _ =>
      (hasFDerivAt_shift Ψ hd u x).const_mul (ker ε hε u)

theorem Tcv_integrand_integrable (Ψ : Vec d × ℝ → ℝ) (hΨ : ContDiff ℝ 1 Ψ)
    (hc : HasCompactSupport Ψ) (z : Vec d × ℝ) :
    Integrable (fun u => ker ε hε u • fderiv ℝ Ψ (z.1, z.2 + u)) volume := by
  have hfc : Continuous (fderiv ℝ Ψ) := hΨ.continuous_fderiv one_ne_zero
  obtain ⟨D, hD⟩ := hfc.bounded_above_of_compact_support (hc.fderiv ℝ)
  refine ((ker_integrable (ε := ε) (hε := hε)).norm.mul_const D).mono'
    ((ker_continuous (ε := ε) (hε := hε)).smul (hfc.comp (continuous_const.prodMk
      (continuous_const.add continuous_id)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hD _) (norm_nonneg _)

theorem Tcv_fderiv_apply (Ψ : Vec d × ℝ → ℝ) (hΨ : ContDiff ℝ 1 Ψ) (hc : HasCompactSupport Ψ)
    (z v : Vec d × ℝ) :
    fderiv ℝ (Tcv ε hε Ψ) z v = ∫ u, ker ε hε u * fderiv ℝ Ψ (z.1, z.2 + u) v := by
  rw [(Tcv_hasFDerivAt Ψ hΨ hc z).fderiv,
    ContinuousLinearMap.integral_apply (Tcv_integrand_integrable Ψ hΨ hc z)]
  simp

theorem Tcv_contDiff (Ψ : Vec d × ℝ → ℝ) (hΨ : ContDiff ℝ 1 Ψ) (hc : HasCompactSupport Ψ) :
    ContDiff ℝ 1 (Tcv ε hε Ψ) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun z => (Tcv_hasFDerivAt Ψ hΨ hc z).differentiableAt, ?_⟩
  have hfc : Continuous (fderiv ℝ Ψ) := hΨ.continuous_fderiv one_ne_zero
  obtain ⟨D, hD⟩ := hfc.bounded_above_of_compact_support (hc.fderiv ℝ)
  have hshift : ∀ x : Vec d × ℝ, Continuous fun u : ℝ => (x.1, x.2 + u) := fun x =>
    continuous_const.prodMk (continuous_const.add continuous_id)
  have h : fderiv ℝ (Tcv ε hε Ψ) =
      fun z => ∫ u, ker ε hε u • fderiv ℝ Ψ (z.1, z.2 + u) :=
    funext fun z => (Tcv_hasFDerivAt Ψ hΨ hc z).fderiv
  rw [h]
  refine continuous_of_dominated
    (F := fun (z : Vec d × ℝ) (u : ℝ) => ker ε hε u • fderiv ℝ Ψ (z.1, z.2 + u))
    (bound := fun u => ‖ker ε hε u‖ * D) ?_ ?_ ?_ ?_
  · intro z
    exact ((ker_continuous (ε := ε) (hε := hε)).smul (hfc.comp (hshift z))).aestronglyMeasurable
  · intro z
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hD _) (norm_nonneg _)
  · exact (ker_integrable (ε := ε) (hε := hε)).norm.mul_const _
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (continuous_const : Continuous fun _ : Vec d × ℝ => ker ε hε u).smul
      (hfc.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)))

end EinsteinFull.ParabolicBridge
