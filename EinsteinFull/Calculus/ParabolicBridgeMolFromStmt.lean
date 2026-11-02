import EinsteinFull.Calculus.ParabolicBridgeStmtData

/-!
# `MolData` from the distributional hypotheses of the statement
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ}

theorem molData_of_stmt {τ r K Lam : ℝ} {x : Vec d} (hr : 0 < r) (hK : 0 < K)
    (A ω1 : Vec d → Mat d) (hA : ∀ y, IsEllipticMatrix 1 Lam (A y))
    (hAm : ∀ j k, Measurable fun y => A y j k)
    (hAω : ∀ y j k, A y j k = (K / 2) * ω1 y j k)
    (v : ℝ × Vec d → ℝ) (g : Fin d → ℝ × Vec d → ℝ)
    (hvm : Measurable v) (hgm : ∀ j, Measurable (g j))
    (hv : MemLp v 2 (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)))
    (hg : ∀ j, MemLp (g j) 2 (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)))
    (H1 : ∀ φ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r → ∀ j : Fin d,
      ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v z * fderiv ℝ φ z (0, Pi.single j 1) =
        -∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, g j z * φ z)
    (H2 : ∀ φ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r →
      ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v z * fderiv ℝ φ z (1, 0) =
        (1 / 2) * ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, ∑ j : Fin d,
          (∑ k : Fin d, ω1 z.2 j k * g k z) * fderiv ℝ φ z (0, Pi.single j 1)) :
    MolData (euclideanBall x r) (-r ^ 2 / K) 0 Lam A (fun z => v (Tm τ K z))
      (fun k z => g k (Tm τ K z)) := by
  have hcyl' := Tm_preimage_cyl τ K hK r (euclideanBall x r)
  have hmeasC : MeasurableSet (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r) :=
    measurableSet_Ioo.prod (isOpen_euclideanBall x r).measurableSet
  have hK0 : K ≠ 0 := hK.ne'
  refine ⟨isOpen_euclideanBall x r, (volume_euclideanBall_ne_top x hr.le).lt_top,
    hvm.comp (Tm_measurable τ K), fun k => (hgm k).comp (Tm_measurable τ K), ?_, ?_, hA, hAm,
    ?_, ?_⟩
  · have := memLp_comp_Tm τ K hK hmeasC hv
    rwa [hcyl'] at this
  · intro k
    have := memLp_comp_Tm τ K hK hmeasC (hg k)
    rwa [hcyl'] at this
  · intro ψ hψ hc hs j
    have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
    obtain ⟨hcs, hsub⟩ := xfer_hasCompactSupport τ K hK ψ hc
    have hφsm : ContDiff ℝ (⊤ : ℕ∞) (ψ ∘ TmInv τ K) := hψ.comp (TmInv_contDiff τ K)
    have hts : tsupport (ψ ∘ TmInv τ K) ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r := by
      intro p hp
      obtain ⟨z, hz, rfl⟩ := hsub hp
      have : z ∈ Tm τ K ⁻¹' (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r) := by
        rw [hcyl']; exact hs hz
      exact this
    have hmain := H1 (ψ ∘ TmInv τ K) hφsm hcs hts j
    have eF : ∀ z : Vec d × ℝ, fderiv ℝ (ψ ∘ TmInv τ K) (Tm τ K z) (0, Pi.single j 1) =
        fderiv ℝ ψ z (basisVec j, 0) := by
      intro z
      rw [fderiv_xfer τ K ψ hd, TmInv_Tm τ K hK]
      simp [basisVec]
    have eP : ∀ z : Vec d × ℝ, (ψ ∘ TmInv τ K) (Tm τ K z) = ψ z := fun z => by
      simp [Function.comp, TmInv_Tm τ K hK]
    have t1 := setIntegral_Tm τ K hK
      (fun z => v z * fderiv ℝ (ψ ∘ TmInv τ K) z (0, Pi.single j 1))
      (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)
    have t2 := setIntegral_Tm τ K hK (fun z => g j z * (ψ ∘ TmInv τ K) z)
      (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)
    rw [hcyl'] at t1 t2
    rw [t1, t2] at hmain
    simp only [eF, eP] at hmain
    refine mul_left_cancel₀ hK0 ?_
    rw [mul_neg]
    exact hmain
  · intro ψ hψ hc hs
    have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
    obtain ⟨hcs, hsub⟩ := xfer_hasCompactSupport τ K hK ψ hc
    have hφsm : ContDiff ℝ (⊤ : ℕ∞) (ψ ∘ TmInv τ K) := hψ.comp (TmInv_contDiff τ K)
    have hts : tsupport (ψ ∘ TmInv τ K) ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r := by
      intro p hp
      obtain ⟨z, hz, rfl⟩ := hsub hp
      have : z ∈ Tm τ K ⁻¹' (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r) := by
        rw [hcyl']; exact hs hz
      exact this
    have hmain := H2 (ψ ∘ TmInv τ K) hφsm hcs hts
    have eT : ∀ z : Vec d × ℝ, fderiv ℝ (ψ ∘ TmInv τ K) (Tm τ K z) (1, 0) =
        K⁻¹ * fderiv ℝ ψ z (0, 1) := by
      intro z
      rw [fderiv_xfer τ K ψ hd, TmInv_Tm τ K hK]
      have : ((0 : Vec d), K⁻¹ * (1 : ℝ)) = K⁻¹ • ((0 : Vec d), (1 : ℝ)) := by
        ext <;> simp
      rw [this, map_smul, smul_eq_mul]
    have eF : ∀ (z : Vec d × ℝ) (j : Fin d),
        fderiv ℝ (ψ ∘ TmInv τ K) (Tm τ K z) (0, Pi.single j 1) =
        fderiv ℝ ψ z (basisVec j, 0) := by
      intro z j
      rw [fderiv_xfer τ K ψ hd, TmInv_Tm τ K hK]
      simp [basisVec]
    have t1 := setIntegral_Tm τ K hK
      (fun z => v z * fderiv ℝ (ψ ∘ TmInv τ K) z (1, 0))
      (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)
    have t2 := setIntegral_Tm τ K hK
      (fun z => ∑ j : Fin d, (∑ k : Fin d, ω1 z.2 j k * g k z) *
        fderiv ℝ (ψ ∘ TmInv τ K) z (0, Pi.single j 1))
      (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)
    rw [hcyl'] at t1 t2
    rw [t1, t2] at hmain
    simp only [eT, eF] at hmain
    have l1 : ∫ z in euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0,
        v (Tm τ K z) * (K⁻¹ * fderiv ℝ ψ z (0, 1)) =
        K⁻¹ * ∫ z in euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0,
          v (Tm τ K z) * fderiv ℝ ψ z (0, 1) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      ring
    have l2 : ∫ z in euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0, ∑ j : Fin d,
        (∑ k : Fin d, A z.1 j k * g k (Tm τ K z)) * fderiv ℝ ψ z (basisVec j, 0) =
        (K / 2) * ∫ z in euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0, ∑ j : Fin d,
          (∑ k : Fin d, ω1 (Tm τ K z).2 j k * g k (Tm τ K z)) *
            fderiv ℝ ψ z (basisVec j, 0) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hAω, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [show (Tm τ K z).2 = z.1 from rfl]
      ring
    rw [l1, mul_inv_cancel_left₀ hK0] at hmain
    rw [l2, hmain]
    ring

end EinsteinFull.ParabolicBridge
