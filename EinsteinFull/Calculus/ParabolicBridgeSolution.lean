import EinsteinFull.Calculus.ParabolicBridgeMolData

/-!
# The delayed mollification is a library weak solution
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ} {U : Set (Vec d)} {b e Lam : ℝ} {A : Vec d → Mat d} {V : Vec d × ℝ → ℝ}
  {G : Fin d → Vec d × ℝ → ℝ}

theorem MolData.adj_flux (h : MolData U b e Lam A V G) {ε : ℝ} (hε : 0 < ε)
    (φ : Vec d × ℝ → ℝ) (hφ1 : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (j k : Fin d) :
    ∫ z, (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
        fderiv ℝ φ z (basisVec j, 0) =
      ∫ z in U ×ˢ Ioo b e, (A z.1 j k * G k z) * fderiv ℝ (Tcv ε hε φ) z (basisVec j, 0) := by
  have hS := h.measurableSet_S
  have hGx_m : Measurable ((U ×ˢ Ioo b e).indicator (G k)) := (h.measG k).indicator hS
  have hGx_2 : MemLp ((U ×ˢ Ioo b e).indicator (G k)) 2 volume := indicator_memLp hS (h.memG k)
  have hGx_1 := indicator_integrable hS h.vol_S (h.memG k)
  have hHm : Measurable fun w : Vec d × ℝ => A w.1 j k * (U ×ˢ Ioo b e).indicator (G k) w :=
    ((h.measA j k).comp measurable_fst).mul hGx_m
  have hbd : ∀ w : Vec d × ℝ, ‖A w.1 j k‖ ≤ Lam := fun w => by
    simpa using h.abs_A_le w.1 j k
  have hH1 : Integrable (fun w : Vec d × ℝ => A w.1 j k * (U ×ˢ Ioo b e).indicator (G k) w)
      volume :=
    hGx_1.bdd_mul (c := Lam) (((h.measA j k).comp measurable_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbd)
  have hH2 : MemLp (fun w : Vec d × ℝ => A w.1 j k * (U ×ˢ Ioo b e).indicator (G k) w) 2
      volume :=
    hGx_2.of_le_mul (c := Lam) hHm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbd w) (norm_nonneg _))
  have e1 : ∀ z : Vec d × ℝ, A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z =
      MolS ε hε (fun w => A w.1 j k * (U ×ˢ Ioo b e).indicator (G k) w) z := fun z =>
    (MolS_const_mul_fst (fun y => A y j k) _ z).symm
  simp_rw [e1]
  have hadj := integral_MolS_mul (ε := ε) (hε := hε)
    (fun w : Vec d × ℝ => A w.1 j k * (U ×ˢ Ioo b e).indicator (G k) w)
    (fun w => fderiv ℝ φ w (basisVec j, 0)) hHm hH1 hH2
    (fderiv_apply_continuous φ hφ1 _) (fderiv_apply_hasCompactSupport φ hφc _)
  rw [hadj]
  have e2 := integral_indicator_mul hS (fun z : Vec d × ℝ => A z.1 j k) (G k)
    (fun z => fderiv ℝ (Tcv ε hε φ) z (basisVec j, 0))
  rw [← e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show A z.1 j k * (U ×ˢ Ioo b e).indicator (G k) z * Tcv ε hε (fun w => fderiv ℝ φ w (basisVec j, 0)) z =
    A z.1 j k * (U ×ˢ Ioo b e).indicator (G k) z * fderiv ℝ (Tcv ε hε φ) z (basisVec j, 0)
  rw [Tcv_fderiv_apply φ hφ1 hφc z (basisVec j, 0)]
  rfl

theorem MolData.adj_time (h : MolData U b e Lam A V G) {ε : ℝ} (hε : 0 < ε)
    (φ : Vec d × ℝ → ℝ) (hφ1 : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ z, MolS ε hε ((U ×ˢ Ioo b e).indicator V) z * fderiv ℝ φ z (0, 1) =
      ∫ z in U ×ˢ Ioo b e, V z * fderiv ℝ (Tcv ε hε φ) z (0, 1) := by
  have hS := h.measurableSet_S
  have hVx_m : Measurable ((U ×ˢ Ioo b e).indicator V) := h.measV.indicator hS
  have hVx_2 : MemLp ((U ×ˢ Ioo b e).indicator V) 2 volume := indicator_memLp hS h.memV
  have hVx_1 := indicator_integrable hS h.vol_S h.memV
  have hadj := integral_MolS_mul (ε := ε) (hε := hε) ((U ×ˢ Ioo b e).indicator V)
    (fun w => fderiv ℝ φ w (0, 1)) hVx_m hVx_1 hVx_2
    (fderiv_apply_continuous φ hφ1 _) (fderiv_apply_hasCompactSupport φ hφc _)
  rw [hadj]
  have e2 := integral_indicator_mul hS (fun _ : Vec d × ℝ => (1 : ℝ)) V
    (fun z => fderiv ℝ (Tcv ε hε φ) z (0, 1))
  simp only [one_mul] at e2
  rw [← e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show (U ×ˢ Ioo b e).indicator V z * Tcv ε hε (fun w => fderiv ℝ φ w (0, 1)) z =
    (U ×ˢ Ioo b e).indicator V z * fderiv ℝ (Tcv ε hε φ) z (0, 1)
  rw [Tcv_fderiv_apply φ hφ1 hφc z (0, 1)]
  rfl

/-- The weak equation for the delayed mollification, tested on `C¹` functions. -/
theorem MolData.weakEq_core (h : MolData U b e Lam A V G) {ε : ℝ} (hε : 0 < ε)
    (φ : Vec d × ℝ → ℝ) (hφ1 : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ U ×ˢ Ioo (b + 3 * ε) e) :
    ∫ z, MolS ε hε ((U ×ˢ Ioo b e).indicator V) z * fderiv ℝ φ z (0, 1) =
      ∑ j : Fin d, ∑ k : Fin d, ∫ z,
        (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
          fderiv ℝ φ z (basisVec j, 0) := by
  obtain ⟨hψc, hψs⟩ := Tcv_support_in (hε := hε) (U := U) (b := b) (e := e) φ hφc hφs
  have hψ1 : ContDiff ℝ 1 (Tcv ε hε φ) := Tcv_contDiff φ hφ1 hφc
  rw [h.adj_time hε φ hφ1 hφc, h.H2_C1 _ hψ1 hψc hψs]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcont := fderiv_apply_continuous (Tcv ε hε φ) hψ1 (basisVec j, 0)
  have hcs := fderiv_apply_hasCompactSupport (Tcv ε hε φ) hψc (basisVec j, 0)
  calc ∫ z in U ×ˢ Ioo b e, Hs A G j z * fderiv ℝ (Tcv ε hε φ) z (basisVec j, 0)
      = ∫ z in U ×ˢ Ioo b e, ∑ k : Fin d,
          (A z.1 j k * G k z) * fderiv ℝ (Tcv ε hε φ) z (basisVec j, 0) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [Hs, Finset.sum_mul]
    _ = ∑ k : Fin d, ∫ z in U ×ˢ Ioo b e,
          (A z.1 j k * G k z) * fderiv ℝ (Tcv ε hε φ) z (basisVec j, 0) :=
        integral_finset_sum _ (fun k _ => h.integrableOn_Aj_mul j k hcont hcs)
    _ = ∑ k : Fin d, ∫ z, (A z.1 j k *
          MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) * fderiv ℝ φ z (basisVec j, 0) :=
        Finset.sum_congr rfl fun k _ => (h.adj_flux hε φ hφ1 hφc j k).symm

end EinsteinFull.ParabolicBridge
