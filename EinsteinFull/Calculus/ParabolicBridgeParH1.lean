import EinsteinFull.Calculus.ParabolicBridgeSolution

/-!
# The delayed mollification as a `ParH1Function` weak solution
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ} {U : Set (Vec d)} {b e Lam : ℝ} {A : Vec d → Mat d} {V : Vec d × ℝ → ℝ}
  {G : Fin d → Vec d × ℝ → ℝ}

theorem MolData.isParabolicCoeff (h : MolData U b e Lam A V G) (I : Set ℝ) :
    IsParabolicCoeff 1 Lam (fun z : Vec d × ℝ => A z.1) U I where
  measurable := fun i j =>
    (((h.measA i j).comp measurable_fst).aemeasurable)
  elliptic := Filter.Eventually.of_forall fun z => h.ell z.1

theorem MolData.exists_solution (h : MolData U b e Lam A V G) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ParH1Function U (Ioc (b + 3 * ε) e),
      (∀ z, u.toFun z = MolS ε hε ((U ×ˢ Ioo b e).indicator V) z) ∧
      (∀ z i, u.grad z i = MolS ε hε ((U ×ˢ Ioo b e).indicator (G i)) z) ∧
      IsParabolicWeakSolution (fun z : Vec d × ℝ => A z.1) U (Ioc (b + 3 * ε) e) u := by
  have hS := h.measurableSet_S
  have hVx_m : Measurable ((U ×ˢ Ioo b e).indicator V) := h.measV.indicator hS
  have hVx_2 : MemLp ((U ×ˢ Ioo b e).indicator V) 2 volume := indicator_memLp hS h.memV
  have hVxl := (eLpNorm_two_lt_top_iff hVx_m.aestronglyMeasurable).mp hVx_2
  have hGx_m : ∀ k, Measurable ((U ×ˢ Ioo b e).indicator (G k)) := fun k =>
    (h.measG k).indicator hS
  have hGx_2 : ∀ k, MemLp ((U ×ˢ Ioo b e).indicator (G k)) 2 volume := fun k =>
    indicator_memLp hS (h.memG k)
  have hMS2 : MemLp (MolS ε hε ((U ×ˢ Ioo b e).indicator V)) 2 volume :=
    (eLpNorm_MolS_le _ hVx_m).trans_lt hVx_2
  have hGS2 : ∀ k, MemLp (MolS ε hε ((U ×ˢ Ioo b e).indicator (G k))) 2 volume := fun k =>
    (eLpNorm_MolS_le _ (hGx_m k)).trans_lt (hGx_2 k)
  have hsliceW : ∀ᵐ t ∂(volume.restrict (Ioc (b + 3 * ε) e)),
      HasWeakGradientOn U
        (parSlice (MolS ε hε ((U ×ˢ Ioo b e).indicator V)) t)
        (parSlice (fun z i => MolS ε hε ((U ×ˢ Ioo b e).indicator (G i)) z) t) := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    intro i
    exact slice_weakPartial U h.isOpen b e t ⟨ht.1, ht.2⟩ V (G i) h.integrableOn_V
      (h.integrableOn_G i) i (fun φ hφ hc hs => h.H1 φ hφ hc hs i)
  have hsliceL2 : ∀ t ∈ Ioc (b + 3 * ε) e, ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
      MemLp (parSlice (MolS ε hε ((U ×ˢ Ioo b e).indicator V)) t) 2 (volume.restrict K) :=
    fun t _ K _ _ => slice_memLp_restrict _ hVx_m hVxl t K
  have hwc : ∀ ψ : Vec d → ℝ, IsL2c U ψ →
      ContinuousOn (fun t => ∫ x in U, MolS ε hε ((U ×ˢ Ioo b e).indicator V) (x, t) * ψ x)
        (Ioc (b + 3 * ε) e) := by
    intro ψ hψ
    obtain ⟨hψ2U, K, hK, hKU, hψK⟩ := hψ
    have hψ0 : ∀ x, x ∉ U → ψ x = 0 := fun x hx => hψK x (fun hxK => hx (hKU hxK))
    have hψ2 : MemLp ψ 2 volume := by
      have h1 : MemLp (U.indicator ψ) 2 volume :=
        (memLp_indicator_iff_restrict h.isOpen.measurableSet).mpr hψ2U
      have h2 : U.indicator ψ = ψ := by
        funext x
        by_cases hx : x ∈ U
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx, hψ0 x hx]
      rwa [h2] at h1
    have hcont := weakCont_aux (ε := ε) (hε := hε) ((U ×ˢ Ioo b e).indicator V) hVx_m hVx_2
      (Ioo b e) measurableSet_Ioo measure_Ioo_lt_top.ne
      (fun x s hs => Set.indicator_of_notMem (fun hh => hs hh.2) _) ψ hψ2
    refine hcont.continuousOn.congr fun t _ => ?_
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hψ0 x hx, mul_zero])
  let u : ParH1Function U (Ioc (b + 3 * ε) e) :=
    { toFun := MolS ε hε ((U ×ˢ Ioo b e).indicator V)
      grad := fun z i => MolS ε hε ((U ×ˢ Ioo b e).indicator (G i)) z
      memL2 := hMS2.restrict _
      gradMemL2 := fun i => (hGS2 i).restrict _
      sliceWeakGradient := hsliceW
      sliceL2loc := hsliceL2
      weakCont := hwc }
  refine ⟨u, fun z => rfl, fun z i => rfl, ?_⟩
  intro φ
  have hts : tsupport φ.toFun ⊆ U ×ˢ Ioo (b + 3 * ε) e := by
    intro z hz
    have h' := φ.tsupport_subset hz
    rwa [interior_Ioc] at h'
  have hφ1 : ContDiff ℝ 1 φ.toFun := φ.contDiff
  have hφc : HasCompactSupport φ.toFun := φ.hasCompactSupport
  have hder0 : ∀ z, z ∉ tsupport φ.toFun → ∀ v, fderiv ℝ φ.toFun z v = 0 := by
    intro z hz v
    have : z ∉ tsupport (fderiv ℝ φ.toFun) := fun hh => hz (tsupport_fderiv_subset ℝ hh)
    simp [image_eq_zero_of_notMem_tsupport this]
  have hX : ∀ z, parWeakIntegrand (fun z : Vec d × ℝ => A z.1) u φ.toFun z =
      -(MolS ε hε ((U ×ˢ Ioo b e).indicator V) z * fderiv ℝ φ.toFun z (0, 1)) +
        ∑ j : Fin d, ∑ k : Fin d,
          (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
            fderiv ℝ φ.toFun z (basisVec j, 0) := by
    intro z
    simp only [parWeakIntegrand, parTimeDeriv, parSpaceGrad, vecDot, matVecMul, Finset.sum_mul, u]
  have hΦt2 : MemLp (fun w => fderiv ℝ φ.toFun w (0, 1)) 2 volume :=
    (fderiv_apply_continuous φ.toFun hφ1 _).memLp_of_hasCompactSupport
      (fderiv_apply_hasCompactSupport _ hφc _)
  have hΦj2 : ∀ j : Fin d, MemLp (fun w => fderiv ℝ φ.toFun w (basisVec j, 0)) 2 volume :=
    fun j => (fderiv_apply_continuous φ.toFun hφ1 _).memLp_of_hasCompactSupport
      (fderiv_apply_hasCompactSupport _ hφc _)
  have hI1 : Integrable (fun z => MolS ε hε ((U ×ˢ Ioo b e).indicator V) z *
      fderiv ℝ φ.toFun z (0, 1)) volume := hMS2.integrable_mul hΦt2
  have hAGW2 : ∀ j k : Fin d, MemLp (fun z : Vec d × ℝ =>
      A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) 2 volume := fun j k =>
    (hGS2 k).of_le_mul (c := Lam)
      (((h.measA j k).comp measurable_fst).mul
        (MolS_measurable _ (hGx_m k))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using h.abs_A_le z.1 j k) (norm_nonneg _))
  have hI2 : ∀ j k : Fin d, Integrable (fun z : Vec d × ℝ =>
      (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
        fderiv ℝ φ.toFun z (basisVec j, 0)) volume := fun j k =>
    (hAGW2 j k).integrable_mul (hΦj2 j)
  have hsum : Integrable (fun z : Vec d × ℝ => ∑ j : Fin d, ∑ k : Fin d,
      (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
        fderiv ℝ φ.toFun z (basisVec j, 0)) volume :=
    integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hI2 j k
  have hXint : Integrable (parWeakIntegrand (fun z : Vec d × ℝ => A z.1) u φ.toFun) volume :=
    (hI1.neg.add hsum).congr (Filter.Eventually.of_forall fun z => (hX z).symm)
  have hzero : ∀ z, z ∉ U ×ˢ Ioc (b + 3 * ε) e →
      parWeakIntegrand (fun z : Vec d × ℝ => A z.1) u φ.toFun z = 0 := by
    intro z hz
    have hzt : z ∉ tsupport φ.toFun := fun hh => hz (by
      have := hts hh
      exact ⟨this.1, Ioo_subset_Ioc_self this.2⟩)
    rw [hX z]
    simp [hder0 z hzt]
  refine ⟨hXint.integrableOn, ?_⟩
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).trans ?_
  have hI1n : Integrable (fun z => -(MolS ε hε ((U ×ˢ Ioo b e).indicator V) z *
      fderiv ℝ φ.toFun z (0, 1))) volume := hI1.neg
  have s1 : ∫ z, parWeakIntegrand (fun z : Vec d × ℝ => A z.1) u φ.toFun z =
      ∫ z, (-(MolS ε hε ((U ×ˢ Ioo b e).indicator V) z * fderiv ℝ φ.toFun z (0, 1)) +
        ∑ j : Fin d, ∑ k : Fin d,
          (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
            fderiv ℝ φ.toFun z (basisVec j, 0)) :=
    integral_congr_ae (Filter.Eventually.of_forall hX)
  have s2 : ∫ z, (-(MolS ε hε ((U ×ˢ Ioo b e).indicator V) z * fderiv ℝ φ.toFun z (0, 1)) +
        ∑ j : Fin d, ∑ k : Fin d,
          (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
            fderiv ℝ φ.toFun z (basisVec j, 0)) =
      (∫ z, -(MolS ε hε ((U ×ˢ Ioo b e).indicator V) z * fderiv ℝ φ.toFun z (0, 1))) +
        ∫ z, ∑ j : Fin d, ∑ k : Fin d,
          (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
            fderiv ℝ φ.toFun z (basisVec j, 0) :=
    integral_add hI1n hsum
  have s3 : ∫ z, -(MolS ε hε ((U ×ˢ Ioo b e).indicator V) z * fderiv ℝ φ.toFun z (0, 1)) =
      -∫ z, MolS ε hε ((U ×ˢ Ioo b e).indicator V) z * fderiv ℝ φ.toFun z (0, 1) :=
    integral_neg _
  have s4 : ∫ z, ∑ j : Fin d, ∑ k : Fin d,
          (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
            fderiv ℝ φ.toFun z (basisVec j, 0) =
      ∑ j : Fin d, ∑ k : Fin d, ∫ z,
          (A z.1 j k * MolS ε hε ((U ×ˢ Ioo b e).indicator (G k)) z) *
            fderiv ℝ φ.toFun z (basisVec j, 0) := by
    refine (integral_finset_sum _
      (fun j _ => integrable_finset_sum _ fun k _ => hI2 j k)).trans ?_
    exact Finset.sum_congr rfl fun j _ => integral_finset_sum _ fun k _ => hI2 j k
  have hc := h.weakEq_core hε φ.toFun hφ1 hφc hts
  linarith [s1, s2, s3, s4, hc]

end EinsteinFull.ParabolicBridge
