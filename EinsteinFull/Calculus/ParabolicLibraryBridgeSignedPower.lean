import EinsteinFull.Calculus.ParabolicLibraryBridgeSignedStep

/-!
# The signed Moser power step
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.SignedLocalMax

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.LocalMax

/-- **Moser power step** for weak solutions of arbitrary sign; `C₀` depends only on `d`. -/
theorem power_step_S (d : ℕ) (hd : 0 < d) : ∃ C₀ : ℝ, 0 < C₀ ∧ PowerStepPropS d C₀ := by
  obtain ⟨Cs, hCs, hcore⟩ := cutoff_comp_energy_sobolev_S d hd
  obtain ⟨Bst, hBst0, hBst⟩ := exists_abs_deriv_smoothTransition_le
  refine ⟨max 1 (5 * Cs.toReal) * (4 * Bst + 2048), by positivity, ?_⟩
  intro Lam hLam a ha u hu ε hε p hp r ρ T T' tTop hr hrρ hρ1 hT hTT' hT't htTop
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set K : ℝ := 2 + p / (p - 1) with hKdef
  have hp1 : 0 < p - 1 := by linarith
  have hK1 : 1 ≤ K := by
    have : 0 ≤ p / (p - 1) := div_nonneg (by linarith) hp1.le
    linarith
  have hK0 : 0 ≤ K := by linarith
  have hLam0 : 0 ≤ Lam := by linarith
  set J := Ioo T tTop with hJ
  set η := cylCutoff (d := d) r ρ T T' with hηdef
  set Kx := tsupport (canonicalBallCutoff (0 : Vec d) r ρ) with hKxdef
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := cylCutoff_contDiff hr.le hrρ T T'
  have hKx : IsCompact Kx := (canonicalBallCutoff_hasCompactSupport hr.le hrρ).isCompact
  have hKxρ : Kx ⊆ euclideanBall (0 : Vec d) ρ :=
    canonicalBallCutoff_tsupport_subset_outer hr.le hrρ
  have hρ0 : 0 ≤ ρ := by linarith
  have hKxΩ : Kx ⊆ euclideanBall (0 : Vec d) 1 := hKxρ.trans (euclideanBall_mono hρ0 hρ1)
  have hηx : ∀ x t, x ∉ Kx → η (x, t) = 0 := fun x t hx => cylCutoff_eq_zero_of_notMem hx t
  have hδ : 0 < (T' - T) / 2 := by linarith
  have hηt : ∀ x t, t ≤ T + (T' - T) / 2 → η (x, t) = 0 :=
    fun x t ht => cylCutoff_eq_zero_of_le hTT' x ht
  have hJI : J ⊆ Ioc (-1 : ℝ) 0 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set Bη : ℝ := 2 * (2 * Bst / (T' - T)) + 2 * Lam * K * (1024 / (ρ - r) ^ 2) with hBηdef
  have hgap : 0 < T' - T := by linarith
  have hgapr : 0 < ρ - r := by linarith
  have hBη0 : 0 ≤ Bη := by positivity
  have hb : ∀ z, 2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z) ≤
      Bη := by
    intro z
    have h1 : |η z| ≤ 1 := by
      rw [abs_of_nonneg (cylCutoff_nonneg _ _ _ _ z)]; exact cylCutoff_le_one _ _ _ _ z
    have h2 := abs_parTimeDeriv_cylCutoff_le hBst hr.le hrρ hTT' z
    have h3 := vecNormSq_parSpaceGrad_cylCutoff_le (d := d) hr.le hrρ T T' z
    have h4 : 2 * |η z| * |parTimeDeriv η z| ≤ 2 * (2 * Bst / (T' - T)) := by
      have := abs_nonneg (parTimeDeriv η z)
      calc 2 * |η z| * |parTimeDeriv η z| ≤ 2 * 1 * (2 * Bst / (T' - T)) := by gcongr
        _ = _ := by ring
    have h5 : 2 * Lam * K * vecNormSq (parSpaceGrad η z) ≤ 2 * Lam * K * (1024 / (ρ - r) ^ 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hsupp : ∀ z : Vec d × ℝ, z.1 ∉ euclideanBall (0 : Vec d) ρ →
      2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z) = 0 := by
    rintro ⟨x, t⟩ hx
    have hxK : x ∉ Kx := fun h => hx (hKxρ h)
    have hξ : canonicalBallCutoff (0 : Vec d) r ρ x = 0 := image_eq_zero_of_notMem_tsupport hxK
    have hgradξ : classicalGradient (canonicalBallCutoff (0 : Vec d) r ρ) x = 0 := by
      funext i
      rw [classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hxK]
      rfl
    rw [hηx x t hxK, parTimeDeriv_cylCutoff r ρ T T' x t hr.le hrρ rfl, hξ,
      parSpaceGrad_cylCutoff hr.le hrρ, hgradξ, smul_zero]
    simp [vecNormSq, vecDot]
  set I0 := ∫⁻ z in euclideanBall (0 : Vec d) ρ ×ˢ J, ENNReal.ofReal (|u.toFun z| + ε) ^ p
    with hI0
  choose F G hF2 hF''b hG1 hG'b hstr using
    fun n : ℕ => exists_signedFamily hp hε (N := (n : ℝ)) (σ := 1 / ((n : ℝ) + 1))
      n.cast_nonneg (by positivity)
  set q : ℝ := 2 * ((d : ℝ) + 2) / d with hq
  have hN : ∀ n : ℕ, ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ J,
      ENNReal.ofReal |η z * G n (u.toFun z)| ^ q ≤
        Cs * (ENNReal.ofReal K * (ENNReal.ofReal Bη * I0)) ^ (2 / (d : ℝ)) *
          (ENNReal.ofReal (5 * K) * (ENNReal.ofReal Bη * I0)) := by
    intro n
    have hFs : ∀ s, 0 ≤ F n s ∧ 0 ≤ deriv (deriv (F n)) s ∧
        deriv (F n) s ^ 2 ≤ K * deriv (deriv (F n)) s * F n s := fun s =>
      ⟨(hstr n s).1, (hstr n s).2.1, (hstr n s).2.2.1⟩
    obtain ⟨hE1, hE2⟩ := power_energy_estimate_S (isOpen_euclideanBall _ _) ha u hu (F n)
      (hF2 n) (hF''b n) hK0 hFs η hη hKx hKxΩ hηx hT (hTT'.trans hT't) htTop hδ hηt
    have hE3 : ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ J, ENNReal.ofReal
        (F n (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z))) ≤
          energyBound Lam K (F n) u η T tTop := by
      refine lintegral_mono fun z => ?_
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hstr n _).1)
      have : 0 ≤ 2 * |η z| * |parTimeDeriv η z| := by positivity
      linarith
    have hR : energyBound Lam K (F n) u η T tTop ≤ ENNReal.ofReal Bη * I0 :=
      energyBound_le_of_support_S u hρ0 hρ1 hε (by linarith) hBη0 (by positivity)
        (fun s => (hstr n s).2.2.2.2.2.1) hsupp hb
    obtain ⟨M, hM, hGM⟩ := hG'b n
    have hcore' := hcore (isOpen_euclideanBall _ _) (volume_euclideanBall_ne_top _ zero_le_one)
      measurableSet_Ioo hJI u (F n) (G n) (hG1 n) M hM hGM hK1 hLam
      (fun s => ⟨(hstr n s).1, (hstr n s).2.1, (hstr n s).2.2.2.1,
        (hstr n s).2.2.2.2.1⟩) η hη Kx hKx hKxΩ hηx (energyBound Lam K (F n) u η T tTop)
      hE1 hE2 hE3
    refine hcore'.trans ?_
    gcongr
  set S' := euclideanBall (0 : Vec d) r ×ˢ Ioo T' tTop with hS'
  have hS'm : MeasurableSet S' := (measurableSet_euclideanBall _ _).prod measurableSet_Ioo
  have hS'sub : S' ⊆ euclideanBall (0 : Vec d) 1 ×ˢ J :=
    prod_mono (euclideanBall_mono hr.le (hrρ.le.trans hρ1))
      (Ioo_subset_Ioo_left hTT'.le)
  have huS' : AEMeasurable u.toFun (volume.restrict S') :=
    (u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono
      (hS'sub.trans (prod_mono subset_rfl hJI)) le_rfl)).aemeasurable
  have hlim : ∀ᵐ z ∂(volume.restrict S'),
      liminf (fun n : ℕ => ENNReal.ofReal |G n (u.toFun z)| ^ q) atTop =
        ENNReal.ofReal (|u.toFun z| + ε) ^ (p * (((d : ℝ) + 2) / d)) := by
    refine Filter.Eventually.of_forall fun z => ?_
    refine Tendsto.liminf_eq ?_
    have hT : Tendsto (fun n : ℕ => G n (u.toFun z)) atTop
        (𝓝 ((|u.toFun z| + ε) ^ (p / 2))) := by
      refine (tendsto_signed_half_power (p := p) hε (u.toFun z)).congr' ?_
      obtain ⟨n₀, hn₀⟩ := exists_nat_ge |u.toFun z|
      filter_upwards [eventually_ge_atTop n₀] with n hn
      have hle : |u.toFun z| ≤ (n : ℝ) := hn₀.trans (by exact_mod_cast hn)
      exact ((hstr n _).2.2.2.2.2.2.2 ((sh_le_abs (by positivity) _).trans hle)).symm
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal |G n (u.toFun z)|) atTop
        (𝓝 (ENNReal.ofReal |(|u.toFun z| + ε) ^ (p / 2)|)) :=
      ENNReal.tendsto_ofReal hT.abs
    have h3 := h2.ennrpow_const q
    have e : ENNReal.ofReal |(|u.toFun z| + ε) ^ (p / 2)| ^ q =
        ENNReal.ofReal (|u.toFun z| + ε) ^ (p * (((d : ℝ) + 2) / d)) :=
      ofReal_half_pow_rpow (by positivity) (by linarith)
    rw [e] at h3
    exact h3
  have hmeas : ∀ n : ℕ, AEMeasurable (fun z => ENNReal.ofReal |G n (u.toFun z)| ^ q)
      (volume.restrict S') := fun n =>
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (((hG1 n).continuous.measurable.comp_aemeasurable huS').abs)).pow_const q
  have hset : ∀ n : ℕ, ∫⁻ z in S', ENNReal.ofReal |G n (u.toFun z)| ^ q ≤
      ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ J, ENNReal.ofReal |η z * G n (u.toFun z)| ^ q := by
    intro n
    calc ∫⁻ z in S', ENNReal.ofReal |G n (u.toFun z)| ^ q
        = ∫⁻ z in S', ENNReal.ofReal |η z * G n (u.toFun z)| ^ q := by
          refine setLIntegral_congr_fun hS'm fun z hz => ?_
          obtain ⟨x, t⟩ := z
          rw [show η (x, t) = 1 from cylCutoff_eq_one hr.le hrρ hTT' hz.1 hz.2.1.le, one_mul]
      _ ≤ _ := lintegral_mono_set hS'sub
  calc ∫⁻ z in S', ENNReal.ofReal (|u.toFun z| + ε) ^ (p * (((d : ℝ) + 2) / d))
      = ∫⁻ z in S', liminf (fun n : ℕ => ENNReal.ofReal |G n (u.toFun z)| ^ q) atTop :=
        (lintegral_congr_ae hlim).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ z in S', ENNReal.ofReal |G n (u.toFun z)| ^ q) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ Cs * (ENNReal.ofReal K * (ENNReal.ofReal Bη * I0)) ^ (2 / (d : ℝ)) *
          (ENNReal.ofReal (5 * K) * (ENNReal.ofReal Bη * I0)) :=
        Filter.liminf_le_of_frequently_le'
          (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
            (hset n).trans (hN n)))
    _ ≤ ENNReal.ofReal (max 1 (5 * Cs.toReal) * (K * Bη)) ^ (((d : ℝ) + 2) / d) *
          I0 ^ (((d : ℝ) + 2) / d) := power_step_arith hd hCs hK1 (Y := Bη) I0
    _ ≤ _ := by
        refine mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by positivity))
          le_rfl
        have hg1 : 0 ≤ 1 / (ρ - r) ^ 2 := by positivity
        have hg2 : 0 ≤ 1 / (T' - T) := by positivity
        have hKK : K ≤ Lam * K ^ 2 := by
          have h1 := mul_le_mul_of_nonneg_left hK1 (by linarith : 0 ≤ K)
          have h2 := mul_le_mul_of_nonneg_right hLam (sq_nonneg K)
          linarith
        have e1 : K * Bη = 4 * Bst * K * (1 / (T' - T)) +
            2048 * (Lam * K ^ 2) * (1 / (ρ - r) ^ 2) := by
          rw [hBηdef]; field_simp; ring
        rw [e1]
        have hm : 0 ≤ max 1 (5 * Cs.toReal) := le_trans zero_le_one (le_max_left _ _)
        have key : 4 * Bst * K * (1 / (T' - T)) + 2048 * (Lam * K ^ 2) * (1 / (ρ - r) ^ 2) ≤
            (4 * Bst + 2048) * Lam * K ^ 2 * (1 / (ρ - r) ^ 2 + 1 / (T' - T)) := by
          have a1 : 4 * Bst * K * (1 / (T' - T)) ≤ 4 * Bst * (Lam * K ^ 2) * (1 / (T' - T)) := by
            gcongr
          linarith [mul_nonneg (mul_nonneg hBst0 (by positivity : (0 : ℝ) ≤ Lam * K ^ 2)) hg1,
            mul_nonneg (by positivity : (0 : ℝ) ≤ Lam * K ^ 2) hg2]
        calc max 1 (5 * Cs.toReal) * (4 * Bst * K * (1 / (T' - T)) +
              2048 * (Lam * K ^ 2) * (1 / (ρ - r) ^ 2))
            ≤ max 1 (5 * Cs.toReal) * ((4 * Bst + 2048) * Lam * K ^ 2 *
                (1 / (ρ - r) ^ 2 + 1 / (T' - T))) := mul_le_mul_of_nonneg_left key hm
          _ = _ := by ring

end EinsteinFull.SignedLocalMax
