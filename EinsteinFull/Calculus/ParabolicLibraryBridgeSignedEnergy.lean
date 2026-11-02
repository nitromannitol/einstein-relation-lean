import EllipticRegularity.Parabolic.LocalMax.Energy
import EinsteinFull.Calculus.ParabolicLibraryBridgeSignedFamily

/-!
# The power energy estimate for signed weak solutions

A fork of the library's `EnergyRamp`/`EnergyTime`/`EnergyGrad`/`Energy` in which the
nonnegativity of the solution is dropped and the structural inequalities of the nonlinearity
are assumed on all of `ℝ` (as satisfied by the sign-symmetric family).
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.SignedLocalMax

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.Chain PDE.Parabolic.WeakSlice
  PDE.Parabolic.LocalMax

/-- The hypotheses of the signed power energy estimate. -/
structure EnergyHypS {d : ℕ} (U : Set (Vec d)) (Lam : ℝ) (a : ParCoeffField d)
    (u : ParH1Function U (Ioc (-1 : ℝ) 0)) (F : ℝ → ℝ) (K : ℝ) (η : Vec d × ℝ → ℝ)
    (Kx : Set (Vec d)) (T tTop δ : ℝ) : Prop where
  isOpen : IsOpen U
  coeff : IsParabolicCoeff 1 Lam a U (Ioc (-1 : ℝ) 0)
  solution : IsParabolicWeakSolution a U (Ioc (-1 : ℝ) 0) u
  contDiffF : ContDiff ℝ 2 F
  bdd : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C
  K_nonneg : 0 ≤ K
  Fs : ∀ s, 0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧ deriv F s ^ 2 ≤ K * deriv (deriv F) s * F s
  contDiffη : ContDiff ℝ (⊤ : ℕ∞) η
  compact : IsCompact Kx
  subset : Kx ⊆ U
  vanish_x : ∀ x t, x ∉ Kx → η (x, t) = 0
  hT : -1 < T
  hTt : T < tTop
  htTop : tTop ≤ 0
  hδ : 0 < δ
  vanish_t : ∀ x t, t ≤ T + δ → η (x, t) = 0

variable {d : ℕ} {U : Set (Vec d)} {Lam : ℝ} {a : ParCoeffField d}
  {u : ParH1Function U (Ioc (-1 : ℝ) 0)} {F : ℝ → ℝ} {K : ℝ} {η : Vec d × ℝ → ℝ}
  {Kx : Set (Vec d)} {T tTop δ : ℝ}

theorem EnergyHypS.contDiffη_one (H : EnergyHypS U Lam a u F K η Kx T tTop δ) :
    ContDiff ℝ 1 η := H.contDiffη.of_le (by exact_mod_cast le_top)

/-- Core inequality for a fixed ramp (signed solutions). -/
theorem ramp_energy_core_S (H : EnergyHypS U Lam a u F K η Kx T tTop δ) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ t, χ t ≤ 1)
    (hχd : ∀ t, deriv χ t ≤ 0) {t₁ : ℝ} (h1 : t₁ < tTop) (hχt : ∀ t, t₁ ≤ t → χ t = 0) :
    (∫⁻ z in U ×ˢ Ioo T tTop,
        ENNReal.ofReal (F (u.toFun z) * η z ^ 2 * (-deriv χ z.2)) ≤
        energyBound Lam K F u η T tTop) ∧
    ∫⁻ z in U ×ˢ Ioo T tTop,
        ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z) *
          η z ^ 2 * χ z.2) ≤ energyBound Lam K F u η T tTop := by
  by_cases hR : energyBound Lam K F u η T tTop = ⊤
  · rw [hR]; exact ⟨le_top, le_top⟩
  have hη1 := H.contDiffη_one
  set R := energyBound Lam K F u η T tTop with hRdef
  set S : Set (Vec d × ℝ) := U ×ˢ Ioo T tTop with hS
  set ν : Measure (Vec d × ℝ) := volume.restrict S with hν
  have hsub : S ⊆ U ×ˢ Ioc (-1 : ℝ) 0 := prod_mono subset_rfl fun t ht =>
    ⟨by linarith [ht.1, H.hT], by linarith [ht.2, H.htTop]⟩
  let φ := rampTestFunction (U := U) hη1 hχ H.compact H.subset H.vanish_x H.hT H.htTop H.hδ h1
    H.vanish_t hχt
  have hφ : φ.toFun = rampTest η χ := rfl
  have hsupp : tsupport φ.toFun ⊆ U ×ˢ Ioo T tTop := by
    rw [hφ]
    exact tsupport_rampTest_subset_Ioo H.compact H.subset H.vanish_x H.hδ h1 H.vanish_t hχt
  obtain ⟨hWi, hW0⟩ := weak_solution_renormalization_of_deriv2_bounded H.isOpen
    (ordConnected_Ioc) H.coeff u H.solution F H.contDiffF H.bdd φ
    (s := T) (t := tTop) ⟨H.hT, by linarith [H.hTt, H.htTop]⟩
    ⟨by linarith [H.hTt, H.hT], H.htTop⟩ H.hTt hsupp
  set W : Vec d × ℝ → ℝ := renormalizedIntegrand a u F φ.toFun with hWdef
  have hres := restrict_prod_Ioo_eq U T tTop
  have hWi' : Integrable W ν := by
    rw [hν, hS, hres]; exact hWi
  have hW0' : ∫ z, W z ∂ν = 0 := by
    rw [hν, hS, hres]; exact hW0
  have hell : ∀ᵐ z ∂ν, IsEllipticMatrix 1 Lam (a z) :=
    ae_restrict_of_ae_restrict_of_subset hsub H.coeff.elliptic
  let Y : Vec d × ℝ → ℝ := fun z => F (u.toFun z) *
    (2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z))
  let Bf : Vec d × ℝ → ℝ := fun z => χ z.2 * Y z
  have hY0 : ∀ᵐ z ∂ν, 0 ≤ Y z := by
    filter_upwards [hell] with z he
    have hLam : 0 ≤ Lam := he.Lam_pos.le
    have hF0 := (H.Fs (u.toFun z)).1
    have := vecNormSq_nonneg (parSpaceGrad η z)
    have := H.K_nonneg
    positivity
  have hB0 : ∀ᵐ z ∂ν, 0 ≤ Bf z := by
    filter_upwards [hY0] with z hz using mul_nonneg (hχ0 _) hz
  have hBY : ∀ᵐ z ∂ν, Bf z ≤ Y z := by
    filter_upwards [hY0] with z hz
    calc Bf z = χ z.2 * Y z := rfl
      _ ≤ 1 * Y z := mul_le_mul_of_nonneg_right (hχ1 _) hz
      _ = Y z := one_mul _
  have hRY : ∫⁻ z, ENNReal.ofReal (Y z) ∂ν = R := rfl
  have hBle : ∫⁻ z, ENNReal.ofReal (Bf z) ∂ν ≤ R := by
    rw [← hRY]
    exact lintegral_mono_ae (by filter_upwards [hBY] with z hz using ENNReal.ofReal_le_ofReal hz)
  have hum : AEStronglyMeasurable u.toFun ν :=
    u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hmeasB : AEStronglyMeasurable Bf ν := by
    have hFc : Continuous F := H.contDiffF.continuous
    have h1 : AEStronglyMeasurable (fun z => F (u.toFun z)) ν := hFc.comp_aestronglyMeasurable hum
    have h2 : Continuous fun z : Vec d × ℝ => 2 * |η z| * |parTimeDeriv η z| +
        2 * Lam * K * vecNormSq (parSpaceGrad η z) :=
      ((continuous_const.mul (hη1.continuous.abs)).mul
        (continuous_parTimeDeriv hη1).abs).add
        (continuous_const.mul (continuous_vecNormSq_parSpaceGrad hη1))
    have h3 : Continuous fun z : Vec d × ℝ => χ z.2 := hχ.continuous.comp continuous_snd
    exact h3.aestronglyMeasurable.mul (h1.mul h2.aestronglyMeasurable)
  have hBint : Integrable Bf ν := by
    refine ⟨hmeasB, ?_⟩
    have : ∫⁻ z, ‖Bf z‖ₑ ∂ν = ∫⁻ z, ENNReal.ofReal (Bf z) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hB0] with z hz using Real.enorm_eq_ofReal hz
    unfold HasFiniteIntegral
    rw [this]
    exact lt_of_le_of_lt hBle (lt_top_iff_ne_top.2 hR)
  have hpt : ∀ᵐ z ∂ν, F (u.toFun z) * η z ^ 2 * (-deriv χ z.2) +
      1 / 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z) * η z ^ 2 * χ z.2 -
      Bf z ≤ W z := by
    filter_upwards [hell] with z he
    obtain ⟨hF0, hF2, hF1⟩ := H.Fs (u.toFun z)
    have := renorm_pointwise_lower he (u.grad z) (parSpaceGrad η z) (F0 := F (u.toFun z))
      (F1 := deriv F (u.toFun z)) (F2 := deriv (deriv F) (u.toFun z)) (η := η z)
      (τ := parTimeDeriv η z) (χ := χ z.2) (χ' := deriv χ z.2) hF0 hF2 H.K_nonneg (hχ0 _) hF1
    simp only [hWdef, renormalizedIntegrand, hφ, parTimeDeriv_rampTest hη1 hχ,
      parSpaceGrad_rampTest hη1 hχ, rampTest]
    simpa only [Bf, Y] using this
  have hA1 : ∀ᵐ z ∂ν, 0 ≤ F (u.toFun z) * η z ^ 2 * (-deriv χ z.2) :=
    Filter.Eventually.of_forall fun z => by
      have := (H.Fs (u.toFun z)).1
      have := hχd z.2
      have : 0 ≤ -deriv χ z.2 := by linarith
      positivity
  have hA2 : ∀ᵐ z ∂ν, 0 ≤ 1 / 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z) *
      η z ^ 2 * χ z.2 :=
    Filter.Eventually.of_forall fun z => by
      have := (H.Fs (u.toFun z)).2.1
      have := vecNormSq_nonneg (u.grad z)
      have := hχ0 z.2
      positivity
  have hsumint : Integrable (fun z => W z + Bf z) ν := hWi'.add hBint
  have hsum0 : ∀ᵐ z ∂ν, 0 ≤ W z + Bf z := by
    filter_upwards [hpt, hA1, hA2, hB0] with z h h1 h2 h3
    linarith
  have hL : ∫⁻ z, ENNReal.ofReal (W z + Bf z) ∂ν ≤ R := by
    rw [← ofReal_integral_eq_lintegral_ofReal hsumint hsum0, integral_add hWi' hBint, hW0',
      zero_add, ofReal_integral_eq_lintegral_ofReal hBint hB0]
    exact hBle
  constructor
  · refine le_trans (lintegral_mono_ae ?_) hL
    filter_upwards [hpt, hA1, hA2, hB0] with z h h1 h2 h3
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · refine le_trans (lintegral_mono_ae ?_) hL
    filter_upwards [hpt, hA1, hA2, hB0] with z h h1 h2 h3
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem ofReal_eq_two_mul_ofReal_half_S (x : ℝ) :
    ENNReal.ofReal x = 2 * ENNReal.ofReal (1 / 2 * x) := by
  have : x = 2 * (1 / 2 * x) := by ring
  conv_lhs => rw [this]
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

theorem ramp_energy_grad_fixed_S (H : EnergyHypS U Lam a u F K η Kx T tTop δ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫⁻ z in U ×ˢ Ioo T tTop, ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) *
      vecNormSq (u.grad z) * η z ^ 2 * timeRamp (tTop - ε) ε z.2) ≤
      energyBound Lam K F u η T tTop :=
  (ramp_energy_core_S H (χ := timeRamp (tTop - ε) ε)
    ((timeRamp_contDiff _ _).of_le (by exact_mod_cast le_top))
    (timeRamp_nonneg _ _) (timeRamp_le_one _ _)
    (fun t => by
      rw [deriv_timeRamp]
      exact neg_nonpos.2 (rampKernel_nonneg hε t))
    (by linarith) (fun t ht => timeRamp_eq_zero hε ht)).2

/-- The gradient estimate. -/
theorem energy_grad_estimate_S (H : EnergyHypS U Lam a u F K η Kx T tTop δ) :
    ∫⁻ z in U ×ˢ Ioo T tTop,
        ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) ≤
      2 * energyBound Lam K F u η T tTop := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  set Sn : ℕ → Set (Vec d × ℝ) := fun n => U ×ˢ Ioo T (tTop - 2 * ε n) with hSn
  have hmono : Monotone Sn := by
    intro n m hnm
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have : ε m ≤ ε n := by
      simp only [hεdef]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    exact prod_mono subset_rfl (Ioo_subset_Ioo_right (by linarith))
  have hcover : U ×ˢ Ioo T tTop ⊆ ⋃ n, Sn n := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (tTop - t) / 2 by linarith)
    exact mem_iUnion.2 ⟨n, hx, ht1, by simp only [hεdef]; linarith⟩
  calc ∫⁻ z in U ×ˢ Ioo T tTop, _
      ≤ ∫⁻ z in ⋃ n, Sn n, ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) *
          vecNormSq (u.grad z)) := lintegral_mono_set hcover
    _ = ⨆ n, ∫⁻ z in Sn n, ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) *
          vecNormSq (u.grad z)) := setLIntegral_iUnion_of_directed _ hmono.directed_le
    _ ≤ 2 * energyBound Lam K F u η T tTop := by
        refine iSup_le fun n => ?_
        have hSnm : MeasurableSet (Sn n) := H.isOpen.measurableSet.prod measurableSet_Ioo
        have hsubS : Sn n ⊆ U ×ˢ Ioo T tTop :=
          prod_mono subset_rfl (Ioo_subset_Ioo_right (by linarith [hε n]))
        have hχ1 : ∀ z ∈ Sn n, timeRamp (tTop - ε n) (ε n) z.2 = 1 := fun z hz =>
          timeRamp_eq_one (hε n) (by linarith [hz.2.2])
        calc ∫⁻ z in Sn n, ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) *
              vecNormSq (u.grad z))
            = ∫⁻ z in Sn n, 2 * ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) *
                vecNormSq (u.grad z) * η z ^ 2 * timeRamp (tTop - ε n) (ε n) z.2) := by
              refine setLIntegral_congr_fun hSnm fun z hz => ?_
              rw [hχ1 z hz, ofReal_eq_two_mul_ofReal_half_S]
              refine congrArg (fun r => 2 * ENNReal.ofReal r) ?_
              ring
          _ = 2 * ∫⁻ z in Sn n, ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) *
                vecNormSq (u.grad z) * η z ^ 2 * timeRamp (tTop - ε n) (ε n) z.2) :=
              lintegral_const_mul' _ _ (by simp)
          _ ≤ 2 * ∫⁻ z in U ×ˢ Ioo T tTop, ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) *
                vecNormSq (u.grad z) * η z ^ 2 * timeRamp (tTop - ε n) (ε n) z.2) :=
              mul_le_mul_right (lintegral_mono_set hsubS) 2
          _ ≤ 2 * energyBound Lam K F u η T tTop :=
              mul_le_mul_right (ramp_energy_grad_fixed_S H (hε n)) 2

/-- The time-slice estimate. -/
theorem energy_time_estimate_S (H : EnergyHypS U Lam a u F K η Kx T tTop δ) :
    ∀ᵐ t ∂(volume.restrict (Ioo T tTop)),
      ∫⁻ x in U, ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) ≤
        energyBound Lam K F u η T tTop := by
  by_cases hR : energyBound Lam K F u η T tTop = ⊤
  · exact Eventually.of_forall fun _ => by rw [hR]; exact le_top
  have hη1 := H.contDiffη_one
  have hsub : U ×ˢ Ioo T tTop ⊆ U ×ˢ Ioc (-1 : ℝ) 0 := prod_mono subset_rfl fun t ht =>
    ⟨by linarith [ht.1, H.hT], by linarith [ht.2, H.htTop]⟩
  have hum : AEStronglyMeasurable u.toFun (volume.restrict (U ×ˢ Ioo T tTop)) :=
    u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
  let Hf : Vec d × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (η z ^ 2 * F (u.toFun z))
  have hHm : AEMeasurable Hf (volume.restrict (U ×ˢ Ioo T tTop)) := by
    have h1 : AEStronglyMeasurable (fun z => F (u.toFun z)) (volume.restrict (U ×ˢ Ioo T tTop)) :=
      H.contDiffF.continuous.comp_aestronglyMeasurable hum
    have h2 : Continuous fun z : Vec d × ℝ => η z ^ 2 := hη1.continuous.pow 2
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (h2.aestronglyMeasurable.mul h1).aemeasurable
  have hHm' := hHm
  rw [restrict_prod_eq_prod] at hHm'
  have hGm : AEMeasurable (fun τ => ∫⁻ x in U, Hf (x, τ)) (volume.restrict (Ioo T tTop)) :=
    hHm'.lintegral_prod_left'
  refine ae_le_of_ramp_bounds hR hGm fun t₁ ht₁ h hh => ?_
  have hcore := (ramp_energy_core_S H (χ := timeRamp t₁ h)
    ((timeRamp_contDiff _ _).of_le (by exact_mod_cast le_top))
    (timeRamp_nonneg _ _) (timeRamp_le_one _ _)
    (fun t => by
      rw [deriv_timeRamp]
      exact neg_nonpos.2 (rampKernel_nonneg hh t))
    ht₁.2 (fun t ht => timeRamp_eq_zero hh ht)).1
  refine le_trans (le_of_eq ?_) hcore
  have hpt : ∀ z : Vec d × ℝ, ENNReal.ofReal (F (u.toFun z) * η z ^ 2 *
      (-deriv (timeRamp t₁ h) z.2)) = ENNReal.ofReal (rampKernel t₁ h z.2) * Hf z := by
    intro z
    rw [deriv_timeRamp, neg_neg, ← ENNReal.ofReal_mul (rampKernel_nonneg hh _)]
    congr 1; ring
  simp_rw [hpt]
  rw [lintegral_prod_slices_Ioo]
  · refine lintegral_congr fun τ => ?_
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  · exact (ENNReal.measurable_ofReal.comp
      ((rampKernel_continuous t₁ h).measurable.comp measurable_snd)).aemeasurable.mul hHm

/-- The signed power energy estimate. -/
theorem power_energy_estimate_S {U : Set (Vec d)} (hU : IsOpen U) {Lam : ℝ}
    {a : ParCoeffField d} (ha : IsParabolicCoeff 1 Lam a U (Ioc (-1 : ℝ) 0))
    (u : ParH1Function U (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution a U (Ioc (-1 : ℝ) 0) u)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hF'' : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C)
    {K : ℝ} (hK : 0 ≤ K)
    (hFs : ∀ s, 0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧
      deriv F s ^ 2 ≤ K * deriv (deriv F) s * F s)
    (η : Vec d × ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) {Kx : Set (Vec d)} (hKx : IsCompact Kx)
    (hKxU : Kx ⊆ U) (hηx : ∀ x t, x ∉ Kx → η (x, t) = 0)
    {T tTop δ : ℝ} (hT : -1 < T) (hTt : T < tTop) (htTop : tTop ≤ 0) (hδ : 0 < δ)
    (hηt : ∀ x t, t ≤ T + δ → η (x, t) = 0) :
    (∀ᵐ t ∂(volume.restrict (Ioo T tTop)),
      ∫⁻ x in U, ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) ≤
        energyBound Lam K F u η T tTop) ∧
    ∫⁻ z in U ×ˢ Ioo T tTop,
        ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) ≤
      2 * energyBound Lam K F u η T tTop :=
  have H : EnergyHypS U Lam a u F K η Kx T tTop δ :=
    ⟨hU, ha, hu, hF, hF'', hK, hFs, hη, hKx, hKxU, hηx, hT, hTt, htTop, hδ, hηt⟩
  ⟨energy_time_estimate_S H, energy_grad_estimate_S H⟩

end EinsteinFull.SignedLocalMax
