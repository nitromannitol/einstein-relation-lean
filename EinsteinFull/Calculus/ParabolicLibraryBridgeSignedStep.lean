import EllipticRegularity.Parabolic.LocalMax.PowerStep
import EinsteinFull.Calculus.ParabolicLibraryBridgeSignedEnergy

/-!
# The Moser power step for signed weak solutions

A fork of the library's `PowerStepCore`/`PowerStep` for solutions of arbitrary sign.  The
nonlinearity is the sign-symmetric family `F̃ = powF ∘ sh_σ`, `σ = 1/(n+1)`, `N = n`; the
reverse Hölder step is obtained for `|u| + ε`.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.SignedLocalMax

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.LocalMax

/-- The signed power-step property. -/
def PowerStepPropS (d : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (Lam : ℝ), 1 ≤ Lam → ∀ (a : ParCoeffField d),
    IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
    ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
    IsParabolicWeakSolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
    ∀ ε : ℝ, 0 < ε → ∀ p : ℝ, 1 < p → ∀ r ρ T T' tTop : ℝ, 0 < r → r < ρ → ρ ≤ 1 →
    -1 < T → T < T' → T' < tTop → tTop ≤ 0 →
    ∫⁻ z in euclideanBall (0 : Vec d) r ×ˢ Ioo T' tTop,
        ENNReal.ofReal (|u.toFun z| + ε) ^ (p * (((d : ℝ) + 2) / d)) ≤
      ENNReal.ofReal (C₀ * Lam * (2 + p / (p - 1)) ^ 2 * (1 / (ρ - r) ^ 2 + 1 / (T' - T))) ^
          (((d : ℝ) + 2) / d) *
        (∫⁻ z in euclideanBall (0 : Vec d) ρ ×ˢ Ioo T tTop,
          ENNReal.ofReal (|u.toFun z| + ε) ^ p) ^ (((d : ℝ) + 2) / d)

/-- **Reverse Hölder core** for signed `u`. -/
theorem cutoff_comp_energy_sobolev_S (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {U : Set (Vec d)} {I J : Set ℝ}, IsOpen U → volume U ≠ ⊤ →
      MeasurableSet J → J ⊆ I → ∀ (u : ParH1Function U I),
      ∀ (F G : ℝ → ℝ), ContDiff ℝ 1 G → ∀ M : ℝ, 0 ≤ M → (∀ s, |deriv G s| ≤ M) →
      ∀ {K Lam : ℝ}, 1 ≤ K → 1 ≤ Lam →
      (∀ s, 0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧ G s ^ 2 ≤ K * F s ∧
        deriv G s ^ 2 ≤ K * deriv (deriv F) s) →
      ∀ η : Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → ∀ Kx : Set (Vec d), IsCompact Kx →
      Kx ⊆ U → (∀ x t, x ∉ Kx → η (x, t) = 0) → ∀ R : ℝ≥0∞,
      (∀ᵐ t ∂(volume.restrict J),
        ∫⁻ x in U, ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) ≤ R) →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal
        (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) ≤ 2 * R →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal
        (F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z))) ≤ R →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal |η z * G (u.toFun z)| ^ (2 * ((d : ℝ) + 2) / d) ≤
        C * (ENNReal.ofReal K * R) ^ (2 / (d : ℝ)) * (ENNReal.ofReal (5 * K) * R) := by
  obtain ⟨C, hC, hGN⟩ := slice_cutoff_comp_gagliardo_nirenberg d hd
  refine ⟨C, hC, ?_⟩
  intro U I J hU hfin hJ hJI u F G hG M hM hGM K Lam hK hLam hstr η hη Kx hKx hKxU hηx R
    hE1 hE2 hE3
  have hK0 : 0 ≤ K := by linarith
  refine hGN hU hfin hJ hJI u G hG M hM hGM η hη Kx hKx hKxU hηx _ _ ?_ ?_
  · filter_upwards [hE1] with t ht
    calc ∫⁻ x in U, ENNReal.ofReal ((η (x, t) * G (u.toFun (x, t))) ^ 2)
        ≤ ∫⁻ x in U, ENNReal.ofReal K * ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul hK0]
          refine ENNReal.ofReal_le_ofReal ?_
          have := (hstr (u.toFun (x, t))).2.2.1
          have hη2 := sq_nonneg (η (x, t))
          calc (η (x, t) * G (u.toFun (x, t))) ^ 2
              = η (x, t) ^ 2 * G (u.toFun (x, t)) ^ 2 := by ring
            _ ≤ η (x, t) ^ 2 * (K * F (u.toFun (x, t))) :=
                mul_le_mul_of_nonneg_left this hη2
            _ = K * (η (x, t) ^ 2 * F (u.toFun (x, t))) := by ring
      _ = ENNReal.ofReal K * ∫⁻ x in U, ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * R := by gcongr
  · have hpt : ∀ z : Vec d × ℝ,
        ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η z)) ≤
          ENNReal.ofReal (2 * K) * ENNReal.ofReal
              (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) +
            ENNReal.ofReal (1 / Lam) * ENNReal.ofReal
              (F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z))) := by
      intro z
      obtain ⟨hF0, hF20, hG2, hG'2⟩ := hstr (u.toFun z)
      have hb := vecNormSq_cutoffCompGrad_le u (F := F) η z hG2 hG'2
      have hA : 0 ≤ η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hF20) (vecNormSq_nonneg _)
      have hB : 0 ≤ F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z)) :=
        mul_nonneg hF0 (by have := vecNormSq_nonneg (parSpaceGrad η z); positivity)
      have hLam0 : 0 < Lam := by linarith
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (mul_nonneg (by positivity) hA) (mul_nonneg (by positivity) hB)]
      refine ENNReal.ofReal_le_ofReal (hb.trans (le_of_eq ?_))
      field_simp
    have hmeasA : AEMeasurable (fun z => ENNReal.ofReal (2 * K) * ENNReal.ofReal
        (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)))
        (volume.restrict (U ×ˢ J)) := by
      refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_).const_mul _
      have hμ : volume.restrict (U ×ˢ J) ≤ volume.restrict (U ×ˢ I) :=
        Measure.restrict_mono (prod_mono subset_rfl hJI) le_rfl
      have huM : AEMeasurable u.toFun (volume.restrict (U ×ˢ J)) :=
        (u.memL2.aestronglyMeasurable.mono_measure hμ).aemeasurable
      have hgM : AEMeasurable u.grad (volume.restrict (U ×ˢ J)) :=
        aemeasurable_pi_iff.2 fun i =>
          ((u.gradMemL2 i).aestronglyMeasurable.mono_measure hμ).aemeasurable
      have hηc : Continuous η := hη.continuous
      have hF2 : Measurable (deriv (deriv F)) := measurable_deriv _
      exact ((hηc.measurable.comp_aemeasurable aemeasurable_id).pow_const 2).mul
        (hF2.comp_aemeasurable huM) |>.mul (continuous_vecNormSq.measurable.comp_aemeasurable hgM)
    calc ∫⁻ z in U ×ˢ J, ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η z))
        ≤ ∫⁻ z in U ×ˢ J, (ENNReal.ofReal (2 * K) * ENNReal.ofReal
              (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) +
            ENNReal.ofReal (1 / Lam) * ENNReal.ofReal
              (F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z)))) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 * K) * (∫⁻ z in U ×ˢ J, ENNReal.ofReal
              (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z))) +
            ENNReal.ofReal (1 / Lam) * ∫⁻ z in U ×ˢ J, ENNReal.ofReal
              (F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z))) := by
          rw [lintegral_add_left' hmeasA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (2 * K) * (2 * R) + ENNReal.ofReal (1 / Lam) * R := by gcongr
      _ = (ENNReal.ofReal (2 * K) * 2 + ENNReal.ofReal (1 / Lam)) * R := by ring
      _ ≤ ENNReal.ofReal (5 * K) * R := by
          gcongr
          have hL : 1 / Lam ≤ 1 := by rw [div_le_one (by linarith)]; exact hLam
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The energy bound is controlled by the `L^p` integral of `|u| + ε` on the support cylinder. -/
theorem energyBound_le_of_support_S {d : ℕ} {I : Set ℝ}
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) I)
    {Lam K ε p T tTop ρ Bη : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hε : 0 < ε) (hp : 0 ≤ p)
    (hBη : 0 ≤ Bη) (hLK : 0 ≤ Lam * K)
    {F : ℝ → ℝ} (hFle : ∀ s, F s ≤ (|s| + ε) ^ p)
    {η : Vec d × ℝ → ℝ}
    (hsupp : ∀ z : Vec d × ℝ, z.1 ∉ euclideanBall (0 : Vec d) ρ →
      2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z) = 0)
    (hb : ∀ z, 2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z) ≤ Bη) :
    energyBound Lam K F u η T tTop ≤ ENNReal.ofReal Bη *
      ∫⁻ z in euclideanBall (0 : Vec d) ρ ×ˢ Ioo T tTop, ENNReal.ofReal (|u.toFun z| + ε) ^ p := by
  unfold energyBound
  set S := euclideanBall (0 : Vec d) ρ ×ˢ Ioo T tTop with hS
  have hSm : MeasurableSet S := (measurableSet_euclideanBall _ _).prod measurableSet_Ioo
  have hbnn : ∀ z, 0 ≤ 2 * |η z| * |parTimeDeriv η z| +
      2 * Lam * K * vecNormSq (parSpaceGrad η z) := fun z => by
    have h1 : 0 ≤ 2 * |η z| * |parTimeDeriv η z| := by positivity
    have h2 : 0 ≤ 2 * Lam * K * vecNormSq (parSpaceGrad η z) := by
      have := vecNormSq_nonneg (parSpaceGrad η z)
      have : 0 ≤ 2 * Lam * K := by linarith
      positivity
    linarith
  calc ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioo T tTop, ENNReal.ofReal (F (u.toFun z) *
        (2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z)))
      ≤ ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioo T tTop,
          S.indicator (fun z => ENNReal.ofReal Bη * ENNReal.ofReal (|u.toFun z| + ε) ^ p) z := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem
          ((measurableSet_euclideanBall (0 : Vec d) 1).prod measurableSet_Ioo)] with z hzmem
        by_cases hzS : z ∈ S
        · rw [indicator_of_mem hzS, ENNReal.ofReal_rpow_of_nonneg (by positivity) hp,
            ← ENNReal.ofReal_mul hBη]
          refine ENNReal.ofReal_le_ofReal ?_
          calc F (u.toFun z) * (2 * |η z| * |parTimeDeriv η z| +
                2 * Lam * K * vecNormSq (parSpaceGrad η z))
              ≤ (|u.toFun z| + ε) ^ p * Bη :=
                mul_le_mul (hFle _) (hb z) (hbnn z) (Real.rpow_nonneg (by positivity) _)
            _ = Bη * (|u.toFun z| + ε) ^ p := mul_comm _ _
        · have hz1 : z.1 ∉ euclideanBall (0 : Vec d) ρ := fun h => hzS ⟨h, hzmem.2⟩
          rw [indicator_of_notMem hzS, hsupp z hz1, mul_zero, ENNReal.ofReal_zero]
    _ = ∫⁻ z in S, ENNReal.ofReal Bη * ENNReal.ofReal (|u.toFun z| + ε) ^ p := by
        rw [lintegral_indicator hSm, Measure.restrict_restrict hSm,
          inter_eq_left.2 (prod_mono (euclideanBall_mono hρ0 hρ1) subset_rfl)]
    _ = ENNReal.ofReal Bη * ∫⁻ z in S, ENNReal.ofReal (|u.toFun z| + ε) ^ p :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Pointwise convergence of the sign-symmetric half-power truncations. -/
theorem tendsto_signed_half_power {p ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    Tendsto (fun n : ℕ => (sh (1 / ((n : ℝ) + 1)) s + ε) ^ (p / 2)) atTop
      (𝓝 ((|s| + ε) ^ (p / 2))) := by
  have h1 : Tendsto (fun n : ℕ => sh (1 / ((n : ℝ) + 1)) s) atTop (𝓝 |s|) := by
    have hσ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlow : Tendsto (fun n : ℕ => |s| - 1 / ((n : ℝ) + 1)) atTop (𝓝 |s|) := by
      simpa using (tendsto_const_nhds (x := |s|)).sub hσ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => abs_sub_le_sh s) (fun n => sh_le_abs (by positivity) s)
  have h2 : Tendsto (fun n : ℕ => sh (1 / ((n : ℝ) + 1)) s + ε) atTop (𝓝 (|s| + ε)) :=
    h1.add_const ε
  exact h2.rpow_const (Or.inl (by positivity))

end EinsteinFull.SignedLocalMax
