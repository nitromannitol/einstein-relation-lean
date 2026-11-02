import EinsteinFull.Calculus.ParabolicBridgeAssembly2
import EinsteinFull.Calculus.ParabolicBridgeAssembly3

/-!
# The scaled Hölder decay for all radii ratios `θ ≤ 1/2`
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

theorem scaled_decay (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) (K : ℝ) (hK : 1 ≤ K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 1 ≤ C ∧
    ∀ (x : Vec d) (r : ℝ), 0 < r →
    ∀ (A : Vec d → Mat d) (V : Vec d × ℝ → ℝ) (G : Fin d → Vec d × ℝ → ℝ),
    MolData (euclideanBall x r) (-r ^ 2 / K) 0 Lam A V G →
    ∀ (κ θ : ℝ), 0 < θ → θ ≤ 1 / 2 →
      Real.sqrt (⨍ z, |V z - ⨍ w, V w ∂(volume.restrict
          (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0))| ^ 2
          ∂(volume.restrict (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0))) ≤
        C * θ ^ α * Real.sqrt (⨍ z, |V z - κ| ^ 2 ∂(volume.restrict
          (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0))) := by
  obtain ⟨α, C₀, hα0, hα1, hC₀1, hosc⟩ := scaled_osc_bound d hd Lam hLam
  have hK0 : 0 < K := by linarith
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hs1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hK
  have hss : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK0.le
  have hcd : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos (0 : Vec d) one_pos
  set cd : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hcddef
  set s : ℝ := Real.sqrt K with hsdef
  set θ₀ : ℝ := 3 / (16 * s) with hθ₀
  have hθ₀pos : 0 < θ₀ := by positivity
  set W : ℝ := cd * (2 * s) ^ (d + 2) / K with hW
  have hWpos : 0 < W := by positivity
  set B : ℝ := Real.sqrt ((1 / θ₀) ^ (d + 2)) with hB
  have hBpos : 0 < B := Real.sqrt_pos.mpr (by positivity)
  refine ⟨α, max 1 (max (C₀ * (2 * s) ^ α / 2 * Real.sqrt W) (B / θ₀)), hα0, hα1,
    le_max_left _ _, ?_⟩
  intro x r hr A V G h κ θ hθ hθ2
  have hr0 : r ≠ 0 := hr.ne'
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hKne : K ≠ 0 := hK0.ne'
  have hcd0 : cd ≠ 0 := hcd.ne'
  have hs0 : s ≠ 0 := hs.ne'
  have hθ1 : θ ≤ 1 := by linarith
  have hθr0 : 0 < θ * r := mul_pos hθ hr
  have hθr : θ * r ≤ r := by nlinarith
  have hθα : θ ≤ θ ^ α := by
    have := Real.rpow_le_rpow_of_exponent_ge hθ hθ1 hα1
    rwa [Real.rpow_one] at this
  have hθαpos : 0 < θ ^ α := Real.rpow_pos_of_pos hθ α
  have hSm : MeasurableSet (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0) := h.measurableSet_S
  have hEm : MeasurableSet (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0) :=
    (isOpen_euclideanBall x _).measurableSet.prod measurableSet_Ioo
  have hEsub : euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0 ⊆
      euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0 := by
    refine Set.prod_mono (euclideanBall_mono hθr0.le hθr) (Set.Ioo_subset_Ioo_left ?_)
    rw [div_le_div_iff_of_pos_right hK0]
    have : (θ * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hθr0.le hθr 2
    linarith
  have hSfin : volume (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0) ≠ ⊤ := h.vol_S.ne
  have hEfin : volume (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0) ≠ ⊤ :=
    ne_top_of_le_ne_top hSfin (measure_mono hEsub)
  have hmS : (volume (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)).toReal =
      cd * r ^ d * (r ^ 2 / K) := vol_cyl x hr hK0
  have hmE : (volume (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)).toReal =
      cd * (θ * r) ^ d * ((θ * r) ^ 2 / K) := vol_cyl x hθr0 hK0
  have hmSpos : 0 < cd * r ^ d * (r ^ 2 / K) := by positivity
  have hmEpos : 0 < cd * (θ * r) ^ d * ((θ * r) ^ 2 / K) := by positivity
  haveI : IsFiniteMeasure (volume.restrict (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hSfin⟩
  haveI : IsFiniteMeasure
      (volume.restrict (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hEfin⟩
  have hVS : MemLp V 2 (volume.restrict (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)) := h.memV
  have hVE : MemLp V 2 (volume.restrict
      (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)) :=
    hVS.mono_measure (Measure.restrict_mono hEsub le_rfl)
  have hvolS : (volume.restrict (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)).real Set.univ =
      cd * r ^ d * (r ^ 2 / K) := by
    rw [measureReal_def, Measure.restrict_apply_univ, hmS]
  have hvolE : (volume.restrict
      (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)).real Set.univ =
      cd * (θ * r) ^ d * ((θ * r) ^ 2 / K) := by
    rw [measureReal_def, Measure.restrict_apply_univ, hmE]
  have hgS : MemLp (fun z => V z - κ) 2
      (volume.restrict (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)) :=
    hVS.sub (memLp_const κ)
  have step1 := sqrt_avg_osc_le_const
    (volume.restrict (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)) hVE κ
  have hSsq0 : 0 ≤ ⨍ z, |V z - κ| ^ 2 ∂(volume.restrict
      (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)) := by
    rw [average_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (integral_nonneg fun z => by positivity)
  by_cases hc : 2 * s * θ ≤ 3 / 8
  · -- Case A: the Hölder decay from the parabolic core
    have hA := hosc x r K hr hK A V G h κ θ hθ hc
    have hρ'pos : 0 < r / (2 * s) := by positivity
    have hρ'r : r / (2 * s) ≤ r := div_le_self hr.le (by linarith)
    have hρ'2 : (r / (2 * s)) ^ 2 = r ^ 2 / (4 * K) := by
      rw [← hss]
      field_simp
      ring
    have hbQ : -r ^ 2 / K ≤ 0 - (r / (2 * s)) ^ 2 := by
      rw [hρ'2]
      have e2 : r ^ 2 / (4 * K) ≤ r ^ 2 / K :=
        div_le_div_of_nonneg_left (sq_nonneg r) hK0 (by linarith)
      have e3 : -r ^ 2 / K = -(r ^ 2 / K) := by ring
      linarith
    have hQm : MeasurableSet (euclideanBall x (r / (2 * s)) ×ˢ Ioc (0 - (r / (2 * s)) ^ 2) 0) :=
      (isOpen_euclideanBall x _).measurableSet.prod measurableSet_Ioc
    have hNnull : volume ((univ : Set (Vec d)) ×ˢ ({0} : Set ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    have hQsub : euclideanBall x (r / (2 * s)) ×ˢ Ioc (0 - (r / (2 * s)) ^ 2) 0 ⊆
        euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0 ∪ (univ ×ˢ {0}) := by
      intro z hz
      by_cases h0 : z.2 = 0
      · exact Or.inr ⟨mem_univ _, h0⟩
      · left
        refine ⟨euclideanBall_mono hρ'pos.le hρ'r hz.1, ?_, lt_of_le_of_ne hz.2.2 h0⟩
        have := hz.2.1
        linarith
    have hle := restrict_le_of_subset_union_null volume hQm hSm hNnull hQsub
    have hN0le : (eLpNorm (fun z => V z - κ) 2 (volume.restrict
        (euclideanBall x (r / (2 * s)) ×ˢ Ioc (0 - (r / (2 * s)) ^ 2) 0))).toReal ≤
        (eLpNorm (fun z => V z - κ) 2 (volume.restrict
          (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0))).toReal :=
      ENNReal.toReal_mono hgS.ne (eLpNorm_mono_measure _ hle)
    have hN1 : (eLpNorm (fun z => V z - κ) 2 (volume.restrict
        (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0))).toReal =
        Real.sqrt (cd * r ^ d * (r ^ 2 / K)) * Real.sqrt (⨍ z, |V z - κ| ^ 2 ∂(volume.restrict
          (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0))) := by
      rw [← sqrt_integral_sq_eq _ hgS,
        sqrt_integral_eq_mul_avg (volume.restrict (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0))
          (by rw [hvolS]; exact hmSpos) (fun z => V z - κ), hvolS]
    have hcm : (((r / (2 * s)) ^ (d + 2))⁻¹) ^ (1 / 2 : ℝ) *
        Real.sqrt (cd * r ^ d * (r ^ 2 / K)) = Real.sqrt W := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
      congr 1
      rw [hW, div_pow, inv_div]
      field_simp
      ring
    have hcpos : 0 ≤ (((r / (2 * s)) ^ (d + 2))⁻¹) ^ (1 / 2 : ℝ) := by positivity
    have hCle : C₀ * (2 * s) ^ α / 2 * Real.sqrt W ≤
        max 1 (max (C₀ * (2 * s) ^ α / 2 * Real.sqrt W) (B / θ₀)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    refine hA.trans ?_
    have hC₀0 : 0 ≤ C₀ := by linarith
    calc C₀ * (2 * s * θ) ^ α / 2 * (((r / (2 * s)) ^ (d + 2))⁻¹) ^ (1 / 2 : ℝ) *
          (eLpNorm (fun z => V z - κ) 2 (volume.restrict
            (euclideanBall x (r / (2 * s)) ×ˢ Ioc (0 - (r / (2 * s)) ^ 2) 0))).toReal
        ≤ C₀ * (2 * s * θ) ^ α / 2 * (((r / (2 * s)) ^ (d + 2))⁻¹) ^ (1 / 2 : ℝ) *
          (Real.sqrt (cd * r ^ d * (r ^ 2 / K)) * Real.sqrt (⨍ z, |V z - κ| ^ 2 ∂(volume.restrict
            (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)))) :=
          mul_le_mul_of_nonneg_left (hN0le.trans hN1.le) (by positivity)
      _ = (C₀ * (2 * s) ^ α / 2 * Real.sqrt W) * θ ^ α * Real.sqrt (⨍ z, |V z - κ| ^ 2
            ∂(volume.restrict (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0))) := by
          rw [Real.mul_rpow (by positivity) hθ.le, ← hcm]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCle hθαpos.le) (Real.sqrt_nonneg _)
  · -- Case B: large `θ`, comparison of averages
    have hθθ₀ : θ₀ < θ := by
      rw [hθ₀, div_lt_iff₀ (by positivity)]
      push_neg at hc
      nlinarith
    have hEpos' : 0 < (volume (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)).toReal := by
      rw [hmE]; exact hmEpos
    have hSpos' : 0 < (volume (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)).toReal := by
      rw [hmS]; exact hmSpos
    have hint : IntegrableOn (fun z => |V z - κ| ^ 2)
        (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0) volume := by
      have := hgS.integrable_sq
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      exact (sq_abs _).symm
    have hb := avg_sq_le_of_subset volume hEm hSm hEsub
      (by simpa [measureReal_def] using hEpos') (by simpa [measureReal_def] using hSpos') hSfin hint
    have hratio : (volume.real (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)) /
        (volume.real (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)) =
        (1 / θ) ^ (d + 2) := by
      rw [measureReal_def, measureReal_def, hmS, hmE]
      have e : cd * (θ * r) ^ d * ((θ * r) ^ 2 / K) =
          θ ^ (d + 2) * (cd * r ^ d * (r ^ 2 / K)) := by
        rw [mul_pow, mul_pow, pow_add]
        ring
      have hne : cd * r ^ d * (r ^ 2 / K) ≠ 0 := hmSpos.ne'
      rw [e, div_eq_iff (mul_ne_zero (pow_ne_zero _ hθ0) hne), one_div, inv_pow,
        inv_mul_cancel_left₀ (pow_ne_zero _ hθ0)]
    rw [hratio] at hb
    have h1 : Real.sqrt (⨍ z in euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0,
        |V z - κ| ^ 2) ≤ Real.sqrt ((1 / θ) ^ (d + 2)) *
          Real.sqrt (⨍ z, |V z - κ| ^ 2 ∂(volume.restrict
            (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0))) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hb
    have h2 : Real.sqrt ((1 / θ) ^ (d + 2)) ≤ B := by
      refine Real.sqrt_le_sqrt ?_
      exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hθ₀pos hθθ₀.le) _
    have h3 : B ≤ B / θ₀ * θ ^ α := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hθ₀pos]
      exact mul_le_mul_of_nonneg_left (le_trans hθθ₀.le hθα) hBpos.le
    have hCle : B / θ₀ ≤ max 1 (max (C₀ * (2 * s) ^ α / 2 * Real.sqrt W) (B / θ₀)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    refine step1.trans (h1.trans ?_)
    calc Real.sqrt ((1 / θ) ^ (d + 2)) *
          Real.sqrt (⨍ z, |V z - κ| ^ 2 ∂(volume.restrict
            (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0)))
        ≤ (B / θ₀ * θ ^ α) * Real.sqrt (⨍ z, |V z - κ| ^ 2 ∂(volume.restrict
            (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0))) :=
          mul_le_mul_of_nonneg_right (h2.trans h3) (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCle hθαpos.le) (Real.sqrt_nonneg _)

end EinsteinFull.ParabolicBridge
