import EinsteinFull.Calculus.ParabolicBridgeSlice

/-!
# `L²` slices and weak continuity of the delayed mollification
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ} {ε : ℝ} {hε : 0 < ε}

theorem tmoll_le_of_ker_bound {B : ℝ} (hB : ∀ r, |ker ε hε r| ≤ B) (r : ℝ) :
    tmoll ε hε r ≤ B := by
  have := hB (r + 2 * ε)
  simp only [ker, add_sub_cancel_right] at this
  exact (le_abs_self _).trans this

/-- Every time slice of the delayed mollification is `L²` on any set. -/
theorem slice_memLp_restrict (F : Vec d × ℝ → ℝ) (hF : Measurable F)
    (hFl : ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ≠ ⊤) (t : ℝ) (K : Set (Vec d)) :
    MemLp (fun x => MolS ε hε F (x, t)) 2 (volume.restrict K) := by
  obtain ⟨B, hB0, hB⟩ := ker_bound (ε := ε) (hε := hε)
  have hmeas : Measurable fun x => MolS ε hε F (x, t) :=
    (MolS_measurable F hF).comp (measurable_id.prodMk measurable_const)
  have hm : Measurable fun z : Vec d × ℝ => ‖F z‖ₑ ^ (2 : ℝ) := hF.enorm.pow_const _
  refine (eLpNorm_two_lt_top_iff hmeas.aestronglyMeasurable).mpr ?_
  have hpt : ∀ x : Vec d, ‖MolS ε hε F (x, t)‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal B * ∫⁻ s, ‖F (x, s)‖ₑ ^ (2 : ℝ) := by
    intro x
    have h1 := enorm_Mol_sq_le (ε := ε) (hε := hε) F hF (shiftT (2 * ε) (x, t))
    refine h1.trans ?_
    have hslice : Measurable fun s : ℝ => ‖F (x, s)‖ₑ ^ (2 : ℝ) :=
      (hF.comp (measurable_const.prodMk measurable_id)).enorm.pow_const _
    rw [← lintegral_const_mul _ hslice]
    refine lintegral_mono fun s => ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (tmoll_le_of_ker_bound hB _)) le_rfl
  have h1 : ∫⁻ x in K, ‖MolS ε hε F (x, t)‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal B * ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) := by
    calc ∫⁻ x in K, ‖MolS ε hε F (x, t)‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ x in K, ENNReal.ofReal B * ∫⁻ s, ‖F (x, s)‖ₑ ^ (2 : ℝ) :=
          lintegral_mono hpt
      _ ≤ ∫⁻ x, ENNReal.ofReal B * ∫⁻ s, ‖F (x, s)‖ₑ ^ (2 : ℝ) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal B * ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFl) h1

theorem abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

/-- Weak continuity of the delayed mollification in time. -/
theorem weakCont_aux (F : Vec d × ℝ → ℝ) (hF : Measurable F) (hF2 : MemLp F 2 volume)
    (J : Set ℝ) (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hFJ : ∀ x s, s ∉ J → F (x, s) = 0) (ψ : Vec d → ℝ) (hψ : MemLp ψ 2 volume) :
    Continuous fun t => ∫ x, MolS ε hε F (x, t) * ψ x := by
  obtain ⟨B, hB0, hB⟩ := ker_bound (ε := ε) (hε := hε)
  have hFl : Integrable (fun z => F z ^ 2) volume := hF2.integrable_sq
  have hψl : Integrable (fun x => ψ x ^ 2) volume := hψ.integrable_sq
  have hind : Integrable (J.indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hJ).mpr (integrableOn_const hJfin)
  have hP : Integrable (fun z : Vec d × ℝ => ψ z.1 ^ 2 * J.indicator (fun _ : ℝ => (1 : ℝ)) z.2)
      (volume.prod volume) := hψl.mul_prod hind
  have hFψ : Integrable (fun z : Vec d × ℝ => F z * ψ z.1) (volume.prod volume) := by
    have hFl' : Integrable (fun z => F z ^ 2) (volume.prod volume) := by
      rwa [Measure.volume_eq_prod] at hFl
    refine Integrable.mono' ((hFl'.add hP).div_const 2)
      (hF.aestronglyMeasurable.mul
        (hψ.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_fst))
      (Filter.Eventually.of_forall fun z => ?_)
    by_cases hs : z.2 ∈ J
    · simp only [Set.indicator_of_mem hs, mul_one, Real.norm_eq_abs, Pi.add_apply]
      exact abs_mul_le_half_sq _ _
    · have h0 : F z = 0 := hFJ z.1 z.2 hs
      simp [h0, Set.indicator_of_notMem hs]
  set m : ℝ → ℝ := fun s => ∫ x, F (x, s) * ψ x with hm
  have hmint : Integrable m volume := hFψ.integral_prod_right
  have hcalc : ∀ t, ∫ x, MolS ε hε F (x, t) * ψ x = ∫ s, ker ε hε (t - s) * m s := by
    intro t
    have e1 : ∀ x : Vec d, MolS ε hε F (x, t) * ψ x =
        ∫ s, ker ε hε (t - s) * (F (x, s) * ψ x) := by
      intro x
      rw [MolS_eq, ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show ker ε hε (t - s) * F (x, s) * ψ x = ker ε hε (t - s) * (F (x, s) * ψ x)
      ring
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun (x : Vec d) (s : ℝ) =>
        ker ε hε (t - s) * (F (x, s) * ψ x)) (volume.prod volume) :=
      hFψ.bdd_mul (c := B)
        ((ker_continuous.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => by simpa using hB _)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    beta_reduce
    rw [integral_const_mul]
  have hfun : (fun t => ∫ x, MolS ε hε F (x, t) * ψ x) =
      fun t => ∫ s, ker ε hε (t - s) * m s := funext hcalc
  rw [hfun]
  refine continuous_of_dominated (F := fun t s => ker ε hε (t - s) * m s)
    (bound := fun s => B * ‖m s‖) ?_ ?_ ?_ ?_
  · intro t
    exact ((ker_continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
      hmint.aestronglyMeasurable
  · intro t
    refine Filter.Eventually.of_forall fun s => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hB _) (norm_nonneg _)
  · exact hmint.norm.const_mul B
  · exact Filter.Eventually.of_forall fun s =>
      ((ker_continuous.comp (continuous_id.sub continuous_const)).mul continuous_const)

end EinsteinFull.ParabolicBridge
