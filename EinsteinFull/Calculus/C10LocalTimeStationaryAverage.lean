import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The real iterated square average is dominated by the product-space L² norm.
This estimate also covers the Bochner integral's nonintegrable convention. -/
private lemma sqrt_iterated_square_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (κ : Measure Y) [SFinite κ]
    (g : X × Y → ℂ) (hg : Measurable g) :
    ‖Real.sqrt (∫ x, ∫ y, ‖g (x, y)‖ ^ 2 ∂κ ∂ν)‖ₑ ≤
      eLpNorm g 2 (ν.prod κ) := by
  have hn : 0 ≤ ∫ x, ∫ y, ‖g (x, y)‖ ^ 2 ∂κ ∂ν :=
    integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _
  have hi : ENNReal.ofReal (∫ x, ∫ y, ‖g (x, y)‖ ^ 2 ∂κ ∂ν) ≤
      ∫⁻ x, ∫⁻ y, ‖g (x, y)‖ₑ ^ (2 : ℝ) ∂κ ∂ν := by
    calc
      _ = ‖∫ x, ∫ y, ‖g (x, y)‖ ^ 2 ∂κ ∂ν‖ₑ :=
        (Real.enorm_eq_ofReal hn).symm
      _ ≤ ∫⁻ x, ‖∫ y, ‖g (x, y)‖ ^ 2 ∂κ‖ₑ ∂ν :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ _ := lintegral_mono fun x => by
        calc
          _ ≤ ∫⁻ y, ‖‖g (x, y)‖ ^ 2‖ₑ ∂κ := enorm_integral_le_lintegral_enorm _
          _ = _ := lintegral_congr fun y => by
            rw [Real.enorm_eq_ofReal (sq_nonneg _),
              ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hg.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_prod _ (hg.enorm.pow_const _).aemeasurable]
  rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg hn (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact ENNReal.rpow_le_rpow hi (by positivity)

private lemma elp_power_identity {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (hp0 : 0 < p) (μ : Measure Z) (g : Z → ℂ) (hg : Measurable g) :
    (eLpNorm g (ENNReal.ofReal p) μ) ^ p = ∫⁻ z, ‖g z‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity)
    ENNReal.ofReal_ne_top hg.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul]
  simp [one_div, hp0.ne']

theorem local_time_stationary_square_average_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (κ : Measure (Vec d)) [IsProbabilityMeasure κ]
    (p M : ℝ) (hp : 2 ≤ p) (hM : 0 ≤ M)
    (F : ℝ × FieldPair d → ℂ) (hF : Measurable F)
    (hbound : ∀ᵐ s ∂ν,
      MemLp (fun ω => F (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (fun ω => F (s, ω)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ M) :
    let A := fun ω : FieldPair d => Real.sqrt
      (∫ s, ∫ y, ‖F (s, translate y ω)‖ ^ 2 ∂κ ∂ν)
    MemLp A (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm A (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ M := by
  let := reducedLaw_probability Q
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpz : ENNReal.ofReal p ≠ 0 := by positivity
  have hpfin : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have htwo : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp)
  let G : (ℝ × Vec d) × FieldPair d → ℂ :=
    fun q => F (q.1.1, translate q.1.2 q.2)
  have hG : Measurable G :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  let A := fun ω : FieldPair d => Real.sqrt
    (∫ s, ∫ y, ‖F (s, translate y ω)‖ ^ 2 ∂κ ∂ν)
  change MemLp A (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm A (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ M
  have hshift : Measurable (fun q : (FieldPair d × ℝ) × Vec d =>
      F (q.1.2, translate q.2 q.1.1)) :=
    hF.comp ((measurable_snd.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst))))
  have hInner : StronglyMeasurable (fun q : FieldPair d × ℝ =>
      ∫ y, ‖F (q.2, translate y q.1)‖ ^ 2 ∂κ) :=
    (hshift.norm.pow_const 2).stronglyMeasurable.integral_prod_right'
  have hOuter : StronglyMeasurable (fun ω : FieldPair d =>
      ∫ s, ∫ y, ‖F (s, translate y ω)‖ ^ 2 ∂κ ∂ν) :=
    hInner.integral_prod_right'
  have hA : Measurable A :=
    Real.continuous_sqrt.measurable.comp hOuter.measurable
  have hpoint (ω : FieldPair d) :
      ‖A ω‖ₑ ^ p ≤ ∫⁻ z, ‖G (z, ω)‖ₑ ^ p ∂ν.prod κ := by
    have hslice : Measurable (fun z => G (z, ω)) :=
      hG.comp measurable_prodMk_right
    rw [← elp_power_identity p hp0 (ν.prod κ) _ hslice]
    apply ENNReal.rpow_le_rpow _ hp0.le
    exact (sqrt_iterated_square_le ν κ _ hslice).trans
      (eLpNorm_le_eLpNorm_of_exponent_le htwo)
  have hmoment : ∫⁻ ω, ∫⁻ z, ‖G (z, ω)‖ₑ ^ p ∂ν.prod κ ∂reducedLaw Q ≤
      ENNReal.ofReal M ^ p := by
    rw [lintegral_lintegral_swap (hG.enorm.pow_const p).aemeasurable.prod_swap]
    rw [lintegral_prod _ ((hG.enorm.pow_const p).lintegral_prod_right').aemeasurable]
    calc
      _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal M ^ p ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hbound] with s hs
        calc
          _ ≤ ∫⁻ y : Vec d, ENNReal.ofReal M ^ p ∂κ := by
            apply lintegral_mono
            intro y
            change ∫⁻ ω, ‖F (s, translate y ω)‖ₑ ^ p ∂reducedLaw Q ≤ _
            have hFs : Measurable (fun ω => F (s, ω)) :=
              hF.comp measurable_prodMk_left
            have hstat := (measurePreserving_translate (reducedLaw Q)
              (reducedLaw_stationary Q) y).lintegral_comp (hFs.enorm.pow_const p)
            rw [hstat, ← elp_power_identity p hp0 (reducedLaw Q) (fun ω => F (s, ω)) hFs]
            apply ENNReal.rpow_le_rpow _ hp0.le
            calc
              _ = ENNReal.ofReal (eLpNorm (fun ω => F (s, ω))
                  (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
                (ENNReal.ofReal_toReal hs.1.eLpNorm_lt_top.ne).symm
              _ ≤ _ := ENNReal.ofReal_le_ofReal hs.2
          _ = _ := by simp
      _ = _ := by simp
  have hnorm : eLpNorm A (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
    apply (ENNReal.rpow_le_rpow_iff hp0).mp
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpz hpfin hA.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul]
    simpa only [one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] using
      (lintegral_mono hpoint).trans hmoment
  exact ⟨hnorm.trans_lt ENNReal.ofReal_lt_top,
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm).trans_eq
      (ENNReal.toReal_ofReal hM)⟩

end EinsteinFull.Blueprint

#print axioms EinsteinFull.Blueprint.local_time_stationary_square_average_memLp

#lint
