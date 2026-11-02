import EinsteinFull.Calculus.SpatialPairingSupport
import Mathlib.Analysis.Convex.Integral

/-! Minkowski's integral inequality for kernel averages of the stationary translation
action, proved by convexity: the set of `L²` elements with `Lᵖ` norm at most `M` is closed
and convex, and each translate of an element of it stays in it. -/

open MeasureTheory Filter
open scoped Topology ENNReal
open EinsteinRelation

noncomputable section

namespace EinsteinFull.Calculus.K6

/-- The set of `L²` elements whose `Lᵖ` seminorm is at most `m`. -/
def lpBall {d : ℕ} (Q : Measure (FieldPair d)) (q m : ℝ≥0∞) : Set (Lp ℂ 2 Q) :=
  {V | eLpNorm (V : FieldPair d → ℂ) q Q ≤ m}

theorem convex_lpBall {d : ℕ} (Q : Measure (FieldPair d)) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (m : ℝ≥0∞) : Convex ℝ (lpBall Q q m) := by
  intro V hV W hW a b ha hb hab
  show eLpNorm (((a • V + b • W : Lp ℂ 2 Q)) : FieldPair d → ℂ) q Q ≤ m
  calc eLpNorm (((a • V + b • W : Lp ℂ 2 Q)) : FieldPair d → ℂ) q Q
      = eLpNorm (a • (V : FieldPair d → ℂ) + b • (W : FieldPair d → ℂ)) q Q := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [Lp.coeFn_add (a • V) (b • W), Lp.coeFn_smul a V,
          Lp.coeFn_smul b W] with ω h1 h2 h3
        rw [h1, Pi.add_apply, Pi.add_apply, h2, h3]
    _ ≤ eLpNorm (a • (V : FieldPair d → ℂ)) q Q + eLpNorm (b • (W : FieldPair d → ℂ)) q Q :=
        eLpNorm_add_le hq
    _ = ENNReal.ofReal a * eLpNorm (V : FieldPair d → ℂ) q Q +
          ENNReal.ofReal b * eLpNorm (W : FieldPair d → ℂ) q Q := by
        rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal ha,
          Real.enorm_eq_ofReal hb]
    _ ≤ ENNReal.ofReal a * m + ENNReal.ofReal b * m := by
        gcongr <;> assumption
    _ = m := by
        rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]

theorem smul_mem_lpBall {d : ℕ} (Q : Measure (FieldPair d)) {q m : ℝ≥0∞} {V : Lp ℂ 2 Q}
    (hV : V ∈ lpBall Q q m) {s : ℝ} (hs : |s| ≤ 1) : s • V ∈ lpBall Q q m := by
  show eLpNorm (((s • V : Lp ℂ 2 Q)) : FieldPair d → ℂ) q Q ≤ m
  rw [eLpNorm_congr_ae (Lp.coeFn_smul s V), eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  calc ENNReal.ofReal |s| * eLpNorm (V : FieldPair d → ℂ) q Q ≤ 1 * m := by
        gcongr
        exact ENNReal.ofReal_le_one.2 hs
        exact hV
    _ = m := one_mul m

theorem isClosed_lpBall {d : ℕ} (Q : Measure (FieldPair d)) (q m : ℝ≥0∞) :
    IsClosed (lpBall Q q m) := by
  refine IsSeqClosed.isClosed ?_
  intro V W hV hVW
  have hm : TendstoInMeasure Q (fun n => (V n : FieldPair d → ℂ)) atTop (W : FieldPair d → ℂ) :=
    tendstoInMeasure_of_tendsto_Lp hVW
  obtain ⟨φ, hφ, hae⟩ := hm.exists_seq_tendsto_ae
  have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := q) (f := fun n => (V (φ n) : FieldPair d → ℂ))
    (fun n => Lp.aestronglyMeasurable _) (W : FieldPair d → ℂ) (Lp.aestronglyMeasurable W) hae
  refine hlim.trans ?_
  have : ∀ n, eLpNorm (V (φ n) : FieldPair d → ℂ) q Q ≤ m := fun n => hV (φ n)
  calc _ ≤ liminf (fun _ : ℕ => m) atTop := liminf_le_liminf (Eventually.of_forall this)
    _ = m := liminf_const _

theorem smul_nonneg_mem_lpBall {d : ℕ} (Q : Measure (FieldPair d)) {q m : ℝ≥0∞}
    {V : Lp ℂ 2 Q} (hV : V ∈ lpBall Q q m) {t : ℝ} (ht : 0 ≤ t) :
    t • V ∈ lpBall Q q (ENNReal.ofReal t * m) := by
  show eLpNorm (((t • V : Lp ℂ 2 Q)) : FieldPair d → ℂ) q Q ≤ _
  rw [eLpNorm_congr_ae (Lp.coeFn_smul t V), eLpNorm_const_smul, Real.enorm_eq_ofReal ht]
  gcongr
  exact hV

theorem complexTranslation_mem_lpBall {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) {q m : ℝ≥0∞} {U : Lp ℂ 2 Q} (hU : U ∈ lpBall Q q m) (y : Vec d) :
    complexTranslation Q hQ y U ∈ lpBall Q q m := by
  show eLpNorm ((complexTranslation Q hQ y U : Lp ℂ 2 Q) : FieldPair d → ℂ) q Q ≤ m
  rw [eLpNorm_congr_ae (EinsteinFull.coeFn_complexTranslation Q hQ y U)]
  have := eLpNorm_comp_measurePreserving (p := q) (Lp.aestronglyMeasurable U)
    (measurePreserving_translate Q hQ y)
  exact (le_of_eq this).trans hU

theorem kernel_average_mem_lpBall {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {q m : ℝ≥0∞} (hq : 1 ≤ q)
    (c : Vec d → ℝ) (hc : Integrable c) (hcc : Continuous c)
    {U : Lp ℂ 2 Q} (hU : U ∈ lpBall Q q m) :
    (∫ y : Vec d, c y • complexTranslation Q hQ y U : Lp ℂ 2 Q) ∈
      lpBall Q q (ENNReal.ofReal (∫ y : Vec d, |c y|) * m) := by
  set A : ℝ := ∫ y : Vec d, |c y| with hA
  have hA0 : 0 ≤ A := integral_nonneg fun y => abs_nonneg _
  rcases hA0.eq_or_lt with hAz | hApos
  · have hcz : (fun y => |c y|) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg _) hc.abs).1 hAz.symm
    have hI : (∫ y : Vec d, c y • complexTranslation Q hQ y U : Lp ℂ 2 Q) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hcz] with y hy
      have : c y = 0 := abs_eq_zero.1 hy
      simp [this]
    rw [hI, ← hAz]
    show eLpNorm (((0 : Lp ℂ 2 Q)) : FieldPair d → ℂ) q Q ≤ _
    rw [eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 Q)]
    simp
  have hdens : Measurable fun y => ENNReal.ofReal |c y| := (hcc.abs.measurable).ennreal_ofReal
  set μ : Measure (Vec d) := volume.withDensity (fun y => ENNReal.ofReal |c y|) with hμ
  have hμuniv : μ Set.univ = ENNReal.ofReal A := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      hA, ofReal_integral_eq_lintegral_ofReal hc.abs (Eventually.of_forall fun y => abs_nonneg _)]
  haveI : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact ENNReal.ofReal_lt_top⟩
  haveI : NeZero μ := ⟨fun h => by
    rw [h] at hμuniv
    simp only [Measure.coe_zero, Pi.zero_apply] at hμuniv
    exact hApos.ne' (ENNReal.ofReal_eq_zero.1 hμuniv.symm |>.antisymm hA0)⟩
  set f : Vec d → Lp ℂ 2 Q := fun y =>
    (|c y|⁻¹ * c y) • complexTranslation Q hQ y U with hf
  have hpt : ∀ y, |c y| • f y = c y • complexTranslation Q hQ y U := by
    intro y
    simp only [hf, smul_smul]
    congr 1
    by_cases h : c y = 0
    · simp [h]
    · rw [mul_inv_cancel_left₀ (abs_ne_zero.2 h)]
  have hfmem : ∀ y, f y ∈ lpBall Q q m := by
    intro y
    refine smul_mem_lpBall Q (complexTranslation_mem_lpBall Q hQ hU y) ?_
    by_cases h : c y = 0
    · simp [h]
    · rw [abs_mul, abs_inv, abs_abs, inv_mul_cancel₀ (abs_ne_zero.2 h)]
  have hint : Integrable f μ := by
    rw [hμ, integrable_withDensity_iff_integrable_smul' hdens
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    have ht : Continuous (fun x : Vec d => complexTranslation Q hQ x U) :=
      (continuous_complexTranslation Q hQ).comp (continuous_id.prodMk continuous_const)
    have key : (fun y => (ENNReal.ofReal |c y|).toReal • f y) =
        fun y => c y • complexTranslation Q hQ y U := by
      funext y
      rw [ENNReal.toReal_ofReal (abs_nonneg _), hpt]
    rw [key]
    apply (hc.norm.mul_const ‖U‖).mono' (hcc.smul ht).aestronglyMeasurable
    filter_upwards [] with x
    show ‖c x • complexTranslation Q hQ x U‖ ≤ _
    rw [norm_smul, norm_complexTranslation, Real.norm_eq_abs]
  have hI : (∫ y : Vec d, c y • complexTranslation Q hQ y U : Lp ℂ 2 Q) = A • ⨍ y, f y ∂μ := by
    have h1 : ∫ y, f y ∂μ = ∫ y : Vec d, c y • complexTranslation Q hQ y U := by
      rw [hμ, integral_withDensity_eq_integral_toReal_smul hdens
        (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
      congr 1
      funext y
      rw [ENNReal.toReal_ofReal (abs_nonneg _), hpt]
    rw [average_eq, ← h1, Measure.real, hμuniv, ENNReal.toReal_ofReal hA0, smul_smul,
      mul_inv_cancel₀ hApos.ne', one_smul]
  rw [hI]
  exact smul_nonneg_mem_lpBall Q (Convex.average_mem (convex_lpBall Q hq m) (isClosed_lpBall Q q m)
    (Eventually.of_forall hfmem) hint) hA0

/-- Minkowski's integral inequality for real kernel averages of the stationary translation
action: an `Lᵖ` field stays in `Lᵖ`, with the kernel's `L¹` mass as the constant. -/
theorem memLp_integral_smul_complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {p : ℝ} (hp : 1 ≤ p)
    (c : Vec d → ℝ) (hc : Integrable c) (hcc : Continuous c)
    (U : Lp ℂ 2 Q) (hU : MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) Q) :
    MemLp ((∫ y : Vec d, c y • complexTranslation Q hQ y U : Lp ℂ 2 Q) : FieldPair d → ℂ)
        (ENNReal.ofReal p) Q ∧
      (eLpNorm ((∫ y : Vec d, c y • complexTranslation Q hQ y U : Lp ℂ 2 Q) :
          FieldPair d → ℂ) (ENNReal.ofReal p) Q).toReal ≤
        (∫ y : Vec d, |c y|) * (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) Q).toReal := by
  have hq : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hUm : U ∈ lpBall Q (ENNReal.ofReal p) (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) Q) :=
    by change eLpNorm _ _ _ ≤ _; exact le_rfl
  have hmem := kernel_average_mem_lpBall Q hQ hq c hc hcc hUm
  have hA0 : 0 ≤ ∫ y : Vec d, |c y| := integral_nonneg fun y => abs_nonneg _
  have hfin : ENNReal.ofReal (∫ y : Vec d, |c y|) *
      eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) Q ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU.eLpNorm_ne_top
  have hle : eLpNorm ((∫ y : Vec d, c y • complexTranslation Q hQ y U : Lp ℂ 2 Q) :
      FieldPair d → ℂ) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (∫ y : Vec d, |c y|) *
      eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) Q := hmem
  have hlt := lt_of_le_of_lt hle hfin.lt_top
  refine ⟨hlt, ?_⟩
  have := ENNReal.toReal_mono hfin hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0] at this

end EinsteinFull.Calculus.K6
