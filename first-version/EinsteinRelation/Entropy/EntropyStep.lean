import EinsteinRelation.Entropy.FisherBoundRoute
import EinsteinRelation.Entropy.FisherCauchySchwarz
import EinsteinRelation.Calculus.WeakChainRule

/-! # The entropy step of Lemma 4.1

Source: `paper/main.tex` 569-596 (Step 3 of Lemma 4.1), in the discrete form of
the resolvent route to Lemma 4.1. For an `H¹` solution `ρ ≥ 0` of
`μρ - L*ρ = μρ'`, testing with the regularized logarithm `g_ε(ρ)` gives

`¼ E[Dρ·aDρ / (ρ + ε)] ≤ μ (E Φ_ε(ρ') - E Φ_ε(ρ)) + Λ λ² E[ρ]`,

where `g_ε(u) = ∫₁ᵘ (ε + max(v, 0))⁻¹ dv` (so `g_ε(u) = log((ε+u)/(ε+1))` for `u ≥ 0`) and
`Φ_ε(u) = ∫₁ᵘ g_ε`. The denominator `ρ + ε` is affine in `ρ`, which is what the final convexity
step needs.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology NNReal

noncomputable section

open EinsteinRelation.External.GantertSection7Support

namespace EinsteinRelation.Entropy

variable {d : ℕ}

/-! ## The regularized logarithm -/

/-- `k_ε(v) = (ε + max(v, 0))⁻¹`, the derivative of the regularized logarithm. -/
def rlogDeriv (ε v : ℝ) : ℝ := (ε + max v 0)⁻¹

/-- The regularized logarithm `g_ε(u) = ∫₁ᵘ k_ε`. -/
def rlog (ε u : ℝ) : ℝ := ∫ v in (1 : ℝ)..u, rlogDeriv ε v

/-- The regularized entropy `Φ_ε(u) = ∫₁ᵘ g_ε`. -/
def rent (ε u : ℝ) : ℝ := ∫ v in (1 : ℝ)..u, rlog ε v

theorem rlogDeriv_pos {ε : ℝ} (hε : 0 < ε) (v : ℝ) : 0 < rlogDeriv ε v :=
  inv_pos.mpr (add_pos_of_pos_of_nonneg hε (le_max_right _ _))

theorem rlogDeriv_le {ε : ℝ} (hε : 0 < ε) (v : ℝ) : rlogDeriv ε v ≤ ε⁻¹ :=
  inv_anti₀ hε (le_add_of_nonneg_right (le_max_right _ _))

theorem rlogDeriv_of_nonneg (ε : ℝ) {v : ℝ} (hv : 0 ≤ v) : rlogDeriv ε v = (ε + v)⁻¹ := by
  rw [rlogDeriv, max_eq_left hv]

theorem continuous_rlogDeriv {ε : ℝ} (hε : 0 < ε) : Continuous (rlogDeriv ε) :=
  (continuous_const.add (continuous_id.max continuous_const)).inv₀ fun v =>
    (add_pos_of_pos_of_nonneg hε (le_max_right _ _)).ne'

theorem hasDerivAt_rlog {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    HasDerivAt (rlog ε) (rlogDeriv ε u) u :=
  ((continuous_rlogDeriv hε).integral_hasStrictDerivAt 1 u).hasDerivAt

theorem deriv_rlog {ε : ℝ} (hε : 0 < ε) : deriv (rlog ε) = rlogDeriv ε :=
  funext fun u => (hasDerivAt_rlog hε u).deriv

theorem contDiff_rlog {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (rlog ε) :=
  contDiff_one_iff_deriv.mpr ⟨fun u => (hasDerivAt_rlog hε u).differentiableAt,
    by rw [deriv_rlog hε]; exact continuous_rlogDeriv hε⟩

theorem continuous_rlog {ε : ℝ} (hε : 0 < ε) : Continuous (rlog ε) :=
  (contDiff_rlog hε).continuous

theorem abs_deriv_rlog_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) : |deriv (rlog ε) u| ≤ ε⁻¹ := by
  rw [deriv_rlog hε, abs_of_pos (rlogDeriv_pos hε u)]
  exact rlogDeriv_le hε u

theorem rlog_one (ε : ℝ) : rlog ε 1 = 0 := intervalIntegral.integral_same

theorem monotone_rlog {ε : ℝ} (hε : 0 < ε) : Monotone (rlog ε) :=
  monotone_of_deriv_nonneg (fun u => (hasDerivAt_rlog hε u).differentiableAt) fun u => by
    rw [deriv_rlog hε]
    exact (rlogDeriv_pos hε u).le

theorem abs_rlog_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) : |rlog ε u| ≤ ε⁻¹ * |u - 1| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := u)
    (f := rlogDeriv ε) (C := ε⁻¹) fun v _ => by
      rw [Real.norm_eq_abs, abs_of_pos (rlogDeriv_pos hε v)]
      exact rlogDeriv_le hε v
  rw [Real.norm_eq_abs] at h
  exact h

theorem hasDerivAt_rent {ε : ℝ} (hε : 0 < ε) (u : ℝ) : HasDerivAt (rent ε) (rlog ε u) u :=
  ((continuous_rlog hε).integral_hasStrictDerivAt 1 u).hasDerivAt

theorem rent_one (ε : ℝ) : rent ε 1 = 0 := intervalIntegral.integral_same

/-- **Convexity of the regularized entropy**: `Φ(a) - Φ(b) ≥ g(b) (a - b)`. -/
theorem rent_sub_ge {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    rlog ε b * (a - b) ≤ rent ε a - rent ε b := by
  have hc := continuous_rlog hε
  have hsub : rent ε a - rent ε b = ∫ v in b..a, rlog ε v := by
    unfold rent
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := volume) 1 a)
      (hc.intervalIntegrable (μ := volume) 1 b)]
  rw [hsub]
  rcases le_total b a with hba | hab
  · have h := intervalIntegral.integral_mono_on (μ := volume) hba (continuous_const.intervalIntegrable _ _)
      (hc.intervalIntegrable b a) fun v hv => monotone_rlog hε hv.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  · have h := intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable a b)
      (continuous_const.intervalIntegrable _ _) fun v hv => monotone_rlog hε hv.2
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    rw [intervalIntegral.integral_symm]
    linarith

theorem rent_nonneg {ε : ℝ} (hε : 0 < ε) (a : ℝ) : 0 ≤ rent ε a := by
  have h := rent_sub_ge hε a 1
  rw [rlog_one, zero_mul, rent_one, sub_zero] at h
  exact h

theorem rent_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) : rent ε a ≤ ε⁻¹ * (a - 1) ^ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := a)
    (f := rlog ε) (C := ε⁻¹ * |a - 1|) fun v hv => by
      rw [Real.norm_eq_abs]
      refine (abs_rlog_le hε v).trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hε.le))
      rcases Set.mem_uIoc.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ v - 1), abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith : v - 1 ≤ 0), abs_of_nonpos (by linarith : a - 1 ≤ 0)]
        linarith
  rw [Real.norm_eq_abs] at h
  calc rent ε a ≤ |rent ε a| := le_abs_self _
    _ ≤ ε⁻¹ * |a - 1| * |a - 1| := h
    _ = ε⁻¹ * (a - 1) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

theorem measurable_rlog {ε : ℝ} (hε : 0 < ε) : Measurable (rlog ε) := (continuous_rlog hε).measurable

theorem measurable_rent {ε : ℝ} (hε : 0 < ε) : Measurable (rent ε) :=
  (continuous_iff_continuousAt.mpr fun u => (hasDerivAt_rent hε u).continuousAt).measurable

/-- `ρ² k_ε(ρ) ≤ ρ` for `ρ ≥ 0`. -/
theorem sq_mul_rlogDeriv_le {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 * rlogDeriv ε r ≤ r := by
  rw [rlogDeriv_of_nonneg ε hr, ← div_eq_mul_inv, div_le_iff₀ (by linarith)]
  nlinarith

/-! ## The quadratic form of the coefficient -/

/-- The quadratic form `v·a(0)v = ∑_k v_k ∑_j a_{jk}(0) v_j`. -/
def qform (w : FieldPair d) (v : Vec d) : ℝ := ∑ k, v k * ∑ j, w.1 0 j k * v j

/-- The force component `(a(0) e₁)·v = ∑_j a_{j1}(0) v_j`. -/
def bform (hd : 2 ≤ d) (w : FieldPair d) (v : Vec d) : ℝ :=
  ∑ j, w.1 0 j (firstCoordinateIndex hd) * v j

theorem dot_unitVector_left' (i : Fin d) (x : Vec d) : dot (unitVector i) x = x i := by
  simp [dot, unitVector, Pi.single_apply]

theorem euclideanSq_unitVector' (i : Fin d) : euclideanSq (unitVector i) = 1 := by
  rw [euclideanSq, dot_unitVector_left']
  simp [unitVector]

theorem dot_mulVec_eq_qform {w : FieldPair d} (hsym : (w.1 0).transpose = w.1 0) (v : Vec d) :
    dot v ((w.1 0).mulVec v) = qform w v := by
  unfold dot qform
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have := congrFun (congrFun hsym k) j
  rw [Matrix.transpose_apply] at this
  exact this.symm

/-- Almost surely, `qform` is elliptic and `(a e₁·v)² ≤ Λ v·av`. -/
theorem ae_qform_bounds (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), ∀ v : Vec d,
      (sourceReducedBound Λ₀)⁻¹ * euclideanSq v ≤ qform w v ∧
        bform hd w v ^ 2 ≤ sourceReducedBound Λ₀ * qform w v := by
  have hΛ := sourceReducedBound_pos' Λ₀
  filter_upwards [ae_reduced_elliptic_zero Q] with w hw v
  obtain ⟨hsym, hell⟩ := hw
  set A := w.1 0 with hAdef
  set e := unitVector (firstCoordinateIndex hd) with hedef
  have hq := dot_mulVec_eq_qform hsym v
  have hnn : ∀ ξ : Vec d, 0 ≤ dot ξ (A.mulVec ξ) := fun ξ =>
    (mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg_fisher ξ)).trans (hell ξ).1
  refine ⟨hq ▸ (hell v).1, ?_⟩
  have hb : dot e (A.mulVec v) = bform hd w v := by
    rw [hedef, dot_unitVector_left']
    simp only [Matrix.mulVec, dotProduct, bform]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have := congrFun (congrFun hsym j) (firstCoordinateIndex hd)
    rw [Matrix.transpose_apply] at this
    exact this
  have hP : 0 < dot e (A.mulVec e) := by
    have h1 := (hell e).1
    rw [euclideanSq_unitVector', mul_one] at h1
    exact (inv_pos.mpr hΛ).trans_le h1
  have hPle : dot e (A.mulVec e) ≤ sourceReducedBound Λ₀ := by
    have h1 := (hell e).2
    rw [euclideanSq_unitVector', mul_one] at h1
    exact h1
  have hcs := sq_le_mul_of_quadratic_nonneg hP fun t => by
    rw [← dot_quad_expand A hsym e v t]
    exact hnn _
  have hqv : 0 ≤ qform w v := hq ▸ hnn v
  rw [hb, hq] at hcs
  calc bform hd w v ^ 2 ≤ dot e (A.mulVec e) * qform w v := hcs
    _ ≤ sourceReducedBound Λ₀ * qform w v := mul_le_mul_of_nonneg_right hPle hqv

/-! ## The chain rule for the regularized logarithm -/

/-- A weak horizontal gradient satisfies the identity against concrete horizontal tests. -/
theorem HasWeakHorizontalGradient.integral_test' {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {u : FieldPair d → ℝ} {V : FieldPair d → Vec d}
    (huV : HasWeakHorizontalGradient Q hQ u V) (i : Fin d) {K : FieldPair d → ℝ}
    (hK : IsHorizontalTest K) :
    (∫ ω, u ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, V ω i * K ω ∂Q) := by
  have key := huV.2.2 i ((hK.memLp Q 2).toLp K)
    ((hK.memLp_derivative Q 2 i).toLp (horizontalDerivative i K))
    (hK.isHorizontallySmoothTest Q hQ) (hK.hasHorizontalLpDerivative_toLp Q hQ i)
  have e1 : ∫ ω, u ω * ((hK.memLp_derivative Q 2 i).toLp (horizontalDerivative i K)) ω ∂Q =
      ∫ ω, u ω * horizontalDerivative i K ω ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [(hK.memLp_derivative Q 2 i).coeFn_toLp] with ω hω
    simp only [hω]
  have e2 : ∫ ω, V ω i * ((hK.memLp Q 2).toLp K) ω ∂Q = ∫ ω, V ω i * K ω ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [(hK.memLp Q 2).coeFn_toLp] with ω hω
    simp only [hω]
  rw [← e1, ← e2]
  exact key

/-- **The chain rule** for the regularized logarithm: `D g_ε(ρ) = k_ε(ρ) Dρ`. -/
theorem hasWeakHorizontalGradient_rlog {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ε : ℝ} (hε : 0 < ε) {ρ : FieldPair d → ℝ} {V : FieldPair d → Vec d}
    (hρm : Measurable ρ) (hρ : MemLp ρ 2 Q) (hVm : Measurable V)
    (hV : ∀ j, MemLp (fun w => V w j) 2 Q) (hρV : HasWeakHorizontalGradient Q hQ ρ V) :
    HasWeakHorizontalGradient Q hQ (fun w => rlog ε (ρ w))
      (fun w j => rlogDeriv ε (ρ w) * V w j) := by
  have hum : Measurable fun w => rlog ε (ρ w) := (measurable_rlog hε).comp hρm
  have hkm : Measurable fun w => rlogDeriv ε (ρ w) := (continuous_rlogDeriv hε).measurable.comp hρm
  have hkb : ∀ w, ‖rlogDeriv ε (ρ w)‖ ≤ ε⁻¹ := fun w => by
    rw [Real.norm_eq_abs, abs_of_pos (rlogDeriv_pos hε _)]
    exact rlogDeriv_le hε _
  have hρi : Integrable ρ Q := hρ.integrable one_le_two
  have hui : Integrable (fun w => rlog ε (ρ w)) Q := by
    refine Integrable.mono' ((hρi.abs.add (integrable_const 1)).const_mul ε⁻¹)
      hum.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_rlog_le hε _).trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hε.le))
    exact (abs_sub _ _).trans (by simp)
  refine ⟨hui, fun j => ((hV j).integrable one_le_two).bdd_mul hkm.aestronglyMeasurable
    (ae_of_all _ hkb), fun i F G hFs hG => ?_⟩
  have h := Calculus.integral_chain_smooth hQ (contDiff_rlog hε) (abs_deriv_rlog_le hε) hρm hρi
    ((measurable_pi_apply i).comp hVm) ((hV i).integrable one_le_two) i
    (fun K hK => HasWeakHorizontalGradient.integral_test' hρV i hK) hFs hG
  rw [deriv_rlog hε] at h
  exact h

/-! ## The entropy inequality -/

theorem memLp_two_of_abs_le_affine {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {ρ g : FieldPair d → ℝ} (hρ : MemLp ρ 2 Q) (hgm : Measurable g) {c : ℝ}
    (hg : ∀ w, |g w| ≤ c * (|ρ w| + 1)) : MemLp g 2 Q :=
  ((hρ.abs.add (memLp_const 1)).const_mul c).of_le hgm.aestronglyMeasurable
    (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      refine (hg w).trans (le_abs_self _) |>.trans_eq ?_
      simp)

theorem measurable_entry_sum_V (hd : 2 ≤ d) {V : FieldPair d → Vec d} (hVm : Measurable V) :
    Measurable fun w : FieldPair d => bform hd w (V w) := by
  unfold bform
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j
    (firstCoordinateIndex hd)).measurable.mul ((measurable_pi_apply j).comp hVm)

/-- Pointwise Young: `λ ρ k b ≤ ¼ k q + Λ λ² ρ` when `b² ≤ Λ q`, `q ≥ 0`, `ρ ≥ 0`. -/
theorem young_rlog {ε Λ lam r q b : ℝ} (hε : 0 < ε) (hΛ : 0 ≤ Λ) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hb : b ^ 2 ≤ Λ * q) :
    lam * (r * rlogDeriv ε r * b) ≤ (1 / 4) * (rlogDeriv ε r * q) + Λ * lam ^ 2 * r := by
  have hk := (rlogDeriv_pos hε r).le
  set k := rlogDeriv ε r with hkdef
  set X := lam * r * b with hXdef
  set Y := lam ^ 2 * r ^ 2 * Λ with hYdef
  have hY : 0 ≤ Y := by positivity
  have hX2 : X ^ 2 ≤ Y * q := by
    have : X ^ 2 = lam ^ 2 * r ^ 2 * b ^ 2 := by rw [hXdef]; ring
    rw [this, hYdef, mul_assoc (lam ^ 2 * r ^ 2) Λ q]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hXle : X ≤ (1 / 4) * q + Y := by nlinarith [sq_nonneg ((1 / 4) * q - Y)]
  have hrk := sq_mul_rlogDeriv_le hε hr
  calc lam * (r * k * b) = k * X := by rw [hXdef]; ring
    _ ≤ k * ((1 / 4) * q + Y) := mul_le_mul_of_nonneg_left hXle hk
    _ = (1 / 4) * (k * q) + Λ * lam ^ 2 * (r ^ 2 * k) := by rw [hYdef]; ring
    _ ≤ (1 / 4) * (k * q) + Λ * lam ^ 2 * r := by
        have : 0 ≤ Λ * lam ^ 2 := by positivity
        linarith [mul_le_mul_of_nonneg_left hrk this]

/-- **The entropy step**: for an `H¹` solution `ρ ≥ 0` of `μρ - L*ρ = μρ'`,
`¼ E[k_ε(ρ) Dρ·aDρ] ≤ μ (E Φ_ε(ρ') - E Φ_ε(ρ)) + Λ λ² E[ρ]`. -/
theorem entropy_step (hd : 2 ≤ d) (lam : ℝ) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {μ0 : ℝ} (hμ0 : 0 ≤ μ0)
    {ρ ρp : FieldPair d → ℝ} (hρm : Measurable ρ) (hρ : MemLp ρ 2 (Carriers.reducedReferenceLaw Q))
    (hρ0 : ∀ w, 0 ≤ ρ w) (hρpm : Measurable ρp)
    (hρp : MemLp ρp 2 (Carriers.reducedReferenceLaw Q))
    {K : ℝ} (hK : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), ∀ x j k, |w.1 x j k| ≤ K)
    {V : FieldPair d → Vec d} (hVm : Measurable V)
    (hV : ∀ j, MemLp (fun w => V w j) 2 (Carriers.reducedReferenceLaw Q))
    (hρV : HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ ρ V)
    (hweak : ∀ (u : FieldPair d → ℝ) (G : FieldPair d → Vec d), Measurable u →
        MemLp u 2 (Carriers.reducedReferenceLaw Q) → Measurable G →
        (∀ j, MemLp (fun w => G w j) 2 (Carriers.reducedReferenceLaw Q)) →
        HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ u G →
        μ0 * (∫ w, ρ w * u w ∂(Carriers.reducedReferenceLaw Q)) +
            (1 / 2 : ℝ) * ∑ k, (∫ w, V w k * ∑ j, w.1 0 j k * G w j
              ∂(Carriers.reducedReferenceLaw Q)) -
            lam * (∫ w, ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * G w j
              ∂(Carriers.reducedReferenceLaw Q)) =
          ∫ w, (μ0 * ρp w) * u w ∂(Carriers.reducedReferenceLaw Q))
    {ε : ℝ} (hε : 0 < ε) :
    (1 / 4 : ℝ) * ∫ w, rlogDeriv ε (ρ w) * qform w (V w) ∂(Carriers.reducedReferenceLaw Q) ≤
      μ0 * ((∫ w, rent ε (ρp w) ∂(Carriers.reducedReferenceLaw Q)) -
          ∫ w, rent ε (ρ w) ∂(Carriers.reducedReferenceLaw Q)) +
        sourceReducedBound Λ₀ * lam ^ 2 * ∫ w, ρ w ∂(Carriers.reducedReferenceLaw Q) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    reducedReferenceLaw_isProbabilityMeasure Q
  have hqb := ae_qform_bounds hd Q
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  set Λ := sourceReducedBound Λ₀ with hΛdef
  have hΛ : 0 < Λ := sourceReducedBound_pos' Λ₀
  -- The test pair `(g_ε(ρ), k_ε(ρ) V)`.
  set u : FieldPair d → ℝ := fun w => rlog ε (ρ w) with hudef
  set k : FieldPair d → ℝ := fun w => rlogDeriv ε (ρ w) with hkdef
  set G : FieldPair d → Vec d := fun w j => k w * V w j with hGdef
  have hum : Measurable u := (measurable_rlog hε).comp hρm
  have hkm : Measurable k := (continuous_rlogDeriv hε).measurable.comp hρm
  have hkb : ∀ w, ‖k w‖ ≤ ε⁻¹ := fun w => by
    rw [Real.norm_eq_abs, abs_of_pos (rlogDeriv_pos hε _)]
    exact rlogDeriv_le hε _
  have hk0 : ∀ w, 0 ≤ k w := fun w => (rlogDeriv_pos hε _).le
  have hu : MemLp u 2 μ := memLp_two_of_abs_le_affine hρ hum fun w =>
    (abs_rlog_le hε _).trans (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by simp))
      (inv_nonneg.mpr hε.le))
  have hGm : Measurable G := measurable_pi_lambda _ fun j =>
    hkm.mul ((measurable_pi_apply j).comp hVm)
  have hG : ∀ j, MemLp (fun w => G w j) 2 μ := fun j =>
    ((hV j).const_mul ε⁻¹).of_le (hkm.mul ((measurable_pi_apply j).comp hVm)).aestronglyMeasurable
      (ae_of_all _ fun w => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hε)]
        exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hkb w) (abs_nonneg _))
  have huG : HasWeakHorizontalGradient μ hQ u G :=
    hasWeakHorizontalGradient_rlog hQ hε hρm hρ hVm hV hρV
  have hE := hweak u G hum hu hGm hG huG
  -- Rewriting the flux and drift terms.
  have hsumV : ∀ k', MemLp (fun w => ∑ j, w.1 0 j k' * V w j) 2 μ := fun k' =>
    memLp_entry_sum hK hV k'
  have hqi : Integrable (fun w => qform w (V w)) μ := by
    unfold qform
    exact integrable_finset_sum _ fun k' _ => (hV k').integrable_mul (hsumV k')
  have hkqi : Integrable (fun w => k w * qform w (V w)) μ :=
    hqi.bdd_mul hkm.aestronglyMeasurable (ae_of_all _ hkb)
  have hT1 : ∑ k', (∫ w, V w k' * ∑ j, w.1 0 j k' * G w j ∂μ) = ∫ w, k w * qform w (V w) ∂μ := by
    have hint : ∀ k', Integrable (fun w => V w k' * ∑ j, w.1 0 j k' * G w j) μ := fun k' =>
      (hV k').integrable_mul (memLp_entry_sum hK hG k')
    rw [← integral_finset_sum _ fun k' _ => hint k']
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [hGdef, qform, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun j _ => by ring
  have hbi : MemLp (fun w => bform hd w (V w)) 2 μ := memLp_entry_sum hK hV _
  have hT2 : ∫ w, ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * G w j ∂μ =
      ∫ w, ρ w * k w * bform hd w (V w) ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [hGdef, bform, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hT1, hT2] at hE
  -- Integrability of the remaining terms.
  have hρu : Integrable (fun w => ρ w * u w) μ := hρ.integrable_mul hu
  have hρpu : Integrable (fun w => ρp w * u w) μ := hρp.integrable_mul hu
  have hρkb : Integrable (fun w => ρ w * k w * bform hd w (V w)) μ := by
    have h1 : MemLp (fun w => k w * bform hd w (V w)) 2 μ :=
      (hbi.const_mul ε⁻¹).of_le (hkm.mul (measurable_entry_sum_V hd hVm)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hε)]
          exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hkb w)
            (abs_nonneg _))
    exact (hρ.integrable_mul h1).congr (ae_of_all _ fun w => by simp only [Pi.mul_apply]; ring)
  have hρ2 : Integrable (fun w => ρ w ^ 2) μ := (memLp_two_iff_integrable_sq hρ.1).mp hρ
  have hρp2 : Integrable (fun w => ρp w ^ 2) μ := (memLp_two_iff_integrable_sq hρp.1).mp hρp
  have hrent : ∀ {f : FieldPair d → ℝ}, Measurable f → Integrable (fun w => f w ^ 2) μ →
      Integrable (fun w => rent ε (f w)) μ := fun {f} hfm hf2 => by
    refine Integrable.mono' (((hf2.add (integrable_const 1)).const_mul (2 * ε⁻¹)))
      ((measurable_rent hε).comp hfm).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (rent_nonneg hε _)]
    refine (rent_le hε _).trans ?_
    have h1 : (f w - 1) ^ 2 ≤ 2 * (f w ^ 2 + 1) := by nlinarith [sq_nonneg (f w + 1)]
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hε.le)
    show ε⁻¹ * (f w - 1) ^ 2 ≤ 2 * ε⁻¹ * (f w ^ 2 + 1)
    linarith
  have hrρ := hrent hρm hρ2
  have hrρp := hrent hρpm hρp2
  have hρi : Integrable ρ μ := hρ.integrable one_le_two
  -- The convexity bound.
  have hA : ∫ w, (μ0 * ρp w) * u w ∂μ - μ0 * ∫ w, ρ w * u w ∂μ ≤
      μ0 * ((∫ w, rent ε (ρp w) ∂μ) - ∫ w, rent ε (ρ w) ∂μ) := by
    have e1 : ∫ w, (μ0 * ρp w) * u w ∂μ = μ0 * ∫ w, ρp w * u w ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun w => by ring)
    rw [e1, ← mul_sub, ← integral_sub hρpu hρu, ← integral_sub hrρp hrρ]
    refine mul_le_mul_of_nonneg_left (integral_mono (hρpu.sub hρu) (hrρp.sub hrρ) fun w => ?_) hμ0
    have := rent_sub_ge hε (ρp w) (ρ w)
    simp only [hudef]
    linarith
  -- The Young bound.
  have hB : lam * ∫ w, ρ w * k w * bform hd w (V w) ∂μ ≤
      (1 / 4) * (∫ w, k w * qform w (V w) ∂μ) + Λ * lam ^ 2 * ∫ w, ρ w ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hkqi.const_mul _) (hρi.const_mul _)]
    refine integral_mono_ae (hρkb.const_mul _) ((hkqi.const_mul _).add (hρi.const_mul _)) ?_
    filter_upwards [hqb] with w hw
    obtain ⟨hlow, hbq⟩ := hw (V w)
    have hq0 : 0 ≤ qform w (V w) :=
      (mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg_fisher _)).trans hlow
    have := young_rlog (lam := lam) hε hΛ.le (hρ0 w) hq0 hbq
    simpa only [hkdef] using this
  linarith

end EinsteinRelation.Entropy
