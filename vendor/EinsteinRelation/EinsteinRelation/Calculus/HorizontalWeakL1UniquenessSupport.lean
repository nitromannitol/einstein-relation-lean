import EinsteinRelation.Calculus.HorizontalWeakL1Support
import EinsteinRelation.Correctors.HorizontalCoreLpDensity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Filter

noncomputable section

namespace EinsteinRelation

private theorem integrable_horizontalScalarMollifier {d : ℕ} {F : FieldPair d → ℝ}
    (hF : Measurable F) (hFb : ∀ ω, |F ω| ≤ 1) (ε : ℝ) (ω : FieldPair d) :
    Integrable (fun x : Vec d => mollifier d x * F (translate (ε • x) ω)) := by
  have hbase : Integrable (mollifier d) (volume : Measure (Vec d)) :=
    (contDiff_mollifier d).continuous.integrable_of_hasCompactSupport (hasCompactSupport_mollifier d)
  have hshift : Measurable (fun x : Vec d => translate (ε • x) ω) := by
    have hmap : Continuous (fun x : Vec d => (ε • x, ω)) :=
      (continuous_id.const_smul ε).prodMk (continuous_const : Continuous fun _ : Vec d => ω)
    exact (Probability.continuous_translate.comp hmap).measurable
  have hFm : Measurable (fun x : Vec d => F (translate (ε • x) ω)) := hF.comp hshift
  refine Integrable.mono' hbase ?_ ?_
  · exact ((contDiff_mollifier d).continuous.measurable.mul hFm).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg d x)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hFb (translate (ε • x) ω)) (mollifier_nonneg d x)

private theorem abs_horizontalScalarMollifier_le_one {d : ℕ} {F : FieldPair d → ℝ}
    (hF : Measurable F) (hFb : ∀ ω, |F ω| ≤ 1) (ε : ℝ) (ω : FieldPair d) :
    |∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)| ≤ 1 := by
  have hbase : Integrable (mollifier d) (volume : Measure (Vec d)) :=
    (contDiff_mollifier d).continuous.integrable_of_hasCompactSupport (hasCompactSupport_mollifier d)
  have hI := integrable_horizontalScalarMollifier hF hFb ε ω
  have hbd : ∀ x : Vec d,
      ‖mollifier d x * F (translate (ε • x) ω)‖ ≤ mollifier d x := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg d x)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hFb (translate (ε • x) ω)) (mollifier_nonneg d x)
  calc
    |∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)| =
        ‖∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x : Vec d, ‖mollifier d x * F (translate (ε • x) ω)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : Vec d, mollifier d x := integral_mono hI.norm hbase hbd
    _ = 1 := integral_mollifier d

/-- Bounded smooth orbit tests separate scalar `L¹(Q)` classes on a stationary probability
measure. The proof smooths the measurable sign representative, extracts an almost everywhere
convergent subsequence from the actual `L²` mollifier approximation, and uses the `L¹` norm as the
dominating function. -/
theorem eq_zero_of_horizontalCore_pairing_eq_zero_l1 {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (g : Lp ℝ 1 Q)
    (hg : ∀ H : FieldPair d → ℝ, IsHorizontalTest H →
      (∫ ω, g ω * H ω ∂Q) = 0) :
    g = 0 := by
  let hag := (Lp.memLp g).aestronglyMeasurable
  let gr : FieldPair d → ℝ := hag.mk g
  have hgrm : Measurable gr := hag.measurable_mk
  have hgr : (fun ω => g ω) =ᵐ[Q] gr := hag.ae_eq_mk
  let φ : FieldPair d → ℝ := fun ω => if gr ω < 0 then -1 else 1
  have hφm : Measurable φ :=
    Measurable.ite (measurableSet_lt hgrm measurable_const) measurable_const measurable_const
  have hφb : ∀ ω, |φ ω| ≤ 1 := by
    intro ω
    dsimp [φ]
    split_ifs <;> norm_num
  have hφLp : MemLp φ 2 Q :=
    MemLp.of_bound hφm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hφb)
  obtain ⟨hS, hS_lim⟩ := Correctors.exists_scalarMollifier_Lp_approximation
    Q hQ hφm ⟨1, hφb⟩ hφLp
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let S : ℕ → Lp ℝ 2 Q := fun n =>
    (hS (ε n)).toLp (fun ω => ∫ x : Vec d, mollifier d x * φ (translate (ε n • x) ω))
  have hε : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hS_tendsto : Tendsto S atTop (nhds (hφLp.toLp φ)) := by
    exact hS_lim.comp hε
  have hS_measure : TendstoInMeasure Q (fun n => S n) atTop (hφLp.toLp φ) :=
    tendstoInMeasure_of_tendsto_Lp hS_tendsto
  obtain ⟨ns, _hnsMono, hS_ae⟩ := hS_measure.exists_seq_tendsto_ae
  have hφ_toLp : (hφLp.toLp φ : Lp ℝ 2 Q) =ᵐ[Q] φ := hφLp.coeFn_toLp
  have hS_ae' : ∀ᵐ ω ∂Q,
      Tendsto (fun n => S (ns n) ω) atTop (nhds (φ ω)) := by
    filter_upwards [hS_ae, hφ_toLp] with ω hω hωφ
    simpa only [hωφ] using hω
  have hrep : ∀ n, (S n : FieldPair d → ℝ) =ᵐ[Q]
      (fun ω => ∫ x : Vec d, mollifier d x * φ (translate (ε n • x) ω)) :=
    fun n => (hS (ε n)).coeFn_toLp
  have hbound : ∀ n ω,
      |∫ x : Vec d, mollifier d x * φ (translate (ε n • x) ω)| ≤ 1 :=
    fun n ω => abs_horizontalScalarMollifier_le_one hφm hφb (ε n) ω
  have htest : ∀ n, IsHorizontalTest
      (fun ω => ∫ x : Vec d, mollifier d x * φ (translate (ε n • x) ω)) := by
    intro n
    exact Correctors.isHorizontalTest_scaled_mollifier hφm ⟨1, hφb⟩ (ε n) (by positivity)
  have hpair : ∀ n,
      (∫ ω, g ω * (∫ x : Vec d, mollifier d x * φ (translate (ε (ns n) • x) ω)) ∂Q) = 0 := by
    intro n
    exact hg _ (htest (ns n))
  let P : ℕ → FieldPair d → ℝ := fun n ω => g ω * S (ns n) ω
  have hP_meas : ∀ n, AEStronglyMeasurable (P n) Q := by
    intro n
    exact (Lp.memLp g).aestronglyMeasurable.mul (Lp.aestronglyMeasurable (S (ns n)))
  have hP_bound : ∀ n, ∀ᵐ ω ∂Q, ‖P n ω‖ ≤ ‖g ω‖ := by
    intro n
    filter_upwards [hrep (ns n)] with ω hω
    dsimp [P]
    calc
      ‖g ω * S (ns n) ω‖ = ‖g ω‖ * ‖S (ns n) ω‖ := norm_mul _ _
      _ = ‖g ω‖ * |S (ns n) ω| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ = ‖g ω‖ * |∫ x : Vec d, mollifier d x * φ (translate (ε (ns n) • x) ω)| := by
        rw [hω]
      _ ≤ ‖g ω‖ * 1 :=
        mul_le_mul_of_nonneg_left (hbound (ns n) ω) (norm_nonneg _)
      _ = ‖g ω‖ := mul_one _
  have hgInt : Integrable (fun ω => g ω) Q :=
    (Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 1)
  have hP_lim : ∀ᵐ ω ∂Q, Tendsto (fun n => P n ω) atTop (nhds (g ω * φ ω)) := by
    filter_upwards [hS_ae'] with ω hω
    simpa only [P] using (hω).const_mul (g ω)
  have hIntegral_lim : Tendsto (fun n => ∫ ω, P n ω ∂Q) atTop
      (nhds (∫ ω, g ω * φ ω ∂Q)) :=
    tendsto_integral_filter_of_dominated_convergence (fun ω => ‖g ω‖)
      (Filter.Eventually.of_forall hP_meas) (Filter.Eventually.of_forall hP_bound)
      hgInt.norm hP_lim
  have hIntegral_zero : ∀ n, (∫ ω, P n ω ∂Q) = 0 := by
    intro n
    calc
      (∫ ω, P n ω ∂Q) =
          ∫ ω, g ω * (∫ x : Vec d, mollifier d x * φ (translate (ε (ns n) • x) ω)) ∂Q := by
            apply integral_congr_ae
            filter_upwards [hrep (ns n)] with ω hω
            dsimp [P]
            rw [hω]
      _ = 0 := hpair n
  have hIntegral_zero_lim : Tendsto (fun n => ∫ ω, P n ω ∂Q) atTop (nhds 0) := by
    simpa only [hIntegral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hprod_zero : (∫ ω, g ω * φ ω ∂Q) = 0 :=
    tendsto_nhds_unique hIntegral_lim hIntegral_zero_lim
  have hprod_abs : (fun ω => g ω * φ ω) =ᵐ[Q] fun ω => |g ω| := by
    filter_upwards [hgr] with ω hω
    dsimp [φ]
    rw [hω]
    by_cases hneg : gr ω < 0
    · simp [hneg, abs_of_neg hneg]
    · simp [hneg, abs_of_nonneg (le_of_not_gt hneg)]
  have habs_zero : (∫ ω, |g ω| ∂Q) = 0 := by
    calc
      (∫ ω, |g ω| ∂Q) = ∫ ω, g ω * φ ω ∂Q := (integral_congr_ae hprod_abs).symm
      _ = 0 := hprod_zero
  have habs_nonneg : 0 ≤ᵐ[Q] fun ω => |g ω| := Filter.Eventually.of_forall fun _ => abs_nonneg _
  have habs_ae_zero : (fun ω => |g ω|) =ᵐ[Q] fun _ => (0 : ℝ) :=
    (integral_eq_zero_iff_of_nonneg_ae habs_nonneg hgInt.norm).mp habs_zero
  have hg_ae_zero : (fun ω => g ω) =ᵐ[Q] fun _ => (0 : ℝ) :=
    habs_ae_zero.mono fun ω hω => abs_eq_zero.mp hω
  exact Lp.ext (hg_ae_zero.trans (Lp.coeFn_zero ℝ 1 Q).symm)

private theorem weakHorizontalL1_pairing_eq_of_two {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {f : Lp ℝ 1 Q}
    {G H : Lp (EuclideanSpace ℝ (Fin d)) 1 Q}
    (hG : HasWeakHorizontalL1Gradient Q f G) (hH : HasWeakHorizontalL1Gradient Q f H)
    (i : Fin d) (ψ : FieldPair d → ℝ) (hψ : IsHorizontalTest ψ) :
    (∫ ω, (G ω i - H ω i) * ψ ω ∂Q) = 0 := by
  obtain ⟨_, hGint, hGweak⟩ := hG i ψ hψ
  obtain ⟨_, hHint, hHweak⟩ := hH i ψ hψ
  have hpair : (∫ ω, G ω i * ψ ω ∂Q) = ∫ ω, H ω i * ψ ω ∂Q := by
    linarith [hGweak, hHweak]
  have hfun : (fun ω => (G ω i - H ω i) * ψ ω) =
      fun ω => G ω i * ψ ω - H ω i * ψ ω := by
    funext ω
    ring
  calc
    (∫ ω, (G ω i - H ω i) * ψ ω ∂Q) =
        ∫ ω, (G ω i * ψ ω - H ω i * ψ ω) ∂Q := by rw [hfun]
    _ = (∫ ω, G ω i * ψ ω ∂Q) - ∫ ω, H ω i * ψ ω ∂Q := integral_sub hGint hHint
    _ = 0 := by rw [hpair, sub_self]

/-- Two weak horizontal `L¹` gradients of the same scalar class agree as Euclidean `L¹` classes.
The argument uses the actual bounded smooth orbit tests and (L¹) separation; it adds no
integrability or regularity assumptions to the scalar or either vector field. -/
theorem HasWeakHorizontalL1Gradient.unique {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {f : Lp ℝ 1 Q}
    {G H : Lp (EuclideanSpace ℝ (Fin d)) 1 Q}
    (hG : HasWeakHorizontalL1Gradient Q f G) (hH : HasWeakHorizontalL1Gradient Q f H) :
    G = H := by
  have hcoord : ∀ i : Fin d, (fun ω => G ω i) =ᵐ[Q] fun ω => H ω i := by
    intro i
    let π : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj i
    let gi : Lp ℝ 1 Q := π.compLpL 1 Q (G - H)
    have hgi : (gi : FieldPair d → ℝ) =ᵐ[Q] fun ω => G ω i - H ω i := by
      filter_upwards [π.coeFn_compLpL (G - H), Lp.coeFn_sub G H] with ω hω hsub
      calc
        gi ω = π ((G - H) ω) := by simpa only [gi, ContinuousLinearMap.coeFn_compLpL] using hω
        _ = π (G ω - H ω) := by
          rw [hsub]
          simp only [Pi.sub_apply]
        _ = G ω i - H ω i := by simp [π, PiLp.proj_apply]
    have hgiTest : ∀ ψ : FieldPair d → ℝ, IsHorizontalTest ψ →
        (∫ ω, gi ω * ψ ω ∂Q) = 0 := by
      intro ψ hψ
      calc
        (∫ ω, gi ω * ψ ω ∂Q) = ∫ ω, (G ω i - H ω i) * ψ ω ∂Q := by
          apply integral_congr_ae
          filter_upwards [hgi] with ω hω
          rw [hω]
        _ = 0 := weakHorizontalL1_pairing_eq_of_two hG hH i ψ hψ
    have hgi0 : gi = 0 := eq_zero_of_horizontalCore_pairing_eq_zero_l1 Q hQ gi hgiTest
    have hgi0fun : (gi : FieldPair d → ℝ) =ᵐ[Q] fun _ => (0 : ℝ) := by
      filter_upwards [Lp.coeFn_zero ℝ 1 Q] with ω hω0
      calc
        gi ω = (0 : Lp ℝ 1 Q) ω := congrArg (fun z : Lp ℝ 1 Q => z ω) hgi0
        _ = 0 := hω0
    filter_upwards [hgi, hgi0fun] with ω hω hω0
    have hdiff : G ω i - H ω i = 0 := by rw [← hω, hω0]
    exact sub_eq_zero.mp hdiff
  apply Lp.ext
  filter_upwards [ae_all_iff.2 hcoord] with ω hω
  ext i
  exact hω i

end EinsteinRelation
