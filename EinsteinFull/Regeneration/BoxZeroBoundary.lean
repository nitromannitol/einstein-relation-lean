import EinsteinFull.Regeneration.BoxCutoff
import EinsteinFull.Regeneration.ZeroBoundaryCutoffLimit
import PDEFoundation.Measure.LpPower
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Zero-boundary criterion for coordinate boxes

Normalized face-collar mass controls the derivative cost of smooth box
cutoffs, giving a zero-boundary Sobolev representative.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The two width-`ε` collars normal to one coordinate. -/
def boxFaceCollars {d : ℕ} (a b : PDE.Vec d) (i : Fin d) (ε : ℝ) : Set (PDE.Vec d) :=
  {x | x i ≤ a i + ε ∨ b i - ε ≤ x i}

/-- Face collars are measurable. -/
theorem measurableSet_boxFaceCollars {d : ℕ} (a b : PDE.Vec d) (i : Fin d) (ε : ℝ) :
    MeasurableSet (boxFaceCollars a b i ε) := by
  exact (measurableSet_le (measurable_pi_apply i) measurable_const).union
    (measurableSet_le measurable_const (measurable_pi_apply i))

/-- Vanishing normalized mass on all face collars gives zero Sobolev boundary values. -/
theorem memH10_of_box_face_collars {d : ℕ} (a b : PDE.Vec d)
    (hQ : PDE.IsOpenBoundedConvexDomain (PDE.axisBox a b))
    (u : PDE.H1Function (PDE.axisBox a b)) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ k, 0 < ε k)
    (hcollar : ∀ i : Fin d, Tendsto (fun k =>
      (∫ x in boxFaceCollars a b i (ε k), u x ^ 2 ∂(PDE.volumeOn (PDE.axisBox a b))) /
        (ε k) ^ 2) atTop (𝓝 0)) : PDE.MemH10 (PDE.axisBox a b) u.toFun := by
  let Q := PDE.axisBox a b
  let widths : ℕ → PDE.Vec d := fun k _ => ε k
  let inner : ℕ → Set (PDE.Vec d) := fun k => boxCutoffInset a b (widths k)
  let outer : ℕ → Set (PDE.Vec d) := fun _ => Q
  let C : ℕ → ℝ := fun k => ∑ i : Fin d, 32 / widths k i
  let η : ∀ k, PDE.QuantitativeSmoothCutoff (inner k) (outer k) (C k) :=
    fun k => quantitativeBoxCutoff a b (widths k) (fun _ => hεpos k)
  have hη : ∀ᵐ x ∂(PDE.volumeOn Q), Tendsto (fun k => η k x) atTop (𝓝 1) := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with x hx
    have hall : ∀ j : Fin d, ∀ᶠ k in atTop,
        ε k < min (x j - a j) (b j - x j) := by
      intro j
      have hj := hx j (Set.mem_univ j)
      have hp : 0 < min (x j - a j) (b j - x j) := by
        apply lt_min <;> linarith [hj.1, hj.2]
      exact hε.eventually_lt_const hp
    have hevent : ∀ᶠ k in atTop, η k x = 1 := by
      filter_upwards [Filter.eventually_all.2 hall] with k hk
      apply (η k).eq_one_on_inner
      intro j _
      have hj := hk j
      change a j + ε k ≤ x j ∧ x j ≤ b j - ε k
      have h1 := (lt_min_iff.mp hj).1
      have h2 := (lt_min_iff.mp hj).2
      constructor <;> linarith
    have hevent' : (fun k => η k x) =ᶠ[atTop] (fun _ => (1 : ℝ)) := hevent
    exact tendsto_const_nhds.congr' hevent'.symm
  apply memH10_of_cutoff_gradient_tendsto_zero hQ u inner outer C η (fun _ => subset_rfl) hη
  intro i
  apply PDE.tendsto_eLpNorm_two_zero_of_tendsto_integral_sq
  · intro k
    have hηcont : Continuous (fun x => PDE.classicalGradient (η k).toFun x i) := by
      exact (continuous_apply i).comp
        (PDE.ContDiff.continuous_classicalGradient ((η k).smooth.of_le (by norm_num)))
    apply (u.memL2).of_le_mul (c := 32 / ε k)
      (u.memL2.aestronglyMeasurable.mul hηcont.aestronglyMeasurable)
    filter_upwards with x
    change ‖u x * PDE.classicalGradient (η k).toFun x i‖ ≤ (32 / ε k) * ‖u x‖
    simp only [norm_mul, Real.norm_eq_abs]
    have hb := boxCutoff_gradient_coord_le (a := a) (b := b) (δ := widths k)
      (fun _ => hεpos k) i x
    change |PDE.classicalGradient (η k).toFun x i| ≤ 32 / ε k at hb
    nlinarith [mul_le_mul_of_nonneg_left hb (abs_nonneg (u x))]
  · have hbound : Tendsto (fun k => 1024 *
        ((∫ x in boxFaceCollars a b i (ε k), u x ^ 2 ∂(PDE.volumeOn Q)) / (ε k) ^ 2))
        atTop (𝓝 0) := by simpa using (hcollar i).const_mul 1024
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun k => integral_nonneg fun _ => sq_nonneg _) ?_
    intro k
    let S := boxFaceCollars a b i (ε k)
    have hS : MeasurableSet S := measurableSet_boxFaceCollars a b i (ε k)
    have hηcont : Continuous (fun x => PDE.classicalGradient (η k).toFun x i) := by
      exact (continuous_apply i).comp
        (PDE.ContDiff.continuous_classicalGradient ((η k).smooth.of_le (by norm_num)))
    have hmem : MemLp (fun x => u x * PDE.classicalGradient (η k).toFun x i)
        2 (PDE.volumeOn Q) := by
      apply (u.memL2).of_le_mul (c := 32 / ε k)
        (u.memL2.aestronglyMeasurable.mul hηcont.aestronglyMeasurable)
      filter_upwards with x
      change ‖u x * PDE.classicalGradient (η k).toFun x i‖ ≤ (32 / ε k) * ‖u x‖
      simp only [norm_mul, Real.norm_eq_abs]
      have hb := boxCutoff_gradient_coord_le (a := a) (b := b) (δ := widths k)
        (fun _ => hεpos k) i x
      change |PDE.classicalGradient (η k).toFun x i| ≤ 32 / ε k at hb
      nlinarith [mul_le_mul_of_nonneg_left hb (abs_nonneg (u x))]
    have hright : Integrable (S.indicator (fun x => (32 / ε k) ^ 2 * u x ^ 2))
        (PDE.volumeOn Q) := (u.memL2.integrable_sq.const_mul _).indicator hS
    have hpoint : ∀ᵐ x ∂(PDE.volumeOn Q),
        (u x * PDE.classicalGradient (η k).toFun x i) ^ 2 ≤
          S.indicator (fun x => (32 / ε k) ^ 2 * u x ^ 2) x := by
      filter_upwards with x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        have hb := boxCutoff_gradient_coord_le (a := a) (b := b) (δ := widths k)
          (fun _ => hεpos k) i x
        change |PDE.classicalGradient (η k).toFun x i| ≤ 32 / ε k at hb
        have hs : (PDE.classicalGradient (η k).toFun x i) ^ 2 ≤ (32 / ε k) ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
        nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (u x))]
      · rw [indicator_of_notMem hx]
        have hx' : a i + ε k < x i ∧ x i < b i - ε k := by
          simpa only [S, boxFaceCollars, mem_ofPred_eq, not_or, not_le] using hx
        have hz := boxCutoff_gradient_coord_eq_zero_of_interior (a := a) (b := b)
          (δ := widths k) (fun _ => hεpos k) i x hx'
        change PDE.classicalGradient (η k).toFun x i = 0 at hz
        rw [hz]
        simp
    have hcompare := integral_mono_ae hmem.integrable_sq hright hpoint
    rw [integral_indicator hS, integral_const_mul] at hcompare
    calc
      _ ≤ (32 / ε k) ^ 2 * (∫ x in S, u x ^ 2 ∂(PDE.volumeOn Q)) := hcompare
      _ = _ := by field_simp [ne_of_gt (hεpos k)]; ring

end EinsteinFull.Regeneration
