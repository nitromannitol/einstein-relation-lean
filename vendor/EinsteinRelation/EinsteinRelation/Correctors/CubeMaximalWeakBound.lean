import EinsteinRelation.Environment.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A deterministic weak maximal estimate for coordinate cubes

Source: `paper/main.tex:693-698`. A disjoint Vitali subfamily controls
all bad centers by fourfold dilations. The coordinate-cube bound is an
internal tool for proving sublinearity with the manuscript's Euclidean norm.
-/

open MeasureTheory Set
noncomputable section
namespace EinsteinRelation.Correctors

/-- The weak maximal estimate follows from Vitali covering and the exact
Lebesgue scaling of coordinate cubes, without a stochastic input. -/
theorem exists_cube_maximal_weak_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Vec d → ℝ), Integrable f volume →
      (∀ x, 0 ≤ f x) → ∀ (S t : ℝ), 0 < S → 0 < t →
      volume {x : Vec d | ∃ r : ℝ, 0 < r ∧ r ≤ S ∧
        t * volume.real (Metric.closedBall x r) < ∫ y in Metric.closedBall x r, f y} ≤
      ENNReal.ofReal (C / t * ∫ x, f x) := by
  classical
  let C : ℝ := 4 ^ d
  have hC : 0 < C := pow_pos (by norm_num) _
  refine ⟨C, hC, ?_⟩
  intro f hfi hf S t _ ht
  let T : Set (Vec d × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ S ∧
    t * volume.real (Metric.closedBall p.1 p.2) < ∫ y in Metric.closedBall p.1 p.2, f y}
  obtain ⟨u, hu, hd, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T Prod.fst Prod.snd
      S (fun p hp => hp.2.1) 4 (by norm_num)
  have hcount : u.Countable := hd.countable_of_nonempty_interior fun p hp =>
    (Metric.nonempty_ball.mpr (hu hp).1).mono Metric.ball_subset_interior_closedBall
  letI : Countable u := hcount.to_subtype
  let B : u → Set (Vec d) := fun p => Metric.closedBall p.1.1 p.1.2
  let B4 : u → Set (Vec d) := fun p => Metric.closedBall p.1.1 (4 * p.1.2)
  have hdisj : Pairwise (fun p q : u => Disjoint (B p) (B q)) := by
    intro p q hpq
    exact hd p.2 q.2 (Subtype.coe_ne_coe.mpr hpq)
  have hsub : {x : Vec d | ∃ r : ℝ, 0 < r ∧ r ≤ S ∧
      t * volume.real (Metric.closedBall x r) < ∫ y in Metric.closedBall x r, f y} ⊆
      ⋃ p : u, B4 p := by
    rintro x ⟨r, hr, hSr, hbad⟩
    obtain ⟨p, hp, hcov⟩ := hcover (x, r) ⟨hr, hSr, hbad⟩
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hcov (Metric.mem_closedBall_self hr.le)⟩
  have hvol (p : u) : volume (B4 p) = ENNReal.ofReal C * volume (B p) := by
    have hr : 0 ≤ p.1.2 := (hu p.2).1.le
    dsimp only [B4, B]
    rw [Real.volume_pi_closedBall _ (mul_nonneg (by norm_num) hr),
      Real.volume_pi_closedBall _ hr]
    simp only [Fintype.card_fin]
    rw [← ENNReal.ofReal_mul hC.le]
    congr 1
    dsimp only [C]
    rw [← mul_pow]
    congr 1
    ring
  have hb (p : u) : volume (B p) ≤ ENNReal.ofReal t⁻¹ *
      ∫⁻ x in B p, ENNReal.ofReal (f x) := by
    have hreal : volume.real (B p) ≤ (∫ x in B p, f x) / t :=
      (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using (hu p.2).2.2.le)
    have hbound := ENNReal.ofReal_le_ofReal hreal
    change ENNReal.ofReal ((volume (B p)).toReal) ≤ _ at hbound
    rw [ENNReal.ofReal_toReal (isCompact_closedBall _ _).measure_ne_top,
      div_eq_mul_inv, mul_comm (∫ x in B p, f x),
      ENNReal.ofReal_mul (inv_nonneg.mpr ht.le),
      ofReal_integral_eq_lintegral_ofReal (hfi.integrableOn) (ae_of_all _ hf)] at hbound
    exact hbound
  have hb4 (p : u) : volume (B4 p) ≤ ENNReal.ofReal (C / t) *
      ∫⁻ x in B p, ENNReal.ofReal (f x) := by
    rw [hvol]
    calc
      ENNReal.ofReal C * volume (B p) ≤ ENNReal.ofReal C *
          (ENNReal.ofReal t⁻¹ * ∫⁻ x in B p, ENNReal.ofReal (f x)) :=
        mul_le_mul_right (hb p) _
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hC.le, div_eq_mul_inv]
  have hsum : (∑' p : u, ∫⁻ x in B p, ENNReal.ofReal (f x)) ≤
      ∫⁻ x, ENNReal.ofReal (f x) := by
    rw [← lintegral_iUnion (fun _ => measurableSet_closedBall) hdisj]
    exact setLIntegral_le_lintegral _ _
  calc
    volume {x : Vec d | ∃ r : ℝ, 0 < r ∧ r ≤ S ∧
        t * volume.real (Metric.closedBall x r) < ∫ y in Metric.closedBall x r, f y}
        ≤ volume (⋃ p : u, B4 p) := measure_mono hsub
    _ ≤ ∑' p : u, volume (B4 p) := measure_iUnion_le _
    _ ≤ ∑' p : u, ENNReal.ofReal (C / t) *
        ∫⁻ x in B p, ENNReal.ofReal (f x) := ENNReal.tsum_le_tsum hb4
    _ = ENNReal.ofReal (C / t) * (∑' p : u, ∫⁻ x in B p, ENNReal.ofReal (f x)) :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (C / t) * ∫⁻ x, ENNReal.ofReal (f x) := mul_le_mul_right hsum _
    _ = ENNReal.ofReal (C / t * ∫ x, f x) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf),
        ENNReal.ofReal_mul (div_nonneg hC.le ht.le)]

end EinsteinRelation.Correctors
