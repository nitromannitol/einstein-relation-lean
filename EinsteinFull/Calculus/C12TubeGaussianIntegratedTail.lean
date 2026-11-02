import EinsteinRelation.Clock.HeatCubeMasses
import EinsteinRelation.TimeChange.EuclideanTransport
import EinsteinRelation.TimeChange.Pairing
import EinsteinFull.External.Source.GMPDirichletKernel

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open EinsteinRelation.Correctors EinsteinRelation.Clock
open scoped Topology

noncomputable section
namespace EinsteinFull.Calculus

/-- Split the Gaussian exponent into a distance factor and an integrable factor. -/
theorem c12_gaussian_tail_exponent_split {a t r s : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hrs : r ≤ s) :
    Real.exp (-s / (a * t)) ≤
      Real.exp (-r / (2 * a * t)) * Real.exp (-s / (2 * a * t)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : -r / (2 * a * t) + -s / (2 * a * t) =
      (-r - s) / (2 * a * t) := by ring
  rw [h]
  have he : -s / (a * t) = (-2 * s) / (2 * a * t) := by
    field_simp
  rw [he]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * a * t)).2
  linarith

/-- The mass of an unnormalized Euclidean Gaussian. -/
theorem c12_integral_gaussian_euclidean {d : ℕ} {a : ℝ} (ha : 0 < a) :
    (∫ y : Vec d, Real.exp (-(euclideanSq y) / a)) =
      (Real.pi * a) ^ ((d : ℝ) / 2) := by
  have h := congrArg (fun z : ℝ => (Real.pi * a) ^ ((d : ℝ) / 2) * z)
    (integral_euclideanHeatKernel (d := d) (show 0 < a / 4 by positivity))
  rw [mul_one, ← integral_const_mul] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with y
  simp only [euclideanHeatKernel]
  have hb : 4 * Real.pi * (a / 4) = Real.pi * a := by ring
  rw [hb, ← mul_assoc, ← Real.rpow_add (by positivity)]
  rw [show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]
  congr 1 <;> ring

/-- An unnormalized Euclidean Gaussian is integrable. -/
theorem c12_integrable_gaussian_euclidean {d : ℕ} {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : Vec d => Real.exp (-(euclideanSq y) / a)) volume := by
  have h := (integrable_euclideanHeatKernel (d := d) (show 0 < a / 4 by positivity)).const_mul
    ((4 * Real.pi * (a / 4)) ^ ((d : ℝ) / 2))
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [euclideanHeatKernel]
  rw [← mul_assoc, ← Real.rpow_add (by positivity)]
  rw [show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]
  congr 1 <;> ring

/-- Translation preserves the mass and integrability of the Gaussian. -/
theorem c12_translated_gaussian_euclidean {d : ℕ} {a : ℝ} (ha : 0 < a)
    (x : Vec d) :
    Integrable (fun y : Vec d => Real.exp (-(euclideanSq (y - x)) / a)) volume ∧
    (∫ y : Vec d, Real.exp (-(euclideanSq (y - x)) / a)) =
      (Real.pi * a) ^ ((d : ℝ) / 2) := by
  constructor
  · simpa only [sub_eq_add_neg] using
      (c12_integrable_gaussian_euclidean (d := d) ha).comp_add_right (-x)
  · calc
      (∫ y : Vec d, Real.exp (-(euclideanSq (y - x)) / a)) =
          ∫ y : Vec d, Real.exp (-(euclideanSq y) / a) :=
        integral_sub_right_eq_self (fun y : Vec d => Real.exp (-(euclideanSq y) / a)) x
      _ = _ := c12_integral_gaussian_euclidean ha

/-- The heat scaling cancels the dimensional power of time. -/
theorem c12_gaussian_time_power_cancel (d : ℕ) {C t : ℝ} (hC : 0 < C) (ht : 0 < t) :
    Real.rpow t (-(d : ℝ) / 2) * (Real.pi * (2 * C * t)) ^ ((d : ℝ) / 2) =
      (Real.pi * (2 * C)) ^ ((d : ℝ) / 2) := by
  simp only [Real.rpow_eq_pow]
  have he : Real.pi * (2 * C * t) = (Real.pi * (2 * C)) * t := by ring
  rw [he, Real.mul_rpow (by positivity) ht.le]
  have hc : t ^ (-((d : ℝ) / 2)) * t ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero]
  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring]
  calc
    _ = (Real.pi * (2 * C)) ^ ((d : ℝ) / 2) *
        (t ^ (-((d : ℝ) / 2)) * t ^ ((d : ℝ) / 2)) := by ring
    _ = _ := by rw [hc, mul_one]

/-- A translated Gaussian has at most its full mass on any measurable restriction. -/
theorem c12_restricted_gaussian_mass_bound {d : ℕ} {a : ℝ} (ha : 0 < a)
    (x : Vec d) (s : Set (Vec d)) :
    (∫ y in s, Real.exp (-(euclideanSq (y - x)) / a)) ≤
      (Real.pi * a) ^ ((d : ℝ) / 2) := by
  calc
    _ ≤ ∫ y : Vec d, Real.exp (-(euclideanSq (y - x)) / a) :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ fun _ => (Real.exp_pos _).le)
        (c12_translated_gaussian_euclidean ha x).1
    _ = _ := (c12_translated_gaussian_euclidean ha x).2

/-- The normalized Gaussian mass is bounded uniformly over time and restrictions. -/
theorem c12_restricted_gaussian_scaled_mass_bound (d : ℕ) {C t : ℝ}
    (hC : 0 < C) (ht : 0 < t) (x : Vec d) (s : Set (Vec d)) :
    Real.rpow t (-(d : ℝ) / 2) *
        (∫ y in s, Real.exp (-(euclideanSq (y - x)) / (2 * C * t))) ≤
      (Real.pi * (2 * C)) ^ ((d : ℝ) / 2) := by
  calc
    _ ≤ Real.rpow t (-(d : ℝ) / 2) *
        (Real.pi * (2 * C * t)) ^ ((d : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left
        (c12_restricted_gaussian_mass_bound (by positivity) x s) (Real.rpow_nonneg ht.le _)
    _ = _ := c12_gaussian_time_power_cancel d hC ht

/-- Outside a Euclidean ball, extract the distance-dependent Gaussian factor. -/
theorem c12_gaussian_exterior_exponent_bound {d : ℕ} {C t δ : ℝ}
    (hC : 0 < C) (ht : 0 < t) (hδ : 0 < δ) (x y : Vec d)
    (hy : y ∉ sourceBall x δ) :
    Real.exp (-(euclideanNorm (x - y)) ^ 2 / (C * t)) ≤
      Real.exp (-δ ^ 2 / (2 * C * t)) *
        Real.exp (-(euclideanSq (y - x)) / (2 * C * t)) := by
  have hs : euclideanNorm (x - y) = euclideanNorm (y - x) := by
    rw [← neg_sub y x]
    have h := TimeChange.euclideanNorm_smul (-1 : ℝ) (y - x)
    simpa using h
  have hd : δ ≤ euclideanNorm (y - x) := by
    exact le_of_not_gt hy
  have hn : 0 ≤ euclideanNorm (y - x) := by
    unfold euclideanNorm
    exact Real.sqrt_nonneg _
  have hsq : δ ^ 2 ≤ (euclideanNorm (y - x)) ^ 2 := by
    nlinarith
  rw [hs, TimeChange.euclideanSq_eq_sq_euclideanNorm]
  exact c12_gaussian_tail_exponent_split hC ht hsq

/-- The Gaussian envelope has an integrated off-diagonal tail. -/
@[nolint unusedArguments]
theorem c12_gaussian_integrated_offdiagonal_tail (d : ℕ) (hd : 2 ≤ d)
    (C R : ℝ) (hC : 0 < C) (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : ℝ → Vec d → Vec d → ℝ),
      (∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        AEStronglyMeasurable (K t x) (volume.restrict (sourceBall 0 R))) →
      (∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          |K t x y| ≤ C * Real.rpow t (-(d : ℝ)/2) *
            Real.exp (-(euclideanNorm (x-y))^2/(C*t))) →
      ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ δ : ℝ, 0 < δ →
        (∫ y in sourceBall (0 : Vec d) R \ sourceBall x δ, |K t x y|) ≤
          B * Real.exp (-δ^2/(B*t)) := by
  let M : ℝ := C * (Real.pi * (2 * C)) ^ ((d : ℝ) / 2)
  let B : ℝ := 2 * C + M + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 < B := by dsimp [B]; linarith
  have hBC : 2 * C ≤ B := by dsimp [B]; linarith
  have hBM : M ≤ B := by dsimp [B]; linarith
  refine ⟨B, hB, ?_⟩
  intro K hm hk t ht x hx δ hδ
  let S : Set (Vec d) := sourceBall (0 : Vec d) R \ sourceBall x δ
  have hcont : Continuous (fun z : Vec d => euclideanNorm z) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i))
  have hball : ∀ (z : Vec d) (r : ℝ), MeasurableSet (sourceBall z r) := by
    intro z r
    exact (isOpen_lt (hcont.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet
  have hS : MeasurableSet S := (hball 0 R).diff (hball x δ)
  have hmeas : AEStronglyMeasurable (fun y => |K t x y|) (volume.restrict S) :=
    by
      simpa only [Real.norm_eq_abs] using
        ((hm t ht x hx).mono_measure (Measure.restrict_mono_set volume
          (Set.diff_subset : S ⊆ sourceBall (0 : Vec d) R))).norm
  let A : ℝ := C * Real.rpow t (-(d : ℝ) / 2) * Real.exp (-δ ^ 2 / (2 * C * t))
  let G : Vec d → ℝ := fun y => Real.exp (-(euclideanSq (y - x)) / (2 * C * t))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hG : Integrable G (volume.restrict S) :=
    ((c12_translated_gaussian_euclidean (d := d) (show 0 < 2 * C * t by positivity) x).1).mono_measure Measure.restrict_le_self
  have hmajor : Integrable (fun y => A * G y) (volume.restrict S) := hG.const_mul A
  have hp : ∀ᵐ y ∂volume.restrict S, |K t x y| ≤ A * G y := by
    filter_upwards [ae_restrict_mem hS] with y hy
    have he := c12_gaussian_exterior_exponent_bound hC ht hδ x y hy.2
    have hc : 0 ≤ C * Real.rpow t (-(d : ℝ) / 2) :=
      mul_nonneg hC.le (Real.rpow_nonneg ht.le _)
    calc
      |K t x y| ≤ C * Real.rpow t (-(d : ℝ)/2) *
          Real.exp (-(euclideanNorm (x-y))^2/(C*t)) := hk t ht x hx y hy.1
      _ ≤ C * Real.rpow t (-(d : ℝ)/2) *
          (Real.exp (-δ ^ 2 / (2 * C * t)) * G y) := mul_le_mul_of_nonneg_left he hc
      _ = A * G y := by dsimp [A]; ring
  have hki : Integrable (fun y => |K t x y|) (volume.restrict S) := by
    refine Integrable.mono' hmajor hmeas ?_
    filter_upwards [hp] with y hy
    simpa only [Real.norm_eq_abs, abs_abs] using hy
  have hmexp : Real.exp (-δ ^ 2 / (2 * C * t)) ≤ Real.exp (-δ ^ 2 / (B * t)) := by
    apply Real.exp_le_exp.mpr
    have hden : 2 * C * t ≤ B * t := mul_le_mul_of_nonneg_right hBC ht.le
    have hp1 : 0 < 2 * C * t := by positivity
    have hp2 : 0 < B * t := by positivity
    rw [div_le_div_iff₀ hp1 hp2]
    have hd2 : 0 ≤ δ ^ 2 := sq_nonneg δ
    nlinarith
  calc
    (∫ y in S, |K t x y|) ≤ ∫ y in S, A * G y := integral_mono_ae hki hmajor hp
    _ = A * (∫ y in S, G y) := integral_const_mul _ _
    _ ≤ M * Real.exp (-δ ^ 2 / (2 * C * t)) := by
      have hz := c12_restricted_gaussian_scaled_mass_bound d hC ht x S
      have hz' := mul_le_mul_of_nonneg_left hz
        (mul_nonneg hC.le (Real.exp_pos (-δ ^ 2 / (2 * C * t))).le)
      dsimp [A, M, G] at *
      nlinarith
    _ ≤ B * Real.exp (-δ ^ 2 / (B * t)) :=
      mul_le_mul hBM hmexp (Real.exp_pos _).le (le_trans hM hBM)

#print axioms c12_gaussian_tail_exponent_split
#print axioms c12_integral_gaussian_euclidean
#print axioms c12_integrable_gaussian_euclidean
#print axioms c12_translated_gaussian_euclidean
#print axioms c12_gaussian_time_power_cancel
#print axioms c12_restricted_gaussian_mass_bound
#print axioms c12_restricted_gaussian_scaled_mass_bound
#print axioms c12_gaussian_exterior_exponent_bound
#print axioms c12_gaussian_integrated_offdiagonal_tail

end EinsteinFull.Calculus
