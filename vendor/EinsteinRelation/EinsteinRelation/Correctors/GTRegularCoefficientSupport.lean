import EinsteinRelation.External.GilbargTrudinger
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.Environment.ActualImageLpTransportSupport
import EinsteinRelation.TimeChange.EuclideanTransport

/-!
# Uniform deterministic hypotheses for the reduced harmonic equation

Source: `paper/main.tex:198-207,727-729`. The coefficient of the samplewise
corrector equation is the literal reduced field. Its ellipticity and operator
Lipschitz estimates give the entrywise bounds used by GT 8.17 and 8.32.
The constants below depend only on the dimension and the original bound.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

private theorem coordinate_abs_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  rw [TimeChange.euclideanNorm_eq_norm_toLp]
  exact PiLp.norm_apply_le (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) i

/-- The Euclidean operator bound controls each matrix entry. -/
theorem IsElliptic.entry_abs_le {d : ℕ} {a : Vec d → Mat d} {B : ℝ}
    (hB : 0 < B) (ha : IsElliptic B a) (x : Vec d) (i j : Fin d) :
    |a x i j| ≤ B := by
  have h := (coordinate_abs_le_euclideanNorm ((a x).mulVec (unitVector j)) i).trans
    (isElliptic_mulVec_euclideanNorm_le hB ha x (unitVector j))
  have he : ((a x).mulVec (unitVector j)) i = a x i j := by
    change dotProduct (fun k => a x i k) (Pi.single j 1) = _
    rw [dotProduct_single, mul_one]
  have hu : euclideanNorm (unitVector j) = 1 := by
    simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
  simpa only [he, hu, mul_one] using h

/-- The full entrywise square-sum bound required in GT (8.6). -/
theorem ellipticBound_of_isElliptic {d : ℕ} {a : Vec d → Mat d} {B : ℝ}
    (hB : 0 < B) (ha : IsElliptic B a)
    (hm : ∀ i j, Measurable (fun x => a x i j)) (U : Set (Vec d)) :
    EllipticBound U a B⁻¹ (((d : ℝ) + 1) * B) := by
  refine ⟨hm, fun x _ => ⟨fun ξ => ((ha x).2 ξ).1, ?_⟩⟩
  calc
    (∑ i, ∑ j, |a x i j| ^ 2) ≤ ∑ _ : Fin d, ∑ _ : Fin d, B ^ 2 := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        (sq_le_sq₀ (abs_nonneg _) hB.le).2 (IsElliptic.entry_abs_le hB ha x i j)
    _ = (d : ℝ) ^ 2 * B ^ 2 := by simp; ring
    _ ≤ (((d : ℝ) + 1) * B) ^ 2 := by
      have hd : (d : ℝ) ^ 2 ≤ ((d : ℝ) + 1) ^ 2 := by
        nlinarith only [Nat.cast_nonneg (α := ℝ) d]
      nlinarith only [mul_le_mul_of_nonneg_right hd (sq_nonneg B)]

private theorem ball_distance_lt_two {d : ℕ} {x y : Vec d}
    (hx : x ∈ ball 0 1) (hy : y ∈ ball 0 1) : euclideanNorm (x - y) < 2 := by
  have he : euclideanNorm (-y) = euclideanNorm y := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp, TimeChange.euclideanNorm_eq_norm_toLp]
    exact norm_neg _
  have ht := TimeChange.euclideanNorm_add_le x (-y)
  change euclideanNorm (x - 0) < 1 at hx
  change euclideanNorm (y - 0) < 1 at hy
  simp only [sub_zero] at hx hy
  rw [he] at ht
  simpa only [sub_eq_add_neg] using ht.trans_lt (by linarith)

private theorem le_two_mul_rpow_half {t : ℝ} (ht : 0 ≤ t) (htwo : t ≤ 2) :
    t ≤ 2 * t ^ (1 / (2 : ℝ)) := by
  rw [← Real.sqrt_eq_rpow]
  have hs := Real.sq_sqrt ht
  have hn := Real.sqrt_nonneg t
  nlinarith only [ht, htwo, hs, hn]

/-- A bounded Lipschitz coefficient has a bounded half-Hölder norm on the
Euclidean unit ball; the two distances are never replaced by the Pi norm. -/
theorem holderBound_half_of_isElliptic_lipschitz {d : ℕ} {a : Vec d → Mat d}
    {B A : ℝ} (hB : 0 < B) (hA : 0 ≤ A) (ha : IsElliptic B a)
    (hlip : IsOperatorLipschitz A a) (i j : Fin d) :
    HolderBound (ball 0 1) (1 / 2) (fun x => a x i j) (B + 2 * A) := by
  refine ⟨B, 2 * A, hB.le, by positivity, le_rfl, ?_, ?_⟩
  · intro x _
    exact IsElliptic.entry_abs_le hB ha x i j
  · intro x hx y hy
    calc
      |a x i j - a y i j| ≤ A * euclideanNorm (x - y) := hlip.entry_bound i j x y
      _ ≤ A * (2 * euclideanNorm (x - y) ^ (1 / (2 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (le_two_mul_rpow_half (Real.sqrt_nonneg _) (ball_distance_lt_two hx hy).le) hA
      _ = _ := by ring

/-- Uniform GT coefficients on every environment in the actual reduced image.
The lower ellipticity, square-sum, and Hölder constants are shared by all laws. -/
theorem reduced_gt_coefficient_hypotheses {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      EllipticBound (ball 0 1) ω.1 (sourceReducedBound L)⁻¹
        (((d : ℝ) + 1) * sourceReducedBound L) ∧
      ∀ i j, HolderBound (ball 0 1) (1 / 2) (fun x => ω.1 x i j)
        (sourceReducedBound L + 2 * (Real.exp (2 * L) * (L + 2 * L ^ 2))) := by
  filter_upwards [ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q] with ω hω
  rcases hω with ⟨η, hη, rfl⟩
  have hb := sourceReducedBound_support Q.ellipticity_parameter hη
  have hB : 0 < sourceReducedBound L := zero_lt_one.trans_le hb.1
  have hL : 0 ≤ L := zero_le_one.trans Q.ellipticity_parameter
  refine ⟨ellipticBound_of_isElliptic hB hb.2.1 ?_ _, ?_⟩
  · intro i j
    exact ((continuous_apply j).comp ((continuous_apply i).comp
      (reduce η).1.continuous)).measurable
  · exact holderBound_half_of_isElliptic_lipschitz hB (by positivity) hb.2.1 hb.2.2.2.1


end EinsteinRelation.Correctors
