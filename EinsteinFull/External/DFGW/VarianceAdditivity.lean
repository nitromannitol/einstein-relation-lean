import EinsteinFull.External.DFGW.StationaryVariance
import EinsteinFull.External.DFGW.MartingaleVariance
import EinsteinFull.External.DFGW.MartingaleProjection

/-! # Additivity of compensated-martingale variance

A stationary-increment square-integrable martingale has an additive second moment. This is the
variance scaling used in the forward-velocity energy estimate.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The increment process compensated by its state-dependent forward velocity. -/
noncomputable def compensated (X : ℝ → ℝ → C(ℝ, S) → Vec d) (φ : S → Vec d)
    (t : ℝ≥0) (η : C(ℝ, S)) : Vec d :=
  X 0 t η - ∫ u in (0 : ℝ)..t, φ (η u)

/-- The second moment of each compensated martingale coordinate is additive in time. -/
theorem integral_compensated_sq_add (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : Integrable φ μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d) (s t : ℝ≥0) :
    (∫ η, (compensated X φ (s + t) η i) ^ 2 ∂P) =
      (∫ η, (compensated X φ s η i) ^ 2 ∂P) +
        ∫ η, (compensated X φ t η i) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  have hMc : Martingale (fun t η => compensated X φ t η i) Draft.dfgwPast P :=
    martingale_continuousLinearMap hM (ContinuousLinearMap.proj i)
  have hs := integral_martingale_increment_sq hMc (show s ≤ s + t by simp)
    ((hL2 s).eval i) ((hL2 (s + t)).eval i)
  have ht : MemLp (fun η => X 0 (t : ℝ) η - ∫ u in (0 : ℝ)..t, φ (η u)) 2 P := by
    change MemLp (compensated X φ t) 2 P
    exact hL2 t
  have hstat := integral_compensated_increment_sq hP hX φ hφ
    (a := (s : ℝ)) (b := ((s + t : ℝ≥0) : ℝ)) s.coe_nonneg
    (by exact_mod_cast (show s ≤ s + t by simp)) i (by
      simpa only [NNReal.coe_add, add_sub_cancel_left] using ht)
  simp only [NNReal.coe_add, add_sub_cancel_left, Pi.sub_apply] at hstat
  simp only [compensated, NNReal.coe_add, Pi.sub_apply] at hs ⊢
  rw [hstat] at hs
  linarith

/-- The second moment at an integer multiple of a time scales by that integer. -/
theorem integral_compensated_sq_nsmul (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : Integrable φ μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d) (t : ℝ≥0) (n : ℕ) :
    (∫ η, (compensated X φ (n • t) η i) ^ 2 ∂P) =
      (n : ℝ) * ∫ η, (compensated X φ t η i) ^ 2 ∂P := by
  have hz : (∫ η, (compensated X φ 0 η i) ^ 2 ∂P) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [compensated_zero_ae hX φ] with η hη
    have hi := congrFun hη i
    change compensated X φ 0 η i = 0 at hi
    rw [hi]
    norm_num
  induction n with
  | zero => simp [hz]
  | succ n ih =>
    rw [succ_nsmul, integral_compensated_sq_add hP hX φ hφ hL2 hM, ih]
    push_cast
    ring

/-- The compensated martingale variance at time `1 / n` is its variance at time one divided by `n`. -/
theorem integral_compensated_sq_inv_nat (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : Integrable φ μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d) (n : ℕ) (hn : 0 < n) :
    (∫ η, (compensated X φ (n : ℝ≥0)⁻¹ η i) ^ 2 ∂P) =
      (n : ℝ)⁻¹ * ∫ η, (compensated X φ 1 η i) ^ 2 ∂P := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have ht : n • (n : ℝ≥0)⁻¹ = 1 := by simp [nsmul_eq_mul, hn0]
  have h := integral_compensated_sq_nsmul hP hX φ hφ hL2 hM i (n : ℝ≥0)⁻¹ n
  rw [ht] at h
  calc
    (∫ η, (compensated X φ (n : ℝ≥0)⁻¹ η i) ^ 2 ∂P) =
        (n : ℝ)⁻¹ * ((n : ℝ) * ∫ η, (compensated X φ (n : ℝ≥0)⁻¹ η i) ^ 2 ∂P) := by
      rw [← mul_assoc, inv_mul_cancel₀ hn0', one_mul]
    _ = (n : ℝ)⁻¹ * ∫ η, (compensated X φ 1 η i) ^ 2 ∂P := by rw [← h]

end EinsteinFull.External.DFGW
