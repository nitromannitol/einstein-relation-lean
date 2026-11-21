import EinsteinFull.External.DFGW.MartingaleMatrixCovariance
import EinsteinFull.External.DFGW.MartingaleVariance

/-! # Two-time covariance of a stationary martingale

The covariance of two coordinates at ordered times equals their covariance at the earlier time.
For a stationary-increment martingale this is the Brownian covariance `min(s,t) D`.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {Ω ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
variable {ℱ : Filtration ι m} {P : Measure Ω} [IsFiniteMeasure P]

/-- A square-integrable martingale value is orthogonal to the later increment of another
square-integrable martingale. -/
theorem integral_martingale_mul_other_increment (A B : ι → Ω → ℝ)
    (hA : Martingale A ℱ P) (hB : Martingale B ℱ P) {s t : ι} (hst : s ≤ t)
    (hAs : MemLp (A s) 2 P) (hBs : MemLp (B s) 2 P) (hBt : MemLp (B t) 2 P) :
    ∫ ω, A s ω * (B t ω - B s ω) ∂P = 0 := by
  have hsint := hBs.integrable (by norm_num)
  have htint := hBt.integrable (by norm_num)
  have hinc : Integrable (B t - B s) P := htint.sub hsint
  have hprod : Integrable (A s * (B t - B s)) P := hAs.integrable_mul (hBt.sub hBs)
  have hzero : P[B t - B s | ℱ s] =ᵐ[P] 0 := by
    have hc := condExp_of_stronglyMeasurable (ℱ.le s) (hB.stronglyAdapted s) hsint
    filter_upwards [condExp_sub htint hsint (ℱ s), hB.2 s t hst] with ω ha hb
    simp only [Pi.sub_apply, Pi.zero_apply] at ha ⊢
    rw [ha, hb, hc, sub_self]
  have hpull := condExp_mul_of_stronglyMeasurable_left (hA.stronglyAdapted s) hprod hinc
  calc
    (∫ ω, A s ω * (B t ω - B s ω) ∂P) =
        ∫ ω, P[A s * (B t - B s) | ℱ s] ω ∂P := by
      simpa only [Pi.mul_apply, Pi.sub_apply] using
        (integral_condExp (μ := P) (f := A s * (B t - B s)) (ℱ.le s)).symm
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hpull, hzero] with ω hp hz
      simp only [Pi.mul_apply, Pi.zero_apply] at hp hz
      change P[A s * (B t - B s) | ℱ s] ω = (0 : ℝ)
      rw [hp, hz, mul_zero]

/-- For two square-integrable martingales, the covariance at ordered times equals the
covariance at the earlier time. -/
theorem integral_martingale_mul_later (A B : ι → Ω → ℝ)
    (hA : Martingale A ℱ P) (hB : Martingale B ℱ P) {s t : ι} (hst : s ≤ t)
    (hAs : MemLp (A s) 2 P) (hBs : MemLp (B s) 2 P) (hBt : MemLp (B t) 2 P) :
    (∫ ω, A s ω * B t ω ∂P) = ∫ ω, A s ω * B s ω ∂P := by
  have h := integral_martingale_mul_other_increment A B hA hB hst hAs hBs hBt
  have hi1 : Integrable (fun ω => A s ω * B t ω) P := hAs.integrable_mul hBt
  have hi2 : Integrable (fun ω => A s ω * B s ω) P := hAs.integrable_mul hBs
  rw [show (fun ω => A s ω * (B t ω - B s ω)) =
    (fun ω => A s ω * B t ω - A s ω * B s ω) by ext ω; ring,
    integral_sub hi1 hi2] at h
  linarith

end EinsteinFull.External.DFGW
