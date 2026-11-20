import EinsteinFull.External.DFGW.MartingaleProjection
import EinsteinFull.External.DFGW.GridPastFiltration
import EinsteinRelation.Diffusion.Basic

/-! # Diffusively scaled martingale arrays

The scaled projected increments of a continuous-time martingale have martingale partial sums
on the unit-time grid.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The diffusively normalized projected unit increments in row `n`. -/
noncomputable def scaledProjectedIncrement (N : ℝ≥0 → C(ℝ, S) → Vec d) (e : Vec d)
    (n k : ℕ) (η : C(ℝ, S)) : ℝ :=
  (Real.sqrt (n + 1))⁻¹ * dot e (N ((k : ℝ≥0) + 1) η - N k η)

/-- Each row's partial sums form a martingale with respect to the unit-grid filtration. -/
theorem martingale_scaledProjectedIncrement (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (e : Vec d) (n : ℕ) :
    Martingale (fun k η => ∑ j ∈ Finset.range k, scaledProjectedIncrement N e n j η)
      (gridPast 1) P := by
  let : IsProbabilityMeasure P := hP.probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  have hproj : Martingale (fun t η => dot e (N t η)) Draft.dfgwPast P := by
    simpa only [hL] using martingale_continuousLinearMap hN L
  have hgrid : Martingale (fun k : ℕ => fun η => dot e (N k η)) (gridPast 1) P := by
    constructor
    · intro k
      change StronglyMeasurable[Draft.dfgwPast (k • (1 : ℝ≥0))]
        (fun η => dot e (N k η))
      have hk : k • (1 : ℝ≥0) = (k : ℝ≥0) := by simp
      rw [hk]
      exact hproj.stronglyMeasurable k
    · intro i j hij
      simpa only [gridPast, nsmul_eq_mul, mul_one] using
        hproj.condExp_ae_eq (show (i : ℝ≥0) ≤ j by exact_mod_cast hij)
  have hconst : Martingale (fun _ : ℕ => fun η => dot e (N 0 η)) (gridPast 1) P := by
    apply martingale_const_fun (gridPast 1) P
    · simpa only [Nat.cast_zero] using hgrid.stronglyMeasurable 0
    · simpa only [Nat.cast_zero] using hgrid.integrable 0
  have hscaled := (hgrid.sub hconst).smul (Real.sqrt (n + 1))⁻¹
  have heq : (fun k η => ∑ j ∈ Finset.range k, scaledProjectedIncrement N e n j η) =
      (Real.sqrt (n + 1))⁻¹ • ((fun k : ℕ => fun η => dot e (N k η)) -
        (fun _ : ℕ => fun η => dot e (N 0 η))) := by
    funext k η
    simp only [scaledProjectedIncrement, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum]
    congr 1
    have hsub (j : ℕ) : dot e (N ((j : ℝ≥0) + 1) η - N j η) =
        dot e (N ((j + 1 : ℕ) : ℝ≥0) η) - dot e (N j η) := by
      simp only [Nat.cast_add, Nat.cast_one, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    simp_rw [hsub]
    simpa only [Nat.cast_zero] using Finset.sum_range_sub (fun j => dot e (N j η)) k
  rw [heq]
  exact hscaled

end EinsteinFull.External.DFGW
