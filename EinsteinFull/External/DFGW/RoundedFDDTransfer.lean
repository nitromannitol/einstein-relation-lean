import EinsteinFull.External.DFGW.MartingaleFiniteTimeRounding
import EinsteinFull.External.DFGW.ScaledFiniteDimensionalTransfer

/-! # Transfer from rounded martingale finite-dimensional limits

A joint limit for the martingale at rounded observation times transfers to the original
continuous increment process.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} [IsProbabilityMeasure P] {μ : Measure S}
variable {T : ℝ≥0 → Kernel S S} {X : ℝ → ℝ → C(ℝ, S) → Vec d}
variable {Y : C(ℝ, S) → Path d}
variable {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]

/-- Joint convergence of the martingale at rounded times transfers to the increment process. -/
theorem tendstoInDistribution_scaled_fdd_of_rounded_martingale
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) (hφ : MemLp φ 2 μ) (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (hrem : ∀ e : Vec d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0))
    {J : Type*} [Fintype J] (times : J → ℝ≥0) (Z : Ω' → J → Vec d)
    (hlimit : TendstoInDistribution (fun (ε : ℝ) η j => ε •
      N (floorTime ((ε⁻¹ ^ 2).toNNReal * times j)) η) (𝓝[>] 0) Z (fun _ => P) ν) :
    TendstoInDistribution (fun (ε : ℝ) η j => ε • Y η ((ε⁻¹ ^ 2).toNNReal * times j))
      (𝓝[>] 0) Z (fun _ => P) ν := by
  let A : ℝ → C(ℝ, S) → J → Vec d := fun ε η j => ε • N ((ε⁻¹ ^ 2).toNNReal * times j) η
  let B : ℝ → C(ℝ, S) → J → Vec d := fun ε η j => ε •
    N (floorTime ((ε⁻¹ ^ 2).toNNReal * times j)) η
  have hdiff : TendstoInMeasure P (A - B) (𝓝[>] 0) 0 := by
    have h := tendstoInMeasure_martingale_finite_rounding hP N hN hN2 hstat times
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h
    intro ε
    apply ae_of_all P
    intro η
    funext j i
    simp only [A, B, Pi.sub_apply, Pi.smul_apply, smul_sub]
  have hA (ε : ℝ) : AEMeasurable (A ε) P := by
    apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro j
    have hm := (hN.stronglyAdapted ((ε⁻¹ ^ 2).toNNReal * times j)).mono
      (Draft.dfgwPast.le _)
    exact (hm.const_smul ε).measurable
  have hmart : TendstoInDistribution A (𝓝[>] 0) Z (fun _ => P) ν :=
    tendstoInDistribution_of_tendstoInMeasure_sub A Z hlimit hdiff hA
  exact tendstoInDistribution_scaled_finite_dimensional_of_martingale hP hX φ hφ hL2
    N hN2 hstat hrem times Z hmart

end EinsteinFull.External.DFGW
