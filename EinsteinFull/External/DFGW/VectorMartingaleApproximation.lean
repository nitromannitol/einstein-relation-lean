import EinsteinFull.External.DFGW.IncrementMartingaleApproximation
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Vector martingale approximation of DFGW increments

The coordinate martingale approximations assemble into a vector-valued stationary-increment
martingale, with a sublinear mean-square remainder in each coordinate.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The original increment family admits a vector-valued stationary-increment martingale whose
coordinate remainders have mean square `o(t)`. -/
theorem exists_vector_increment_martingale_approximation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) :
    ∃ N : ℝ≥0 → C(ℝ, S) → Vec d,
      Martingale N Draft.dfgwPast P ∧
      (∀ t, MemLp (N t) 2 P) ∧
      (∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
        fun η => N t (Draft.dfgwShift s η)) ∧
      (∀ i : Fin d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        ∫ η, (X 0 t η i - N t η i) ^ 2 ∂P) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure P := hP.probability
  have hex (i : Fin d) : ∃ N : ℝ≥0 → C(ℝ, S) → ℝ,
      Martingale N Draft.dfgwPast P ∧ (∀ t, MemLp (N t) 2 P) ∧
      (∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P] fun η => N t (Draft.dfgwShift s η)) ∧
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        ∫ η, (X 0 t η i - N t η) ^ 2 ∂P) atTop (𝓝 0) := by
    have h := exists_projected_increment_martingale_approximation hP hcoord hX φ hφ hlim hL2 hM
      (unitVector i)
    simpa only [dot, unitVector, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h
  choose N hN using hex
  let V : ℝ≥0 → C(ℝ, S) → Vec d := fun t η i => N i t η
  have hVLp (t : ℝ≥0) : MemLp (V t) 2 P := (memLp_pi_iff).2 fun i => (hN i).2.1 t
  have hVmart : Martingale V Draft.dfgwPast P := by
    constructor
    · intro t
      let : MeasurableSpace C(ℝ, S) := Draft.dfgwPast t
      apply Measurable.stronglyMeasurable
      apply measurable_pi_iff.mpr
      intro i
      exact ((hN i).1.stronglyMeasurable t).measurable
    · intro s t hst
      have hcoordCE (i : Fin d) :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_condExp_comm
          (m := Draft.dfgwPast s) ((hVLp t).integrable one_le_two)
      have hall : ∀ᵐ η ∂P, ∀ i, (P[V t | Draft.dfgwPast s]) η i = N i s η := by
        rw [ae_all_iff]
        intro i
        filter_upwards [hcoordCE i, (hN i).1.condExp_ae_eq hst] with η hc hm
        simpa only [Function.comp_apply, ContinuousLinearMap.proj_apply, V] using hc.trans hm
      filter_upwards [hall] with η hη
      funext i
      exact hη i
  have hstat (s t : ℝ≥0) : (fun η => V (s + t) η - V s η) =ᵐ[P]
      fun η => V t (Draft.dfgwShift s η) := by
    have hall : ∀ᵐ η ∂P, ∀ i, N i (s + t) η - N i s η = N i t (Draft.dfgwShift s η) := by
      rw [ae_all_iff]
      intro i
      exact (hN i).2.2.1 s t
    filter_upwards [hall] with η hη
    funext i
    exact hη i
  exact ⟨V, hVmart, hVLp, hstat, fun i => (hN i).2.2.2⟩

end EinsteinFull.External.DFGW
