import EinsteinFull.External.DFGW.DynkinGridMaximal
import EinsteinFull.External.DFGW.DynkinEnergy

/-! # Energy bound for reversible grid maxima

Cauchy–Schwarz and the Dynkin energy identity bound the reversible grid maximum by the
observable's second moment and its Dirichlet energy.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- On a probability space, the first absolute moment is bounded by the square root of the
second moment. -/
theorem integral_abs_le_sqrt_integral_sq (f : Ω → ℝ) (hf : MemLp f 2 P) :
    (∫ ω, |f ω| ∂P) ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  have h := integral_mul_sq_le (fun ω => |f ω|) (fun _ => 1) hf.abs (memLp_const 1)
  simp only [mul_one, one_pow, integral_const, smul_eq_mul] at h
  have htotal : P.real Set.univ = 1 := by simp [Measure.real]
  have hs : (∫ ω, |f ω| ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
    simpa only [sq_abs, htotal, mul_one] using h
  have hsq : 0 ≤ ∫ ω, f ω ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hr := Real.sq_sqrt hsq
  have hroot := Real.sqrt_nonneg (∫ ω, f ω ^ 2 ∂P)
  have habs : 0 ≤ ∫ ω, |f ω| ∂P := integral_nonneg fun _ => abs_nonneg _
  nlinarith

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {Q : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The reversible grid maximal probability is controlled by the initial second moment and
Dynkin generator energy. -/
theorem measureReal_max_dynkin_grid_le_energy
    (hP : Draft.IsDFGWTrajectoryProcess Q μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (u : ℝ≥0) (n : ℕ)
    (a : ℝ) (ha : 0 < a) :
    (a / 4) * Q.real {η | ∃ k ≤ n, a ≤ |(f : Lp ℝ 2 μ) (η ((k • u : ℝ≥0) : ℝ))|} ≤
      Real.sqrt (∫ η, (f : Lp ℝ 2 μ) (η 0) ^ 2 ∂Q) + 2 *
        Real.sqrt (((n • u : ℝ≥0) : ℝ) *
          (2 * -inner ℝ (f : Lp ℝ 2 μ) ((transitionSemigroup hP).generator f))) := by
  let : IsProbabilityMeasure Q := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have heval : MeasurePreserving (fun η : C(ℝ, S) => η 0) Q μ :=
    ⟨(continuous_eval_const 0).measurable, hP.marginal 0⟩
  have hf : MemLp (fun η : C(ℝ, S) => (f : Lp ℝ 2 μ) (η 0)) 2 Q :=
    (Lp.memLp (f : Lp ℝ 2 μ)).comp_measurePreserving heval
  have hinc : MemLp (fun η => dynkinProcess hP f (n • u) η - dynkinProcess hP f 0 η) 2 Q :=
    (dynkinProcess_memLp hP f (n • u)).sub (dynkinProcess_memLp hP f 0)
  have h0 := integral_abs_le_sqrt_integral_sq _ hf
  have hM := integral_abs_le_sqrt_integral_sq _ hinc
  rw [integral_dynkin_increment_sq_eq_energy hP hcoord f (n • u)] at hM
  have hmax := measureReal_max_dynkin_grid_le hP hcoord f u n a ha
  linarith

end EinsteinFull.External.DFGW
