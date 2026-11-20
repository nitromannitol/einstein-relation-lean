import EinsteinFull.External.DFGW.IncrementSecondMoment
import EinsteinFull.External.DFGW.ObservableEnergy
import EinsteinFull.External.DFGW.IntegralCauchy

/-! # Finite-time forward-velocity energy estimate

The small-time increment bound and Cauchy–Schwarz control the normalized pairing of a
trajectory increment and a state-observable increment by the semigroup energy.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- A normalized trajectory pairing is controlled by the finite-time semigroup energy. -/
theorem normalized_increment_pairing_sq_le (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d)
    (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C)
    (hfL2 : MemLp f 2 μ) (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) * ∫ η, X 0 ((n : ℝ)⁻¹) η i *
      (f (η ((n : ℝ)⁻¹)) - f (η 0)) ∂P) ^ 2 ≤
      4 * ((∫ η, (compensated X φ 1 η i) ^ 2 ∂P) +
        (n : ℝ)⁻¹ * ∫ x, φ x i ^ 2 ∂μ) *
      ((n : ℝ) * (‖hfL2.toLp f‖ ^ 2 - inner ℝ (hfL2.toLp f)
        (transitionOperator hP ((n : ℝ≥0)⁻¹) (hfL2.toLp f)))) := by
  let : IsProbabilityMeasure P := hP.probability
  let q : ℝ≥0 := (n : ℝ≥0)⁻¹
  have hq : (q : ℝ) = (n : ℝ)⁻¹ := by simp [q]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  let U : C(ℝ, S) → ℝ := fun η => X 0 ((n : ℝ)⁻¹) η i
  let V : C(ℝ, S) → ℝ := fun η => f (η ((n : ℝ)⁻¹)) - f (η 0)
  let E : ℝ := ‖hfL2.toLp f‖ ^ 2 - inner ℝ (hfL2.toLp f)
    (transitionOperator hP q (hfL2.toLp f))
  let C : ℝ := ∫ η, (compensated X φ 1 η i) ^ 2 ∂P
  let W : ℝ := ∫ x, φ x i ^ 2 ∂μ
  have hU := increment_memLp_and_sq_le_inv_nat hP hX φ hφ hL2 hM i n hn
  have heval (r : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η r) P μ :=
    ⟨(continuous_eval_const r).measurable, hP.marginal r⟩
  have hV : MemLp V 2 P := by
    change MemLp ((fun η : C(ℝ, S) => f (η ((n : ℝ)⁻¹))) -
      (fun η : C(ℝ, S) => f (η 0))) 2 P
    exact (hfL2.comp_measurePreserving (heval ((n : ℝ)⁻¹))).sub
      (hfL2.comp_measurePreserving (heval 0))
  have hcs : (∫ η, U η * V η ∂P) ^ 2 ≤
      (∫ η, U η ^ 2 ∂P) * ∫ η, V η ^ 2 ∂P := integral_mul_sq_le U V hU.1 hV
  have hVeq : (∫ η, V η ^ 2 ∂P) = 2 * E := by
    have h := integral_observable_increment_sq hP f hf hfb hfL2 q
    simpa only [V, E, hq] using h
  have hVnonneg : 0 ≤ ∫ η, V η ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hUnonneg : 0 ≤ ∫ η, U η ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hUbound : (∫ η, U η ^ 2 ∂P) ≤ 2 * ((n : ℝ)⁻¹ * C + (n : ℝ)⁻¹ ^ 2 * W) := hU.2
  have hBnonneg : 0 ≤ 2 * ((n : ℝ)⁻¹ * C + (n : ℝ)⁻¹ ^ 2 * W) :=
    hUnonneg.trans hUbound
  have hprod := mul_le_mul hUbound hVeq.le hVnonneg hBnonneg
  have hscaled := mul_le_mul_of_nonneg_left (hcs.trans hprod) (sq_nonneg (n : ℝ))
  have halgebra : (n : ℝ) ^ 2 * (2 * ((n : ℝ)⁻¹ * C + (n : ℝ)⁻¹ ^ 2 * W) * (2 * E)) =
      4 * (C + (n : ℝ)⁻¹ * W) * ((n : ℝ) * E) := by
    field_simp
    ring
  rw [halgebra] at hscaled
  change ((n : ℝ) * ∫ η, U η * V η ∂P) ^ 2 ≤ 4 * (C + (n : ℝ)⁻¹ * W) * ((n : ℝ) * E)
  nlinarith

end EinsteinFull.External.DFGW
