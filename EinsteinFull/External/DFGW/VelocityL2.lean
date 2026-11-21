import EinsteinFull.External.DFGW.GeneratorEnergy

/-! # The mean forward velocity as an `L²` vector

The source's coordinatewise velocity pairing is the corresponding `L²` inner product. The
generator-energy estimate can therefore be used with Hilbert-space methods.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

omit [TopologicalSpace S] [BorelSpace S] in
/-- The source velocity pairing agrees with the real `L²` inner product. -/
theorem integral_velocity_mul_eq_inner (φ : S → Vec d) (hφ : MemLp φ 2 μ) (i : Fin d)
    (f : S → ℝ) (hfL2 : MemLp f 2 μ) :
    (∫ x, φ x i * f x ∂μ) =
      inner ℝ ((hφ.eval i).toLp (fun x => φ x i)) (hfL2.toLp f) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hφ.eval i), MemLp.coeFn_toLp hfL2] with x hφx hfx
  rw [hφx, hfx]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]

/-- The generator-energy estimate written as a Hilbert-space pairing. -/
theorem inner_velocity_sq_le_generator_energy (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d)
    (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C)
    (hfL2 : MemLp f 2 μ) (hF : hfL2.toLp f ∈ (transitionSemigroup hP).generatorDomain) :
    (inner ℝ ((hφ.eval i).toLp (fun x => φ x i)) (hfL2.toLp f)) ^ 2 ≤
      (∫ η, (compensated X φ 1 η i) ^ 2 ∂P) *
        (-inner ℝ (hfL2.toLp f) ((transitionSemigroup hP).generator ⟨hfL2.toLp f, hF⟩)) := by
  rw [← integral_velocity_mul_eq_inner φ hφ i f hfL2]
  exact velocity_pairing_sq_le_generator_energy hP hX φ hφ hlim hL2 hM i f hf hfb hfL2 hF

end EinsteinFull.External.DFGW
