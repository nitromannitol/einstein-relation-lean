import EinsteinFull.External.DFGW.GeneratorCore
import EinsteinFull.External.DFGW.BoundedRepresentative

/-! # Generator energy of the mean velocity

The energy estimate for bounded observables extends to the entire generator domain.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The mean-velocity pairing is controlled by generator energy throughout the domain. -/
theorem inner_velocity_sq_le_full_generator_energy
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d)
    (F : (transitionSemigroup hP).generatorDomain) :
    (inner ℝ ((hφ.eval i).toLp (fun x => φ x i)) (F : Lp ℝ 2 μ)) ^ 2 ≤
      (∫ η, (compensated X φ 1 η i) ^ 2 ∂P) *
        (-inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F)) := by
  let lam : MarkovProcess.Semigroup.PositiveShift := ⟨1, by norm_num⟩
  obtain ⟨g, hg, hgen⟩ := exists_simple_resolvent_tendsto_generator hP lam F
  let G : ℕ → (transitionSemigroup hP).generatorDomain := fun n =>
    ⟨(transitionSemigroup hP).resolvent lam (g n),
      (transitionSemigroup hP).resolvent_mem_generatorDomain lam (g n)⟩
  apply generator_energy_bound_of_tendsto hP _ _ F G hg hgen
  intro n
  obtain ⟨C, hC⟩ := (Lp.simpleFunc.toSimpleFunc (g n)).exists_forall_norm_le
  have hgb : ∀ᵐ x ∂μ, ‖(g n : Lp ℝ 2 μ) x‖ ≤ C := by
    filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun (g n)] with x hx
    rw [← hx]
    exact hC x
  have hGb : ∀ᵐ x ∂μ, ‖(G n : Lp ℝ 2 μ) x‖ ≤ (lam : ℝ)⁻¹ * C :=
    transitionResolvent_ae_norm_le hP lam (g n) C hgb
  obtain ⟨f, hf, hfb, hfL2, hrep⟩ := exists_bounded_measurable_rep (G n : Lp ℝ 2 μ) _ hGb
  have hdom : hfL2.toLp f ∈ (transitionSemigroup hP).generatorDomain := by
    rw [hrep]
    exact (G n).property
  have hb := inner_velocity_sq_le_generator_energy hP hX φ hφ hlim hL2 hM i f hf hfb hfL2 hdom
  simpa only [hrep] using hb

end EinsteinFull.External.DFGW
