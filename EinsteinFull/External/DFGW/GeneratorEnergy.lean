import EinsteinFull.External.DFGW.VelocityEnergy
import EinsteinFull.External.DFGW.Semigroup
import MarkovProcess.Semigroup.Generator

/-! # Generator form of the forward-velocity energy estimate

The limiting finite-time semigroup energy of a generator-domain vector is its generator
quadratic form.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The finite-time energy converges to the generator quadratic form. -/
theorem tendsto_generator_energy (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (F : Lp ℝ 2 μ) (hF : F ∈ (transitionSemigroup hP).generatorDomain) :
    Tendsto (fun n : ℕ => (n : ℝ) * (‖F‖ ^ 2 -
      inner ℝ F (transitionOperator hP ((n : ℝ≥0)⁻¹) F))) atTop
      (𝓝 (-inner ℝ F ((transitionSemigroup hP).generator ⟨F, hF⟩))) := by
  have hseq : Tendsto (fun n : ℕ => (n : ℝ≥0)⁻¹) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    change 0 < (n : ℝ≥0)⁻¹
    exact inv_pos.mpr (by exact_mod_cast hn)
  have hgen := ((transitionSemigroup hP).tendsto_generator' ⟨F, hF⟩).comp hseq
  have hinner := (Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := F)) hgen).neg
  apply hinner.congr'
  filter_upwards with n
  change -inner ℝ F (((((n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ)⁻¹) •
    ((transitionSemigroup hP) ((n : ℝ≥0)⁻¹) F - F)) = _
  change -inner ℝ F (((((n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ)⁻¹) •
    (transitionOperator hP ((n : ℝ≥0)⁻¹) F - F)) = _
  simp only [NNReal.coe_inv, NNReal.coe_natCast, inv_inv, inner_smul_right,
    inner_sub_right, real_inner_self_eq_norm_sq]
  ring

variable {d : ℕ} {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The mean velocity pairing is controlled by the generator energy of a bounded observable. -/
theorem velocity_pairing_sq_le_generator_energy (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d)
    (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C)
    (hfL2 : MemLp f 2 μ) (hF : hfL2.toLp f ∈ (transitionSemigroup hP).generatorDomain) :
    (∫ x, φ x i * f x ∂μ) ^ 2 ≤
      (∫ η, (compensated X φ 1 η i) ^ 2 ∂P) *
        (-inner ℝ (hfL2.toLp f) ((transitionSemigroup hP).generator ⟨hfL2.toLp f, hF⟩)) :=
  velocity_pairing_sq_le_energy hP hX φ hφ hlim hL2 hM i f hf hfb hfL2 _
    (tendsto_generator_energy hP (hfL2.toLp f) hF)

end EinsteinFull.External.DFGW
