import EinsteinFull.External.DFGW.ResolventEnergyDifference
import EinsteinFull.External.DFGW.GeneratorEnergyNonnegative
import EinsteinFull.External.DFGW.ResolventVanishing

/-! # Energy convergence of resolvents

Integrable autocorrelations imply that resolvent approximations are Cauchy in generator energy.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A resolvent belongs to the domain of the stationary generator. -/
noncomputable def transitionResolventDomain (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (a : MarkovProcess.Semigroup.PositiveShift) (f : Lp ℝ 2 μ) :
    (transitionSemigroup hP).generatorDomain :=
  ⟨transitionResolvent hP a f, (transitionSemigroup hP).resolvent_mem_generatorDomain a f⟩

/-- The energy of a resolvent difference is bounded by the pairing difference. -/
theorem transitionResolvent_difference_energy_bounds
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (a b : MarkovProcess.Semigroup.PositiveShift) (f : Lp ℝ 2 μ) :
    let F := transitionResolventDomain hP a f - transitionResolventDomain hP b f
    0 ≤ -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F) ∧
      -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F) ≤
        |inner ℝ f (transitionResolvent hP a f) - inner ℝ f (transitionResolvent hP b f)| := by
  let A := transitionResolvent hP a f
  let B := transitionResolvent hP b f
  let F := transitionResolventDomain hP a f - transitionResolventDomain hP b f
  have hF : (F : Lp ℝ 2 μ) = A - B := rfl
  have hgen : (transitionSemigroup hP).generator F = (a : ℝ) • A - (b : ℝ) • B := by
    dsimp only [F, A, B, transitionResolventDomain, transitionResolvent]
    rw [map_sub, (transitionSemigroup hP).generator_resolvent,
      (transitionSemigroup hP).generator_resolvent]
    abel
  constructor
  · exact generator_energy_nonneg hP F
  · rw [hF, hgen]
    rcases le_total (a : ℝ) b with hab | hba
    · exact (transitionResolvent_difference_energy_le hP a b hab f).trans (le_abs_self _)
    · have hs : -inner ℝ (A - B) ((a : ℝ) • A - (b : ℝ) • B) =
          -inner ℝ (B - A) ((b : ℝ) • B - (a : ℝ) • A) := by
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_right]
        ring
      rw [hs]
      have he := transitionResolvent_difference_energy_le hP b a hba f
      have habs : inner ℝ f B - inner ℝ f A ≤ |inner ℝ f A - inner ℝ f B| := by
        have h := neg_le_abs (inner ℝ f A - inner ℝ f B)
        linarith
      exact he.trans habs

/-- Integrable autocorrelation gives convergence of the resolvent quadratic pairings. -/
theorem tendsto_reciprocalShift_pairing (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    Tendsto (fun n : ℕ => inner ℝ f (transitionResolvent hP (reciprocalShift n) f)) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), inner ℝ f (transitionOperator hP t.toNNReal f))) := by
  let r : ℝ → ℝ := fun t => inner ℝ f (transitionOperator hP t.toNNReal f)
  have hr : Continuous r := by
    change Continuous (fun t : ℝ => inner ℝ f (transitionSemigroup hP t.toNNReal f))
    exact continuous_const.inner (((transitionSemigroup hP).continuous_orbit f).comp
      continuous_real_toNNReal)
  have hb : Tendsto (fun n => (reciprocalShift n : ℝ)) atTop (𝓝 0) := by
    simpa only [reciprocalShift] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hb' : Tendsto (fun n => (reciprocalShift n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hb, Filter.Eventually.of_forall fun n => (reciprocalShift n).2⟩
  have h := (tendsto_laplace_integral_zero r hr hint).comp hb'
  simp only [Function.comp_def] at h
  simp_rw [inner_transitionResolvent hP _ f f]
  exact h

/-- Resolvents are Cauchy in generator energy along reciprocal positive parameters. -/
theorem resolvent_energy_cauchy (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      let F := transitionResolventDomain hP (reciprocalShift n) f -
        transitionResolventDomain hP (reciprocalShift m) f;
      -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F) < ε := by
  intro ε hε
  have hc := (tendsto_reciprocalShift_pairing hP f hint).cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hc) ε hε
  refine ⟨N, fun n hn m hm => ?_⟩
  have hb := (transitionResolvent_difference_energy_bounds hP
    (reciprocalShift n) (reciprocalShift m) f).2
  have hd := hN n hn m hm
  rw [Real.dist_eq] at hd
  exact lt_of_le_of_lt hb hd

end EinsteinFull.External.DFGW
