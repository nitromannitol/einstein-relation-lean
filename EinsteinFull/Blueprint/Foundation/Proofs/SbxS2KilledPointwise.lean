import EinsteinFull.Work.W1.GMPKilledSemigroupSupport
import Mathlib.Tactic.Linter

/-!
# Every-start identification for the actual killed GMP law

Right-time continuity follows directly from strict survival and continuous paths,
including paths exiting exactly at the displayed time. The actual semigroup and
positive-time absolute continuity then upgrade an interior almost-everywhere
continuous representative to every interior start. No analytic representative or
identification of the killed form is constructed here.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support

noncomputable section

/-- Strict survival at `t + s` eventually agrees with survival at `t` as the
nonnegative increment tends to zero, even when the exit time equals `t`. -/
theorem eventually_localitySurvival_add_at_zero {d : ℕ} (U : Set (Vec d))
    (γ : Path d) (t : ℝ≥0) :
    ∀ᶠ s : ℝ≥0 in 𝓝 0,
      (((t + s : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ ↔
        (t : ℝ≥0∞) < localityExitTime U γ) := by
  have ht : Tendsto (fun s : ℝ≥0 => ((t + s : ℝ≥0) : ℝ≥0∞))
      (𝓝 0) (𝓝 (t : ℝ≥0∞)) := by
    have hadd : Tendsto (fun s : ℝ≥0 => t + s) (𝓝 0) (𝓝 t) := by
      simpa only [id_eq, add_zero] using!
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => t) (𝓝 0) (𝓝 t)).add
          (tendsto_id : Tendsto (fun s : ℝ≥0 => s) (𝓝 0) (𝓝 0)))
    exact ENNReal.continuous_coe.continuousAt.tendsto.comp hadd
  by_cases hs : (t : ℝ≥0∞) < localityExitTime U γ
  · filter_upwards [ht.eventually (Iio_mem_nhds hs)] with s hts
    exact iff_of_true hts hs
  · apply Eventually.of_forall
    intro s
    have hts : ¬((t + s : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ := by
      intro h
      exact hs (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr
        (le_add_of_nonneg_right zero_le)) h)
    exact iff_of_false hts hs

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)

/-- At every starting point, actual killed expectations of bounded continuous
tests are continuous as a nonnegative time increment decreases to zero. -/
theorem tendsto_integral_gmpKilledEndpointKernel_add_at_zero
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (x : Vec d)
    (f : Vec d → ℝ) (hf : Continuous f) (B : ℝ) (hB : ∀ y, |f y| ≤ B) :
    Tendsto (fun s : ℝ≥0 => ∫ y, f y ∂gmpKilledEndpointKernel G U hU (t + s) x)
      (𝓝 0) (𝓝 (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x)) := by
  classical
  let := G.pathLaw_isMarkovKernel
  let F : ℝ≥0 → Path d → ℝ := fun r =>
    {γ : Path d | (r : ℝ≥0∞) < localityExitTime U γ}.indicator
      (fun γ => f (pathPosition r γ))
  have hB0 : 0 ≤ B := (abs_nonneg (f x)).trans (hB x)
  have hmeas : ∀ s, AEStronglyMeasurable (F (t + s)) (G.pathLaw x) := by
    intro s
    exact ((hf.measurable.comp (measurable_pathPosition (t + s))).indicator
      (measurableSet_localitySurvival U hU (t + s))).aestronglyMeasurable
  have hbound : ∀ s, ∀ᵐ γ ∂G.pathLaw x, ‖F (t + s) γ‖ ≤ B := by
    intro s
    apply ae_of_all
    intro γ
    by_cases hs : ((t + s : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ
    · simpa only [F, Set.indicator, Set.mem_ofPred_eq, hs, ↓reduceIte, Real.norm_eq_abs]
        using hB (pathPosition (t + s) γ)
    · simpa only [F, Set.indicator, Set.mem_ofPred_eq, hs, ↓reduceIte, norm_zero] using hB0
  have hlim : ∀ᵐ γ ∂G.pathLaw x,
      Tendsto (fun s => F (t + s) γ) (𝓝 0) (𝓝 (F t γ)) := by
    apply ae_of_all
    intro γ
    have heq := eventually_localitySurvival_add_at_zero U γ t
    by_cases hs : (t : ℝ≥0∞) < localityExitTime U γ
    · have ht : Tendsto (fun s : ℝ≥0 => f (γ (t + s))) (𝓝 0) (𝓝 (f (γ t))) := by
        have hadd : Tendsto (fun s : ℝ≥0 => t + s) (𝓝 0) (𝓝 t) := by
          simpa only [id_eq, add_zero] using!
            ((tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => t) (𝓝 0) (𝓝 t)).add
              (tendsto_id : Tendsto (fun s : ℝ≥0 => s) (𝓝 0) (𝓝 0)))
        exact (hf.tendsto (γ t)).comp ((γ.continuous.tendsto t).comp hadd)
      have hFt : F t γ = f (γ t) := by
        simp only [F, Set.indicator, Set.mem_ofPred_eq, hs, ↓reduceIte, pathPosition]
      rw [hFt]
      apply ht.congr'
      filter_upwards [heq] with s heq
      simp only [F, Set.indicator, Set.mem_ofPred_eq, heq.mpr hs, ↓reduceIte, pathPosition]
    · have hFt : F t γ = 0 := by
        simp only [F, Set.indicator, Set.mem_ofPred_eq, hs, ↓reduceIte]
      rw [hFt]
      apply tendsto_const_nhds.congr'
      filter_upwards [heq] with s heq
      simp only [F, Set.indicator, Set.mem_ofPred_eq, not_iff_not.mpr heq |>.mpr hs,
        ↓reduceIte]
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) (integrable_const B) hlim
  simpa only [F, ← integral_gmpKilledEndpointKernel G U hU _ x f hf.measurable] using h

/-- A bounded continuous test is integrable against every actual killed endpoint law. -/
theorem integrable_gmpKilledEndpointKernel_of_continuous_bounded
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (x : Vec d)
    (f : Vec d → ℝ) (hf : Continuous f) (B : ℝ) (hB : ∀ y, |f y| ≤ B) :
    Integrable f (gmpKilledEndpointKernel G U hU t x) := by
  let := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  exact (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun y => (Real.norm_eq_abs (f y)).trans_le (hB y))

/-- The actual killed expectations obey the semigroup law on bounded continuous
tests, at every starting point. -/
theorem integral_gmpKilledEndpointKernel_add
    (U : Set (Vec d)) (hU : IsOpen U) (s t : ℝ≥0) (x : Vec d)
    (f : Vec d → ℝ) (hf : Continuous f) (B : ℝ) (hB : ∀ y, |f y| ≤ B) :
    (∫ z, f z ∂gmpKilledEndpointKernel G U hU (s + t) x) =
      ∫ y, (∫ z, f z ∂gmpKilledEndpointKernel G U hU t y)
        ∂gmpKilledEndpointKernel G U hU s x := by
  have hi := integrable_gmpKilledEndpointKernel_of_continuous_bounded G U hU (s + t) x
    f hf B hB
  rw [gmpKilledEndpointKernel_add G U hU s t] at hi ⊢
  exact Kernel.integral_comp hi

/-- Positive-time actual killed laws respect almost-everywhere equalities on
the interior alone; their endpoints lie in the domain at every start. -/
theorem integral_gmpKilledEndpointKernel_congr_ae_restrict
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ≥0) (hs : 0 < s) (x : Vec d)
    (f g : Vec d → ℝ)
    (hfg : f =ᵐ[(physicalReversibleMeasure ω hd lam).restrict U] g) :
    (∫ y, f y ∂gmpKilledEndpointKernel G U hU s x) =
      ∫ y, g y ∂gmpKilledEndpointKernel G U hU s x := by
  have hfg' := (ae_restrict_iff' hU.measurableSet).mp hfg
  apply integral_congr_ae
  filter_upwards [(gmpKilledEndpointKernel_absolutelyContinuous_physical G U hU s hs x).ae_le hfg',
    gmpKilledEndpointKernel_ae_mem G U hU s x] with y hy hyU
  exact hy hyU

/-- If a fixed-time actual killed expectation has a bounded continuous
representative on the interior, that representative agrees at every interior
start. Existence of that representative is a separate analytic obligation. -/
theorem integral_gmpKilledEndpointKernel_eq_of_ae_eq_continuous
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : Continuous f) (B : ℝ) (hB : ∀ y, |f y| ≤ B)
    (g : Vec d → ℝ) (hg : Continuous g) (C : ℝ) (hC : ∀ y, |g y| ≤ C)
    (hfg : (fun y => ∫ z, f z ∂gmpKilledEndpointKernel G U hU t y)
      =ᵐ[(physicalReversibleMeasure ω hd lam).restrict U] g)
    (x : Vec d) (hx : x ∈ U) :
    (∫ z, f z ∂gmpKilledEndpointKernel G U hU t x) = g x := by
  have heq : ∀ s : ℝ≥0, 0 < s →
      (∫ z, f z ∂gmpKilledEndpointKernel G U hU (t + s) x) =
        ∫ y, g y ∂gmpKilledEndpointKernel G U hU s x := by
    intro s hs
    rw [add_comm t s, integral_gmpKilledEndpointKernel_add G U hU s t x f hf B hB]
    exact integral_gmpKilledEndpointKernel_congr_ae_restrict G U hU s hs x _ g hfg
  have hr := (tendsto_integral_gmpKilledEndpointKernel_add_at_zero G U hU t x f hf B hB).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ≥0)))
  have hz := (tendsto_integral_gmpKilledEndpointKernel_at_zero G U hU x hx g hg C hC).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ≥0)))
  have he : ∀ᶠ s : ℝ≥0 in 𝓝[>] 0,
      (∫ z, f z ∂gmpKilledEndpointKernel G U hU (t + s) x) =
        ∫ y, g y ∂gmpKilledEndpointKernel G U hU s x := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact heq s hs
  exact tendsto_nhds_unique hr (hz.congr' (EventuallyEq.symm he))

end

end EinsteinFull

#print axioms EinsteinFull.eventually_localitySurvival_add_at_zero
#print axioms EinsteinFull.tendsto_integral_gmpKilledEndpointKernel_add_at_zero
#print axioms EinsteinFull.integrable_gmpKilledEndpointKernel_of_continuous_bounded
#print axioms EinsteinFull.integral_gmpKilledEndpointKernel_add
#print axioms EinsteinFull.integral_gmpKilledEndpointKernel_congr_ae_restrict
#print axioms EinsteinFull.integral_gmpKilledEndpointKernel_eq_of_ae_eq_continuous

#lint
