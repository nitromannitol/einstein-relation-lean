import EinsteinFull.External.DFGW.ResolventLimitVariance

/-! # Stationary increments of the limiting martingale

The `L²` limit of the resolvent martingales retains their stationary-increment cocycle under
trajectory shifts.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Centered Dynkin increments form a stationary-increment cocycle in `L²`. -/
theorem dynkinIncrementLp_shift (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (s t : ℝ≥0) :
    let hshift : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
      ⟨measurable_shift s, hP.stationary s⟩
    dynkinIncrementLp hP f (s + t) - dynkinIncrementLp hP f s =
      Lp.compMeasurePreserving _ hshift (dynkinIncrementLp hP f t) := by
  let hshift : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
    ⟨measurable_shift s, hP.stationary s⟩
  have hrepr (u : ℝ≥0) : dynkinIncrementLp hP f u =ᵐ[P]
      fun η => dynkinProcess hP f u η - dynkinProcess hP f 0 η :=
    MemLp.coeFn_toLp ((dynkinProcess_memLp hP f u).sub (dynkinProcess_memLp hP f 0))
  have hcomp := Lp.coeFn_compMeasurePreserving (dynkinIncrementLp hP f t) hshift
  have hrepr' := hshift.quasiMeasurePreserving.ae (hrepr t)
  have hsub := Lp.coeFn_sub (dynkinIncrementLp hP f (s + t)) (dynkinIncrementLp hP f s)
  have hinc := dynkinProcess_increment_shift hP f s t
  apply Lp.ext
  filter_upwards [hcomp, hrepr', hrepr (s + t), hrepr s, hsub, hinc] with η hc hr ha hb hd hi
  simp only [Function.comp_apply, Pi.sub_apply] at hc hr hd
  rw [hd, ha, hb, hc, hr]
  linarith

/-- The fixed-time `L²` resolvent limit retains the stationary-increment cocycle. -/
theorem resolvent_limit_stationary_increments (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    (s t : ℝ≥0) :
    let hshift : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
      ⟨measurable_shift s, hP.stationary s⟩
    Z (s + t) - Z s = Lp.compMeasurePreserving _ hshift (Z t) := by
  let hshift : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
    ⟨measurable_shift s, hP.stationary s⟩
  have hleft := (hZ (s + t)).sub (hZ s)
  have hright := ((Lp.isometry_compMeasurePreserving (E := ℝ) (p := 2) hshift).continuous.tendsto
    (Z t)).comp (hZ t)
  have heq : (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) (s + t) - dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) s) =
      (fun n : ℕ => Lp.compMeasurePreserving _ hshift (dynkinIncrementLp hP
        (transitionResolventDomain hP (reciprocalShift n) f) t)) := by
    funext n
    exact dynkinIncrementLp_shift hP _ s t
  change Tendsto (fun n : ℕ => Lp.compMeasurePreserving _ hshift (dynkinIncrementLp hP
    (transitionResolventDomain hP (reciprocalShift n) f) t)) atTop
    (𝓝 (Lp.compMeasurePreserving _ hshift (Z t))) at hright
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end EinsteinFull.External.DFGW
