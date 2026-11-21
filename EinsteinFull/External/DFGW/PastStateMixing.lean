import EinsteinFull.External.DFGW.StateMixing
import EinsteinFull.External.DFGW.MarkovL2

/-! # Mixing between past and future state observables

The Markov property lifts state-space mixing to correlations between an arbitrary
square-integrable past observable and a centered future state observable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A centered future state becomes asymptotically orthogonal to every `L²` past observable. -/
theorem tendsto_inner_past_future_state_zero
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hμ : μ Set.univ ≠ ⊤)
    (s : ℝ≥0) {t : ℝ≥0} (ht : 0 < t) (f : Lp ℝ 2 P)
    (hf : AEStronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] f P)
    (g : Lp ℝ 2 μ) (hg : ∫ x, g x ∂μ = 0) :
    let evalMP (u : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η u) P μ :=
      ⟨(continuous_eval_const u).measurable, hP.marginal u⟩
    Tendsto (fun n : ℕ => inner ℝ f
      (Lp.compMeasurePreserving _ (evalMP (((n • t : ℝ≥0) : ℝ) + s)) g))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic (s : ℝ)) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le s
  let evalMP (u : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η u) P μ :=
    ⟨(continuous_eval_const u).measurable, hP.marginal u⟩
  let U (n : ℕ) : Lp ℝ 2 P :=
    Lp.compMeasurePreserving _ (evalMP (((n • t : ℝ≥0) : ℝ) + s)) g
  let V (n : ℕ) : Lp ℝ 2 P :=
    Lp.compMeasurePreserving _ (evalMP s) (transitionOperator hP (n • t) g)
  have heq (n : ℕ) : (condExpL2 ℝ ℝ hσ (U n) : Lp ℝ 2 P) = V n := by
    have hrep := Lp.coeFn_compMeasurePreserving g (evalMP (((n • t : ℝ≥0) : ℝ) + s))
    have hmem := (Lp.memLp g).comp_measurePreserving (evalMP (((n • t : ℝ≥0) : ℝ) + s))
    have hu : hmem.toLp (fun η => g (η (((n • t : ℝ≥0) : ℝ) + s))) = U n := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp hmem).trans hrep.symm
    have hc : (condExpL2 ℝ ℝ hσ (U n) : Lp ℝ 2 P) =ᵐ[P]
        P[fun η : C(ℝ, S) => g (η (((n • t : ℝ≥0) : ℝ) + s)) |
          Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] := by
      rw [← hu]
      exact hmem.condExpL2_ae_eq_condExp hσ
    have hm := condExp_shifted_L2 hP s (n • t) g
    have hv := Lp.coeFn_compMeasurePreserving (transitionOperator hP (n • t) g) (evalMP s)
    apply Lp.ext
    exact hc.trans (hm.trans hv.symm)
  have hinner (n : ℕ) : inner ℝ f (U n) = inner ℝ f (V n) := by
    calc
      inner ℝ f (U n) = inner ℝ (U n) f := real_inner_comm _ _
      _ = inner ℝ (condExpL2 ℝ ℝ hσ (U n) : Lp ℝ 2 P) f :=
        (inner_condExpL2_eq_inner_fun hσ (U n) f hf).symm
      _ = inner ℝ (V n) f := by rw [heq n]
      _ = inner ℝ f (V n) := real_inner_comm _ _
  have hstate := tendsto_transitionOperator_grid_of_integral_eq_zero hP hμ ht g hg
  have hcomp := ((Lp.isometry_compMeasurePreserving (E := ℝ) (p := 2)
    (evalMP s)).continuous.tendsto 0).comp hstate
  have hV : Tendsto V atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using hcomp
  have hi := (continuous_const.inner continuous_id :
    Continuous (fun x : Lp ℝ 2 P => inner ℝ f x)).tendsto 0
  have hresult := hi.comp hV
  simp only [Function.comp_def, inner_zero_right] at hresult
  change Tendsto (fun n : ℕ => inner ℝ f (U n)) atTop (𝓝 0)
  simpa only [hinner] using hresult

end EinsteinFull.External.DFGW
