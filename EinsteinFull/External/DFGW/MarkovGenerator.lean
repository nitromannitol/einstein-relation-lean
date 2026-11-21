import EinsteinFull.External.DFGW.MarkovL2
import EinsteinFull.External.DFGW.GeneratorEnergy

/-! # Conditional generator identity

The conditional expectation of a generator-domain observable is given by its initial value
and the integrated semigroup orbit of its generator.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The Markov property combined with the fundamental generator identity. -/
theorem condExp_shifted_generator (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (s t : ℝ≥0) (f : (transitionSemigroup hP).generatorDomain) :
    P[fun η : C(ℝ, S) => (f : Lp ℝ 2 μ) (η ((t : ℝ) + s)) |
      Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] =ᵐ[P]
      fun η => (f : Lp ℝ 2 μ) (η s) +
        (∫ u in (0 : ℝ)..t, transitionSemigroup hP u.toNNReal
          ((transitionSemigroup hP).generator f)) (η s) := by
  let g : Lp ℝ 2 μ := ∫ u in (0 : ℝ)..t, transitionSemigroup hP u.toNNReal
    ((transitionSemigroup hP).generator f)
  have hid : transitionOperator hP t (f : Lp ℝ 2 μ) = (f : Lp ℝ 2 μ) + g := by
    have h := (transitionSemigroup hP).operator_sub_eq_integral f t
    change transitionOperator hP t (f : Lp ℝ 2 μ) - (f : Lp ℝ 2 μ) = g at h
    rw [← h]
    abel
  have ha : transitionOperator hP t (f : Lp ℝ 2 μ) =ᵐ[μ]
      fun x => (f : Lp ℝ 2 μ) x + g x := by
    rw [hid]
    exact Lp.coeFn_add (f : Lp ℝ 2 μ) g
  have hev : MeasurePreserving (fun η : C(ℝ, S) => η (s : ℝ)) P μ :=
    ⟨(continuous_eval_const (s : ℝ)).measurable, hP.marginal s⟩
  have ha' := hev.quasiMeasurePreserving.ae ha
  have hm := condExp_shifted_L2 hP s t (f : Lp ℝ 2 μ)
  filter_upwards [ha', hm] with η haη hmη
  exact hmη.trans haη

end EinsteinFull.External.DFGW
