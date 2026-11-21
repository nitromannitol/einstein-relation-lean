import EinsteinFull.External.DFGW.Trajectory
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Reflection pairing for trajectory increments

An antisymmetric increment paired with an endpoint observable changes sign when the endpoint
is exchanged. This is the integration-by-parts identity used in the energy estimate.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Reflection exchanges the endpoint in the pairing of an antisymmetric increment. -/
theorem integral_increment_mul_eval_end (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) {a b : ℝ} (hab : a ≤ b)
    (i : Fin d) (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    (∫ η, X a b η i * f (η b) ∂P) = -(∫ η, X a b η i * f (η a) ∂P) := by
  obtain ⟨C, hC⟩ := hfb
  have hi : Integrable (fun η => X a b η i) P := (hX.integrable a b hab).eval i
  have hp (t : ℝ) : Integrable (fun η => X a b η i * f (η t)) P :=
    hi.mul_bdd (hf.comp (continuous_eval_const t).measurable).aestronglyMeasurable
      (ae_of_all _ fun η => by simpa only [Real.norm_eq_abs] using hC (η t))
  have hm : AEStronglyMeasurable (fun η => X a b η i * f (η b))
      (P.map (Draft.dfgwRefl ((a + b) / 2))) := by
    rw [hP.reversible]
    exact (hp b).aestronglyMeasurable
  have he : 2 * ((a + b) / 2) - b = a := by ring
  calc
    (∫ η, X a b η i * f (η b) ∂P) =
        ∫ η, X a b η i * f (η b) ∂P.map (Draft.dfgwRefl ((a + b) / 2)) := by
      rw [hP.reversible]
    _ = ∫ η, X a b (Draft.dfgwRefl ((a + b) / 2) η) i *
        f (Draft.dfgwRefl ((a + b) / 2) η b) ∂P :=
      integral_map (measurable_refl _).aemeasurable hm
    _ = ∫ η, -(X a b η i * f (η a)) ∂P := by
      apply integral_congr_ae
      filter_upwards [hX.antisymmetric a b hab] with η hη
      have hi' := congrFun hη i
      have he' : Draft.dfgwRefl ((a + b) / 2) η b = η a := by
        change η (2 * ((a + b) / 2) - b) = η a
        rw [he]
      rw [he', hi']
      simp only [Pi.neg_apply, neg_mul]
    _ = -(∫ η, X a b η i * f (η a) ∂P) := integral_neg _

/-- The initial endpoint pairing is half the negative increment pairing. -/
theorem integral_increment_mul_eval_difference (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) {a b : ℝ} (hab : a ≤ b)
    (i : Fin d) (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    2 * (∫ η, X a b η i * f (η a) ∂P) =
      -(∫ η, X a b η i * (f (η b) - f (η a)) ∂P) := by
  obtain ⟨C, hC⟩ := hfb
  have hi : Integrable (fun η => X a b η i) P := (hX.integrable a b hab).eval i
  have hp (t : ℝ) : Integrable (fun η => X a b η i * f (η t)) P :=
    hi.mul_bdd (hf.comp (continuous_eval_const t).measurable).aestronglyMeasurable
      (ae_of_all _ fun η => by simpa only [Real.norm_eq_abs] using hC (η t))
  have he := integral_increment_mul_eval_end hP hX hab i f hf ⟨C, hC⟩
  have hs : (∫ η, X a b η i * (f (η b) - f (η a)) ∂P) =
      (∫ η, X a b η i * f (η b) ∂P) -
        (∫ η, X a b η i * f (η a) ∂P) := by
    simp_rw [mul_sub]
    exact integral_sub (hp b) (hp a)
  rw [hs, he]
  ring

end EinsteinFull.External.DFGW
