import EinsteinFull.External.DFGW.ReflectionPairing
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Forward velocity pairings

Conditional expectation transfers a pairing with the initial state from an increment to its
conditional forward increment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Pairing a conditional increment with an initial-state observable leaves its integral unchanged. -/
theorem integral_condExp_increment_mul_eval (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin d) (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    (∫ η, (P[X 0 t | Draft.dfgwCoordSigma (Set.Iic 0)]) η i * f (η 0) ∂P) =
      ∫ η, X 0 t η i * f (η 0) ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨C, hC⟩ := hfb
  have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le 0
  have hzero : Measurable[Draft.dfgwCoordSigma (S := S) (Set.Iic 0)]
      (fun η : C(ℝ, S) => η 0) := by
    apply Measurable.of_comap_le
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic _) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) (0 : ℝ) (by change (0 : ℝ) ≤ 0; exact le_rfl) le_rfl
  have hfpast : StronglyMeasurable[Draft.dfgwCoordSigma (S := S) (Set.Iic 0)]
      (fun η : C(ℝ, S) => f (η 0)) := (hf.comp hzero).stronglyMeasurable
  have hi : Integrable (fun η => X 0 t η i) P := (hX.integrable 0 t ht).eval i
  have hp : Integrable ((fun η => X 0 t η i) * (fun η : C(ℝ, S) => f (η 0))) P := by
    have h := hi.mul_bdd (hf.comp (continuous_eval_const 0).measurable).aestronglyMeasurable
      (ae_of_all P fun η => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hC (η 0))
    exact h.congr (ae_of_all P fun _ => rfl)
  have hc := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_condExp_comm
    (m := Draft.dfgwCoordSigma (Set.Iic 0)) (hX.integrable 0 t ht)
  have hfn : (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) ∘ X 0 t) =
      (fun η => X 0 t η i) := by ext η; rfl
  rw [hfn] at hc
  have hmul := condExp_mul_of_stronglyMeasurable_right hfpast hp hi
  have hint := integral_condExp (μ := P) (f := (fun η => X 0 t η i) *
    (fun η : C(ℝ, S) => f (η 0))) hσ
  calc
    (∫ η, (P[X 0 t | Draft.dfgwCoordSigma (Set.Iic 0)]) η i * f (η 0) ∂P) =
        ∫ η, (P[fun η => X 0 t η i | Draft.dfgwCoordSigma (Set.Iic 0)]) η * f (η 0) ∂P := by
      apply integral_congr_ae
      filter_upwards [hc] with η hη
      simpa only [Function.comp_apply, ContinuousLinearMap.proj_apply] using congrArg
        (fun z : ℝ => z * f (η 0)) hη
    _ = ∫ η, (P[(fun η => X 0 t η i) * (fun η : C(ℝ, S) => f (η 0)) |
        Draft.dfgwCoordSigma (Set.Iic 0)]) η ∂P := by
      apply integral_congr_ae
      filter_upwards [hmul] with η hη
      simpa only [Pi.mul_apply] using hη.symm
    _ = ∫ η, X 0 t η i * f (η 0) ∂P := by simpa only [Pi.mul_apply] using hint

end EinsteinFull.External.DFGW
