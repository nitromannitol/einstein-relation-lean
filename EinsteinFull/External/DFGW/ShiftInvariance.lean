import EinsteinFull.External.DFGW.Trajectory

/-! # Time-shift invariance

Invariance under one time shift implies invariance under its positive and negative integer
multiples.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

omit [MeasurableSpace S] [BorelSpace S] in
/-- Two trajectory shifts compose by addition of their time parameters. -/
theorem shift_shift (s t : ℝ) (η : C(ℝ, S)) :
    Draft.dfgwShift s (Draft.dfgwShift t η) = Draft.dfgwShift (s + t) η := by
  ext u
  simp only [Draft.dfgwShift, ContinuousMap.coe_comp, ContinuousMap.coe_mk, Function.comp_apply]
  congr 1
  ring

omit [MeasurableSpace S] [BorelSpace S] in
/-- The zero trajectory shift is the identity. -/
theorem shift_zero (η : C(ℝ, S)) : Draft.dfgwShift 0 η = η := by
  ext u
  simp [Draft.dfgwShift]

omit [BorelSpace S] in
/-- Almost-everywhere invariance under one shift extends to every grid iterate in both directions. -/
theorem ae_grid_shift_invariant (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : C(ℝ, S) → ℝ) (t : ℝ≥0)
    (hinv : f ∘ Draft.dfgwShift t =ᵐ[P] f) :
    (∀ n : ℕ, f ∘ Draft.dfgwShift (((n • t : ℝ≥0) : ℝ)) =ᵐ[P] f) ∧
      (∀ n : ℕ, f ∘ Draft.dfgwShift (-((n • t : ℝ≥0) : ℝ)) =ᵐ[P] f) := by
  have hplus : ∀ n : ℕ, f ∘ Draft.dfgwShift (((n • t : ℝ≥0) : ℝ)) =ᵐ[P] f := by
    intro n
    induction n with
    | zero =>
      exact ae_of_all P fun η => by simp only [zero_nsmul, NNReal.coe_zero, Function.comp_apply, shift_zero]
    | succ n ih =>
      have hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
        ⟨measurable_shift _, hP.stationary _⟩
      have hprev := hshift.quasiMeasurePreserving.ae ih
      filter_upwards [hprev, hinv] with η hp hi
      simp only [Function.comp_apply] at hp hi ⊢
      rw [shift_shift] at hp
      simpa only [succ_nsmul, NNReal.coe_add, add_comm] using hp.trans hi
  refine ⟨hplus, ?_⟩
  intro n
  let u : ℝ := ((n • t : ℝ≥0) : ℝ)
  have hshift : MeasurePreserving (Draft.dfgwShift (S := S) (-u)) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  have h := hshift.quasiMeasurePreserving.ae (hplus n)
  filter_upwards [h] with η hη
  change f (Draft.dfgwShift u (Draft.dfgwShift (-u) η)) = f (Draft.dfgwShift (-u) η) at hη
  rw [shift_shift, add_neg_cancel, shift_zero] at hη
  exact hη.symm

end EinsteinFull.External.DFGW
