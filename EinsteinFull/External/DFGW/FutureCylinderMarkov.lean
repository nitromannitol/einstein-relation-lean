import EinsteinFull.External.DFGW.FutureCylinder

/-! # Markov property for future cylinders

The conditional expectation of any bounded ordered cylinder depends only on the current state
and is computed by successive transition kernels.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The conditional expectation of an ordered future cylinder is its iterated kernel
expectation evaluated at the current state. -/
theorem condExp_futureCylinder (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (xs : List (ℝ≥0 × (S → ℝ))) (hxs : FutureCylinderAdmissible xs) (s : ℝ) :
    P[futureCylinder xs s | Draft.dfgwCoordSigma (Set.Iic s)] =ᵐ[P]
      fun η : C(ℝ, S) => futureCylinderKernel T xs (η s) := by
  let : IsProbabilityMeasure P := hP.probability
  have hpast (u : ℝ) : Draft.dfgwCoordSigma (S := S) (Set.Iic u) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := by
    exact iSup₂_le fun v _ => (continuous_eval_const v).measurable.comap_le
  induction xs generalizing s with
  | nil =>
    simpa only [futureCylinder, futureCylinderKernel] using
      (condExp_const (μ := P) (hpast s) (1 : ℝ)).eventuallyEq
  | cons p xs ih =>
    obtain ⟨t, f⟩ := p
    obtain ⟨hfm, D, hD⟩ := hxs (t, f) (by simp)
    have htail : FutureCylinderAdmissible xs := fun p hp => hxs p (by simp [hp])
    obtain ⟨⟨hkm, C, hC⟩, hpath⟩ := futureCylinder_measurable_bounded hP xs htail
    let u : ℝ := (t : ℝ) + s
    have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic s) ≤
        Draft.dfgwCoordSigma (Set.Iic u) := by
      apply iSup₂_le
      intro v hv
      exact le_iSup₂_of_le (f := fun v (_ : v ∈ Set.Iic u) =>
        MeasurableSpace.comap (fun η : C(ℝ, S) => η v) inferInstance) v
        (by change v ≤ u; have : v ≤ s := hv; dsimp [u]; linarith [t.coe_nonneg]) le_rfl
    have heval : Measurable[Draft.dfgwCoordSigma (S := S) (Set.Iic u)]
        (fun η : C(ℝ, S) => η u) := by
      apply Measurable.of_comap_le
      exact le_iSup₂_of_le (f := fun v (_ : v ∈ Set.Iic u) =>
        MeasurableSpace.comap (fun η : C(ℝ, S) => η v) inferInstance)
        u (by change u ≤ u; exact le_rfl) le_rfl
    let A : C(ℝ, S) → ℝ := fun η => f (η u)
    let B : C(ℝ, S) → ℝ := futureCylinder xs u
    have hA : StronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic u)] A :=
      (hfm.comp heval).stronglyMeasurable
    obtain ⟨hBm, E, hE⟩ := hpath u
    have hB : Integrable B P := Integrable.of_bound hBm.aestronglyMeasurable E
      (ae_of_all P fun η => by simpa only [B, Real.norm_eq_abs] using hE η)
    have hAB : Integrable (A * B) P := by
      have h := hB.mul_bdd (hfm.comp (continuous_eval_const u).measurable).aestronglyMeasurable
        (ae_of_all P fun η => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hD (η u))
      exact h.congr (ae_of_all P fun η => by simp only [Pi.mul_apply, A, B, Function.comp_apply, mul_comm])
    have hpull := condExp_mul_of_stronglyMeasurable_left hA hAB hB
    have htailmark := ih htail u
    have hstep : P[A * B | Draft.dfgwCoordSigma (Set.Iic u)] =ᵐ[P]
        fun η : C(ℝ, S) => f (η u) * futureCylinderKernel T xs (η u) := by
      filter_upwards [hpull, htailmark] with η hp hm
      simpa only [Pi.mul_apply, A, B] using hp.trans (congrArg (fun z => f (η u) * z) hm)
    let F : S → ℝ := fun x => f x * futureCylinderKernel T xs x
    have hF : Measurable F := hfm.mul hkm
    have hFb : ∃ K, ∀ x, |F x| ≤ K := by
      refine ⟨D * C, fun x => ?_⟩
      change |f x * futureCylinderKernel T xs x| ≤ D * C
      rw [abs_mul]
      exact mul_le_mul (hD x) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hD x))
    have htower := condExp_condExp_of_le (μ := P) (f := A * B) hσ (hpast u)
    have hcongr := condExp_congr_ae (m := Draft.dfgwCoordSigma (Set.Iic s)) hstep
    have hmark := condExp_shifted hP s t F hF hFb
    exact htower.symm.trans (hcongr.trans hmark)

end EinsteinFull.External.DFGW
