import EinsteinRelation.Correctors.ScalarMomentAverage

/-! # Marginal flow moments under the actual coefficient coupling

Source: `paper/main.tex:817–855`. The two copies need not be independent:
measure-preserving marginals suffice for the space-time RMS difference
bound used in the paired energy estimate.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:817–855`. Marginal moment bounds control the
root-mean-square difference under any coupling, with no independence premise. -/
theorem coupled_scalarL2_average_moment_le {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (μ : Measure (Ω × Ω)) [IsProbabilityMeasure μ]
    (hfst : MeasurePreserving Prod.fst μ Q)
    (hsnd : MeasurePreserving Prod.snd μ Q)
    (ν : Measure X) [IsProbabilityMeasure ν]
    {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C)
    (f : Ω × X → ℝ) (hf : Measurable f)
    (hmom : ∀ x, MemLp (fun ω => f (ω, x)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => f (ω, x)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) :
    (∀ᵐ z ∂μ, MemLp (fun x => f (z.1, x) - f (z.2, x)) 2 ν) ∧
      MemLp (fun z => Real.sqrt (∫ x, (f (z.1, x) - f (z.2, x)) ^ 2 ∂ν))
        (ENNReal.ofReal p) μ ∧
      eLpNorm (fun z => Real.sqrt (∫ x, (f (z.1, x) - f (z.2, x)) ^ 2 ∂ν))
        (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (2 * C) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    calc
      1 = ENNReal.ofReal (1 : ℝ) := by rw [ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal (show 1 ≤ p from by linarith)
  have h2C : 0 ≤ 2 * C := by nlinarith
  let g : (Ω × Ω) × X → ℝ := fun zx => f (zx.1.1, zx.2) - f (zx.1.2, zx.2)
  have hg : Measurable g := by
    unfold g
    refine (hf.comp ?_).sub (hf.comp ?_)
    · refine ((measurable_fst (α := Ω) (β := Ω)).comp
        (measurable_fst (α := Ω × Ω) (β := X))).prodMk ?_
      exact measurable_snd (α := Ω × Ω) (β := X)
    · refine ((measurable_snd (α := Ω) (β := Ω)).comp
        (measurable_fst (α := Ω × Ω) (β := X))).prodMk ?_
      exact measurable_snd (α := Ω × Ω) (β := X)
  have hg_mom (x : X) : MemLp (fun z : Ω × Ω => g (z, x)) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun z : Ω × Ω => g (z, x)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (2 * C) := by
    have h1 : MemLp (fun z : Ω × Ω => f (z.1, x)) (ENNReal.ofReal p) μ :=
      (hmom x).1.comp_measurePreserving hfst
    have h2 : MemLp (fun z : Ω × Ω => f (z.2, x)) (ENNReal.ofReal p) μ :=
      (hmom x).1.comp_measurePreserving hsnd
    have hmem : MemLp (fun z : Ω × Ω => g (z, x)) (ENNReal.ofReal p) μ :=
      h1.sub h2
    have hnorm1 : eLpNorm (fun z : Ω × Ω => f (z.1, x)) (ENNReal.ofReal p) μ =
        eLpNorm (fun ω : Ω => f (ω, x)) (ENNReal.ofReal p) Q :=
      eLpNorm_comp_measurePreserving (hmom x).1.aestronglyMeasurable hfst
    have hnorm2 : eLpNorm (fun z : Ω × Ω => f (z.2, x)) (ENNReal.ofReal p) μ =
        eLpNorm (fun ω : Ω => f (ω, x)) (ENNReal.ofReal p) Q :=
      eLpNorm_comp_measurePreserving (hmom x).1.aestronglyMeasurable hsnd
    refine ⟨hmem, ?_⟩
    calc
      eLpNorm (fun z : Ω × Ω => g (z, x)) (ENNReal.ofReal p) μ ≤
          eLpNorm (fun z : Ω × Ω => f (z.1, x)) (ENNReal.ofReal p) μ +
          eLpNorm (fun z : Ω × Ω => f (z.2, x)) (ENNReal.ofReal p) μ :=
        eLpNorm_sub_le h1.aestronglyMeasurable h2.aestronglyMeasurable hp1
      _ = eLpNorm (fun ω : Ω => f (ω, x)) (ENNReal.ofReal p) Q +
          eLpNorm (fun ω : Ω => f (ω, x)) (ENNReal.ofReal p) Q := by
        rw [hnorm1, hnorm2]
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := by
        gcongr
        · exact (hmom x).2
        · exact (hmom x).2
      _ = ENNReal.ofReal (C + C) := by rw [ENNReal.ofReal_add hC hC]
      _ = ENNReal.ofReal (2 * C) := by congr 1; ring
  have h := scalarL2_average_moment_le μ ν (by linarith) h2C g hg hg_mom
  simpa [g] using h

end EinsteinRelation.Correctors
