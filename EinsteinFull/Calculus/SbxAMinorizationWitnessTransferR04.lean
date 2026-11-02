import EinsteinFull.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.Calculus.SbxS3CleanKernelPatchingR02

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP
open scoped NNReal

noncomputable section
namespace EinsteinFull.Blueprint

/-- Almost-everywhere all-start equality preserves the source minorization in
both directions, with the same time, coin coefficient, radius and direction. -/
theorem source_minorization_ae_iff_of_all_start_eq
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (P P' : QuenchedPathLaws d) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (heq : ∀ᵐ ω ∂Q.measure, ∀ x, P (x, ω) = P' (x, ω)) :
    (∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω)) Δ δ R i) ↔
    (∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P' (x, ω)) Δ δ R i) := by
  constructor <;> intro h
  · filter_upwards [heq, h] with ω he hω
    have hf : (fun x => P (x, ω)) = (fun x => P' (x, ω)) := funext he
    rwa [← hf]
  · filter_upwards [heq, h] with ω he hω
    have hf : (fun x => P (x, ω)) = (fun x => P' (x, ω)) := funext he
    rwa [hf]

/-- A source minorization of one actual reduced kernel transfers to any other
supplied reduced kernel, simultaneously for every start. -/
theorem source_minorization_transfer_supplied_kernel
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (μ : ℝ) (h0 : 0 ≤ μ) (h1 : μ ≤ 1)
    (P P' : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0 h1 P)
    (hP' : IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0 h1 P')
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hminor : ∀ᵐ ω ∂Q.measure,
      HasSourceMinorization (fun x => P (x, ω)) Δ δ R i) :
    ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P' (x, ω)) Δ δ R i :=
  (source_minorization_ae_iff_of_all_start_eq Q P P' Δ δ R i
    (EinsteinFull.s6_supplied_reduced_kernel_pathLaw_unique hd Q μ h0 h1 P P' hP hP')).mp hminor

/-- A single actual reduced-kernel witness for each law and positive force,
with the coin parameter selected before the law and force, supplies the
uniform minorization required by the coupling construction. -/
theorem uniform_source_minorization_of_one_witness
    (h : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      ∀ l : ℝ, 1 ≤ l → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1),
        ∃ P : QuenchedPathLaws d,
          IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0.le h1 P ∧
          ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω))
            (Renewal.regenDelta μ) δ (l / μ) (Renewal.forceCoord hd)) :
    SbxS1CouplingAssemblyR02.UniformSourceMinorization := by
  intro d hd Λ₀ r₀ l hl
  obtain ⟨δ, hδ0, hδ1, hw⟩ := h d hd Λ₀ r₀ l hl
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro Q μ h0 h1 P hP
  obtain ⟨P', hP', hm⟩ := hw Q μ h0 h1
  exact source_minorization_transfer_supplied_kernel hd Q μ h0.le h1 P' P hP' hP
    _ δ _ _ hm

/-- The transfer also applies to the positive auxiliary force of any nonzero
signed force in the full range. -/
theorem source_minorization_transfer_supplied_kernel_abs
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h1 : |lam| ≤ 1) (P P' : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| (abs_nonneg lam) h1 P)
    (hP' : IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| (abs_nonneg lam) h1 P')
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hminor : ∀ᵐ ω ∂Q.measure,
      HasSourceMinorization (fun x => P (x, ω)) Δ δ R i) :
    ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P' (x, ω)) Δ δ R i :=
  source_minorization_transfer_supplied_kernel hd Q |lam| (abs_nonneg lam) h1
    P P' hP hP' Δ δ R i hminor


/-- Transfer from a witness and patch the supplied kernel, preserving the
same coefficient on every environment row of the resulting Markov kernel. -/
theorem patch_supplied_kernel_of_minorization_witness
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (μ : ℝ) (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (P P' : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0 h1 P)
    (hP' : IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0 h1 P')
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hminor : ∀ᵐ ω ∂Q.measure,
      HasSourceMinorization (fun x => P (x, ω)) Δ δ R i) :
    ∃ P'' : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, ∀ x, P'' (x, ω) = P' (x, ω)) ∧
      IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0 h1 P'' ∧
      IsMarkovKernel P'' ∧
      (∀ a, ∀ᵐ γ ∂P'' a, γ 0 = a.1) ∧
      (∀ ω, HasSourceMinorization (fun x => P'' (x, ω)) Δ δ R i) := by
  apply SbxS3Section3R01.clean_patch_reduced_kernel hd Q μ h0 h1 Δ δ R i P' hP'
  exact source_minorization_transfer_supplied_kernel hd Q μ h0 h1 P P' hP hP'
    Δ δ R i hminor

/-- The uniform positive-force contract applies to the absolute value of any
nonzero signed force without changing its structural coin coefficient. -/
theorem uniform_source_minorization_abs
    (h : SbxS1CouplingAssemblyR02.UniformSourceMinorization)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ) (hl : 1 ≤ l) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < |lam|) (h1 : |lam| ≤ 1)
        (P : QuenchedPathLaws d),
        IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω))
          (Renewal.regenDelta |lam|) δ (l / |lam|) (Renewal.forceCoord hd) := by
  obtain ⟨δ, hδ0, hδ1, hminor⟩ := h d hd Λ₀ r₀ l hl
  exact ⟨δ, hδ0, hδ1, fun Q lam h0 h1 P hP => hminor Q |lam| h0 h1 P hP⟩

end EinsteinFull.Blueprint
