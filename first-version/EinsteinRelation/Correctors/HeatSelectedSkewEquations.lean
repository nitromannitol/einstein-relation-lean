import EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport
import EinsteinRelation.Correctors.PlanarFluxCorrector
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Calculus.WeakGradientUniqueness

/-! # Spatial equations of a heat-selected skew corrector

Source: `paper/main.tex:694–708,740–766,948–955`. These lemmas consume
the source selection predicate; existence of the selected potential remains
a separate obligation. In dimension two, its selected gradient is identified
with the rotated canonical centered flux by uniqueness of weak derivatives.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Almost-everywhere skewness suffices for the planar weak-gradient identity.
Source: `paper/main.tex:948–955`. -/
theorem hasWeakGradient_planar_skew_entry_of_ae {U : Set (Vec 2)}
    (hU : IsOpen U) (S : Vec 2 → Mat 2) (q : Vec 2 → Vec 2)
    (hS : ∀ᵐ x ∂volume.restrict U, (S x).transpose = -(S x))
    (hdiv : HasWeakRowDivergence U S q) :
    HasWeakGradient U (fun x => S x 0 1) (fun x => ![-q x 1, q x 0]) := by
  let T : Vec 2 → Mat 2 := fun x => (1 / 2 : ℝ) • (S x - (S x).transpose)
  have hT (x : Vec 2) : (T x).transpose = -(T x) := by
    ext j k
    simp only [T, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sub_apply, Matrix.neg_apply]
    ring
  have hTS : T =ᵐ[volume.restrict U] S := by
    filter_upwards [hS] with x hx
    dsimp only [T]
    rw [hx]
    ext j k
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.neg_apply]
    ring
  have hTdiv := hasWeakRowDivergence_congr_ae hU hdiv hTS.symm
    (Filter.EventuallyEq.rfl : q =ᵐ[volume.restrict U] q)
  exact hasWeakGradient_congr_ae hU (hasWeakGradient_planar_skew_entry T q hT hTdiv)
    (hTS.mono fun _ hx => congrFun (congrFun hx 0) 1) Filter.EventuallyEq.rfl

namespace HeatSelectedSkewMeaning

/-- Stationarity and the canonical flux's `L²` membership supply all local
integrability needed for the source divergence equation.
Source: `paper/main.tex:694–708,740–743`. -/
theorem ae_centeredFlux_locallyIntegrable {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ j : Fin d,
      LocallyIntegrableOn
        (fun x : Vec d => (canonicalCorrectorFlux Q i (translate x ρ) -
          expectedCorrectorFlux Q i).ofLp j) Set.univ volume := by
  filter_upwards [StationarySpatialRealization.ae_spatialRealization_memLp_on_all_compacts
    (reducedEnvironmentLaw_stationary Q) (canonicalCorrectorFlux Q i)] with ρ hρ
  intro j
  apply LocallyIntegrable.locallyIntegrableOn
  rw [locallyIntegrable_iff]
  intro K hK
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hc := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).comp_memLp'
    (hρ K hK)
  exact (hc.sub (memLp_const ((expectedCorrectorFlux Q i).ofLp j))).integrable
    (by norm_num)

/-- The source identities and a genuine weak-gradient representative yield
the production spatial row-divergence predicate.
Source: `paper/main.tex:740–766,948–955`. -/
theorem HasSourceSkewCorrectorColumnAt.hasWeakRowDivergence {d : ℕ}
    {hd : 2 ≤ d} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {σ : FieldPair d → Vec d → Mat d} {ρ : FieldPair d}
    {F : FieldPair d → Fin d → Fin d → Fin d → ℝ}
    (hsource : HasSourceSkewCorrectorColumnAt hd Q i σ ρ)
    (hgradient : HasSelectedHeatGradientRepresentative (σ ρ) F ρ)
    (hflux : ∀ j : Fin d, LocallyIntegrableOn
      (fun x : Vec d => (canonicalCorrectorFlux Q i (translate x ρ) -
        expectedCorrectorFlux Q i).ofLp j) Set.univ volume) :
    HasWeakRowDivergence Set.univ (σ ρ)
      (fun x => (canonicalCorrectorFlux Q i (translate x ρ) -
        expectedCorrectorFlux Q i).ofLp) := by
  let k₀ : Fin d := ⟨0, by omega⟩
  intro j
  refine ⟨fun k => (hgradient j k k₀).1, hflux j, ?_⟩
  intro ψ hψ
  have h := (hsource.2.1 ψ hψ.1 hψ.2.1 j).2.2
  simp only [Measure.restrict_univ, dot, gradient]
  dsimp only at h
  linarith

/-- A heat-selected source skew potential has the literal spatial
row-divergence equation on one event for all tests.
Source: `paper/main.tex:740–766,948–955`. -/
theorem HasHeatSelectedSkewCorrectorColumn.ae_hasWeakRowDivergence {d : ℕ}
    {hd : 2 ≤ d} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {σ : FieldPair d → Vec d → Mat d}
    (hσ : HasHeatSelectedSkewCorrectorColumn hd Q i σ) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q, HasWeakRowDivergence Set.univ (σ ρ)
      (fun x => (canonicalCorrectorFlux Q i (translate x ρ) -
        expectedCorrectorFlux Q i).ofLp) := by
  obtain ⟨F, _, hF⟩ := hσ
  filter_upwards [hF, ae_centeredFlux_locallyIntegrable Q i] with ρ hρ hflux
  exact hρ.1.hasWeakRowDivergence hρ.2.2 hflux

/-- In dimension two the skew entry has exactly the rotated canonical
centered flux as weak gradient. Source: `paper/main.tex:948–955`. -/
theorem HasHeatSelectedSkewCorrectorColumn.ae_planar_weakGradient
    {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw 2 Λ₀ r₀} {i : Fin 2}
    {σ : FieldPair 2 → Vec 2 → Mat 2}
    (hσ : HasHeatSelectedSkewCorrectorColumn (by omega) Q i σ) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
      HasWeakGradient Set.univ (fun x => σ ρ x 0 1)
        (fun x => ![-(canonicalCorrectorFlux Q i (translate x ρ) -
          expectedCorrectorFlux Q i).ofLp 1,
          (canonicalCorrectorFlux Q i (translate x ρ) -
            expectedCorrectorFlux Q i).ofLp 0]) := by
  obtain ⟨F, _, hF⟩ := hσ
  filter_upwards [hF, ae_centeredFlux_locallyIntegrable Q i] with ρ hρ hflux
  exact hasWeakGradient_planar_skew_entry_of_ae isOpen_univ _ _
    (by simpa only [Measure.restrict_univ] using hρ.1.1)
    (hρ.1.hasWeakRowDivergence hρ.2.2 hflux)

/-- The selected planar gradient itself, rather than a newly chosen gradient,
agrees spatially almost everywhere with the rotated canonical flux.
Source: `paper/main.tex:948–955`. -/
theorem HasSelectedHeatGradientRepresentative.planar_ae_eq_rotatedFlux
    {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw 2 Λ₀ r₀} {i : Fin 2}
    {σ : FieldPair 2 → Vec 2 → Mat 2} {ρ : FieldPair 2}
    {F : FieldPair 2 → Fin 2 → Fin 2 → Fin 2 → ℝ}
    (hgradient : HasSelectedHeatGradientRepresentative (σ ρ) F ρ)
    (hsource : HasSourceSkewCorrectorColumnAt (by omega) Q i σ ρ)
    (hflux : ∀ j : Fin 2, LocallyIntegrableOn
      (fun x : Vec 2 => (canonicalCorrectorFlux Q i (translate x ρ) -
        expectedCorrectorFlux Q i).ofLp j) Set.univ volume) :
    (fun x k => F (translate x ρ) 0 1 k) =ᵐ[volume]
      (fun x => ![-(canonicalCorrectorFlux Q i (translate x ρ) -
        expectedCorrectorFlux Q i).ofLp 1,
        (canonicalCorrectorFlux Q i (translate x ρ) -
          expectedCorrectorFlux Q i).ofLp 0]) := by
  exact (hgradient 0 1).ae_eq_of_same_potential
    (hasWeakGradient_planar_skew_entry_of_ae isOpen_univ _ _
      (by simpa only [Measure.restrict_univ] using hsource.1)
      (hsource.hasWeakRowDivergence hgradient hflux))

end HeatSelectedSkewMeaning
end EinsteinRelation.Correctors
