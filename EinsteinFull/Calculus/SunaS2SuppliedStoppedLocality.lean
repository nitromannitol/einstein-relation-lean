import EinsteinFull.Calculus.SunaS2RationalStoppedLaw
import EinsteinFull.Calculus.SunaS7SuppliedKilledFDD
import EinsteinFull.Calculus.SunaS6KilledEveryStartLocality
open MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal Topology
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Regeneration
/-- Locality of supplied stopped laws in a shifted future half-space. -/
theorem s2_shifted_supplied_stopped_locality
    {d : ℕ}
    (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ)
    (hl : 0 < l)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d)
    (_hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K)
    : let R := l / lam;
    let i := Renewal.forceCoord hd;
    ∀ (a : Vec d) (ω ω' : FieldPair d)
    (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
    (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y)
    → (∀ y : Vec d, P (y, ω') = r'.pathLaw y)
    → (∀ y : Vec d, a i - 2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    → ∀ y : Vec d, a i - R ≤ y i → (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | a i - 2 * R < x i}) = (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | a i - 2 * R < x i}) := by
  have hk : S2SuppliedKilledFDDLocality :=
    s7_supplied_killed_fdd_locality_of_endpoint_locality
      (fun hd L hL ω ω' hω hω' lam h0 h1 G G' U hU hag t =>
        s6_supplied_killed_endpoint_eq_of_local_coefficients hd L hL ω ω' hω hω'
          lam h0 h1 G G' U hU hag t)
  exact s2_shifted_future_supplied_stopped_locality_of_killed_fdd hk hd hΛ₀ Q lam l δ hl h0 h1 P K _hK


/-- Locality of supplied stopped laws in the future half-space. -/
theorem s2_future_supplied_stopped_locality
    {d : ℕ}
    (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ)
    (hl : 0 < l)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d)
    (_hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K)
    : let R := l / lam;
    let i := Renewal.forceCoord hd;
    ∀ (ω ω' : FieldPair d)
    (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
    (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y)
    → (∀ y : Vec d, P (y, ω') = r'.pathLaw y)
    → (∀ y : Vec d, -2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    → ∀ y : Vec d, -R ≤ y i → (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) = (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) := by
  have hk : S2SuppliedKilledFDDLocality :=
    s7_supplied_killed_fdd_locality_of_endpoint_locality
      (fun hd L hL ω ω' hω hω' lam h0 h1 G G' U hU hag t =>
        s6_supplied_killed_endpoint_eq_of_local_coefficients hd L hL ω ω' hω hω'
          lam h0 h1 G G' U hU hag t)
  exact s2_future_supplied_stopped_locality_of_killed_fdd hk hd hΛ₀ Q lam l δ hl h0 h1 P K _hK

/-- Locality of supplied stopped laws in the past half-space. -/
theorem s2_past_supplied_stopped_locality
    {d : ℕ}
    (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ)
    (hl : 0 < l)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d)
    (_hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K)
    (v : ℝ)
    : let R := l / lam;
    let i := Renewal.forceCoord hd;
    ∀ (ω ω' : FieldPair d)
    (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
    (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y)
    → (∀ y : Vec d, P (y, ω') = r'.pathLaw y)
    → (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    → ∀ y : Vec d, y i ≤ v → (r.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R}) = (r'.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R}) := by
  have hk : S2SuppliedKilledFDDLocality :=
    s7_supplied_killed_fdd_locality_of_endpoint_locality
      (fun hd L hL ω ω' hω hω' lam h0 h1 G G' U hU hag t =>
        s6_supplied_killed_endpoint_eq_of_local_coefficients hd L hL ω ω' hω hω'
          lam h0 h1 G G' U hU hag t)
  exact s2_past_supplied_stopped_locality_of_killed_fdd hk hd hΛ₀ Q lam l δ hl h0 h1 P K _hK v

end EinsteinFull

