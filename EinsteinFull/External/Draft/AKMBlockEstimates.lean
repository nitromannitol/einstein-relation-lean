import EinsteinFull.External.Source.AKMSelectedLocalizedEnergy

open MeasureTheory

namespace EinsteinFull.External.Draft
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM

/-- DRAFT graph leaf external:AKM#5.29i. Source Lemma5.29(i), (5.90),
printed p.222. This is the genuine centered quadratic energy, without matrix
polarization, physical rescaling, a clock coordinate or an L2 transfer.
The source r>=1 range is restricted to the explicit construction's r>=2. -/
def akmBlockCltStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (K s δ γ η : ℝ) (hK : 1 < K), ∀ h : blockParameterWindow d s δ γ η,
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Measure (Coefficient d K)) (hP : LawHypotheses P),
      let J := sourceSelectedLocalizedEnergy d hd K s δ γ hK
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 P hP
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ η ≤ r → r ≤ R →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
      OsBound P (fun a => |sourceCenteredBlock P J a z R r f p q|)
        s (C * R ^ (-(d : ℝ) / 2))

/-- DRAFT graph leaf external:AKM#5.29ii. Source Lemma5.29(ii),
(5.91)--(5.92), printed p.223. The allowed smoothing interval is
[R^(beta*eta), R^(beta/(1+delta))]; the integral uses the outer cube's volume.
No estimate is asserted for a clock coordinate or a joint matrix block. -/
def akmBlockBoundaryStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (K s δ γ η : ℝ) (hK : 1 < K), ∀ h : blockParameterWindow d s δ γ η,
    ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Measure (Coefficient d K)) (hP : LawHypotheses P),
      let J := sourceSelectedLocalizedEnergy d hd K s δ γ hK
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 P hP
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ (β * η) ≤ r →
        r ≤ R ^ (β / (1 + δ)) →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
        Function.support f ⊆ sourceBlockCube z R \ sourceBlockCube z (R - R ^ β) →
      OsBound P (fun a => |sourceCenteredBlock P J a z R r f p q|)
        s (C * R ^ (-(d : ℝ) / 2 - (1 - β) / 2))

/-- DRAFT graph leaf external:AKM#5.29iii. Source Lemma5.29(iii), printed
p.223. The positive gain is chosen before ellipticity K, as in the source.
Both terms use the SAME centered source family; this is an Os bound on the
volume average, not a Gaussian or joint covariance conclusion. -/
def akmBlockChangeStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (s δ γ η : ℝ),
    ∀ h : blockParameterWindow d s δ γ η,
    ∀ β : ℝ, η ≤ β → β < 1 →
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (K : ℝ) (hK : 1 < K), ∃ C : ℝ, 0 < C ∧
    ∀ (P : Measure (Coefficient d K)) (hP : LawHypotheses P),
      let J := sourceSelectedLocalizedEnergy d hd K s δ γ hK
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 P hP
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ R ^ η → R ^ η ≤ r → r ≤ R ^ β →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      OsBound P (fun a => |sourceCenteredBlock P J a z R r (fun _ => 1) p q -
          sourceCenteredBlock P J a z R (R ^ η) (fun _ => 1) p q|)
        s (C * R ^ (-(d : ℝ) / 2 - ε))

end EinsteinFull.External.Draft
