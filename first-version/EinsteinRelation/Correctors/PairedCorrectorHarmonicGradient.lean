import EinsteinRelation.Correctors.AKMHarmonicGradient
import EinsteinRelation.Correctors.PairedCorrectorEquation
import EinsteinRelation.Correctors.RandomRadiusPointwiseMoments

/-! # The harmonic estimate for two locally agreeing correctors

Source: `paper/main.tex:861–867`. The homogeneous equation is obtained
by subtracting the two actual corrector equations. The random radius is
selected from the first marginal law, before the coupling and solutions.
The pointwise representative regularity remains explicit.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport

/-- Local coefficient agreement cancels the common slope, producing the
literal AKM harmonic pair. Source: `paper/main.tex:861–867`. -/
theorem paired_corrector_isHarmonic {d : ℕ} {K R : ℝ}
    {a₁ a₂ : Coefficient d K}
    (ha : Set.EqOn (fun x => a₁ x) (fun x => a₂ x) (originBall d R)) (e : Vec d)
    {φ₁ φ₂ : Vec d → ℝ} {G₁ G₂ : Vec d → Vec d}
    (hφ₁ : MemLp φ₁ 2 (volume.restrict (originBall d R)))
    (hφ₂ : MemLp φ₂ 2 (volume.restrict (originBall d R)))
    (hG : MemLp (fun x => euclideanNorm (G₁ x - G₂ x)) 2
      (volume.restrict (originBall d R)))
    (hgrad₁ : HasWeakGradient (originBall d R) φ₁ G₁)
    (hgrad₂ : HasWeakGradient (originBall d R) φ₂ G₂)
    (hdiv₁ : HasWeakDivergence (originBall d R)
      (fun x => (a₁ x).mulVec (e + G₁ x)) (fun _ => 0))
    (hdiv₂ : HasWeakDivergence (originBall d R)
      (fun x => (a₂ x).mulVec (e + G₂ x)) (fun _ => 0)) :
    IsHarmonic a₁ R (fun x => φ₁ x - φ₂ x) (fun x => G₁ x - G₂ x) := by
  have hU : IsOpen (originBall d R) := by
    rw [originBall_eq_gt_ball]
    exact paired_isOpen_ball 0 R
  have hp := paired_corrector_harmonic hU ha e hgrad₁ hgrad₂ hdiv₁ hdiv₂
  exact ⟨hφ₁.sub hφ₂, hG, hp⟩

/-- AKM's first-field radius controls the paired corrector gradient on
any coupling having that first marginal. No independence or second-field
regularity is needed. The `C1Alpha` condition concerns the actual difference
whose point gradient appears in the conclusion.
Source: `paper/main.tex:861–867`. -/
theorem ellipticLargeScale_paired_corrector_gradient_origin
    (hAKM : EllipticLargeScale)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hP : BallPoincareEstimate)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hsd : s < d)
    {lam Λ H α : ℝ} (hlam : 0 < lam) (hΛ : 0 < Λ)
    (hH : 0 < H) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
        ∃ X : Coefficient d K → ℝ, Measurable X ∧ (∀ A, 1 ≤ X A) ∧
          StretchedExponentialBound P s C₀ X ∧
          ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
            (a₁ a₂ : Ω → Coefficient d K), MeasurePreserving a₁ ν P →
            ∀ᵐ ω ∂ν, ∀ R : ℝ, X (a₁ ω) ≤ R →
              ∀ (e : Vec d) (φ₁ φ₂ : Vec d → ℝ) (G₁ G₂ : Vec d → Vec d),
                Set.EqOn (fun x => a₁ ω x) (fun x => a₂ ω x) (originBall d (2*R)) →
                MemLp φ₁ 2 (volume.restrict (originBall d (2*R))) →
                MemLp φ₂ 2 (volume.restrict (originBall d (2*R))) →
                MemLp (fun x => euclideanNorm (G₁ x - G₂ x)) 2
                  (volume.restrict (originBall d (2*R))) →
                HasWeakGradient (originBall d (2*R)) φ₁ G₁ →
                HasWeakGradient (originBall d (2*R)) φ₂ G₂ →
                HasWeakDivergence (originBall d (2*R))
                  (fun x => (a₁ ω x).mulVec (e + G₁ x)) (fun _ => 0) →
                HasWeakDivergence (originBall d (2*R))
                  (fun x => (a₂ ω x).mulVec (e + G₂ x)) (fun _ => 0) →
                EllipticBound (ball 0 1) (a₁ ω) lam Λ →
                (∀ i j, HolderBound (ball 0 1) α (fun x => a₁ ω x i j) H) →
                C1Alpha (ball 0 1) α (fun x => φ₁ x - φ₂ x) (fun x => G₁ x - G₂ x) →
                euclideanNorm (G₁ 0 - G₂ 0) ≤ C * (X (a₁ ω))^((d : ℝ)/2) *
                  vectorRms volume (originBall d (2*R)) (fun x => G₁ x - G₂ x) := by
  obtain ⟨C₀, C, hC₀, hC, hbound⟩ := ellipticLargeScale_harmonic_gradient_origin
    hAKM h817 h832 hP d hd K s hK hs hsd hlam hΛ hH hα hα1
  refine ⟨C₀, C, hC₀, hC, ?_⟩
  intro P hP
  obtain ⟨X, hXm, hX, htail, hgood⟩ := hbound P hP
  refine ⟨X, hXm, hX, htail, ?_⟩
  intro Ω _ ν a₁ a₂ hmap
  filter_upwards [hmap.quasiMeasurePreserving.ae hgood] with ω hω
  intro R hR e φ₁ φ₂ G₁ G₂ ha hφ₁ hφ₂ hG hg₁ hg₂ hd₁ hd₂ hell hholder hreg
  have hR0 : 0 ≤ R := zero_le_one.trans ((hX _).trans hR)
  exact hω (2*R) (hR.trans (by linarith)) _ _
    (paired_corrector_isHarmonic ha e hφ₁ hφ₂ hG hg₁ hg₂ hd₁ hd₂) hell hholder hreg

end EinsteinRelation.Correctors
