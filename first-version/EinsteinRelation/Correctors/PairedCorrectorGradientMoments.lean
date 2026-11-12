import EinsteinRelation.Correctors.PairedCorrectorHarmonicGradient
import EinsteinRelation.Correctors.ConditionalCopyMoments

/-! # Paired corrector point moments from the harmonic estimate

Source: `paper/main.tex:861–875`. AKM selects the first-field radius before
the coupling. Its tail and the good-event harmonic estimate are discharged
inside the moment argument. Spatial energy, higher point moments, and
regularity of the same representatives remain explicit internal obligations.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport

/-- The harmonic estimate and its random-radius tail give the sharp
point-gradient rate from the ordinary paired spatial energy rate. One
constant works for every source law and every coupling with that first
marginal. Source: `paper/main.tex:861–875`. -/
theorem ellipticLargeScale_paired_corrector_gradient_moments
    (hAKM : EllipticLargeScale)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hP : BallPoincareEstimate)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hsd : s < d)
    {lam Λ H α : ℝ} (hlam : 0 < lam) (hΛ : 0 < Λ)
    (hH : 0 < H) (hα : 0 < α) (hα1 : α < 1)
    (m B E : ℝ) (hm : 1 ≤ m) (hB : 0 ≤ B) (hE : 0 ≤ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
        (a₁ a₂ : Ω → Coefficient d K), MeasurePreserving a₁ ν P →
      ∀ (R : ℝ), 0 < R → ∀ (e : Vec d)
        (φ₁ φ₂ : Ω → Vec d → ℝ) (G₁ G₂ : Ω → Vec d → Vec d),
        (∀ᵐ ω ∂ν,
          Set.EqOn (fun x => a₁ ω x) (fun x => a₂ ω x) (originBall d (2*R)) ∧
          MemLp (φ₁ ω) 2 (volume.restrict (originBall d (2*R))) ∧
          MemLp (φ₂ ω) 2 (volume.restrict (originBall d (2*R))) ∧
          MemLp (fun x => euclideanNorm (G₁ ω x - G₂ ω x)) 2
            (volume.restrict (originBall d (2*R))) ∧
          HasWeakGradient (originBall d (2*R)) (φ₁ ω) (G₁ ω) ∧
          HasWeakGradient (originBall d (2*R)) (φ₂ ω) (G₂ ω) ∧
          HasWeakDivergence (originBall d (2*R))
            (fun x => (a₁ ω x).mulVec (e + G₁ ω x)) (fun _ => 0) ∧
          HasWeakDivergence (originBall d (2*R))
            (fun x => (a₂ ω x).mulVec (e + G₂ ω x)) (fun _ => 0) ∧
          EllipticBound (ball 0 1) (a₁ ω) lam Λ ∧
          (∀ i j, HolderBound (ball 0 1) α (fun x => a₁ ω x i j) H) ∧
          C1Alpha (ball 0 1) α (fun x => φ₁ ω x - φ₂ ω x)
            (fun x => G₁ ω x - G₂ ω x)) →
        MemLp (fun ω => euclideanNorm (G₁ ω 0 - G₂ ω 0))
          (ENNReal.ofReal (2*m)) ν →
        eLpNorm (fun ω => euclideanNorm (G₁ ω 0 - G₂ ω 0))
          (ENNReal.ofReal (2*m)) ν ≤ ENNReal.ofReal B →
        MemLp (fun ω => vectorRms volume (originBall d (2*R))
          (fun x => G₁ ω x - G₂ ω x)) (ENNReal.ofReal (2*m)) ν →
        eLpNorm (fun ω => vectorRms volume (originBall d (2*R))
          (fun x => G₁ ω x - G₂ ω x)) (ENNReal.ofReal (2*m)) ν ≤
            ENNReal.ofReal (E * R^(-(d : ℝ)/2)) →
        MemLp (fun ω => euclideanNorm (G₁ ω 0 - G₂ ω 0)) (ENNReal.ofReal m) ν ∧
          eLpNorm (fun ω => euclideanNorm (G₁ ω 0 - G₂ ω 0))
            (ENNReal.ofReal m) ν ≤ ENNReal.ofReal (C * R^(-(d : ℝ)/2)) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hbound⟩ :=
    ellipticLargeScale_paired_corrector_gradient_origin hAKM h817 h832 hP
      d hd K s hK hs hsd hlam hΛ hH hα hα1
  let a : ℝ := (d : ℝ)/2
  have ha : 0 < a := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [a]
    linarith
  let D : ℝ := (2 * ((2*m)/(s/a))^((2*m)/(s/a)))^(1/(2*m)) * C₀^a
  refine ⟨D * (C₁ * E + B), by dsimp [D]; positivity, ?_⟩
  intro P hPlaw Ω _ ν a₁ a₂ hmap R hR e φ₁ φ₂ G₁ G₂ hdata hZ hZbound hA hAbound
  obtain ⟨X, hXm, hX, htail, hgood⟩ := hbound P hPlaw
  have htail' := stretchedExponential_comp_of_map_eq hmap.measurable hmap.map_eq hXm htail
  have hpoint : ∀ᵐ ω ∂ν, (X ∘ a₁) ω ≤ R →
      ‖euclideanNorm (G₁ ω 0 - G₂ ω 0)‖ ≤ C₁ * ((X ∘ a₁) ω)^a *
        ‖vectorRms volume (originBall d (2*R)) (fun x => G₁ ω x - G₂ ω x)‖ := by
    filter_upwards [hgood ν a₁ a₂ hmap, hdata] with ω hω hωdata
    rcases hωdata with ⟨heq, hφ₁, hφ₂, hG, hg₁, hg₂, hd₁, hd₂, hell, hholder, hreg⟩
    intro hRgood
    have hZn : 0 ≤ euclideanNorm (G₁ ω 0 - G₂ ω 0) := Real.sqrt_nonneg _
    have hAn : 0 ≤ vectorRms volume (originBall d (2*R))
        (fun x => G₁ ω x - G₂ ω x) := Real.sqrt_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hZn, abs_of_nonneg hAn] using
      hω R hRgood e (φ₁ ω) (φ₂ ω) (G₁ ω) (G₂ ω)
        heq hφ₁ hφ₂ hG hg₁ hg₂ hd₁ hd₂ hell hholder hreg
  simpa only [a, neg_div] using
    eLpNorm_pointwise_decay_of_stretchedExponential_radius
      (hXm.comp hmap.measurable) (fun ω => zero_le_one.trans (hX (a₁ ω)))
      hm hR ha hC₁.le hB hE hs hC₀ htail' hZ hA hpoint hZbound
      (by simpa only [a, neg_div] using hAbound)

end EinsteinRelation.Correctors
