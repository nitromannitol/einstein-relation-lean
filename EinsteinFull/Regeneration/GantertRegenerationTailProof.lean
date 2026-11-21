import EinsteinFull.Regeneration.GMPPositiveSlabExit
import EinsteinFull.Regeneration.RegenerationEndpointMoment
import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationNoReturn
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The regeneration tail and no-return bounds

Gantert–Mathieu–Piatnitski, Lemma 5.8, (5.22) and the no-return bound (5.20), for the
Section 7 zero-potential diffusion with the split coupling, with the statement of
`gantert_regeneration_tail` in `EinsteinFull/Frozen/GantertRegenerationTail.lean`. The
positive slab-exit estimate (GMP Lemma 4.3) holds for every realization of the reduced
kernel, and the reduction of the tail and no-return bounds to that estimate applies.

Departures from the source: the source's proof of Lemma 4.3 uses that the slab-exit
probability solves the boundary-value problem (4.3)–(4.4); here this is proved, by Dynkin's
formula at the exit time, the limit of the zero-boundary resolvents as the rate vanishes, and
the continuity of the exit payoff inside the slab and at its boundary. The source obtains the
exponential moment (5.26) of the first regeneration endpoint from the argument of Shen,
Theorem 4.9; here that argument is carried out with constants uniform in the environment law
and the force, using a uniform exponential moment of the maximal displacement over one
regeneration interval of length `λ⁻²`.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External

open EinsteinRelation

/-- GMP Lemma 5.8, (5.22), and the no-return bound (5.20), for the
Section 7 zero-potential diffusion with the actual split coupling. -/
theorem gantert_regeneration_tail_holds (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K →
      ENNReal.ofReal (1 / 2 : ℝ) ≤
        Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ∧
      ∀ t : ℝ, 0 ≤ t →
        Regeneration.annealedCoupledLaw Q.measure K
          {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
            ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  by_cases hΛ : 1 ≤ Λ₀
  · obtain ⟨L, hL, hpos⟩ := Regeneration.gmp_positive_slab_exit n hd Λ₀ hΛ
    obtain ⟨l₀, hl₀, hsep, hbounds⟩ :=
      Regeneration.first_regeneration_bounds_of_positive_exit (n + 1) hd Λ₀ r₀ L hL
    refine ⟨l₀, hl₀, hsep, fun l hl δ hδ hδ1 => ?_⟩
    obtain ⟨c, C, hc, hC, h⟩ := hbounds l hl δ hδ hδ1
    refine ⟨c, C, hc, hC, fun Q lam h₀ h₁ P K hK => h Q lam h₀ h₁ P K hK ?_⟩
    obtain ⟨-, -, hred, -⟩ := hK
    filter_upwards [hred] with ω hω
    obtain ⟨hω', G, hG⟩ := hω
    intro y
    rw [hG y]
    exact hpos L le_rfl r₀ Q lam h₀ h₁ ω hω' G y
  · obtain ⟨l₀, hl₀, hsep, hbounds⟩ :=
      Regeneration.first_regeneration_bounds_of_positive_exit (n + 1) hd Λ₀ r₀ 1 le_rfl
    refine ⟨l₀, hl₀, hsep, fun l hl δ hδ hδ1 => ?_⟩
    obtain ⟨c, C, hc, hC, -⟩ := hbounds l hl δ hδ hδ1
    exact ⟨c, C, hc, hC, fun Q => absurd Q.ellipticity_parameter hΛ⟩

end EinsteinFull.External
