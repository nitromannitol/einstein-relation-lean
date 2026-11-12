import EinsteinRelation.Calculus.EnvironmentWeakCalculusCore
import EinsteinRelation.Calculus.HorizontalWeakL1UniquenessSupport

/-! # Almost-everywhere uniqueness of weak horizontal gradients

Source `paper/main.tex:241–245`. The coordinates of a weak horizontal gradient are fixed almost
everywhere by the integration-by-parts identity tested against horizontally smooth tests. Bounded
smooth orbit cores are such tests, and they separate integrable classes on the stationary
probability measure, so two weak gradients of the same scalar field agree coordinatewise.
-/

open MeasureTheory Filter

namespace EinsteinRelation

/-- Two weak horizontal gradients of the same scalar field agree almost everywhere in every
coordinate. -/
theorem HasWeakHorizontalGradient.ae_unique {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {f : FieldPair d → ℝ} {Df Df' : FieldPair d → Vec d}
    (h : HasWeakHorizontalGradient Q hQ f Df)
    (h' : HasWeakHorizontalGradient Q hQ f Df') (i : Fin d) :
    (fun ω => Df ω i) =ᵐ[Q] (fun ω => Df' ω i) := by
  have hint : Integrable (fun ω => Df ω i - Df' ω i) Q := (h.2.1 i).sub' (h'.2.1 i)
  -- Against a bounded orbit core `H`, both weak identities test the same L²(Q) derivative of `H`,
  -- so the two pairings `∫ Df_i · H` and `∫ Df'_i · H` coincide.
  have hfun : ∀ H : FieldPair d → ℝ, IsHorizontalTest H →
      (∫ ω, (Df ω i - Df' ω i) * H ω ∂Q) = 0 := by
    intro H hH
    obtain ⟨M, -, hM⟩ := hH.bound_orbit
    have hHm : AEStronglyMeasurable H Q := hH.1.aestronglyMeasurable
    have hHb : ∀ᵐ ω ∂Q, ‖H ω‖ ≤ M :=
      Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, orbit_zero] using hM ω 0
    have hI : Integrable (fun ω => Df ω i * H ω) Q := (h.2.1 i).mul_bdd hHm hHb
    have hI' : Integrable (fun ω => Df' ω i * H ω) Q := (h'.2.1 i).mul_bdd hHm hHb
    have hFsm := hH.isHorizontallySmoothTest Q hQ
    have hDer := hH.hasHorizontalLpDerivative_toLp Q hQ i
    have hA' := h.2.2 i _ _ hFsm hDer
    have hB' := h'.2.2 i _ _ hFsm hDer
    have e := neg_inj.mp (hA'.symm.trans hB')
    have hFH := (hH.memLp Q 2).coeFn_toLp
    have hA : (∫ ω, Df ω i * ((hH.memLp Q 2).toLp H) ω ∂Q) = ∫ ω, Df ω i * H ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hFH] with ω hω
      rw [hω]
    have hB : (∫ ω, Df' ω i * ((hH.memLp Q 2).toLp H) ω ∂Q) = ∫ ω, Df' ω i * H ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hFH] with ω hω
      rw [hω]
    have hAB : (∫ ω, Df ω i * H ω ∂Q) = ∫ ω, Df' ω i * H ω ∂Q :=
      hA.symm.trans (e.trans hB)
    have hsplit : (∫ ω, (Df ω i - Df' ω i) * H ω ∂Q) =
        (∫ ω, Df ω i * H ω ∂Q) - ∫ ω, Df' ω i * H ω ∂Q := by
      have hpoint : (fun ω => (Df ω i - Df' ω i) * H ω) =
          fun ω => Df ω i * H ω - Df' ω i * H ω := by
        funext ω
        ring
      rw [hpoint]
      exact integral_sub hI hI'
    exact hsplit.trans (sub_eq_zero.mpr hAB)
  -- Pass from the function `Df_i - Df'_i` to its `L¹(Q)` class, which pairs to zero with every
  -- bounded orbit core.
  have hpairL1 : ∀ H : FieldPair d → ℝ, IsHorizontalTest H →
      (∫ ω, (Integrable.toL1 (fun ω => Df ω i - Df' ω i) hint) ω * H ω ∂Q) = 0 := by
    intro H hH
    have hcongr : (∫ ω, (Integrable.toL1 (fun ω => Df ω i - Df' ω i) hint) ω * H ω ∂Q) =
        ∫ ω, (Df ω i - Df' ω i) * H ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [Integrable.coeFn_toL1 hint] with ω hω
      rw [hω]
    exact hcongr.trans (hfun H hH)
  have hg0 : Integrable.toL1 (fun ω => Df ω i - Df' ω i) hint = 0 :=
    eq_zero_of_horizontalCore_pairing_eq_zero_l1 Q hQ
      (Integrable.toL1 (fun ω => Df ω i - Df' ω i) hint) hpairL1
  filter_upwards [Integrable.coeFn_toL1 hint, Lp.coeFn_zero ℝ 1 Q] with ω hω hz
  have hzω : (Integrable.toL1 (fun ω => Df ω i - Df' ω i) hint) ω = 0 :=
    (congrArg (fun z : Lp ℝ 1 Q => z ω) hg0).trans hz
  exact sub_eq_zero.mp (hω.symm.trans hzω)

end EinsteinRelation
