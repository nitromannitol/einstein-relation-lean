import EinsteinRelation.Correctors.PoissonLift
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

/-! Source: `paper/main.tex:735-739`. Local integrability survives adding
the independent height coordinate in the explicit Poisson lift. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The pullback of a locally integrable function along the base projection
is locally integrable for coordinate Lebesgue measure. -/
theorem locallyIntegrable_poissonLiftBase {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f : Vec d → E) (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun x : Vec (d + 1) => f (poissonLiftBase x)) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hc : Continuous (poissonLiftBase : Vec (d + 1) → Vec d) := by
    exact continuous_pi (fun i => continuous_apply i.succ)
  have hb := hK.image hc
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : Vec (d + 1))).mp hK.isBounded
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  let s : Set (ℝ × Vec d) := Set.Icc (-R) R ×ˢ (poissonLiftBase '' K)
  have hs : MeasurableSet s := measurableSet_Icc.prod hb.measurableSet
  have he := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => ℝ) 0).restrict_preimage hs
  have hp : Integrable (fun p : ℝ × Vec d => f p.2)
      ((volume : Measure (ℝ × Vec d)).restrict s) := by
    simpa only [Measure.prod_restrict] using
      (hf.integrableOn_isCompact hb).comp_snd (volume.restrict (Set.Icc (-R) R))
  have ht : Integrable (fun x : Vec (d + 1) => f (poissonLiftBase x))
      (volume.restrict (e ⁻¹' s)) := he.integrable_comp_of_integrable hp
  apply ht.mono_measure
  apply Measure.restrict_mono_set
  intro x hx
  change x 0 ∈ Set.Icc (-R) R ∧ poissonLiftBase x ∈ poissonLiftBase '' K
  have hxnorm : ‖x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx
  have hxcoord : |x 0| ≤ R := (norm_le_pi_norm x 0).trans hxnorm
  exact ⟨abs_le.mp hxcoord, ⟨x, hx, rfl⟩⟩

/-- All components of a lifted flux remain locally integrable. -/
theorem locallyIntegrable_poissonLiftFlux {d : ℕ}
    (F : Vec d → Vec d) (B : Vec d → ℝ)
    (hF : ∀ i, LocallyIntegrable (fun x => F x i) volume)
    (hB : LocallyIntegrable B volume) :
    ∀ i, LocallyIntegrable (fun x : Vec (d + 1) => poissonLiftFlux F B x i) volume := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [poissonLiftFlux, Fin.cons_zero] using
      locallyIntegrable_poissonLiftBase B hB
  · simpa only [poissonLiftFlux, Fin.cons_succ] using
      locallyIntegrable_poissonLiftBase (fun x => F x j) (hF j)

/-- Fubini for a locally integrable base function paired with a continuous
compact test on the lifted space. The pairing is genuinely integrable. -/
theorem integral_poissonLiftBase_mul_test {d : ℕ}
    (f : Vec d → ℝ) (hf : LocallyIntegrable f volume)
    (ψ : Vec (d + 1) → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    (∫ x : Vec (d + 1), f (poissonLiftBase x) * ψ x) =
      ∫ t : ℝ, ∫ y : Vec d, f y * ψ (Fin.cons t y) := by
  have hi : Integrable (fun x : Vec (d + 1) => f (poissonLiftBase x) * ψ x) volume := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_poissonLiftBase f hf).integrable_smul_right_of_hasCompactSupport hψ hψc
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have heinv (p : ℝ × Vec d) : e.symm p = Fin.cons p.1 p.2 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have he' := MeasurePreserving.symm e he
  have hp : Integrable (fun p : ℝ × Vec d => f p.2 * ψ (Fin.cons p.1 p.2)) volume := by
    simpa [Function.comp_def, heinv, poissonLiftBase] using
      he'.integrable_comp_of_integrable hi
  have hchange : (∫ x : Vec (d + 1), f (poissonLiftBase x) * ψ x) =
      ∫ p : ℝ × Vec d, f p.2 * ψ (Fin.cons p.1 p.2) := by
    simpa [heinv, poissonLiftBase] using
      (he'.integral_comp' (fun x : Vec (d + 1) => f (poissonLiftBase x) * ψ x)).symm
  exact hchange.trans (integral_prod _ hp)

end EinsteinRelation.Correctors
