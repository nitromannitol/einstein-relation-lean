import EinsteinRelation.Regeneration.FirstIntervalCoupledLaw
import EinsteinRelation.Regeneration.SpatialRecenterEquiv

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration

private theorem first_history_formula {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d)
    [IsProbabilityMeasure (K p)] (hs : ∀ᵐ z ∂K p, z.1 0 = p.1)
    (ho : Renewal.OneIntervalKernelAt Δ δ R i P K p)
    (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F)
    (hb : BoundedRealTest F) :
    (∫ z, F z ∂K p) =
      δ * (∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) true)
        ∂Renewal.killedBridgeMixture Δ R i P p.1 p.2) +
      ((∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) false) ∂P p) -
        δ * ∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) false)
          ∂Renewal.killedBridgeMixture Δ R i P p.1 p.2) := by
  let Fb := fun b γ => F (firstBitSample (Diffusion.stopPathAt Δ γ) b)
  have hFb : ∀ b, Measurable (Fb b) := fun b =>
    (hF.mono (Probability.finiteHistorySigma_le Δ 1) le_rfl).comp
      ((measurable_id.prodMk measurable_const).comp
        (Diffusion.continuous_stopPathAt Δ).measurable)
  have hbFb : ∀ b, BoundedRealTest (Fb b) := by
    obtain ⟨C, hC⟩ := hb
    exact fun b => ⟨C, fun γ => hC _⟩
  have hsFb : ∀ b γ γ', (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → Fb b γ = Fb b γ' := by
    intro b γ γ' hh
    have hstop : Diffusion.stopPathAt Δ γ = Diffusion.stopPathAt Δ γ' := by
      apply ContinuousMap.ext
      intro t
      exact hh _ (min_le_right _ _)
    exact congrArg (fun q => F (firstBitSample q b)) hstop
  have hsplit : ∀ z : CoupledSample d, F z =
      (if z.2 0 = true then (1 : ℝ) else 0) * Fb true z.1 +
      (if z.2 0 = true then (0 : ℝ) else 1) * Fb false z.1 := by
    intro z
    have he : firstBitSample (Diffusion.stopPathAt Δ z.1) (z.2 0) =
        Probability.stoppedHistorySample Δ 1 z := by
      apply Prod.ext
      · ext t j
        simp [firstBitSample, Diffusion.stopPathAt, Probability.stoppedHistorySample]
      · funext k
        by_cases hk : k = 0
        · subst k
          simp [firstBitSample, Probability.stoppedHistorySample]
        · simp [firstBitSample, Probability.stoppedHistorySample, hk]
    have h := Probability.finiteHistory_test_stopped Δ 1 F hF z
    rw [← he] at h
    cases hz : z.2 0 <;> simpa [Fb, hz] using h.symm
  have hshift : ∀ γ : Path d, pathTimeShift γ 0 = γ := by
    intro γ
    ext t j
    simp [pathTimeShift]
  have ht := ho 0 (fun _ => 1) (Fb true) measurable_const ⟨1, fun _ => by simp⟩
    (hFb true) (hbFb true) (hsFb true)
  have hf := ho 0 (fun _ => 1) (Fb false) measurable_const ⟨1, fun _ => by simp⟩
    (hFb false) (hbFb false) (hsFb false)
  simp only [Nat.cast_zero, zero_mul, one_mul, hshift] at ht hf
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_add ht.1 hf.2.2.2.1]
  rw [(integral_first_bit_branches_of_oneIntervalKernelAt Δ δ R i P K p hs ho
    (Fb true) (hFb true) (hbFb true) (hsFb true)).1,
    (integral_first_bit_branches_of_oneIntervalKernelAt Δ δ R i P K p hs ho
      (Fb false) (hFb false) (hbFb false) (hsFb false)).2]

/-- Source `paper/main.tex:406–408`: translation of the diffusion and actual bridge measures determines the translated first bit/history integral. -/
theorem integral_first_history_comp_recenter_of_segment_maps {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (P P' : QuenchedPathLaws d)
    (K K' : CoupledQuenchedLaws d) (p p' : Vec d × FieldPair d) (a : Vec d)
    [IsProbabilityMeasure (K p)] [IsProbabilityMeasure (K' p')]
    (hs : ∀ᵐ z ∂K p, z.1 0 = p.1) (hs' : ∀ᵐ z ∂K' p', z.1 0 = p'.1)
    (ho : Renewal.OneIntervalKernelAt Δ δ R i P K p)
    (ho' : Renewal.OneIntervalKernelAt Δ δ R i P' K' p')
    (hP : (P p).map (recenterPathEquiv a) = P' p')
    (hB : (Renewal.killedBridgeMixture Δ R i P p.1 p.2).map (recenterPathEquiv a) =
      Renewal.killedBridgeMixture Δ R i P' p'.1 p'.2)
    (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F)
    (hb : BoundedRealTest F) :
    (∫ z, F (recenterSample a z) ∂K p) = ∫ z, F z ∂K' p' := by
  have hb' : BoundedRealTest (fun z => F (recenterSample a z)) := by
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun z => hC _⟩
  rw [first_history_formula Δ δ R i P K p hs ho _
    (measurable_finiteHistory_comp_recenter Δ 1 a F hF) hb',
    first_history_formula Δ δ R i P' K' p' hs' ho' F hF hb,
    ← hP, ← hB, integral_map_equiv, integral_map_equiv, integral_map_equiv]
  rfl

end EinsteinRelation.Regeneration
