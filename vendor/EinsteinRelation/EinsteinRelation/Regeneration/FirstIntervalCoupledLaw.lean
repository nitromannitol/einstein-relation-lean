import EinsteinRelation.Regeneration.ReducedOneIntervalHalfSpaceLaws
import EinsteinRelation.Probability.FiniteHistoryStopping

/-!
# The first coupled interval from the literal one-interval identities

Source `paper/main.tex:377–381`. The two bit branches determine every
bounded observation of the first stopped history. The identities below
use the actual coupled law and its actual initial point.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- The true and false branches at time zero, after using the actual
initial point. These are consequences of `OneIntervalKernelAt`. -/
theorem integral_first_bit_branches_of_oneIntervalKernelAt {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsProbabilityMeasure (K xω)]
    (hstart : ∀ᵐ z ∂K xω, z.1 0 = xω.1)
    (hone : Renewal.OneIntervalKernelAt Δ δ R i P K xω)
    (F : Path d → ℝ) (hF : Measurable F) (hb : BoundedRealTest F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') :
    ((∫ z, (if z.2 0 = true then (1 : ℝ) else 0) * F z.1 ∂K xω) =
      δ * ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P xω.1 xω.2) ∧
    ((∫ z, (if z.2 0 = true then (0 : ℝ) else 1) * F z.1 ∂K xω) =
      (∫ γ, F γ ∂P xω) -
        δ * ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P xω.1 xω.2) := by
  obtain ⟨_, _, ht, _, _, _, hf⟩ := hone 0 (fun _ => 1) F measurable_const
    ⟨1, fun _ => by simp⟩ hF hb hsegment
  have hshift : ∀ γ : Path d, pathTimeShift γ 0 = γ := by
    intro γ
    ext t j
    simp [pathTimeShift]
  simp only [Nat.cast_zero, zero_mul, one_mul] at ht hf
  simp only [hshift] at ht hf
  have hbridge : (∫ z, ∫ γ, F γ
      ∂Renewal.killedBridgeMixture Δ R i P (z.1 0) xω.2 ∂K xω) =
      ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P xω.1 xω.2 := by
    calc
      _ = ∫ _z, ∫ γ, F γ
          ∂Renewal.killedBridgeMixture Δ R i P xω.1 xω.2 ∂K xω :=
        integral_congr_ae (hstart.mono fun z hz => by rw [hz])
      _ = _ := by simp
  refine ⟨ht.trans (congrArg (δ * ·) hbridge), hf.trans ?_⟩
  calc
    _ = ∫ _z, ((∫ γ, F γ ∂P xω) -
        δ * ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P xω.1 xω.2) ∂K xω :=
      integral_congr_ae (hstart.mono fun z hz => by rw [hz])
    _ = _ := by simp

/-- Extend one path and its first bit by false later bits. The path may
already have been stopped at the end of the first interval. -/
def firstBitSample {d : ℕ} (γ : Path d) (b : Bool) : CoupledSample d :=
  (γ, fun k => if k = 0 then b else false)

private theorem measurable_firstBitSample {d : ℕ} (b : Bool) :
    Measurable (fun γ : Path d => firstBitSample γ b) :=
  measurable_id.prodMk measurable_const

private theorem firstBitSample_stop_eq {d : ℕ} (Δ : ℝ≥0) (z : CoupledSample d) :
    firstBitSample (Diffusion.stopPathAt Δ z.1) (z.2 0) =
      Probability.stoppedHistorySample Δ 1 z := by
  apply Prod.ext
  · ext t j
    simp [firstBitSample, Diffusion.stopPathAt, Probability.stoppedHistorySample]
  · funext k
    by_cases hk : k = 0
    · subst k
      simp [firstBitSample, Probability.stoppedHistorySample]
    · simp [firstBitSample, Probability.stoppedHistorySample, hk]

/-- Two one-interval constructions have the same first-history integral
whenever their diffusion and bridge integrals agree on the two bit tests.
No uniqueness of a coupled construction is assumed. -/
theorem integral_first_history_eq_of_oneInterval_integrals {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (P P' : QuenchedPathLaws d)
    (K K' : CoupledQuenchedLaws d) (xω xω' : Vec d × FieldPair d)
    [IsProbabilityMeasure (K xω)] [IsProbabilityMeasure (K' xω')]
    (hstart : ∀ᵐ z ∂K xω, z.1 0 = xω.1)
    (hstart' : ∀ᵐ z ∂K' xω', z.1 0 = xω'.1)
    (hone : Renewal.OneIntervalKernelAt Δ δ R i P K xω)
    (hone' : Renewal.OneIntervalKernelAt Δ δ R i P' K' xω')
    (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F)
    (hb : BoundedRealTest F)
    (heq : ∀ b : Bool,
      (∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) b) ∂P xω) =
        ∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) b) ∂P' xω')
    (heqBridge : ∀ b : Bool,
      (∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) b)
        ∂Renewal.killedBridgeMixture Δ R i P xω.1 xω.2) =
      ∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) b)
        ∂Renewal.killedBridgeMixture Δ R i P' xω'.1 xω'.2) :
    (∫ z, F z ∂K xω) = ∫ z, F z ∂K' xω' := by
  let Fb := fun b γ => F (firstBitSample (Diffusion.stopPathAt Δ γ) b)
  have hFb : ∀ b, Measurable (Fb b) := fun b =>
    (hF.mono (Probability.finiteHistorySigma_le Δ 1) le_rfl).comp
      ((measurable_firstBitSample b).comp (Diffusion.continuous_stopPathAt Δ).measurable)
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
    have h := Probability.finiteHistory_test_stopped Δ 1 F hF z
    rw [← firstBitSample_stop_eq] at h
    cases hz : z.2 0 <;> simpa [Fb, hz] using h.symm
  have hbbranch : ∀ b : Bool, BoundedRealTest (fun z : CoupledSample d =>
      (if z.2 0 = true then (if b then (1 : ℝ) else 0) else (if b then 0 else 1)) * Fb b z.1) := by
    intro b
    obtain ⟨C, hC⟩ := hbFb b
    refine ⟨max C 0, fun z => ?_⟩
    cases b <;> by_cases hz : z.2 0 = true <;>
      simp only [hz, Bool.false_eq_true, if_false, if_true, one_mul, zero_mul, abs_zero] <;>
      first | exact le_max_right _ _ | exact (hC _).trans (le_max_left _ _)
  have hi : ∀ (L : CoupledQuenchedLaws d) (p : Vec d × FieldPair d),
      IsProbabilityMeasure (L p) →
      (∫ z, F z ∂L p) =
        (∫ z, (if z.2 0 = true then (1 : ℝ) else 0) * Fb true z.1 ∂L p) +
        ∫ z, (if z.2 0 = true then (0 : ℝ) else 1) * Fb false z.1 ∂L p := by
    intro L p hp
    haveI := hp
    have hbit : Measurable (fun z : CoupledSample d => z.2 0) :=
      (measurable_pi_apply 0).comp measurable_snd
    have ht : Measurable (fun z : CoupledSample d =>
        (if z.2 0 = true then (1 : ℝ) else 0) * Fb true z.1) :=
      (Measurable.ite (measurableSet_eq_fun hbit measurable_const)
        measurable_const measurable_const).mul ((hFb true).comp measurable_fst)
    have hf : Measurable (fun z : CoupledSample d =>
        (if z.2 0 = true then (0 : ℝ) else 1) * Fb false z.1) :=
      (Measurable.ite (measurableSet_eq_fun hbit measurable_const)
        measurable_const measurable_const).mul ((hFb false).comp measurable_fst)
    have htI := Integrable.of_bound (μ := L p) ht.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact (hbbranch true).choose_spec z)
    have hfI := Integrable.of_bound (μ := L p) hf.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact (hbbranch false).choose_spec z)
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_add htI hfI]
  rw [hi K xω inferInstance, hi K' xω' inferInstance]
  have ht := integral_first_bit_branches_of_oneIntervalKernelAt Δ δ R i P K xω
    hstart hone (Fb true) (hFb true) (hbFb true) (hsFb true)
  have hf := integral_first_bit_branches_of_oneIntervalKernelAt Δ δ R i P K xω
    hstart hone (Fb false) (hFb false) (hbFb false) (hsFb false)
  have ht' := integral_first_bit_branches_of_oneIntervalKernelAt Δ δ R i P' K' xω'
    hstart' hone' (Fb true) (hFb true) (hbFb true) (hsFb true)
  have hf' := integral_first_bit_branches_of_oneIntervalKernelAt Δ δ R i P' K' xω'
    hstart' hone' (Fb false) (hFb false) (hbFb false) (hsFb false)
  rw [ht.1, hf.2, ht'.1, hf'.2, heqBridge true, heqBridge false, heq false]


end EinsteinRelation.Regeneration
