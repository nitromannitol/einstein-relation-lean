import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.Pi

/-! Source meanings from `paper/main.tex:704–713,754–772`: the ball average
and fixed-mollifier normalization are distinct, and the latter maps a local
`L¹` class modulo constants to an ordinary local almost-everywhere class. -/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors.NormalizedSpatialRepresentativeSupport

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev EuclideanMatrix (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)

def SkewMatrices (d : ℕ) : Submodule ℝ (EuclideanMatrix d) where
  carrier := {A | ∀ i j, A (j, i) = -A (i, j)}
  zero_mem' := by intro i j; simp
  add_mem' := by
    intro A B hA hB i j
    change A (j, i) + B (j, i) = -(A (i, j) + B (i, j))
    rw [hA i j, hB i j]
    abel
  smul_mem' := by
    intro c A hA i j
    simp [hA i j]

structure SpatialPotential (d : ℕ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  value : Point d → E
  locallyIntegrable : LocallyIntegrable value volume

abbrev ScalarSpatialPotential (d : ℕ) := SpatialPotential d ℝ
abbrev SkewMatrixSpatialPotential (d : ℕ) := SpatialPotential d (SkewMatrices d)

noncomputable def addSpatialConstant {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPotential d E) (c : E) : SpatialPotential d E where
  value := fun x => f.value x + c
  locallyIntegrable := f.locallyIntegrable.add (locallyIntegrable_const _)

def SpatialGaugeEq {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : SpatialPotential d E) : Prop :=
  ∃ c : E, f.value =ᵐ[volume] fun x => g.value x + c

instance spatialGaugeSetoid (d : ℕ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Setoid (SpatialPotential d E) where
  r := SpatialGaugeEq
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro f
      exact ⟨0, Filter.Eventually.of_forall (fun x => by simp)⟩
    · intro f g h
      rcases h with ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      filter_upwards [hc] with x hx
      rw [hx]
      abel
    · intro f g h hfg hgh
      rcases hfg with ⟨c, hc⟩
      rcases hgh with ⟨e, he⟩
      refine ⟨c + e, ?_⟩
      filter_upwards [hc, he] with x hfx hgx
      rw [hfx, hgx]
      abel

instance spatialAESetoid (d : ℕ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Setoid (SpatialPotential d E) where
  r f g := f.value =ᵐ[volume] g.value
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro f
      exact Filter.EventuallyEq.rfl
    · intro f g h
      exact h.symm
    · intro f g h hfg hgh
      exact hfg.trans hgh

abbrev SpatialPotentialClass (d : ℕ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] := Quotient (spatialGaugeSetoid d E)

abbrev SpatialPotentialAEClass (d : ℕ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] := Quotient (spatialAESetoid d E)

abbrev ScalarPotentialClass (d : ℕ) := SpatialPotentialClass d ℝ
abbrev ScalarPotentialAEClass (d : ℕ) := SpatialPotentialAEClass d ℝ
abbrev SkewMatrixPotentialClass (d : ℕ) :=
  SpatialPotentialClass d (SkewMatrices d)
abbrev SkewMatrixPotentialAEClass (d : ℕ) :=
  SpatialPotentialAEClass d (SkewMatrices d)

structure NormalizedSpatialKernel (d : ℕ) where
  density : C(Point d, ℝ)
  nonnegative : ∀ x, 0 ≤ density x
  compactSupport : HasCompactSupport density
  integral_one : (∫ x, density x ∂volume) = 1

structure SourceMollifier (d : ℕ) where
  density : C(Point d, ℝ)
  smooth : ContDiff ℝ (⊤ : ℕ∞) density
  nonnegative : ∀ x, 0 ≤ density x
  compactSupport : HasCompactSupport density
  supportWithinUnitBall : tsupport density ⊆ Metric.ball 0 1
  integral_one : (∫ x, density x ∂volume) = 1

noncomputable def sourceScaledMollifierKernel {d : ℕ}
    (ζ : SourceMollifier d) (R : ℝ) (y x : Point d) : ℝ :=
  (R ^ d)⁻¹ * ζ.density (R⁻¹ • (x - y))

theorem continuous_sourceScaledMollifierKernel {d : ℕ}
    (ζ : SourceMollifier d) (R : ℝ) (y : Point d) :
    Continuous (sourceScaledMollifierKernel ζ R y) := by
  unfold sourceScaledMollifierKernel
  exact continuous_const.mul <| ζ.density.continuous.comp <|
    continuous_const_smul (R⁻¹) |>.comp (continuous_id.sub continuous_const)

theorem hasCompactSupport_sourceScaledMollifierKernel {d : ℕ}
    (ζ : SourceMollifier d) {R : ℝ} (hR : 1 ≤ R) (y : Point d) :
    HasCompactSupport (sourceScaledMollifierKernel ζ R y) := by
  have hRpos : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hR)
  have hc := ζ.compactSupport.comp_smul (inv_ne_zero hRpos)
  have hcy := hc.comp_homeomorph (Homeomorph.addRight (-y))
  unfold sourceScaledMollifierKernel
  exact hcy.mul_left (f := fun _ : Point d => (R ^ d)⁻¹)

theorem integral_sourceScaledMollifierKernel {d : ℕ}
    (ζ : SourceMollifier d) {R : ℝ} (hR : 1 ≤ R) (y : Point d) :
    (∫ x, sourceScaledMollifierKernel ζ R y x ∂volume) = 1 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hshift :
      (∫ x : Point d, ζ.density (R⁻¹ • (x - y)) ∂volume) =
        ∫ x : Point d, ζ.density (R⁻¹ • x) ∂volume := by
    have h := (measurePreserving_add_right (volume : Measure (Point d)) (-y)).integral_comp
      (Homeomorph.addRight (-y)).measurableEmbedding
      (fun z : Point d => ζ.density (R⁻¹ • z))
    simpa only [sub_eq_add_neg] using h
  have hscale := Measure.integral_comp_inv_smul (volume : Measure (Point d))
    (ζ.density : Point d → ℝ) R
  rw [finrank_euclideanSpace_fin] at hscale
  have hpow : 0 < R ^ d := pow_pos hRpos d
  change (∫ x, (R ^ d)⁻¹ * ζ.density (R⁻¹ • (x - y)) ∂volume) = 1
  rw [integral_const_mul, hshift, hscale, abs_of_pos hpow, ζ.integral_one,
    smul_eq_mul]
  field_simp

noncomputable def sourceScaledSpatialKernel {d : ℕ}
    (ζ : SourceMollifier d) (R : ℝ) (y : Point d) (hR : 1 ≤ R) :
    NormalizedSpatialKernel d where
  density := ⟨sourceScaledMollifierKernel ζ R y,
    continuous_sourceScaledMollifierKernel ζ R y⟩
  nonnegative := by
    intro x
    unfold sourceScaledMollifierKernel
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg
      (le_of_lt (lt_of_lt_of_le zero_lt_one hR)) d)) (ζ.nonnegative _)
  compactSupport := hasCompactSupport_sourceScaledMollifierKernel ζ hR y
  integral_one := integral_sourceScaledMollifierKernel ζ hR y

noncomputable def mollifierMean {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f : SpatialPotential d E) : E :=
  ∫ x, w.density x • f.value x ∂volume

private theorem weightedMean_add_constant {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f g : SpatialPotential d E) (c : E)
    (hfg : f.value =ᵐ[volume] fun x => g.value x + c) :
    mollifierMean w f = mollifierMean w g + c := by
  have hf : Integrable (fun x => w.density x • f.value x) volume :=
    f.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      w.density.continuous w.compactSupport
  have hg : Integrable (fun x => w.density x • g.value x) volume :=
    g.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      w.density.continuous w.compactSupport
  have hc : Integrable (fun x : Point d => w.density x • c) volume := by
    exact (locallyIntegrable_const (μ := volume) c).integrable_smul_left_of_hasCompactSupport
      w.density.continuous w.compactSupport
  have hfun : (fun x => w.density x • f.value x) =ᵐ[volume]
      fun x => w.density x • g.value x + w.density x • c := by
    filter_upwards [hfg] with x hx
    rw [hx, smul_add]
  unfold mollifierMean
  rw [integral_congr_ae hfun, integral_add hg hc, integral_smul_const, w.integral_one,
    one_smul]

noncomputable def mollifierCenteredRepresentative {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f : SpatialPotential d E) :
    SpatialPotential d E where
  value := fun x => f.value x - mollifierMean w f
  locallyIntegrable := f.locallyIntegrable.sub (locallyIntegrable_const _)

theorem mollifierCenteredRepresentative_value {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f : SpatialPotential d E) (x : Point d) :
    (mollifierCenteredRepresentative w f).value x = f.value x - mollifierMean w f := rfl

theorem continuous_mollifierCenteredRepresentative {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f : SpatialPotential d E)
    (hf : Continuous f.value) :
    Continuous (mollifierCenteredRepresentative w f).value := by
  have h : Continuous (f.value - fun _ => mollifierMean w f) := hf.sub continuous_const
  exact h

theorem mollifierCenteredRepresentative_gaugeInvariant {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f g : SpatialPotential d E)
    (hfg : SpatialGaugeEq f g) :
    (mollifierCenteredRepresentative w f).value =ᵐ[volume]
      (mollifierCenteredRepresentative w g).value := by
  rcases hfg with ⟨c, hc⟩
  have hm := weightedMean_add_constant w f g c hc
  filter_upwards [hc] with x hx
  simp only [mollifierCenteredRepresentative]
  rw [hx, hm]
  abel

theorem mollifierCenteredRepresentative_addConstant {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f : SpatialPotential d E) (c : E) :
    (mollifierCenteredRepresentative w (addSpatialConstant f c)).value =ᵐ[volume]
      (mollifierCenteredRepresentative w f).value := by
  exact mollifierCenteredRepresentative_gaugeInvariant w (addSpatialConstant f c) f
    ⟨c, Filter.Eventually.of_forall (fun _ => rfl)⟩

/-- The source normalization lands in the ordinary local-AE quotient, so the
subtracted constant remains visible in its codomain. -/
noncomputable def mollifierNormalize {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) :
    SpatialPotentialClass d E → SpatialPotentialAEClass d E :=
  Quotient.lift
    (fun f => Quotient.mk (spatialAESetoid d E) (mollifierCenteredRepresentative w f))
    (fun f g hfg => Quotient.sound (mollifierCenteredRepresentative_gaugeInvariant w f g hfg))

theorem mollifierNormalize_mk {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f : SpatialPotential d E) :
    mollifierNormalize w (Quotient.mk (spatialGaugeSetoid d E) f) =
      Quotient.mk (spatialAESetoid d E) (mollifierCenteredRepresentative w f) := rfl

noncomputable def sourceMollifierNormalize {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d) :
    SpatialPotentialClass d E → SpatialPotentialAEClass d E :=
  mollifierNormalize (sourceScaledSpatialKernel ζ R y hR)

theorem sourceMollifierNormalize_mk {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (f : SpatialPotential d E) :
    sourceMollifierNormalize ζ R hR y (Quotient.mk (spatialGaugeSetoid d E) f) =
      Quotient.mk (spatialAESetoid d E)
        (mollifierCenteredRepresentative (sourceScaledSpatialKernel ζ R y hR) f) := rfl

theorem mollifierNormalize_addConstant {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f : SpatialPotential d E) (c : E) :
    mollifierNormalize w
      (Quotient.mk (spatialGaugeSetoid d E) (addSpatialConstant f c)) =
    mollifierNormalize w (Quotient.mk (spatialGaugeSetoid d E) f) := by
  apply congrArg (mollifierNormalize w)
  apply Quotient.sound
  exact ⟨c, Filter.Eventually.of_forall (fun _ => rfl)⟩

theorem integral_mollifierCenteredRepresentative_eq_zero {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : NormalizedSpatialKernel d) (f : SpatialPotential d E) :
    (∫ x, w.density x • (mollifierCenteredRepresentative w f).value x ∂volume) = 0 := by
  have hf : Integrable (fun x => w.density x • f.value x) volume :=
    f.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      w.density.continuous w.compactSupport
  have hc : Integrable (fun x : Point d => w.density x • mollifierMean w f) volume := by
    have hconst : LocallyIntegrable (fun _ : Point d => mollifierMean w f) volume :=
      locallyIntegrable_const _
    exact hconst.integrable_smul_left_of_hasCompactSupport
      w.density.continuous w.compactSupport
  calc
    (∫ x, w.density x • (mollifierCenteredRepresentative w f).value x ∂volume) =
        (∫ x, w.density x • f.value x ∂volume) -
          ∫ x, w.density x • mollifierMean w f ∂volume := by
      simp only [mollifierCenteredRepresentative]
      have hpoint (x : Point d) :
          w.density x • (f.value x - mollifierMean w f) =
            w.density x • f.value x - w.density x • mollifierMean w f :=
        smul_sub _ _ _
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_sub hf hc]
    _ = mollifierMean w f - mollifierMean w f := by
      rw [mollifierMean, integral_smul_const, w.integral_one, one_smul]
    _ = 0 := sub_self _

theorem integral_sourceMollifierCenteredRepresentative_eq_zero {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (f : SpatialPotential d E) :
    (∫ x, sourceScaledMollifierKernel ζ R y x •
      (mollifierCenteredRepresentative (sourceScaledSpatialKernel ζ R y hR) f).value x
      ∂volume) = 0 :=
  integral_mollifierCenteredRepresentative_eq_zero
    (sourceScaledSpatialKernel ζ R y hR) f

theorem continuous_ae_eq_pointwise {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : SpatialPotential d E) (hfg : f.value =ᵐ[volume] g.value)
    (hf : Continuous f.value) (hg : Continuous g.value) : f.value = g.value :=
  (hf.ae_eq_iff_eq volume hg).mp hfg

theorem continuous_representative_unique_at {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : SpatialPotential d E) (hfg : f.value =ᵐ[volume] g.value)
    (hf : Continuous f.value) (hg : Continuous g.value) (x : Point d) :
    f.value x = g.value x := by
  have h := continuous_ae_eq_pointwise f g hfg hf hg
  exact congrFun h x

theorem sourceMollifierCenteredRepresentative_pointwise_independent
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R)
    (y : Point d) (f g : SpatialPotential d E) (hfg : SpatialGaugeEq f g)
    (hf : Continuous f.value) (hg : Continuous g.value) (x : Point d) :
    (mollifierCenteredRepresentative (sourceScaledSpatialKernel ζ R y hR) f).value x =
      (mollifierCenteredRepresentative (sourceScaledSpatialKernel ζ R y hR) g).value x := by
  exact continuous_representative_unique_at
    (mollifierCenteredRepresentative (sourceScaledSpatialKernel ζ R y hR) f)
    (mollifierCenteredRepresentative (sourceScaledSpatialKernel ζ R y hR) g)
    (mollifierCenteredRepresentative_gaugeInvariant
      (sourceScaledSpatialKernel ζ R y hR) f g hfg)
    (continuous_mollifierCenteredRepresentative
      (sourceScaledSpatialKernel ζ R y hR) f hf)
    (continuous_mollifierCenteredRepresentative
      (sourceScaledSpatialKernel ζ R y hR) g hg)
    x

/-- The source ball normalization remains an independent, guarded definition.
It is not used to define the fixed-mollifier normalization above. -/
noncomputable def correctorBallMean {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (_hR : 1 ≤ R) (y : Point d) (f : SpatialPotential d E) : E :=
  ⨍ x in Metric.ball y (2 * R), f.value x ∂volume

noncomputable def ballCenteredRepresentative {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (hR : 1 ≤ R) (y : Point d) (f : SpatialPotential d E) :
    SpatialPotential d E where
  value := fun x => f.value x - correctorBallMean R hR y f
  locallyIntegrable := f.locallyIntegrable.sub (locallyIntegrable_const _)

private theorem correctorBallMean_add_constant {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {R : ℝ} (hR : 1 ≤ R) (y : Point d) (f g : SpatialPotential d E) (c : E)
    (hfg : f.value =ᵐ[volume] fun x => g.value x + c) :
    correctorBallMean R hR y f = correctorBallMean R hR y g + c := by
  let B : Set (Point d) := Metric.ball y (2 * R)
  have hBint : IntegrableOn g.value B volume := by
    have hclosed : IsCompact (Metric.closedBall y (2 * R)) :=
      isCompact_closedBall y (2 * R)
    have hsubset : B ⊆ Metric.closedBall y (2 * R) := by
      dsimp [B]
      exact Metric.ball_subset_closedBall
    exact (g.locallyIntegrable.integrableOn_isCompact hclosed).mono_set hsubset
  have hcint : IntegrableOn (fun _ : Point d => c) B volume :=
    integrableOn_const (by
      simpa [B] using
        (measure_ball_ne_top (μ := volume) (x := y) (r := 2 * R)))
  have hBpos : 0 < volume B := by
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hRadius : 0 < 2 * R := mul_pos (by norm_num) hRpos
    simpa [B] using Metric.measure_ball_pos (μ := volume) y hRadius
  have hBtop : volume B ≠ ∞ := by
    simpa [B] using (measure_ball_ne_top (μ := volume) (x := y) (r := 2 * R))
  have hBreal : volume.real B ≠ 0 := (ENNReal.toReal_pos hBpos.ne' hBtop).ne'
  have hmean : (∫ x in B, f.value x ∂volume) =
      (∫ x in B, g.value x + c ∂volume) :=
    integral_congr_ae (ae_restrict_of_ae hfg)
  unfold correctorBallMean
  dsimp only [B] at *
  rw [setAverage_eq, setAverage_eq, hmean, integral_add hBint hcint, integral_const]
  simp only [measureReal_restrict_apply_univ]
  rw [smul_add, smul_smul, inv_mul_cancel₀ hBreal, one_smul]

theorem ballCenteredRepresentative_gaugeInvariant {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (hR : 1 ≤ R) (y : Point d) (f g : SpatialPotential d E)
    (hfg : SpatialGaugeEq f g) :
    (ballCenteredRepresentative R hR y f).value =ᵐ[volume]
      (ballCenteredRepresentative R hR y g).value := by
  rcases hfg with ⟨c, hc⟩
  have hm := correctorBallMean_add_constant hR y f g c hc
  filter_upwards [hc] with x hx
  simp only [ballCenteredRepresentative]
  rw [hx, hm]
  abel

noncomputable def ballNormalize {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (hR : 1 ≤ R) (y : Point d) :
    SpatialPotentialClass d E → SpatialPotentialAEClass d E :=
  Quotient.lift
    (fun f => Quotient.mk (spatialAESetoid d E) (ballCenteredRepresentative R hR y f))
    (fun f g hfg => Quotient.sound (ballCenteredRepresentative_gaugeInvariant R hR y f g hfg))

theorem ballCenteredRepresentative_value {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (hR : 1 ≤ R) (y x : Point d) (f : SpatialPotential d E) :
    (ballCenteredRepresentative R hR y f).value x =
      f.value x - ⨍ z in Metric.ball y (2 * R), f.value z ∂volume := rfl

/-- A concrete nonconstant local-integrable field for exercising normalization. -/
noncomputable def firstCoordinatePotential (d : ℕ) [NeZero d] : ScalarSpatialPotential d where
  value x := x ⟨0, NeZero.pos d⟩
  locallyIntegrable := by
    have hcoord : Continuous (fun x : Point d => x ⟨0, NeZero.pos d⟩) :=
      PiLp.continuous_apply 2 (fun _ : Fin d => ℝ)
        (⟨0, NeZero.pos d⟩ : Fin d)
    exact hcoord.locallyIntegrable

theorem continuous_firstCoordinatePotential (d : ℕ) [NeZero d] :
    Continuous (firstCoordinatePotential d).value :=
  PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) (⟨0, NeZero.pos d⟩ : Fin d)

noncomputable def constantScalarPotential (d : ℕ) (c : ℝ) : ScalarSpatialPotential d where
  value := fun _ => c
  locallyIntegrable := locallyIntegrable_const _

theorem sourceNormalizedFirstCoordinate_not_ae_constant {d : ℕ} [NeZero d]
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (c : ℝ) :
    ¬ (mollifierCenteredRepresentative (sourceScaledSpatialKernel ζ R y hR)
        (firstCoordinatePotential d)).value =ᵐ[volume] fun _ => c := by
  intro hae
  let centered := mollifierCenteredRepresentative (sourceScaledSpatialKernel ζ R y hR)
    (firstCoordinatePotential d)
  have hcont : Continuous centered.value := by
    dsimp [centered, mollifierCenteredRepresentative]
    exact (continuous_firstCoordinatePotential d).sub continuous_const
  have hconst : Continuous (fun _ : Point d => c) := continuous_const
  have hpoint := (hcont.ae_eq_iff_eq volume hconst).mp hae
  have hzero := congrFun hpoint (0 : Point d)
  have hone := congrFun hpoint (EuclideanSpace.single ⟨0, NeZero.pos d⟩ 1)
  let m := mollifierMean (sourceScaledSpatialKernel ζ R y hR)
    (firstCoordinatePotential d)
  have hzero' : (0 : ℝ) - m = c := by
    simpa [m, centered, mollifierCenteredRepresentative, firstCoordinatePotential] using hzero
  have hone' : (1 : ℝ) - m = c := by
    simpa [m, centered, mollifierCenteredRepresentative, firstCoordinatePotential,
      EuclideanSpace.single_apply] using hone
  linarith

theorem sourceMollifierNormalize_firstCoordinate_ne_constant {d : ℕ} [NeZero d]
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d) (c : ℝ) :
    sourceMollifierNormalize ζ R hR y
        (Quotient.mk (spatialGaugeSetoid d ℝ) (firstCoordinatePotential d)) ≠
      Quotient.mk (spatialAESetoid d ℝ) (constantScalarPotential d c) := by
  rw [sourceMollifierNormalize_mk]
  intro hclass
  have hae := Quotient.exact hclass
  change (mollifierCenteredRepresentative (sourceScaledSpatialKernel ζ R y hR)
      (firstCoordinatePotential d)).value =ᵐ[volume] fun _ => c at hae
  exact sourceNormalizedFirstCoordinate_not_ae_constant ζ R hR y c hae

#print axioms sourceScaledMollifierKernel
#print axioms sourceScaledSpatialKernel
#print axioms mollifierMean
#print axioms mollifierCenteredRepresentative
#print axioms mollifierCenteredRepresentative_gaugeInvariant
#print axioms mollifierCenteredRepresentative_addConstant
#print axioms mollifierNormalize
#print axioms mollifierNormalize_addConstant
#print axioms integral_mollifierCenteredRepresentative_eq_zero
#print axioms integral_sourceMollifierCenteredRepresentative_eq_zero
#print axioms correctorBallMean
#print axioms ballCenteredRepresentative_gaugeInvariant
#print axioms ballNormalize
#print axioms continuous_representative_unique_at
#print axioms sourceMollifierCenteredRepresentative_pointwise_independent
#print axioms sourceNormalizedFirstCoordinate_not_ae_constant
#print axioms sourceMollifierNormalize_firstCoordinate_ne_constant

end EinsteinRelation.Correctors.NormalizedSpatialRepresentativeSupport
