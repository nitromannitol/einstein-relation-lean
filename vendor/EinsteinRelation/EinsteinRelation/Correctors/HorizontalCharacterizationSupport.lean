import EinsteinRelation.Calculus.HorizontalSobolev
import EinsteinRelation.Correctors.HorizontalGeneratorsIbP
import EinsteinRelation.Correctors.HorizontalCoreSeparatesLp
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory
open Filter
open scoped Topology

noncomputable section

namespace EinsteinRelation.Correctors

/-- Weak horizontal derivatives are defined by their distributional action on the actual
bounded smooth translation core. The integrability clauses make each pairing an actual
Bochner integral; L² representatives enter only through their almost-everywhere classes. -/
def HasWeakHorizontalLpDerivative {d : ℕ} (Q : Measure (FieldPair d))
    (i : Fin d) (f g : Lp ℝ 2 Q) : Prop :=
  ∀ H : FieldPair d → ℝ, IsHorizontalTest H →
    Integrable (fun ω => f ω * horizontalDerivative i H ω) Q ∧
    Integrable (fun ω => g ω * H ω) Q ∧
    (∫ ω, f ω * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, g ω * H ω ∂Q)

theorem HasWeakHorizontalLpDerivative.unique {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {i : Fin d} {f g g' : Lp ℝ 2 Q}
    (hg : HasWeakHorizontalLpDerivative Q i f g)
    (hg' : HasWeakHorizontalLpDerivative Q i f g') : g = g' := by
  have hzero : g - g' = 0 :=
    eq_zero_of_horizontalCore_pairing_eq_zero Q hQ (g - g') (by
      intro H hH
      have h₁ := (hg H hH).2.2
      have h₂ := (hg' H hH).2.2
      have heq : (∫ ω, g ω * H ω ∂Q) = ∫ ω, g' ω * H ω ∂Q := by linarith
      have hrep : (fun ω => (g - g') ω * H ω) =ᵐ[Q]
          (fun ω => g ω * H ω - g' ω * H ω) := by
        filter_upwards [Lp.coeFn_sub g g'] with ω hω
        rw [hω]
        simp only [Pi.sub_apply]
        ring
      calc
        (∫ ω, (g - g') ω * H ω ∂Q) =
            ∫ ω, (g ω * H ω - g' ω * H ω) ∂Q := integral_congr_ae hrep
        _ = 0 := by
          rw [integral_sub (hg H hH).2.1 (hg' H hH).2.1]
          rw [heq]
          ring)
  exact sub_eq_zero.mp hzero

theorem hasHorizontalLpDerivative_to_weak {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {i : Fin d} {f g : Lp ℝ 2 Q}
    (hf : HasHorizontalLpDerivative Q hQ i f g) :
    HasWeakHorizontalLpDerivative Q i f g := by
  intro H hH
  let v : Lp ℝ 2 Q := (hH.memLp Q 2).toLp H
  let w : Lp ℝ 2 Q := (hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H)
  have hv : HasHorizontalLpDerivative Q hQ i v w :=
    tendsto_horizontalCore_differenceQuotient Q hQ hH i
  have hparts := horizontalGenerators_integration_by_parts
    Q hQ i v w f g hv hf
  have hw : w =ᵐ[Q] horizontalDerivative i H :=
    (hH.memLp_derivative Q 2 i).coeFn_toLp
  have hvfun : v =ᵐ[Q] H := (hH.memLp Q 2).coeFn_toLp
  refine ⟨hparts.1.congr ?_, hparts.2.1.congr ?_, ?_⟩
  · filter_upwards [hw] with ω hω
    rw [hω]
    ring
  · filter_upwards [hvfun] with ω hω
    rw [hω]
    ring
  · calc
      (∫ ω, f ω * horizontalDerivative i H ω ∂Q) =
          ∫ ω, w ω * f ω ∂Q := by
        apply integral_congr_ae
        filter_upwards [hw] with ω hω
        rw [hω]
        ring
      _ = -(∫ ω, v ω * g ω ∂Q) := hparts.2.2
      _ = -(∫ ω, g ω * H ω ∂Q) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hvfun] with ω hω
        rw [hω]
        ring

private theorem horizontalTest_translate {d : ℕ} {H : FieldPair d → ℝ}
    (hH : IsHorizontalTest H) (x : Vec d) :
    IsHorizontalTest (fun ω => H (translate x ω)) := by
  refine ⟨hH.1.comp (Probability.measurable_translate x), ?_, ?_⟩
  · intro ω
    have horbit : orbit (fun η => H (translate x η)) ω = orbit H (translate x ω) := by
      funext y
      simp [orbit, translate_add, add_comm]
    rw [horbit]
    exact hH.2.1 (translate x ω)
  · intro coordinates
    obtain ⟨M, hM⟩ := hH.2.2 coordinates
    refine ⟨M, ?_⟩
    intro ω y
    have horbit : orbit (fun η => H (translate x η)) ω = orbit H (translate x ω) := by
      funext z
      simp [orbit, translate_add, add_comm]
    rw [horbit]
    exact hM (translate x ω) y

private theorem horizontalDerivative_translate_observable {d : ℕ} (i : Fin d)
    {H : FieldPair d → ℝ} (x : Vec d) (ω : FieldPair d) :
    horizontalDerivative i (fun η => H (translate x η)) ω =
      horizontalDerivative i H (translate x ω) := by
  have horbit : orbit (fun η => H (translate x η)) ω = orbit H (translate x ω) := by
    funext y
    simp [orbit, translate_add, add_comm]
  simp only [horizontalDerivative, horbit]

private theorem coreValue_translate_eq {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {H : FieldPair d → ℝ}
    (hH : IsHorizontalTest H) (x : Vec d) :
    ((horizontalTest_translate hH x).memLp Q 2).toLp (fun ω => H (translate x ω)) =
      translationLp Q hQ x ((hH.memLp Q 2).toLp H) := by
  apply Lp.ext
  have hsource := (hH.memLp Q 2).coeFn_toLp
  have hsourceShift := (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae hsource
  filter_upwards [((horizontalTest_translate hH x).memLp Q 2).coeFn_toLp,
    coeFn_translationLp Q hQ x ((hH.memLp Q 2).toLp H), hsourceShift] with ω hshift htrans hsrc
  rw [hshift, htrans, hsrc]

private theorem coreDerivative_translate_eq {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {H : FieldPair d → ℝ}
    (hH : IsHorizontalTest H) (i : Fin d) (x : Vec d) :
    ((horizontalTest_translate hH x).memLp_derivative Q 2 i).toLp
        (horizontalDerivative i (fun ω => H (translate x ω))) =
      translationLp Q hQ x
        ((hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H)) := by
  apply Lp.ext
  have hsource := (hH.memLp_derivative Q 2 i).coeFn_toLp
  have hsourceShift := (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae hsource
  filter_upwards [
    ((horizontalTest_translate hH x).memLp_derivative Q 2 i).coeFn_toLp,
    coeFn_translationLp Q hQ x
      ((hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H)), hsourceShift]
    with ω hshift htrans hsrc
  rw [hshift, htrans, hsrc, horizontalDerivative_translate_observable]

private theorem translationLp_unitVector_add {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (i : Fin d) (s r : ℝ) (f : Lp ℝ 2 Q) :
    translationLp Q hQ ((s + r) • unitVector i) f =
      translationLp Q hQ (s • unitVector i) (translationLp Q hQ (r • unitVector i) f) := by
  rw [add_smul, translationLp_add]

private theorem translationLp_unitVector_sub {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (i : Fin d) (s r : ℝ) (f : Lp ℝ 2 Q) :
    translationLp Q hQ (r • unitVector i) f =
      translationLp Q hQ (s • unitVector i) (translationLp Q hQ ((r - s) • unitVector i) f) := by
  have hsplit : r • unitVector i = (s + (r - s)) • unitVector i := by
    congr 1
    ring
  rw [hsplit]
  exact translationLp_unitVector_add Q hQ i s (r - s) f

private theorem hasDerivAt_translationLp_orbit {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (i : Fin d) (f g : Lp ℝ 2 Q)
    (hfg : HasHorizontalLpDerivative Q hQ i f g) (s : ℝ) :
    HasDerivAt (fun r : ℝ => translationLp Q hQ (r • unitVector i) f)
      (translationLp Q hQ (s • unitVector i) g) s := by
  have hzero : translationLp Q hQ ((0 : ℝ) • unitVector i) f = f := by
    rw [zero_smul, translationLp_zero]
  have hG : HasDerivAt (fun h : ℝ => translationLp Q hQ (h • unitVector i) f) g (s - s) := by
    rw [sub_self]
    have hslope : slope (fun h : ℝ => translationLp Q hQ (h • unitVector i) f) 0 =
        fun t : ℝ => t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f) := by
      funext t
      simp only [slope_def_module, sub_zero, hzero]
    rw [hasDerivAt_iff_tendsto_slope, hslope]
    exact hfg
  have hH : HasDerivAt
      (fun r : ℝ => translationLp Q hQ ((r - s) • unitVector i) f) g s :=
    HasDerivAt.comp_sub_const s s hG
  have hL : HasDerivAt
      (⇑(translationLp Q hQ (s • unitVector i)).toContinuousLinearMap ∘
        fun r : ℝ => translationLp Q hQ ((r - s) • unitVector i) f)
      (translationLp Q hQ (s • unitVector i) g) s :=
    (translationLp Q hQ (s • unitVector i)).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt_of_eq s hH rfl
  have hfun : (fun r : ℝ => translationLp Q hQ (r • unitVector i) f) =
      ⇑(translationLp Q hQ (s • unitVector i)).toContinuousLinearMap ∘
        fun r : ℝ => translationLp Q hQ ((r - s) • unitVector i) f := by
    funext r
    exact translationLp_unitVector_sub Q hQ i s r f
  rw [hfun]
  exact hL

private theorem hasDerivAt_translationLp_neg_orbit {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (i : Fin d) (f g : Lp ℝ 2 Q)
    (hfg : HasHorizontalLpDerivative Q hQ i f g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => translationLp Q hQ ((-s) • unitVector i) f)
      (-(translationLp Q hQ ((-t) • unitVector i) g)) t := by
  have hline := hasDerivAt_translationLp_orbit Q hQ i f g hfg (-t)
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := hasDerivAt_neg t
  have hcomp := HasDerivAt.scomp t hline hneg
  refine hcomp.congr_deriv ?_
  simp

private theorem realInner_eq_integral_mul {d : ℕ} (Q : Measure (FieldPair d))
    (u v : Lp ℝ 2 Q) : inner ℝ u v = ∫ ω, u ω * v ω ∂Q := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    simp only [RCLike.inner_apply, conj_trivial]
    ring

private theorem weakHorizontal_generator_pairing {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (i : Fin d)
    (f g : Lp ℝ 2 Q) (hweak : HasWeakHorizontalLpDerivative Q i f g)
    {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) (t : ℝ) :
    inner ℝ (translationLp Q hQ (t • unitVector i) f - f)
        ((hH.memLp Q 2).toLp H) =
      inner ℝ (∫ s in (0 : ℝ)..t, translationLp Q hQ (s • unitVector i) g)
        ((hH.memLp Q 2).toLp H) := by
  let h : Lp ℝ 2 Q := (hH.memLp Q 2).toLp H
  let dh : Lp ℝ 2 Q :=
    (hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H)
  have hgen : HasHorizontalLpDerivative Q hQ i h dh :=
    tendsto_horizontalCore_differenceQuotient Q hQ hH i
  let φ : ℝ → ℝ := fun s =>
    inner ℝ f (translationLp Q hQ ((-s) • unitVector i) h)
  have hOrbitCont : Continuous (fun s : ℝ =>
      translationLp Q hQ (s • unitVector i) g) := by
    have hpair : Continuous (fun s : ℝ => (s • unitVector i, g)) := by fun_prop
    exact (continuous_translationLp Q hQ).comp hpair
  have hScalarCont : Continuous (fun s : ℝ =>
      inner ℝ (translationLp Q hQ (s • unitVector i) g) h) :=
    hOrbitCont.inner continuous_const
  have hderiv : ∀ s : ℝ, HasDerivAt φ
      (inner ℝ (translationLp Q hQ (s • unitVector i) g) h) s := by
    intro s
    let x : Vec d := (-s) • unitVector i
    let Hx : FieldPair d → ℝ := fun ω => H (translate x ω)
    have hHx : IsHorizontalTest Hx := horizontalTest_translate hH x
    let hx : Lp ℝ 2 Q := (hHx.memLp Q 2).toLp Hx
    let dhx : Lp ℝ 2 Q := (hHx.memLp_derivative Q 2 i).toLp
      (horizontalDerivative i Hx)
    have hWeak := hweak Hx hHx
    have hValueEq : hx = translationLp Q hQ x h := by
      exact coreValue_translate_eq Q hQ hH x
    have hDerivativeEq : dhx = translationLp Q hQ x dh := by
      exact coreDerivative_translate_eq Q hQ hH i x
    have hWeakInner : inner ℝ f (translationLp Q hQ x dh) =
        -inner ℝ g (translationLp Q hQ x h) := by
      have hDae := (hHx.memLp_derivative Q 2 i).coeFn_toLp
      have hVae := (hHx.memLp Q 2).coeFn_toLp
      have hDint : (∫ ω, f ω * dhx ω ∂Q) =
          ∫ ω, f ω * horizontalDerivative i Hx ω ∂Q := by
        apply integral_congr_ae
        filter_upwards [hDae] with ω hω
        rw [hω]
      have hVint : (∫ ω, g ω * hx ω ∂Q) = ∫ ω, g ω * Hx ω ∂Q := by
        apply integral_congr_ae
        filter_upwards [hVae] with ω hω
        rw [hω]
      rw [← hDerivativeEq, ← hValueEq,
        realInner_eq_integral_mul Q f dhx, realInner_eq_integral_mul Q g hx]
      calc
        (∫ ω, f ω * dhx ω ∂Q) =
            ∫ ω, f ω * horizontalDerivative i Hx ω ∂Q := hDint
        _ = -(∫ ω, g ω * Hx ω ∂Q) := hWeak.2.2
        _ = -(∫ ω, g ω * hx ω ∂Q) := by rw [hVint]
    have hAdj : inner ℝ g (translationLp Q hQ x h) =
        inner ℝ (translationLp Q hQ (-x) g) h := by
      have hcancel : translationLp Q hQ (-x) (translationLp Q hQ x h) = h := by
        rw [← translationLp_add Q hQ (-x) x h]
        simp [translationLp_zero]
      have hmap := (translationLp Q hQ (-x)).inner_map_map g
        (translationLp Q hQ x h)
      rw [hcancel] at hmap
      exact hmap.symm
    have hminus : -x = s • unitVector i := by
      dsimp [x]
      simp
    have hAdj' : inner ℝ g (translationLp Q hQ x h) =
        inner ℝ (translationLp Q hQ (s • unitVector i) g) h := by
      rw [hAdj, hminus]
    have hOrbit := hasDerivAt_translationLp_neg_orbit Q hQ i h dh hgen s
    have hInner := (innerSL ℝ f).hasFDerivAt.comp_hasDerivAt_of_eq s hOrbit rfl
    have hInner' : HasDerivAt φ (inner ℝ f (-(translationLp Q hQ x dh))) s := by
      exact hInner
    have hderivValue : inner ℝ f (-(translationLp Q hQ x dh)) =
        inner ℝ (translationLp Q hQ (s • unitVector i) g) h := by
      calc
        inner ℝ f (-(translationLp Q hQ x dh)) =
            -inner ℝ f (translationLp Q hQ x dh) := by rw [inner_neg_right]
        _ = inner ℝ g (translationLp Q hQ x h) := by rw [hWeakInner]; ring
        _ = inner ℝ (translationLp Q hQ (s • unitVector i) g) h := hAdj'
    rw [hderivValue] at hInner'
    exact hInner'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := φ) (f' := fun s => inner ℝ (translationLp Q hQ (s • unitVector i) g) h)
    (fun s _ => hderiv s) (hScalarCont.intervalIntegrable 0 t)
  have hVectorIntegral :
      (∫ s in (0 : ℝ)..t, inner ℝ (translationLp Q hQ (s • unitVector i) g) h) =
        inner ℝ (∫ s in (0 : ℝ)..t, translationLp Q hQ (s • unitVector i) g) h := by
    have hmap := (innerSL ℝ h).intervalIntegral_comp_comm (μ := volume)
      (hOrbitCont.intervalIntegrable (μ := volume) 0 t)
    calc
      (∫ s in (0 : ℝ)..t, inner ℝ (translationLp Q hQ (s • unitVector i) g) h) =
          ∫ s in (0 : ℝ)..t, inner ℝ h (translationLp Q hQ (s • unitVector i) g) := by
            congr 1
            funext s
            exact real_inner_comm _ _
      _ = inner ℝ h (∫ s in (0 : ℝ)..t, translationLp Q hQ (s • unitVector i) g) := by
            simpa only [innerSL_apply_apply] using hmap
      _ = inner ℝ (∫ s in (0 : ℝ)..t, translationLp Q hQ (s • unitVector i) g) h :=
            real_inner_comm _ _
  have hleft : inner ℝ (translationLp Q hQ (t • unitVector i) f) h = φ t := by
    dsimp [φ]
    have hcancel : translationLp Q hQ (t • unitVector i)
        (translationLp Q hQ ((-t) • unitVector i) h) = h := by
      rw [← translationLp_add Q hQ (t • unitVector i) ((-t) • unitVector i) h]
      simp [neg_smul, translationLp_zero]
    have hmap := (translationLp Q hQ (t • unitVector i)).inner_map_map f
      (translationLp Q hQ ((-t) • unitVector i) h)
    rw [hcancel] at hmap
    exact hmap
  have hzero : φ 0 = inner ℝ f h := by
    simp [φ, translationLp_zero]
  calc
    inner ℝ (translationLp Q hQ (t • unitVector i) f - f) h =
        inner ℝ (translationLp Q hQ (t • unitVector i) f) h - inner ℝ f h :=
          inner_sub_left _ _ _
    _ = φ t - φ 0 := by rw [hleft, hzero]
    _ = ∫ s in (0 : ℝ)..t,
          inner ℝ (translationLp Q hQ (s • unitVector i) g) h := hFTC.symm
    _ = inner ℝ (∫ s in (0 : ℝ)..t,
          translationLp Q hQ (s • unitVector i) g) h := hVectorIntegral

private theorem hasHorizontalLpDerivative_of_weak {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (i : Fin d)
    (f g : Lp ℝ 2 Q) (hweak : HasWeakHorizontalLpDerivative Q i f g) :
    HasHorizontalLpDerivative Q hQ i f g := by
  have hfixed : ∀ t : ℝ,
      translationLp Q hQ (t • unitVector i) f - f =
        ∫ s in (0 : ℝ)..t, translationLp Q hQ (s • unitVector i) g := by
    intro t
    let v : Lp ℝ 2 Q := translationLp Q hQ (t • unitVector i) f - f -
      ∫ s in (0 : ℝ)..t, translationLp Q hQ (s • unitVector i) g
    have hvpair : ∀ H : FieldPair d → ℝ, ∀ hH : IsHorizontalTest H,
        (∫ ω, v ω * H ω ∂Q) = 0 := by
      intro H hH
      let h : Lp ℝ 2 Q := (hH.memLp Q 2).toLp H
      have hp := weakHorizontal_generator_pairing Q hQ i f g hweak hH t
      have hinner : inner ℝ v h = 0 := by
        dsimp [v]
        rw [inner_sub_left, hp]
        exact sub_self _
      calc
        (∫ ω, v ω * H ω ∂Q) = ∫ ω, v ω * h ω ∂Q := by
          apply integral_congr_ae
          filter_upwards [(hH.memLp Q 2).coeFn_toLp] with ω hω
          rw [hω]
        _ = inner ℝ v h := (realInner_eq_integral_mul Q v h).symm
        _ = 0 := hinner
    have hvzero := eq_zero_of_horizontalCore_pairing_eq_zero Q hQ v hvpair
    change (translationLp Q hQ (t • unitVector i) f - f) -
      (∫ s in (0 : ℝ)..t, translationLp Q hQ (s • unitVector i) g) = 0 at hvzero
    exact sub_eq_zero.mp hvzero
  have hlimit : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f))
      (𝓝[≠] (0 : ℝ)) (nhds g) := by
    have hOrbitCont : Continuous (fun s : ℝ =>
        translationLp Q hQ (s • unitVector i) g) := by
      have hpair : Continuous (fun s : ℝ => (s • unitVector i, g)) := by fun_prop
      exact (continuous_translationLp Q hQ).comp hpair
    have hIntegralDeriv := intervalIntegral.integral_hasDerivAt_right
      (hOrbitCont.intervalIntegrable 0 0)
      (hOrbitCont.stronglyMeasurableAtFilter volume (𝓝 0)) hOrbitCont.continuousAt
    have hDeriv : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..t,
        translationLp Q hQ (s • unitVector i) g) g 0 := by
      convert (show HasFDerivAt _ _ _ from hIntegralDeriv).hasDerivAt using 1
      simp [translationLp_zero]
    have hlimIntegral : Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (∫ s in (0 : ℝ)..t,
          translationLp Q hQ (s • unitVector i) g)) (𝓝[≠] 0) (nhds g) := by
      have hsl := hasDerivAt_iff_tendsto_slope_zero.mp hDeriv
      simpa [translationLp_zero] using hsl
    exact hlimIntegral.congr (fun t => by rw [← hfixed t])
  exact hlimit

/-- The actual strong translation-generator domain is characterized by distributional
horizontal derivatives on the bounded smooth core. The core's value density is used only to
separate an L² residual; the orbit integral identity and its derivative supply the generator limit. -/
theorem horizontalH1_iff_weakHorizontalLpDerivative {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : Lp ℝ 2 Q) :
    f ∈ horizontalH1 Q hQ ↔
      ∀ i : Fin d, ∃ g : Lp ℝ 2 Q,
        HasWeakHorizontalLpDerivative Q i f g := by
  change (∃ g : Fin d → Lp ℝ 2 Q, ∀ i,
      HasHorizontalLpDerivative Q hQ i f (g i)) ↔ _
  constructor
  · rintro ⟨g, hg⟩ i
    exact ⟨g i, hasHorizontalLpDerivative_to_weak (hg i)⟩
  · intro hf
    refine ⟨fun i => Classical.choose (hf i), ?_⟩
    intro i
    exact hasHorizontalLpDerivative_of_weak Q hQ i f (Classical.choose (hf i))
      (Classical.choose_spec (hf i))

/-- Real reduced-law consumer: a bounded smooth horizontal core representative belongs to the
strong H¹ domain for the actual physical-to-reduced pushforward law. -/
theorem reducedCore_mem_horizontalH1 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (hH.memLp (Measure.map reduce Q.measure) 2).toLp H ∈
      horizontalH1 (Measure.map reduce Q.measure)
        (Probability.isStationary_map_reduce Q.measure Q.stationary) := by
  let μ : Measure (FieldPair d) := Measure.map reduce Q.measure
  letI : IsProbabilityMeasure μ := by
    unfold μ
    infer_instance
  have hμ : IsStationary μ := by
    exact Probability.isStationary_map_reduce Q.measure Q.stationary
  change (hH.memLp μ 2).toLp H ∈ horizontalH1 μ hμ
  apply (horizontalH1_iff_weakHorizontalLpDerivative hμ _).2
  intro i
  exact ⟨(hH.memLp_derivative μ 2 i).toLp (horizontalDerivative i H),
    hasHorizontalLpDerivative_to_weak
      (tendsto_horizontalCore_differenceQuotient μ hμ hH i)⟩

/-- The core's literal spatial horizontal derivative satisfies the weak integration-by-parts
identity on the actual reduced pushforward law. -/
theorem reducedCore_has_weakHorizontalDerivative {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {H : FieldPair d → ℝ} (hH : IsHorizontalTest H)
    (i : Fin d) :
    HasWeakHorizontalLpDerivative (Measure.map reduce Q.measure) i
      ((hH.memLp (Measure.map reduce Q.measure) 2).toLp H)
      ((hH.memLp_derivative (Measure.map reduce Q.measure) 2 i).toLp
        (horizontalDerivative i H)) := by
  let μ : Measure (FieldPair d) := Measure.map reduce Q.measure
  letI : IsProbabilityMeasure μ := by
    unfold μ
    infer_instance
  have hμ : IsStationary μ := by
    exact Probability.isStationary_map_reduce Q.measure Q.stationary
  exact hasHorizontalLpDerivative_to_weak
    (tendsto_horizontalCore_differenceQuotient μ hμ hH i)

end EinsteinRelation.Correctors
