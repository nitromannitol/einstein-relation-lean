import EinsteinRelation.Correctors.StationaryCurlRealizationSupport
import EinsteinRelation.Calculus.OrbitWeakGradientSupport

/-!
# Scalar spatial and environment pairings

Source: `paper/main.tex:240-248,693-698`. The vector-valued Fubini
identification also identifies scalar horizontal orbit integrals. A single
coordinate embedding transfers the already proved result without choosing
point values of an almost-everywhere spatial representative.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

/-- Scalar samplewise integration represents the Bochner L² orbit integral. -/
theorem scalar_orbitPairing_ae {d : ℕ} [Fact (2 ≤ d)]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℝ 2 Q) (a : Vec d → ℝ) (ha : Continuous a) (hac : HasCompactSupport a) :
    (fun ω => (∫ x : Vec d, a x • translationLp Q hQ x f ∂volume) ω) =ᵐ[Q]
      fun ω => ∫ x : Vec d, a x * f (translate x ω) ∂volume := by
  let j : Fin d := ⟨0, lt_of_lt_of_le (by omega) (Fact.out : 2 ≤ d)⟩
  let S : ℝ →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (EuclideanSpace.single j 1)
  let G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q := S.compLpL 2 Q f
  let P : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj j
  have hPG : P.compLpL 2 Q G = f := by
    apply Lp.ext
    filter_upwards [P.coeFn_compLpL G, S.coeFn_compLpL f] with ω hP hS
    rw [hP, hS]
    simp [P, S, ContinuousLinearMap.smulRight_apply, EuclideanSpace.single_apply]
  have hF : (fun ω => (G ω).ofLp j) =ᵐ[Q] f := by
    filter_upwards [P.coeFn_compLpL G] with ω hω
    have hp := congrFun (congrArg (fun z : Lp ℝ 2 Q => (z : FieldPair d → ℝ)) hPG) ω
    exact hω.symm.trans hp
  have hprod : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ᵐ ω ∂Q,
      (G (translate x ω)).ofLp j = f (translate x ω) :=
    ae_of_all _ fun x => (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae hF
  have hswap : ∀ᵐ ω ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (G (translate x ω)).ofLp j = f (translate x ω) := by
    apply (Measure.ae_ae_comm ?_).mp hprod
    exact measurableSet_eq_fun
      (((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).continuous.measurable.comp
        (Lp.stronglyMeasurable G).measurable).comp Probability.continuous_translate.measurable)
      ((Lp.stronglyMeasurable f).measurable.comp Probability.continuous_translate.measurable)
  have h := StationaryCurlFubini.ae_samplewise_pairing_eq_orbit_pairing
    Q hQ G j a ha hac
  change (fun ω => (∫ x : Vec d, a x • translationLp Q hQ x
    (P.compLpL 2 Q G) ∂volume) ω) =ᵐ[Q] _ at h
  rw [hPG] at h
  filter_upwards [h, hswap] with ω hω hrep
  exact hω.trans (integral_congr_ae (hrep.mono fun x hx => congrArg (a x * ·) hx))

/-- The horizontal H¹ weak identity has the literal scalar spatial orbit
as its representative, for each fixed smooth compactly supported test. -/
theorem ae_horizontalH1_orbit_weak_test {d : ℕ} [Fact (2 ≤ d)]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : horizontalH1 Q hQ) (i : Fin d)
    (ψ : StationaryCurlRealization.SpatialTest d) :
    ∀ᵐ ω ∂Q,
      (∫ x : Vec d, (f : Lp ℝ 2 Q) (translate x ω) *
        coordinateDerivative i ψ x ∂volume) =
      -(∫ x : Vec d, (horizontalH1Gradient Q hQ f i) (translate x ω) * ψ x ∂volume) := by
  have hd : Continuous (coordinateDerivative i ψ) :=
    (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc : HasCompactSupport (coordinateDerivative i ψ) :=
    ψ.hasCompactSupport.fderiv_apply ℝ (unitVector i)
  let I : Lp ℝ 2 Q := ∫ x : Vec d, ψ x •
    translationLp Q hQ x (horizontalH1Gradient Q hQ f i) ∂volume
  have hweak := horizontalH1_orbit_hasLpWeakPartialDerivative hQ f i
    ψ.contDiff ψ.hasCompactSupport
  have hneg := Lp.coeFn_neg I
  filter_upwards [scalar_orbitPairing_ae Q hQ (f : Lp ℝ 2 Q) _ hd hc,
    scalar_orbitPairing_ae Q hQ (horizontalH1Gradient Q hQ f i) _
      ψ.contDiff.continuous ψ.hasCompactSupport, hneg] with ω hleft hright hn
  have hw := congrArg (fun z : Lp ℝ 2 Q => z ω) hweak
  have hl : (∫ x : Vec d, coordinateDerivative i ψ x *
      (f : Lp ℝ 2 Q) (translate x ω) ∂volume) =
      -(∫ x : Vec d, ψ x * (horizontalH1Gradient Q hQ f i) (translate x ω) ∂volume) :=
    hleft.symm.trans (hw.trans (hn.trans (congrArg Neg.neg hright)))
  simpa only [mul_comm] using hl

end EinsteinRelation.Correctors
