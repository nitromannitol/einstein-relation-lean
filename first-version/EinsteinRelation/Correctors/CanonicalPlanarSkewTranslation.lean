import EinsteinRelation.Correctors.CanonicalScalarTranslation
import EinsteinRelation.Correctors.CanonicalShiftedMeansFromMoments

/-! # Translation of the normalized planar skew corrector

Source: `paper/main.tex:948–963`. The independent skew entry is a weak
potential of the rotated stationary centered flux. Continuity and zero
mollifier means determine its translated additive constant.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Two planar skew matrices agree if their independent entries agree.
Source: `paper/main.tex:948–955`. -/
theorem planar_skew_eq_of_entry_eq {A B : Mat 2}
    (hA : A.transpose = -A) (hB : B.transpose = -B) (h : A 0 1 = B 0 1) : A = B := by
  have diag (M : Mat 2) (hM : M.transpose = -M) (j : Fin 2) : M j j = 0 := by
    have hj := congrArg (fun N : Mat 2 => N j j) hM
    change M j j = -M j j at hj
    linarith only [hj]
  have off (M : Mat 2) (hM : M.transpose = -M) : M 1 0 = -M 0 1 :=
    congrArg (fun N : Mat 2 => N 0 1) hM
  ext j k
  fin_cases j <;> fin_cases k
  · rw [diag A hA, diag B hB]
  · exact h
  · change A 1 0 = B 1 0
    rw [off A hA, off B hB, h]
  · rw [diag A hA, diag B hB]

/-- The normalized heat-selected planar skew field has the exact translated
column decomposition used by the Frobenius-tail cancellation estimate.
Source: `paper/main.tex:948–963`. -/
theorem ae_normalizedPlanarSkew_translation {L r₀ R : ℝ}
    (Q : EnvironmentLaw 2 L r₀) (i : Fin 2) (hR : 1 ≤ R)
    (S : FieldPair 2 → Vec 2 → Mat 2)
    (hS : HasHeatSelectedSkewCorrectorColumn (by omega) Q i S)
    (hSc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (S ω))
    (hSn : ∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (∫ z, S ω (-z) j k ∂mollifierCenterMeasure 2 R) = 0) (y : Vec 2) :
    (fun ω => S (translate y ω) (-y)) =ᵐ[reducedEnvironmentLaw Q]
      (fun ω j k => S ω 0 j k + ∫ z, (Calculus.unitMassScaledMollifier 2 R z -
        Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z j k) := by
  have hpres : MeasurePreserving (translate y)
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
    ⟨Probability.measurable_translate _, reducedEnvironmentLaw_stationary Q _⟩
  have hskew : ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ x,
      (S ω x).transpose = -(S ω x) := by
    obtain ⟨_, _, hselected⟩ := hS
    filter_upwards [hselected, hSc] with ω hω hc
    have heq : (fun x => (S ω x).transpose) = fun x => -(S ω x) :=
      MeasureTheory.Measure.eq_of_ae_eq hω.1.1 hc.matrix_transpose hc.neg
    exact congrFun heq
  have hg := hS.ae_planar_weakGradient
  filter_upwards [hg, hpres.quasiMeasurePreserving.ae hg, hSc,
    hpres.quasiMeasurePreserving.ae hSc, hSn 0 1,
    hpres.quasiMeasurePreserving.ae (hSn 0 1), hskew,
    hpres.quasiMeasurePreserving.ae hskew] with ω hu hv huc hvc hun hvn hsu hsv
  have ht : S (translate y ω) (-y) 0 1 = S ω 0 0 1 +
      ∫ z, (Calculus.unitMassScaledMollifier 2 R z -
        Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z 0 1 := by
    apply normalized_weakPotential_translation (by omega) (zero_lt_one.trans_le hR) y
      (fun x => S ω x 0 1) (fun x => S (translate y ω) x 0 1) _ hu
    · simpa only [translate_add, add_comm] using hv
    · exact (huc.matrix_elem 0 1)
    · exact (hvc.matrix_elem 0 1)
    · exact mollifier_mean_eq_zero_of_centerMean (zero_lt_one.trans_le hR) _ hun
    · exact mollifier_mean_eq_zero_of_centerMean (zero_lt_one.trans_le hR) _ hvn
  have hi := integral_weight_skew_of_ae volume
    (fun z => Calculus.unitMassScaledMollifier 2 R z -
      Calculus.unitMassScaledMollifier 2 R (z - y)) (S ω) (ae_of_all _ hsu)
  apply planar_skew_eq_of_entry_eq (hsv (-y)) _ ht
  change (S ω 0 + (show Mat 2 from fun j k => ∫ z,
    (Calculus.unitMassScaledMollifier 2 R z -
      Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z j k)).transpose = _
  rw [Matrix.transpose_add, hsu 0, hi]
  ext j k
  exact (neg_add _ _).symm

end EinsteinRelation.Correctors
