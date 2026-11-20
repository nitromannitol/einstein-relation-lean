import HCPoly.Provider.Regularity.CorrectorRealRadiusNegOne
import HCPoly.Analytic.TestNorms
import HCPoly.Analytic.AffineNegSobolevNorm

/-!
# Real pairings bounded by the normalized negative-one norm

For a smooth compactly supported vector test of normalized `H¹` norm squared at most `K`, the
normalized pairing with a field is at most `√K` times a real bound on the normalized `H⁻¹`
norm of the field, in absolute value, in the vocabulary of Armstrong, Kuusi and Loher,
*Homogenization at a polynomial scale in high contrast*.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open _root_.Homogenization _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem dualPairing_eq_ofReal {V : Set (Vec d)} {F ψ : Vec d → Vec d}
    (hint : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume) :
    dualPairing V F ψ = ENNReal.ofReal (volumeAverage V fun x => vecDot (F x) (ψ x)) := by
  simp [dualPairing, hint]

/-- The absolute normalized pairing is bounded by the test norm and the negative-one norm. -/
theorem abs_volumeAverage_le_of_negOneNorm_le {V : Set (Vec d)} {F ψ : Vec d → Vec d}
    {K N : ℝ} (hK : 0 < K) (hN : 0 ≤ N) (htest : IsLocalVecTest V ψ)
    (hint : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume)
    (hnorm : h1NormSq V ψ ≤ ENNReal.ofReal K) (hneg : negOneNorm V F ≤ ENNReal.ofReal N) :
    |volumeAverage V fun x => vecDot (F x) (ψ x)| ≤ Real.sqrt K * N := by
  have hdiff : Differentiable ℝ ψ := htest.contDiff.differentiable (by simp)
  have hbound (φ : Vec d → Vec d) (hφ : IsLocalVecTest V φ)
      (hφint : IntegrableOn (fun x => vecDot (F x) (φ x)) V volume)
      (hφnorm : h1NormSq V φ ≤ ENNReal.ofReal K) :
      volumeAverage V (fun x => vecDot (F x) (φ x)) ≤ Real.sqrt K * N := by
    have h := dualPairing_le_negOneNorm_of_h1NormSq_le F φ hK hφ hφnorm
    rw [dualPairing_eq_ofReal hφint] at h
    have h2 : ENNReal.ofReal (volumeAverage V fun x => vecDot (F x) (φ x)) ≤
        ENNReal.ofReal (Real.sqrt K * N) := by
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg K)]
      refine h.trans ?_
      gcongr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
  have hpos := hbound ψ htest hint hnorm
  have hneg' : IsLocalVecTest V (fun x => (-1 : ℝ) • ψ x) := htest.const_smul _
  have hfun : (fun x => vecDot (F x) ((-1 : ℝ) • ψ x)) = fun x => -vecDot (F x) (ψ x) := by
    funext x
    simp [vecDot, Finset.sum_neg_distrib]
  have hnegint : IntegrableOn (fun x => vecDot (F x) ((-1 : ℝ) • ψ x)) V volume := by
    rw [hfun]
    exact hint.neg
  have hnegnorm : h1NormSq V (fun x => (-1 : ℝ) • ψ x) ≤ ENNReal.ofReal K := by
    rw [h1NormSq_smul V (-1) hdiff]
    simpa using hnorm
  have hneg2 := hbound _ hneg' hnegint hnegnorm
  have hflip : volumeAverage V (fun x => vecDot (F x) ((-1 : ℝ) • ψ x)) =
      -volumeAverage V (fun x => vecDot (F x) (ψ x)) := by
    unfold volumeAverage
    rw [hfun, integral_neg, mul_neg]
  rw [hflip] at hneg2
  exact abs_le.mpr ⟨by linarith, hpos⟩

end EinsteinFull.Homogenization
