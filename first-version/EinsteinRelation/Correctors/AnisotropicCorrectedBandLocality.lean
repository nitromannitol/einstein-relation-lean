import EinsteinRelation.Correctors.AnisotropicKernelLocality

/-! # Locality of the actual corrected anisotropic bands

Source: `paper/main.tex:1079–1084`. The band, its correction and both
fluxes use one common observation window independent of the environment law.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- All five actual corrected band fields share the claimed common
window (`paper/main.tex:1079–1084`). -/
theorem anisotropicBand_corrected_locality {d : ℕ} (hd : 2 ≤ d)
    (T : Vec d ≃L[ℝ] Vec d) {L r R : ℝ} (hL : 0 < L) (hr : 0 < r) (hrR : r ≤ R)
    (hT : ∀ x, euclideanNorm (T.symm x) ≤ L * euclideanNorm x)
    {f : FieldPair d → ℝ}
    (hf : Measurable[localSigma {x : Vec d | euclideanNorm x < 33 * R}] f)
    (abar : Mat d) (i : Fin d)
    (phi : Fin d → FieldPair d → ℝ) (Dphi F : Fin d → FieldPair d → Vec d)
    (Sig : Fin d → FieldPair d → Mat d)
    (hphi : ∀ j, Measurable[localSigma {x : Vec d | euclideanNorm x < 33 * r}] (phi j))
    (hDphi : ∀ j, Measurable[localSigma {x : Vec d | euclideanNorm x < 33 * r}] (Dphi j))
    (hF : ∀ j, Measurable[localSigma {x : Vec d | euclideanNorm x < 33 * r}] (F j))
    (hSig : ∀ j, Measurable[localSigma {x : Vec d | euclideanNorm x < 33 * r}] (Sig j)) :
    let K := anisotropicBandKernel T r
    let u := horizontalMollify K f
    let Du := kernelGradient K f
    let H := fun j ω => kernelHessian K f ω j
    let W := {x : Vec d | euclideanNorm x < (33 + 2 * L) * R}
    Measurable[localSigma W] (fun ω => u ω + ∑ j, phi j ω * Du ω j) ∧
    Measurable[localSigma W] (fun ω => Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • H j ω)) ∧
    Measurable[localSigma W] (fun ω => ∑ j,
      (phi j ω • ((ω.1 0).mulVec (H j ω)) - (Sig j ω).mulVec (H j ω) + Du ω j • F j ω)) ∧
    Measurable[localSigma W]
      (fun ω => u ω • abar.mulVec (unitVector i) + ∑ j, Du ω j • (fun k => Sig j ω i k)) ∧
    Measurable[localSigma W] (fun ω => ∑ j,
      (phi j ω * dot ((ω.1 0).mulVec (unitVector i)) (H j ω) -
        (Sig j ω).mulVec (H j ω) i + Du ω j * F j ω i)) := by
  dsimp only
  letI : MeasurableSpace (FieldPair d) :=
    localSigma {x : Vec d | euclideanNorm x < (33 + 2 * L) * R}
  have hR : 0 < R := hr.trans_le hrR
  have hm (cs : List (Fin d)) := measurable_localSigma_anisotropicBand_common hd T hL hr hrR hT hf cs
  have hwindow : localSigma {x : Vec d | euclideanNorm x < 33 * r} ≤
      localSigma {x : Vec d | euclideanNorm x < (33 + 2 * L) * R} := by
    apply Probability.localSigma_mono
    intro x hx
    change euclideanNorm x < (33 + 2 * L) * R
    change euclideanNorm x < 33 * r at hx
    nlinarith [mul_pos hL hR]
  apply measurable_localSigma_scalarCorrected
    (show euclideanNorm (0 : Vec d) < (33 + 2 * L) * R by
      simp only [euclideanNorm, euclideanSq, dot, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, Real.sqrt_zero]
      positivity) abar i (hm [])
    (show Measurable[localSigma {x : Vec d | euclideanNorm x < (33 + 2 * L) * R}]
      (kernelGradient (anisotropicBandKernel T r) f) from
        measurable_pi_iff.mpr fun j => (hm [j]).neg)
    (fun j => (hphi j).mono hwindow le_rfl)
    (fun j => (hDphi j).mono hwindow le_rfl)
    (fun j => show Measurable[localSigma {x : Vec d | euclideanNorm x < (33 + 2 * L) * R}]
      (fun ω => kernelHessian (anisotropicBandKernel T r) f ω j) from
        measurable_pi_iff.mpr fun k => hm [k, j])
    (fun j => (hF j).mono hwindow le_rfl)
    (fun j => (hSig j).mono hwindow le_rfl)

end EinsteinRelation.Correctors
