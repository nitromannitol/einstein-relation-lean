import EinsteinRelation.Correctors.AnisotropicPoissonEquation
import EinsteinRelation.Correctors.LocalCorrectorRowSource

/-! # Corrected equations for the actual anisotropic Poisson band

Source: `paper/main.tex:1044–1069`. The compact anisotropic band is used
directly in both corrected weak identities. The skew row source is the
explicit residual from the local flux equation.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- The actual kernel and local correctors satisfy both one-scale
identities (`paper/main.tex:1044–1069`). -/
theorem anisotropicBand_corrected_equations {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (hd : 2 ≤ d) (abar : Mat d) (T : Vec d ≃L[ℝ] Vec d)
    (hBA : let M : Mat d := fun i j => T (unitVector j) i
      M * abar * M.transpose = 1)
    {r : ℝ} (hr : 0 < r) {f : FieldPair d → ℝ}
    (hf : Measurable f) (hf2 : MemLp f 2 Q)
    (phi : Fin d → FieldPair d → ℝ) (Dphi F : Fin d → FieldPair d → Vec d)
    (Sig : Fin d → FieldPair d → Mat d)
    (hphi : ∀ j, HasWeakHorizontalGradient Q hQ (phi j) (Dphi j))
    (hphim : ∀ j, Measurable (phi j)) (hDphim : ∀ j, Measurable (Dphi j))
    (hskew : ∀ j, ∀ ω, (Sig j ω).transpose = -(Sig j ω))
    (hrows : ∀ j i, HasWeakHorizontalDivergence Q hQ (fun ω k => Sig j ω i k)
      (fun ω => (∑ k, ω.1 0 i k * (unitVector j k + Dphi j ω k)) - abar i j - F j ω i))
    (hphi2 : ∀ j, MemLp (phi j) 2 Q)
    (hDphi2 : ∀ j i, MemLp (fun ω => Dphi j ω i) 2 Q)
    (hSig2 : ∀ j i k, MemLp (fun ω => Sig j ω i k) 2 Q)
    (hF2 : ∀ j i, MemLp (fun ω => F j ω i) 2 Q)
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C)
    (ha : ∀ᵐ ω ∂Q, (ω.1 0).transpose = ω.1 0) (habar : abar.transpose = abar)
    (i₁ : Fin d) :
    let K := anisotropicBandKernel T r
    let u := horizontalMollify K f
    let Du := kernelGradient K f
    let H := fun j ω => kernelHessian K f ω j
    let v := fun ω => u ω + ∑ j, phi j ω * Du ω j
    let Dv := fun ω => Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • H j ω)
    SatisfiesReducedGeneratorEquation Q hQ 0 v Dv
      (fun ω => horizontalMollify (anisotropicAverage T r) f ω -
        horizontalMollify (anisotropicAverage T (2 * r)) f ω)
      (fun ω => (1 / 2 : ℝ) • ∑ j,
        (phi j ω • ((ω.1 0).mulVec (H j ω)) - (Sig j ω).mulVec (H j ω) + Du ω j • F j ω)) i₁ ∧
    HasWeakHorizontalDivergence Q hQ
      (fun ω => u ω • abar.mulVec (unitVector i₁) + ∑ j, Du ω j • (fun k => Sig j ω i₁ k))
      (fun ω => dot ((ω.1 0).mulVec (unitVector i₁)) (Dv ω) -
        ∑ j, (phi j ω * dot ((ω.1 0).mulVec (unitVector i₁)) (H j ω) -
          (Sig j ω).mulVec (H j ω) i₁ + Du ω j * F j ω i₁)) := by
  dsimp only
  let K := anisotropicBandKernel T r
  let R : Fin d → FieldPair d → Vec d := fun j ω i =>
    (∑ k, ω.1 0 i k * (unitVector j k + Dphi j ω k)) - abar i j - F j ω i
  have hK := anisotropicBandKernel_contDiff hd T hr
  have hKc := anisotropicBandKernel_hasCompactSupport hd T hr
  have hm (cs : List (Fin d)) := measurable_horizontalMollify
    (coordinateIterate cs K) (KernelCalculus.contDiff_coordinateIterate hK cs).continuous.measurable hf
  have h₂ (cs : List (Fin d)) : MemLp (horizontalMollify (coordinateIterate cs K) f) 2 Q :=
    memLp_horizontalMollify hQ one_le_two (by norm_num)
      (KernelCalculus.contDiff_coordinateIterate hK cs).continuous.measurable
      (KernelCalculus.integrable_coordinateIterate hK hKc cs) hf hf2
  have hDu₂ (j : Fin d) : MemLp (fun ω => kernelGradient K f ω j) 2 Q := (h₂ [j]).neg
  have hH₂ (j i : Fin d) : MemLp (fun ω => kernelHessian K f ω j i) 2 Q := h₂ [i, j]
  have hDum : Measurable (kernelGradient K f) := measurable_pi_lambda _ fun j => (hm [j]).neg
  have hHm (j : Fin d) : Measurable (fun ω => kernelHessian K f ω j) :=
    measurable_pi_lambda _ fun i => hm [i, j]
  have hR₂ (j i : Fin d) : MemLp (fun ω => R j ω i) 2 Q :=
    memLp_localCorrector_rowSource (hDphi2 j) (hF2 j) hA abar j i
  have hflux : ∀ᵐ ω ∂Q, ∀ j, (ω.1 0).mulVec (unitVector j + Dphi j ω) =
      abar.mulVec (unitVector j) + (R j ω + F j ω) :=
    ae_of_all _ fun ω => localCorrector_flux_identity (ω.1 0) abar (fun j => Dphi j ω) (fun j => F j ω)
  have hu := hasWeakHorizontalGradient_horizontalMollify hQ hK hKc hf hf2
  have hDu := hasWeakHorizontalGradient_kernelGradient hQ hK hKc hf hf2
  constructor
  · exact satisfiesReducedGeneratorEquation_scalarCorrected abar hu hphi hphim hDphim
      (hasWeakHorizontalDivergence_anisotropicBand hQ hd abar T hBA hr hf hf2) hDu
      (fun j => ae_of_all _ (hskew j)) hrows hDum hHm hSig2 hR₂ hDu₂ hH₂ hphi2 hDphi2 hF2 hflux hA i₁
  · exact hasWeakHorizontalDivergence_scalarCorrectedDrift abar hu hDu hrows hDum hHm
      hSig2 hR₂ hDu₂ hH₂ ha habar hflux i₁

end EinsteinRelation.Correctors
