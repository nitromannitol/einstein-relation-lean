import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import EinsteinFull.Homogenization.KernelConvolutionL2

/-!
# Second derivatives of convolutions with an integrable kernel

For an integrable kernel `κ` and a smooth compactly supported function `ψ` on `ℝ^d`, the
convolution `U = κ * ψ` is differentiable with `∂ᵢ U = κ * ∂ᵢ ψ`, and all its derivatives are
square integrable. Two integrations by parts give the identity
`∫ (∂ᵢ∂ⱼ U)² = ∫ ∂ᵢ∂ᵢ U ∂ⱼ∂ⱼ U`, and hence `∑ᵢⱼ ‖∂ᵢ∂ⱼ U‖₂² = ‖ΔU‖₂²`. This is the `L²` estimate
of second derivatives by the Laplacian on which the Calderón–Zygmund bound for the heat formula
(6.7) of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, rests.
-/

open MeasureTheory
open scoped ENNReal Convolution

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors

variable {d : ℕ}

/-- A smooth compactly supported function on `ℝ^d`. -/
def IsSmoothCompact (ψ : Vec d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ

theorem IsSmoothCompact.coordinateDerivative {ψ : Vec d → ℝ} (h : IsSmoothCompact ψ)
    (i : Fin d) : IsSmoothCompact (coordinateDerivative i ψ) :=
  ⟨((contDiff_infty_iff_fderiv.mp h.1).2).clm_apply contDiff_const,
    h.2.fderiv_apply ℝ (unitVector i)⟩

theorem IsSmoothCompact.contDiff_one {ψ : Vec d → ℝ} (h : IsSmoothCompact ψ) :
    ContDiff ℝ 1 ψ :=
  h.1.of_le (by exact_mod_cast le_top)

theorem IsSmoothCompact.memLp {ψ : Vec d → ℝ} (h : IsSmoothCompact ψ) :
    MemLp ψ 2 volume :=
  h.1.continuous.memLp_of_hasCompactSupport h.2

/-- Mixed coordinate derivatives of a smooth function commute. -/
theorem coordinateDerivative_comm {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i j : Fin d) :
    EinsteinRelation.coordinateDerivative i (EinsteinRelation.coordinateDerivative j ψ) =
      EinsteinRelation.coordinateDerivative j (EinsteinRelation.coordinateDerivative i ψ) := by
  ext x
  have hinner : (2 : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
  have hn : minSmoothness ℝ 2 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact_mod_cast hinner
  have hs := (hψ.contDiffAt (x := x)).isSymmSndFDerivAt hn
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y) x := by
    have hbound : (1 : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact_mod_cast hinner
    exact ((hψ.contDiffAt (x := x)).fderiv_right hbound).differentiableAt (by norm_num)
  have happly (v w : Vec d) :
      fderiv ℝ (fun y => fderiv ℝ ψ y v) x w =
        (fderiv ℝ (fderiv ℝ ψ) x w) v := by
    have h := fderiv_clm_apply hd (differentiableAt_const (x := x) v)
    have h' := congrArg (fun L : Vec d →L[ℝ] ℝ => L w) h
    simpa using h'
  have hswap := hs.iteratedFDeriv_cons (v := unitVector i) (w := unitVector j)
  change fderiv ℝ (EinsteinRelation.coordinateDerivative j ψ) x (unitVector i) =
    fderiv ℝ (EinsteinRelation.coordinateDerivative i ψ) x (unitVector j)
  rw [show EinsteinRelation.coordinateDerivative j ψ = fun y => fderiv ℝ ψ y (unitVector j) by rfl,
      show EinsteinRelation.coordinateDerivative i ψ = fun y => fderiv ℝ ψ y (unitVector i) by rfl]
  rw [happly (unitVector j) (unitVector i), happly (unitVector i) (unitVector j)]
  simpa [iteratedFDeriv_two_apply] using hswap

/-- The convolution `κ * F`, `(κ * F)(x) = ∫ κ(x - y) F(y) dy`. -/
noncomputable def kconv (κ F : Vec d → ℝ) : Vec d → ℝ :=
  κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F

theorem kconv_apply (κ F : Vec d → ℝ) (x : Vec d) :
    kconv κ F x = ∫ y, κ (x - y) * F y := by
  rw [kconv, convolution_lsmul_swap]
  simp only [smul_eq_mul]

theorem hasFDerivAt_kconv {κ F : Vec d → ℝ} (hκ : LocallyIntegrable κ volume)
    (hF : IsSmoothCompact F) (x : Vec d) :
    HasFDerivAt (kconv κ F)
      ((κ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Vec d), volume] fderiv ℝ F) x) x :=
  hF.2.hasFDerivAt_convolution_right _ hκ hF.contDiff_one x

theorem differentiable_kconv {κ F : Vec d → ℝ} (hκ : LocallyIntegrable κ volume)
    (hF : IsSmoothCompact F) : Differentiable ℝ (kconv κ F) := fun x =>
  (hasFDerivAt_kconv hκ hF x).differentiableAt

/-- Differentiation falls on the smooth compactly supported factor. -/
theorem coordinateDerivative_kconv {κ F : Vec d → ℝ} (hκ : LocallyIntegrable κ volume)
    (hF : IsSmoothCompact F) (i : Fin d) :
    EinsteinRelation.coordinateDerivative i (kconv κ F) =
      kconv κ (EinsteinRelation.coordinateDerivative i F) := by
  funext x
  unfold EinsteinRelation.coordinateDerivative
  rw [(hasFDerivAt_kconv hκ hF x).fderiv,
    convolution_precompR_apply _ hκ (hF.2.fderiv ℝ)
      (hF.1.continuous_fderiv (by simp)) x (unitVector i)]
  rfl

theorem memLp_kconv {κ F : Vec d → ℝ} (hκ : Measurable κ) (hκ1 : ∫⁻ z, ‖κ z‖ₑ ≠ ⊤)
    (hF : IsSmoothCompact F) : MemLp (kconv κ F) 2 volume := by
  have h := memLp_kernel hκ hκ1 hF.1.continuous.measurable hF.memLp
  have heq : kconv κ F = fun x => ∫ y, κ (x - y) * F y := funext (kconv_apply κ F)
  rw [heq]
  exact h

section IntegrationByParts

variable {κ : Vec d → ℝ} (hκm : Measurable κ) (hκ1 : ∫⁻ z, ‖κ z‖ₑ ≠ ⊤)
include hκm hκ1

theorem locallyIntegrable_of_lintegral : LocallyIntegrable κ volume :=
  (show Integrable κ volume from ⟨hκm.aestronglyMeasurable, hκ1.lt_top⟩).locallyIntegrable

theorem integrable_kconv_mul {F G : Vec d → ℝ} (hF : IsSmoothCompact F) (hG : IsSmoothCompact G) :
    Integrable (fun x => kconv κ F x * kconv κ G x) volume :=
  (memLp_kconv hκm hκ1 hF).integrable_mul (memLp_kconv hκm hκ1 hG)

/-- Integration by parts between two convolutions with the same kernel. -/
theorem integral_kconv_mul_kconv_coordinateDerivative {F G : Vec d → ℝ}
    (hF : IsSmoothCompact F) (hG : IsSmoothCompact G) (i : Fin d) :
    ∫ x, kconv κ F x * kconv κ (EinsteinRelation.coordinateDerivative i G) x =
      -∫ x, kconv κ (EinsteinRelation.coordinateDerivative i F) x * kconv κ G x := by
  have hκ := locallyIntegrable_of_lintegral hκm hκ1
  have hcd : ∀ H : Vec d → ℝ, IsSmoothCompact H → ∀ x,
      fderiv ℝ (kconv κ H) x (unitVector i) =
        kconv κ (EinsteinRelation.coordinateDerivative i H) x := fun H hH x =>
    congrFun (coordinateDerivative_kconv hκ hH i) x
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := kconv κ F) (g := kconv κ G) (v := unitVector i)
    (by simpa only [hcd F hF] using
      integrable_kconv_mul hκm hκ1 (hF.coordinateDerivative i) hG)
    (by simpa only [hcd G hG] using
      integrable_kconv_mul hκm hκ1 hF (hG.coordinateDerivative i))
    (integrable_kconv_mul hκm hκ1 hF hG)
    (fun x _ => differentiable_kconv hκ hF x) (fun x _ => differentiable_kconv hκ hG x)
  simpa only [hcd F hF, hcd G hG] using h

/-- **Second derivatives by the Laplacian**: `∫ (∂ᵢ∂ⱼ U)² = ∫ ∂ᵢ∂ᵢ U ∂ⱼ∂ⱼ U` for `U = κ * ψ`. -/
theorem integral_kconv_mixed_sq {ψ : Vec d → ℝ} (hψ : IsSmoothCompact ψ) (i j : Fin d) :
    ∫ x, kconv κ (EinsteinRelation.coordinateDerivative i
        (EinsteinRelation.coordinateDerivative j ψ)) x ^ 2 =
      ∫ x, kconv κ (EinsteinRelation.coordinateDerivative i
          (EinsteinRelation.coordinateDerivative i ψ)) x *
        kconv κ (EinsteinRelation.coordinateDerivative j
          (EinsteinRelation.coordinateDerivative j ψ)) x := by
  set A := EinsteinRelation.coordinateDerivative j ψ with hA
  have hAs : IsSmoothCompact A := hψ.coordinateDerivative j
  have hiA := hAs.coordinateDerivative i
  set B := EinsteinRelation.coordinateDerivative i (EinsteinRelation.coordinateDerivative i ψ)
    with hB
  have hBs : IsSmoothCompact B := (hψ.coordinateDerivative i).coordinateDerivative i
  have h1 := integral_kconv_mul_kconv_coordinateDerivative hκm hκ1 hiA hAs i
  have hcomm : EinsteinRelation.coordinateDerivative i
      (EinsteinRelation.coordinateDerivative i A) =
        EinsteinRelation.coordinateDerivative j B := by
    rw [hA, hB, coordinateDerivative_comm hψ.1 i j,
      coordinateDerivative_comm (hψ.coordinateDerivative i).1 i j]
  rw [hcomm] at h1
  have h2 := integral_kconv_mul_kconv_coordinateDerivative hκm hκ1 hBs hAs j
  simp_rw [sq]
  rw [h1, h2]

/-- **`L²` second derivatives by the Laplacian**: `∑ᵢⱼ ‖∂ᵢ∂ⱼ U‖₂² = ‖ΔU‖₂²` for `U = κ * ψ`. -/
theorem sum_integral_kconv_sq {ψ : Vec d → ℝ} (hψ : IsSmoothCompact ψ) :
    ∑ i, ∑ j, ∫ x, kconv κ (EinsteinRelation.coordinateDerivative i
        (EinsteinRelation.coordinateDerivative j ψ)) x ^ 2 =
      ∫ x, (∑ i, kconv κ (EinsteinRelation.coordinateDerivative i
        (EinsteinRelation.coordinateDerivative i ψ)) x) ^ 2 := by
  have hD : ∀ i, IsSmoothCompact (EinsteinRelation.coordinateDerivative i
      (EinsteinRelation.coordinateDerivative i ψ)) := fun i =>
    (hψ.coordinateDerivative i).coordinateDerivative i
  simp_rw [integral_kconv_mixed_sq hκm hκ1 hψ, sq, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_kconv_mul hκm hκ1 (hD i) (hD j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_kconv_mul hκm hκ1 (hD i) (hD j)]

end IntegrationByParts

end EinsteinFull.Homogenization
