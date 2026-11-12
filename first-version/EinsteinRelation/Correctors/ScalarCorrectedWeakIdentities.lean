import EinsteinRelation.Correctors.SkewDivergenceProduct
import EinsteinRelation.Calculus.WeakHorizontalFiniteSums

/-! # Weak identities of the scalar two-scale expansion

Source: `paper/main.tex:1044–1069`, Steps 3 and 4 of Proposition 6.1.
These identities use the weak gradients and row divergences of the local
correctors. The square-integrable moment assumptions ensure that every product
is integrable; no differentiability of a local corrector is assumed.
-/

open MeasureTheory
open scoped Matrix

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] {hQ : IsStationary Q}

/-- Weak gradient of the corrected scalar field on one scale
(`paper/main.tex:1048–1054`). -/
theorem hasWeakHorizontalGradient_scalarCorrected
    {u : FieldPair d → ℝ} {Du : FieldPair d → Vec d}
    {phi : Fin d → FieldPair d → ℝ} {Dphi DDu : Fin d → FieldPair d → Vec d}
    (hu : HasWeakHorizontalGradient Q hQ u Du)
    (hphi : ∀ j, HasWeakHorizontalGradient Q hQ (phi j) (Dphi j))
    (hDu : ∀ j, HasWeakHorizontalGradient Q hQ (fun ω => Du ω j) (DDu j))
    (hphim : ∀ j, Measurable (phi j)) (hDphim : ∀ j, Measurable (Dphi j))
    (hDum : Measurable Du) (hDDum : ∀ j, Measurable (DDu j))
    (hphi2 : ∀ j, MemLp (phi j) 2 Q)
    (hDphi2 : ∀ j i, MemLp (fun ω => Dphi j ω i) 2 Q)
    (hDu2 : ∀ j, MemLp (fun ω => Du ω j) 2 Q)
    (hDDu2 : ∀ j i, MemLp (fun ω => DDu j ω i) 2 Q) :
    HasWeakHorizontalGradient Q hQ
      (fun ω => u ω + ∑ j, phi j ω * Du ω j)
      (fun ω => Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • DDu j ω)) := by
  have hp : ∀ j, HasWeakHorizontalGradient Q hQ (fun ω => phi j ω * Du ω j)
      (fun ω i => Du ω j * Dphi j ω i + phi j ω * DDu j ω i) := fun j =>
    (hphi j).mul_of_memLp_two (hDu j) (hphim j) ((measurable_pi_apply j).comp hDum)
      (hDphim j) (hDDum j) (hphi2 j) (hDu2 j) (hDphi2 j) (hDDu2 j)
  have hs := HasWeakHorizontalGradient.finset_sum Finset.univ (fun j _ => hp j)
  simpa only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hu.add hs

/-- The corrected flux differs from its homogenized flux and its explicit error
by a divergence-free field (`paper/main.tex:1050–1054`). -/
theorem hasWeakHorizontalDivergence_scalarCorrectedFluxDifference
    (abar : Mat d) {Du : FieldPair d → Vec d}
    {phi : Fin d → FieldPair d → ℝ} {Dphi DDu R F : Fin d → FieldPair d → Vec d}
    {Sig : Fin d → FieldPair d → Mat d}
    (hDu : ∀ j, HasWeakHorizontalGradient Q hQ (fun ω => Du ω j) (DDu j))
    (hskew : ∀ j, ∀ᵐ ω ∂Q, (Sig j ω).transpose = -(Sig j ω))
    (hrows : ∀ j i, HasWeakHorizontalDivergence Q hQ (fun ω k => Sig j ω i k) (fun ω => R j ω i))
    (hDum : Measurable Du) (hDDum : ∀ j, Measurable (DDu j))
    (hSig2 : ∀ j i k, MemLp (fun ω => Sig j ω i k) 2 Q)
    (hR2 : ∀ j i, MemLp (fun ω => R j ω i) 2 Q)
    (hDu2 : ∀ j, MemLp (fun ω => Du ω j) 2 Q)
    (hDDu2 : ∀ j i, MemLp (fun ω => DDu j ω i) 2 Q)
    (hflux : ∀ᵐ ω ∂Q, ∀ j, (ω.1 0) *ᵥ (unitVector j + Dphi j ω) =
      abar *ᵥ unitVector j + (R j ω + F j ω)) :
    HasWeakHorizontalDivergence Q hQ
      (fun ω => (ω.1 0) *ᵥ (Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • DDu j ω)) -
        (abar *ᵥ Du ω + ∑ j, (phi j ω • ((ω.1 0) *ᵥ DDu j ω) -
          Sig j ω *ᵥ DDu j ω + Du ω j • F j ω))) (fun _ => 0) := by
  have hp : ∀ j, HasWeakHorizontalDivergence Q hQ
      (fun ω i => Du ω j * R j ω i + ∑ k, Sig j ω i k * DDu j ω k) (fun _ => 0) := fun j =>
    hasWeakHorizontalDivergence_skewProduct (hskew j) (hrows j) (hDu j)
      ((measurable_pi_apply j).comp hDum) (hDDum j) (hSig2 j) (hR2 j) (hDu2 j) (hDDu2 j)
  have hs := HasWeakHorizontalDivergence.finset_sum Finset.univ (fun j _ => hp j)
  simp only [Finset.sum_const_zero] at hs
  apply hs.congr_field
  filter_upwards [hflux] with ω hω
  change (∑ j, (Du ω j • R j ω + Sig j ω *ᵥ DDu j ω)) = _
  rw [scalarCorrected_mulVec_gradient (ω.1 0) abar (Du ω) (fun j => phi j ω)
    (fun j => Dphi j ω) (fun j => DDu j ω) (fun j => R j ω) (fun j => F j ω) hω]
  simp only [smul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

/-- The first-row corrected flux is a weak divergence plus the explicit scalar
remainder of Step 4 (`paper/main.tex:1060–1069`). -/
theorem hasWeakHorizontalDivergence_scalarCorrectedDrift
    {u : FieldPair d → ℝ} {Du : FieldPair d → Vec d} (abar : Mat d)
    {phi : Fin d → FieldPair d → ℝ} {Dphi DDu R F : Fin d → FieldPair d → Vec d}
    {Sig : Fin d → FieldPair d → Mat d}
    (hu : HasWeakHorizontalGradient Q hQ u Du)
    (hDu : ∀ j, HasWeakHorizontalGradient Q hQ (fun ω => Du ω j) (DDu j))
    (hrows : ∀ j i, HasWeakHorizontalDivergence Q hQ (fun ω k => Sig j ω i k) (fun ω => R j ω i))
    (hDum : Measurable Du) (hDDum : ∀ j, Measurable (DDu j))
    (hSig2 : ∀ j i k, MemLp (fun ω => Sig j ω i k) 2 Q)
    (hR2 : ∀ j i, MemLp (fun ω => R j ω i) 2 Q)
    (hDu2 : ∀ j, MemLp (fun ω => Du ω j) 2 Q)
    (hDDu2 : ∀ j i, MemLp (fun ω => DDu j ω i) 2 Q)
    (ha : ∀ᵐ ω ∂Q, (ω.1 0).transpose = ω.1 0) (habar : abar.transpose = abar)
    (hflux : ∀ᵐ ω ∂Q, ∀ j, (ω.1 0) *ᵥ (unitVector j + Dphi j ω) =
      abar *ᵥ unitVector j + (R j ω + F j ω)) (i : Fin d) :
    HasWeakHorizontalDivergence Q hQ
      (fun ω => u ω • (abar *ᵥ unitVector i) + ∑ j, Du ω j • (fun k => Sig j ω i k))
      (fun ω =>
        dot ((ω.1 0) *ᵥ unitVector i)
          (Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • DDu j ω)) -
        ∑ j, (phi j ω * dot ((ω.1 0) *ᵥ unitVector i) (DDu j ω) -
          (Sig j ω *ᵥ DDu j ω) i + Du ω j * F j ω i)) := by
  have hp : ∀ j, HasWeakHorizontalDivergence Q hQ
      (fun ω k => Du ω j * Sig j ω i k)
      (fun ω => Du ω j * R j ω i + ∑ k, Sig j ω i k * DDu j ω k) := fun j =>
    (hrows j i).mul_of_memLp_two (hDu j) ((measurable_pi_apply j).comp hDum)
      (hDDum j) (hSig2 j i) (hR2 j i) (hDu2 j) (hDDu2 j)
  have hs := HasWeakHorizontalDivergence.finset_sum Finset.univ (fun j _ => hp j)
  have hbase := hu.divergence_const_mul (abar *ᵥ unitVector i)
  have htotal := hbase.add hs
  apply Entropy.HasWeakHorizontalDivergence.congr_div htotal
  filter_upwards [ha, hflux] with ω hω hω'
  exact (scalarCorrected_dot_first_row (ω.1 0) abar hω habar (Du ω) (fun j => phi j ω)
    (fun j => Dphi j ω) (fun j => DDu j ω) (fun j => R j ω) (fun j => F j ω)
    (fun j => Sig j ω) hω' i).symm

end EinsteinRelation.Correctors
