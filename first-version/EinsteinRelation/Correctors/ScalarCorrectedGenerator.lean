import EinsteinRelation.Correctors.ScalarCorrectedWeakIdentities

/-! # The generator identity of one corrected scalar band

Source: `paper/main.tex:1044–1059`, Step 3 of Proposition 6.1.
Starting from the homogenized Poisson equation of a scalar band, the local
corrector flux equations and skew cancellation give the reduced generator
equation with the explicit flux error. The band Poisson equation and moment
estimates still have to be supplied by the kernel construction.
-/

open MeasureTheory
open scoped Matrix

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- The explicit error flux is integrable from second moments of its factors
and an essential bound on the coefficient (`paper/main.tex:1056–1059`). -/
theorem integrable_scalarCorrectedFluxError {Q : Measure (FieldPair d)}
    {phi : Fin d → FieldPair d → ℝ} {Du : FieldPair d → Vec d}
    {DDu F : Fin d → FieldPair d → Vec d} {Sig : Fin d → FieldPair d → Mat d}
    (hphi2 : ∀ j, MemLp (phi j) 2 Q)
    (hSig2 : ∀ j i k, MemLp (fun ω => Sig j ω i k) 2 Q)
    (hDu2 : ∀ j, MemLp (fun ω => Du ω j) 2 Q)
    (hDDu2 : ∀ j i, MemLp (fun ω => DDu j ω i) 2 Q)
    (hF2 : ∀ j i, MemLp (fun ω => F j ω i) 2 Q)
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C) (i : Fin d) :
    Integrable (fun ω =>
      (∑ j, (phi j ω • ((ω.1 0) *ᵥ DDu j ω) - Sig j ω *ᵥ DDu j ω + Du ω j • F j ω)) i) Q := by
  obtain ⟨C, hC⟩ := hA
  have haDDu : ∀ j, MemLp (fun ω => ((ω.1 0) *ᵥ DDu j ω) i) 2 Q := by
    intro j
    change MemLp (fun ω => ∑ k, ω.1 0 i k * DDu j ω k) 2 Q
    apply memLp_finset_sum Finset.univ
    intro k _
    have hb : ∀ᵐ ω ∂Q, |ω.1 0 i k| ≤ C := hC.mono fun ω hω => hω i k
    simpa only [mul_comm] using memLp_mul_of_ae_bound (hDDu2 j k)
      (measurable_coeff_entry i k).aestronglyMeasurable hb
  have hsDDu : ∀ j, Integrable (fun ω => (Sig j ω *ᵥ DDu j ω) i) Q := by
    intro j
    change Integrable (fun ω => ∑ k, Sig j ω i k * DDu j ω k) Q
    exact integrable_finset_sum _ fun k _ => (hSig2 j i k).integrable_mul (hDDu2 j k)
  simp only [Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact integrable_finset_sum _ fun j _ =>
    (((hphi2 j).integrable_mul (haDDu j)).sub (hsDDu j)).add ((hDu2 j).integrable_mul (hF2 j i))

/-- The corrected scalar band satisfies its reduced generator equation with
the explicit flux error (`paper/main.tex:1053–1059`). -/
theorem satisfiesReducedGeneratorEquation_scalarCorrected {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {u f : FieldPair d → ℝ} {Du : FieldPair d → Vec d} (abar : Mat d)
    {phi : Fin d → FieldPair d → ℝ} {Dphi DDu R F : Fin d → FieldPair d → Vec d}
    {Sig : Fin d → FieldPair d → Mat d}
    (hu : HasWeakHorizontalGradient Q hQ u Du)
    (hphi : ∀ j, HasWeakHorizontalGradient Q hQ (phi j) (Dphi j))
    (hphim : ∀ j, Measurable (phi j)) (hDphim : ∀ j, Measurable (Dphi j))
    (hPoisson : HasWeakHorizontalDivergence Q hQ (fun ω => abar *ᵥ Du ω) (fun ω => 2 * f ω))
    (hDu : ∀ j, HasWeakHorizontalGradient Q hQ (fun ω => Du ω j) (DDu j))
    (hskew : ∀ j, ∀ᵐ ω ∂Q, (Sig j ω).transpose = -(Sig j ω))
    (hrows : ∀ j i, HasWeakHorizontalDivergence Q hQ (fun ω k => Sig j ω i k) (fun ω => R j ω i))
    (hDum : Measurable Du) (hDDum : ∀ j, Measurable (DDu j))
    (hSig2 : ∀ j i k, MemLp (fun ω => Sig j ω i k) 2 Q)
    (hR2 : ∀ j i, MemLp (fun ω => R j ω i) 2 Q)
    (hDu2 : ∀ j, MemLp (fun ω => Du ω j) 2 Q)
    (hDDu2 : ∀ j i, MemLp (fun ω => DDu j ω i) 2 Q)
    (hphi2 : ∀ j, MemLp (phi j) 2 Q)
    (hDphi2 : ∀ j i, MemLp (fun ω => Dphi j ω i) 2 Q)
    (hF2 : ∀ j i, MemLp (fun ω => F j ω i) 2 Q)
    (hflux : ∀ᵐ ω ∂Q, ∀ j, (ω.1 0) *ᵥ (unitVector j + Dphi j ω) =
      abar *ᵥ unitVector j + (R j ω + F j ω))
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C)
    (i₁ : Fin d) :
    SatisfiesReducedGeneratorEquation Q hQ 0
      (fun ω => u ω + ∑ j, phi j ω * Du ω j)
      (fun ω => Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • DDu j ω)) f
      (fun ω => (1 / 2 : ℝ) • ∑ j,
        (phi j ω • ((ω.1 0) *ᵥ DDu j ω) - Sig j ω *ᵥ DDu j ω + Du ω j • F j ω)) i₁ := by
  have hgrad := hasWeakHorizontalGradient_scalarCorrected hu hphi hDu hphim hDphim hDum
    hDDum hphi2 hDphi2 hDu2 hDDu2
  let v : FieldPair d → ℝ := fun ω => u ω + ∑ j, phi j ω * Du ω j
  let Dv : FieldPair d → Vec d := fun ω => Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • DDu j ω)
  let B : FieldPair d → Vec d := fun ω => ∑ j,
    (phi j ω • ((ω.1 0) *ᵥ DDu j ω) - Sig j ω *ᵥ DDu j ω + Du ω j • F j ω)
  change SatisfiesReducedGeneratorEquation Q hQ 0 v Dv f (fun ω => (1 / 2 : ℝ) • B ω) i₁
  have hB : ∀ i, Integrable (fun ω => B ω i) Q :=
    integrable_scalarCorrectedFluxError hphi2 hSig2 hDu2 hDDu2 hF2 hA
  have hcancel := hasWeakHorizontalDivergence_scalarCorrectedFluxDifference (phi := phi) abar hDu hskew
    hrows hDum hDDum hSig2 hR2 hDu2 hDDu2 hflux
  have hdiv : HasWeakHorizontalDivergence Q hQ
      (fun ω => (ω.1 0) *ᵥ Dv ω - B ω) (fun ω => 2 * f ω) := by
    have htotal := hPoisson.add hcancel
    simp only [add_zero] at htotal
    apply htotal.congr_field
    exact ae_of_all _ fun ω => by change abar *ᵥ Du ω +
      ((ω.1 0) *ᵥ Dv ω - (abar *ᵥ Du ω + B ω)) = (ω.1 0) *ᵥ Dv ω - B ω; abel
  have hfi : Integrable f Q := by
    simpa only [← mul_assoc, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_mul]
      using hPoisson.2.1.const_mul (1 / 2 : ℝ)
  refine ⟨hgrad, hfi, fun i => (hB i).const_mul (1 / 2 : ℝ), fun K hK DK hDK => ?_⟩
  obtain ⟨C, hC⟩ := hA
  have hN : ∀ i, ∃ N : ℝ, ∀ᵐ ω ∂Q, |DK i ω| ≤ N := fun i =>
    ae_bound_of_hasHorizontalLpDerivative hK (hDK i)
  have hleft := integrable_double_sum_flux hC hN hgrad.2.1
  have hright := integrable_sum_mul_derivative hB hK hDK
  have heq : (∫ ω, ∑ i, ((ω.1 0) *ᵥ Dv ω - B ω) i * DK i ω ∂Q) =
      (∫ ω, ∑ i, ∑ j, DK i ω * ω.1 0 i j * Dv ω j ∂Q) -
        ∫ ω, ∑ i, B ω i * DK i ω ∂Q := by
    calc
      _ = ∫ ω, ((∑ i, ∑ j, DK i ω * ω.1 0 i j * Dv ω j) - ∑ i, B ω i * DK i ω) ∂Q := by
        congr 1
        funext ω
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.mulVec, dotProduct]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := integral_sub hleft hright
  have hsource : (∫ ω, (2 * f ω) * K ω ∂Q) = 2 * ∫ ω, f ω * K ω ∂Q := by
    simpa only [mul_assoc] using integral_const_mul (2 : ℝ) (fun ω => f ω * K ω)
  have herr : (∫ ω, ∑ i, ((1 / 2 : ℝ) • B ω) i * DK i ω ∂Q) =
      (1 / 2 : ℝ) * ∫ ω, ∑ i, B ω i * DK i ω ∂Q := by
    calc
      _ = ∫ ω, (1 / 2 : ℝ) * (∑ i, B ω i * DK i ω) ∂Q := by
        congr 1
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      _ = _ := integral_const_mul _ _
  have hid := hdiv.2.2 K hK DK hDK
  rw [heq, hsource] at hid
  simp only [zero_mul, add_zero, herr]
  linarith only [hid]

end EinsteinRelation.Correctors
