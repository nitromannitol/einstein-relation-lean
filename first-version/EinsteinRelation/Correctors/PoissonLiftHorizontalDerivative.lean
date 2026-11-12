import EinsteinRelation.Correctors.PoissonLiftLocalIntegrability

/-! Source: `paper/main.tex:735-739`. A divergence-free spatial flux
remains divergence-free in its original components after adjoining an
independent height coordinate. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Every fixed-height slice of a compact smooth lifted test is a compact
smooth test in the original space. -/
theorem isSpatialTest_poissonLiftSlice {d : ℕ}
    {ψ : Vec (d + 1) → ℝ} (hψ : IsSpatialTest Set.univ ψ) (t : ℝ) :
    IsSpatialTest Set.univ (fun y : Vec d => ψ (Fin.cons t y)) := by
  refine ⟨hψ.1.comp ?_, ?_, Set.subset_univ _⟩
  · apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact contDiff_const
    · exact contDiff_apply ℝ ℝ j
  · have hc : Continuous (poissonLiftBase : Vec (d + 1) → Vec d) :=
      continuous_pi (fun i => continuous_apply i.succ)
    apply HasCompactSupport.intro (hψ.2.1.image hc)
    intro y hy
    by_contra hn
    apply hy
    exact ⟨Fin.cons t y, subset_tsupport _ hn, by ext i; simp [poissonLiftBase]⟩

/-- Horizontal coordinate derivatives commute with fixed-height slicing. -/
theorem coordinateDerivative_poissonLiftSlice {d : ℕ}
    {ψ : Vec (d + 1) → ℝ} (hψ : Differentiable ℝ ψ)
    (i : Fin d) (t : ℝ) (y : Vec d) :
    coordinateDerivative i (fun z : Vec d => ψ (Fin.cons t z)) y =
      coordinateDerivative i.succ ψ (Fin.cons t y) := by
  let L : Vec d →L[ℝ] Vec (d + 1) :=
    ContinuousLinearMap.pi (Fin.cons 0 (fun j => ContinuousLinearMap.proj j))
  have hc : HasFDerivAt (fun z : Vec d => Fin.cons t z) L y := by
    apply hasFDerivAt_pi.mpr
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hasFDerivAt_const t y
    · exact (ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ).hasFDerivAt
  have hu : L (unitVector i) = unitVector i.succ := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [L, unitVector, Pi.single_apply]
  unfold coordinateDerivative
  change (fderiv ℝ (ψ ∘ (fun z : Vec d => Fin.cons t z)) y) (unitVector i) = _
  rw [((hψ (Fin.cons t y)).hasFDerivAt.comp y hc).fderiv]
  change (fderiv ℝ ψ (Fin.cons t y)) (L (unitVector i)) = _
  rw [hu]

/-- The original components of a divergence-free flux have zero pairing
against the horizontal part of every compact smooth lifted test. -/
theorem integral_horizontal_gradient_poissonLift_zero {d : ℕ}
    (F : Vec d → Vec d) (hF : HasWeakDivergence Set.univ F (fun _ => 0))
    (ψ : Vec (d + 1) → ℝ) (hψ : IsSpatialTest Set.univ ψ) :
    (∫ x : Vec (d + 1), ∑ i : Fin d,
      F (poissonLiftBase x) i * coordinateDerivative i.succ ψ x ∂volume) = 0 := by
  have hi (i : Fin d) : Integrable (fun x : Vec (d + 1) =>
      F (poissonLiftBase x) i * coordinateDerivative i.succ ψ x) volume := by
    have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i.succ ψ) :=
      ((contDiff_infty_iff_fderiv.mp hψ.1).2).clm_apply contDiff_const
    have hDc : HasCompactSupport (coordinateDerivative i.succ ψ) :=
      hψ.2.1.fderiv_apply ℝ (unitVector i.succ)
    simpa only [smul_eq_mul] using
      (locallyIntegrable_poissonLiftBase (fun x => F x i)
        (locallyIntegrableOn_univ.mp (hF.1 i))).integrable_smul_right_of_hasCompactSupport
        hD.continuous hDc
  have hisum := integrable_finset_sum Finset.univ (fun i _ => hi i)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have heinv (p : ℝ × Vec d) : e.symm p = Fin.cons p.1 p.2 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have he' := MeasurePreserving.symm e he
  have hp : Integrable (fun p : ℝ × Vec d => ∑ i : Fin d,
      F p.2 i * coordinateDerivative i.succ ψ (Fin.cons p.1 p.2)) volume := by
    simpa [Function.comp_def, heinv, poissonLiftBase] using
      he'.integrable_comp_of_integrable hisum
  have hchange : (∫ x : Vec (d + 1), ∑ i : Fin d,
      F (poissonLiftBase x) i * coordinateDerivative i.succ ψ x) =
      ∫ p : ℝ × Vec d, ∑ i : Fin d,
        F p.2 i * coordinateDerivative i.succ ψ (Fin.cons p.1 p.2) := by
    simpa [heinv, poissonLiftBase] using
      (he'.integral_comp' (fun x : Vec (d + 1) => ∑ i : Fin d,
        F (poissonLiftBase x) i * coordinateDerivative i.succ ψ x)).symm
  have hinner (t : ℝ) : (∫ y : Vec d, ∑ i : Fin d,
      F y i * coordinateDerivative i.succ ψ (Fin.cons t y)) = 0 := by
    have h := hF.2.2 (fun y : Vec d => ψ (Fin.cons t y))
      (isSpatialTest_poissonLiftSlice hψ t)
    simp only [setIntegral_univ, zero_mul, integral_zero, neg_zero] at h
    simpa only [dot, gradient, coordinateDerivative_poissonLiftSlice
      (hψ.1.differentiable (by simp))] using h
  rw [hchange, Measure.volume_eq_prod ℝ (Vec d)]
  rw [integral_prod _ (by simpa only [Measure.volume_eq_prod] using hp)]
  simp_rw [hinner, integral_zero]

end EinsteinRelation.Correctors
