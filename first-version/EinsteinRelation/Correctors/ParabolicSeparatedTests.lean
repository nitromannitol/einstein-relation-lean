import EinsteinRelation.Correctors.AKMParabolicIntegrability

/-! # Separated tests in the genuine parabolic weak equation

Source: `paper/main.tex:808-816`. Tensor tests give the actual weak time
identity of each spatial pairing, with all Fubini integrability justified
by the energy class. No differentiability of the flow in time is assumed.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Tensor tests recover the scalar weak time equation from the full
space-time equation. Source: `paper/main.tex:808-816`. -/
theorem parabolicSolution_separated_time_test {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηI : tsupport η ⊆ interior I)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    (∫ t in I, (∫ x in U, u (t,x) * ψ x) * deriv η t) =
      ∫ t in I, η t * ∫ x in U, dot ((A x).mulVec (G (t,x))) (gradient ψ x) := by
  let Φ : ℝ × Vec d → ℝ := fun z => η z.1 * ψ z.2
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ :=
    (hη.comp contDiff_fst).mul (hψ.1.comp contDiff_snd)
  have hs : tsupport Φ ⊆ tsupport η ×ˢ tsupport ψ := by
    apply closure_minimal ?_ ((isClosed_tsupport η).prod (isClosed_tsupport ψ))
    intro z hz
    exact ⟨subset_tsupport η (fun h => hz (by simp only [Φ, h, zero_mul])),
      subset_tsupport ψ (fun h => hz (by simp only [Φ, h, mul_zero]))⟩
  have hΦc : HasCompactSupport Φ :=
    (hηc.isCompact.prod hψ.2.1.isCompact).of_isClosed_subset (isClosed_tsupport Φ) hs
  have hΦU : tsupport Φ ⊆ interior I ×ˢ U :=
    fun z hz => ⟨hηI (hs hz).1, hψ.2.2 (hs hz).2⟩
  have hd (z : ℝ × Vec d) (v : ℝ × Vec d) :
      fderiv ℝ Φ z v = deriv η z.1 * v.1 * ψ z.2 +
        η z.1 * fderiv ℝ ψ z.2 v.2 := by
    have hηd := (hη.differentiable (by norm_num)).differentiableAt (x := z.1)
    have hψd := (hψ.1.differentiable (by norm_num)).differentiableAt (x := z.2)
    have hf : DifferentiableAt ℝ (fun w : ℝ × Vec d => η w.1) z :=
      hηd.comp z differentiableAt_fst
    have hg : DifferentiableAt ℝ (fun w : ℝ × Vec d => ψ w.2) z :=
      hψd.comp z differentiableAt_snd
    change fderiv ℝ ((fun w : ℝ × Vec d => η w.1) * (fun w => ψ w.2)) z v = _
    have he : fderiv ℝ (fun w : ℝ × Vec d => η w.1) z =
        (fderiv ℝ η z.1).comp (fderiv ℝ Prod.fst z) :=
      fderiv_comp z hηd differentiableAt_fst
    have hp : fderiv ℝ (fun w : ℝ × Vec d => ψ w.2) z =
        (fderiv ℝ ψ z.2).comp (fderiv ℝ Prod.snd z) :=
      fderiv_comp z hψd differentiableAt_snd
    rw [fderiv_mul hf hg, he, hp]
    simp [fderiv_fst, fderiv_snd]
    ring
  have ht (z : ℝ × Vec d) : fderiv ℝ Φ z (1,0) = deriv η z.1 * ψ z.2 := by
    rw [hd]
    simp only [mul_one, map_zero, mul_zero, add_zero]
  have hx (z : ℝ × Vec d) (j : Fin d) :
      fderiv ℝ Φ z (0, unitVector j) = η z.1 * coordinateDerivative j ψ z.2 := by
    rw [hd]
    simp only [mul_zero, zero_mul, zero_add, coordinateDerivative]
  let ν : Measure (ℝ × Vec d) := volume.restrict (I ×ˢ U)
  have hD (v : ℝ × Vec d) : MemLp (fun z => fderiv ℝ Φ z v) 2 ν :=
    (((contDiff_infty_iff_fderiv.mp hΦ).2.clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
      (hΦc.fderiv_apply ℝ v)).mono_measure Measure.restrict_le_self
  have htime : Integrable (fun z => u z * fderiv ℝ Φ z (1,0)) ν :=
    hsol.1.integrable_mul (hD (1,0))
  have hflux : Integrable (fun z => dot ((A z.2).mulVec (G z))
      (fun j => fderiv ℝ Φ z (0,unitVector j))) ν :=
    integrable_finset_sum Finset.univ fun j _ =>
      (parabolicSolution_flux_coordinate_memLp hK A hsol j).integrable_mul (hD (0,unitVector j))
  have heq := hsol.2.2.2.2 Φ hΦ hΦc hΦU
  change (∫ z, -(u z) * fderiv ℝ Φ z (1,0) +
    dot ((A z.2).mulVec (G z)) (fun j => fderiv ℝ Φ z (0,unitVector j)) ∂ν) = 0 at heq
  simp only [neg_mul] at heq
  have hi := integral_add htime.neg hflux
  simp only [Pi.neg_apply] at hi
  rw [hi, integral_neg] at heq
  have he : (∫ z, u z * fderiv ℝ Φ z (1,0) ∂ν) =
      ∫ z, dot ((A z.2).mulVec (G z)) (fun j => fderiv ℝ Φ z (0,unitVector j)) ∂ν := by
    linarith only [heq]
  have hν : ν = (volume.restrict I).prod (volume.restrict U) := by
    dsimp only [ν]
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hν] at htime hflux he
  rw [integral_prod _ htime, integral_prod _ hflux] at he
  convert he using 1
  · congr 1
    funext t
    simp_rw [ht]
    rw [← integral_mul_const]
    congr 1
    funext x
    ring
  · congr 1
    funext t
    simp_rw [hx]
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [dot, gradient, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

end EinsteinRelation.Correctors
