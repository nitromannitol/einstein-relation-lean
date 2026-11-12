import EinsteinRelation.Correctors.PairedPDEWeakEnergyIdentity

/-! # Polarization of the weak energy identity

Source: `paper/main.tex:832–840`. Two independent compact cutoffs give the
bilinear testing identity needed for temporal weights that are not squares.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Polarized energy testing for the actual weak solution. Both cutoffs
are smooth; the solution is only in the parabolic energy class.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_polarized_cutoff_energy_identity {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ θ : ℝ × Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hζc : HasCompactSupport ζ) (hθc : HasCompactSupport θ)
    (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    (hθsupp : tsupport θ ⊆ interior I ×ˢ U) :
    let P := fun z => dot ((A z.2).mulVec (G z)) (fun j =>
      ζ z * θ z * G z j + u z * (ζ z * fderiv ℝ θ z (0, unitVector j) +
        θ z * fderiv ℝ ζ z (0, unitVector j)))
    Integrable P (volume.restrict (I ×ˢ U)) ∧
      2 * (∫ z in I ×ˢ U, P z) =
        ∫ z in I ×ˢ U,
          (ζ z * fderiv ℝ θ z (1, 0) + θ z * fderiv ℝ ζ z (1, 0)) * (u z)^2 := by
  let μ := volume.restrict (I ×ˢ U)
  let F := fun (β : ℝ × Vec d → ℝ) z => dot ((A z.2).mulVec (G z))
    (fun j => β z ^ 2 * G z j + 2 * β z * u z * fderiv ℝ β z (0, unitVector j))
  let T := fun (β : ℝ × Vec d → ℝ) z => β z * fderiv ℝ β z (1, 0) * (u z)^2
  let P := fun z => dot ((A z.2).mulVec (G z)) (fun j =>
    ζ z * θ z * G z j + u z * (ζ z * fderiv ℝ θ z (0, unitVector j) +
      θ z * fderiv ℝ ζ z (0, unitVector j)))
  let Q := fun z => (ζ z * fderiv ℝ θ z (1, 0) +
    θ z * fderiv ℝ ζ z (1, 0)) * (u z)^2
  have hx := parabolicSolution_cutoff_energy_identity hK hI hU hsol hζ hζc hζsupp
  have hy := parabolicSolution_cutoff_energy_identity hK hI hU hsol hθ hθc hθsupp
  have hs := parabolicSolution_cutoff_energy_identity hK hI hU hsol (hζ.add hθ)
    (hζc.add hθc) ((tsupport_add ζ θ).trans (Set.union_subset hζsupp hθsupp))
  change Integrable (F ζ) μ ∧ (∫ z, F ζ z ∂μ) = ∫ z, T ζ z ∂μ at hx
  change Integrable (F θ) μ ∧ (∫ z, F θ z ∂μ) = ∫ z, T θ z ∂μ at hy
  change Integrable (F (ζ + θ)) μ ∧
    (∫ z, F (ζ + θ) z ∂μ) = ∫ z, T (ζ + θ) z ∂μ at hs
  have hd (z v : ℝ × Vec d) :
      fderiv ℝ (ζ + θ) z v = fderiv ℝ ζ z v + fderiv ℝ θ z v := by
    rw [fderiv_add (hζ.differentiable (by norm_cast) z)
      (hθ.differentiable (by norm_cast) z), ContinuousLinearMap.add_apply]
  have hP (z : ℝ × Vec d) : F (ζ + θ) z - F ζ z - F θ z = 2 * P z := by
    simp only [F, P, dot, Pi.add_apply, hd, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hQ (z : ℝ × Vec d) : T (ζ + θ) z - T ζ z - T θ z = Q z := by
    dsimp only [T, Q]
    rw [hd]
    simp only [Pi.add_apply]
    ring
  have hT (β : ℝ × Vec d → ℝ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
      (hβc : HasCompactSupport β) : Integrable (T β) μ := by
    have hβm : MemLp β ∞ μ := hβ.continuous.memLp_top_of_hasCompactSupport hβc _
    have hdm : MemLp (fun z => fderiv ℝ β z (1, 0)) ∞ μ :=
      ((contDiff_infty_iff_fderiv.mp hβ).2.clm_apply contDiff_const).continuous
        |>.memLp_top_of_hasCompactSupport (hβc.fderiv_apply ℝ (1, 0)) _
    have hleft : MemLp (fun z => β z * u z) 2 μ := hsol.1.mul' hβm
    have hright : MemLp (fun z => fderiv ℝ β z (1, 0) * u z) 2 μ := hsol.1.mul' hdm
    convert hleft.integrable_mul hright using 1
    funext z
    simp only [T, Pi.mul_apply]
    ring
  have hiP : Integrable P μ := by
    have hi : Integrable (fun z => (F (ζ + θ) z - F ζ z - F θ z) / 2) μ :=
      ((hs.1.sub hx.1).sub hy.1).div_const 2
    exact hi.congr (Filter.Eventually.of_forall fun z => by
      change (F (ζ + θ) z - F ζ z - F θ z) / 2 = P z
      rw [hP]; ring)
  refine ⟨hiP, ?_⟩
  change 2 * (∫ z, P z ∂μ) = ∫ z, Q z ∂μ
  calc
    _ = ∫ z, F (ζ + θ) z - F ζ z - F θ z ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hP z).symm)
    _ = (∫ z, F (ζ + θ) z ∂μ) - (∫ z, F ζ z ∂μ) - ∫ z, F θ z ∂μ := by
      rw [integral_sub (f := fun z => F (ζ + θ) z - F ζ z) (g := F θ)
        (hs.1.sub hx.1) hy.1, integral_sub (f := F (ζ + θ)) (g := F ζ) hs.1 hx.1]
    _ = (∫ z, T (ζ + θ) z ∂μ) - (∫ z, T ζ z ∂μ) - ∫ z, T θ z ∂μ := by
      rw [hs.2, hx.2, hy.2]
    _ = ∫ z, T (ζ + θ) z - T ζ z - T θ z ∂μ := by
      rw [integral_sub (f := fun z => T (ζ + θ) z - T ζ z) (g := T θ)
        ((hT _ (hζ.add hθ) (hζc.add hθc)).sub (hT _ hζ hζc))
        (hT _ hθ hθc), integral_sub (f := T (ζ + θ)) (g := T ζ)
        (hT _ (hζ.add hθ) (hζc.add hθc)) (hT _ hζ hζc)]
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hQ)

end EinsteinRelation.Correctors
