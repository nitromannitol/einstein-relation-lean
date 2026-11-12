import EinsteinRelation.Correctors.AKMParabolicIntegrability

/-! # Fubini for the actual finite-time coefficient flux

Source: `paper/main.tex:808-816`. The actual gradient energy makes every
coordinate time integral and every compactly tested flux integrable.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual spatial flux pairing commutes with finite-time integration.
Source: `paper/main.tex:808-816`. -/
theorem parabolicSolution_time_integral_flux_pairing {d : ℕ} {K a b : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    (∫ x in U, dot ((A x).mulVec (fun j => ∫ t in Set.Ioo a b, G (t,x) j))
      (gradient ψ x)) =
      ∫ t in Set.Ioo a b, ∫ x in U, dot ((A x).mulVec (G (t,x)))
        (gradient ψ x) := by
  let ν : Measure (ℝ × Vec d) := volume.restrict (Set.Ioo a b ×ˢ U)
  have hν : ν = (volume.restrict (Set.Ioo a b)).prod (volume.restrict U) := by
    dsimp [ν]
    rw [Measure.volume_eq_prod ℝ (Vec d), Measure.prod_restrict]
  haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hG (j : Fin d) : Integrable (fun z => G z j) ν := by
    have hm : MemLp (fun z => G z j) 2 ν := by
      apply hsol.2.2.1.of_le
        ((continuous_apply j).comp_aestronglyMeasurable hsol.2.1)
      exact Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ euclideanNorm (G z) from Real.sqrt_nonneg _)]
        apply Real.abs_le_sqrt
        change G z j ^ 2 ≤ ∑ k : Fin d, G z k * G z k
        rw [sq]
        exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
    exact hm.integrable one_le_two
  have hf : Integrable (fun z : ℝ × Vec d =>
      dot ((A z.2).mulVec (G z)) (gradient ψ z.2)) ν := by
    apply integrable_finset_sum Finset.univ
    intro j _
    have hc : Continuous (fun x => coordinateDerivative j ψ x) :=
      ((contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const).continuous
    obtain ⟨C, hC⟩ := (hψ.2.1.fderiv_apply ℝ (unitVector j)).exists_bound_of_continuous hc
    exact ((parabolicSolution_flux_coordinate_memLp hK A hsol j).integrable one_le_two).mul_bdd
      (hc.comp continuous_snd).measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z.2)
  have hGi : ∀ᵐ x ∂volume.restrict U, ∀ j : Fin d,
      Integrable (fun t => G (t,x) j) (volume.restrict (Set.Ioo a b)) := by
    apply ae_all_iff.mpr
    intro j
    have hg := hG j
    rw [hν] at hg
    exact hg.prod_left_ae
  have he : (∫ x in U, dot ((A x).mulVec (fun j => ∫ t in Set.Ioo a b, G (t,x) j))
      (gradient ψ x)) =
      ∫ x in U, ∫ t in Set.Ioo a b, dot ((A x).mulVec (G (t,x))) (gradient ψ x) := by
    apply integral_congr_ae
    filter_upwards [hGi] with x hx
    simp only [dot, Matrix.mulVec, dotProduct, Finset.sum_mul]
    symm
    rw [integral_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ (fun j _ =>
        ((hx j).const_mul (A x i j)).mul_const (gradient ψ x i)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum Finset.univ (fun j _ =>
      ((hx j).const_mul (A x i j)).mul_const (gradient ψ x i))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const, integral_const_mul]
  rw [he]
  rw [hν] at hf
  exact (integral_integral_swap hf).symm

end EinsteinRelation.Correctors
