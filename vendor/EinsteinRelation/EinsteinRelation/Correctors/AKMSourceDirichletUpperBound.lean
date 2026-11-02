import EinsteinRelation.Correctors.AKMSourceDirichletCompetitors

/-!
# Uniform domination of the literal Dirichlet value

Source: `paper/main.tex:693-698,727-729`; AKM (1.14), printed p. 8,
and the expectations following (1.23), printed p. 11. Integrability in the
coefficient law reduces to measurability by the affine competitor bound.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.External.AKM
open Environment.AKMTestIntegralSupport

/-- The affine competitor gives the uniform elliptic bound on every
finite-volume domain, including null domains. -/
theorem sourceDirichletEnergy_le_ellipticity {d : ℕ} {K : ℝ}
    (hK : 0 ≤ K) (a : Coefficient d K) (U : Set (Vec d))
    (hU : volume U ≠ ⊤) (e : Vec d) :
    sourceDirichletEnergy a U e ≤ (K / 2) * euclideanSq e := by
  letI : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hU.lt_top⟩
  have he : 0 ≤ euclideanSq e := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (e i)
  have hC : 0 ≤ (K / 2) * euclideanSq e := mul_nonneg (div_nonneg hK (by norm_num)) he
  apply (sourceDirichletEnergy_le_affine a U e).trans
  rw [setAverage_eq, smul_eq_mul]
  have hint : (∫ x in U, (1 / 2 : ℝ) * dot e ((a x).mulVec e) ∂volume) ≤
      volume.real U * ((K / 2) * euclideanSq e) := by
    calc
      _ ≤ ∫ _x in U, (K / 2) * euclideanSq e ∂volume := by
        exact integral_mono_of_nonneg
          (ae_of_all _ fun x => mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (he.trans (a.elliptic x e).1))
          (integrable_const ((K / 2) * euclideanSq e))
          (ae_of_all _ fun x => by linarith only [(a.elliptic x e).2])
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  by_cases hz : volume.real U = 0
  · simpa only [hz, inv_zero, zero_mul] using hC
  calc
    _ ≤ (volume.real U)⁻¹ * (volume.real U * ((K / 2) * euclideanSq e)) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr measureReal_nonneg)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]

/-- The triadic cubes have finite volume. -/
theorem sourceTriadicCube_volume_ne_top (d n : ℕ) :
    volume (sourceTriadicCube d n) ≠ ⊤ := by
  simp only [sourceTriadicCube, Real.volume_pi_Ioo]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

/-- The bound is uniform in the coefficient field and triadic scale. -/
theorem sourceDirichletEnergy_triadic_upper {d : ℕ} {K : ℝ}
    (hK : 0 ≤ K) (a : Coefficient d K) (n : ℕ) (e : Vec d) :
    sourceDirichletEnergy a (sourceTriadicCube d n) e ≤ (K / 2) * euclideanSq e :=
  sourceDirichletEnergy_le_ellipticity hK a _ (sourceTriadicCube_volume_ne_top d n) e

/-- For a finite coefficient law, measurability is the only remaining
integrability obligation for the bounded nonnegative Dirichlet value. -/
theorem integrable_sourceDirichletEnergy_of_aestronglyMeasurable
    {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (n : ℕ) (e : Vec d)
    (hm : AEStronglyMeasurable
      (fun a => sourceDirichletEnergy a (sourceTriadicCube d n) e) P) :
    Integrable (fun a => sourceDirichletEnergy a (sourceTriadicCube d n) e) P := by
  apply (integrable_const ((K / 2) * euclideanSq e)).mono' hm
  exact ae_of_all _ fun a => by
    rw [Real.norm_of_nonneg (sourceDirichletEnergy_nonneg a _ e)]
    exact sourceDirichletEnergy_triadic_upper hK a n e

end EinsteinRelation.External.AKM
