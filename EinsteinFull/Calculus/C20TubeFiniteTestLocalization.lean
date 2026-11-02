import EinsteinFull.Calculus.C18TubeFixedNonlinearIntegrability

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- A finite sum of differentiable tests has the sum of their weighted pairings. -/
theorem c20_finite_test_pairing_sum {d n : ℕ}
    (μ : Measure (ℝ × Vec d))
    (A C : ℝ × Vec d → ℝ) (B : ℝ × Vec d → Vec d)
    (ψ : Fin n → ℝ × Vec d → ℝ)
    (hψ : ∀ i, Differentiable ℝ (ψ i))
    (hi : ∀ i, Integrable (fun z =>
      A z * fderiv ℝ (ψ i) z (1,0) +
      dot (B z) (fun j => fderiv ℝ (ψ i) z (0,unitVector j)) + C z * ψ i z) μ) :
    (∫ z, A z * fderiv ℝ (fun z => ∑ i, ψ i z) z (1,0) +
      dot (B z) (fun j => fderiv ℝ (fun z => ∑ i, ψ i z) z (0,unitVector j)) +
      C z * (∑ i, ψ i z) ∂μ) =
    ∑ i, ∫ z, A z * fderiv ℝ (ψ i) z (1,0) +
      dot (B z) (fun j => fderiv ℝ (ψ i) z (0,unitVector j)) + C z * ψ i z ∂μ := by
  classical
  have hpoint (z : ℝ × Vec d) :
      A z * fderiv ℝ (fun z => ∑ i, ψ i z) z (1,0) +
        dot (B z) (fun j => fderiv ℝ (fun z => ∑ i, ψ i z) z (0,unitVector j)) +
        C z * (∑ i, ψ i z) =
      ∑ i, (A z * fderiv ℝ (ψ i) z (1,0) +
        dot (B z) (fun j => fderiv ℝ (ψ i) z (0,unitVector j)) + C z * ψ i z) := by
    rw [fderiv_fun_sum (fun i _ => (hψ i).differentiableAt)]
    simp only [sum_apply, dot, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  simp_rw [hpoint]
  exact integral_finsetSum Finset.univ (fun i _ => hi i)

/-- A temporal partition equal to one on the support reconstructs the test globally. -/
theorem c20_temporal_partition_test_eq {d n : ℕ}
    (η : Fin n → ℝ → ℝ) (ψ : ℝ × Vec d → ℝ)
    (hpart : ∀ z ∈ tsupport ψ, ∑ i, η i z.1 = 1) :
    ψ = fun z => ∑ i, η i z.1 * ψ z := by
  classical
  funext z
  rw [← Finset.sum_mul]
  by_cases hz : z ∈ tsupport ψ
  · rw [hpart z hz, one_mul]
  · have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
    rw [hzero, mul_zero]

/-- A test supported in a smaller region has the same pairing on either region. -/
theorem c20_test_pairing_restrict {d : ℕ} (μ : Measure (ℝ × Vec d))
    (s t : Set (ℝ × Vec d)) (ht : MeasurableSet t) (hst : s ⊆ t)
    (A C : ℝ × Vec d → ℝ) (B : ℝ × Vec d → Vec d)
    (φ : ℝ × Vec d → ℝ) (hφ : tsupport φ ⊆ s) :
    (∫ z in t, A z * fderiv ℝ φ z (1,0) +
      dot (B z) (fun j => fderiv ℝ φ z (0,unitVector j)) + C z * φ z ∂μ) =
    (∫ z in s, A z * fderiv ℝ φ z (1,0) +
      dot (B z) (fun j => fderiv ℝ φ z (0,unitVector j)) + C z * φ z ∂μ) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ht hst
  intro z hz
  have hn : z ∉ tsupport φ := fun h => hz.2 (hφ h)
  simp [fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn, dot]

/-- Local zero pairings for a temporal partition imply the full weighted identity. -/
theorem c20_weighted_finite_test_localization {d n : ℕ} {a b R : ℝ}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (F : ℝ → ℝ)
    (η : Fin n → ℝ → ℝ) (ψ : ℝ × Vec d → ℝ)
    (hpart : ∀ z ∈ tsupport ψ, ∑ i, η i z.1 = 1)
    (hdiff : ∀ i, Differentiable ℝ (fun z => η i z.1 * ψ z))
    (hi : ∀ i, Integrable (fun z : ℝ × Vec d =>
      -(ρ z.2 * F (u z)) * fderiv ℝ (fun z => η i z.1 * ψ z) z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ (fun z => η i z.1 * ψ z) z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * (η i z.1 * ψ z))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (s : Fin n → Set (ℝ × Vec d))
    (hsub : ∀ i, s i ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (hsupp : ∀ i, tsupport (fun z => η i z.1 * ψ z) ⊆ s i)
    (hlocal : ∀ i, (∫ z in s i,
      -(ρ z.2 * F (u z)) * fderiv ℝ (fun z => η i z.1 * ψ z) z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ (fun z => η i z.1 * ψ z) z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * (η i z.1 * ψ z)) = 0) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0 := by
  classical
  have hglobal (i : Fin n) : (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ (fun z => η i z.1 * ψ z) z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ (fun z => η i z.1 * ψ z) z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * (η i z.1 * ψ z)) = 0 := by
    have hr := c20_test_pairing_restrict volume (s i)
      (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
      (measurableSet_Ioo.prod (c20_sourceBall_measurable 0 R)) (hsub i)
      (fun z => -(ρ z.2 * F (u z)))
      (fun z => deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z))
      (fun z => deriv F (u z) • ((α z.2).mulVec (G z)))
      (fun z => η i z.1 * ψ z) (hsupp i)
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] at hr ⊢
    exact hr.trans (by simpa [dot, Finset.mul_sum, mul_assoc] using hlocal i)
  have hsum := c20_finite_test_pairing_sum
    (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R))
    (fun z => -(ρ z.2 * F (u z)))
    (fun z => deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z))
    (fun z => deriv F (u z) • ((α z.2).mulVec (G z)))
    (fun i z => η i z.1 * ψ z) hdiff (by simpa [dot, Finset.mul_sum, mul_assoc] using hi)
  have heq := c20_temporal_partition_test_eq η ψ hpart
  rw [← heq] at hsum
  have heqz (z : ℝ × Vec d) : (∑ i, η i z.1 * ψ z) = ψ z :=
    (congrFun heq z).symm
  simp_rw [heqz] at hsum
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] at hsum hglobal ⊢
  simpa only [hglobal, Finset.sum_const_zero] using hsum

/-- Smooth compact partition pieces have the integrability needed by localization. -/
theorem c20_caloric_partition_piece_integrable {d n : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (η : Fin n → ℝ → ℝ) (ψ : ℝ × Vec d → ℝ)
    (hη : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (η i))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : ∀ i, tsupport (fun z => η i z.1 * ψ z) ⊆
      Set.Ioo a b ×ˢ sourceBall 0 R) :
    ∀ i, Differentiable ℝ (fun z => η i z.1 * ψ z) ∧
      Integrable (fun z : ℝ × Vec d =>
        -(ρ z.2 * F (u z)) * fderiv ℝ (fun z => η i z.1 * ψ z) z (1,0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ (fun z => η i z.1 * ψ z) z (0,unitVector j)) +
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * (η i z.1 * ψ z))
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  intro i
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec d => η i z.1 * ψ z) :=
    ((hη i).comp contDiff_fst).mul hψ
  refine ⟨hp.differentiable (by simp), ?_⟩
  exact c18_tested_nonlinear_pairing_integrable hκ hR hab ρ α hell 0 u G
    hcal.1 hcal.2.1 hcal.2.2.1 F hF M hM hder _ hp hc.mul_left (hs i)

end EinsteinFull.Calculus
