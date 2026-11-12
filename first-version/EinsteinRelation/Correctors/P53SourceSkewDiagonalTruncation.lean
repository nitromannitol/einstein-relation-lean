import EinsteinRelation.Correctors.P53SourceSkewTruncationPairing
import EinsteinRelation.Correctors.P53SourceSkewHeatSmoothedDivergence
import EinsteinRelation.Correctors.P53SourceSkewHeatWindowTransfer
import EinsteinRelation.Correctors.HeatTransferTimeIntegrability

/-!
# The row divergence of the AKM heat truncations

Source: `paper/main.tex:732-748`; AKM Lemma 6.1, Step 4. Summing the truncations
over the column equal to the derivative index, the term with the divergence of
the source vanishes because the source is divergence free, and the Laplacian term
integrates in time to the difference of two heat averages of the source:
`Σ_k ⟨T_{jkk}, ψ⟩ = ⟨H_a g_j, ψ⟩ - ⟨H_b g_j, ψ⟩` on the window `[a, b]`.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

variable {d : ℕ}

/-- The coordinate Laplacian is the sum of the diagonal second derivatives. -/
theorem coordLaplacian_eq_sum (ψ : Vec d → ℝ) :
    coordLaplacian ψ = fun x => ∑ k : Fin d,
      coordinateDerivative k (coordinateDerivative k ψ) x := rfl

/-- Row divergence of the tested truncations along almost every orbit. -/
theorem ae_sum_horizontalMollify_truncation_diag (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hg2 : ∀ k, MemLp (fun ω => g ω k) 2 Q)
    (hdiv : ∀ᵐ ρ ∂Q, HasWeakDivergence Set.univ (fun x => g (translate x ρ)) (fun _ => 0))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (m n : ℕ)
    (j : Fin d) :
    ∀ᵐ ρ ∂Q, (∑ k : Fin d, horizontalMollify ψ (fun ω =>
        iteratedAKMHeatGradientTruncation (fun y => g (translate y ω)) m n j k k 0) ρ) =
      horizontalMollify ψ (heatSmoothed (((m + 1 : ℕ) : ℝ)⁻¹) (fun ω => g ω j)) ρ -
        horizontalMollify ψ (heatSmoothed ((n + 1 : ℕ) : ℝ) (fun ω => g ω j)) ρ := by
  set a : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹ with hadef
  set b : ℝ := ((n + 1 : ℕ) : ℝ) with hbdef
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by
    have h1 : a ≤ 1 := inv_le_one_of_one_le₀ (by norm_cast; omega)
    have h2 : (1 : ℝ) ≤ b := by rw [hbdef]; norm_cast; omega
    linarith
  set ν : Measure ℝ := volume.restrict (truncationWindow m n) with hνdef
  have hgi (i : Fin d) : Integrable (fun ω => g ω i) Q := (hg2 i).integrable one_le_two
  have hgk (i : Fin d) : Measurable (fun ω => g ω i) := (measurable_pi_apply i).comp hg
  have hDD (p q : Fin d) :
      ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative p (coordinateDerivative q ψ)) :=
    contDiff_coordinateDerivative' (contDiff_coordinateDerivative' hψ q) p
  have hDDc (p q : Fin d) : HasCompactSupport (coordinateDerivative p (coordinateDerivative q ψ)) :=
    hasCompactSupport_coordinateDerivative' (hasCompactSupport_coordinateDerivative' hψc q) p
  have hDDm (p q : Fin d) := (hDD p q).continuous.measurable
  have hDDi (p q : Fin d) : Integrable (coordinateDerivative p (coordinateDerivative q ψ)) volume :=
    (hDD p q).continuous.integrable_of_hasCompactSupport (hDDc p q)
  -- time integrability of every term on the window
  have hwin : truncationWindow m n ⊆ Set.Ioc 0 b := fun t ht => ⟨lt_of_lt_of_le ha ht.1, ht.2⟩
  have htimeInt (p q i : Fin d) : ∀ᵐ ρ ∂Q, Integrable (fun t =>
      horizontalMollify (coordinateDerivative p (coordinateDerivative q ψ))
        (heatSmoothed t (fun ω => g ω i)) ρ) ν := by
    filter_upwards [ae_intervalIntegrable_horizontalMollify_heatSmoothed Q hQ (hDDm p q)
      (hDDi p q) (hgk i) (hgi i) (by positivity : (0 : ℝ) ≤ b)] with ρ hρ
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp hρ).mono_set hwin
  -- the divergence term vanishes for almost every time
  have hjoint (p q i : Fin d) : Measurable (fun z : ℝ × FieldPair d =>
      horizontalMollify (coordinateDerivative p (coordinateDerivative q ψ))
        (heatSmoothed z.1 (fun ω => g ω i)) z.2) :=
    measurable_horizontalMollify_heatSmoothed_joint (hDDm p q) (hgk i)
  have hdivTime : ∀ᵐ ρ ∂Q, ∀ᵐ t ∂ν, (∑ k : Fin d,
      horizontalMollify (coordinateDerivative j (coordinateDerivative k ψ))
        (heatSmoothed t (fun ω => g ω k)) ρ) = 0 := by
    have hset : MeasurableSet {z : ℝ × FieldPair d | (∑ k : Fin d,
        horizontalMollify (coordinateDerivative j (coordinateDerivative k ψ))
          (heatSmoothed z.1 (fun ω => g ω k)) z.2) = 0} :=
      measurableSet_eq_fun (Finset.measurable_sum _ fun k _ => hjoint j k k) measurable_const
    refine (Measure.ae_ae_comm (μ := ν) (ν := Q) hset).mp ?_
    refine (ae_restrict_iff' (measurableSet_truncationWindow m n)).mpr (ae_of_all _ fun t ht => ?_)
    have h := ae_sum_horizontalMollify_heatSmoothed_divergence_eq_zero Q hQ hg hgi hdiv
      (contDiff_coordinateDerivative' hψ j) (hasCompactSupport_coordinateDerivative' hψc j)
      (truncationWindow_pos ht).le
    filter_upwards [h] with ρ hρ
    simpa only [coordinateDerivative_comm hψ j] using hρ
  -- the Laplacian term
  have hlapTime : ∀ᵐ ρ ∂Q, ∀ᵐ t ∂ν, (∑ k : Fin d,
      horizontalMollify (coordinateDerivative k (coordinateDerivative k ψ))
        (heatSmoothed t (fun ω => g ω j)) ρ) =
        horizontalMollify (coordLaplacian ψ) (heatSmoothed t (fun ω => g ω j)) ρ := by
    have hset : MeasurableSet {z : ℝ × FieldPair d | (∑ k : Fin d,
        horizontalMollify (coordinateDerivative k (coordinateDerivative k ψ))
          (heatSmoothed z.1 (fun ω => g ω j)) z.2) =
        horizontalMollify (coordLaplacian ψ) (heatSmoothed z.1 (fun ω => g ω j)) z.2} :=
      measurableSet_eq_fun (Finset.measurable_sum _ fun k _ => hjoint k k j)
        (measurable_horizontalMollify_heatSmoothed_joint
          (continuous_coordLaplacian (hψ.of_le (by norm_cast))).measurable (hgk j))
    refine (Measure.ae_ae_comm (μ := ν) (ν := Q) hset).mp ?_
    refine (ae_restrict_iff' (measurableSet_truncationWindow m n)).mpr (ae_of_all _ fun t ht => ?_)
    have hHt : Measurable (heatSmoothed t (fun ω => g ω j)) :=
      (measurable_heatSmoothed_joint (hgk j)).comp (measurable_const.prodMk measurable_id)
    have hHti : Integrable (heatSmoothed t (fun ω => g ω j)) Q := by
      have h := eLpNorm_heatSmoothed_le Q hQ le_rfl (hgk j) (truncationWindow_pos ht).le
      rw [ENNReal.ofReal_one] at h
      exact memLp_one_iff_integrable.mp ⟨hHt.aestronglyMeasurable,
        h.trans_lt (memLp_one_iff_integrable.mpr (hgi j)).eLpNorm_lt_top⟩
    have h := horizontalMollify_sum_kernel_ae hQ Finset.univ (fun k => hDDm k k)
      (fun k => hDDi k k) hHt hHti
    filter_upwards [h] with ρ hρ
    rw [coordLaplacian_eq_sum, hρ]
  filter_upwards [ae_all_iff.mpr fun k => ae_horizontalMollify_truncation_eq Q hQ hg hg2 hψ hψc
      m n j k k, ae_all_iff.mpr fun k => htimeInt j k k, ae_all_iff.mpr fun k => htimeInt k k j,
    hdivTime, hlapTime, ae_setIntegral_horizontalMollify_laplacian_heatSmoothed Q hQ
      (hψ.of_le (by norm_cast)) hψc (hgk j) (hgi j) ha.le hab]
    with ρ hT hA hB hdivρ hlapρ hwinρ
  simp_rw [hT]
  have hsum := integral_finset_sum (μ := ν) Finset.univ fun k _ => (hA k).sub (hB k)
  simp only [Pi.sub_apply] at hsum
  rw [← hsum]
  have hcongr : (fun t => ∑ k : Fin d,
      (horizontalMollify (coordinateDerivative j (coordinateDerivative k ψ))
          (heatSmoothed t (fun ω => g ω k)) ρ -
        horizontalMollify (coordinateDerivative k (coordinateDerivative k ψ))
          (heatSmoothed t (fun ω => g ω j)) ρ)) =ᵐ[ν]
      fun t => -horizontalMollify (coordLaplacian ψ) (heatSmoothed t (fun ω => g ω j)) ρ := by
    filter_upwards [hdivρ, hlapρ] with t h1 h2
    rw [Finset.sum_sub_distrib, h1, h2, zero_sub]
  rw [integral_congr_ae hcongr, integral_neg]
  have hw := hwinρ.2
  change (∫ t in truncationWindow m n, _) = _ at hw
  rw [hw]
  ring

end EinsteinRelation.Correctors
