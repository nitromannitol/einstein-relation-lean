import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_local_u23_crude_u2D_energy
import EinsteinFull.Frozen.EndpointWeakFlux
import EinsteinFull.Calculus.ComplexGeneratorUniquenessSupport
import EinsteinFull.Calculus.C2TestReplacementSupport

open MeasureTheory
open scoped NNReal ENNReal
open EinsteinRelation

namespace EinsteinFull.Calculus.K8

private theorem norm_unitVector_le {d : ℕ} (i k : Fin d) :
    ‖((unitVector i k : ℝ) : ℂ)‖ ≤ 1 := by
  by_cases h : k = i
  · subst h; simp [unitVector]
  · simp [unitVector, Pi.single_apply, h]

/-- Pointwise bound of the flux formula from bounds on its ingredients. -/
private theorem norm_flux_le {d : ℕ} (A B : ℝ) (hA : 0 ≤ A)
    (c a G e : Fin d → ℂ)
    (hc : ∀ k, ‖a k - c k‖ ≤ A) (hG : ∀ k, ‖G k‖ ≤ B)
    (he : ∀ k, ‖e k‖ ≤ 8 * B) :
    ‖∑ k : Fin d, (a k - c k) * (G k - e k)‖ ≤ d * (A * (B + 8 * B)) := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ (Finset.univ : Finset (Fin d)), ‖(a k - c k) * (G k - e k)‖ ≤ A * (B + 8 * B) := by
    intro k _
    rw [norm_mul]
    exact mul_le_mul (hc k) ((norm_sub_le _ _).trans (add_le_add (hG k) (he k)))
      (norm_nonneg _) hA
  refine (Finset.sum_le_sum this).trans ?_
  simp


/-- For `t ≥ 1` and `‖ζ‖ ≤ 4`, every weak flux of the actual indexed endpoint is essentially
bounded (crude energy, reduced-coefficient bounds, gradient uniqueness through the local-time
gradient), hence lies in every finite `Lᵖ`. -/
theorem endpoint_flux_memLp_of_crude
    (hlt : EinsteinFull.Blueprint.node_e_u3A_local_u2D_timeStmt)
    (hcr : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 4)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (t : ℝ≥0) (ht : 1 ≤ (t : ℝ)) (G J : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hGJ : IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t) G J)
    {p : ℝ} (j : Fin d) :
    MemLp (J j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := by
  letI := EinsteinFull.reducedLaw_probability Q
  have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le one_pos ht
  obtain ⟨C1, Cp, hC1, hCp, hlt'⟩ := hlt d hd D 2 le_rfl
  obtain ⟨Glt, V, hGlt, -⟩ := hlt' Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨C, N, hC, hcr'⟩ := hcr d hd D
  obtain ⟨Gc, hGc1, hGc2⟩ := hcr' Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨h1, h2, -⟩ := hGlt t ht0
  have hG : G = Glt t := hGJ.1.unique h1
  have hGc : Gc t = Glt t := (hGc1 t ht).unique h2
  have hcrude := (hGc2 t ht hζ).1
  set B : ℝ := C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) with hBdef
  have hB : 0 ≤ B := by positivity
  have hGb : ∀ᵐ ω ∂reducedLaw Q, ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ B ∧
      ∀ k, ‖G k ω‖ ≤ B := by
    filter_upwards [hcrude] with ω hω
    refine ⟨(le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hω, fun k => ?_⟩
    have hk : ‖G k ω‖ ≤ Real.sqrt (∑ j : Fin d, ‖Gc t j ω‖ ^ 2) := by
      rw [hG, ← hGc]
      apply Real.le_sqrt_of_sq_le
      exact Finset.single_le_sum (f := fun j : Fin d => ‖Gc t j ω‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    exact hk.trans ((le_add_of_nonneg_left (norm_nonneg _)).trans hω)
  have hUb : ∀ᵐ ω ∂reducedLaw Q, ν = Sum.inr true →
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ B := by
    filter_upwards [hGb] with ω hω hν
    subst hν
    exact hω.1
  obtain ⟨H, hH⟩ := (Set.finite_range
    (fun q : Fin d × Fin d => |homogenizedCoefficient Q q.1 q.2|)).bddAbove
  have hcoef := EinsteinFull.Calculus.C2TestReplacement.ae_abs_reducedCoefficient_entry_le Q
  have haa : ∀ k, (a j k : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => (ω.1 0 j k : ℂ) :=
    fun k => ha j k
  have haall : ∀ᵐ ω ∂reducedLaw Q, ∀ k, a j k ω = (ω.1 0 j k : ℂ) := by
    rw [ae_all_iff]; exact haa
  have hJj := hGJ.2 j
  set A : ℝ := |sourceReducedBound D.ellipticity| + |H| with hAdef
  have hA : 0 ≤ A := by positivity
  have hbound : ∀ᵐ ω ∂reducedLaw Q, ‖(J j : FieldPair d → ℂ) ω‖ ≤ d * (A * (B + 8 * B)) := by
    filter_upwards [hJj, hcoef, haall, hGb, hUb] with ω hJω hcω haω hGω hUω
    rw [hJω]
    refine norm_flux_le A B hA _ _ _ _ ?_ ?_ ?_
    swap
    · intro k; exact hGω.2 k
    · intro k
      rw [haω k]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := hcω j k
      have h2 : |homogenizedCoefficient Q j k| ≤ H := hH ⟨(j, k), rfl⟩
      exact add_le_add (h1.trans (le_abs_self _)) (h2.trans (le_abs_self _))
    · intro k
      cases ν with
      | inl i => simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hB
      | inr b =>
        cases b with
        | false => simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hB
        | true =>
          have hU := hUω rfl
          simp only [norm_mul]
          have hu := norm_unitVector_le (⟨0, by omega⟩ : Fin d) k
          have h2' : ‖(2 : ℂ)‖ = 2 := by simp
          have h2 : ‖(2 : ℂ)‖ * ‖ζ‖ ≤ 8 := by rw [h2']; linarith
          calc _ ≤ (8 : ℝ) * 1 * B := by
                gcongr
            _ = 8 * B := by ring
  have hmeas : AEStronglyMeasurable (J j : FieldPair d → ℂ) (reducedLaw Q) :=
    (Lp.stronglyMeasurable (J j)).aestronglyMeasurable
  have htop : MemLp (J j : FieldPair d → ℂ) ∞ (reducedLaw Q) :=
    memLp_top_of_bound hmeas _ hbound
  exact htop.mono_exponent le_top

end EinsteinFull.Calculus.K8
