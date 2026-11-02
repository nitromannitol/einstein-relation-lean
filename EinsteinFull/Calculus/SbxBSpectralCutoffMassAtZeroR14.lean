import EinsteinFull.Calculus.SbxBNormalizedLocalDefectR10
import EinsteinFull.Calculus.SbxBUnitPointwiseHarnackR12

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- The annular exponential defect estimate implies the prescribed-point initial
trace for the actual symmetric spectral action of any admissible cutoff. -/
theorem br14_spectral_cutoff_initial_one
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ)
    (hDecay : ∃ D : ℝ, 0 < D ∧
      ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
      ∀ (s : DirichletSpectralResolution ρ α R) (x : Vec d) (r : ℝ), 0 < r →
        sourceBall x (2*r) ⊆ sourceBall 0 R →
      ∀ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
        tsupport φ ⊆ sourceBall x (2*r) →
        (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
        (∀ z ∈ sourceBall x r, φ z = 1) →
        (∀ z, euclideanSq (fun i => fderiv ℝ φ z (unitVector i)) ≤ 1024 / r^2) →
      ∀ T : ℝ, 0 < T → T ≤ r^2 →
        (∫ z in Set.Ioo (0 : ℝ) T ×ˢ sourceBall x (r/2),
          |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
              s.eigenfunction n z.2 * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1| ^ 2)
          ≤ D * T * r^d * Real.exp (-(r^2 / (D*T))))
    {R : ℝ} (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (x : Vec d) (r : ℝ) (hr : 0 < r)
    (hinside : sourceBall x (2*r) ⊆ sourceBall 0 R)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hsupp : tsupport φ ⊆ sourceBall x (2*r))
    (hbounds : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1)
    (hplateau : ∀ z ∈ sourceBall x r, φ z = 1)
    (hgrad : ∀ z, euclideanSq (fun i => fderiv ℝ φ z (unitVector i)) ≤ 1024 / r^2) :
    Tendsto (fun t : ℝ => ∫ y, (∑' n, Real.exp (-s.eigenvalue n*t) *
      s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
  obtain ⟨C, hC, hunit⟩ := b_weighted_unit_L2_local_max_integral d hd κ hκ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C' := C / ε
  have hC' : 0 < C' := div_pos hC hε
  obtain ⟨a, ha, ha2, hlocal⟩ :=
    b_normalized_local_defect_of_exponential_estimate d hd κ C' hκ hC' hDecay
  let q := a*r
  have hq : 0 < q := mul_pos ha hr
  have hsmallrad : 2*q < r := by
    dsimp [q]
    have h := mul_lt_mul_of_pos_right ha2 hr
    nlinarith
  have hinner := b_sourceBall_closure_subset_larger x hsmallrad
  have hball : sourceBall x r ⊆ sourceBall (0 : Vec d) R := by
    intro z hz
    apply hinside
    change euclideanNorm (z-x) < r at hz
    change euclideanNorm (z-x) < 2*r
    linarith
  have hclose : closure (sourceBall x (2*q)) ⊆ sourceBall 0 R := hinner.trans hball
  have hplateau' : ∀ z ∈ sourceBall x (2*q), φ z = 1 := by
    intro z hz
    exact hplateau z (hinner (subset_closure hz))
  have hs := br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell s
  obtain ⟨H, hcal, hcont⟩ := b_native_cutoff_defect_caloric_continuous
    hd hκ hR hell s hs φ hφ hbounds x q (q^2) hq (sq_pos_of_pos hq) hclose hplateau'
  let v : ℝ × Vec d → ℝ := fun z => if 0 < z.1 then
    (∫ y, (∑' n, Real.exp (-s.eigenvalue n*z.1) * s.eigenfunction n z.2 *
      s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1 else 0
  change IsWeightedCaloric ρ α (Set.Ioo (-q^2) (q^2)) (sourceBall x q) v H at hcal
  change ContinuousOn v (Set.Ioo (0 : ℝ) (q^2) ×ˢ sourceBall x q) at hcont
  have hcont' : ContinuousOn v (Set.Ioo (0 : ℝ) (q^2/4) ×ˢ sourceBall x (q/2)) :=
    hcont.mono (by
      rintro ⟨t,z⟩ ⟨ht,hz⟩
      refine ⟨⟨ht.1, by nlinarith [ht.2, sq_pos_of_pos hq]⟩, ?_⟩
      change euclideanNorm (z-x) < q/2 at hz
      change euclideanNorm (z-x) < q
      linarith)
  let I : ℝ := (q^(d+2))⁻¹ *
    ∫ z in Set.Ioo (-q^2) (q^2) ×ˢ sourceBall x q, |v z|^2
  have hI : 0 ≤ I := mul_nonneg (inv_nonneg.mpr (pow_nonneg hq.le _))
    (integral_nonneg fun z => sq_nonneg _)
  have hsmall : I ≤ (1 / (2*C'))^2 := by
    simpa only [I, q, v] using hlocal R hR ρ α hell s x r hr hinside φ hφ
      hsupp hbounds hplateau hgrad
  have hroot : Real.sqrt I ≤ 1 / (2*C') := by
    have hsq := Real.sq_sqrt hI
    have hn : 0 ≤ 1 / (2*C') := by positivity
    nlinarith [Real.sqrt_nonneg I, sq_nonneg (Real.sqrt I + 1 / (2*C'))]
  have hpoint := b_scaled_weighted_caloric_pointwise_max d hd κ C hκ hC hunit
    x q hq ρ α hell v H hcal hcont'
  have hx : x ∈ sourceBall x (q/2) := by
    change euclideanNorm (x-x) < q/2
    simpa [euclideanNorm, euclideanSq, dot] using (half_pos hq)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show 0 < q^2/4 by positivity)).filter_mono nhdsWithin_le_nhds]
    with t ht htq
  change 0 < t at ht
  have hh := hpoint t ⟨ht, htq⟩ x hx
  have hmul := mul_le_mul_of_nonneg_left hroot hC.le
  have heq : C * (1/(2*C')) = ε/2 := by
    dsimp [C']
    field_simp
  rw [heq] at hmul
  simp only [Real.dist_eq]
  have hh' : |(∫ y, (∑' n, Real.exp (-s.eigenvalue n*t) *
      s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1| ≤ ε/2 := by
    simpa only [v, if_pos ht, I] using hh.trans hmul
  linarith

#print axioms br14_spectral_cutoff_initial_one

end EinsteinFull.Calculus
