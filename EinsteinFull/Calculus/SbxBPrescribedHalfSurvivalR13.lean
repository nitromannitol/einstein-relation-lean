import EinsteinFull.Calculus.SbxBWeightedLocalMaxR09
import EinsteinFull.Calculus.SbxBNormalizedLocalDefectR10

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- The annular exponential defect estimate implies uniform survival for every
prescribed starting point, with the time constant fixed before the domain and
coefficients. -/
theorem b_prescribed_half_survival_of_exponential_defect
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
          ≤ D * T * r^d * Real.exp (-(r^2 / (D*T)))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ), 0 < R →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ (x : Vec d) (r : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      ∀ t : ℝ, 0 < t → t ≤ δ*r^2 →
        (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K t x y := by
  obtain ⟨C, hC, hbound⟩ := b_weighted_unit_L2_local_max d hd κ hκ
  have hunit : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      essSup (fun z => ENNReal.ofReal |u z|)
        (volume.restrict (Set.Ioo (-(1/4 : ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (C * Real.sqrt
        (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, |u z|^2)) := by
    intro ρ α hell u G hcal
    have h := hbound ρ α hell u G hcal
    have hreal : (eLpNorm u 2
        (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))).toReal =
        Real.sqrt (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z| ^ 2) := by
      rw [hcal.1.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
      congr 1
      · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
          simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs])
      · simp
    have hn : eLpNorm u 2 (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) =
        ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z| ^ 2)) := by
      rw [← hreal, ENNReal.ofReal_toReal hcal.1.eLpNorm_ne_top]
    have hsup : essSup (fun z => ENNReal.ofReal |u z|)
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
        eLpNorm u ⊤ (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) := by
      simpa only [eLpNormEssSup_eq_essSup_enorm, Real.enorm_eq_ofReal_abs] using
        (eLpNormEssSup_le_eLpNorm_top (f := u)
          (μ := volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))))
    calc
      _ ≤ ENNReal.ofReal C * eLpNorm u 2
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := hsup.trans h
      _ = _ := by rw [hn, ← ENNReal.ofReal_mul hC.le]
  exact b_uniform_prescribed_row_of_local_defect d hd κ C hκ hC hunit
    (b_normalized_local_defect_of_exponential_estimate d hd κ C hκ hC hDecay)

end EinsteinFull.Calculus

#print axioms EinsteinFull.Calculus.b_prescribed_half_survival_of_exponential_defect
