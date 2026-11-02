import EinsteinFull.Calculus.C7DyadicAdjustableHolderRecovery

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint

theorem c19_dyadic_adjustable_point_majorant_recovery (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (bmax : ℝ) (hbmax : 0 < bmax) : ∃ b : ℝ, 0 < b ∧ b ≤ min bmax (1/16) ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 → ∀ growth K A : ℝ, 0 ≤ growth → 0 ≤ K → 0 ≤ A → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ (t/8)‖ ≤ K * Real.exp (growth*‖ζ‖^2*((t : ℝ)/8)) * (((t : ℝ)/8) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * ((t : ℝ)/8) ^ (-(d : ℝ)/4)) → ∀ hbt : 0 < b*(t : ℝ), ‖gaussianAverage hd Q (b*(t : ℝ)) hbt (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤ A * Real.exp (growth*‖ζ‖^2*(t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤ (A+K/2) * Real.exp (growth*‖ζ‖^2*(t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) := by
  obtain ⟨b, hb, hbsmall, herr⟩ := c7_dyadic_adjustable_weighted_holder_half_error hlocal d hd D bmax hbmax
  refine ⟨b, hb, hbsmall, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hz growth K A hgrowth hK hA hU hbt hgauss
  have he := herr Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hz growth K hgrowth hK hU hbt
  have htriangle := norm_le_norm_sub_add (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
    (gaussianAverage hd Q (b * (t : ℝ)) hbt (indexedEndpoint hd Q ν ζ P Pdag β a μ t))
  calc
    _ ≤ _ := htriangle
    _ ≤ (K/2) * Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) + A * Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) := add_le_add he hgauss
    _ = _ := by ring


/-- Rescaling the Gaussian radius costs one constant for both force weights. -/
theorem c19_dyadic_weight_rescale (b t x y z : ℝ)
    (hb : 0 < b) (ht : 0 < t) (hz : 0 ≤ z) :
    (b * t) ^ x + z * (b * t) ^ y ≤
      max (b ^ x) (b ^ y) * (t ^ x + z * t ^ y) := by
  rw [Real.mul_rpow hb.le ht.le, Real.mul_rpow hb.le ht.le]
  have hx := mul_le_mul_of_nonneg_right (le_max_left (b ^ x) (b ^ y))
    (Real.rpow_nonneg ht.le x)
  have hy := mul_le_mul_of_nonneg_right (le_max_right (b ^ x) (b ^ y))
    (mul_nonneg hz (Real.rpow_nonneg ht.le y))
  nlinarith only [hx, hy]


/-- Recover the point estimate from the naturally scaled Gaussian majorant. -/
theorem c19_dyadic_point_recovery_from_gaussian_weight (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (bmax : ℝ) (hbmax : 0 < bmax) : ∃ b : ℝ, 0 < b ∧ b ≤ min bmax (1/16) ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 → ∀ growth K A : ℝ, 0 ≤ growth → 0 ≤ K → 0 ≤ A → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ (t/8)‖ ≤ K * Real.exp (growth*‖ζ‖^2*((t : ℝ)/8)) * (((t : ℝ)/8) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * ((t : ℝ)/8) ^ (-(d : ℝ)/4)) → ∀ hbt : 0 < b*(t : ℝ), ‖gaussianAverage hd Q (b*(t : ℝ)) hbt (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤ A * Real.exp (growth*‖ζ‖^2*(t : ℝ)) * ((b*(t : ℝ)) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (b*(t : ℝ)) ^ (-(d : ℝ)/4)) → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤ (A * max (b ^ (-(1/2+(d : ℝ)/4))) (b ^ (-(d : ℝ)/4)) + K/2) * Real.exp (growth*‖ζ‖^2*(t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) := by
  obtain ⟨b, hb, hbsmall, herr⟩ :=
    c19_dyadic_adjustable_point_majorant_recovery hlocal d hd D bmax hbmax
  refine ⟨b, hb, hbsmall, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hz growth K A hgrowth hK hA hU hbt hgauss
  let c : ℝ := max (b ^ (-(1/2+(d : ℝ)/4))) (b ^ (-(d : ℝ)/4))
  have hc : 0 ≤ c := le_trans (Real.rpow_nonneg hb.le _) (le_max_left _ _)
  have hw := c19_dyadic_weight_rescale b (t : ℝ) (-(1/2+(d : ℝ)/4))
    (-(d : ℝ)/4) ‖ζ‖ hb (by linarith) (norm_nonneg ζ)
  have hbound : ‖gaussianAverage hd Q (b*(t : ℝ)) hbt
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤
      (A*c) * Real.exp (growth*‖ζ‖^2*(t : ℝ)) *
      ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) := by
    calc
      _ ≤ _ := hgauss
      _ ≤ A * Real.exp (growth*‖ζ‖^2*(t : ℝ)) *
          (c * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4))) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hA (Real.exp_pos _).le)
      _ = _ := by ring
  exact herr Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hz growth K (A*c)
    hgrowth hK (mul_nonneg hA hc) hU hbt hbound


/-- In the unit force window, the point weight has unforced decay. -/
theorem c19_unit_force_point_weight (t x z : ℝ) (ht : 0 < t)
    (hz : z * Real.sqrt t ≤ 1) :
    t ^ (-(1/2+x)) + z * t ^ (-x) ≤ 2 * t ^ (-(1/2+x)) := by
  have hp : t ^ (1/2 : ℝ) * t ^ (-(1/2+x)) = t ^ (-x) := by
    rw [← Real.rpow_add ht]
    congr 1 <;> ring
  rw [Real.sqrt_eq_rpow] at hz
  have h := mul_le_mul_of_nonneg_right hz (Real.rpow_nonneg ht.le (-(1/2+x)))
  have hf : z * t ^ (-x) ≤ t ^ (-(1/2+x)) := by
    calc
      _ = z * (t ^ (1/2 : ℝ) * t ^ (-(1/2+x))) := by rw [hp]
      _ = (z * t ^ (1/2 : ℝ)) * t ^ (-(1/2+x)) := by ring
      _ ≤ _ := by simpa only [one_mul] using h
  linarith


/-- Pointwise half of the dyadic step, with actual endpoint and Gaussian bounds. -/
theorem c19_dyadic_actual_point_step
    (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (bmax : ℝ) (hbmax : 0 < bmax) :
    ∃ b : ℝ, 0 < b ∧ b ≤ min bmax (1/16) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∀ (T : ℝ) (t : ℝ≥0) (growth Kp A : ℝ),
      8 ≤ T → T ≤ (t : ℝ) → (t : ℝ) ≤ 2*T →
      ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 1 → 0 ≤ growth → 0 ≤ Kp → 0 ≤ A →
      (∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ T →
        ‖indexedEndpoint hd Q ν ζ P Pdag β a μ r‖ ≤
          Kp * Real.exp (growth*‖ζ‖^2*(r : ℝ)) *
          ((r : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (r : ℝ) ^ (-(d : ℝ)/4))) →
      (∀ hbt : 0 < b*(t : ℝ),
        ‖gaussianAverage hd Q (b*(t : ℝ)) hbt (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤
          A * Real.exp (growth*‖ζ‖^2*(t : ℝ)) *
          ((b*(t : ℝ)) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (b*(t : ℝ)) ^ (-(d : ℝ)/4))) →
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤
        (A * max (b ^ (-(1/2+(d : ℝ)/4))) (b ^ (-(d : ℝ)/4)) + Kp/2) *
        Real.exp (growth*‖ζ‖^2*(t : ℝ)) *
        ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) := by
  obtain ⟨b, hb, hbsmall, hrec⟩ :=
    c19_dyadic_point_recovery_from_gaussian_weight hlocal d hd D bmax hbmax
  refine ⟨b, hb, hbsmall, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν T t growth Kp A hT ht ht2 hz hg hK hA hpoint havg
  have ht1 : 1 ≤ (t : ℝ) := by linarith
  have h8lo : 1 ≤ ((t/8 : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith
  have h8hi : ((t/8 : ℝ≥0) : ℝ) ≤ T := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith
  have hu := hpoint (t/8) h8lo h8hi
  have hbt : 0 < b * (t : ℝ) := mul_pos hb (by linarith)
  exact hrec Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht1 (by linarith)
    growth Kp A hg hK hA (by simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hu)
    hbt (havg hbt)

end EinsteinFull.Blueprint
