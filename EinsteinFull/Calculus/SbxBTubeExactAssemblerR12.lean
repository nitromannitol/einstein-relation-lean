import EinsteinFull.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.Calculus.SbxBSpectralRowHarnackR14
import EinsteinFull.Calculus.SbxBContinuousDensityColumnDeltaR14
import EinsteinFull.Calculus.SbxBNativeFundamentalAssemblyR13
import EinsteinFull.Calculus.SbxBTubeMeasureAssemblerR01
import EinsteinFull.Calculus.SbxBNativeKernelComparisonR12
import EinsteinFull.Calculus.SbxBPrescribedHalfSurvivalR13
import EinsteinFull.Calculus.SbxBLocalizedDefectAssemblyR12

open MeasureTheory
open scoped NNReal ENNReal CompactlySupported
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP

/-- A pointwise lower bound on the native kernel gives the compact-test
inequality for the actual killed row at every interior starting point. -/
theorem b_actual_native_compact_test_of_pointwise
    (c m : ℝ) (hc : 0 < c) (hm : 0 < m)
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (y : Vec d) (hy : y ∈ sourceBall 0 R)
    (V : Set (Vec d)) (hV : MeasurableSet V) (hsub : V ⊆ sourceBall 0 R)
    (hlower : ∀ x ∈ V, c * Real.rpow (t : ℝ) (-(d : ℝ)/2) ≤ K t x y / ρ y)
    (hrho : ∀ x ∈ V, m ≤ ρ x)
    (f : C_c(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x) (hfV : tsupport f ⊆ V) :
    (m * c * Real.rpow (t : ℝ) (-(d : ℝ)/2)) * ∫ x, f x ∂(volume : Measure (Vec d)) ≤
      ∫ x, f x ∂gmpKilledEndpointKernel r (sourceBall 0 R)
        (dirichletBall (d := d) R).isOpen t y := by
  let ν := gmpKilledEndpointKernel r (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t y
  letI := isFiniteKernel_gmpKilledEndpointKernel r (sourceBall 0 R)
    (dirichletBall (d := d) R).isOpen t
  have hmeasure := b_actual_native_setwise_lower_of_pointwise c m hc hm r hκ hR hell hcoeff
    hK t ht y hy V hV hsub hlower hrho
  have hcomp := integral_mono_measure hmeasure (ae_of_all _ hf) f.integrable
  have hsupp : V.indicator (fun x => f x) = fun x => f x := by
    funext x
    by_cases hx : x ∈ V
    · simp [hx]
    · have hx' : x ∉ tsupport f := fun h => hx (hfV h)
      simp [hx, image_eq_zero_of_notMem_tsupport hx']
  have hrest : (∫ x in V, f x ∂(volume : Measure (Vec d))) = ∫ x, f x ∂(volume : Measure (Vec d)) := by
    rw [← integral_indicator hV, hsupp]
  have hnonneg : 0 ≤ m * c * Real.rpow (t : ℝ) (-(d : ℝ)/2) :=
    (mul_pos (mul_pos hm hc) (Real.rpow_pos_of_pos ht _)).le
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hnonneg, smul_eq_mul, hrest] using hcomp

/-- Capped convolution gives an actual killed-row compact-test bound at the
full prescribed time. The two short-time inputs remain separate and literal. -/
theorem b_actual_capped_compact_test
    (d : ℕ) (hd : 2 ≤ d) (κ δ H S T : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hS : 0 < S) (hT : 0 < T) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (R lam : ℝ),
    0 < R → ∀ (h0 : 0 < lam) (h1 : lam ≤ 1), S = lam * R →
    ∀ (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω),
    ∀ (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0.le h1),
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    (∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x) →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ (x : Vec d), x ∈ sourceBall 0 (S/2) → lam⁻¹ • x ∈ sourceBall 0 R →
    ∀ (V : Set (Vec d)), MeasurableSet V → V ⊆ sourceBall 0 R →
      (∀ z ∈ V, lam • z ∈ sourceBall 0 (S/2)) →
    ∀ f : C_c(Vec d, ℝ), (∀ z, 0 ≤ f z) → tsupport f ⊆ V →
      (cstar * lam^d) * ∫ z, f z ∂(volume : Measure (Vec d)) ≤
        ∫ z, f z ∂gmpKilledEndpointKernel r (sourceBall 0 R)
          (dirichletBall (d := d) R).isOpen (T / lam^2).toNNReal (lam⁻¹ • x) := by
  obtain ⟨a, ha, hbound⟩ := Calculus.b_source_oriented_capped_fixed_time_lower
    d hd κ δ H S T hκ hδ hH hS hT
  refine ⟨κ * a, mul_pos hκ ha, ?_⟩
  intro R lam hR hlam hle hSR L hL ω hω r ρ α hell hcoeff K G hK hmass hcomp x hx hy V hV hsub hscaled f hf hfV
  have ht : 0 < T / lam^2 := div_pos hT (sq_pos_of_pos hlam)
  have ht' : 0 < (((T / lam^2).toNNReal : ℝ≥0) : ℝ) := by simpa [Real.coe_toNNReal _ ht.le] using ht
  let b : ℝ := a * lam^d / Real.rpow (T / lam^2) (-(d : ℝ)/2)
  have hb : 0 < b := div_pos (mul_pos ha (pow_pos hlam _)) (Real.rpow_pos_of_pos ht _)
  have hlower : ∀ z ∈ V, b * Real.rpow ((T / lam^2).toNNReal : ℝ) (-(d : ℝ)/2) ≤
      K (T / lam^2).toNNReal z (lam⁻¹ • x) / ρ (lam⁻¹ • x) := by
    intro z hz
    have hh := hbound R lam hR hlam hSR ρ α hell K G hK hmass hcomp x hx (lam • z) (hscaled z hz)
    have heq : lam⁻¹ • (lam • z) = z := by simp [smul_smul, hlam.ne']
    rw [heq] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (pow_nonneg hlam.le d)
    have hpow : lam ^ d ≠ 0 := pow_ne_zero _ hlam.ne'
    have he : lam ^ d * ((lam⁻¹)^d * K (T / lam^2) z (lam⁻¹ • x) / ρ (lam⁻¹ • x)) =
        K (T / lam^2) z (lam⁻¹ • x) / ρ (lam⁻¹ • x) := by
      rw [inv_pow]; field_simp
    rw [he] at hh'
    have hrp : Real.rpow (T / lam^2) (-(d : ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
    simpa only [Real.coe_toNNReal _ ht.le, b, div_mul_cancel₀ _ hrp, mul_comm] using hh'
  have htest := b_actual_native_compact_test_of_pointwise b κ hb hκ r hκ hR hell hcoeff hK
    (T / lam^2).toNNReal ht' (lam⁻¹ • x) hy V hV hsub hlower
    (fun z _ => (hell.2.2 z).1) f hf hfV
  have hrp : Real.rpow (T / lam^2) (-(d : ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  rw [Real.coe_toNNReal _ ht.le] at htest
  have heq : κ * b * Real.rpow (T / lam^2) (-(d : ℝ)/2) = κ * a * lam^d := by
    dsimp only [b]
    calc
      κ * (a * lam^d / Real.rpow (T / lam^2) (-(d : ℝ)/2)) *
          Real.rpow (T / lam^2) (-(d : ℝ)/2) =
        κ * ((a * lam^d / Real.rpow (T / lam^2) (-(d : ℝ)/2)) *
          Real.rpow (T / lam^2) (-(d : ℝ)/2)) := by ring
      _ = κ * a * lam^d := by rw [div_mul_cancel₀ _ hrp]; ring
  rw [heq] at htest
  exact htest

/-- Compact tests for a translated actual killed row transport back to the
original realization, with the same Lebesgue constant. -/
theorem b_actual_compact_test_translate {d : ℕ} (hd : 2 ≤ d)
    (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (z : Vec d)
    (hωz : IsRegular L (translate z ω))
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (s : GantertFixedEnvironmentRealization hd L hL (translate z ω) hωz lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (V : Set (Vec d)) (t : ℝ≥0) (x : Vec d)
    (c : ℝ)
    (htest : ∀ g : C_c(Vec d, ℝ), (∀ y, 0 ≤ g y) →
      tsupport g ⊆ (fun y : Vec d => y + z) ⁻¹' V →
      c * ∫ y, g y ∂(volume : Measure (Vec d)) ≤
        ∫ y, g y ∂gmpKilledEndpointKernel s ((fun y : Vec d => y + z) ⁻¹' U)
          (hU.preimage (continuous_id.add continuous_const)) t x)
    (f : C_c(Vec d, ℝ)) (hf : ∀ y, 0 ≤ f y) (hfV : tsupport f ⊆ V) :
    c * ∫ y, f y ∂(volume : Measure (Vec d)) ≤
      ∫ y, f y ∂gmpKilledEndpointKernel r U hU t (x + z) := by
  let e : Vec d ≃ₜ Vec d := Homeomorph.addRight z
  let g : C_c(Vec d, ℝ) := ⟨⟨fun y => f (y + z), f.continuous.comp e.continuous⟩,
    f.hasCompactSupport.comp_homeomorph e⟩
  have hgV : tsupport g ⊆ (fun y : Vec d => y + z) ⁻¹' V := by
    change tsupport (f ∘ e) ⊆ _
    rw [tsupport_comp_eq_preimage f e]
    exact Set.preimage_mono hfV
  have hg := htest g (fun y => hf (y + z)) hgV
  have hvol : (∫ y, g y ∂(volume : Measure (Vec d))) = ∫ y, f y ∂volume := by
    change (∫ y, f (y + z) ∂(volume : Measure (Vec d))) = _
    have hm : Measurable (fun y : Vec d => y + z) := (continuous_id.add continuous_const).measurable
    calc
      _ = ∫ y, f y ∂Measure.map (fun y : Vec d => y + z) volume := by
        symm
        exact integral_map hm.aemeasurable f.continuous.aestronglyMeasurable
      _ = _ := by rw [map_add_right_eq_self]
  have hrow := s4_supplied_killed_endpoint_translation hd L hL ω hω lam h0 h1 z hωz r s U hU t x
  have hm : Measurable (fun y : Vec d => y - z) := (continuous_id.sub continuous_const).measurable
  rw [hvol, hrow] at hg
  have hi : (∫ y, g y ∂Measure.map (fun y : Vec d => y - z)
      (gmpKilledEndpointKernel r U hU t (x + z))) =
      ∫ y, g (y - z) ∂gmpKilledEndpointKernel r U hU t (x + z) :=
    integral_map hm.aemeasurable g.continuous.aestronglyMeasurable
  rw [hi] at hg
  change c * ∫ y, f y ∂(volume : Measure (Vec d)) ≤
    ∫ y, f ((y - z) + z) ∂gmpKilledEndpointKernel r U hU t (x + z) at hg
  simpa only [sub_add_cancel] using hg

/-- The capped estimate holds on every translated ball for the original
actual realization, under the two literal native short-time estimates. -/
theorem b_actual_translated_capped_compact_test
    (d : ℕ) (hd : 2 ≤ d) (κ δ H S T : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hS : 0 < S) (hT : 0 < T) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (R lam : ℝ),
    0 < R → ∀ (h0 : 0 < lam) (h1 : lam ≤ 1), S = lam * R →
    ∀ (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω)
      (z : Vec d) (hωz : IsRegular L (translate z ω))
      (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0.le h1)
      (s : GantertFixedEnvironmentRealization hd L hL (translate z ω) hωz lam h0.le h1),
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    (∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd (translate z ω) lam x ∧
      α x = s4PhysicalAlpha hd (translate z ω) lam x) →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ (x : Vec d), x ∈ sourceBall 0 (S/2) → lam⁻¹ • x ∈ sourceBall 0 R →
    ∀ (V : Set (Vec d)), MeasurableSet V → V ⊆ sourceBall 0 R →
      (∀ y ∈ V, lam • y ∈ sourceBall 0 (S/2)) →
    ∀ f : C_c(Vec d, ℝ), (∀ y, 0 ≤ f y) →
      tsupport f ⊆ (fun y : Vec d => y - z) ⁻¹' V →
      (cstar * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) ≤
        ∫ y, f y ∂gmpKilledEndpointKernel r
          ((fun y : Vec d => y - z) ⁻¹' sourceBall 0 R)
          ((dirichletBall (d := d) R).isOpen.preimage (continuous_id.sub continuous_const))
          (T / lam^2).toNNReal (lam⁻¹ • x + z) := by
  obtain ⟨cstar, hc, hbound⟩ := b_actual_capped_compact_test d hd κ δ H S T hκ hδ hH hS hT
  refine ⟨cstar, hc, ?_⟩
  intro R lam hR hlam hle hSR L hL ω hω z hωz r s ρ α hell hcoeff K G hK hmass hcomp x hx hy V hV hsub hscaled f hf hfV
  let U : Set (Vec d) := (fun y : Vec d => y - z) ⁻¹' sourceBall 0 R
  have hU : IsOpen U := (dirichletBall (d := d) R).isOpen.preimage (continuous_id.sub continuous_const)
  have hpre : (fun y : Vec d => y + z) ⁻¹' U = sourceBall 0 R := by
    ext y
    simp [U]
  have hpreV : (fun y : Vec d => y + z) ⁻¹' ((fun y : Vec d => y - z) ⁻¹' V) = V := by
    ext y
    simp
  apply b_actual_compact_test_translate hd L hL ω hω lam hlam.le hle z hωz r s U hU
    ((fun y : Vec d => y - z) ⁻¹' V) _ (lam⁻¹ • x) _ ?_ f hf hfV
  intro g hg hgV
  rw [hpreV] at hgV
  have hb := hbound R lam hR hlam hle hSR L hL (translate z ω) hωz s ρ α hell hcoeff
    K G hK hmass hcomp x hx hy V hV hsub hscaled g hg hgV
  simpa only [hpre] using hb

/-- The prescribed successive endpoint windows lie in the inner half of the
centered killed ball, both before and after physical force scaling. -/
theorem b_renewal_window_centered_geometry {d : ℕ}
    (eps lam : ℝ) (heps : 0 < eps) (hlam : 0 < lam)
    (c₀ c₁ x y : Vec d)
    (hstep : euclideanNorm (c₁ - c₀) ≤ eps / 16)
    (hx : euclideanNorm (x - c₀) < eps / 16)
    (hy : euclideanNorm (y - c₁) < eps / 16) :
    x - c₀ ∈ sourceBall 0 ((eps/2)/2) ∧
    lam⁻¹ • (x - c₀) ∈ sourceBall 0 ((eps/2)/lam) ∧
    y - c₀ ∈ sourceBall 0 ((eps/2)/2) ∧
    lam⁻¹ • (y - c₀) ∈ sourceBall 0 ((eps/2)/lam) := by
  have htri := TimeChange.euclideanNorm_add_le (y - c₁) (c₁ - c₀)
  simp only [sub_add_sub_cancel] at htri
  have hy' : euclideanNorm (y - c₀) < eps / 4 := by linarith
  have hx' : euclideanNorm (x - c₀) < eps / 4 := by linarith
  have hscale (v : Vec d) (hv : euclideanNorm v < eps / 4) :
      lam⁻¹ • v ∈ sourceBall 0 ((eps/2)/lam) := by
    change euclideanNorm (lam⁻¹ • v - 0) < (eps/2)/lam
    rw [sub_zero, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hlam)]
    rw [← div_eq_inv_mul]
    exact (div_lt_div_iff_of_pos_right hlam).2 (by linarith)
  refine ⟨?_, hscale _ hx', ?_, hscale _ hy'⟩
  all_goals
    change euclideanNorm (_ - 0) < (eps/2)/2
    simp only [sub_zero]
    linarith

/-- The physical translated ball is exactly the scaled renewal tube ball. -/
theorem b_renewal_physical_ball {d : ℕ} (eps lam : ℝ) (hlam : 0 < lam)
    (c : Vec d) :
    (fun y : Vec d => y - lam⁻¹ • c) ⁻¹' sourceBall 0 ((eps/2)/lam) =
      (fun y : Vec d => lam • y) ⁻¹' {y | euclideanNorm (y-c) < eps/2} := by
  ext y
  change euclideanNorm ((y - lam⁻¹ • c) - 0) < (eps/2)/lam ↔
    euclideanNorm (lam • y - c) < eps/2
  have heq : lam • (y - lam⁻¹ • c) = lam • y - c := by
    simp [smul_sub, smul_smul, hlam.ne']
  rw [sub_zero, ← heq, TimeChange.euclideanNorm_smul, abs_of_pos hlam]
  rw [mul_comm lam (euclideanNorm (y - lam⁻¹ • c)), ← lt_div_iff₀ hlam]

private theorem b_renewal_scaled_ball_isOpen {d : ℕ} (eps lam : ℝ) (c : Vec d) :
    IsOpen ((fun y : Vec d => lam • y) ⁻¹' {y | euclideanNorm (y-c) < eps/2}) := by
  have ho : IsOpen {y : Vec d | euclideanNorm (y-c) < eps/2} :=
    isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const
  have hs : Continuous (fun y : Vec d => lam • y) :=
    (continuous_const : Continuous (fun _ : Vec d => lam)).smul continuous_id
  exact ho.preimage hs

/-- Full-time actual killed-row tests on a prescribed renewal mesh piece. -/
theorem b_renewal_piece_compact_test
    (d : ℕ) (hd : 2 ≤ d) (κ δ H eps T : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (heps : 0 < eps) (hT : 0 < T) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1),
    ∀ (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω)
      (c₀ c₁ : Vec d) (hωz : IsRegular L (translate (lam⁻¹ • c₀) ω))
      (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0.le h1)
      (s : GantertFixedEnvironmentRealization hd L hL (translate (lam⁻¹ • c₀) ω) hωz lam h0.le h1),
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    (∀ x ∈ sourceBall (0 : Vec d) ((eps/2)/lam),
      ρ x = s4PhysicalRho hd (translate (lam⁻¹ • c₀) ω) lam x ∧
      α x = s4PhysicalAlpha hd (translate (lam⁻¹ • c₀) ω) lam x) →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α ((eps/2)/lam) K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 ((eps/2)/lam) →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 ((eps/2)/lam), K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 ((eps/2)/lam) →
      y ∈ sourceBall 0 ((eps/2)/lam) → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    euclideanNorm (c₁-c₀) ≤ eps/16 → ∀ x : Vec d,
      euclideanNorm (x-c₀) < eps/16 → ∀ f : C_c(Vec d, ℝ), (∀ y, 0 ≤ f y) →
      tsupport f ⊆ (fun y : Vec d => lam • y) ⁻¹'
        {y | euclideanNorm (y-c₁) < eps/16} →
      (cstar * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) ≤
        ∫ y, f y ∂gmpKilledEndpointKernel r
          ((fun y : Vec d => lam • y) ⁻¹' {y | euclideanNorm (y-c₀) < eps/2})
          (b_renewal_scaled_ball_isOpen eps lam c₀)
          (T/lam^2).toNNReal (lam⁻¹ • x) := by
  obtain ⟨cstar, hc, hbound⟩ := b_actual_translated_capped_compact_test
    d hd κ δ H (eps/2) T hκ hδ hH (by positivity) hT
  refine ⟨cstar, hc, ?_⟩
  intro lam hlam hle L hL ω hω c₀ c₁ hωz r s ρ α hell hcoeff K G hK hmass hcomp hstep x hx f hf hfV
  let z : Vec d := lam⁻¹ • c₀
  let V : Set (Vec d) := {y | euclideanNorm (lam • y + c₀ - c₁) < eps/16}
  have hV : MeasurableSet V := by
    apply IsOpen.measurableSet
    have hs : Continuous (fun y : Vec d => lam • y) :=
      (continuous_const : Continuous (fun _ : Vec d => lam)).smul continuous_id
    exact isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      ((hs.add continuous_const).sub continuous_const)) continuous_const
  have hrelative (y : Vec d) : lam⁻¹ • (lam • y + c₀ - c₀) = y := by
    simp [smul_smul, hlam.ne']
  have hinside (y : Vec d) (hy : y ∈ V) :
      y ∈ sourceBall 0 ((eps/2)/lam) ∧ lam • y ∈ sourceBall 0 ((eps/2)/2) := by
    have hy' : euclideanNorm ((lam • y + c₀) - c₁) < eps/16 := hy
    have hg := b_renewal_window_centered_geometry eps lam heps hlam c₀ c₁ x (lam • y + c₀) hstep hx hy'
    constructor
    · simpa only [hrelative] using hg.2.2.2
    · simpa only [add_sub_cancel_right] using hg.2.2.1
  have hstart := b_renewal_window_centered_geometry eps lam heps hlam c₀ c₁ x c₁ hstep hx (by
    simp only [sub_self, euclideanNorm, euclideanSq, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
    positivity)
  have hfV' : tsupport f ⊆ (fun y : Vec d => y-z) ⁻¹' V := by
    intro y hy
    have hy' := hfV hy
    change euclideanNorm (lam • y - c₁) < eps/16 at hy'
    change euclideanNorm (lam • (y-z) + c₀ - c₁) < eps/16
    have heq : lam • (y-z) + c₀ = lam • y := by
      dsimp [z]
      simp [smul_sub, smul_smul, hlam.ne']
    simpa only [heq] using hy'
  have hh := hbound ((eps/2)/lam) lam (div_pos (by positivity) hlam) hlam hle
    (by field_simp) L hL ω hω z hωz r s ρ α hell hcoeff K G hK hmass hcomp
    (x-c₀) hstart.1 hstart.2.1 V hV (fun y hy => (hinside y hy).1)
    (fun y hy => (hinside y hy).2) f hf hfV'
  have hstartEq : lam⁻¹ • (x-c₀) + z = lam⁻¹ • x := by
    dsimp [z]
    simp [smul_sub]
  simpa only [hstartEq, z, b_renewal_physical_ball eps lam hlam c₀] using hh

/-- Uniform elliptic extensions of the actual translated reduced coefficients. -/
@[nolint defsWithUnderscore]
def b_renewal_coefficient_extension (d : ℕ) (hd : 2 ≤ d)
    (L B eps κ : ℝ) : Prop :=
  ∀ (ω : FieldPair d), IsRegular (sourceReducedBound L) (zeroPotentialReducedPair ω) →
  ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ c : Vec d, euclideanNorm c < B →
  ∃ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α ∧
    ∀ x ∈ sourceBall (0 : Vec d) ((eps/2)/lam),
      ρ x = s4PhysicalRho hd (translate (lam⁻¹ • c) (zeroPotentialReducedPair ω)) lam x ∧
      α x = s4PhysicalAlpha hd (translate (lam⁻¹ • c) (zeroPotentialReducedPair ω)) lam x

/-- Uniform elliptic extensions with their actual continuous density. -/
@[nolint defsWithUnderscore]
def b_renewal_continuous_coefficient_extension (d : ℕ) (hd : 2 ≤ d)
    (L B eps κ : ℝ) : Prop :=
  ∀ (ω : FieldPair d), IsRegular (sourceReducedBound L) (zeroPotentialReducedPair ω) →
  ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ c : Vec d, euclideanNorm c < B →
  ∃ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α ∧
    Continuous ρ ∧ ∀ x ∈ sourceBall (0 : Vec d) ((eps/2)/lam),
      ρ x = s4PhysicalRho hd (translate (lam⁻¹ • c) (zeroPotentialReducedPair ω)) lam x ∧
      α x = s4PhysicalAlpha hd (translate (lam⁻¹ • c) (zeroPotentialReducedPair ω)) lam x

/-- The translated zero-potential field admits an explicit bounded extension. -/
theorem b_renewal_continuous_coefficient_extension_of_regular_bound
    (d : ℕ) (hd : 2 ≤ d) (L B eps : ℝ) (heps : 0 < eps) :
    ∃ κ, 0 < κ ∧ b_renewal_continuous_coefficient_extension d hd L B eps κ := by
  let D := eps / 2
  let M := max 1 (sourceReducedBound L)
  let κ := Regeneration.boundedForceKappa M D
  have hL' : 1 ≤ M := le_max_left _ _
  have hLpos : 0 < sourceReducedBound L := by
    unfold sourceReducedBound
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg (L + 1/6)]
  have hLM : sourceReducedBound L ≤ M := le_max_right _ _
  refine ⟨κ, Regeneration.boundedForceKappa_pos hL', ?_⟩
  intro ω hω lam hlam hle c hc
  let η := translate (lam⁻¹ • c) (zeroPotentialReducedPair ω)
  have hωM : IsRegular M (zeroPotentialReducedPair ω) := by
    rcases hω with ⟨hell, hpot, hlip, hpotlip⟩
    refine ⟨?_, fun x => (hpot x).trans hLM, ?_, ?_⟩
    · intro x
      refine ⟨(hell x).1, fun v => ⟨?_, ?_⟩⟩
      · exact (mul_le_mul_of_nonneg_right (inv_anti₀ hLpos hLM)
          (euclideanSq_nonneg_coords v)).trans ((hell x).2 v).1
      · exact ((hell x).2 v).2.trans (mul_le_mul_of_nonneg_right hLM
          (euclideanSq_nonneg_coords v))
    · intro x y v
      exact (hlip x y v).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    · intro x y
      exact (hpotlip x y).trans (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _))
  have hη : IsRegular M η :=
    (ActualImageLpStateTransport.isRegular_translate_iff _ _).mpr hωM
  let i := firstCoordinateIndex hd
  let ρ := Regeneration.boundedForceDensity D i
  let α := Regeneration.boundedForceCoefficient η D i lam
  have hell := Regeneration.boundedForceCoefficient_elliptic hL'
    (show 0 ≤ D by dsimp [D]; positivity) η hη i lam
  have hscale : Measurable (fun x : Vec d => lam • x) :=
    (continuous_id.const_smul lam).measurable
  refine ⟨fun x => ρ (lam • x), fun x => α (lam • x),
    ⟨hell.1.comp hscale, hell.2.1.comp hscale, fun x => hell.2.2 (lam • x)⟩,
    (Regeneration.continuous_boundedForceDensity D i).comp (continuous_id.const_smul lam), ?_⟩
  intro x hx
  have hx' : euclideanNorm (lam • x) ≤ D := by
    change euclideanNorm (x - 0) < (eps / 2) / lam at hx
    rw [sub_zero] at hx
    rw [TimeChange.euclideanNorm_smul, abs_of_pos hlam]
    dsimp [D]
    have h := (lt_div_iff₀ hlam).mp hx
    nlinarith
  have hρ : ρ (lam • x) = Real.exp (2 * lam * x i) := by
    rw [show ρ = Regeneration.boundedForceDensity D i from rfl,
      Regeneration.boundedForceDensity_eq i _ hx']
    simp [mul_assoc]
  have hηzero (y : Vec d) : η.2 y = 0 := by simp [η]
  have hρphys : s4PhysicalRho hd η lam x = Real.exp (2 * lam * x i) := by
    rw [s4PhysicalRho, physicalReversibleDensity_eq_source_formula, hηzero]
    simp [i]
  constructor
  · exact hρ.trans hρphys.symm
  · dsimp [α, Regeneration.boundedForceCoefficient]
    rw [show Regeneration.boundedForceDensity D i (lam • x) = ρ (lam • x) from rfl,
      hρ]
    have hpoint : lam⁻¹ • (lam • x) = x := by simp [smul_smul, hlam.ne']
    rw [hpoint]
    simp only [reducedCoefficient, clockDensity, hηzero, mul_zero, Real.exp_zero, one_smul]
    rw [s4PhysicalAlpha, hρphys]
    congr 1 <;> ring

/-- The translated zero-potential field admits an explicit bounded extension. -/
theorem b_renewal_coefficient_extension_of_regular_bound
    (d : ℕ) (hd : 2 ≤ d) (L B eps : ℝ) (heps : 0 < eps) :
    ∃ κ, 0 < κ ∧ b_renewal_coefficient_extension d hd L B eps κ := by
  obtain ⟨κ, hκ, hext⟩ :=
    b_renewal_continuous_coefficient_extension_of_regular_bound d hd L B eps heps
  refine ⟨κ, hκ, ?_⟩
  intro ω hω lam hlam hle c hc
  obtain ⟨ρ, α, hell, _, hcoeff⟩ := hext ω hω lam hlam hle c hc
  exact ⟨ρ, α, hell, hcoeff⟩

/-- Existence of the native spectral Dirichlet kernel. -/
@[nolint defsWithUnderscore]
def b_renewal_spectral_existence (d : ℕ) (κ : ℝ) : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∃ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G

/-- Native spectral existence for continuous density representatives. -/
@[nolint defsWithUnderscore]
def b_renewal_continuous_spectral_existence (d : ℕ) (κ : ℝ) : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → Continuous ρ →
    ∃ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G

/-- Native short-time survival in a ball. -/
@[nolint defsWithUnderscore]
def b_renewal_native_half_survival (d : ℕ) (κ δ : ℝ) : Prop :=
  ∀ (R : ℝ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsUniformlyElliptic κ ρ α → IsSpectralDirichletFundamentalSolution ρ α R K G →
    ∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y

/-- The localized exponential defect used to obtain prescribed-start survival. -/
@[nolint defsWithUnderscore]
def b_renewal_exponential_defect (d : ℕ) (κ : ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧
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
        ≤ D * T * r^d * Real.exp (-(r^2 / (D*T)))

/-- The native spectral cutoff has the required exponential defect. -/
theorem b_renewal_exponential_defect_of_ellipticity
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    b_renewal_exponential_defect d κ := by
  obtain ⟨D, hD, hdefect⟩ := Calculus.br12_native_cutoff_localized_spacetime hd hκ
  refine ⟨D, hD, ?_⟩
  intro R hR ρ α hell s x r hr hinside φ hφ hsupp hbounds hplateau hgrad T hT hTr
  have hsum : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) := by
    intro t ht x hx y hy
    exact Blueprint.SbxS3UniformCrossHeat.spectral_heat_cross_summable_closedBall
      hd hκ hell hR s t ht x y (subset_closure hx) (subset_closure hy)
  have hsmall : sourceBall x (r/2) ⊆ sourceBall (0 : Vec d) R := by
    intro z hz
    apply hinside
    change euclideanNorm (z-x) < r/2 at hz
    change euclideanNorm (z-x) < 2*r
    linarith
  exact hdefect ρ α hell R hR s hsum x r hr hsmall φ hφ hbounds hplateau
    hsupp hgrad T hT hTr

/-- The exponential defect yields native short-time survival. -/
theorem b_renewal_native_half_survival_of_exponential_defect
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ)
    (hdecay : b_renewal_exponential_defect d κ) :
    ∃ δ, 0 < δ ∧ b_renewal_native_half_survival d κ δ := by
  obtain ⟨δ, hδ, hmass⟩ :=
    Calculus.b_prescribed_half_survival_of_exponential_defect d hd κ hκ hdecay
  refine ⟨δ, hδ, ?_⟩
  intro R ρ α K G hell hK x r u hr hball hu hut
  have hx : x ∈ sourceBall (0 : Vec d) R := hball (by
    change euclideanNorm (x-x) < 2*r
    simpa [euclideanNorm, euclideanSq, dot] using (show 0 < 2*r by positivity))
  have hR : 0 < R := by
    change euclideanNorm (x-0) < R at hx
    exact (show 0 ≤ euclideanNorm (x-0) from Real.sqrt_nonneg _).trans_lt hx
  exact hmass R hR ρ α hell K G hK x r hr hball u hu hut

/-- Uniform native half-survival for every prescribed starting point. -/
theorem b_renewal_native_half_survival_of_ellipticity
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ δ, 0 < δ ∧ b_renewal_native_half_survival d κ δ :=
  b_renewal_native_half_survival_of_exponential_defect d hd κ hκ
    (b_renewal_exponential_defect_of_ellipticity d hd κ hκ)

/-- Native pointwise kernel Harnack comparison. -/
@[nolint defsWithUnderscore]
def b_renewal_native_harnack (d : ℕ) (κ δ H : ℝ) : Prop :=
  ∀ (R : ℝ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsUniformlyElliptic κ ρ α → IsSpectralDirichletFundamentalSolution ρ α R K G →
    ∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)

/-- A local pointwise comparison gives the native kernel comparison through a
finite parabolic chain. -/
theorem b_renewal_native_harnack_of_scaled_unit
    (d : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hh : Calculus.BScaledUnitPointwiseHarnack d κ) :
    ∃ δ H, 0 < δ ∧ 0 < H ∧ b_renewal_native_harnack d κ δ H := by
  obtain ⟨H, hH, hchain⟩ :=
    Calculus.b_shifted_pointwise_harnack_of_scaled_unit d κ 1 0 (by norm_num)
      (by norm_num) hh
  refine ⟨1/16, H, by norm_num, hH, ?_⟩
  intro R ρ α K G hell hK x y r u hr hball hy hu hut hdist
  have hx : x ∈ sourceBall (0 : Vec d) R := hball (by
    change euclideanNorm (x-x) < 2*r
    simpa [euclideanNorm, euclideanSq, dot] using (show 0 < 2*r by positivity))
  have hR : 0 < R := by
    change euclideanNorm (x-0) < R at hx
    exact (show 0 ≤ euclideanNorm (x-0) from Real.sqrt_nonneg _).trans_lt hx
  have hdist' : euclideanNorm (y-x)^2 ≤ u := by
    rw [show y-x = -(x-y) by abel, Entropy.euclideanNorm_neg',
      ← TimeChange.euclideanSq_eq_sq_euclideanNorm]
    exact hdist
  have hsq : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hsq2 : (Real.sqrt u)^2 = u := Real.sq_sqrt hu.le
  have hsq4 : Real.sqrt (4*u) = 2*Real.sqrt u := by
    have h1 : 0 ≤ Real.sqrt (4*u) := Real.sqrt_nonneg _
    have h2 : (Real.sqrt (4*u))^2 = 4*u := Real.sq_sqrt (by positivity)
    nlinarith
  have hnorm : 0 ≤ euclideanNorm (y-x) := Real.sqrt_nonneg _
  have hdist'' : euclideanNorm (y-x) ≤ Real.sqrt u := by nlinarith
  have hmargin : euclideanNorm (y-x) + 3*Real.sqrt (4*u) ≤ 2*r := by
    rw [hsq4]
    nlinarith [sq_nonneg (r - 4*Real.sqrt u)]
  have hball' : sourceBall y ((1+0+2)*Real.sqrt (4*u)) ⊆ sourceBall 0 R := by
    intro z hz
    apply hball
    change euclideanNorm (z-x) < 2*r
    change euclideanNorm (z-y) < (1+0+2)*Real.sqrt (4*u) at hz
    have htri := TimeChange.euclideanNorm_add_le (z-y) (y-x)
    have heq : z-x = (z-y)+(y-x) := by ext i; simp
    rw [heq]
    nlinarith
  let v : ℝ × Vec d → ℝ := fun p => K (u+p.1) p.2 x
  let F : ℝ × Vec d → Vec d := fun p => G (u+p.1) p.2 x
  have hc : IsWeightedCaloric ρ α (Set.Ioo 0 (2*(4*u))) (sourceBall 0 R) v F := by
    have hhcal := (hK.1 x hx).2.2.2.1 u (9*u) hu (by linarith)
    have hc' := Calculus.c18_weighted_caloric_time_translate ρ α 0 (8*u) u
      (sourceBall 0 R) (fun p => K p.1 p.2 x) (fun p => G p.1 p.2 x) (by
        convert hhcal.1 using 1 <;> congr 1 <;> ring)
    convert hc' using 1 <;> try { congr 1 <;> ring }
  have hcont : ContinuousOn v (Set.Ioo 0 (2*(4*u)) ×ˢ sourceBall 0 R) := by
    have hcmap : ContinuousOn (fun p : ℝ × Vec d => (u+p.1,p.2))
        (Set.Ioo 0 (2*(4*u)) ×ˢ sourceBall 0 R) :=
      ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
    have hmaps : Set.MapsTo (fun p : ℝ × Vec d => (u+p.1,p.2))
        (Set.Ioo 0 (2*(4*u)) ×ˢ sourceBall 0 R)
        (Set.Ioi 0 ×ˢ closure (sourceBall (0 : Vec d) R)) := by
      intro p hp
      exact ⟨by change 0 < u+p.1; linarith [hp.1.1], subset_closure hp.2⟩
    simpa [v, Function.comp_def] using (hK.1 x hx).1.comp hcmap hmaps
  have hnonneg : ∀ p ∈ Set.Ioo 0 (2*(4*u)) ×ˢ sourceBall 0 R, 0 ≤ v p := by
    intro p hp
    exact (hK.1 x hx).2.1 (u+p.1) (by linarith [hp.1.1]) p.2 hp.2
  have hxy : euclideanNorm (x-y) ≤ (1+0)*Real.sqrt (4*u) := by
    rw [show x-y = -(y-x) by abel, Entropy.euclideanNorm_neg', hsq4]
    nlinarith
  have h := hchain R hR ρ α hell (4*u) (by positivity) v F hc hcont hnonneg
    x hx y hy hball' hxy
  have hρx : 0 < ρ x := hκ.trans_le (hell.2.2 x).1
  have hρy : 0 < ρ y := hκ.trans_le (hell.2.2 y).1
  have hsym := hK.weighted_symmetry (show 0 < 4*u by positivity) hx hy
  have heq : K (4*u) y x / ρ x = K (4*u) x y / ρ y := by
    apply (div_eq_div_iff (ne_of_gt hρx) (ne_of_gt hρy)).2
    nlinarith [hsym]
  have h' : K (2*u) x x ≤ H * K (4*u) y x := by
    have ht1 : u + (4*u)/4 = 2*u := by ring
    have ht2 : u + 3*(4*u)/4 = 4*u := by ring
    simpa only [v, ht1, ht2] using h
  have hdiv := div_le_div_of_nonneg_right h' hρx.le
  rw [mul_div_assoc, heq] at hdiv
  exact hdiv

/-- Scaled cylinder Harnack supplies the native kernel comparison. -/
theorem b_renewal_native_harnack_of_scaled_harnack
    (d : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hh : Calculus.BScaledCylinderPointwiseHarnack d κ) :
    ∃ δ H, 0 < δ ∧ 0 < H ∧ b_renewal_native_harnack d κ δ H := by
  obtain ⟨δ, H, hδ, hH, hcomp⟩ :=
    Calculus.b_native_kernel_comparison_of_scaled_harnack d κ hκ hh
  refine ⟨δ, H, hδ, hH, ?_⟩
  intro R ρ α K G hell hK x y r u hr hball hy hu hut hdist
  have hx : x ∈ sourceBall (0 : Vec d) R := hball (by
    change euclideanNorm (x-x) < 2*r
    simpa [euclideanNorm, euclideanSq, dot] using (show 0 < 2*r by positivity))
  have hR : 0 < R := by
    change euclideanNorm (x-0) < R at hx
    exact (show 0 ≤ euclideanNorm (x-0) from Real.sqrt_nonneg _).trans_lt hx
  exact hcomp R hR ρ α hell K G hK x y r u hr hball hy hu hut hdist

/-- The exact tube statement follows from four displayed analytic inputs. -/
theorem b_tube_probability_of_native_inputs
    (hinputs : ∀ (d : ℕ) (hd : 2 ≤ d) (L r₀ l B : ℝ), 0 < l → 0 < B →
      ∃ κ δ H : ℝ, 0 < κ ∧ 0 < δ ∧ 0 < H ∧
        b_renewal_coefficient_extension d hd L B (l/32) κ ∧
        b_renewal_spectral_existence d κ ∧
        b_renewal_native_half_survival d κ δ ∧
        b_renewal_native_harnack d κ δ H) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt := by
  apply b_tube_probability_of_compact_row_testing
  dsimp only [bTubeCompactRowTestingInput]
  intro d hd L r₀ l hl B C N hB hC hN hgeom
  obtain ⟨κ, δ, H, hκ, hδ, hH, hext, hspectral, hmass, hharnack⟩ :=
    hinputs d hd L r₀ l B hl hB
  have heps : 0 < l/32 := by positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨c₂, hc₂, h₂⟩ := b_renewal_piece_compact_test d hd κ δ H (l/32) (1/N)
    hκ hδ hH heps (by positivity)
  obtain ⟨c₃, hc₃, h₃⟩ := b_renewal_piece_compact_test d hd κ δ H (l/32) (2/N)
    hκ hδ hH heps (by positivity)
  refine ⟨min c₂ c₃, lt_min hc₂ hc₃, ?_⟩
  intro Q lam h0 h1 P hP
  filter_upwards [hP] with ω hreal
  obtain ⟨hω, R, hrow⟩ := hreal
  intro j hj k hk x hx f hf hfV
  let h : ℝ := ((j : ℝ)-1)/N
  let γ₂ : ℝ → Vec d := fun u => min ((25*l/4)*u) (25*l/8) • unitVector (Regeneration.Renewal.forceCoord hd)
  let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u-1)
  let γ : ℕ → ℝ → Vec d := fun j => if j = 2 then γ₂ else γ₃
  let c : ℕ → Vec d := fun k => γ j ((k : ℝ)*h)
  have hkreal : (k : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hk)
  have htime : (k : ℝ)*h ≤ (j : ℝ)-1 := by
    have hh := (hgeom j hj).1
    have hn := (hgeom j hj).2.1
    have := mul_le_mul_of_nonneg_right hkreal hh.le
    linarith
  have hcB : euclideanNorm (c k) < B := by
    have hh := (hgeom j hj).2.2.1 ((k : ℝ)*h) (mul_nonneg (by positivity) (hgeom j hj).1.le) htime
    dsimp [c, γ, γ₂, γ₃, h] at *
    linarith
  have hstep : euclideanNorm (c (k+1)-c k) ≤ (l/32)/16 := by
    apply (hgeom j hj).2.2.2 k hk (((k+1 : ℕ) : ℝ)*h)
    · have : (k : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ k)
      exact mul_le_mul_of_nonneg_right this (hgeom j hj).1.le
    · rfl
  let η := zeroPotentialReducedPair ω
  let hωc : IsRegular (sourceReducedBound L) (translate (lam⁻¹ • c k) η) :=
    (ActualImageLpStateTransport.isRegular_translate_iff (lam⁻¹ • c k) η).mpr hω
  let S := Classical.choice (u5_regular_signed_fixed_environment_realization_exists
    hd (one_le_sourceReducedBound Q.ellipticity_parameter) (translate (lam⁻¹ • c k) η) hωc lam h0.le h1)
  obtain ⟨ρ, α, hell, hcoeff⟩ := hext ω hω lam h0 h1 (c k) hcB
  obtain ⟨K, G, hK⟩ := hspectral ((l/32/2)/lam) (by positivity) ρ α hell
  have hintegral : 0 ≤ ∫ y, f y ∂(volume : Measure (Vec d)) := integral_nonneg hf
  have hc₂' : (min c₂ c₃ * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) ≤
      (c₂ * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) := by gcongr; exact min_le_left _ _
  have hc₃' : (min c₂ c₃ * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) ≤
      (c₃ * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) := by gcongr; exact min_le_right _ _
  rcases hj with rfl | rfl
  · have hb := h₂ lam h0 h1 (sourceReducedBound L) (one_le_sourceReducedBound Q.ellipticity_parameter)
      η hω (c k) (c (k+1)) hωc R S ρ α hell hcoeff K G hK
      (hmass _ _ _ _ _ hell hK) (hharnack _ _ _ _ _ hell hK) hstep x hx f hf hfV
    have ht : h = 1/N := by dsimp [h]; norm_num
    simpa [gmpKilledEndpointKernel_apply, ← hrow, abs_of_pos h0, c, h, γ, γ₂, γ₃, show (2 : ℝ) - 1 = 1 by norm_num] using hc₂'.trans hb
  · have hb := h₃ lam h0 h1 (sourceReducedBound L) (one_le_sourceReducedBound Q.ellipticity_parameter)
      η hω (c k) (c (k+1)) hωc R S ρ α hell hcoeff K G hK
      (hmass _ _ _ _ _ hell hK) (hharnack _ _ _ _ _ hell hK) hstep x hx f hf hfV
    have ht : h = 2/N := by dsimp [h]; norm_num
    simpa [gmpKilledEndpointKernel_apply, ← hrow, abs_of_pos h0, c, h, γ, γ₂, γ₃, show (3 : ℝ) - 1 = 2 by norm_num] using hc₃'.trans hb

/-- The exact tube statement follows from four displayed analytic inputs. -/
theorem b_tube_probability_of_continuous_native_inputs
    (hinputs : ∀ (d : ℕ) (hd : 2 ≤ d) (L r₀ l B : ℝ), 0 < l → 0 < B →
      ∃ κ δ H : ℝ, 0 < κ ∧ 0 < δ ∧ 0 < H ∧
        b_renewal_continuous_coefficient_extension d hd L B (l/32) κ ∧
        b_renewal_continuous_spectral_existence d κ ∧
        b_renewal_native_half_survival d κ δ ∧
        b_renewal_native_harnack d κ δ H) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt := by
  apply b_tube_probability_of_compact_row_testing
  dsimp only [bTubeCompactRowTestingInput]
  intro d hd L r₀ l hl B C N hB hC hN hgeom
  obtain ⟨κ, δ, H, hκ, hδ, hH, hext, hspectral, hmass, hharnack⟩ :=
    hinputs d hd L r₀ l B hl hB
  have heps : 0 < l/32 := by positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨c₂, hc₂, h₂⟩ := b_renewal_piece_compact_test d hd κ δ H (l/32) (1/N)
    hκ hδ hH heps (by positivity)
  obtain ⟨c₃, hc₃, h₃⟩ := b_renewal_piece_compact_test d hd κ δ H (l/32) (2/N)
    hκ hδ hH heps (by positivity)
  refine ⟨min c₂ c₃, lt_min hc₂ hc₃, ?_⟩
  intro Q lam h0 h1 P hP
  filter_upwards [hP] with ω hreal
  obtain ⟨hω, R, hrow⟩ := hreal
  intro j hj k hk x hx f hf hfV
  let h : ℝ := ((j : ℝ)-1)/N
  let γ₂ : ℝ → Vec d := fun u => min ((25*l/4)*u) (25*l/8) • unitVector (Regeneration.Renewal.forceCoord hd)
  let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u-1)
  let γ : ℕ → ℝ → Vec d := fun j => if j = 2 then γ₂ else γ₃
  let c : ℕ → Vec d := fun k => γ j ((k : ℝ)*h)
  have hkreal : (k : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hk)
  have htime : (k : ℝ)*h ≤ (j : ℝ)-1 := by
    have hh := (hgeom j hj).1
    have hn := (hgeom j hj).2.1
    have := mul_le_mul_of_nonneg_right hkreal hh.le
    linarith
  have hcB : euclideanNorm (c k) < B := by
    have hh := (hgeom j hj).2.2.1 ((k : ℝ)*h) (mul_nonneg (by positivity) (hgeom j hj).1.le) htime
    dsimp [c, γ, γ₂, γ₃, h] at *
    linarith
  have hstep : euclideanNorm (c (k+1)-c k) ≤ (l/32)/16 := by
    apply (hgeom j hj).2.2.2 k hk (((k+1 : ℕ) : ℝ)*h)
    · have : (k : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ k)
      exact mul_le_mul_of_nonneg_right this (hgeom j hj).1.le
    · rfl
  let η := zeroPotentialReducedPair ω
  let hωc : IsRegular (sourceReducedBound L) (translate (lam⁻¹ • c k) η) :=
    (ActualImageLpStateTransport.isRegular_translate_iff (lam⁻¹ • c k) η).mpr hω
  let S := Classical.choice (u5_regular_signed_fixed_environment_realization_exists
    hd (one_le_sourceReducedBound Q.ellipticity_parameter) (translate (lam⁻¹ • c k) η) hωc lam h0.le h1)
  obtain ⟨ρ, α, hell, hcont, hcoeff⟩ := hext ω hω lam h0 h1 (c k) hcB
  obtain ⟨K, G, hK⟩ := hspectral ((l/32/2)/lam) (by positivity) ρ α hell hcont
  have hintegral : 0 ≤ ∫ y, f y ∂(volume : Measure (Vec d)) := integral_nonneg hf
  have hc₂' : (min c₂ c₃ * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) ≤
      (c₂ * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) := by gcongr; exact min_le_left _ _
  have hc₃' : (min c₂ c₃ * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) ≤
      (c₃ * lam^d) * ∫ y, f y ∂(volume : Measure (Vec d)) := by gcongr; exact min_le_right _ _
  rcases hj with rfl | rfl
  · have hb := h₂ lam h0 h1 (sourceReducedBound L) (one_le_sourceReducedBound Q.ellipticity_parameter)
      η hω (c k) (c (k+1)) hωc R S ρ α hell hcoeff K G hK
      (hmass _ _ _ _ _ hell hK) (hharnack _ _ _ _ _ hell hK) hstep x hx f hf hfV
    have ht : h = 1/N := by dsimp [h]; norm_num
    simpa [gmpKilledEndpointKernel_apply, ← hrow, abs_of_pos h0, c, h, γ, γ₂, γ₃, show (2 : ℝ) - 1 = 1 by norm_num] using hc₂'.trans hb
  · have hb := h₃ lam h0 h1 (sourceReducedBound L) (one_le_sourceReducedBound Q.ellipticity_parameter)
      η hω (c k) (c (k+1)) hωc R S ρ α hell hcoeff K G hK
      (hmass _ _ _ _ _ hell hK) (hharnack _ _ _ _ _ hell hK) hstep x hx f hf hfV
    have ht : h = 2/N := by dsimp [h]; norm_num
    simpa [gmpKilledEndpointKernel_apply, ← hrow, abs_of_pos h0, c, h, γ, γ₂, γ₃, show (3 : ℝ) - 1 = 2 by norm_num] using hc₃'.trans hb

/-- The exact tube statement from the three remaining native kernel inputs. -/
theorem b_tube_probability_of_native_kernel_inputs
    (hspectral : ∀ (d : ℕ) (κ : ℝ), 0 < κ → b_renewal_spectral_existence d κ)
    (hsurvival : ∀ (d : ℕ) (κ : ℝ), 0 < κ →
      ∃ δ, 0 < δ ∧ b_renewal_native_half_survival d κ δ)
    (hharnack : ∀ (d : ℕ) (κ : ℝ), 0 < κ →
      ∃ δ H, 0 < δ ∧ 0 < H ∧ b_renewal_native_harnack d κ δ H) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt := by
  apply b_tube_probability_of_native_inputs
  intro d hd L r₀ l B hl hB
  obtain ⟨κ, hκ, hext⟩ := b_renewal_coefficient_extension_of_regular_bound
    d hd L B (l/32) (by positivity)
  obtain ⟨δ₁, hδ₁, hmass⟩ := hsurvival d κ hκ
  obtain ⟨δ₂, H, hδ₂, hH, hcomp⟩ := hharnack d κ hκ
  refine ⟨κ, min δ₁ δ₂, H, hκ, lt_min hδ₁ hδ₂, hH, hext,
    hspectral d κ hκ, ?_, ?_⟩
  · intro R ρ α K G hell hK x r u hr hball hu hut
    apply hmass R ρ α K G hell hK x r u hr hball hu
    exact hut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r))
  · intro R ρ α K G hell hK x y r u hr hball hy hu hut hxy
    apply hcomp R ρ α K G hell hK x y r u hr hball hy hu _ hxy
    exact hut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r))

/-- Only dimensions covered by the source statement need native estimates. -/
theorem b_tube_probability_of_dimension_native_kernel_inputs
    (hspectral : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      b_renewal_spectral_existence d κ)
    (hsurvival : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      ∃ δ, 0 < δ ∧ b_renewal_native_half_survival d κ δ)
    (hharnack : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      ∃ δ H, 0 < δ ∧ 0 < H ∧ b_renewal_native_harnack d κ δ H) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt := by
  apply b_tube_probability_of_native_inputs
  intro d hd L r₀ l B hl hB
  obtain ⟨κ, hκ, hext⟩ := b_renewal_coefficient_extension_of_regular_bound
    d hd L B (l/32) (by positivity)
  obtain ⟨δ₁, hδ₁, hmass⟩ := hsurvival d hd κ hκ
  obtain ⟨δ₂, H, hδ₂, hH, hcomp⟩ := hharnack d hd κ hκ
  refine ⟨κ, min δ₁ δ₂, H, hκ, lt_min hδ₁ hδ₂, hH, hext,
    hspectral d hd κ hκ, ?_, ?_⟩
  · intro R ρ α K G hell hK x r u hr hball hu hut
    apply hmass R ρ α K G hell hK x r u hr hball hu
    exact hut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r))
  · intro R ρ α K G hell hK x y r u hr hball hy hu hut hxy
    apply hcomp R ρ α K G hell hK x y r u hr hball hy hu _ hxy
    exact hut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r))

/-- Only dimensions covered by the source statement need native estimates. -/
theorem b_tube_probability_of_continuous_native_kernel_inputs
    (hspectral : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      b_renewal_continuous_spectral_existence d κ)
    (hsurvival : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      ∃ δ, 0 < δ ∧ b_renewal_native_half_survival d κ δ)
    (hharnack : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      ∃ δ H, 0 < δ ∧ 0 < H ∧ b_renewal_native_harnack d κ δ H) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt := by
  apply b_tube_probability_of_continuous_native_inputs
  intro d hd L r₀ l B hl hB
  obtain ⟨κ, hκ, hext⟩ := b_renewal_continuous_coefficient_extension_of_regular_bound
    d hd L B (l/32) (by positivity)
  obtain ⟨δ₁, hδ₁, hmass⟩ := hsurvival d hd κ hκ
  obtain ⟨δ₂, H, hδ₂, hH, hcomp⟩ := hharnack d hd κ hκ
  refine ⟨κ, min δ₁ δ₂, H, hκ, lt_min hδ₁ hδ₂, hH, hext,
    hspectral d hd κ hκ, ?_, ?_⟩
  · intro R ρ α K G hell hK x r u hr hball hu hut
    apply hmass R ρ α K G hell hK x r u hr hball hu
    exact hut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r))
  · intro R ρ α K G hell hK x y r u hr hball hy hu hut hxy
    apply hcomp R ρ α K G hell hK x y r u hr hball hy hu _ hxy
    exact hut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r))

/-- The exact tube statement follows from continuous-density spectral existence
and pointwise native kernel comparison. -/
theorem b_tube_probability_of_continuous_spectral_and_harnack
    (hspectral : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      b_renewal_continuous_spectral_existence d κ)
    (hharnack : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      ∃ δ H, 0 < δ ∧ 0 < H ∧ b_renewal_native_harnack d κ δ H) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt :=
  b_tube_probability_of_continuous_native_kernel_inputs hspectral
    b_renewal_native_half_survival_of_ellipticity hharnack

/-- The exact tube statement follows from continuous-density spectral existence
and the local pointwise comparison used by the parabolic chain. -/
theorem b_tube_probability_of_continuous_spectral_and_scaled_unit
    (hspectral : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      b_renewal_continuous_spectral_existence d κ)
    (hharnack : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      Calculus.BScaledUnitPointwiseHarnack d κ) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt :=
  b_tube_probability_of_continuous_spectral_and_harnack hspectral
    (fun d hd κ hκ => b_renewal_native_harnack_of_scaled_unit d κ hκ
      (hharnack d hd κ hκ))

/-- Uniform native kernel comparison obtained from weighted weak Harnack. -/
theorem b_renewal_native_harnack_of_ellipticity
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ δ H, 0 < δ ∧ 0 < H ∧ b_renewal_native_harnack d κ δ H := by
  apply b_renewal_native_harnack_of_scaled_unit d κ hκ
  exact Calculus.b_pointwise_harnack_chain_step_of_unit d κ
    (Calculus.b_unit_pointwise_harnack_r14 d hd κ hκ)

/-- Continuous-density native spectral existence implies the tube estimate. -/
theorem b_tube_probability_of_continuous_spectral
    (hspectral : ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
      b_renewal_continuous_spectral_existence d κ) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt :=
  b_tube_probability_of_continuous_spectral_and_harnack hspectral
    b_renewal_native_harnack_of_ellipticity

/-- The pointwise initial trace of the native spectral series is the only
remaining input for the exact tube statement. -/
theorem b_tube_probability_of_spectral_initial_delta
    (hinit : ∀ (d : ℕ) (hd : 2 ≤ d) (κ : ℝ), 0 < κ →
      ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → Continuous ρ →
      ∀ s : DirichletSpectralResolution ρ α R, BNativeSpectralInitialDeltaR13 s) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt := by
  apply b_tube_probability_of_continuous_spectral
  intro d hd κ hκ R hR ρ α hell hρ
  obtain ⟨s, G, hfund⟩ :=
    b_native_fundamental_exists_of_initial_delta_r14 hd hκ hR hell
      (hinit d hd κ hκ R hR ρ α hell hρ)
  exact ⟨bNativeSpectralKernelR13 s, G, hfund⟩

/-- The weighted spectral-row initial trace implies the exact tube estimate. -/
theorem b_tube_probability_of_weighted_spectral_row_initial_trace
    (hrow : ∀ (d : ℕ) (hd : 2 ≤ d) (κ : ℝ), 0 < κ →
      ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → Continuous ρ →
      ∀ s : DirichletSpectralResolution ρ α R, Calculus.br14WeightedRowInitialTrace s) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt := by
  apply b_tube_probability_of_spectral_initial_delta
  intro d hd κ hκ R hR ρ α hell hρ s y hy φ hφ
  exact Calculus.br14_native_column_initial_delta hκ hell hρ s
    (hrow d hd κ hκ R hR ρ α hell hρ s) y hy φ hφ.1.continuous hφ.2.1 hφ.2.2

#print axioms b_tube_probability_of_weighted_spectral_row_initial_trace
#print axioms b_tube_probability_of_spectral_initial_delta
#print axioms b_tube_probability_of_continuous_spectral
#print axioms b_renewal_native_harnack_of_ellipticity
#print axioms b_tube_probability_of_continuous_spectral_and_scaled_unit
#print axioms b_renewal_native_harnack_of_scaled_unit
#print axioms b_tube_probability_of_continuous_spectral_and_harnack
#print axioms b_renewal_native_half_survival_of_ellipticity
#print axioms b_renewal_exponential_defect_of_ellipticity
#print axioms b_renewal_native_half_survival_of_exponential_defect
#print axioms b_tube_probability_of_continuous_native_kernel_inputs
#print axioms b_renewal_continuous_coefficient_extension_of_regular_bound
#print axioms b_renewal_native_harnack_of_scaled_harnack
#print axioms b_tube_probability_of_dimension_native_kernel_inputs
#print axioms b_renewal_coefficient_extension_of_regular_bound
#print axioms b_tube_probability_of_native_kernel_inputs
#print axioms b_tube_probability_of_native_inputs
#print axioms b_renewal_piece_compact_test
#print axioms b_renewal_physical_ball
#print axioms b_renewal_window_centered_geometry
#print axioms b_actual_translated_capped_compact_test
#print axioms b_actual_compact_test_translate
#print axioms b_actual_capped_compact_test
#print axioms b_actual_native_compact_test_of_pointwise
end EinsteinFull
