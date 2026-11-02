import EinsteinFull.Calculus.C12TubeWeightedDaviesGaffney

open EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open MeasureTheory
open scoped NNReal

noncomputable section
namespace EinsteinFull.Calculus

/-- Nash decay for the actual supplied Dirichlet spectral resolution. The
constant is chosen uniformly before the ball and coefficient fields. -/
theorem c12_supplied_spectral_heat_L1_L2_decay {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R),
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)) (F : ℝ),
        0 < F → (∫ x, |f x| ∂dirichletVolume ρ R) ≤ F →
      ∀ (t : ℝ≥0), 0 < t →
        ‖SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f‖ ^ 2 ≤
        ((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)) * F ^ (4 / (d : ℝ)))) * t) ^
          (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hdec⟩ := spectral_heat_native_L1_L2_decay hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h s
  classical
  choose u hu hv using fun n => c16_supplied_eigenfunction_dirichletEquation hd hκ hR h s n
  have hb : ∀ n, spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n) := by
    intro n
    rw [show spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) from
      congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n]
    apply Lp.ext
    exact (s.square_integrable n).coeFn_toLp.trans (hu n).symm
  exact hdec R hR ρ α h s u hb (by simpa only [← hb] using hv)

#print axioms c12_supplied_spectral_heat_L1_L2_decay

/-- The supplied Dirichlet kernel has sub-Markov total mass at almost every
starting point, with respect to Lebesgue measure on the source ball. -/
theorem c12_supplied_kernel_mass_ae_le_one {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) :
    ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      0 ≤ (∫ y in sourceBall (0 : Vec d) R, K t x y) ∧
        (∫ y in sourceBall (0 : Vec d) R, K t x y) ≤ 1 := by
  classical
  obtain ⟨s, hs⟩ := c12_supplied_kernel_heat_action_L2 hκ h K G hK
  choose u hu hv using fun n => c16_supplied_eigenfunction_dirichletEquation hd hκ hR h s n
  have hb : ∀ n, spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n) := by
    intro n
    rw [show spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) from
      congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n]
    apply Lp.ext
    exact (s.square_integrable n).coeFn_toLp.trans (hu n).symm
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let f : Lp ℝ 2 (dirichletVolume ρ R) := Lp.const 2 _ (1 : ℝ)
  have hf : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1 := by
    filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with x hx
    rw [show f x = 1 from hx]
    exact ⟨zero_le_one, le_rfl⟩
  let τ : ℝ≥0 := ⟨t, ht.le⟩
  have horder := (dirichletHilbert_spectralHeat_order hd hκ h R hR s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) u (spectralHeatBasis s) hb
    (by simpa only [← hb] using hv) τ f).2 hf
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    change volume.restrict (sourceBall (0 : Vec d) R) ≪
      (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun y => ENNReal.ofReal (ρ y))
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun y => ne_of_gt
      (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hκ (h.2.2 y).1))
  filter_upwards [hac.ae_le horder, hac.ae_le (hs τ ht f)] with x hx hact
  have heq : (∫ y in sourceBall (0 : Vec d) R, K t x y * f y) =
      ∫ y in sourceBall (0 : Vec d) R, K t x y := by
    apply integral_congr_ae
    filter_upwards [hac.ae_le (Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ)))] with y hy
    rw [show f y = 1 from hy, mul_one]
  change SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) τ f x =
      ∫ y in sourceBall (0 : Vec d) R, K t x y * f y at hact
  rw [heq] at hact
  rw [← hact]
  exact hx

#print axioms c12_supplied_kernel_mass_ae_le_one

/-- Almost every supplied spectral heat row has weighted L¹ norm at most one. -/
theorem c12_supplied_heat_row_L1_ae_le_one {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) :
    ∃ s : DirichletSpectralResolution ρ α R,
      ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
        (∫ y, |(∑' i, (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
          (s.square_integrable i).toLp (s.eigenfunction i)) y| ∂dirichletVolume ρ R) ≤ 1 := by
  obtain ⟨s, hs⟩ := hK.2
  have hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) :=
    fun t ht x hx y hy => (hs t ht x hx y hy).1
  refine ⟨s, ?_⟩
  have hball : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  filter_upwards [c12_supplied_kernel_mass_ae_le_one hd hκ hR h K G hK t ht,
    ae_restrict_mem hball] with x hx hxb
  have hrow := c16_supplied_heat_row_Lp_ae_eq s hspec t ht x hxb
  have heq : (∫ y, |(∑' i, (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
          (s.square_integrable i).toLp (s.eigenfunction i)) y| ∂dirichletVolume ρ R) =
      ∫ y in sourceBall (0 : Vec d) R, K t x y := by
    calc
      _ = ∫ y, |∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x *
          s.eigenfunction i y| ∂dirichletVolume ρ R := by
        apply integral_congr_ae
        filter_upwards [hrow] with y hy
        rw [hy]
      _ = ∫ y in sourceBall (0 : Vec d) R, K t x y := by
        change (∫ y, |∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x *
          s.eigenfunction i y| ∂(volume.restrict (sourceBall (0 : Vec d) R)).withDensity
            (fun y => ENNReal.ofReal (ρ y))) = _
        rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hball] with y hy
        have hp : 0 < ρ y := lt_of_lt_of_le hκ (h.2.2 y).1
        have hk : 0 ≤ K t x y := (hK.1 y hy).2.1 t ht x hxb
        have hs0 : 0 ≤ ∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x *
            s.eigenfunction i y := by
          rw [(hs t ht x hxb y hy).2] at hk
          exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hk) hp
        simp only [ENNReal.toReal_ofReal hp.le, smul_eq_mul, abs_of_nonneg hs0]
        exact ((hs t ht x hxb y hy).2).symm
  rw [heq]
  exact hx.2

#print axioms c12_supplied_heat_row_L1_ae_le_one

/-- The supplied spectral heat operator advances its own positive-time row. -/
theorem c12_supplied_heat_operator_row {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (p : ℝ≥0) (q : ℝ) (hq : 0 < q) (x : Vec d) (hx : x ∈ sourceBall 0 R) :
    SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) p
      (∑' i, (Real.exp (-s.eigenvalue i * q) * s.eigenfunction i x) •
        (s.square_integrable i).toLp (s.eigenfunction i)) =
    ∑' i, (Real.exp (-s.eigenvalue i * ((p : ℝ) + q)) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i) := by
  apply (spectralHeatBasis s).repr.injective
  apply lp.ext
  funext n
  rw [SpectralHeat.heatOperator_repr,
    c16_supplied_heat_row_basis_coordinate s hspec q hq x hx,
    c16_supplied_heat_row_basis_coordinate s hspec _
      (add_pos_of_nonneg_of_pos p.coe_nonneg hq) x hx]
  rw [mul_add, Real.exp_add]
  ring

#print axioms c12_supplied_heat_operator_row

/-- Nash decay bounds the supplied positive-time heat rows almost everywhere. -/
theorem c12_supplied_heat_row_L2_decay_for_spectrum {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (p : ℝ≥0), 0 < p → ∀ (q : ℝ), 0 < q →
      ∀ s : DirichletSpectralResolution ρ α R,
        (∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
          ∀ y ∈ sourceBall (0 : Vec d) R,
            Summable (fun n => Real.exp (-s.eigenvalue n * t) *
              s.eigenfunction n x * s.eigenfunction n y) ∧
            K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
              s.eigenfunction n x * s.eigenfunction n y) →
        ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
          ‖(∑' i, (Real.exp (-s.eigenvalue i * ((p : ℝ) + q)) *
            s.eigenfunction i x) • (s.square_integrable i).toLp (s.eigenfunction i))‖ ^ 2 ≤
          ((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * p) ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hdec⟩ := c12_supplied_spectral_heat_L1_L2_decay hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK p hp q hq s hs
  have hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) :=
    fun t ht x hx y hy => (hs t ht x hx y hy).1
  have hmass := c12_supplied_kernel_mass_ae_le_one hd hκ hR h K G hK q hq
  have hball : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  filter_upwards [hmass, ae_restrict_mem hball] with x hx hxb
  have hrow := c16_supplied_heat_row_Lp_ae_eq s hspec q hq x hxb
  have hL1 : (∫ y, |(∑' i, (Real.exp (-s.eigenvalue i * q) *
      s.eigenfunction i x) • (s.square_integrable i).toLp (s.eigenfunction i)) y|
      ∂dirichletVolume ρ R) ≤ 1 := by
    have heq : (∫ y, |(∑' i, (Real.exp (-s.eigenvalue i * q) *
        s.eigenfunction i x) • (s.square_integrable i).toLp (s.eigenfunction i)) y|
        ∂dirichletVolume ρ R) = ∫ y in sourceBall (0 : Vec d) R, K q x y := by
      calc
        _ = ∫ y, |∑' i, Real.exp (-s.eigenvalue i * q) * s.eigenfunction i x *
            s.eigenfunction i y| ∂dirichletVolume ρ R := by
          apply integral_congr_ae
          filter_upwards [hrow] with y hy
          rw [hy]
        _ = _ := by
          change (∫ y, |∑' i, Real.exp (-s.eigenvalue i * q) * s.eigenfunction i x *
            s.eigenfunction i y| ∂(volume.restrict (sourceBall (0 : Vec d) R)).withDensity
              (fun y => ENNReal.ofReal (ρ y))) = _
          rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
            (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hball] with y hy
          have hpρ : 0 < ρ y := lt_of_lt_of_le hκ (h.2.2 y).1
          have hk : 0 ≤ K q x y := (hK.1 y hy).2.1 q hq x hxb
          have hs0 : 0 ≤ ∑' i, Real.exp (-s.eigenvalue i * q) *
              s.eigenfunction i x * s.eigenfunction i y := by
            rw [(hs q hq x hxb y hy).2] at hk
            exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hk) hpρ
          simp only [ENNReal.toReal_ofReal hpρ.le, smul_eq_mul, abs_of_nonneg hs0]
          exact ((hs q hq x hxb y hy).2).symm
    rw [heq]
    exact hx.2
  have hbound := hdec R hR ρ α h s _ 1 zero_lt_one hL1 p hp
  rw [c12_supplied_heat_operator_row s hspec p q hq x hxb] at hbound
  simpa only [Real.one_rpow, mul_one] using hbound

#print axioms c12_supplied_heat_row_L2_decay_for_spectrum

/-- Nash decay bounds the supplied positive-time heat rows almost everywhere. -/
theorem c12_supplied_heat_row_L2_decay {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (p : ℝ≥0), 0 < p → ∀ (q : ℝ), 0 < q →
      ∃ s : DirichletSpectralResolution ρ α R,
        ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
          ‖(∑' i, (Real.exp (-s.eigenvalue i * ((p : ℝ) + q)) *
            s.eigenfunction i x) • (s.square_integrable i).toLp (s.eigenfunction i))‖ ^ 2 ≤
          ((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * p) ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hdec⟩ := c12_supplied_heat_row_L2_decay_for_spectrum hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK p hp q hq
  obtain ⟨s, hs⟩ := hK.2
  exact ⟨s, hdec R hR ρ α h K G hK p hp q hq s hs⟩

#print axioms c12_supplied_heat_row_L2_decay

/-- Almost-everywhere diagonal bound for the literal supplied kernel. -/
theorem c12_supplied_kernel_diagonal_decay {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (p : ℝ≥0), 0 < p → ∀ (q : ℝ), 0 < q →
      ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
        K (((p : ℝ) + q) + ((p : ℝ) + q)) x x ≤
          κ⁻¹ * (((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * p) ^
            (-(d : ℝ) / 2)) := by
  obtain ⟨C, hC, hdec⟩ := c12_supplied_heat_row_L2_decay_for_spectrum hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK p hp q hq
  obtain ⟨s, hs⟩ := hK.2
  have ht : 0 < (p : ℝ) + q := add_pos_of_nonneg_of_pos p.coe_nonneg hq
  have hball : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  filter_upwards [hdec R hR ρ α h K G hK p hp q hq s hs,
    ae_restrict_mem hball] with x hx hxb
  change ‖spectralHeatRow s ((p : ℝ) + q) x‖ ^ 2 ≤ _ at hx
  rw [(hs _ (add_pos ht ht) x hxb x hxb).2,
    ← spectral_heat_row_inner hd hκ h hR s _ _ ht ht x x hxb hxb,
    real_inner_self_eq_norm_sq]
  calc
    ρ x * ‖spectralHeatRow s ((p : ℝ) + q) x‖ ^ 2 ≤
        ρ x * (((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * p) ^
          (-(d : ℝ) / 2)) := mul_le_mul_of_nonneg_left hx (le_of_lt (lt_of_lt_of_le hκ (h.2.2 x).1))
    _ ≤ _ := mul_le_mul_of_nonneg_right (h.2.2 x).2.1 (le_trans (sq_nonneg _) hx)

#print axioms c12_supplied_kernel_diagonal_decay

/-- Nash decay gives a uniform off-diagonal bound for almost every pair of
points. This is the unweighted prefactor needed before Gaussian separation. -/
theorem c12_supplied_kernel_pair_decay {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (p : ℝ≥0), 0 < p → ∀ (q : ℝ), 0 < q →
      ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
        ∀ᵐ y ∂volume.restrict (sourceBall (0 : Vec d) R),
          K (((p : ℝ) + q) + ((p : ℝ) + q)) x y ≤
            κ⁻¹ * (((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * p) ^
              (-(d : ℝ) / 2)) := by
  obtain ⟨C, hC, hdec⟩ := c12_supplied_heat_row_L2_decay_for_spectrum hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK p hp q hq
  obtain ⟨s, hs⟩ := hK.2
  have ht : 0 < (p : ℝ) + q := add_pos_of_nonneg_of_pos p.coe_nonneg hq
  have hball : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  filter_upwards [hdec R hR ρ α h K G hK p hp q hq s hs,
    ae_restrict_mem hball] with x hx hxb
  filter_upwards [hdec R hR ρ α h K G hK p hp q hq s hs,
    ae_restrict_mem hball] with y hy hyb
  change ‖spectralHeatRow s ((p : ℝ) + q) x‖ ^ 2 ≤ _ at hx
  change ‖spectralHeatRow s ((p : ℝ) + q) y‖ ^ 2 ≤ _ at hy
  have hprod : ‖spectralHeatRow s ((p : ℝ) + q) x‖ *
      ‖spectralHeatRow s ((p : ℝ) + q) y‖ ≤
      ((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * p) ^ (-(d : ℝ) / 2) := by
    nlinarith [sq_nonneg (‖spectralHeatRow s ((p : ℝ) + q) x‖ -
      ‖spectralHeatRow s ((p : ℝ) + q) y‖)]
  rw [(hs _ (add_pos ht ht) x hxb y hyb).2,
    ← spectral_heat_row_inner hd hκ h hR s _ _ ht ht x y hxb hyb]
  calc
    ρ y * inner ℝ (spectralHeatRow s ((p : ℝ) + q) x)
        (spectralHeatRow s ((p : ℝ) + q) y) ≤
      ρ y * (‖spectralHeatRow s ((p : ℝ) + q) x‖ *
        ‖spectralHeatRow s ((p : ℝ) + q) y‖) :=
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _)
        (le_of_lt (lt_of_lt_of_le hκ (h.2.2 y).1))
    _ ≤ ρ y * _ := mul_le_mul_of_nonneg_left hprod
      (le_of_lt (lt_of_lt_of_le hκ (h.2.2 y).1))
    _ ≤ _ := mul_le_mul_of_nonneg_right (h.2.2 y).2.1 (le_trans (sq_nonneg _) hx)

#print axioms c12_supplied_kernel_pair_decay

/-- The localized supplied heat row inherits Gaussian L² separation with
its Nash decay prefactor. -/
theorem c12_supplied_localized_heat_row_davies_gaffney {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (p : ℝ≥0), 0 < p → ∀ (q : ℝ), 0 < q →
      ∀ (s : DirichletSpectralResolution ρ α R),
        (∀ u : ℝ, 0 < u → ∀ x ∈ sourceBall (0 : Vec d) R,
          ∀ y ∈ sourceBall (0 : Vec d) R,
            Summable (fun n => Real.exp (-s.eigenvalue n * u) *
              s.eigenfunction n x * s.eigenfunction n y) ∧
            K u x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * u) *
              s.eigenfunction n x * s.eigenfunction n y) →
      ∀ (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B), B.Nonempty →
      ∀ (δ : ℝ), 0 < δ →
        (∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x - y)) →
      ∀ (t : ℝ≥0), 0 < t →
      ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
        let row := spectralHeatRow s ((p : ℝ) + q) x
        let f := ((Lp.memLp row).indicator hB).toLp (B.indicator fun z => row z)
        let g := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f
        ‖((Lp.memLp g).indicator hA).toLp (A.indicator fun z => g z)‖ ^ 2 ≤
          Real.exp (-(δ ^ 2) / ((8 * κ⁻¹ ^ 2) * (t : ℝ))) *
          (((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * p) ^ (-(d : ℝ) / 2)) := by
  obtain ⟨C, hC, hdec⟩ := c12_supplied_heat_row_L2_decay_for_spectrum hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK p hp q hq s hs A B hA hB hBn δ hδ hsep t ht
  filter_upwards [hdec R hR ρ α h K G hK p hp q hq s hs] with x hx
  let row := spectralHeatRow s ((p : ℝ) + q) x
  let f := ((Lp.memLp row).indicator hB).toLp (B.indicator fun z => row z)
  have hf : ∀ᵐ z ∂dirichletVolume ρ R, z ∉ B → f z = 0 := by
    filter_upwards [((Lp.memLp row).indicator hB).coeFn_toLp] with z hz hnot
    change ((Lp.memLp row).indicator hB).toLp (B.indicator fun z => row z) z = 0
    rw [hz, Set.indicator_of_notMem hnot]
  have hnorm : ‖f‖ ≤ ‖row‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [((Lp.memLp row).indicator hB).coeFn_toLp] with z hz
    change ‖((Lp.memLp row).indicator hB).toLp (B.indicator fun z => row z) z‖ ≤ ‖row z‖
    rw [hz]
    exact norm_indicator_le_norm_self _ _
  have hsq : ‖f‖ ^ 2 ≤ ‖row‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
  change ‖row‖ ^ 2 ≤ _ at hx
  have hDG := c12_supplied_spectral_heat_davies_gaffney hd hκ h R hR s
    A B hA hBn δ hδ hsep t ht f hf
  exact hDG.trans (mul_le_mul_of_nonneg_left (hsq.trans hx) (Real.exp_pos _).le)

#print axioms c12_supplied_localized_heat_row_davies_gaffney

/-- The full heat-flow tail is bounded by the initial tail plus the
Gaussian leakage from the separated part. -/
theorem c12_supplied_spectral_heat_tail_step {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBn : B.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x - y))
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    let P := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t
    let restrict := fun (S : Set (Vec d)) (hS : MeasurableSet S)
        (g : Lp ℝ 2 (dirichletVolume ρ R)) =>
      ((Lp.memLp g).indicator hS).toLp (S.indicator fun z => g z)
    ‖restrict A hA (P f)‖ ≤
      Real.exp (-(δ ^ 2) / ((16 * κ⁻¹ ^ 2) * (t : ℝ))) * ‖f‖ +
        ‖restrict Bᶜ hB.compl f‖ := by
  let P := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t
  let restrict := fun (S : Set (Vec d)) (hS : MeasurableSet S)
      (g : Lp ℝ 2 (dirichletVolume ρ R)) =>
    ((Lp.memLp g).indicator hS).toLp (S.indicator fun z => g z)
  have hsplit : restrict B hB f + restrict Bᶜ hB.compl f = f := by
    apply Lp.ext
    filter_upwards [((Lp.memLp f).indicator hB).coeFn_toLp,
      ((Lp.memLp f).indicator hB.compl).coeFn_toLp, Lp.coeFn_add (restrict B hB f)
        (restrict Bᶜ hB.compl f)] with x hx hy hz
    change (restrict B hB f + restrict Bᶜ hB.compl f) x = f x
    rw [hz]
    change restrict B hB f x + restrict Bᶜ hB.compl f x = f x
    rw [hx, hy]
    by_cases hxb : x ∈ B <;> simp [hxb]
  have hlocal : ∀ g k, restrict A hA (g + k) = restrict A hA g + restrict A hA k := by
    intro g k
    apply Lp.ext
    filter_upwards [((Lp.memLp (g + k)).indicator hA).coeFn_toLp,
      ((Lp.memLp g).indicator hA).coeFn_toLp,
      ((Lp.memLp k).indicator hA).coeFn_toLp,
      Lp.coeFn_add g k, Lp.coeFn_add (restrict A hA g) (restrict A hA k)] with x hx hy hz hadd hadd'
    change restrict A hA (g + k) x = (restrict A hA g + restrict A hA k) x
    rw [hx, hadd']
    change A.indicator (fun z => (g + k) z) x = restrict A hA g x + restrict A hA k x
    rw [hy, hz]
    by_cases hxa : x ∈ A
    · simpa only [Set.indicator_of_mem hxa, Pi.add_apply] using hadd
    · simp [hxa]
  have hsmall : ‖restrict A hA (P (restrict B hB f))‖ ^ 2 ≤
      Real.exp (-(δ ^ 2) / ((8 * κ⁻¹ ^ 2) * (t : ℝ))) * ‖f‖ ^ 2 := by
    have hf : ∀ᵐ z ∂dirichletVolume ρ R, z ∉ B → restrict B hB f z = 0 := by
      filter_upwards [((Lp.memLp f).indicator hB).coeFn_toLp] with z hz hzB
      change ((Lp.memLp f).indicator hB).toLp (B.indicator fun z => f z) z = 0
      rw [hz, Set.indicator_of_notMem hzB]
    have hnorm : ‖restrict B hB f‖ ≤ ‖f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [((Lp.memLp f).indicator hB).coeFn_toLp] with z hz
      change ‖((Lp.memLp f).indicator hB).toLp (B.indicator fun z => f z) z‖ ≤ ‖f z‖
      rw [hz]
      exact norm_indicator_le_norm_self _ _
    have hdg := c12_supplied_spectral_heat_davies_gaffney hd hκ h R hR s
      A B hA hBn δ hδ hsep t ht (restrict B hB f) hf
    exact hdg.trans (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm) (Real.exp_pos _).le)
  have hexp : (Real.exp (-(δ ^ 2) / ((16 * κ⁻¹ ^ 2) * (t : ℝ)))) ^ 2 =
      Real.exp (-(δ ^ 2) / ((8 * κ⁻¹ ^ 2) * (t : ℝ))) := by
    rw [sq, ← Real.exp_add]
    congr 1 <;> ring
  have hsmall' : ‖restrict A hA (P (restrict B hB f))‖ ≤
      Real.exp (-(δ ^ 2) / ((16 * κ⁻¹ ^ 2) * (t : ℝ))) * ‖f‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
    simpa only [mul_pow, hexp] using hsmall
  have hlarge : ‖restrict A hA (P (restrict Bᶜ hB.compl f))‖ ≤ ‖restrict Bᶜ hB.compl f‖ := by
    calc
      _ ≤ ‖P (restrict Bᶜ hB.compl f)‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [((Lp.memLp (P (restrict Bᶜ hB.compl f))).indicator hA).coeFn_toLp] with z hz
        change ‖((Lp.memLp (P (restrict Bᶜ hB.compl f))).indicator hA).toLp
          (A.indicator fun z => P (restrict Bᶜ hB.compl f) z) z‖ ≤ _
        rw [hz]
        exact norm_indicator_le_norm_self _ _
      _ ≤ _ := SpectralHeat.heatOperator_norm_le _ _ _ _ _
  change ‖restrict A hA (P f)‖ ≤ _
  conv_lhs => rw [← hsplit, map_add, hlocal]
  exact (norm_add_le _ _).trans (add_le_add hsmall' hlarge)

#print axioms c12_supplied_spectral_heat_tail_step

/-- A separately continuous envelope for the supplied kernel extends from
almost every pair to every interior pair, with the ellipticity loss. -/
theorem c12_supplied_kernel_envelope_pointwise {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) (D : Vec d → Vec d → ℝ)
    (hD : ∀ x ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R, 0 ≤ D x y)
    (hcD₁ : ∀ y, ContinuousOn (fun x => D x y) (sourceBall (0 : Vec d) R))
    (hcD₂ : ∀ x, ContinuousOn (fun y => D x y) (sourceBall (0 : Vec d) R))
    (hae : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      ∀ᵐ y ∂volume.restrict (sourceBall (0 : Vec d) R), K t x y ≤ D x y) :
    ∀ x ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
      K t x y ≤ κ⁻¹ * (D x y / κ) := by
  let B := sourceBall (0 : Vec d) R
  have hB : IsOpen B := (dirichletBall (d := d) R).isOpen
  have hc : ∀ y ∈ B, ContinuousOn (fun x => K t x y) B := by
    intro y hy
    apply ((hK.1 y hy).1).comp (continuous_const.prodMk continuous_id).continuousOn
    intro x hx
    exact ⟨ht, subset_closure hx⟩
  have hrow : ∀ᵐ x ∂volume.restrict B, ∀ y ∈ B, K t x y / ρ y ≤ D x y / κ := by
    filter_upwards [hae, ae_restrict_mem hB.measurableSet] with x hx hxb
    have hρx : 0 < ρ x := lt_of_lt_of_le hκ (h.2.2 x).1
    have hcont : ContinuousOn (fun y => D x y / κ - K t y x / ρ x) B :=
      ((hcD₂ x).div_const κ).sub ((hc x hxb).div_const (ρ x))
    have hbound : ∀ᵐ y ∂volume.restrict B, 0 ≤ D x y / κ - K t y x / ρ x := by
      filter_upwards [hx, ae_restrict_mem hB.measurableSet] with y hy hyb
      have hρy : 0 < ρ y := lt_of_lt_of_le hκ (h.2.2 y).1
      have hs := hK.weighted_symmetry ht hxb hyb
      have heq : K t y x / ρ x = K t x y / ρ y := by
        apply (div_eq_div_iff hρx.ne' hρy.ne').2
        nlinarith [hs]
      rw [heq]
      have hh := (div_le_div_of_nonneg_right hy hρy.le).trans
        (div_le_div_of_nonneg_left (hD x hxb y hyb) hκ (h.2.2 y).1)
      linarith
    have hall := continuousOn_le_of_ae_restrict hB hcont hbound
    intro y hy
    have hh := hall y hy
    have hs := hK.weighted_symmetry ht hxb hy
    have hρy : 0 < ρ y := lt_of_lt_of_le hκ (h.2.2 y).1
    have heq : K t y x / ρ x = K t x y / ρ y := by
      apply (div_eq_div_iff hρx.ne' hρy.ne').2
      nlinarith [hs]
    rw [heq] at hh
    linarith
  intro x hx y hy
  have hρy : 0 < ρ y := lt_of_lt_of_le hκ (h.2.2 y).1
  have hcont : ContinuousOn (fun z => D z y / κ - K t z y / ρ y) B :=
    ((hcD₁ y).div_const κ).sub ((hc y hy).div_const (ρ y))
  have hbound : ∀ᵐ z ∂volume.restrict B, 0 ≤ D z y / κ - K t z y / ρ y := by
    filter_upwards [hrow] with z hz
    linarith [hz y hy]
  have hpt := continuousOn_le_of_ae_restrict hB hcont hbound x hx
  have hnorm : K t x y / ρ y ≤ D x y / κ := by linarith
  have hmul := (div_le_iff₀ hρy).mp hnorm
  have hDκ : 0 ≤ D x y / κ := div_nonneg (hD x hx y hy) hκ.le
  have hρupper := mul_le_mul_of_nonneg_left (h.2.2 y).2.1 hDκ
  nlinarith

#print axioms c12_supplied_kernel_envelope_pointwise

/-- An almost-everywhere uniform bound for the supplied density extends to
all interior points, using the kernel's weighted symmetry and continuous
representatives in its first spatial argument. -/
theorem c12_supplied_kernel_uniform_bound_pointwise {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t D : ℝ) (ht : 0 < t) (hD : 0 ≤ D)
    (hae : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      ∀ᵐ y ∂volume.restrict (sourceBall (0 : Vec d) R), K t x y ≤ D) :
    ∀ x ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
      K t x y ≤ κ⁻¹ * (D / κ) := by
  exact c12_supplied_kernel_envelope_pointwise hκ h K G hK t ht (fun _ _ => D)
    (by intro x hx y hy; exact hD)
    (by intro y; exact continuousOn_const)
    (by intro x; exact continuousOn_const) hae

#print axioms c12_supplied_kernel_uniform_bound_pointwise

/-- The Nash prefactor bound for the supplied kernel holds at every
interior pair, without any continuity assumption on the density. -/
theorem c12_supplied_kernel_pair_decay_pointwise {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (p : ℝ≥0), 0 < p → ∀ (q : ℝ), 0 < q →
      ∀ x ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
        K (((p : ℝ) + q) + ((p : ℝ) + q)) x y ≤
          κ⁻¹ * ((κ⁻¹ * (((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * p) ^
            (-(d : ℝ) / 2))) / κ) := by
  obtain ⟨C, hC, hpair⟩ := c12_supplied_kernel_pair_decay hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK p hp q hq
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hD : 0 ≤ κ⁻¹ * (((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * p) ^
      (-(d : ℝ) / 2)) := by positivity
  have ht : 0 < ((p : ℝ) + q) + ((p : ℝ) + q) := by positivity
  exact c12_supplied_kernel_uniform_bound_pointwise hκ h K G hK _ _ ht hD
    (hpair R hR ρ α h K G hK p hp q hq)

#print axioms c12_supplied_kernel_pair_decay_pointwise

/-- The supplied Dirichlet kernel is pointwise ultracontractive, with its
constant uniform in the domain and all admissible coefficient fields. -/
theorem c12_supplied_kernel_ultracontractive {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (t : ℝ), 0 < t →
      ∀ x ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
        K t x y ≤ C * t ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hpair⟩ := c12_supplied_kernel_pair_decay_pointwise hd hκ
  let A : ℝ := 4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ))) / 4
  let p : ℝ := -(d : ℝ) / 2
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨κ⁻¹ * ((κ⁻¹ * A ^ p) / κ), by positivity, ?_⟩
  intro R hR ρ α h K G hK t ht x hx y hy
  let q : ℝ≥0 := ⟨t / 4, by positivity⟩
  have hq : 0 < q := by change 0 < t / 4; positivity
  have hb := hpair R hR ρ α h K G hK q hq (t / 4) (by positivity) x hx y hy
  have hqval : (q : ℝ) = t / 4 := rfl
  have he : ((q : ℝ) + t / 4) + ((q : ℝ) + t / 4) = t := by rw [hqval]; ring
  have hf : (4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))) * (q : ℝ) = A * t := by
    rw [hqval]; dsimp [A]; ring
  rw [he, hf, Real.mul_rpow hA.le ht.le] at hb
  convert hb using 1 <;> dsimp [p] <;> ring

#print axioms c12_supplied_kernel_ultracontractive

/-- The supplied spectral heat row obeys the Nash L² decay at every
interior starting point and every positive time. -/
theorem c12_supplied_heat_row_L2_decay_pointwise {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) ∧
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (t : ℝ), 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ‖spectralHeatRow s t x‖ ^ 2 ≤ C * t ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hk⟩ := c12_supplied_kernel_ultracontractive hd hκ
  let p : ℝ := -(d : ℝ) / 2
  refine ⟨κ⁻¹ * C * (2 : ℝ) ^ p, by positivity, ?_⟩
  intro R hR ρ α h K G hK s hs t ht x hx
  have hρ : 0 < ρ x := lt_of_lt_of_le hκ (h.2.2 x).1
  have hb := hk R hR ρ α h K G hK (t + t) (add_pos ht ht) x hx x hx
  rw [(hs (t + t) (add_pos ht ht) x hx x hx).2,
    ← spectral_heat_row_inner hd hκ h hR s t t ht ht x x hx hx,
    real_inner_self_eq_norm_sq] at hb
  have hcomp : κ * ‖spectralHeatRow s t x‖ ^ 2 ≤
      ρ x * ‖spectralHeatRow s t x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (h.2.2 x).1 (sq_nonneg _)
  have hb' : ‖spectralHeatRow s t x‖ ^ 2 ≤
      κ⁻¹ * (C * (t + t) ^ p) := by
    dsimp [p] at *
    have hh := hcomp.trans hb
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hκ).2 (by nlinarith)
  have ht2 : t + t = 2 * t := by ring
  rw [ht2, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le] at hb'
  convert hb' using 1 <;> dsimp [p] <;> ring

#print axioms c12_supplied_heat_row_L2_decay_pointwise

open Filter
open scoped Topology

/-- The heat mass transferred between two positively separated sets tends
to zero in weighted L² as time decreases to zero. -/
theorem c12_supplied_separated_kernel_mass_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAb : A ⊆ sourceBall 0 R) (hBb : B ⊆ sourceBall 0 R)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x-y)) :
    Tendsto (fun t : ℝ => ∫ x in A, ρ x * (∫ y in B, K t x y)^2)
      (𝓝[>] 0) (𝓝 0) := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hv : MemLp (fun _ : Vec d => (1 : ℝ)) 2 (dirichletVolume ρ R) :=
    memLp_const 1
  obtain ⟨C, hC, hDG⟩ := c12_native_weighted_davies_gaffney_of_two_le d hd κ R hκ hR
  let a : ℝ := δ ^ 2 / (8 * κ⁻¹ ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hlim : Tendsto (fun t : ℝ => Real.exp (-a * t⁻¹) *
      (∫ y in B, ρ y)) (𝓝[>] 0) (𝓝 0) := by
    have htop : Tendsto (fun t : ℝ => a * t⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop ha
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp htop).mul_const (∫ y in B, ρ y)
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun t => integral_nonneg fun x =>
      mul_nonneg (le_trans hκ.le (h.2.2 x).1) (sq_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hb := hDG ρ α h K G hK A B hA hB hAb hBb δ t hδ ht hsep
      (fun _ => 1) hv
    simpa [a, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hb

#print axioms c12_supplied_separated_kernel_mass_tendsto_zero

/-- Ultracontractivity controls the squared L² mass of a restricted row by
its weighted L¹ mass on the same set. -/
theorem c12_supplied_restricted_row_L2_sq_le_mass {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (t : ℝ), 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ (B : Set (Vec d)) (hB : MeasurableSet B),
        let row := spectralHeatRow s t x
        ‖((Lp.memLp row).indicator hB).toLp (B.indicator fun y => row y)‖ ^ 2 ≤
          C * t ^ (-(d : ℝ) / 2) * ∫ y in B, row y ∂dirichletVolume ρ R := by
  obtain ⟨C, hC, hbound⟩ := c12_supplied_kernel_ultracontractive hd hκ
  refine ⟨κ⁻¹ * C, by positivity, ?_⟩
  intro R hR ρ α h K G hK s hs t ht x hx B hB
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let row := spectralHeatRow s t x
  let f := B.indicator fun y => row y
  have hf : MemLp f 2 (dirichletVolume ρ R) := (Lp.memLp row).indicator hB
  have hball : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hrow : ∀ᵐ y ∂dirichletVolume ρ R,
      0 ≤ row y ∧ row y ≤ κ⁻¹ * C * t ^ (-(d : ℝ) / 2) := by
    filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht x hx,
      (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hball)] with y hy hyb
    change row y = _ at hy
    have hρ : 0 < ρ y := lt_of_lt_of_le hκ (h.2.2 y).1
    have hk0 := (hK.1 y hyb).2.1 t ht x hx
    have hk := hbound R hR ρ α h K G hK t ht x hx y hyb
    rw [hs t ht x hx y hyb, ← hy] at hk0 hk
    constructor
    · exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hk0) hρ
    · have hmul : κ * row y ≤ ρ y * row y :=
        mul_le_mul_of_nonneg_right (h.2.2 y).1
          (nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hk0) hρ)
      have hdiv : row y ≤ (C * t ^ (-(d : ℝ) / 2)) / κ :=
        (le_div_iff₀ hκ).2 (by nlinarith [hmul.trans hk])
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
  have hpoint : ∀ᵐ y ∂dirichletVolume ρ R,
      f y ^ 2 ≤ (κ⁻¹ * C * t ^ (-(d : ℝ) / 2)) * f y := by
    filter_upwards [hrow] with y hy
    by_cases hyB : y ∈ B
    · simp only [f, Set.indicator_of_mem hyB]
      nlinarith [hy.1, hy.2]
    · simp [f, hyB]
  have hi := integral_mono_ae hf.integrable_sq
    ((hf.integrable (by norm_num)).const_mul (κ⁻¹ * C * t ^ (-(d : ℝ) / 2))) hpoint
  have hnorm : ‖hf.toLp f‖ ^ 2 = ∫ y, f y ^ 2 ∂dirichletVolume ρ R := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with y hy
    rw [hy]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  change ‖hf.toLp f‖ ^ 2 ≤ _
  rw [hnorm]
  rw [integral_const_mul] at hi
  simpa [f, integral_indicator hB] using hi

#print axioms c12_supplied_restricted_row_L2_sq_le_mass

/-- Weighted mass of a supplied spectral row is the Lebesgue mass of the
kernel on the same measurable subset of the source ball. -/
theorem c12_supplied_row_mass_eq_kernel_mass {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ)
    (s : DirichletSpectralResolution ρ α R)
    (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
    (B : Set (Vec d)) (hB : MeasurableSet B) (hBb : B ⊆ sourceBall 0 R) :
    (∫ y in B, spectralHeatRow s t x y ∂dirichletVolume ρ R) =
      ∫ y in B, K t x y := by
  have hball : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    change volume.restrict (sourceBall (0 : Vec d) R) ≪
      (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun y => ENNReal.ofReal (ρ y))
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun y => ne_of_gt
      (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hκ (h.2.2 y).1))
  rw [← integral_indicator hB]
  change (∫ y, B.indicator (fun z => spectralHeatRow s t x z) y ∂
    (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
      (fun y => ENNReal.ofReal (ρ y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ y in sourceBall (0 : Vec d) R, B.indicator (fun z => K t x z) y := by
      apply integral_congr_ae
      filter_upwards [hac.ae_le (spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht x hx),
        ae_restrict_mem hball] with y hy hyb
      change spectralHeatRow s t x y = _ at hy
      by_cases hyB : y ∈ B
      · simp only [Set.indicator_of_mem hyB, ENNReal.toReal_ofReal
          (le_trans hκ.le (h.2.2 y).1), smul_eq_mul]
        rw [hy, ← hs t ht x hx y hyb]
      · simp [hyB]
    _ = ∫ y in B, K t x y := by
      rw [integral_indicator hB, Measure.restrict_restrict hB,
        Set.inter_eq_left.mpr hBb]

#print axioms c12_supplied_row_mass_eq_kernel_mass

/-- Separated kernel mass decays faster than every polynomial at small
times, in the weighted L² norm of the starting point. -/
theorem c12_supplied_separated_kernel_mass_polynomial_decay {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAb : A ⊆ sourceBall 0 R) (hBb : B ⊆ sourceBall 0 R)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x-y)) (q : ℝ) :
    Tendsto (fun t : ℝ => t ^ (-q) *
      (∫ x in A, ρ x * (∫ y in B, K t x y)^2)) (𝓝[>] 0) (𝓝 0) := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hv : MemLp (fun _ : Vec d => (1 : ℝ)) 2 (dirichletVolume ρ R) :=
    memLp_const 1
  obtain ⟨C, hC, hDG⟩ := c12_native_weighted_davies_gaffney_of_two_le d hd κ R hκ hR
  let a : ℝ := δ ^ 2 / (8 * κ⁻¹ ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hlim : Tendsto (fun t : ℝ => t ^ (-q) * Real.exp (-a * t⁻¹) *
      (∫ y in B, ρ y)) (𝓝[>] 0) (𝓝 0) := by
    have htop := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q a ha).comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop)
    simpa only [Real.rpow_neg_eq_inv_rpow, Function.comp_apply, zero_mul] using
      htop.mul_const (∫ y in B, ρ y)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (integral_nonneg fun x =>
      mul_nonneg (le_trans hκ.le (h.2.2 x).1) (sq_nonneg _))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hb := hDG ρ α h K G hK A B hA hB hAb hBb δ t hδ ht hsep
      (fun _ => 1) hv
    have hb' := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le (-q))
    simpa [a, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hb'

#print axioms c12_supplied_separated_kernel_mass_polynomial_decay

/-- Along a subsequence of any positive times approaching zero, a polynomially
scaled separated kernel mass vanishes almost everywhere on the starting set. -/
theorem c12_supplied_separated_kernel_mass_ae_subsequence {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAb : A ⊆ sourceBall 0 R) (hBb : B ⊆ sourceBall 0 R)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x-y))
    (q : ℝ) (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (htlim : Tendsto t atTop (𝓝[>] 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂dirichletVolume ρ R, x ∈ A →
        Tendsto (fun n => (t (ns n)) ^ (-q) * ∫ y in B, K (t (ns n)) x y)
          atTop (𝓝 0) := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hv : MemLp (fun _ : Vec d => (1 : ℝ)) 2 (dirichletVolume ρ R) := memLp_const 1
  obtain ⟨s, hs⟩ := c12_supplied_kernel_heat_action_L2 hκ h K G hK
  let f : Lp ℝ 2 (dirichletVolume ρ R) := (hv.indicator hB).toLp (B.indicator fun _ => 1)
  let g (n : ℕ) : Lp ℝ 2 (dirichletVolume ρ R) :=
    SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun i => (s.eigenvalue_pos i).le) ⟨t n, (ht n).le⟩ f
  let u (n : ℕ) : Lp ℝ 2 (dirichletVolume ρ R) :=
    (t n) ^ (-q) • ((Lp.memLp (g n)).indicator hA).toLp (A.indicator fun x => g n x)
  have hg (n : ℕ) : (fun x => g n x) =ᵐ[dirichletVolume ρ R]
      fun x => ∫ y in B, K (t n) x y := by
    filter_upwards [hs ⟨t n, (ht n).le⟩ (ht n) f] with x hx
    change g n x = ∫ y in sourceBall (0 : Vec d) R, K (t n) x y * f y at hx
    rw [hx, c12_restricted_input_kernel_integral hκ h B hB hBb (fun _ => 1) hv]
    simp
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    change volume.restrict (sourceBall (0 : Vec d) R) ≪
      (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun y => ENNReal.ofReal (ρ y))
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun y => ne_of_gt
      (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hκ (h.2.2 y).1))
  have hnorm (n : ℕ) : ‖u n‖ ^ 2 = (t n) ^ (-(2*q)) *
      (∫ x in A, ρ x * (∫ y in B, K (t n) x y)^2) := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (ht n).le _), mul_pow,
      c12_dirichlet_restricted_norm_sq hκ h A hA hAb (fun x => g n x) (Lp.memLp (g n))]
    have hr : ((t n) ^ (-q)) ^ (2 : ℕ) = (t n) ^ (-(2*q)) := by
      rw [pow_two, ← Real.rpow_add (ht n)]
      congr 1 <;> ring
    rw [hr]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAb (hac.ae_le (hg n))] with x hx
    rw [hx]
  have hsq : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hnorm]
    exact (c12_supplied_separated_kernel_mass_polynomial_decay hd hκ hR h K G hK
      A B hA hB hAb hBb δ hδ hsep (2*q)).comp htlim
  have hu : Tendsto u atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    have hh := Real.continuous_sqrt.tendsto 0 |>.comp hsq
    convert hh using 1
    · funext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hrep : ∀ᵐ x ∂dirichletVolume ρ R, ∀ n, x ∈ A →
      u n x = (t n) ^ (-q) * ∫ y in B, K (t n) x y := by
    have he : ∀ n, ∀ᵐ x ∂dirichletVolume ρ R, x ∈ A →
        u n x = (t n) ^ (-q) * ∫ y in B, K (t n) x y := by
      intro n
      filter_upwards [Lp.coeFn_smul ((t n) ^ (-q))
        (((Lp.memLp (g n)).indicator hA).toLp (A.indicator fun x => g n x)),
        ((Lp.memLp (g n)).indicator hA).coeFn_toLp, hg n] with x hx hy hz hxA
      change u n x = _
      rw [hx]
      change (t n) ^ (-q) * (((Lp.memLp (g n)).indicator hA).toLp
        (A.indicator fun x => g n x)) x = _
      rw [hy, Set.indicator_of_mem hxA, hz]
    exact ae_all_iff.mpr he
  filter_upwards [hae, hrep, Lp.coeFn_zero ℝ 2 (dirichletVolume ρ R)] with x hx hr hz hxA
  have hx' : Tendsto (fun n => u (ns n) x) atTop (𝓝 0) := by
    simpa only [hz, Pi.zero_apply] using hx
  exact hx'.congr' (Filter.Eventually.of_forall fun n => hr (ns n) hxA)

#print axioms c12_supplied_separated_kernel_mass_ae_subsequence

/-- Finite iteration of the separated heat-flow tail estimate along decreasing
positive times and nested target sets. -/
theorem c12_supplied_spectral_heat_tail_iteration {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (x : Vec d) (hx : x ∈ sourceBall 0 R)
    (A : ℕ → Set (Vec d)) (hA : ∀ n, MeasurableSet (A n))
    (hAn : ∀ n, (A (n+1))ᶜ.Nonempty)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hsep : ∀ n, ∀ z ∈ A n, ∀ y ∈ (A (n+1))ᶜ,
      δ n ≤ euclideanNorm (z-y))
    (p : ℕ → ℝ≥0) (hp : ∀ n, 0 < p n)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (htstep : ∀ n, t n = (p n : ℝ) + t (n+1)) (N : ℕ) :
    let row := fun n => spectralHeatRow s (t n) x
    let restrict := fun n => ((Lp.memLp (row n)).indicator (hA n)).toLp
      ((A n).indicator fun z => row n z)
    ‖restrict 0‖ ≤ (∑ n ∈ Finset.range N,
      Real.exp (-(δ n ^ 2) / ((16 * κ⁻¹ ^ 2) * (p n : ℝ))) * ‖row (n+1)‖) +
        ‖restrict N‖ := by
  let row := fun n => spectralHeatRow s (t n) x
  let restrict := fun n => ((Lp.memLp (row n)).indicator (hA n)).toLp
    ((A n).indicator fun z => row n z)
  have hstep (n : ℕ) : ‖restrict n‖ ≤
      Real.exp (-(δ n ^ 2) / ((16 * κ⁻¹ ^ 2) * (p n : ℝ))) * ‖row (n+1)‖ +
        ‖restrict (n+1)‖ := by
    have hrow : SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun i => (s.eigenvalue_pos i).le) (p n) (row (n+1)) = row n := by
      dsimp only [row, spectralHeatRow]
      rw [c12_supplied_heat_operator_row s hspec (p n) (t (n+1)) (ht (n+1)) x hx,
        ← htstep n]
    have hbound := c12_supplied_spectral_heat_tail_step hd hκ h R hR s
      (A n) ((A (n+1))ᶜ) (hA n) (hA (n+1)).compl (hAn n)
      (δ n) (hδ n) (hsep n) (p n) (hp n) (row (n+1))
    dsimp only at hbound
    rw [hrow] at hbound
    simpa only [compl_compl] using hbound
  change ‖restrict 0‖ ≤ (∑ n ∈ Finset.range N,
    Real.exp (-(δ n ^ 2) / ((16 * κ⁻¹ ^ 2) * (p n : ℝ))) * ‖row (n+1)‖) +
      ‖restrict N‖
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep N]

#print axioms c12_supplied_spectral_heat_tail_iteration

/-- Geometric leakage terms have a uniform Gaussian bound when the
separation-to-time ratio is at least one. -/
theorem c12_geometric_gaussian_leakage_sum (r b : ℝ) (hr : 0 < r) (hb : 1 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 1 ≤ a → ∀ N : ℕ,
      (∑ n ∈ Finset.range N, r ^ n * Real.exp (-a * b ^ n)) ≤
        C * Real.exp (-a / 2) := by
  let f : ℕ → ℝ := fun n => r ^ n * Real.exp (-(b ^ n) / 2)
  have hfpos : ∀ n, 0 < f n := fun n => by dsimp [f]; positivity
  have hsum : Summable f := by
    refine summable_of_ratio_test_tendsto_lt_one (l := 0) one_pos
      (Eventually.of_forall fun n => (hfpos n).ne') ?_
    have hratio : ∀ n : ℕ, ‖f (n+1)‖ / ‖f n‖ =
        r * Real.exp (-((b-1)/2) * b ^ n) := by
      intro n
      rw [Real.norm_of_nonneg (hfpos _).le, Real.norm_of_nonneg (hfpos n).le,
        div_eq_iff (hfpos n).ne']
      dsimp only [f]
      have he : Real.exp (-(b ^ (n+1)) / 2) =
          Real.exp (-(b ^ n) / 2) * Real.exp (-((b-1)/2) * b ^ n) := by
        rw [← Real.exp_add, pow_succ]
        congr 1 <;> ring
      rw [he, pow_succ]
      ring
    simp_rw [hratio]
    have hc : 0 < (b-1)/2 := by linarith
    have hlim : Tendsto (fun n : ℕ => r * Real.exp (-((b-1)/2) * b ^ n))
        atTop (𝓝 (r * 0)) := by
      refine Tendsto.const_mul _ (Real.tendsto_exp_atBot.comp ?_)
      refine Filter.Tendsto.neg_mul_atTop (by linarith) tendsto_const_nhds ?_
      exact tendsto_pow_atTop_atTop_of_one_lt hb
    simpa using hlim
  let C : ℝ := 1 + ∑' n, f n
  have hC : 0 < C := by
    dsimp [C]
    have : 0 ≤ ∑' n, f n := tsum_nonneg (fun n => (hfpos n).le)
    linarith
  refine ⟨C, hC, ?_⟩
  intro a ha N
  have hterm (n : ℕ) : r ^ n * Real.exp (-a * b ^ n) ≤
      Real.exp (-a / 2) * f n := by
    have hbpow : 1 ≤ b ^ n := one_le_pow₀ hb.le
    have hp : 0 ≤ (a-1) * (b ^ n-1) := mul_nonneg (by linarith) (by linarith)
    have hexp : Real.exp (-a * b ^ n) ≤
        Real.exp (-a / 2) * Real.exp (-(b ^ n) / 2) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith
    dsimp [f]
    calc
      _ ≤ r ^ n * (Real.exp (-a / 2) * Real.exp (-(b ^ n) / 2)) :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt (pow_pos hr n))
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Finset.range N, Real.exp (-a / 2) * f n :=
      Finset.sum_le_sum fun n _ => hterm n
    _ = Real.exp (-a / 2) * ∑ n ∈ Finset.range N, f n := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-a / 2) * ∑' n, f n :=
      mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun n _ => (hfpos n).le))
        (Real.exp_pos _).le
    _ ≤ C * Real.exp (-a / 2) := by
      dsimp [C]
      have he := Real.exp_pos (-a / 2)
      nlinarith

#print axioms c12_geometric_gaussian_leakage_sum

end EinsteinFull.Calculus
