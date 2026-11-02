import EinsteinFull.Calculus.RadialTruncationSupport
import EinsteinFull.Calculus.ComplexGeneratorEnergySupport
import EinsteinFull.Calculus.ComplexForceDriftSupport

/-!
# Nonlinear radial testing on the actual generator domain

The bounded radial weight gives an integrable weighted Euclidean gradient
energy. Its full H1 chain rule and anisotropic pointwise coercivity pass to
actual reduced-law integrals. Testing the full unforced generator graph with
this admissible function then gives the nonlinear stationary energy bound.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The concrete saturated radial weight of an L2 representative is essentially bounded. -/
theorem memLp_radialTruncationWeight {d : ℕ} (μ : Measure (FieldPair d))
    (f : Lp ℂ 2 μ) {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    MemLp (fun ω => radialTruncationWeight ε R a (‖f ω‖ ^ 2)) ∞ μ := by
  have hc : Continuous (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2)) :=
    (continuousOn_radialTruncationWeight_slope (a := a) hε hR).1.comp_continuous
      (continuous_norm.pow 2) (fun z => sq_nonneg ‖z‖)
  apply memLp_top_of_bound (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
    ((ε + R) ^ a)
  exact Filter.Eventually.of_forall fun ω => by
    have hw : 0 ≤ radialTruncationWeight ε R a (‖f ω‖ ^ 2) :=
      Real.rpow_nonneg (radialTruncationBase_pos_le hε hR (sq_nonneg ‖f ω‖)).1.le _
    rw [Real.norm_eq_abs, abs_of_nonneg hw]
    exact Real.rpow_le_rpow
      (radialTruncationBase_pos_le hε hR (sq_nonneg ‖f ω‖)).1.le
      (radialTruncationBase_pos_le hε hR (sq_nonneg ‖f ω‖)).2 ha

/-- The actual bounded-weight Euclidean gradient energy is integrable. -/
theorem integrable_radialTruncation_energy {d : ℕ} (μ : Measure (FieldPair d))
    (f : Lp ℂ 2 μ) (G : Fin d → Lp ℂ 2 μ) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    Integrable (fun ω => radialTruncationWeight ε R a (‖f ω‖ ^ 2) *
      (∑ j, ‖G j ω‖ ^ 2)) μ := by
  simpa only [Pi.mul_apply, mul_comm] using! (integrable_finset_sum Finset.univ fun j _ =>
    (Lp.memLp (G j)).norm.integrable_sq).mul_of_top_left
      (memLp_radialTruncationWeight μ f hε hR ha)

/-- Integrated anisotropic coercivity for the literal radial-test gradient. -/
theorem radialTruncation_energy_lowerBound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q))
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a)
    (hH : ∀ j, H j =ᵐ[reducedLaw Q] fun ω =>
      complexRadialDifferential (radialTruncationWeight ε R a (‖f ω‖ ^ 2))
        (radialTruncationSlope ε R a (‖f ω‖ ^ 2)) (f ω) (G j ω)) :
    (Real.exp (2 * Λ₀) * Λ₀)⁻¹ *
      (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) *
        (∑ j, ‖G j ω‖ ^ 2) ∂reducedLaw Q) ≤
      (∫ ω, ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω
        ∂reducedLaw Q).re := by
  have hi := integrable_radialTruncation_energy (reducedLaw Q) f G hε hR ha
  have hE := integrable_reduced_complex_energy Q H G
  have hr : (∫ ω, (∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω).re
      ∂reducedLaw Q) = (∫ ω, ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω
      ∂reducedLaw Q).re := integral_re hE
  rw [← hr, ← integral_const_mul]
  apply integral_mono_ae (hi.const_mul _) hE.re
  filter_upwards [Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q,
    ae_all_iff.mpr hH] with ω hω hrep
  simp only [hrep]
  have hw : 0 ≤ radialTruncationWeight ε R a (‖f ω‖ ^ 2) :=
    Real.rpow_nonneg (radialTruncationBase_pos_le hε hR (sq_nonneg ‖f ω‖)).1.le _
  have hs := (radialTruncationSlope_mul_le hε hR ha (sq_nonneg ‖f ω‖)).1
  have hm : 0 ≤ (Real.exp (2 * Λ₀) * Λ₀)⁻¹ := inv_nonneg.mpr
    (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter))
  have hp := complexRadialDifferential_energy_lowerBound (ω.1 0)
    (Real.exp (2 * Λ₀) * Λ₀)⁻¹ _ _ hm hw hs (fun ξ => ((hω 0).2 ξ).1)
      (f ω) (fun j => G j ω)
  calc
    _ = radialTruncationWeight ε R a (‖f ω‖ ^ 2) *
        (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * (∑ j, ‖G j ω‖ ^ 2) := by ring
    _ ≤ _ := hp


private theorem radial_force_young (K b x y : ℝ) (hK : 0 < K) :
    b * y * x ≤ (K⁻¹ / 4) * x ^ 2 + K * b ^ 2 * y ^ 2 := by
  have h : 0 ≤ K⁻¹ * (x - 2 * K * b * y) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (inv_pos.mpr hK).le (sq_nonneg _)) (by norm_num)
  have he : K⁻¹ * (x - 2 * K * b * y) ^ 2 / 4 =
      (K⁻¹ / 4) * x ^ 2 + K * b ^ 2 * y ^ 2 - b * y * x := by
    field_simp
    ring
  rw [he] at h
  linarith only [h]

/-- The force term of a radial test is absorbed with the same bounded weight;
the remaining constant is independent of the radial cutoff. -/
theorem complexRadial_force_young {d : ℕ} (A : Mat d) (i : Fin d)
    (K b : ℝ) (hK : 0 < K) (hb : 0 ≤ b)
    (hA : ∀ j, |A j i| ≤ K) (ζ z : ℂ) (G : Fin d → ℂ) :
    (ζ * star (b • z) * (∑ j, (A j i : ℂ) * G j)).re ≤
      (K⁻¹ / 4) * b * (∑ j, ‖G j‖ ^ 2) +
        ((d : ℝ) * K * (‖ζ‖ * K) ^ 2) * b * ‖z‖ ^ 2 := by
  have hp (j : Fin d) : (ζ * star (b • z) * ((A j i : ℂ) * G j)).re ≤
      b * ((K⁻¹ / 4) * ‖G j‖ ^ 2 + K * (‖ζ‖ * K) ^ 2 * ‖z‖ ^ 2) := by
    have hn : ‖(A j i : ℂ)‖ ≤ K := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hA j
    calc
      _ ≤ ‖ζ * star (b • z) * ((A j i : ℂ) * G j)‖ := Complex.re_le_norm _
      _ = ‖ζ‖ * (b * ‖z‖) * (‖(A j i : ℂ)‖ * ‖G j‖) := by
        rw [norm_mul, norm_mul, norm_mul, norm_star, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hb]
      _ ≤ ‖ζ‖ * (b * ‖z‖) * (K * ‖G j‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
          (by positivity)
      _ = b * ((‖ζ‖ * K) * ‖z‖ * ‖G j‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (radial_force_young K (‖ζ‖ * K) ‖G j‖ ‖z‖ hK) hb
  calc
    _ = ∑ j, (ζ * star (b • z) * ((A j i : ℂ) * G j)).re := by
      rw [Finset.mul_sum]
      exact map_sum Complex.reAddGroupHom _ _
    _ ≤ ∑ j, b * ((K⁻¹ / 4) * ‖G j‖ ^ 2 +
        K * (‖ζ‖ * K) ^ 2 * ‖z‖ ^ 2) := Finset.sum_le_sum fun j _ => hp j
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Conjugate H1 testing of the full unforced graph retains the actual bilinear energy. -/
theorem IsComplexGeneratorPair.unforced_test {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (v : Lp ℂ 2 (reducedLaw Q)) (H : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H) :
    inner ℂ v g = -(1 / 2 : ℂ) * (∫ ω,
      ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q) := by
  obtain ⟨G', hG', hw⟩ := hfg
  have he : G' = G := hG'.unique hG
  subst G'
  have ht := hw (star v) (fun j => star (H j)) (fun j => (hv j).star)
  have hm : (∫ ω, g ω * (star v : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) =
      inner ℂ v g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v] with ω hω
    change (star v : Lp ℂ 2 (reducedLaw Q)) ω = star (v ω) at hω
    simp only [hω, RCLike.inner_apply, Complex.star_def]
  have hE : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω *
      (star (H j) : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr fun j => Lp.coeFn_star (H j)] with ω hω
    change ∀ j, (star (H j) : Lp ℂ 2 (reducedLaw Q)) ω = star (H j ω) at hω
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hω j]
    ring
  simpa only [hm, hE, zero_mul, add_zero] using ht

/-- Conjugate testing at any complex force uses the actual bounded column drift. -/
theorem IsComplexGeneratorPair.conjugate_test {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (v : Lp ℂ 2 (reducedLaw Q)) (H : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H) :
    inner ℂ v g = -(1 / 2 : ℂ) * (∫ ω,
      ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q) +
      ζ * inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 G)) := by
  have ht := (hfg.change_force 0 hG).unforced_test hG v H hv
  simp only [zero_sub, inner_add_right, inner_smul_right, neg_mul] at ht
  linear_combination ht

/-- The weighted mass term of the radial energy estimate is integrable. -/
theorem integrable_radialTruncation_mass {d : ℕ} (μ : Measure (FieldPair d))
    (f : Lp ℂ 2 μ) {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    Integrable (fun ω => radialTruncationWeight ε R a (‖f ω‖ ^ 2) * ‖f ω‖ ^ 2) μ := by
  simpa only [Pi.mul_apply, mul_comm] using!
    (Lp.memLp f).norm.integrable_sq.mul_of_top_left
      (memLp_radialTruncationWeight μ f hε hR ha)

/-- Integrated Young absorption of the actual force flux against the literal
radial test, with a constant independent of both truncation parameters. -/
theorem re_radialTruncation_force_pair_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f v : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a)
    (hv : v =ᵐ[reducedLaw Q] fun ω => radialTruncationWeight ε R a (‖f ω‖ ^ 2) • f ω) :
    (ζ * inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 G))).re ≤
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
        (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) *
          (∑ j, ‖G j ω‖ ^ 2) ∂reducedLaw Q) +
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
        (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) *
        (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) * ‖f ω‖ ^ 2 ∂reducedLaw Q) := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  let D := complexForceDrift Q i (WithLp.toLp 2 G)
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hD : D =ᵐ[reducedLaw Q] fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω :=
    complexForceDrift_coe Q i (WithLp.toLp 2 G)
  have hF : Integrable (fun ω => ζ * (star (v ω) * D ω)) (reducedLaw Q) :=
    ((Lp.memLp v).star.integrable_mul (Lp.memLp D)).const_mul ζ
  have hleft : (ζ * inner ℂ v D).re =
      ∫ ω, (ζ * (star (v ω) * D ω)).re ∂reducedLaw Q := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply, Complex.star_def]
    rw [← integral_const_mul]
    simpa only [Complex.star_def, mul_comm] using! (integral_re hF).symm
  rw [hleft, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_radialTruncation_energy (reducedLaw Q) f G hε hR ha).const_mul _)
      ((integrable_radialTruncation_mass (reducedLaw Q) f hε hR ha).const_mul _)]
  apply integral_mono_ae hF.re
    (((integrable_radialTruncation_energy (reducedLaw Q) f G hε hR ha).const_mul _).add
      ((integrable_radialTruncation_mass (reducedLaw Q) f hε hR ha).const_mul _))
  filter_upwards [hv, hD, Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q]
    with ω hvω hDω hω
  rw [hvω, hDω]
  have hcol (j : Fin d) : |ω.1 0 j i| ≤ K :=
    abs_entry_le_of_quadratic_bounds hK.le (ω.1 0) (hω 0).1
      (fun ξ => (mul_nonneg (inv_nonneg.mpr hK.le) (euclideanSq_nonneg_coords ξ)).trans
        ((hω 0).2 ξ).1) (fun ξ => ((hω 0).2 ξ).2) j i
  have hw : 0 ≤ radialTruncationWeight ε R a (‖f ω‖ ^ 2) :=
    Real.rpow_nonneg (radialTruncationBase_pos_le hε hR (sq_nonneg ‖f ω‖)).1.le _
  have hp := complexRadial_force_young (ω.1 0) i K _ hK hw hcol ζ (f ω)
    (fun j => G j ω)
  change (ζ * (star (radialTruncationWeight ε R a (‖f ω‖ ^ 2) • f ω) *
      (∑ j, (ω.1 0 j i : ℂ) * G j ω))).re ≤
    (K⁻¹ / 4) * (radialTruncationWeight ε R a (‖f ω‖ ^ 2) *
      (∑ j, ‖G j ω‖ ^ 2)) + ((d : ℝ) * K * (‖ζ‖ * K) ^ 2) *
        (radialTruncationWeight ε R a (‖f ω‖ ^ 2) * ‖f ω‖ ^ 2)
  calc
    _ = (ζ * star (radialTruncationWeight ε R a (‖f ω‖ ^ 2) • f ω) *
        (∑ j, (ω.1 0 j i : ℂ) * G j ω)).re := by congr 1; ring
    _ ≤ _ := hp
    _ = _ := by ring

/-- Every full unforced generator pair admits its actual nonlinear radial H1 test
and the resulting integrated weighted gradient coercivity bound. -/
theorem IsComplexGeneratorPair.unforced_radialTruncation_coercive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    ∃ (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (v : Lp ℂ 2 (reducedLaw Q))
      (H : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H ∧
      (v =ᵐ[reducedLaw Q] fun ω => radialTruncationWeight ε R a (‖f ω‖ ^ 2) • f ω) ∧
      (∀ j, H j =ᵐ[reducedLaw Q] fun ω =>
        complexRadialDifferential (radialTruncationWeight ε R a (‖f ω‖ ^ 2))
          (radialTruncationSlope ε R a (‖f ω‖ ^ 2)) (f ω) (G j ω)) ∧
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 2) *
        (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) *
          (∑ j, ‖G j ω‖ ^ 2) ∂reducedLaw Q) ≤ -(inner ℂ v g).re := by
  obtain ⟨G, hG, hw⟩ := hfg
  have hfg : IsComplexGeneratorPair Q i 0 f g := ⟨G, hG, hw⟩
  let hLip := lipschitzWith_radialTruncation hε hR ha
  let hzero : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
    by simp only [smul_zero]
  let v := hLip.compLp hzero f
  obtain ⟨H, hv, hH⟩ := hG.radialTruncation hε hR ha
  refine ⟨G, v, H, hG, hv, hLip.coeFn_compLp hzero f, hH, ?_⟩
  have ht := hfg.unforced_test hG v H hv
  have hb := radialTruncation_energy_lowerBound Q f G H hε hR ha hH
  have hr : (inner ℂ v g).re = -(1 / 2 : ℝ) *
      (∫ ω, ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω
        ∂reducedLaw Q).re := by
    rw [ht, Complex.mul_re]
    norm_num
  linarith only [hb, hr]

/-- The actual full forced graph retains nonlinear weighted coercivity after a
quadratic force shift, uniformly in the two radial cutoff parameters. -/
theorem IsComplexGeneratorPair.forced_radialTruncation_coercive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    ∃ (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (v : Lp ℂ 2 (reducedLaw Q))
      (H : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H ∧
      (v =ᵐ[reducedLaw Q] fun ω => radialTruncationWeight ε R a (‖f ω‖ ^ 2) • f ω) ∧
      (∀ j, H j =ᵐ[reducedLaw Q] fun ω =>
        complexRadialDifferential (radialTruncationWeight ε R a (‖f ω‖ ^ 2))
          (radialTruncationSlope ε R a (‖f ω‖ ^ 2)) (f ω) (G j ω)) ∧
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
        (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) *
          (∑ j, ‖G j ω‖ ^ 2) ∂reducedLaw Q) ≤ -(inner ℂ v g).re +
        ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) *
          (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) * ‖f ω‖ ^ 2 ∂reducedLaw Q) := by
  obtain ⟨G, hG, hw⟩ := hfg
  have hfg : IsComplexGeneratorPair Q i ζ f g := ⟨G, hG, hw⟩
  let hLip := lipschitzWith_radialTruncation hε hR ha
  let hzero : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
    by simp only [smul_zero]
  let v := hLip.compLp hzero f
  obtain ⟨H, hv, hH⟩ := hG.radialTruncation hε hR ha
  have hvrep := hLip.coeFn_compLp hzero f
  refine ⟨G, v, H, hG, hv, hvrep, hH, ?_⟩
  have ht := hfg.conjugate_test hG v H hv
  have hb := radialTruncation_energy_lowerBound Q f G H hε hR ha hH
  have hy := re_radialTruncation_force_pair_le Q i ζ f v G hε hR ha hvrep
  have hr : (inner ℂ v g).re = -(1 / 2 : ℝ) *
      (∫ ω, ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω
        ∂reducedLaw Q).re +
      (ζ * inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 G))).re := by
    rw [ht, Complex.add_re, Complex.mul_re]
    norm_num
  linarith only [hb, hy, hr]

end EinsteinFull
