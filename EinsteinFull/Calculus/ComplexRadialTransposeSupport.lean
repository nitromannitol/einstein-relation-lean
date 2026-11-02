import EinsteinFull.Calculus.ComplexRadialGeneratorSupport

/-!
# Nonlinear radial force estimates for bilinear transposition

The transposed drift differentiates the radial test. Its relative differential
bound costs `1 + 2*a`, while Young absorption keeps the same positive weighted
Euclidean energy and a force shift independent of both radial cutoffs.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private theorem transpose_radial_young (K b x y : ℝ) (hK : 0 < K) :
    b * y * x ≤ (K⁻¹ / 4) * x ^ 2 + K * b ^ 2 * y ^ 2 := by
  have h : 0 ≤ K⁻¹ * (x - 2 * K * b * y) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (inv_pos.mpr hK).le (sq_nonneg _)) (by norm_num)
  have he : K⁻¹ * (x - 2 * K * b * y) ^ 2 / 4 =
      (K⁻¹ / 4) * x ^ 2 + K * b ^ 2 * y ^ 2 - b * y * x := by
    field_simp
    ring
  rw [he] at h
  linarith only [h]

/-- Pointwise absorption for the actual transposed force: the derivative falls
on the radial test, retaining every anisotropic coefficient in the column. -/
theorem complexRadial_transpose_force_young {d : ℕ} (A : Mat d) (i : Fin d)
    (K : ℝ) (hK : 0 < K) (hA : ∀ j, |A j i| ≤ K)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a)
    (ζ z : ℂ) (G : Fin d → ℂ) :
    (ζ * z * (∑ j, (A j i : ℂ) * star
      (complexRadialDifferential (radialTruncationWeight ε R a (‖z‖ ^ 2))
        (radialTruncationSlope ε R a (‖z‖ ^ 2)) z (G j)))).re ≤
      (K⁻¹ / 4) * radialTruncationWeight ε R a (‖z‖ ^ 2) * (∑ j, ‖G j‖ ^ 2) +
        ((d : ℝ) * K * (‖ζ‖ * K * (1 + 2 * a)) ^ 2) *
          radialTruncationWeight ε R a (‖z‖ ^ 2) * ‖z‖ ^ 2 := by
  let b := radialTruncationWeight ε R a (‖z‖ ^ 2)
  let D := complexRadialDifferential b (radialTruncationSlope ε R a (‖z‖ ^ 2)) z
  have hb : 0 ≤ b :=
    Real.rpow_nonneg (radialTruncationBase_pos_le hε hR (sq_nonneg ‖z‖)).1.le _
  have hD (j : Fin d) : ‖D (G j)‖ ≤ ((1 + 2 * a) * b) * ‖G j‖ :=
    (D.le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (norm_radialTruncationDifferential_le hε hR ha z) (norm_nonneg _))
  have hp (j : Fin d) : (ζ * z * ((A j i : ℂ) * star (D (G j)))).re ≤
      b * ((K⁻¹ / 4) * ‖G j‖ ^ 2 +
        K * (‖ζ‖ * K * (1 + 2 * a)) ^ 2 * ‖z‖ ^ 2) := by
    have hn : ‖(A j i : ℂ)‖ ≤ K := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hA j
    calc
      _ ≤ ‖ζ * z * ((A j i : ℂ) * star (D (G j)))‖ := Complex.re_le_norm _
      _ = ‖ζ‖ * ‖z‖ * (‖(A j i : ℂ)‖ * ‖D (G j)‖) := by
        simp only [norm_mul, norm_star]
      _ ≤ ‖ζ‖ * ‖z‖ * (K * (((1 + 2 * a) * b) * ‖G j‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hn (hD j) (norm_nonneg _) hK.le) (by positivity)
      _ = b * ((‖ζ‖ * K * (1 + 2 * a)) * ‖z‖ * ‖G j‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (transpose_radial_young K (‖ζ‖ * K * (1 + 2 * a)) ‖G j‖ ‖z‖ hK) hb
  calc
    _ = ∑ j, (ζ * z * ((A j i : ℂ) * star (D (G j)))).re := by
      rw [Finset.mul_sum]
      exact map_sum Complex.reAddGroupHom _ _
    _ ≤ ∑ j, b * ((K⁻¹ / 4) * ‖G j‖ ^ 2 +
        K * (‖ζ‖ * K * (1 + 2 * a)) ^ 2 * ‖z‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hp j
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Integrated transposed-force absorption for the literal radial-test gradient.
The constant depends on the power and structural ellipticity, not the cutoffs. -/
theorem re_radialTruncation_transpose_force_pair_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (G H : Fin d → Lp ℂ 2 (reducedLaw Q))
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a)
    (hH : ∀ j, H j =ᵐ[reducedLaw Q] fun ω =>
      complexRadialDifferential (radialTruncationWeight ε R a (‖f ω‖ ^ 2))
        (radialTruncationSlope ε R a (‖f ω‖ ^ 2)) (f ω) (G j ω)) :
    (ζ * inner ℂ (complexForceDrift Q i (WithLp.toLp 2 H)) f).re ≤
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
        (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) *
          (∑ j, ‖G j ω‖ ^ 2) ∂reducedLaw Q) +
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
        (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2) *
        (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) * ‖f ω‖ ^ 2 ∂reducedLaw Q) := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  let D := complexForceDrift Q i (WithLp.toLp 2 H)
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hD : D =ᵐ[reducedLaw Q] fun ω => ∑ j, (ω.1 0 j i : ℂ) * H j ω :=
    complexForceDrift_coe Q i (WithLp.toLp 2 H)
  have hF : Integrable (fun ω => ζ * (star (D ω) * f ω)) (reducedLaw Q) :=
    ((Lp.memLp D).star.integrable_mul (Lp.memLp f)).const_mul ζ
  have hleft : (ζ * inner ℂ D f).re =
      ∫ ω, (ζ * (star (D ω) * f ω)).re ∂reducedLaw Q := by
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
  filter_upwards [ae_all_iff.mpr hH, hD, Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q]
    with ω hHω hDω hω
  rw [hDω]
  simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal, hHω,
    RCLike.re_to_complex]
  have hcol (j : Fin d) : |ω.1 0 j i| ≤ K :=
    abs_entry_le_of_quadratic_bounds hK.le (ω.1 0) (hω 0).1
      (fun ξ => (mul_nonneg (inv_nonneg.mpr hK.le) (euclideanSq_nonneg_coords ξ)).trans
        ((hω 0).2 ξ).1) (fun ξ => ((hω 0).2 ξ).2) j i
  have hp := complexRadial_transpose_force_young (ω.1 0) i K hK hcol hε hR ha ζ
    (f ω) (fun j => G j ω)
  have hsum : (∑ j, star
      (complexRadialDifferential (radialTruncationWeight ε R a (‖f ω‖ ^ 2))
        (radialTruncationSlope ε R a (‖f ω‖ ^ 2)) (f ω) (G j ω)) * (ω.1 0 j i : ℂ)) =
      ∑ j, (ω.1 0 j i : ℂ) * star
        (complexRadialDifferential (radialTruncationWeight ε R a (‖f ω‖ ^ 2))
          (radialTruncationSlope ε R a (‖f ω‖ ^ 2)) (f ω) (G j ω)) :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [Complex.star_def] at hsum
  rw [hsum]
  simp only [Complex.star_def] at hp
  convert! hp using 1 <;> try dsimp only [K, Pi.add_apply, Pi.mul_apply]
  · congr 1
    ring
  · ring

/-- The full horizontal H1 weak graph of the bilinear transposed differential
expression. The drift differentiates every test. This definition does not
assert identification with the transpose of a semigroup generator. -/
def IsComplexTransposeGeneratorPair {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f g : Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∃ Gf : Fin d → Lp ℂ 2 (reducedLaw Q),
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f Gf ∧
    ∀ (v : Lp ℂ 2 (reducedLaw Q)) (Gv : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v Gv →
      (∫ ω, g ω * v ω ∂reducedLaw Q) =
        -(1 / 2 : ℂ) * (∫ ω,
          ∑ j, ∑ k, (ω.1 0 j k : ℂ) * Gf k ω * Gv j ω ∂reducedLaw Q) +
        ζ * (∫ ω, f ω * (∑ j, (ω.1 0 j i : ℂ) * Gv j ω) ∂reducedLaw Q)

/-- At zero force the two full weak H1 graphs are literally the same. -/
theorem isComplexTransposeGeneratorPair_zero_iff {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexTransposeGeneratorPair Q i 0 f g ↔ IsComplexGeneratorPair Q i 0 f g := by
  simp only [IsComplexTransposeGeneratorPair, IsComplexGeneratorPair,
    zero_mul, add_zero]

/-- The full weak transpose graph is contained in the actual bilinear adjoint
of the full forward graph. Symmetry is taken only almost everywhere. -/
theorem IsComplexTransposeGeneratorPair.bilinear_duality
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g u v : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (huv : IsComplexGeneratorPair Q i ζ u v) :
    (∫ ω, g ω * u ω ∂reducedLaw Q) = ∫ ω, f ω * v ω ∂reducedLaw Q := by
  obtain ⟨Gf, hGf, hwf⟩ := hfg
  obtain ⟨Gu, hGu, hwu⟩ := huv
  have ht := hwf u Gu hGu
  have hu := hwu f Gf hGf
  have hE : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * Gf k ω * Gu j ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * Gu k ω * Gf j ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hω
    have hs (j k : Fin d) : ω.1 0 j k = ω.1 0 k j :=
      congrArg (fun M : Mat d => M k j) (hω 0).1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hs k j]
    ring
  have hF : (∫ ω, f ω * (∑ j, (ω.1 0 j i : ℂ) * Gu j ω) ∂reducedLaw Q) =
      ∫ ω, (∑ j, (ω.1 0 j i : ℂ) * Gu j ω) * f ω ∂reducedLaw Q :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  calc
    _ = _ := ht
    _ = ∫ ω, v ω * f ω ∂reducedLaw Q := by rw [hE, hF]; exact hu.symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

/-- Conjugate testing of the entire transpose weak H1 graph gives the principal
energy and the column drift applied to the test gradient. -/
theorem IsComplexTransposeGeneratorPair.conjugate_test
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (v : Lp ℂ 2 (reducedLaw Q)) (H : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H) :
    inner ℂ v g = -(1 / 2 : ℂ) * (∫ ω,
      ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q) +
      ζ * inner ℂ (complexForceDrift Q i (WithLp.toLp 2 H)) f := by
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
  have hT : (∫ ω, f ω * (∑ j, (ω.1 0 j i : ℂ) *
      (star (H j) : Lp ℂ 2 (reducedLaw Q)) ω) ∂reducedLaw Q) =
      inner ℂ (complexForceDrift Q i (WithLp.toLp 2 H)) f := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [complexForceDrift_coe Q i (WithLp.toLp 2 H),
      ae_all_iff.mpr fun j => Lp.coeFn_star (H j)] with ω hD hstar
    change ∀ j, (star (H j) : Lp ℂ 2 (reducedLaw Q)) ω = star (H j ω) at hstar
    rw [hD]
    simp only [RCLike.inner_apply, Complex.star_def, hstar, map_sum, map_mul,
      Complex.conj_ofReal, Finset.mul_sum]
  simpa only [hm, hE, hT] using ht

/-- Every pair in the full transpose weak H1 graph admits the nonlinear radial
test and cutoff-independent weighted gradient absorption. -/
theorem IsComplexTransposeGeneratorPair.radialTruncation_coercive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
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
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2) *
          (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) * ‖f ω‖ ^ 2 ∂reducedLaw Q) := by
  obtain ⟨G, hG, hw⟩ := hfg
  have hfg : IsComplexTransposeGeneratorPair Q i ζ f g := ⟨G, hG, hw⟩
  let hLip := lipschitzWith_radialTruncation hε hR ha
  let hzero : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
    by simp only [smul_zero]
  let v := hLip.compLp hzero f
  obtain ⟨H, hv, hH⟩ := hG.radialTruncation hε hR ha
  have hvrep := hLip.coeFn_compLp hzero f
  refine ⟨G, v, H, hG, hv, hvrep, hH, ?_⟩
  have ht := hfg.conjugate_test hG v H hv
  have hb := radialTruncation_energy_lowerBound Q f G H hε hR ha hH
  have hy := re_radialTruncation_transpose_force_pair_le Q i ζ f G H hε hR ha hH
  have hr : (inner ℂ v g).re = -(1 / 2 : ℝ) *
      (∫ ω, ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω
        ∂reducedLaw Q).re +
      (ζ * inner ℂ (complexForceDrift Q i (WithLp.toLp 2 H)) f).re := by
    rw [ht, Complex.add_re, Complex.mul_re]
    norm_num
  linarith only [hb, hy, hr]

end EinsteinFull
