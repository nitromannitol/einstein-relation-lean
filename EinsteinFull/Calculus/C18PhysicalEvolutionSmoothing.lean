import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds_u23_derivatives
import EinsteinFull.Calculus.C4PhysicalForwardTimePrimitive
import EinsteinFull.Calculus.C8PhysicalTransposeTimePrimitive
import EinsteinFull.Calculus.C4PhysicalOrbitGradientContinuity
import EinsteinFull.Calculus.C4PhysicalH1TimePrimitive
import EinsteinFull.Calculus.PhysicalFormCoefficientSupport
import EinsteinFull.Calculus.ComplexLpChainSupport
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import EinsteinRelation.Calculus.ClassicalSpatialDerivative
import PDEFoundation.Sobolev.WeakDerivative.Affine
import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceDensity
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.DiffQuotientLp

open MeasureTheory
open scoped NNReal ENNReal BigOperators Topology

namespace EinsteinFull
open EinsteinRelation

/-- The unweighted estimate on one event for the actual forward and transpose
evolutions. The constant is chosen before the law and the event before the
direction, force, evolution and datum. This supplies the global L2 input to
the remaining spatial regularity argument. -/
theorem c18_physical_evolution_L2_bound
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ r₀), ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      ‖S t f‖ ≤ Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖ := by
  obtain ⟨C, c, hC, _hc, h⟩ := hoff d hd Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro r₀ Q
  filter_upwards [h r₀ Q] with ω hω
  intro i ζ P Pdag hP hPdag S hS t ht f
  have hb := ((hω i ζ P Pdag hP hPdag S hS t ht).2
    Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ 0 le_rfl
    (by intros; exact Real.sqrt_nonneg _) f
    (Filter.Eventually.of_forall (by simp))).2
  simpa only [Set.indicator_univ, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_div, sub_zero, ← Lp.norm_def] using hb

/-- The deterministic derivative sequence and L2 growth bound hold on the same
event, uniformly over both physical evolutions and all complex forces. -/
theorem c18_physical_evolution_smooth_L2_event
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ M : ℕ → ℝ, 1 ≤ C ∧
      (∀ k : ℕ, 1 ≤ k → 0 < M k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
      IsSmoothWithBounds M ω ∧
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      ‖S t f‖ ≤ Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖ := by
  obtain ⟨C, hC, hL2⟩ := c18_physical_evolution_L2_bound hoff d hd
    D.ellipticity D.one_le_ellipticity
  obtain ⟨M, hM, hsmooth⟩ := hder d D
  refine ⟨C, M, hC, hM, ?_⟩
  intro Q hQ
  filter_upwards [hsmooth Q hQ, hL2 D.dependenceRange Q] with ω hω hbound
  exact ⟨hω, hbound⟩

/-- A bounded physical orbit has a quantitative H1 time primitive, for both
the forward evolution and its actual bilinear transpose. No generator-domain
condition is imposed on the initial datum. -/
theorem c18_physical_time_primitive_H1_bound
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    (S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (hS : S ∈ [P, Pdag])
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0)
    (B : ℝ) (hbound : ∀ s : ℝ≥0, s ≤ t → ‖S s f‖ ≤ B) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl)
        (∫ s in (0 : ℝ)..(t : ℝ), S s.toNNReal f) G ∧
      (∑ j, ‖G j‖ ^ 2) ≤
        4 * Λ * (B * (t : ℝ)) * (B + ‖f‖) +
          4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * ‖ζ‖ ^ 2 * (B * (t : ℝ)) ^ 2 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbound 0 zero_le)
  have hu : ‖∫ s in (0 : ℝ)..(t : ℝ), S s.toNNReal f‖ ≤ B * (t : ℝ) := by
    have hb : ∀ s ∈ Set.uIoc (0 : ℝ) (t : ℝ), ‖S s.toNNReal f‖ ≤ B := by
      intro s hs
      have hs' : s ≤ (t : ℝ) :=
        (Set.uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property) ▸ hs).2
      exact hbound s.toNNReal (by simpa using Real.toNNReal_le_toNNReal hs')
    simpa only [sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hg : ‖S t f - f‖ ≤ B + ‖f‖ :=
    (norm_sub_le _ _).trans (add_le_add (hbound t le_rfl) le_rfl)
  have hgraph : ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl)
        (∫ s in (0 : ℝ)..(t : ℝ), S s.toNNReal f) G ∧
      (∑ j, ‖G j‖ ^ 2) ≤
        4 * Λ * ‖∫ s in (0 : ℝ)..(t : ℝ), S s.toNNReal f‖ * ‖S t f - f‖ +
          4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * ‖ζ‖ ^ 2 *
            ‖∫ s in (0 : ℝ)..(t : ℝ), S s.toNNReal f‖ ^ 2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with hS | hS
    · rw [hS]
      exact Blueprint.physical_complex_generator_gradient_bound a i ζ ha hΛ hA
        (Blueprint.physical_forward_generator_timeIntegral a i ζ P hP f t)
    · rw [hS]
      exact Blueprint.physical_complex_transpose_generator_gradient_bound a i ζ ha hΛ hA
        (Blueprint.physical_transpose_generator_timeIntegral a i ζ P Pdag hPdag f t)
  obtain ⟨G, hG, hgrad⟩ := hgraph
  refine ⟨G, hG, hgrad.trans ?_⟩
  apply add_le_add
  · exact mul_le_mul
      (mul_le_mul_of_nonneg_left hu (by positivity)) hg (norm_nonneg _)
      (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB t.property) |>.mpr hu)
      (by positivity)

open Blueprint EinsteinRelation.External.AKM

/-- The forward physical graph retains its coercive gradient term when
one keeps the signed real energy pairing. -/
theorem c18_physical_generator_coercive
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) u G ∧
      (1 / (4 * Λ)) * (∑ j, ‖G j‖ ^ 2) ≤ -(inner ℂ u g).re +
        ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u‖ ^ 2 := by
  classical
  obtain ⟨G, hG, hweak⟩ := hug
  refine ⟨G, hG, ?_⟩
  let Q : Vec d → ℂ := fun x => ∑ j, ∑ k,
    (a x j k : ℂ) * G k x * star (G j x)
  let F : Vec d → ℂ := fun x => (∑ j, (a x j i : ℂ) * G j x) * star (u x)
  have hQi : Integrable Q volume := by
    apply integrable_finsetSum Finset.univ
    intro j _
    apply integrable_finsetSum Finset.univ
    intro k _
    exact ((ha j k).mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (G j)).star
  have hFi : Integrable F volume := by
    have hcol : MemLp (fun x => ∑ j, (a x j i : ℂ) * G j x) 2 volume :=
      memLp_finsetSum _ fun j _ => (ha j i).mul (r := 2) (Lp.memLp (G j))
    exact hcol.integrable_mul (Lp.memLp u).star
  have hN : Integrable (fun x => ∑ j, ‖G j x‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq
  have hU : Integrable (fun x => ‖u x‖ ^ 2) volume := (Lp.memLp u).norm.integrable_sq
  have hpoint : ∀ᵐ x ∂volume,
      (1 / (4 * Λ)) * (∑ j, ‖G j x‖ ^ 2) ≤
        -((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re +
          ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u x‖ ^ 2 := by
    filter_upwards [hA] with x hx
    have hc := s5_coercive hx (fun j => G j x)
    have hf := physicalForceColumn_young (a x) i Λ Λ hΛ
      (fun j => hx.entry_abs_le j i) (ζ * star (u x)) (fun j => G j x)
    have he : ζ * F x = (ζ * star (u x)) * (∑ j, (a x j i : ℂ) * G j x) := by
      dsimp only [F]; ring
    rw [← he] at hf
    simp only [norm_mul, norm_star, mul_pow] at hf
    have hr := Complex.re_le_norm (ζ * F x)
    rw [norm_mul] at hr
    change Λ⁻¹ * (∑ j, ‖G j x‖ ^ 2) ≤ (Q x).re at hc
    have hreal : ((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re =
        -(1 / 2 : ℝ) * (Q x).re + (ζ * F x).re := by simp [Complex.mul_re]
    rw [hreal]
    have hinv : Λ⁻¹ = 4 * (1 / (4 * Λ)) := by field_simp
    rw [hinv] at hc
    nlinarith only [hc, hf, hr]
  have hT : Integrable (fun x => (1 / 2 : ℂ) * Q x * (-1) + ζ * F x) volume :=
    ((hQi.const_mul _).mul_const _).add (hFi.const_mul _)
  have hi := integral_mono_ae (hN.const_mul (1 / (4 * Λ)))
    (hT.re.neg.add (hU.const_mul ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2))) hpoint
  have hNeq : (∫ x, ∑ j, ‖G j x‖ ^ 2) = ∑ j, ‖G j‖ ^ 2 := by
    rw [integral_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq]
    exact Finset.sum_congr rfl fun j _ => (physicalL2_norm_sq volume (G j)).symm
  have htest := hweak (star u) (fun j => star (G j)) (physicalH1Graph_star u G hG)
  have hQa : (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * (star (G j)) x) = ∫ x, Q x := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (G j))] with x hx
    simp only [Q, hx, Pi.star_apply]
  have hFa : (∫ x, (∑ j, (a x j i : ℂ) * G j x) * (star u) x) = ∫ x, F x := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star u] with x hx
    rw [hx]; rfl
  rw [hQa, hFa] at htest
  have hTeq : (∫ x, (1 / 2 : ℂ) * Q x * (-1) + ζ * F x) = ∫ x, g x * (star u) x := by
    rw [integral_add ((hQi.const_mul _).mul_const _) (hFi.const_mul _),
      integral_mul_const, integral_const_mul, integral_const_mul, htest]
    ring
  have hpair : (∫ x, g x * (star u) x) = inner ℂ u g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star u] with x hx
    simp only [hx, RCLike.inner_apply, Pi.star_apply, Complex.star_def, mul_comm]
  have hrealint := integral_re hT
  simp only [RCLike.re_eq_complex_re] at hrealint
  simp only [Pi.add_apply, Pi.neg_apply, RCLike.re_eq_complex_re] at hi
  rw [integral_const_mul, hNeq, integral_add (f := fun x => -((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re)
      (g := fun x => ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u x‖ ^ 2)
      hT.re.neg (hU.const_mul _),
    integral_neg, hrealint, hTeq, hpair, integral_const_mul,
    ← physicalL2_norm_sq] at hi
  exact hi

/-- The bilinear transpose physical graph retains its coercive gradient term when
one keeps the signed real energy pairing. -/
theorem c18_physical_transpose_generator_coercive
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) u G ∧
      (1 / (4 * Λ)) * (∑ j, ‖G j‖ ^ 2) ≤ -(inner ℂ u g).re +
        ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u‖ ^ 2 := by
  classical
  obtain ⟨G, hG, hweak⟩ := hug
  refine ⟨G, hG, ?_⟩
  let Q : Vec d → ℂ := fun x => ∑ j, ∑ k,
    (a x k j : ℂ) * G k x * star (G j x)
  let F : Vec d → ℂ := fun x => u x * (∑ j, (a x j i : ℂ) * star (G j x))
  have hQi : Integrable Q volume := by
    apply integrable_finsetSum Finset.univ
    intro j _
    apply integrable_finsetSum Finset.univ
    intro k _
    exact ((ha k j).mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (G j)).star
  have hFi : Integrable F volume := by
    have hcol : MemLp (fun x => ∑ j, (a x j i : ℂ) * star (G j x)) 2 volume :=
      memLp_finsetSum _ fun j _ => (ha j i).mul (r := 2) (Lp.memLp (G j)).star
    exact (Lp.memLp u).integrable_mul hcol
  have hN : Integrable (fun x => ∑ j, ‖G j x‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq
  have hU : Integrable (fun x => ‖u x‖ ^ 2) volume := (Lp.memLp u).norm.integrable_sq
  have hpoint : ∀ᵐ x ∂volume,
      (1 / (4 * Λ)) * (∑ j, ‖G j x‖ ^ 2) ≤
        -((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re +
          ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u x‖ ^ 2 := by
    filter_upwards [hA] with x hx
    have hc := s5_coercive hx (fun j => star (G j x))
    have hQ : (∑ j, ∑ k, (a x j k : ℂ) * star (G k x) *
        (starRingEnd ℂ) (star (G j x))) = Q x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      simp only [starRingEnd_apply, star_star]
      ring
    rw [hQ] at hc
    simp only [norm_star] at hc
    have hf := physicalForceColumn_young (a x) i Λ Λ hΛ
      (fun j => hx.entry_abs_le j i) (ζ * u x) (fun j => star (G j x))
    have he : ζ * F x = (ζ * u x) * (∑ j, (a x j i : ℂ) * star (G j x)) := by
      dsimp only [F]; ring
    rw [← he] at hf
    simp only [norm_mul, norm_star, mul_pow] at hf
    have hr := Complex.re_le_norm (ζ * F x)
    rw [norm_mul] at hr
    change Λ⁻¹ * (∑ j, ‖G j x‖ ^ 2) ≤ (Q x).re at hc
    have hreal : ((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re =
        -(1 / 2 : ℝ) * (Q x).re + (ζ * F x).re := by simp [Complex.mul_re]
    rw [hreal]
    have hinv : Λ⁻¹ = 4 * (1 / (4 * Λ)) := by field_simp
    rw [hinv] at hc
    nlinarith only [hc, hf, hr]
  have hT : Integrable (fun x => (1 / 2 : ℂ) * Q x * (-1) + ζ * F x) volume :=
    ((hQi.const_mul _).mul_const _).add (hFi.const_mul _)
  have hi := integral_mono_ae (hN.const_mul (1 / (4 * Λ)))
    (hT.re.neg.add (hU.const_mul ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2))) hpoint
  have hNeq : (∫ x, ∑ j, ‖G j x‖ ^ 2) = ∑ j, ‖G j‖ ^ 2 := by
    rw [integral_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq]
    exact Finset.sum_congr rfl fun j _ => (physicalL2_norm_sq volume (G j)).symm
  have htest := hweak (star u) (fun j => star (G j)) (physicalH1Graph_star u G hG)
  have hQa : (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * (star (G j)) x) = ∫ x, Q x := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (G j))] with x hx
    simp only [Q, hx, Pi.star_apply]
  have hFa : (∫ x, u x * (∑ j, (a x j i : ℂ) * (star (G j)) x)) = ∫ x, F x := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (G j))] with x hx
    simp only [F, hx, Pi.star_apply]
  rw [hQa, hFa] at htest
  have hTeq : (∫ x, (1 / 2 : ℂ) * Q x * (-1) + ζ * F x) = ∫ x, g x * (star u) x := by
    rw [integral_add ((hQi.const_mul _).mul_const _) (hFi.const_mul _),
      integral_mul_const, integral_const_mul, integral_const_mul, htest]
    ring
  have hpair : (∫ x, g x * (star u) x) = inner ℂ u g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star u] with x hx
    simp only [hx, RCLike.inner_apply, Pi.star_apply, Complex.star_def, mul_comm]
  have hrealint := integral_re hT
  simp only [RCLike.re_eq_complex_re] at hrealint
  simp only [Pi.add_apply, Pi.neg_apply, RCLike.re_eq_complex_re] at hi
  rw [integral_const_mul, hNeq, integral_add (f := fun x => -((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re)
      (g := fun x => ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u x‖ ^ 2)
      hT.re.neg (hU.const_mul _),
    integral_neg, hrealint, hTeq, hpair, integral_const_mul,
    ← physicalL2_norm_sq] at hi
  exact hi

/-- The exact integrated L2 energy identity for a generator-domain orbit.
The same identity applies to the physical forward and transpose semigroups. -/
theorem c18_semigroup_energy_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) {f g : E} (hfg : Gen f g) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ),
      2 * (inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re) =
        ‖P t f‖ ^ 2 - ‖f‖ ^ 2 := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hP.cont f).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => P s.toNNReal g) :=
    (hP.cont g).comp continuous_real_toNNReal
  have hder : ∀ s ∈ Set.Ioo (0 : ℝ) (t : ℝ),
      HasDerivWithinAt (fun r : ℝ => ‖P r.toNNReal f‖ ^ 2)
        (2 * (inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re) (Set.Ioi s) s := by
    intro s hs
    have hd := (hP.hasDerivWithinAt_orbit hfg s hs.1.le).norm_sq
    change HasDerivWithinAt (fun r : ℝ => ‖P r.toNNReal f‖ ^ 2)
      (2 * (inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re) (Set.Ici s) s at hd
    exact hd.mono Set.Ioi_subset_Ici_self
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (show (0 : ℝ) ≤ (t : ℝ) from t.property) (hu.norm.pow 2).continuousOn
    hder (((Complex.continuous_re.comp (hu.inner (𝕜 := ℂ) hv)).const_mul 2).intervalIntegrable 0 t)
  simpa only [Pi.pow_apply, Real.toNNReal_coe, Real.toNNReal_zero, hP.zero,
    ContinuousLinearMap.id_apply] using hi

private theorem c18_integrated_gradient_energy
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) {f g : E} (hfg : Gen f g)
    (G : ℝ → Fin d → E) (hG : ∀ j, Continuous (fun s => G s j)) (μ K : ℝ)
    (hcoer : ∀ s : ℝ, μ * (∑ j, ‖G s j‖ ^ 2) ≤
      -(inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re + K * ‖P s.toNNReal f‖ ^ 2)
    (t : ℝ≥0) :
    μ * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
      (‖f‖ ^ 2 - ‖P t f‖ ^ 2) / 2 +
        K * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2) := by
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hP.cont f).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => P s.toNNReal g) :=
    (hP.cont g).comp continuous_real_toNNReal
  have hc := Complex.continuous_re.comp (hu.inner (𝕜 := ℂ) hv)
  have hn : Continuous (fun s => ∑ j, ‖G s j‖ ^ 2) :=
    continuous_finset_sum _ fun j _ => (hG j).norm.pow 2
  have hleft := (hn.const_mul μ).intervalIntegrable (μ := (volume : Measure ℝ))
    (0 : ℝ) (t : ℝ)
  have hneg : IntervalIntegrable
      (fun s : ℝ => -(inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re)
      volume 0 t := hc.neg.intervalIntegrable 0 t
  have hK : IntervalIntegrable (fun s : ℝ => K * ‖P s.toNNReal f‖ ^ 2)
      volume 0 t := ((hu.norm.pow 2).const_mul K).intervalIntegrable 0 t
  have hright := hneg.add hK
  have hi := intervalIntegral.integral_mono
    (show (0 : ℝ) ≤ (t : ℝ) from t.property) hleft hright hcoer
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hneg hK,
    intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hi
  have he := c18_semigroup_energy_identity hP hfg t
  rw [intervalIntegral.integral_const_mul] at he
  nlinarith only [hi, he]

/-- The integrated coercive gradient estimate for an actual forward
physical orbit starting in the generator domain. Its right side contains no
norm of the initial generator image. -/
theorem c18_physical_orbit_integrated_gradient
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexSemigroup a i ζ S)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ t : ℝ≥0,
        (1 / (4 * Λ)) * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
          (‖f‖ ^ 2 - ‖S t f‖ ^ 2) / 2 +
            ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) *
              (∫ s in (0 : ℝ)..(t : ℝ), ‖S s.toNNReal f‖ ^ 2) := by
  have hsem : S5Semigroup S (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2⟩
  obtain ⟨G, hG, hGc⟩ := physical_generator_orbit_continuous_gradient a i ζ ha hΛ hA
    (fun s : ℝ => S s.toNNReal f) (fun s : ℝ => S s.toNNReal g)
    ((hsem.cont f).comp continuous_real_toNNReal)
    ((hsem.cont g).comp continuous_real_toNNReal)
    (fun s => hsem.map_gen hfg s.toNNReal)
  refine ⟨G, hG, hGc, fun t => c18_integrated_gradient_energy hsem hfg G hGc
    (1 / (4 * Λ)) ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) ?_ t⟩
  intro s
  obtain ⟨H, hH, hc⟩ := c18_physical_generator_coercive a i ζ ha hΛ hA
    (hsem.map_gen hfg s.toNNReal)
  have he := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (S s.toNNReal f) H (G s) hH (hG s)
  rw [he] at hc
  exact hc

/-- The integrated coercive gradient estimate for an actual bilinear transpose
physical orbit starting in the generator domain. Its right side contains no
norm of the initial generator image. -/
theorem c18_physical_transpose_orbit_integrated_gradient
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ t : ℝ≥0,
        (1 / (4 * Λ)) * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
          (‖f‖ ^ 2 - ‖S t f‖ ^ 2) / 2 +
            ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) *
              (∫ s in (0 : ℝ)..(t : ℝ), ‖S s.toNNReal f‖ ^ 2) := by
  have hsem : S5Semigroup S (IsPhysicalComplexTransposeGeneratorPair a i ζ) :=
    ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
  obtain ⟨G, hG, hGc⟩ := physical_transpose_generator_orbit_continuous_gradient a i ζ ha hΛ hA
    (fun s : ℝ => S s.toNNReal f) (fun s : ℝ => S s.toNNReal g)
    ((hsem.cont f).comp continuous_real_toNNReal)
    ((hsem.cont g).comp continuous_real_toNNReal)
    (fun s => hsem.map_gen hfg s.toNNReal)
  refine ⟨G, hG, hGc, fun t => c18_integrated_gradient_energy hsem hfg G hGc
    (1 / (4 * Λ)) ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) ?_ t⟩
  intro s
  obtain ⟨H, hH, hc⟩ := c18_physical_transpose_generator_coercive a i ζ ha hΛ hA
    (hsem.map_gen hfg s.toNNReal)
  have he := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (S s.toNNReal f) H (G s) hH (hG s)
  rw [he] at hc
  exact hc

/-- Strong convergence in time-space L2 preserves a closed value-gradient
relation almost everywhere when the values already converge at each time. -/
private theorem c18_ae_closedGraph_of_L2_cauchy
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [CompleteSpace F]
    {μ : Measure ℝ} {K : Set (E × F)} (hK : IsClosed K)
    (u : ℕ → ℝ → E) (v : ℕ → ℝ → F) (w : ℝ → E)
    (hv : ∀ n, MemLp (v n) 2 μ)
    (hvc : CauchySeq (fun n => (hv n).toLp (v n)))
    (hu : ∀ s, Filter.Tendsto (fun n => u n s) Filter.atTop (𝓝 (w s)))
    (hgraph : ∀ n s, (u n s, v n s) ∈ K) :
    ∃ g : Lp F 2 μ, ∀ᵐ s ∂μ, (w s, g s) ∈ K := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hvc
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  have hrep : ∀ᵐ s ∂μ, ∀ n, (hv n).toLp (v n) s = v n s :=
    ae_all_iff.mpr fun n => (hv n).coeFn_toLp
  refine ⟨g, ?_⟩
  filter_upwards [hlim, hrep] with s hs hrep
  have hvs : Filter.Tendsto (fun n => v (ns n) s) Filter.atTop (𝓝 (g s)) := by
    simpa only [hrep] using hs
  exact hK.mem_of_tendsto
    (((hu s).comp hns.tendsto_atTop).prodMk_nhds hvs)
    (Filter.Eventually.of_forall fun n => hgraph (ns n) s)

private theorem c18_L2_norm_sq
    {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ} (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable f)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
  exact integral_nonneg fun _ => sq_nonneg _

private theorem c18_continuous_memLp_Icc
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hf : Continuous f) (T : ℝ) :
    MemLp f 2 (volume.restrict (Set.Icc 0 T)) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf.norm.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable B
    ((ae_restrict_mem measurableSet_Icc).mono fun s hs => hB ⟨s, hs, rfl⟩)

private theorem c18_cauchy_of_norm_sq_bound
    {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
    (V : ℕ → E) (f : ℕ → H) (hf : CauchySeq f) (C : ℝ)
    (hbound : ∀ n m, ‖V n - V m‖ ^ 2 ≤ C * ‖f n - f m‖ ^ 2) :
    CauchySeq V := by
  have hfc : Filter.Tendsto (fun nm : ℕ × ℕ => ‖f nm.1 - f nm.2‖)
      Filter.atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using cauchySeq_iff_tendsto_dist_atTop_0.mp hf
  have hsq : Filter.Tendsto (fun nm : ℕ × ℕ => ‖V nm.1 - V nm.2‖ ^ 2)
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun nm : ℕ × ℕ => sq_nonneg ‖V nm.1 - V nm.2‖)
      (fun nm : ℕ × ℕ => hbound nm.1 nm.2)
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using (hfc.pow 2).const_mul C
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, dist_eq_norm, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using h

/-- An integrated difference estimate gives strong convergence of gradients
in time-space L2, and therefore an almost-everywhere closed-graph limit. -/
private theorem c18_ae_closedGraph_of_integrated_difference
    {E F H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [CompleteSpace F]
    [NormedAddCommGroup H] {K : Set (E × F)} (hK : IsClosed K)
    (u : ℕ → ℝ → E) (v : ℕ → ℝ → F) (w : ℝ → E)
    (f : ℕ → H) (hf : CauchySeq f) (T C : ℝ)
    (hv : ∀ n, Continuous (v n))
    (hu : ∀ s, Filter.Tendsto (fun n => u n s) Filter.atTop (𝓝 (w s)))
    (hgraph : ∀ n s, (u n s, v n s) ∈ K)
    (hbound : ∀ n m,
      (∫ s in Set.Icc 0 T, ‖v n s - v m s‖ ^ 2) ≤ C * ‖f n - f m‖ ^ 2) :
    ∃ g : Lp F 2 (volume.restrict (Set.Icc 0 T)),
      ∀ᵐ s ∂volume.restrict (Set.Icc 0 T), (w s, g s) ∈ K := by
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 T)
  have hmem := fun n => c18_continuous_memLp_Icc (v n) (hv n) T
  let V : ℕ → Lp F 2 μ := fun n => (hmem n).toLp (v n)
  have heq (n m : ℕ) : ‖V n - V m‖ ^ 2 =
      ∫ s, ‖v n s - v m s‖ ^ 2 ∂μ := by
    rw [c18_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (V n) (V m),
      (hmem n).coeFn_toLp, (hmem m).coeFn_toLp] with s hs hn hm
    rw [hs]
    change ‖V n s - V m s‖ ^ 2 = _
    change V n s = v n s at hn
    change V m s = v m s at hm
    rw [hn, hm]
  have hvc : CauchySeq V := c18_cauchy_of_norm_sq_bound V f hf C
    (fun n m => (heq n m).trans_le (hbound n m))
  exact c18_ae_closedGraph_of_L2_cauchy hK u v w hmem hvc hu hgraph

private theorem c18_gen_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) {f g u v : E} (hfg : Gen f g) (huv : Gen u v) :
    Gen (f - u) (g - v) := by
  apply (hP.gen _ _).mp
  have h := ((hP.gen _ _).mpr hfg).sub ((hP.gen _ _).mpr huv)
  convert h using 1
  ext t
  simp only [map_sub, smul_sub]
  module

private theorem c18_physicalH1_sub {d : ℕ}
    {u v : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u - v) (fun j => G j - H j) := by
  have hneg {j : Fin d} {f g : Vec d → ℝ}
      (h : HasWeakPartialDerivative Set.univ j f g) :
      HasWeakPartialDerivative Set.univ j (fun x => -f x) (fun x => -g x) := by
    refine ⟨fun x hx => (h.1 x hx).neg, fun x hx => (h.2.1 x hx).neg, ?_⟩
    intro φ hφ
    simp only [neg_mul, integral_neg, h.2.2 φ hφ]
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => u x - v x) (fun j x => G j x - H j x)
    (Lp.coeFn_sub _ _) (fun _ => Lp.coeFn_sub _ _)).mpr
  constructor
  · intro j
    simpa only [sub_eq_add_neg, Complex.add_re, Complex.neg_re] using
      Correctors.hasWeakPartialDerivative_add (hu.1 j) (hneg (hv.1 j))
  · intro j
    simpa only [sub_eq_add_neg, Complex.add_im, Complex.neg_im] using
      Correctors.hasWeakPartialDerivative_add (hu.2 j) (hneg (hv.2 j))

private theorem c18_pi_norm_sq_le_sum {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (G : Fin d → E) : ‖G‖ ^ 2 ≤ ∑ j, ‖G j‖ ^ 2 := by
  have hn : 0 ≤ ∑ j, ‖G j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : ‖G‖ ≤ Real.sqrt (∑ j, ‖G j‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    apply (Real.le_sqrt (norm_nonneg _) hn).mpr
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖G k‖) (Finset.mem_univ j)
  have hsq := sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _) |>.mpr hb
  rwa [Real.sq_sqrt hn] at hsq

private theorem c18_integrated_gradient_bound
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (μ K : ℝ) (hμ : 0 < μ) (hK : 0 ≤ K)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (K * (t : ℝ)) * ‖f‖)
    (f : E) (G : ℝ → Fin d → E) (hG : ∀ j, Continuous (fun s => G s j))
    (t : ℝ≥0)
    (henergy : μ * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
      (‖f‖ ^ 2 - ‖P t f‖ ^ 2) / 2 +
        K * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2)) :
    (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2) ≤
      ((1 / 2 + K * (Real.exp (K * (t : ℝ)) ^ 2 * (t : ℝ))) / μ) * ‖f‖ ^ 2 := by
  have hGc : Continuous G := continuous_pi hG
  have hsc : Continuous (fun s => ∑ j, ‖G s j‖ ^ 2) :=
    continuous_finset_sum _ fun j _ => (hG j).norm.pow 2
  have huc : Continuous (fun s : ℝ => ‖P s.toNNReal f‖ ^ 2) :=
    ((hP.cont f).comp continuous_real_toNNReal).norm.pow 2
  have hsq (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (t : ℝ)) :
      ‖P s.toNNReal f‖ ^ 2 ≤ Real.exp (K * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
    have he : Real.exp (K * (s.toNNReal : ℝ)) ≤ Real.exp (K * (t : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.coe_toNNReal _ hs.1] using hs.2) hK
    have hb := (hgrowth f s.toNNReal).trans (mul_le_mul_of_nonneg_right he (norm_nonneg f))
    calc
      ‖P s.toNNReal f‖ ^ 2 ≤ (Real.exp (K * (t : ℝ)) * ‖f‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
      _ = _ := mul_pow _ _ _
  have hui : (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2) ≤
      Real.exp (K * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 * (t : ℝ) := by
    have hb := intervalIntegral.integral_mono_on (NNReal.coe_nonneg t)
      (huc.intervalIntegrable (μ := volume) 0 t) (intervalIntegrable_const (μ := volume) (c :=
        Real.exp (K * (t : ℝ)) ^ 2 * ‖f‖ ^ 2)) hsq
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hb
  have hcompare : (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2) ≤
      ∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property),
      ← integral_Icc_eq_integral_Ioc]
    exact integral_mono ((hGc.norm.pow 2).integrableOn_Icc) hsc.integrableOn_Icc
      (fun s => c18_pi_norm_sq_le_sum (G s))
  have hmul := mul_le_mul_of_nonneg_left hcompare hμ.le
  have huim := mul_le_mul_of_nonneg_left hui hK
  have hfinal : μ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2) ≤
      (1 / 2 + K * (Real.exp (K * (t : ℝ)) ^ 2 * (t : ℝ))) * ‖f‖ ^ 2 := by
    nlinarith only [hmul, henergy, huim, sq_nonneg ‖P t f‖]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hμ).mpr
  nlinarith only [hfinal]

/-- Dense generator approximations and the coercive energy estimate yield
physical H1 at almost every time, for arbitrary initial L2 data. -/
private theorem c18_semigroup_ae_H1_of_energy
    {d : ℕ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen) (μ K : ℝ) (hμ : 0 < μ) (hK : 0 ≤ K)
    (hcoer : ∀ f g, Gen f g → (inner ℂ f g).re ≤ K * ‖f‖ ^ 2)
    (horbit : ∀ f g, Gen f g →
      ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
        (∀ j, Continuous (fun s => G s j)) ∧
        ∀ t : ℝ≥0, μ * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
          (‖f‖ ^ 2 - ‖P t f‖ ^ 2) / 2 +
            K * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    ∃ G : Lp (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) 2
        (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))),
      ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)),
        IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s) := by
  classical
  obtain ⟨F, H, hFH, hF⟩ := hP.exists_gen_approx f
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδ : Filter.Tendsto δ Filter.atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall hδpos⟩
  have hFlim := hF.comp hδ
  choose G hG hGc hGe using fun n => horbit (F (δ n)) (H (δ n)) (hFH _ (hδpos n))
  have hgrowth (u : Lp ℂ 2 (volume : Measure (Vec d))) (r : ℝ≥0) :
      ‖P r u‖ ≤ Real.exp (K * (r : ℝ)) * ‖u‖ := by
    simpa only [ContinuousLinearMap.id_apply] using
      hP.weighted_growth (ContinuousLinearMap.id ℂ _) K
        (by simpa only [ContinuousLinearMap.id_apply] using hcoer) u r
  apply c18_ae_closedGraph_of_integrated_difference
    (isClosed_physicalH1Graph volume (Or.inl rfl))
    (fun n s => P s.toNNReal (F (δ n))) G (fun s => P s.toNNReal f)
    (fun n => F (δ n)) hFlim.cauchySeq (t : ℝ)
    ((1 / 2 + K * (Real.exp (K * (t : ℝ)) ^ 2 * (t : ℝ))) / μ)
    (fun n => continuous_pi (hGc n))
    (fun s => ((P s.toNNReal).continuous.tendsto f).comp hFlim) hG
  intro n m
  obtain ⟨J, hJ, hJc, hJe⟩ := horbit (F (δ n) - F (δ m)) (H (δ n) - H (δ m))
    (c18_gen_sub hP (hFH _ (hδpos n)) (hFH _ (hδpos m)))
  have hdiff (s : ℝ) : J s = G n s - G m s := by
    apply physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (P s.toNNReal (F (δ n) - F (δ m))) (J s) (G n s - G m s) (hJ s)
    change IsPhysicalH1Graph volume (Or.inl rfl)
      (P s.toNNReal (F (δ n) - F (δ m))) (fun j => G n s j - G m s j)
    rw [map_sub]
    exact c18_physicalH1_sub (hG n s) (hG m s)
  have hb := c18_integrated_gradient_bound hP μ K hμ hK hgrowth
    (F (δ n) - F (δ m)) J hJc t (hJe t)
  simpa only [hdiff] using hb

/-- Both actual physical evolutions have weak spatial L2 gradients at almost
every time, for every initial L2 datum. This is the strong time-space limit of
dense generator-domain approximations, without a generator bound on the datum. -/
theorem c18_physical_evolution_L2_time_gradient
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag) :
    ∀ S ∈ [P, Pdag], ∀ f : Lp ℂ 2 (volume : Measure (Vec d)), ∀ t : ℝ≥0,
    ∃ G : Lp (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) 2
        (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))),
      ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)),
        IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s) := by
  intro S hS f t
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with hS | hS
  · subst S
    apply c18_semigroup_ae_H1_of_energy
      (⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩ :
        S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ))
      (1 / (4 * Λ)) ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (by positivity) (by positivity)
      (fun u g hug => ?_)
      (fun u g hug => c18_physical_orbit_integrated_gradient a i ζ ha hΛ hA P hP hug)
      f t
    obtain ⟨G, _hG, hc⟩ := c18_physical_generator_coercive a i ζ ha hΛ hA hug
    have hn : 0 ≤ (1 / (4 * Λ)) * ∑ j, ‖G j‖ ^ 2 := by positivity
    linarith only [hc, hn]
  · subst S
    apply c18_semigroup_ae_H1_of_energy
      (⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩ :
        S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair a i ζ))
      (1 / (4 * Λ)) ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (by positivity) (by positivity)
      (fun u g hug => ?_)
      (fun u g hug => c18_physical_transpose_orbit_integrated_gradient
        a i ζ ha hΛ hA P Pdag hPdag hug) f t
    obtain ⟨G, _hG, hc⟩ := c18_physical_transpose_generator_coercive a i ζ ha hΛ hA hug
    have hn : 0 ≤ (1 / (4 * Λ)) * ∑ j, ‖G j‖ ^ 2 := by positivity
    linarith only [hc, hn]

/-- In particular, arbitrary-data physical orbits lie in H1 at almost every
time of each compact time interval. -/
theorem c18_physical_evolution_ae_H1
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    (S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (hS : S ∈ [P, Pdag])
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)),
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) G := by
  obtain ⟨G, hG⟩ := c18_physical_evolution_L2_time_gradient a i ζ ha hΛ hA
    P Pdag hP hPdag S hS f t
  exact hG.mono fun s hs => ⟨G s, hs⟩

private theorem c18_physicalH1_add {d : ℕ}
    {u v : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u + v) (fun j => G j + H j) := by
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => u x + v x) (fun j x => G j x + H j x)
    (Lp.coeFn_add u v) (fun j => Lp.coeFn_add (G j) (H j))).mpr
  exact ⟨fun j => by simpa only [Complex.add_re] using
      Correctors.hasWeakPartialDerivative_add (hu.1 j) (hv.1 j),
    fun j => by simpa only [Complex.add_im] using
      Correctors.hasWeakPartialDerivative_add (hu.2 j) (hv.2 j)⟩

private theorem c18_semigroup_orbit_integral
    {d : ℕ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen) {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : Gen f g) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, P s.toNNReal g) = P t.toNNReal f - f := by
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hP.cont f).comp continuous_real_toNNReal
  have hg : Continuous (fun s : ℝ => P s.toNNReal g) :=
    (hP.cont g).comp continuous_real_toNNReal
  have hder : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun r : ℝ => P r.toNNReal f)
        (P s.toNNReal g) (Set.Ioi s) s := by
    intro s hs
    exact (hP.hasDerivWithinAt_orbit hfg s hs.1.le).mono Set.Ioi_subset_Ici_self
  simpa only [Real.toNNReal_zero, hP.zero, ContinuousLinearMap.id_apply] using
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hu.continuousOn hder
      (hg.intervalIntegrable (μ := volume) 0 t)

private theorem c18_semigroup_gradient_primitive
    {d : ℕ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))} (hfg : Gen f g)
    (F : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : IsPhysicalH1Graph volume (Or.inl rfl) f F)
    (H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal g) (H s))
    (hHc : ∀ j, Continuous (fun s => H s j)) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      ∀ s j, HasDerivAt (fun r => G r j) (H s j) s := by
  let G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun s j => F j + ∫ r in (0 : ℝ)..s, H r j
  refine ⟨G, ?_, ?_⟩
  · intro s hs
    have hi := Blueprint.physicalH1Graph_intervalIntegral
      (fun r => P r.toNNReal g) H ((hP.cont g).comp continuous_real_toNNReal) hHc hH 0 s
    have hf := c18_physicalH1_add hF hi
    have he : f + (∫ r in (0 : ℝ)..s, P r.toNNReal g) = P s.toNNReal f := by
      rw [c18_semigroup_orbit_integral hP hfg s hs]
      abel
    rw [he] at hf
    exact hf
  · intro s j
    exact ((hHc j).integral_hasStrictDerivAt 0 s).hasDerivAt.const_add (F j)

/-- On the second generator domain, the actual physical gradient is
differentiable in time, with derivative the gradient of the generator orbit. -/
theorem c18_physical_D2_orbit_gradient
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexGeneratorPair a i ζ g h) :
    ∃ G H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal g) (H s)) ∧
      (∀ s j, HasDerivAt (fun r => G r j) (H s j) s) ∧
      ∀ j, Continuous (fun s => H s j) := by
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  obtain ⟨H, hH, hHc⟩ := Blueprint.physical_generator_orbit_continuous_gradient
    a i ζ ha hΛ hA (fun s => P s.toNNReal g) (fun s => P s.toNNReal h)
    ((hp.cont g).comp continuous_real_toNNReal) ((hp.cont h).comp continuous_real_toNNReal)
    (fun s => hp.map_gen hgh s.toNNReal)
  obtain ⟨G, hG, hGd⟩ := c18_semigroup_gradient_primitive hp hfg
    hfg.choose hfg.choose_spec.1 H hH hHc
  exact ⟨G, H, hG, hH, hGd, hHc⟩

/-- The same differentiable-gradient statement for the actual bilinear
transpose, retaining its full divergence-form generator graph. -/
theorem c18_physical_transpose_D2_orbit_gradient
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair a i ζ g h) :
    ∃ G H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal f) (G s)) ∧
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal g) (H s)) ∧
      (∀ s j, HasDerivAt (fun r => G r j) (H s j) s) ∧
      ∀ j, Continuous (fun s => H s j) := by
  let hp : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair a i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  obtain ⟨H, hH, hHc⟩ := Blueprint.physical_transpose_generator_orbit_continuous_gradient
    a i ζ ha hΛ hA (fun s => Pdag s.toNNReal g) (fun s => Pdag s.toNNReal h)
    ((hp.cont g).comp continuous_real_toNNReal) ((hp.cont h).comp continuous_real_toNNReal)
    (fun s => hp.map_gen hgh s.toNNReal)
  obtain ⟨G, hG, hGd⟩ := c18_semigroup_gradient_primitive hp hfg
    hfg.choose hfg.choose_spec.1 H hH hHc
  exact ⟨G, H, hG, hH, hGd, hHc⟩

private theorem c18_semigroup_gen_real_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) {f g : E} (hfg : Gen f g) (c : ℝ) :
    Gen (c • f) (c • g) := by
  apply (hP.gen _ _).mp
  have hh := ((hP.gen f g).mpr hfg).const_smul c
  apply hh.congr'
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [(P t).map_smul_of_tower c f, ← smul_sub, smul_comm]

private theorem c18_semigroup_average_tendsto
    {d : ℕ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Filter.Tendsto (fun δ : ℝ => δ⁻¹ • (∫ s in (0 : ℝ)..δ, P s.toNNReal f))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) := by
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hP.cont f).comp continuous_real_toNNReal
  have hh := (hu.integral_hasStrictDerivAt 0 0).hasDerivAt.tendsto_slope_zero_right
  simpa only [zero_add, intervalIntegral.integral_same, sub_zero,
    Real.toNNReal_zero, hP.zero, ContinuousLinearMap.id_apply] using hh

private theorem c18_semigroup_D2_approx
    {d : ℕ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen)
    (hI : ∀ u δ, 0 ≤ δ →
      Gen (∫ s in (0 : ℝ)..δ, P s.toNNReal u) (P δ.toNNReal u - u))
    {f g : Lp ℂ 2 (volume : Measure (Vec d))} (hfg : Gen f g) :
    ∃ F G H : ℝ → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ δ, 0 < δ → Gen (F δ) (G δ) ∧ Gen (G δ) (H δ)) ∧
      Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds f) ∧
      Filter.Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds g) := by
  let A := fun (u : Lp ℂ 2 (volume : Measure (Vec d))) (δ : ℝ) =>
    δ⁻¹ • (∫ s in (0 : ℝ)..δ, P s.toNNReal u)
  refine ⟨A f, A g, fun δ => δ⁻¹ • (P δ.toNNReal g - g), ?_,
    c18_semigroup_average_tendsto hP f, c18_semigroup_average_tendsto hP g⟩
  intro δ hδ
  constructor
  · have hi := hI f δ hδ.le
    rw [← c18_semigroup_orbit_integral hP hfg δ hδ.le] at hi
    exact c18_semigroup_gen_real_smul hP hi δ⁻¹
  · exact c18_semigroup_gen_real_smul hP (hI g δ hδ.le) δ⁻¹

/-- Actual forward second-domain data approximate every first-domain pair in
both its value and generator image, with no coefficient differentiability
assumption needed for this approximation. -/
theorem c18_physical_generator_D2_approx
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    ∃ F G H : ℝ → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ δ, 0 < δ → IsPhysicalComplexGeneratorPair a i ζ (F δ) (G δ) ∧
        IsPhysicalComplexGeneratorPair a i ζ (G δ) (H δ)) ∧
      Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds f) ∧
      Filter.Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds g) := by
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  apply c18_semigroup_D2_approx hp (hfg := hfg)
  intro u δ hδ
  simpa only [Real.coe_toNNReal', max_eq_left hδ] using
    Blueprint.physical_forward_generator_timeIntegral a i ζ P hP u δ.toNNReal

/-- Graph-norm density of the actual bilinear transpose second generator
domain in its first domain. -/
theorem c18_physical_transpose_generator_D2_approx
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    ∃ F G H : ℝ → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ δ, 0 < δ → IsPhysicalComplexTransposeGeneratorPair a i ζ (F δ) (G δ) ∧
        IsPhysicalComplexTransposeGeneratorPair a i ζ (G δ) (H δ)) ∧
      Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds f) ∧
      Filter.Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds g) := by
  let hp : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair a i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  apply c18_semigroup_D2_approx hp (hfg := hfg)
  intro u δ hδ
  simpa only [Real.coe_toNNReal', max_eq_left hδ] using
    Blueprint.physical_transpose_generator_timeIntegral a i ζ P Pdag hPdag u δ.toNNReal

private noncomputable def c18_coefficient_mul {d : ℕ} (b : Vec d → ℂ)
    (hb : MemLp b ∞ volume) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 (hb.toLp b)

private theorem c18_coefficient_mul_coe {d : ℕ} (b : Vec d → ℂ)
    (hb : MemLp b ∞ volume) (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    c18_coefficient_mul b hb u =ᵐ[volume] fun x => b x * u x := by
  change (ContinuousLinearMap.mul ℂ ℂ).holder 2 (hb.toLp b) u =ᵐ[volume] _
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hb.toLp b) u,
    hb.coeFn_toLp] with x hx hb'
  simpa only [ContinuousLinearMap.mul_apply', hb'] using hx

private theorem c18_principal_cross_eq_sum_inner {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (X Y : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * X k x * star (Y j x)) =
      ∑ j, ∑ k, inner ℂ (Y j) (c18_coefficient_mul (fun x => (a x j k : ℂ))
        (ha j k) (X k)) := by
  have hi j k : Integrable (fun x => (a x j k : ℂ) * X k x * star (Y j x)) volume :=
    ((ha j k).fun_mul (r := 2) (Lp.memLp (X k))).integrable_mul (Lp.memLp (Y j)).star
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi j k]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ fun k _ => hi j k]
  apply Finset.sum_congr rfl
  intro k _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [c18_coefficient_mul_coe (fun x => (a x j k : ℂ)) (ha j k) (X k)]
    with x hx
  simp only [hx, RCLike.inner_apply, starRingEnd_apply]

/-- The literal anisotropic principal form differentiates along differentiable
L2 gradient curves. This does not differentiate the coefficients in time. -/
theorem c18_physical_principal_form_hasDerivAt
    {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hG : ∀ j, HasDerivAt (fun r => G r j) (H j) s) :
    HasDerivAt (fun r => ∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G r k x * star (G r j x))
      ((∫ x, ∑ j, ∑ k, (a x j k : ℂ) * H k x * star (G s j x)) +
       (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (H j x))) s := by
  have he := c18_principal_cross_eq_sum_inner a ha
  have hf : (fun r => ∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G r k x * star (G r j x)) =
      (fun r => ∑ j, ∑ k, inner ℂ (G r j)
        (c18_coefficient_mul (fun x => (a x j k : ℂ)) (ha j k) (G r k))) := by
    funext r
    exact he (G r) (G r)
  rw [hf, he H (G s), he (G s) H]
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hG j).inner ℂ (((c18_coefficient_mul (fun x => (a x j k : ℂ))
        (ha j k)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hG k))
  simpa only [Finset.sum_add_distrib, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars'] using hd

private theorem c18_principal_cross_integrable {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (X Y : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    Integrable (fun x => ∑ j, ∑ k,
      (a x j k : ℂ) * X k x * star (Y j x)) volume :=
  integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    ((ha j k).fun_mul (r := 2) (Lp.memLp (X k))).integrable_mul (Lp.memLp (Y j)).star

private theorem c18_principal_cross_re_symm {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    (X Y : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * X k x * star (Y j x)).re =
      (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * Y k x * star (X j x)).re := by
  have hX := integral_re (c18_principal_cross_integrable a ha X Y)
  have hY := integral_re (c18_principal_cross_integrable a ha Y X)
  simp only [RCLike.re_eq_complex_re] at hX hY
  rw [← hX, ← hY]
  apply integral_congr_ae
  filter_upwards [hsym] with x hx
  simp only [Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [hx j k]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- Symmetry of the actual coefficients identifies the real principal-energy
derivative with twice its mixed form, without differentiating in space. -/
theorem c18_physical_principal_energy_hasDerivAt {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hG : ∀ j, HasDerivAt (fun r => G r j) (H j) s) :
    HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G r k x * star (G r j x)).re)
      (2 * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (H j x)).re) s := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (c18_physical_principal_form_hasDerivAt a ha G H s hG)
  have hsymm := c18_principal_cross_re_symm a ha hsym H (G s)
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.add_re,
    hsymm, two_mul] using! hd

/-- Whole-space column integration by parts includes the derivative of the
actual coefficient column. It applies to the bilinear transpose drift. -/
theorem c18_physical_column_integration_by_parts {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (haSmooth : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hDa : ∀ j k l, MemLp
      (fun x => (coordinateDerivative l (fun y => a y j k) x : ℂ)) ∞ volume)
    (i : Fin d) (u v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    (∫ x, u x * (∑ j, (a x j i : ℂ) * H j x)) =
      -(∫ x, (∑ j, (a x j i : ℂ) * G j x) * v x) -
        (∫ x, (∑ j, (coordinateDerivative j (fun y => a y j i) x : ℂ)) * u x * v x) := by
  have hL j : Integrable (fun x => u x * (a x j i : ℂ) * H j x) volume :=
    ((Lp.memLp u).fun_mul (r := 2) (ha j i)).integrable_mul (Lp.memLp (H j))
  have hR j : Integrable (fun x => (a x j i : ℂ) * G j x * v x) volume :=
    ((ha j i).fun_mul (r := 2) (Lp.memLp (G j))).integrable_mul (Lp.memLp v)
  have hD j : Integrable (fun x =>
      (coordinateDerivative j (fun y => a y j i) x : ℂ) * u x * v x) volume :=
    ((hDa j i j).fun_mul (r := 2) (Lp.memLp u)).integrable_mul (Lp.memLp v)
  have hLeq : (∫ x, u x * (∑ j, (a x j i : ℂ) * H j x)) =
      ∑ j, ∫ x, u x * (a x j i : ℂ) * H j x := by
    rw [← integral_finsetSum _ fun j _ => hL j]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [Finset.mul_sum, mul_assoc]
  have hReq : (∫ x, (∑ j, (a x j i : ℂ) * G j x) * v x) =
      ∑ j, ∫ x, (a x j i : ℂ) * G j x * v x := by
    simp only [Finset.sum_mul]
    exact integral_finsetSum _ fun j _ => hR j
  have hDeq : (∫ x, (∑ j,
      (coordinateDerivative j (fun y => a y j i) x : ℂ)) * u x * v x) =
      ∑ j, ∫ x, (coordinateDerivative j (fun y => a y j i) x : ℂ) * u x * v x := by
    simp only [Finset.sum_mul]
    exact integral_finsetSum _ fun j _ => hD j
  rw [hLeq, hReq, hDeq, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hw := physicalH1Graph_integral_weighted_gradient (fun x => a x j i)
    (haSmooth j i) (ha j i) (hDa j i) u v G H hu hv j
  have hcomm : (∫ x, (a x j i : ℂ) * G j x * v x) =
      ∫ x, G j x * (a x j i : ℂ) * v x := by
    congr 1
    funext x
    ring
  rw [← hcomm] at hw
  linear_combination hw

private theorem c18_L2_star_pair {d : ℕ}
    (g : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, g x * (star g) x) = inner ℂ g g := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star g] with x hx
  simp only [hx, RCLike.inner_apply, Pi.star_apply, Complex.star_def, mul_comm]

private theorem c18_principal_star_test {d : ℕ} (a : Vec d → Mat d)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * (star (H j)) x) =
      ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * star (H j x) := by
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (H j))] with x hx
  simp only [hx, Pi.star_apply]

private theorem c18_column_star_test {d : ℕ} (a : Vec d → Mat d) (i : Fin d)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (g : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, (∑ j, (a x j i : ℂ) * G j x) * (star g) x) =
      ∫ x, (∑ j, (a x j i : ℂ) * G j x) * star (g x) := by
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star g] with x hx
  rw [hx]
  rfl

private theorem c18_principal_graph_test_real {d : ℕ}
    (g : Lp ℂ 2 (volume : Measure (Vec d))) (B F ζ : ℂ)
    (ht : inner ℂ g g = -(1 / 2 : ℂ) * B + ζ * F) :
    2 * B.re = -4 * ‖g‖ ^ 2 + 4 * (ζ * F).re := by
  have hh (z : ℂ) : (-(1 / 2 : ℂ) * z).re = -(1 / 2 : ℝ) * z.re := by
    norm_num [Complex.mul_re]
  have hn : (inner ℂ g g).re = ‖g‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa only [RCLike.re_eq_complex_re] using
      (RCLike.re_ofReal_pow (K := ℂ) ‖g‖ 2)
  have hr := congrArg Complex.re ht
  rw [hn, Complex.add_re, hh] at hr
  linarith only [hr]

/-- Testing the actual forward graph with the conjugate generator image gives
the principal-energy derivative, with the original non-divergence drift. -/
theorem c18_physical_generator_principal_energy_hasDerivAt {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u (G s))
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (hG : ∀ j, HasDerivAt (fun r => G r j) (H j) s) :
    HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G r k x * star (G r j x)).re)
      (-4 * ‖g‖ ^ 2 + 4 * (ζ *
        (∫ x, (∑ j, (a x j i : ℂ) * G s j x) * star (g x))).re) s := by
  obtain ⟨K, hK, hw⟩ := hug
  have hKG := physicalH1Graph_gradient_unique volume (Or.inl rfl) u K (G s) hK hu
  rw [hKG] at hw
  have ht := hw (star g) (fun j => star (H j)) (physicalH1Graph_star g H hg)
  rw [c18_L2_star_pair, c18_principal_star_test,
    c18_column_star_test] at ht
  have hr := c18_principal_graph_test_real g _ _ ζ ht
  have hd := c18_physical_principal_energy_hasDerivAt a ha hsym G H s hG
  rw [hr] at hd
  exact hd

/-- For the actual bilinear transpose, the same test exposes both the
coefficient-column drift and its divergence, with their required signs. -/
theorem c18_physical_transpose_principal_energy_hasDerivAt {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    (haSmooth : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hDa : ∀ j k l, MemLp
      (fun x => (coordinateDerivative l (fun y => a y j k) x : ℂ)) ∞ volume)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u (G s))
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (hG : ∀ j, HasDerivAt (fun r => G r j) (H j) s) :
    HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G r k x * star (G r j x)).re)
      (-4 * ‖g‖ ^ 2 - 4 * (ζ *
        ((∫ x, (∑ j, (a x j i : ℂ) * G s j x) * star (g x)) +
         (∫ x, (∑ j, (coordinateDerivative j (fun y => a y j i) x : ℂ)) *
           u x * star (g x)))).re) s := by
  obtain ⟨K, hK, hw⟩ := hug
  have hKG := physicalH1Graph_gradient_unique volume (Or.inl rfl) u K (G s) hK hu
  rw [hKG] at hw
  have ht := hw (star g) (fun j => star (H j)) (physicalH1Graph_star g H hg)
  have hpr : (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G s k x * (star (H j)) x) =
      ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (H j x) := by
    apply integral_congr_ae
    filter_upwards [hsym, ae_all_iff.mpr (fun j => Lp.coeFn_star (H j))]
      with x hsym' hstar
    simp only [hsym', hstar, Pi.star_apply]
  have hdiv : (∫ x, (∑ j,
      (coordinateDerivative j (fun y => a y j i) x : ℂ)) * u x * (star g) x) =
      ∫ x, (∑ j, (coordinateDerivative j (fun y => a y j i) x : ℂ)) *
        u x * star (g x) := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star g] with x hx
    rw [hx]
    rfl
  rw [c18_L2_star_pair, hpr,
    c18_physical_column_integration_by_parts a ha haSmooth hDa i u (star g)
      (G s) (fun j => star (H j)) hu (physicalH1Graph_star g H hg),
    c18_column_star_test, hdiv] at ht
  have hr := c18_principal_graph_test_real g _ _ ζ ht
  have hd := c18_physical_principal_energy_hasDerivAt a ha hsym G H s hG
  have he (F D : ℂ) : (ζ * (-F - D)).re = -(ζ * (F + D)).re := by
    rw [show -F - D = -(F + D) by ring, mul_neg, Complex.neg_re]
  rw [he] at hr
  convert hd using 1 <;> linarith only [hr]

private theorem c18_force_column_young {d : ℕ} (A : Mat d) (i : Fin d)
    (Λ : ℝ) (hΛ : 0 < Λ) (hA : ∀ j, |A j i| ≤ Λ)
    (ζ g : ℂ) (G : Fin d → ℂ) :
    ‖ζ * ((∑ j, (A j i : ℂ) * G j) * star g)‖ ≤
      (((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * (∑ j, ‖G j‖ ^ 2) +
        (1 / 4 : ℝ) * ‖g‖ ^ 2 := by
  let t : ℝ := 1 / (4 * ((d : ℝ) + 1) * Λ ^ 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hd0 : (d : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have h1 : 1 / (4 * t) = ((d : ℝ) + 1) * Λ ^ 2 := by
    dsimp [t]
    field_simp [hΛ.ne', hd0] <;> ring
  have h2 : (d : ℝ) * t * Λ ^ 2 ≤ (1 / 4 : ℝ) := by
    have he : (d : ℝ) * t * Λ ^ 2 = (d : ℝ) / (4 * ((d : ℝ) + 1)) := by
      dsimp [t]
      field_simp [hΛ.ne', hd0] <;> ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have he : ζ * ((∑ j, (A j i : ℂ) * G j) * star g) =
      star g * (∑ j, (A j i : ℂ) * (ζ * G j)) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy := physicalForceColumn_young A i Λ t ht hA (star g) (fun j => ζ * G j)
  rw [← he, h1] at hy
  simp only [norm_mul, norm_star, mul_pow, ← Finset.mul_sum] at hy
  calc
    _ ≤ (((d : ℝ) + 1) * Λ ^ 2) * (‖ζ‖ ^ 2 * ∑ j, ‖G j‖ ^ 2) +
        ((d : ℝ) * t * Λ ^ 2) * ‖g‖ ^ 2 := by
      simpa only [norm_mul, norm_star, mul_assoc] using hy
    _ ≤ (((d : ℝ) + 1) * Λ ^ 2) * (‖ζ‖ ^ 2 * ∑ j, ‖G j‖ ^ 2) +
        (1 / 4 : ℝ) * ‖g‖ ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖g‖))
    _ = _ := by ring

/-- A quarter of the generator-image norm absorbs the actual force column.
The remaining term uses the Euclidean sum of gradient-coordinate norms. -/
theorem c18_physical_force_column_norm_le {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (g : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * star (g x))‖ ≤
      (((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * (∑ j, ‖G j‖ ^ 2) +
        (1 / 4 : ℝ) * ‖g‖ ^ 2 := by
  let C : ℝ := ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2
  let F : Vec d → ℂ := fun x => (∑ j, (a x j i : ℂ) * G j x) * star (g x)
  have hFi : Integrable F volume :=
    (memLp_finsetSum _ fun j _ => (ha j i).fun_mul (r := 2) (Lp.memLp (G j))).integrable_mul
      (Lp.memLp g).star
  have hN : Integrable (fun x => ∑ j, ‖G j x‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq
  have hg : Integrable (fun x => ‖g x‖ ^ 2) volume := (Lp.memLp g).norm.integrable_sq
  have hp : ∀ᵐ x ∂volume, ‖ζ * F x‖ ≤ C * (∑ j, ‖G j x‖ ^ 2) +
      (1 / 4 : ℝ) * ‖g x‖ ^ 2 := by
    filter_upwards [hA] with x hx
    exact c18_force_column_young (a x) i Λ hΛ (fun j => hx.entry_abs_le j i)
      ζ (g x) (fun j => G j x)
  have hi := integral_mono_ae (hFi.const_mul ζ).norm
    ((hN.const_mul C).add (hg.const_mul (1 / 4 : ℝ))) hp
  simp only [Pi.add_apply] at hi
  have hNeq : (∫ x, ∑ j, ‖G j x‖ ^ 2) = ∑ j, ‖G j‖ ^ 2 := by
    rw [integral_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq]
    exact Finset.sum_congr rfl fun j _ => (physicalL2_norm_sq volume (G j)).symm
  rw [integral_add (hN.const_mul C) (hg.const_mul (1 / 4 : ℝ)),
    integral_const_mul, hNeq, integral_const_mul, ← physicalL2_norm_sq] at hi
  have hn := norm_integral_le_integral_norm (μ := volume) (fun x => ζ * F x)
  rw [integral_const_mul] at hn
  exact hn.trans hi

/-- Ellipticity controls the full Euclidean gradient by the real anisotropic
principal energy of the actual L2 gradient classes. -/
theorem c18_physical_principal_energy_coercive {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∑ j, ‖G j‖ ^ 2) ≤ Λ *
      (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * star (G j x)).re := by
  have hQ := c18_principal_cross_integrable a ha G G
  have hN : Integrable (fun x => ∑ j, ‖G j x‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq
  have hp : ∀ᵐ x ∂volume, Λ⁻¹ * (∑ j, ‖G j x‖ ^ 2) ≤
      (∑ j, ∑ k, (a x j k : ℂ) * G k x * star (G j x)).re := by
    filter_upwards [hA] with x hx
    exact s5_coercive hx (fun j => G j x)
  have hi := integral_mono_ae (hN.const_mul Λ⁻¹) hQ.re hp
  simp only [RCLike.re_eq_complex_re] at hi
  have hNeq : (∫ x, ∑ j, ‖G j x‖ ^ 2) = ∑ j, ‖G j‖ ^ 2 := by
    rw [integral_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq]
    exact Finset.sum_congr rfl fun j _ => (physicalL2_norm_sq volume (G j)).symm
  have hreal := integral_re hQ
  simp only [RCLike.re_eq_complex_re] at hreal
  rw [integral_const_mul, hNeq, hreal] at hi
  have hh := mul_le_mul_of_nonneg_left hi hΛ.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul] using hh

/-- The principal energy along a twice-domain forward orbit satisfies a
scalar differential upper bound without a generator-image norm on its RHS. -/
theorem c18_physical_generator_principal_energy_derivative_le {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u (G s))
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (hG : ∀ j, HasDerivAt (fun r => G r j) (H j) s) :
    ∃ q' : ℝ, HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
      q' ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) *
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re := by
  let C : ℝ := ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2
  let F : ℂ := ζ * (∫ x, (∑ j, (a x j i : ℂ) * G s j x) * star (g x))
  refine ⟨-4 * ‖g‖ ^ 2 + 4 * F.re,
    c18_physical_generator_principal_energy_hasDerivAt a i ζ ha
      (hA.mono fun _ hx => hx.symm) hug G H s hu hg hG, ?_⟩
  have hf := (Complex.re_le_norm F).trans
    (c18_physical_force_column_norm_le a i ζ ha hΛ hA (G s) g)
  have hc := c18_physical_principal_energy_coercive a ha hΛ hA (G s)
  calc
    -4 * ‖g‖ ^ 2 + 4 * F.re ≤ (4 * C) * (∑ j, ‖G s j‖ ^ 2) := by
      change F.re ≤ C * (∑ j, ‖G s j‖ ^ 2) + (1 / 4 : ℝ) * ‖g‖ ^ 2 at hf
      nlinarith only [hf, sq_nonneg ‖g‖]
    _ ≤ (4 * C) * (Λ *
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re) :=
      mul_le_mul_of_nonneg_left hc (by dsimp [C]; positivity)
    _ = _ := by dsimp [C]; ring

private theorem c18_bounded_multiplier_young (B : ℝ)
    (ζ b u g : ℂ) (hb : ‖b‖ ≤ B) :
    ‖ζ * (b * u * star g)‖ ≤ B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 +
      (1 / 4 : ℝ) * ‖g‖ ^ 2 := by
  calc
    ‖ζ * (b * u * star g)‖ ≤ (B * ‖ζ‖ * ‖u‖) * ‖g‖ := by
      simp only [norm_mul, norm_star]
      nlinarith only [mul_le_mul_of_nonneg_left hb (norm_nonneg ζ),
        norm_nonneg ζ, norm_nonneg u, norm_nonneg g,
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (norm_nonneg ζ))
          (mul_nonneg (norm_nonneg u) (norm_nonneg g))]
    _ ≤ _ := by nlinarith only [sq_nonneg (B * ‖ζ‖ * ‖u‖ - ‖g‖ / 2)]

/-- A bounded actual divergence is a lower order term and consumes only a
quarter of the squared generator image in the principal energy identity. -/
theorem c18_physical_divergence_norm_le {d : ℕ} (b : Vec d → ℂ)
    (hb : MemLp b ∞ volume) (B : ℝ)
    (hbound : ∀ᵐ x ∂volume, ‖b x‖ ≤ B) (ζ : ℂ)
    (u g : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖ζ * (∫ x, b x * u x * star (g x))‖ ≤
      B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 + (1 / 4 : ℝ) * ‖g‖ ^ 2 := by
  let C : ℝ := B ^ 2 * ‖ζ‖ ^ 2
  have hF := (hb.fun_mul (r := 2) (Lp.memLp u)).integrable_mul (Lp.memLp g).star
  have hu := (Lp.memLp u).norm.integrable_sq
  have hg := (Lp.memLp g).norm.integrable_sq
  have hp : ∀ᵐ x ∂volume, ‖ζ * (b x * u x * star (g x))‖ ≤
      C * ‖u x‖ ^ 2 + (1 / 4 : ℝ) * ‖g x‖ ^ 2 := by
    filter_upwards [hbound] with x hx
    exact c18_bounded_multiplier_young B ζ (b x) (u x) (g x) hx
  have hi := integral_mono_ae (hF.const_mul ζ).norm
    ((hu.const_mul C).add (hg.const_mul (1 / 4 : ℝ))) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (hu.const_mul C) (hg.const_mul (1 / 4 : ℝ)),
    integral_const_mul, integral_const_mul, ← physicalL2_norm_sq,
    ← physicalL2_norm_sq] at hi
  have hn := norm_integral_le_integral_norm (μ := volume)
    (fun x => ζ * (b x * u x * star (g x)))
  rw [integral_const_mul] at hn
  exact hn.trans hi

/-- The bilinear transpose has the same principal energy control, with the
actual coefficient divergence contributing an explicit zeroth order term. -/
theorem c18_physical_transpose_principal_energy_derivative_le {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (haSmooth : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hDa : ∀ j k l, MemLp
      (fun x => (coordinateDerivative l (fun y => a y j k) x : ℂ)) ∞ volume)
    (B : ℝ)
    (hdiv : ∀ᵐ x ∂volume,
      ‖∑ j, (coordinateDerivative j (fun y => a y j i) x : ℂ)‖ ≤ B)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u (G s))
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (hG : ∀ j, HasDerivAt (fun r => G r j) (H j) s) :
    ∃ q' : ℝ, HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
      q' ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) *
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re +
          4 * B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 := by
  let C : ℝ := ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2
  let F : ℂ := ∫ x, (∑ j, (a x j i : ℂ) * G s j x) * star (g x)
  let D : ℂ := ∫ x, (∑ j,
    (coordinateDerivative j (fun y => a y j i) x : ℂ)) * u x * star (g x)
  refine ⟨-4 * ‖g‖ ^ 2 - 4 * (ζ * (F + D)).re,
    c18_physical_transpose_principal_energy_hasDerivAt a i ζ ha
      (hA.mono fun _ hx => hx.symm) haSmooth hDa hug G H s hu hg hG, ?_⟩
  have hF := c18_physical_force_column_norm_le a i ζ ha hΛ hA (G s) g
  have hD := c18_physical_divergence_norm_le
    (fun x => ∑ j, (coordinateDerivative j (fun y => a y j i) x : ℂ))
    (memLp_finsetSum _ fun j _ => hDa j i j) B hdiv ζ u g
  have hr : -(ζ * (F + D)).re ≤ ‖ζ * F‖ + ‖ζ * D‖ := by
    calc
      _ ≤ ‖ζ * (F + D)‖ := by
        simpa only [Complex.neg_re, norm_neg] using Complex.re_le_norm (-(ζ * (F + D)))
      _ ≤ _ := by rw [mul_add]; exact norm_add_le _ _
  have hc := c18_physical_principal_energy_coercive a ha hΛ hA (G s)
  calc
    -4 * ‖g‖ ^ 2 - 4 * (ζ * (F + D)).re ≤
        (4 * C) * (∑ j, ‖G s j‖ ^ 2) + 4 * B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 := by
      change ‖ζ * F‖ ≤ C * (∑ j, ‖G s j‖ ^ 2) + (1 / 4 : ℝ) * ‖g‖ ^ 2 at hF
      change ‖ζ * D‖ ≤ B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 + (1 / 4 : ℝ) * ‖g‖ ^ 2 at hD
      nlinarith only [hr, hF, hD, sq_nonneg ‖g‖]
    _ ≤ (4 * C) * (Λ *
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re) +
          4 * B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hc
        (show 0 ≤ 4 * C by dsimp [C]; positivity)) le_rfl
    _ = _ := by dsimp [C]; ring

private lemma c18_euclidean_unit {d : ℕ} (j : Fin d) :
    euclideanNorm (unitVector j) = 1 := by
  change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

private lemma c18_coordinate_abs_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  have hsq : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (f := fun j => v j * v j)
      (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact hsq

/-- The structural first derivative bound controls each actual coordinate
derivative at every spatial point. -/
theorem c18_smooth_coefficient_derivative_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω) (l j k : Fin d)
    (x : Vec d) : |coordinateDerivative l (fun y => ω.1 y j k) x| ≤ M 1 := by
  obtain ⟨A, B, _, hB, hAB, hA, _⟩ := hsmooth.2 1 (by norm_num)
  have hb := hA x (fun _ => unitVector l) (unitVector k)
  simp only [iteratedFDeriv_one_apply, c18_euclidean_unit,
    Finset.prod_const_one, mul_one] at hb
  have hc := c18_coordinate_abs_le_euclideanNorm
    (Matrix.mulVec (fun j k => fderiv ℝ (fun y => ω.1 y j k) x (unitVector l))
      (unitVector k)) j
  have he (N : Mat d) : (N.mulVec (unitVector k)) j = N j k := by
    change dotProduct (fun m => N j m) (Pi.single k 1) = _
    rw [dotProduct_single, mul_one]
  erw [he] at hc
  exact (hc.trans hb).trans (by linarith)

/-- Smooth structural bounds supply bounded actual derivatives and the
uniform bound needed for the actual transpose column divergence. -/
theorem c18_smooth_coefficient_divergence_bounds {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω) :
    0 ≤ M 1 ∧
      (∀ j k l, MemLp
        (fun x => (coordinateDerivative l (fun y => ω.1 y j k) x : ℂ)) ∞ volume) ∧
      (∀ (i : Fin d) (x : Vec d),
        ‖∑ j, (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)‖ ≤
          (d : ℝ) * M 1) := by
  have hM : 0 ≤ M 1 := by
    obtain ⟨A, B, hA, hB, hAB, _⟩ := hsmooth.2 1 (by norm_num)
    linarith
  refine ⟨hM, ?_, ?_⟩
  · intro j k l
    have hD : Continuous (coordinateDerivative l (fun y => ω.1 y j k)) :=
      ((contDiff_infty_iff_fderiv.mp (hsmooth.1.1 j k)).2.clm_apply
        contDiff_const).continuous
    apply memLp_top_of_bound (Complex.continuous_ofReal.comp hD).aestronglyMeasurable (M 1)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
        c18_smooth_coefficient_derivative_bound hsmooth l j k x
  · intro i x
    calc
      _ ≤ ∑ j : Fin d, ‖(coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin d, M 1 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [Complex.norm_real, Real.norm_eq_abs] using
          c18_smooth_coefficient_derivative_bound hsmooth j j i x
      _ = _ := by simp

/-- The actual forward twice-domain orbit carries a continuous gradient
whose principal energy obeys the scalar differential inequality. -/
theorem c18_physical_D2_principal_energy_bound
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexGeneratorPair a i ζ g h) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ s, 0 ≤ s → ∃ q' : ℝ,
        HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
          (a x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
        q' ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) *
          (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re := by
  obtain ⟨G, H, hG, hH, hd, _⟩ :=
    c18_physical_D2_orbit_gradient a i ζ ha hΛ hA P hP hfg hgh
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  refine ⟨G, hG, fun j => continuous_iff_continuousAt.mpr (fun s =>
    (hd s j).continuousAt), ?_⟩
  intro s hs
  exact c18_physical_generator_principal_energy_derivative_le a i ζ ha hΛ hA
    (hp.map_gen hfg s.toNNReal) G (H s) s (hG s hs) (hH s) (hd s)

/-- For the actual bilinear transpose the lower order energy coefficient
comes from the given structural smooth bounds on the actual field. -/
theorem c18_physical_transpose_D2_principal_energy_bound
    {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hsmooth : IsSmoothWithBounds M ω) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ s, 0 ≤ s → ∃ q' : ℝ,
        HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
          (ω.1 x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
        q' ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) *
          (∫ x, ∑ j, ∑ k, (ω.1 x j k : ℂ) * G s k x * star (G s j x)).re +
            4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2 * ‖Pdag s.toNNReal f‖ ^ 2 := by
  obtain ⟨G, H, hG, hH, hd, _⟩ :=
    c18_physical_transpose_D2_orbit_gradient ω.1 i ζ ha hΛ hA P Pdag hPdag hfg hgh
  let hp : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  obtain ⟨hM, hDa, hdiv⟩ := c18_smooth_coefficient_divergence_bounds hsmooth
  refine ⟨G, hG, fun j => continuous_iff_continuousAt.mpr (fun s =>
    (hd s j).continuousAt), ?_⟩
  intro s hs
  exact c18_physical_transpose_principal_energy_derivative_le ω.1 i ζ ha hΛ hA
    hsmooth.1.1 hDa ((d : ℝ) * M 1)
    (Filter.Eventually.of_forall (hdiv i)) (hp.map_gen hfg s.toNNReal)
    G (H s) s (hG s hs) (hH s) (hd s)

/-- Integrating the scalar differential upper bound backwards from an
endpoint turns an integrated energy estimate into an endpoint estimate. -/
theorem c18_principal_energy_endpoint_from_integral_on
    (q q' : ℝ → ℝ) (K E t : ℝ) (hK : 0 ≤ K) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (hq : ∀ s ∈ Set.Icc 0 t, HasDerivAt q (q' s) s)
    (hnonneg : ∀ s ∈ Set.Icc 0 t, 0 ≤ q s)
    (hbound : ∀ s ∈ Set.Icc 0 t, q' s ≤ K * q s + E) :
    t * (q t * Real.exp (-K * t)) ≤
      (∫ s in (0 : ℝ)..t, q s) + E * t ^ 2 := by
  let F : ℝ → ℝ := fun s => q s * Real.exp (-K * s) - E * s
  have hqc : ContinuousOn q (Set.Icc 0 t) :=
    fun s hs => (hq s hs).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (Set.Icc 0 t) :=
    (hqc.mul (by fun_prop)).sub (by fun_prop)
  have hFd (s : ℝ) (hs : s ∈ Set.Icc 0 t) : HasDerivAt F
      ((q' s - K * q s) * Real.exp (-K * s) - E) s := by
    have he : HasDerivAt (fun r : ℝ => Real.exp (-K * r))
        (-K * Real.exp (-K * s)) s := by
      convert (((hasDerivAt_id s).const_mul (-K)).exp) using 1 <;>
        simp only [id_eq, mul_one] <;> ring
    convert ((hq s hs).mul he).sub ((hasDerivAt_id s).const_mul E) using 1 <;>
      first | rfl | ring
  have hant : AntitoneOn F (Set.Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hFc
      (fun s hs => (hFd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    have hs' : s ∈ Set.Icc 0 t := interior_subset hs
    have he : Real.exp (-K * s) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith only [mul_nonneg hK hs'.1])
    have hmul := mul_le_mul_of_nonneg_right (hbound s hs')
      (Real.exp_pos (-K * s)).le
    have hEexp := mul_le_mul_of_nonneg_left he hE
    rw [(hFd s hs').deriv]
    nlinarith only [hmul, hEexp]
  have hp (s : ℝ) (hs : s ∈ Set.Icc 0 t) :
      q t * Real.exp (-K * t) ≤ q s + E * t := by
    have hm := hant hs ⟨ht, le_rfl⟩ hs.2
    have he : Real.exp (-K * s) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith only [mul_nonneg hK hs.1])
    have hqe := mul_le_mul_of_nonneg_left he (hnonneg s hs)
    dsimp [F] at hm
    nlinarith only [hm, hqe, mul_nonneg hE hs.1]
  have hi := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => q t * Real.exp (-K * t)) volume 0 t)
    ((hqc.add continuousOn_const).intervalIntegrable_of_Icc ht) hp
  simp only [Pi.add_apply] at hi
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hqc.intervalIntegrable_of_Icc ht) intervalIntegrable_const,
    intervalIntegral.integral_const] at hi
  simp only [sub_zero, smul_eq_mul] at hi
  nlinarith only [hi]

/-- Integrating the scalar differential upper bound backwards from an
endpoint turns an integrated energy estimate into an endpoint estimate. -/
theorem c18_principal_energy_endpoint_from_integral
    (q q' : ℝ → ℝ) (hq : ∀ s, HasDerivAt q (q' s) s)
    (K E t : ℝ) (hK : 0 ≤ K) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (hnonneg : ∀ s ∈ Set.Icc 0 t, 0 ≤ q s)
    (hbound : ∀ s ∈ Set.Icc 0 t, q' s ≤ K * q s + E) :
    t * (q t * Real.exp (-K * t)) ≤
      (∫ s in (0 : ℝ)..t, q s) + E * t ^ 2 := by
  let F : ℝ → ℝ := fun s => q s * Real.exp (-K * s) - E * s
  have hqc : Continuous q := continuous_iff_continuousAt.mpr
    (fun s => (hq s).continuousAt)
  have hFc : Continuous F := by dsimp [F]; fun_prop
  have hFd (s : ℝ) : HasDerivAt F
      ((q' s - K * q s) * Real.exp (-K * s) - E) s := by
    have he : HasDerivAt (fun r : ℝ => Real.exp (-K * r))
        (-K * Real.exp (-K * s)) s := by
      convert (((hasDerivAt_id s).const_mul (-K)).exp) using 1 <;>
        simp only [id_eq, mul_one] <;> ring
    convert ((hq s).mul he).sub ((hasDerivAt_id s).const_mul E) using 1 <;>
      first | rfl | ring
  have hant : AntitoneOn F (Set.Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hFc.continuousOn
      (fun s _ => (hFd s).differentiableAt.differentiableWithinAt)
    intro s hs
    have hs' : s ∈ Set.Icc 0 t := interior_subset hs
    have he : Real.exp (-K * s) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith only [mul_nonneg hK hs'.1])
    have hmul := mul_le_mul_of_nonneg_right (hbound s hs')
      (Real.exp_pos (-K * s)).le
    have hEexp := mul_le_mul_of_nonneg_left he hE
    rw [(hFd s).deriv]
    nlinarith only [hmul, hEexp]
  have hp (s : ℝ) (hs : s ∈ Set.Icc 0 t) :
      q t * Real.exp (-K * t) ≤ q s + E * t := by
    have hm := hant hs ⟨ht, le_rfl⟩ hs.2
    have he : Real.exp (-K * s) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith only [mul_nonneg hK hs.1])
    have hqe := mul_le_mul_of_nonneg_left he (hnonneg s hs)
    dsimp [F] at hm
    nlinarith only [hm, hqe, mul_nonneg hE hs.1]
  have hi := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => q t * Real.exp (-K * t)) volume 0 t)
    ((hqc.add continuous_const).intervalIntegrable 0 t) hp
  simp only [Pi.add_apply] at hi
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hqc.intervalIntegrable 0 t) intervalIntegrable_const,
    intervalIntegral.integral_const] at hi
  simp only [sub_zero, smul_eq_mul] at hi
  nlinarith only [hi]

private theorem c18_principal_pointwise_upper {d : ℕ} {A : Mat d} {Λ : ℝ}
    (hA : S5Elliptic A Λ) (X : Fin d → ℂ) :
    (∑ j, ∑ k, (A j k : ℂ) * X k * star (X j)).re ≤ Λ * ∑ j, ‖X j‖ ^ 2 := by
  have hre : (∑ j, ∑ k, (A j k : ℂ) * X k * star (X j)).re =
      s5Bil A (fun k => (X k).re) (fun k => (X k).re) +
        s5Bil A (fun k => (X k).im) (fun k => (X k).im) := by
    unfold s5Bil
    rw [← Finset.sum_add_distrib, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hn : ∑ j, ‖X j‖ ^ 2 = ∑ j, (X j).re ^ 2 + ∑ j, (X j).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply] <;> ring
  rw [hre, hn, mul_add]
  exact add_le_add (hA.upper _) (hA.upper _)

/-- The actual anisotropic principal energy has the matching upper bound,
so its time integral is controlled by the checked gradient energy estimate. -/
theorem c18_physical_principal_energy_upper {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * star (G j x)).re ≤
      Λ * (∑ j, ‖G j‖ ^ 2) := by
  have hQ := c18_principal_cross_integrable a ha G G
  have hN : Integrable (fun x => ∑ j, ‖G j x‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq
  have hp : ∀ᵐ x ∂volume,
      (∑ j, ∑ k, (a x j k : ℂ) * G k x * star (G j x)).re ≤
        Λ * (∑ j, ‖G j x‖ ^ 2) := by
    filter_upwards [hA] with x hx
    exact c18_principal_pointwise_upper hx (fun j => G j x)
  have hi := integral_mono_ae hQ.re (hN.const_mul Λ) hp
  have hreal := integral_re hQ
  simp only [RCLike.re_eq_complex_re] at hi hreal
  rw [hreal, integral_const_mul,
    integral_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq] at hi
  simpa only [← physicalL2_norm_sq] using hi

/-- A fixed positive time gradient bound obtained from the actual principal
energy differential inequality and integrated coercivity. All constants are
independent of the initial generator image. -/
private theorem c18_physical_gradient_endpoint_bound
    {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen)
    (μ L K J : ℝ) (hμ : 0 < μ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖)
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : ∀ j, Continuous (fun s => G s j))
    (t : ℝ≥0) (ht : 0 < t)
    (henergy : μ * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
      (‖f‖ ^ 2 - ‖P t f‖ ^ 2) / 2 +
        L * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2))
    (hder : ∀ s, 0 ≤ s → ∃ q' : ℝ,
      HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
      q' ≤ K * (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * G s k x * star (G s j x)).re + J * ‖P s.toNNReal f‖ ^ 2) :
    (∑ j, ‖G t j‖ ^ 2) ≤
      (Λ * (Λ * (d : ℝ) *
        ((1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ) +
          J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) ^ 2) /
        ((t : ℝ) * Real.exp (-K * (t : ℝ)))) * ‖f‖ ^ 2 := by
  let q : ℝ → ℝ := fun s => (∫ x, ∑ j, ∑ k,
    (a x j k : ℂ) * G s k x * star (G s j x)).re
  let B := (1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ
  have ht' : (0 : ℝ) < t := ht
  have hqc : ContinuousOn q (Set.Icc 0 (t : ℝ)) := by
    intro s hs
    exact (hder s hs.1).choose_spec.1.continuousAt.continuousWithinAt
  have hqp (s : ℝ) : q s ≤ Λ * (d : ℝ) * ‖G s‖ ^ 2 := by
    have hb := c18_physical_principal_energy_upper a ha hA (G s)
    have hn : (∑ j, ‖G s j‖ ^ 2) ≤ (d : ℝ) * ‖G s‖ ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin d, ‖G s‖ ^ 2 := Finset.sum_le_sum fun j _ =>
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm (G s) j)
        _ = _ := by simp
    exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_left hn hΛ.le])
  have hnonneg (s : ℝ) : 0 ≤ q s := by
    have hb := c18_physical_principal_energy_coercive a ha hΛ hA (G s)
    have hn : 0 ≤ ∑ j, ‖G s j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    change (∑ j, ‖G s j‖ ^ 2) ≤ Λ * q s at hb
    nlinarith only [hb, hn, hΛ]
  have hint := c18_integrated_gradient_bound hP μ L hμ hL hgrowth f G hG t henergy
  have hqi : (∫ s in (0 : ℝ)..(t : ℝ), q s) ≤
      Λ * (d : ℝ) * B * ‖f‖ ^ 2 := by
    have hgcont : Continuous (fun s => ‖G s‖ ^ 2) := (continuous_pi hG).norm.pow 2
    have hi := intervalIntegral.integral_mono_on ht'.le
      (hqc.intervalIntegrable_of_Icc (μ := volume) ht'.le)
      ((hgcont.const_mul (Λ * (d : ℝ))).intervalIntegrable (μ := volume) 0 t)
      (fun s _ => hqp s)
    rw [intervalIntegral.integral_const_mul] at hi
    have heq : (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2) =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le ht'.le, ← integral_Icc_eq_integral_Ioc]
    rw [heq] at hi
    have hm := mul_le_mul_of_nonneg_left hint
      (mul_nonneg hΛ.le (Nat.cast_nonneg d))
    calc
      _ ≤ Λ * (d : ℝ) * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2) := hi
      _ ≤ Λ * (d : ℝ) * (B * ‖f‖ ^ 2) := hm
      _ = _ := by ring
  have hsq (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      ‖P s.toNNReal f‖ ^ 2 ≤ Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
    have he : Real.exp (L * (s.toNNReal : ℝ)) ≤ Real.exp (L * (t : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.coe_toNNReal _ hs.1] using hs.2) hL
    have hb := (hgrowth f s.toNNReal).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg f))
    exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb).trans_eq (mul_pow _ _ _)
  let q' : ℝ → ℝ := fun s => if hs : 0 ≤ s then (hder s hs).choose else 0
  have hd (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) : HasDerivAt q (q' s) s := by
    dsimp [q']; rw [dif_pos hs.1]; exact (hder s hs.1).choose_spec.1
  have hb (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      q' s ≤ K * q s + J * Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
    dsimp [q']; rw [dif_pos hs.1]
    have hm := mul_le_mul_of_nonneg_left (hsq s hs) hJ
    exact (hder s hs.1).choose_spec.2.trans (by dsimp [q]; nlinarith only [hm])
  have he := c18_principal_energy_endpoint_from_integral_on q q' K
    (J * Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2) t hK (by positivity) ht'.le
    hd (fun s _ => hnonneg s) hb
  have hcoer := c18_physical_principal_energy_coercive a ha hΛ hA (G t)
  change (∑ j, ‖G t j‖ ^ 2) ≤ Λ * q t at hcoer
  have hdpos : 0 < (t : ℝ) * Real.exp (-K * (t : ℝ)) :=
    mul_pos ht' (Real.exp_pos _)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hdpos).mpr
  have he' := mul_le_mul_of_nonneg_left he hΛ.le
  have hi' := mul_le_mul_of_nonneg_left hqi hΛ.le
  have hc' := mul_le_mul_of_nonneg_right hcoer hdpos.le
  dsimp [B] at hi'
  nlinarith only [he', hi', hc']

/-- Forward twice-domain data have a fixed positive time H1 bound whose
constant depends only on the displayed coefficient, force and time data. -/
theorem c18_physical_D2_gradient_at_time
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P) (t : ℝ≥0) (ht : 0 < t) :
    ∃ C : ℝ, ∀ f g h : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair a i ζ f g →
      IsPhysicalComplexGeneratorPair a i ζ g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G ∧
        (∑ j, ‖G j‖ ^ 2) ≤ C * ‖f‖ ^ 2 := by
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖ := by
    intro f t
    apply hp.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f t
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_generator_coercive a i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]
  refine ⟨Λ * (Λ * (d : ℝ) *
    ((1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ) +
      0 * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) ^ 2) /
        ((t : ℝ) * Real.exp (-K * (t : ℝ))), ?_⟩
  intro f g h hfg hgh
  obtain ⟨G, hG, hGc, hder⟩ :=
    c18_physical_D2_principal_energy_bound a i ζ ha hΛ hA P hP hfg hgh
  obtain ⟨H, hH, _, henergy⟩ :=
    c18_physical_orbit_integrated_gradient a i ζ ha hΛ hA P hP hfg
  have heq : (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖H s j‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := (Set.uIcc_of_le t.property ▸ hs).1
    dsimp only
    rw [physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (P s.toNNReal f) (G s) (H s) (hG s hs') (hH s)]
  refine ⟨G t, ?_, ?_⟩
  · simpa only [Real.toNNReal_coe] using hG t t.property
  · apply c18_physical_gradient_endpoint_bound a ha hΛ hA hp μ L K 0
      hμ hL hK le_rfl hgrowth f G hGc t ht
    · rw [heq]; exact henergy t
    · simpa only [zero_mul, add_zero] using hder

/-- The corresponding bound for the actual bilinear transpose includes
only the structural first derivative bound on the actual coefficients. -/
theorem c18_physical_transpose_D2_gradient_at_time
    {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hsmooth : IsSmoothWithBounds M ω) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ C : ℝ, ∀ f g h : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g →
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (Pdag t f) G ∧
        (∑ j, ‖G j‖ ^ 2) ≤ C * ‖f‖ ^ 2 := by
  let hp : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2
  let J := 4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hgrowth : ∀ f t, ‖Pdag t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖ := by
    intro f t
    apply hp.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f t
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_transpose_generator_coercive
      ω.1 i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]
  refine ⟨Λ * (Λ * (d : ℝ) *
    ((1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ) +
      J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) ^ 2) /
        ((t : ℝ) * Real.exp (-K * (t : ℝ))), ?_⟩
  intro f g h hfg hgh
  obtain ⟨G, hG, hGc, hder⟩ :=
    c18_physical_transpose_D2_principal_energy_bound hsmooth i ζ ha hΛ hA
      P Pdag hPdag hfg hgh
  obtain ⟨H, hH, _, henergy⟩ :=
    c18_physical_transpose_orbit_integrated_gradient ω.1 i ζ ha hΛ hA P Pdag hPdag hfg
  have heq : (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖H s j‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := (Set.uIcc_of_le t.property ▸ hs).1
    dsimp only
    rw [physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (Pdag s.toNNReal f) (G s) (H s) (hG s hs') (hH s)]
  refine ⟨G t, ?_, ?_⟩
  · simpa only [Real.toNNReal_coe] using hG t t.property
  · apply c18_physical_gradient_endpoint_bound ω.1 ha hΛ hA hp μ L K J
      hμ hL hK hJ hgrowth f G hGc t ht
    · rw [heq]; exact henergy t
    · exact hder

/-- Density of twice-domain data and a uniform endpoint estimate pass actual
weak gradients to every initial L2 class through the closed H1 graph. -/
private theorem c18_semigroup_H1_of_D2_bound
    {d : ℕ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen)
    (happrox : ∀ f g, Gen f g →
      ∃ F G H : ℝ → Lp ℂ 2 (volume : Measure (Vec d)),
        (∀ δ, 0 < δ → Gen (F δ) (G δ) ∧ Gen (G δ) (H δ)) ∧
        Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds f) ∧
        Filter.Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds g))
    (t : ℝ≥0) (C : ℝ)
    (hbound : ∀ f g h, Gen f g → Gen g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G ∧
        (∑ j, ‖G j‖ ^ 2) ≤ C * ‖f‖ ^ 2)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G := by
  classical
  let D2 : Set (Lp ℂ 2 (volume : Measure (Vec d))) :=
    {u | ∃ v w, Gen u v ∧ Gen v w}
  have hfirst (u v : Lp ℂ 2 (volume : Measure (Vec d))) (huv : Gen u v) :
      u ∈ closure D2 := by
    obtain ⟨F, G, H, hgen, hF, _⟩ := happrox u v huv
    apply mem_closure_of_tendsto hF
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ⟨G δ, H δ, hgen δ hδ⟩
  have hdense : Dense D2 := by
    intro u
    obtain ⟨F, G, hgen, hF⟩ := hP.exists_gen_approx u
    apply isClosed_closure.mem_of_tendsto hF
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hfirst (F δ) (G δ) (hgen δ hδ)
  obtain ⟨F, hF, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense f)
  change ∀ n, ∃ v w, Gen (F n) v ∧ Gen v w at hF
  choose g h hg hh using hF
  choose G hG hb using fun n => hbound (F n) (g n) (h n) (hg n) (hh n)
  have hdiff (n m : ℕ) : ‖G n - G m‖ ^ 2 ≤ C * ‖F n - F m‖ ^ 2 := by
    obtain ⟨H, hH, hHb⟩ := hbound (F n - F m) (g n - g m) (h n - h m)
      (c18_gen_sub hP (hg n) (hg m)) (c18_gen_sub hP (hh n) (hh m))
    have hsub : IsPhysicalH1Graph volume (Or.inl rfl)
        (P t (F n - F m)) (fun j => G n j - G m j) := by
      simpa only [map_sub] using c18_physicalH1_sub (hG n) (hG m)
    have he := physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (P t (F n - F m)) H (fun j => G n j - G m j) hH hsub
    rw [he] at hHb
    exact (c18_pi_norm_sq_le_sum (G n - G m)).trans hHb
  have hC : CauchySeq G := c18_cauchy_of_norm_sq_bound G F hlim.cauchySeq C hdiff
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨V, physicalH1Graph_of_tendsto volume (Or.inl rfl)
    (fun n => (P t (F n), G n)) (P t f, V) hG ?_⟩
  exact (((P t).continuous.tendsto f).comp hlim).prodMk_nhds hV

/-- Every strictly positive time of both actual physical evolutions maps
arbitrary L2 data into the physical weak H1 graph. -/
theorem physical_positive_time_H1 {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag) :
    ∀ S ∈ [P, Pdag], ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∀ t : ℝ≥0, 0 < t → ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (S t f) G := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ hΛ0 hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  intro S hS f t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with hS | hS
  · subst S
    obtain ⟨C, hC⟩ := c18_physical_D2_gradient_at_time ω.1 i ζ ha hΛ0 hA P hP t ht
    exact c18_semigroup_H1_of_D2_bound
      (⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩ :
        S5Semigroup P (IsPhysicalComplexGeneratorPair ω.1 i ζ))
      (fun u v huv => c18_physical_generator_D2_approx ω.1 i ζ P hP huv) t C hC f
  · subst S
    obtain ⟨C, hC⟩ := c18_physical_transpose_D2_gradient_at_time hsmooth i ζ ha hΛ0 hA
      P Pdag hPdag t ht
    exact c18_semigroup_H1_of_D2_bound
      (⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩ :
        S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ))
      (fun u v huv => c18_physical_transpose_generator_D2_approx
        ω.1 i ζ P Pdag hPdag huv) t C hC f

/-- The forward principal energy retains three squared generator-image norms
after absorbing the actual force column. -/
theorem c18_physical_generator_principal_energy_dissipative {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u (G s))
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (hG : ∀ j, HasDerivAt (fun r => G r j) (H j) s) :
    ∃ q' : ℝ, HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
      q' + 3 * ‖g‖ ^ 2 ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) *
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re := by
  let C : ℝ := ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2
  let F : ℂ := ζ * (∫ x, (∑ j, (a x j i : ℂ) * G s j x) * star (g x))
  refine ⟨-4 * ‖g‖ ^ 2 + 4 * F.re,
    c18_physical_generator_principal_energy_hasDerivAt a i ζ ha
      (hA.mono fun _ hx => hx.symm) hug G H s hu hg hG, ?_⟩
  have hf := (Complex.re_le_norm F).trans
    (c18_physical_force_column_norm_le a i ζ ha hΛ hA (G s) g)
  have hc := c18_physical_principal_energy_coercive a ha hΛ hA (G s)
  calc
    -4 * ‖g‖ ^ 2 + 4 * F.re + 3 * ‖g‖ ^ 2 ≤ (4 * C) * (∑ j, ‖G s j‖ ^ 2) := by
      change F.re ≤ C * (∑ j, ‖G s j‖ ^ 2) + (1 / 4 : ℝ) * ‖g‖ ^ 2 at hf
      nlinarith only [hf, sq_nonneg ‖g‖]
    _ ≤ (4 * C) * (Λ *
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re) :=
      mul_le_mul_of_nonneg_left hc (by dsimp [C]; positivity)
    _ = _ := by dsimp [C]; ring

/-- The actual bilinear transpose retains two squared generator-image norms
after absorbing its force column and coefficient divergence. -/
theorem c18_physical_transpose_principal_energy_dissipative {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (haSmooth : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hDa : ∀ j k l, MemLp
      (fun x => (coordinateDerivative l (fun y => a y j k) x : ℂ)) ∞ volume)
    (B : ℝ)
    (hdiv : ∀ᵐ x ∂volume,
      ‖∑ j, (coordinateDerivative j (fun y => a y j i) x : ℂ)‖ ≤ B)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u (G s))
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (hG : ∀ j, HasDerivAt (fun r => G r j) (H j) s) :
    ∃ q' : ℝ, HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
      q' + 2 * ‖g‖ ^ 2 ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) *
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re +
          4 * B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 := by
  let C : ℝ := ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2
  let F : ℂ := ∫ x, (∑ j, (a x j i : ℂ) * G s j x) * star (g x)
  let D : ℂ := ∫ x, (∑ j,
    (coordinateDerivative j (fun y => a y j i) x : ℂ)) * u x * star (g x)
  refine ⟨-4 * ‖g‖ ^ 2 - 4 * (ζ * (F + D)).re,
    c18_physical_transpose_principal_energy_hasDerivAt a i ζ ha
      (hA.mono fun _ hx => hx.symm) haSmooth hDa hug G H s hu hg hG, ?_⟩
  have hF := c18_physical_force_column_norm_le a i ζ ha hΛ hA (G s) g
  have hD := c18_physical_divergence_norm_le
    (fun x => ∑ j, (coordinateDerivative j (fun y => a y j i) x : ℂ))
    (memLp_finsetSum _ fun j _ => hDa j i j) B hdiv ζ u g
  have hr : -(ζ * (F + D)).re ≤ ‖ζ * F‖ + ‖ζ * D‖ := by
    calc
      _ ≤ ‖ζ * (F + D)‖ := by
        simpa only [Complex.neg_re, norm_neg] using Complex.re_le_norm (-(ζ * (F + D)))
      _ ≤ _ := by rw [mul_add]; exact norm_add_le _ _
  have hc := c18_physical_principal_energy_coercive a ha hΛ hA (G s)
  calc
    -4 * ‖g‖ ^ 2 - 4 * (ζ * (F + D)).re + 2 * ‖g‖ ^ 2 ≤
        (4 * C) * (∑ j, ‖G s j‖ ^ 2) + 4 * B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 := by
      change ‖ζ * F‖ ≤ C * (∑ j, ‖G s j‖ ^ 2) + (1 / 4 : ℝ) * ‖g‖ ^ 2 at hF
      change ‖ζ * D‖ ≤ B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 + (1 / 4 : ℝ) * ‖g‖ ^ 2 at hD
      nlinarith only [hr, hF, hD, sq_nonneg ‖g‖]
    _ ≤ (4 * C) * (Λ *
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re) +
          4 * B ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hc
        (show 0 ≤ 4 * C by dsimp [C]; positivity)) le_rfl
    _ = _ := by dsimp [C]; ring

/-- The forward twice-domain orbit retains generator dissipation in its
actual principal energy differential inequality. -/
theorem c18_physical_D2_principal_energy_dissipative
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexGeneratorPair a i ζ g h) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ s, 0 ≤ s → ∃ q' : ℝ,
        HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
          (a x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
        q' + 3 * ‖P s.toNNReal g‖ ^ 2 ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) *
          (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G s k x * star (G s j x)).re := by
  obtain ⟨G, H, hG, hH, hd, _⟩ :=
    c18_physical_D2_orbit_gradient a i ζ ha hΛ hA P hP hfg hgh
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  refine ⟨G, hG, fun j => continuous_iff_continuousAt.mpr (fun s =>
    (hd s j).continuousAt), ?_⟩
  intro s hs
  exact c18_physical_generator_principal_energy_dissipative a i ζ ha hΛ hA
    (hp.map_gen hfg s.toNNReal) G (H s) s (hG s hs) (hH s) (hd s)

/-- The actual transpose twice-domain orbit retains generator dissipation
with the coefficient divergence bounded by structural smoothness. -/
theorem c18_physical_transpose_D2_principal_energy_dissipative
    {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hsmooth : IsSmoothWithBounds M ω) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ s, 0 ≤ s → ∃ q' : ℝ,
        HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
          (ω.1 x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
        q' + 2 * ‖Pdag s.toNNReal g‖ ^ 2 ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) *
          (∫ x, ∑ j, ∑ k, (ω.1 x j k : ℂ) * G s k x * star (G s j x)).re +
            4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2 * ‖Pdag s.toNNReal f‖ ^ 2 := by
  obtain ⟨G, H, hG, hH, hd, _⟩ :=
    c18_physical_transpose_D2_orbit_gradient ω.1 i ζ ha hΛ hA P Pdag hPdag hfg hgh
  let hp : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  obtain ⟨hM, hDa, hdiv⟩ := c18_smooth_coefficient_divergence_bounds hsmooth
  refine ⟨G, hG, fun j => continuous_iff_continuousAt.mpr (fun s =>
    (hd s j).continuousAt), ?_⟩
  intro s hs
  exact c18_physical_transpose_principal_energy_dissipative ω.1 i ζ ha hΛ hA
    hsmooth.1.1 hDa ((d : ℝ) * M 1)
    (Filter.Eventually.of_forall (hdiv i)) (hp.map_gen hfg s.toNNReal)
    G (H s) s (hG s hs) (hH s) (hd s)

/-- Integrating a differential dissipation inequality does not require
integrability of the chosen derivative of the principal energy. -/
theorem c18_principal_energy_integrated_dissipation
    (q q' r w : ℝ → ℝ) (c K J a b : ℝ) (hab : a ≤ b)
    (hqc : Continuous q) (hrc : Continuous r) (hwc : Continuous w)
    (hq : ∀ s ∈ Set.Icc a b, HasDerivAt q (q' s) s)
    (hd : ∀ s ∈ Set.Icc a b, q' s + c * r s ≤ K * q s + J * w s) :
    c * (∫ s in a..b, r s) ≤ q a - q b +
      K * (∫ s in a..b, q s) + J * (∫ s in a..b, w s) := by
  let F : ℝ → ℝ := fun s => q s + c * (∫ x in a..s, r x) -
    K * (∫ x in a..s, q x) - J * (∫ x in a..s, w x)
  have hprim (f : ℝ → ℝ) (hf : Continuous f) (s : ℝ) :
      HasDerivAt (fun t => ∫ x in a..t, f x) (f s) s :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a s)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hF (s : ℝ) (hs : s ∈ Set.Icc a b) :
      HasDerivAt F (q' s + c * r s - K * q s - J * w s) s := by
    exact (((hq s hs).add ((hprim r hrc s).const_mul c)).sub
      ((hprim q hqc s).const_mul K)).sub ((hprim w hwc s).const_mul J)
  have hc : ContinuousOn F (Set.Icc a b) :=
    fun s hs => (hF s hs).continuousAt.continuousWithinAt
  have hm : AntitoneOn F (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hc
      (fun s hs => (hF s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hF s (interior_subset hs)).deriv]
    linarith only [hd s (interior_subset hs)]
  have he := hm (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩) hab
  dsimp [F] at he
  simp only [intervalIntegral.integral_same, mul_zero, add_zero, sub_zero] at he
  linarith only [he]

/-- The anisotropic principal form is continuous along continuous L2
gradient curves, including outside the physical nonnegative time interval. -/
theorem c18_physical_principal_form_continuous {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : ∀ j, Continuous (fun s => G s j)) :
    Continuous (fun s => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G s k x * star (G s j x)).re) := by
  have he : (fun s => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G s k x * star (G s j x)).re) =
      (fun s => (∑ j, ∑ k, inner ℂ (G s j)
        (c18_coefficient_mul (fun x => (a x j k : ℂ)) (ha j k) (G s k))).re) := by
    funext s
    rw [c18_principal_cross_eq_sum_inner a ha]
  rw [he]
  exact Complex.continuous_re.comp (continuous_finset_sum _ fun j _ =>
    continuous_finset_sum _ fun k _ => (hG j).inner (𝕜 := ℂ)
      ((c18_coefficient_mul (fun x => (a x j k : ℂ)) (ha j k)).continuous.comp (hG k)))

/-- Semigroup growth transfers an integrated orbit norm to its endpoint.
This applies in particular to the actual generator-image orbit. -/
theorem c18_semigroup_endpoint_norm_from_integral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (L : ℝ) (hL : 0 ≤ L)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖)
    (g : E) (t : ℝ≥0) :
    (t : ℝ) * ‖P t g‖ ^ 2 ≤ Real.exp (L * (t : ℝ)) ^ 2 *
      (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal g‖ ^ 2) := by
  have hc : Continuous (fun s : ℝ => ‖P s.toNNReal g‖ ^ 2) :=
    ((hP.cont g).comp continuous_real_toNNReal).norm.pow 2
  have hb (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      ‖P t g‖ ^ 2 ≤ Real.exp (L * (t : ℝ)) ^ 2 * ‖P s.toNNReal g‖ ^ 2 := by
    have hs' : s.toNNReal ≤ t := by
      exact_mod_cast (show (s.toNNReal : ℝ) ≤ (t : ℝ) by
        simpa only [Real.coe_toNNReal _ hs.1] using hs.2)
    have he : Real.exp (L * ((t - s.toNNReal : ℝ≥0) : ℝ)) ≤
        Real.exp (L * (t : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (NNReal.coe_le_coe.mpr tsub_le_self) hL)
    have hp : P t g = P (t - s.toNNReal) (P s.toNNReal g) := by
      rw [← ContinuousLinearMap.comp_apply, ← hP.add, tsub_add_cancel_of_le hs']
    have hn := hgrowth (P s.toNNReal g) (t - s.toNNReal)
    rw [← hp] at hn
    have hn' := hn.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
    exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn').trans_eq (mul_pow _ _ _)
  have hi := intervalIntegral.integral_mono_on t.property
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ‖P t g‖ ^ 2) volume 0 t)
    ((hc.const_mul _).intervalIntegrable (μ := volume) 0 t) hb
  convert hi using 1 <;>
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      intervalIntegral.integral_const_mul] <;> rfl

/-- Integrated generator dissipation along the actual twice-domain
forward orbit, with its literal anisotropic principal energy. -/
theorem c18_physical_D2_integrated_generator
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexGeneratorPair a i ζ g h) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ t : ℝ≥0,
        let q : ℝ → ℝ := fun s : ℝ => (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * G s k x * star (G s j x)).re
        3 * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal g‖ ^ 2) ≤
          q 0 - q t + (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) * (∫ s in (0 : ℝ)..(t : ℝ), q s) := by
  obtain ⟨G, hG, hGc, hder⟩ := c18_physical_D2_principal_energy_dissipative a i ζ ha hΛ hA P hP hfg hgh
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) := ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  let q : ℝ → ℝ := fun s : ℝ => (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * G s k x * star (G s j x)).re
  have hqc : Continuous q := c18_physical_principal_form_continuous a ha G hGc
  let q' : ℝ → ℝ := fun s => if hs : 0 ≤ s then (hder s hs).choose else 0
  refine ⟨G, hG, hGc, ?_⟩
  intro t
  have hd (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) : HasDerivAt q (q' s) s := by
    dsimp [q']; rw [dif_pos hs.1]
    exact (hder s hs.1).choose_spec.1
  have hb (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      q' s + 3 * ‖P s.toNNReal g‖ ^ 2 ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) * q s +
        0 * ‖P s.toNNReal f‖ ^ 2 := by
    dsimp [q']; rw [dif_pos hs.1]
    simpa only [zero_mul, add_zero] using (hder s hs.1).choose_spec.2
  have hi := c18_principal_energy_integrated_dissipation q q'
    (fun s => ‖P s.toNNReal g‖ ^ 2) (fun s => ‖P s.toNNReal f‖ ^ 2)
    3 (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) 0 0 t t.property hqc
    (((hp.cont g).comp continuous_real_toNNReal).norm.pow 2)
    (((hp.cont f).comp continuous_real_toNNReal).norm.pow 2) hd hb
  simpa only [zero_mul, add_zero] using hi

/-- Integrated generator dissipation along the actual twice-domain
bilinear transpose orbit, with its literal anisotropic principal energy. -/
theorem c18_physical_transpose_D2_integrated_generator
    {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hsmooth : IsSmoothWithBounds M ω) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ t : ℝ≥0,
        let q : ℝ → ℝ := fun s : ℝ => (∫ x, ∑ j, ∑ k,
        (ω.1 x j k : ℂ) * G s k x * star (G s j x)).re
        2 * (∫ s in (0 : ℝ)..(t : ℝ), ‖Pdag s.toNNReal g‖ ^ 2) ≤
          q 0 - q t + (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) * (∫ s in (0 : ℝ)..(t : ℝ), q s) +
            (4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2) * (∫ s in (0 : ℝ)..(t : ℝ), ‖Pdag s.toNNReal f‖ ^ 2) := by
  obtain ⟨G, hG, hGc, hder⟩ := c18_physical_transpose_D2_principal_energy_dissipative hsmooth i ζ ha hΛ hA P Pdag hPdag hfg hgh
  let hp : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ) := ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  let q : ℝ → ℝ := fun s : ℝ => (∫ x, ∑ j, ∑ k,
        (ω.1 x j k : ℂ) * G s k x * star (G s j x)).re
  have hqc : Continuous q := c18_physical_principal_form_continuous ω.1 ha G hGc
  let q' : ℝ → ℝ := fun s => if hs : 0 ≤ s then (hder s hs).choose else 0
  refine ⟨G, hG, hGc, ?_⟩
  intro t
  have hd (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) : HasDerivAt q (q' s) s := by
    dsimp [q']; rw [dif_pos hs.1]
    exact (hder s hs.1).choose_spec.1
  have hb (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      q' s + 2 * ‖Pdag s.toNNReal g‖ ^ 2 ≤ (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) * q s +
        (4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2) * ‖Pdag s.toNNReal f‖ ^ 2 := by
    dsimp [q']; rw [dif_pos hs.1]
    simpa only [zero_mul, add_zero] using (hder s hs.1).choose_spec.2
  have hi := c18_principal_energy_integrated_dissipation q q'
    (fun s => ‖Pdag s.toNNReal g‖ ^ 2) (fun s => ‖Pdag s.toNNReal f‖ ^ 2)
    2 (4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2) (4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2) 0 t t.property hqc
    (((hp.cont g).comp continuous_real_toNNReal).norm.pow 2)
    (((hp.cont f).comp continuous_real_toNNReal).norm.pow 2) hd hb
  simpa only [zero_mul, add_zero] using hi

private noncomputable def c18_mass_pairing {d : ℕ} :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2

private theorem c18_mass_pairing_eq_integral {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    c18_mass_pairing u v = ∫ x, u x * v x := by
  exact (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral u v

private noncomputable def c18_weak_principal {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) : ℂ :=
  ∑ j, ∑ k, c18_mass_pairing
    (c18_coefficient_mul (fun x => (a x j k : ℂ)) (ha j k) (G k)) (H j)

private theorem c18_weak_principal_eq_integral {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    c18_weak_principal a ha G H =
      ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * H j x := by
  have hi j k : Integrable (fun x => (a x j k : ℂ) * G k x * H j x) volume :=
    ((ha j k).fun_mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (H j))
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi j k]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ fun k _ => hi j k]
  apply Finset.sum_congr rfl
  intro k _
  rw [c18_mass_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [c18_coefficient_mul_coe (fun x => (a x j k : ℂ)) (ha j k) (G k)]
    with x hx
  rw [hx]

private noncomputable def c18_weak_column {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (v : Lp ℂ 2 (volume : Measure (Vec d))) : ℂ :=
  ∑ j, c18_mass_pairing
    (c18_coefficient_mul (fun x => (a x j i : ℂ)) (ha j i) (G j)) v

private theorem c18_weak_column_eq_integral {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (v : Lp ℂ 2 (volume : Measure (Vec d))) :
    c18_weak_column a ha i G v = ∫ x, (∑ j, (a x j i : ℂ) * G j x) * v x := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum (f := fun j x => (a x j i : ℂ) * G j x * v x)
    Finset.univ (fun j _ =>
      ((ha j i).fun_mul (r := 2) (Lp.memLp (G j))).integrable_mul (Lp.memLp v))]
  apply Finset.sum_congr rfl
  intro j _
  rw [c18_mass_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [c18_coefficient_mul_coe (fun x => (a x j i : ℂ)) (ha j i) (G j)]
    with x hx
  rw [hx]

private theorem c18_forward_graph_iff {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ)
    (u g : Lp ℂ 2 (volume : Measure (Vec d))) :
    IsPhysicalComplexGeneratorPair a i ζ u g ↔
      ∃ G, IsPhysicalH1Graph volume (Or.inl rfl) u G ∧
        ∀ v H, IsPhysicalH1Graph volume (Or.inl rfl) v H →
          c18_mass_pairing g v = -(1 / 2 : ℂ) * c18_weak_principal a ha G H +
            ζ * c18_weak_column a ha i G v := by
  constructor
  · rintro ⟨G, hG, hw⟩
    refine ⟨G, hG, ?_⟩
    intro v H hH
    rw [c18_mass_pairing_eq_integral, c18_weak_principal_eq_integral,
      c18_weak_column_eq_integral]
    exact hw v H hH
  · rintro ⟨G, hG, hw⟩
    refine ⟨G, hG, ?_⟩
    intro v H hH
    simpa only [c18_mass_pairing_eq_integral, c18_weak_principal_eq_integral,
      c18_weak_column_eq_integral] using hw v H hH

private theorem c18_transpose_graph_iff {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ)
    (u g : Lp ℂ 2 (volume : Measure (Vec d))) :
    IsPhysicalComplexTransposeGeneratorPair a i ζ u g ↔
      ∃ G, IsPhysicalH1Graph volume (Or.inl rfl) u G ∧
        ∀ v H, IsPhysicalH1Graph volume (Or.inl rfl) v H →
          c18_mass_pairing g v = -(1 / 2 : ℂ) *
            c18_weak_principal (fun x j k => a x k j) (fun j k => ha k j) G H +
              ζ * c18_weak_column a ha i H u := by
  constructor
  · rintro ⟨G, hG, hw⟩
    refine ⟨G, hG, ?_⟩
    intro v H hH
    erw [c18_mass_pairing_eq_integral, c18_weak_principal_eq_integral,
      c18_weak_column_eq_integral]
    convert hw v H hH using 1
    congr 2
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _
  · rintro ⟨G, hG, hw⟩
    refine ⟨G, hG, ?_⟩
    intro v H hH
    have he := hw v H hH
    erw [c18_mass_pairing_eq_integral, c18_weak_principal_eq_integral,
      c18_weak_column_eq_integral] at he
    convert he using 1
    congr 2
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _

private theorem c18_physical_generator_pair_sub {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ)
    {u v g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g)
    (hvh : IsPhysicalComplexGeneratorPair a i ζ v h) :
    IsPhysicalComplexGeneratorPair a i ζ (u - v) (g - h) := by
  obtain ⟨G, hG, hwG⟩ := (c18_forward_graph_iff a ha i ζ u g).mp hug
  obtain ⟨H, hH, hwH⟩ := (c18_forward_graph_iff a ha i ζ v h).mp hvh
  apply (c18_forward_graph_iff a ha i ζ _ _).mpr
  refine ⟨G - H, c18_physicalH1_sub hG hH, ?_⟩
  intro w W hW
  have h1 := hwG w W hW
  have h2 := hwH w W hW
  simp only [c18_weak_principal, c18_weak_column, Pi.sub_apply, map_sub,
    ContinuousLinearMap.sub_apply, Finset.sum_sub_distrib] at h1 h2 ⊢
  rw [h1, h2]
  ring

private theorem c18_physical_transpose_generator_pair_sub {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ)
    {u v g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (hvh : IsPhysicalComplexTransposeGeneratorPair a i ζ v h) :
    IsPhysicalComplexTransposeGeneratorPair a i ζ (u - v) (g - h) := by
  obtain ⟨G, hG, hwG⟩ := (c18_transpose_graph_iff a ha i ζ u g).mp hug
  obtain ⟨H, hH, hwH⟩ := (c18_transpose_graph_iff a ha i ζ v h).mp hvh
  apply (c18_transpose_graph_iff a ha i ζ _ _).mpr
  refine ⟨G - H, c18_physicalH1_sub hG hH, ?_⟩
  intro w W hW
  have h1 := hwG w W hW
  have h2 := hwH w W hW
  simp only [c18_weak_principal, c18_weak_column, Pi.sub_apply, map_sub,
    ContinuousLinearMap.sub_apply, Finset.sum_sub_distrib] at h1 h2 ⊢
  rw [h1, h2]
  ring

private theorem c18_cauchy_gradient_of_coercive_differences
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] (u v : ℕ → E) (G : ℕ → H)
    (hu : CauchySeq u) (hv : CauchySeq v) (μ L : ℝ) (hμ : 0 < μ)
    (hb : ∀ n m, μ * ‖G n - G m‖ ^ 2 ≤
      -(inner ℂ (u n - u m) (v n - v m)).re + L * ‖u n - u m‖ ^ 2) :
    CauchySeq G := by
  have hdu : Filter.Tendsto (fun nm : ℕ × ℕ => ‖u nm.1 - u nm.2‖)
      Filter.atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using cauchySeq_iff_tendsto_dist_atTop_0.mp hu
  have hdv : Filter.Tendsto (fun nm : ℕ × ℕ => ‖v nm.1 - v nm.2‖)
      Filter.atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using cauchySeq_iff_tendsto_dist_atTop_0.mp hv
  have hup (nm : ℕ × ℕ) : ‖G nm.1 - G nm.2‖ ^ 2 ≤
      (‖u nm.1 - u nm.2‖ * ‖v nm.1 - v nm.2‖ + L * ‖u nm.1 - u nm.2‖ ^ 2) / μ := by
    apply (le_div_iff₀ hμ).mpr
    have hi : -(inner ℂ (u nm.1 - u nm.2) (v nm.1 - v nm.2)).re ≤
        ‖u nm.1 - u nm.2‖ * ‖v nm.1 - v nm.2‖ :=
      (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
    nlinarith only [hb nm.1 nm.2, hi]
  have hsq : Filter.Tendsto (fun nm : ℕ × ℕ => ‖G nm.1 - G nm.2‖ ^ 2)
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) hup
    simpa only [zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
      zero_div] using ((hdu.mul hdv).add ((hdu.pow 2).const_mul L)).div_const μ
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, dist_eq_norm, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using hs

private theorem c18_weak_principal_continuous_left {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    Continuous (fun G => c18_weak_principal a ha G H) := by
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  exact (c18_mass_pairing.flip (H j)).continuous.comp
    ((c18_coefficient_mul (fun x => (a x j k : ℂ)) (ha j k)).continuous.comp
      (continuous_apply k))

private theorem c18_weak_column_continuous_left {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d)
    (v : Lp ℂ 2 (volume : Measure (Vec d))) :
    Continuous (fun G => c18_weak_column a ha i G v) := by
  apply continuous_finset_sum
  intro j _
  exact (c18_mass_pairing.flip v).continuous.comp
    ((c18_coefficient_mul (fun x => (a x j i : ℂ)) (ha j i)).continuous.comp
      (continuous_apply j))

private theorem c18_weak_column_continuous_right {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    Continuous (fun v => c18_weak_column a ha i G v) := by
  apply continuous_finset_sum
  intro j _
  exact (c18_mass_pairing
    (c18_coefficient_mul (fun x => (a x j i : ℂ)) (ha j i) (G j))).continuous

/-- Strong convergence of both coordinates closes the actual forward
physical generator graph. Coercivity supplies convergence of the gradients. -/
theorem c18_physical_generator_pair_of_tendsto
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    {u v : ℕ → Lp ℂ 2 (volume : Measure (Vec d))}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : Filter.Tendsto u Filter.atTop (𝓝 f))
    (hv : Filter.Tendsto v Filter.atTop (𝓝 g))
    (hp : ∀ n, IsPhysicalComplexGeneratorPair ω.1 i ζ (u n) (v n)) :
    IsPhysicalComplexGeneratorPair ω.1 i ζ f g := by
  classical
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ hΛ0 hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  choose G hG hw using fun n => (c18_forward_graph_iff ω.1 ha i ζ (u n) (v n)).mp (hp n)
  have hC : CauchySeq G := c18_cauchy_gradient_of_coercive_differences u v G
    hu.cauchySeq hv.cauchySeq (1 / (4 * Λ)) ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2)
    (by positivity) (fun n m => by
      obtain ⟨W, hW, hb⟩ := c18_physical_generator_coercive ω.1 i ζ ha hΛ0 hA
        (c18_physical_generator_pair_sub ω.1 ha i ζ (hp n) (hp m))
      have he := physicalH1Graph_gradient_unique volume (Or.inl rfl)
        (u n - u m) W (G n - G m) hW (c18_physicalH1_sub (hG n) (hG m))
      rw [he] at hb
      exact (mul_le_mul_of_nonneg_left (c18_pi_norm_sq_le_sum (G n - G m))
        (by positivity : 0 ≤ 1 / (4 * Λ))).trans hb)
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hC
  apply (c18_forward_graph_iff ω.1 ha i ζ f g).mpr
  refine ⟨H, physicalH1Graph_of_tendsto volume (Or.inl rfl)
    (fun n => (u n, G n)) (f, H) hG (hu.prodMk_nhds hH), ?_⟩
  intro w W hW
  have hm := ((c18_mass_pairing.flip w).continuous.tendsto g).comp hv
  have hpr := ((c18_weak_principal_continuous_left ω.1 ha W).tendsto H).comp hH
  have hcol := ((c18_weak_column_continuous_left ω.1 ha i w).tendsto H).comp hH
  have hr := (hpr.const_mul (-(1 / 2 : ℂ))).add (hcol.const_mul ζ)
  have he : Filter.Tendsto (fun n => c18_mass_pairing (v n) w) Filter.atTop
      (𝓝 (-(1 / 2 : ℂ) * c18_weak_principal ω.1 ha H W +
        ζ * c18_weak_column ω.1 ha i H w)) :=
    hr.congr' (Filter.Eventually.of_forall fun n => (hw n w W hW).symm)
  exact tendsto_nhds_unique hm he

/-- The actual bilinear transpose generator graph is also closed under
strong convergence of its value and generator coordinates. -/
theorem c18_physical_transpose_generator_pair_of_tendsto
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    {u v : ℕ → Lp ℂ 2 (volume : Measure (Vec d))}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : Filter.Tendsto u Filter.atTop (𝓝 f))
    (hv : Filter.Tendsto v Filter.atTop (𝓝 g))
    (hp : ∀ n, IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (u n) (v n)) :
    IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g := by
  classical
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ hΛ0 hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  choose G hG hw using fun n => (c18_transpose_graph_iff ω.1 ha i ζ (u n) (v n)).mp (hp n)
  have hC : CauchySeq G := c18_cauchy_gradient_of_coercive_differences u v G
    hu.cauchySeq hv.cauchySeq (1 / (4 * Λ)) ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2)
    (by positivity) (fun n m => by
      obtain ⟨W, hW, hb⟩ := c18_physical_transpose_generator_coercive ω.1 i ζ ha hΛ0 hA
        (c18_physical_transpose_generator_pair_sub ω.1 ha i ζ (hp n) (hp m))
      have he := physicalH1Graph_gradient_unique volume (Or.inl rfl)
        (u n - u m) W (G n - G m) hW (c18_physicalH1_sub (hG n) (hG m))
      rw [he] at hb
      exact (mul_le_mul_of_nonneg_left (c18_pi_norm_sq_le_sum (G n - G m))
        (by positivity : 0 ≤ 1 / (4 * Λ))).trans hb)
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hC
  apply (c18_transpose_graph_iff ω.1 ha i ζ f g).mpr
  refine ⟨H, physicalH1Graph_of_tendsto volume (Or.inl rfl)
    (fun n => (u n, G n)) (f, H) hG (hu.prodMk_nhds hH), ?_⟩
  intro w W hW
  have hm := ((c18_mass_pairing.flip w).continuous.tendsto g).comp hv
  have hpr := ((c18_weak_principal_continuous_left
    (fun x j k => ω.1 x k j) (fun j k => ha k j) W).tendsto H).comp hH
  have hcol := ((c18_weak_column_continuous_right ω.1 ha i W).tendsto f).comp hu
  have hr := (hpr.const_mul (-(1 / 2 : ℂ))).add (hcol.const_mul ζ)
  have he : Filter.Tendsto (fun n => c18_mass_pairing (v n) w) Filter.atTop
      (𝓝 (-(1 / 2 : ℂ) *
        c18_weak_principal (fun x j k => ω.1 x k j) (fun j k => ha k j) H W +
          ζ * c18_weak_column ω.1 ha i W f)) :=
    hr.congr' (Filter.Eventually.of_forall fun n => (hw n w W hW).symm)
  exact tendsto_nhds_unique hm he

/-- Dissipation and integrated coercivity bound the generator endpoint.
The reference datum `F` permits a preceding semigroup time split. -/
private theorem c18_generator_endpoint_from_dissipation
    {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen)
    (μ L K J ν A D : ℝ) (hμ : 0 < μ) (hL : 0 ≤ L)
    (hK : 0 ≤ K) (hJ : 0 ≤ J) (hν : 0 < ν)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖)
    (F f g : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : ∀ j, Continuous (fun s => G s j)) (t : ℝ≥0) (ht : 0 < t)
    (henergy : μ * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
      (‖f‖ ^ 2 - ‖P t f‖ ^ 2) / 2 +
        L * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2))
    (hzero : (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G 0 k x * star (G 0 j x)).re ≤ A * ‖F‖ ^ 2)
    (hdatum : ‖f‖ ^ 2 ≤ D * ‖F‖ ^ 2)
    (hdiss : let q : ℝ → ℝ := fun s => (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * G s k x * star (G s j x)).re
      ν * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal g‖ ^ 2) ≤
        q 0 - q t + K * (∫ s in (0 : ℝ)..(t : ℝ), q s) +
          J * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2)) :
    ‖P t g‖ ^ 2 ≤
      (Real.exp (L * (t : ℝ)) ^ 2 *
        (A + (K * Λ * (d : ℝ) *
          ((1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ) +
            J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ)) * D) /
              (ν * (t : ℝ))) * ‖F‖ ^ 2 := by
  let q : ℝ → ℝ := fun s => (∫ x, ∑ j, ∑ k,
    (a x j k : ℂ) * G s k x * star (G s j x)).re
  let B := (1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hqc : Continuous q := c18_physical_principal_form_continuous a ha G hG
  have hqp (s : ℝ) : q s ≤ Λ * (d : ℝ) * ‖G s‖ ^ 2 := by
    have hb := c18_physical_principal_energy_upper a ha hA (G s)
    have hn : (∑ j, ‖G s j‖ ^ 2) ≤ (d : ℝ) * ‖G s‖ ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin d, ‖G s‖ ^ 2 := Finset.sum_le_sum fun j _ =>
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm (G s) j)
        _ = _ := by simp
    exact hb.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hn hΛ.le)
  have hnonneg : 0 ≤ q t := by
    have hb := c18_physical_principal_energy_coercive a ha hΛ hA (G t)
    have hn : 0 ≤ ∑ j, ‖G t j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    change (∑ j, ‖G t j‖ ^ 2) ≤ Λ * q t at hb
    nlinarith only [hb, hn, hΛ]
  have hint := c18_integrated_gradient_bound hP μ L hμ hL hgrowth f G hG t henergy
  have hqi : (∫ s in (0 : ℝ)..(t : ℝ), q s) ≤
      Λ * (d : ℝ) * B * ‖f‖ ^ 2 := by
    have hgcont : Continuous (fun s => ‖G s‖ ^ 2) := (continuous_pi hG).norm.pow 2
    have hi := intervalIntegral.integral_mono_on t.property
      (hqc.intervalIntegrable (μ := volume) 0 t)
      ((hgcont.const_mul (Λ * (d : ℝ))).intervalIntegrable (μ := volume) 0 t)
      (fun s _ => hqp s)
    rw [intervalIntegral.integral_const_mul] at hi
    have heq : (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2) =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2 := by
      erw [intervalIntegral.integral_of_le t.property, ← integral_Icc_eq_integral_Ioc]
      rfl
    erw [heq] at hi
    exact hi.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hint (mul_nonneg hΛ.le (Nat.cast_nonneg d)))
  have hsq (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      ‖P s.toNNReal f‖ ^ 2 ≤ Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
    have he : Real.exp (L * (s.toNNReal : ℝ)) ≤ Real.exp (L * (t : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by simpa only [Real.coe_toNNReal _ hs.1] using hs.2) hL)
    have hb := (hgrowth f s.toNNReal).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg f))
    exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb).trans_eq (mul_pow _ _ _)
  have hui : (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2) ≤
      Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) * ‖f‖ ^ 2 := by
    have hc : Continuous (fun s : ℝ => ‖P s.toNNReal f‖ ^ 2) :=
      ((hP.cont f).comp continuous_real_toNNReal).norm.pow 2
    have hi := intervalIntegral.integral_mono_on t.property
      (hc.intervalIntegrable (μ := volume) 0 t) (intervalIntegrable_const (μ := volume)) hsq
    have hconst : (∫ _s in (0 : ℝ)..(t : ℝ),
        Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2) =
          Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) * ‖f‖ ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring
    have hi' := hi.trans_eq hconst
    convert hi' using 1 <;> rfl
  have hiq := mul_le_mul_of_nonneg_left hqi hK
  have hiu := mul_le_mul_of_nonneg_left hui hJ
  have hdata := mul_le_mul_of_nonneg_left hdatum
    (show 0 ≤ K * Λ * (d : ℝ) * B + J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) by positivity)
  have hb : ν * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal g‖ ^ 2) ≤
      (A + (K * Λ * (d : ℝ) * B +
        J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ)) * D) * ‖F‖ ^ 2 := by
    change ν * _ ≤ q 0 - q t + K * _ + J * _ at hdiss
    change q 0 ≤ _ at hzero
    nlinarith only [hdiss, hzero, hnonneg, hiq, hiu, hdata]
  have he := c18_semigroup_endpoint_norm_from_integral hP L hL hgrowth g t
  have he' := mul_le_mul_of_nonneg_left he hν.le
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg (Real.exp (L * (t : ℝ))))
  have ht' : (0 : ℝ) < t := ht
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hν ht')).mpr
  dsimp [B] at hb'
  nlinarith only [he', hb']

/-- A half-time split removes all dependence on the initial generator image
from the actual twice-domain generator endpoint bound. -/
theorem c18_physical_D2_generator_at_time
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P) (t : ℝ≥0) (ht : 0 < t) :
    ∃ C : ℝ, ∀ f g h : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair a i ζ f g →
      IsPhysicalComplexGeneratorPair a i ζ g h →
      ‖P t g‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  let τ : ℝ≥0 := t / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hττ : τ + τ = t := add_halves t
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2
  let J : ℝ := 0
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hgrowth : ∀ f s, ‖P s f‖ ≤ Real.exp (L * (s : ℝ)) * ‖f‖ := by
    intro f s
    apply hp.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f s
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_generator_coercive a i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]
  obtain ⟨C₀, hC₀⟩ := c18_physical_D2_gradient_at_time a i ζ ha hΛ hA P hP τ hτ
  refine ⟨Real.exp (L * (τ : ℝ)) ^ 2 *
    (Λ * C₀ + (K * Λ * (d : ℝ) *
      ((1 / 2 + L * (Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ))) / μ) +
        J * Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ)) *
          Real.exp (L * (τ : ℝ)) ^ 2) / (3 * (τ : ℝ)), ?_⟩
  intro f g h hfg hgh
  have hfg' := hp.map_gen hfg τ
  have hgh' := hp.map_gen hgh τ
  obtain ⟨G, hG, hGc, hdiss⟩ := c18_physical_D2_integrated_generator a i ζ ha hΛ hA P hP hfg' hgh'
  obtain ⟨H, hH, _, henergy⟩ := c18_physical_orbit_integrated_gradient a i ζ ha hΛ hA P hP hfg'
  have heq : (∫ s in (0 : ℝ)..(τ : ℝ), ∑ j, ‖G s j‖ ^ 2) =
      ∫ s in (0 : ℝ)..(τ : ℝ), ∑ j, ‖H s j‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := (Set.uIcc_of_le τ.property ▸ hs).1
    dsimp only
    rw [physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (P s.toNNReal (P τ f)) (G s) (H s) (hG s hs') (hH s)]
  obtain ⟨V, hV, hbV⟩ := hC₀ f g h hfg hgh
  have hz : G 0 = V := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (P τ f) (G 0) V
    (by simpa only [Real.toNNReal_zero, hp.zero, ContinuousLinearMap.id_apply]
      using hG 0 le_rfl) hV
  have hzero : (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G 0 k x * star (G 0 j x)).re ≤ (Λ * C₀) * ‖f‖ ^ 2 := by
    rw [hz]
    exact (c18_physical_principal_energy_upper a ha hA V).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbV hΛ.le)
  have hdatum : ‖P τ f‖ ^ 2 ≤ Real.exp (L * (τ : ℝ)) ^ 2 * ‖f‖ ^ 2 :=
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hgrowth f τ)).trans_eq
      (mul_pow _ _ _)
  have hb := c18_generator_endpoint_from_dissipation a ha hΛ hA hp
    μ L K J 3 (Λ * C₀) (Real.exp (L * (τ : ℝ)) ^ 2)
    hμ hL hK hJ (by norm_num) hgrowth f (P τ f) (P τ g) G hGc τ hτ
    (by rw [heq]; exact henergy τ) hzero hdatum
    (by simpa only [J, K, zero_mul, add_zero] using hdiss τ)
  have htcomp : P τ (P τ g) = P t g := by
    rw [← ContinuousLinearMap.comp_apply, ← hp.add, hττ]
  rwa [htcomp] at hb

/-- A half-time split removes all dependence on the initial generator image
from the actual transpose twice-domain generator endpoint bound. -/
theorem c18_physical_transpose_D2_generator_at_time
    {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hsmooth : IsSmoothWithBounds M ω) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag) (t : ℝ≥0) (ht : 0 < t) :
    ∃ C : ℝ, ∀ f g h : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g →
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h →
      ‖Pdag t g‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  let hp : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  let τ : ℝ≥0 := t / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hττ : τ + τ = t := add_halves t
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2
  let J : ℝ := 4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hgrowth : ∀ f s, ‖Pdag s f‖ ≤ Real.exp (L * (s : ℝ)) * ‖f‖ := by
    intro f s
    apply hp.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f s
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_transpose_generator_coercive ω.1 i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]
  obtain ⟨C₀, hC₀⟩ := c18_physical_transpose_D2_gradient_at_time hsmooth i ζ ha hΛ hA P Pdag hPdag τ hτ
  refine ⟨Real.exp (L * (τ : ℝ)) ^ 2 *
    (Λ * C₀ + (K * Λ * (d : ℝ) *
      ((1 / 2 + L * (Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ))) / μ) +
        J * Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ)) *
          Real.exp (L * (τ : ℝ)) ^ 2) / (2 * (τ : ℝ)), ?_⟩
  intro f g h hfg hgh
  have hfg' := hp.map_gen hfg τ
  have hgh' := hp.map_gen hgh τ
  obtain ⟨G, hG, hGc, hdiss⟩ := c18_physical_transpose_D2_integrated_generator hsmooth i ζ ha hΛ hA P Pdag hPdag hfg' hgh'
  obtain ⟨H, hH, _, henergy⟩ := c18_physical_transpose_orbit_integrated_gradient ω.1 i ζ ha hΛ hA P Pdag hPdag hfg'
  have heq : (∫ s in (0 : ℝ)..(τ : ℝ), ∑ j, ‖G s j‖ ^ 2) =
      ∫ s in (0 : ℝ)..(τ : ℝ), ∑ j, ‖H s j‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := (Set.uIcc_of_le τ.property ▸ hs).1
    dsimp only
    rw [physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (Pdag s.toNNReal (Pdag τ f)) (G s) (H s) (hG s hs') (hH s)]
  obtain ⟨V, hV, hbV⟩ := hC₀ f g h hfg hgh
  have hz : G 0 = V := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (Pdag τ f) (G 0) V
    (by simpa only [Real.toNNReal_zero, hp.zero, ContinuousLinearMap.id_apply]
      using hG 0 le_rfl) hV
  have hzero : (∫ x, ∑ j, ∑ k,
      (ω.1 x j k : ℂ) * G 0 k x * star (G 0 j x)).re ≤ (Λ * C₀) * ‖f‖ ^ 2 := by
    rw [hz]
    exact (c18_physical_principal_energy_upper ω.1 ha hA V).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbV hΛ.le)
  have hdatum : ‖Pdag τ f‖ ^ 2 ≤ Real.exp (L * (τ : ℝ)) ^ 2 * ‖f‖ ^ 2 :=
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hgrowth f τ)).trans_eq
      (mul_pow _ _ _)
  have hb := c18_generator_endpoint_from_dissipation ω.1 ha hΛ hA hp
    μ L K J 2 (Λ * C₀) (Real.exp (L * (τ : ℝ)) ^ 2)
    hμ hL hK hJ (by norm_num) hgrowth f (Pdag τ f) (Pdag τ g) G hGc τ hτ
    (by rw [heq]; exact henergy τ) hzero hdatum
    (by simpa only [J, K, zero_mul, add_zero] using hdiss τ)
  have htcomp : Pdag τ (Pdag τ g) = Pdag t g := by
    rw [← ContinuousLinearMap.comp_apply, ← hp.add, hττ]
  rwa [htcomp] at hb

/-- A closed generator graph and a bound on its second domain give
positive-time domain smoothing for all initial Hilbert-space data. -/
private theorem c18_semigroup_generator_of_D2_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen)
    (happrox : ∀ f g, Gen f g → ∃ F G H : ℝ → E,
      (∀ δ, 0 < δ → Gen (F δ) (G δ) ∧ Gen (G δ) (H δ)) ∧
      Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds f) ∧
      Filter.Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds g))
    (hclosed : ∀ (u v : ℕ → E) (f g : E),
      Filter.Tendsto u Filter.atTop (𝓝 f) → Filter.Tendsto v Filter.atTop (𝓝 g) →
      (∀ n, Gen (u n) (v n)) → Gen f g)
    (t : ℝ≥0) (C : ℝ)
    (hbound : ∀ f g h, Gen f g → Gen g h → ‖P t g‖ ^ 2 ≤ C * ‖f‖ ^ 2)
    (f : E) : ∃ g, Gen (P t f) g := by
  classical
  let D2 : Set E := {u | ∃ v w, Gen u v ∧ Gen v w}
  have hfirst (u v : E) (huv : Gen u v) : u ∈ closure D2 := by
    obtain ⟨F, G, H, hgen, hF, _⟩ := happrox u v huv
    apply mem_closure_of_tendsto hF
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ⟨G δ, H δ, hgen δ hδ⟩
  have hdense : Dense D2 := by
    intro u
    obtain ⟨F, G, hgen, hF⟩ := hP.exists_gen_approx u
    apply isClosed_closure.mem_of_tendsto hF
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hfirst (F δ) (G δ) (hgen δ hδ)
  obtain ⟨F, hF, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense f)
  change ∀ n, ∃ v w, Gen (F n) v ∧ Gen v w at hF
  choose g h hg hh using hF
  let V : ℕ → E := fun n => P t (g n)
  have hdiff (n m : ℕ) : ‖V n - V m‖ ^ 2 ≤ C * ‖F n - F m‖ ^ 2 := by
    simpa only [map_sub] using hbound (F n - F m) (g n - g m) (h n - h m)
      (c18_gen_sub hP (hg n) (hg m)) (c18_gen_sub hP (hh n) (hh m))
  have hV : CauchySeq V := c18_cauchy_of_norm_sq_bound V F hlim.cauchySeq C hdiff
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hV
  exact ⟨v, hclosed (fun n => P t (F n)) V (P t f) v
    (((P t).continuous.tendsto f).comp hlim) hv (fun n => hP.map_gen (hg n) t)⟩

/-- Every positive time of both actual physical evolutions belongs to its
full weak generator domain, for arbitrary initial L2 data. -/
theorem c18_physical_positive_time_generator_pairs
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag) :
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)), ∀ t : ℝ≥0, 0 < t →
      (∃ g : Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexGeneratorPair ω.1 i ζ (P t f) g) ∧
      (∃ gdag : Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (Pdag t f) gdag) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ hΛ0 hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  intro f t ht
  constructor
  · obtain ⟨C, hC⟩ := c18_physical_D2_generator_at_time ω.1 i ζ ha hΛ0 hA P hP t ht
    exact c18_semigroup_generator_of_D2_bound
      (⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩ :
        S5Semigroup P (IsPhysicalComplexGeneratorPair ω.1 i ζ))
      (fun u v huv => c18_physical_generator_D2_approx ω.1 i ζ P hP huv)
      (fun u v f g hu hv hp => c18_physical_generator_pair_of_tendsto
        hΛ hell hsmooth hu hv hp) t C hC f
  · obtain ⟨C, hC⟩ := c18_physical_transpose_D2_generator_at_time hsmooth i ζ ha hΛ0 hA
      P Pdag hPdag t ht
    exact c18_semigroup_generator_of_D2_bound
      (⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩ :
        S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ))
      (fun u v huv => c18_physical_transpose_generator_D2_approx
        ω.1 i ζ P Pdag hPdag huv)
      (fun u v f g hu hv hp => c18_physical_transpose_generator_pair_of_tendsto
        hΛ hell hsmooth hu hv hp) t C hC f

private theorem c18_semigroup_generator_chains
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen)
    (hreg : ∀ (f : E) (t : ℝ≥0), 0 < t → ∃ g, Gen (P t f) g) :
    ∀ (n : ℕ) (f : E) (t : ℝ≥0), 0 < t →
      ∃ u : Fin (n + 1) → E, u 0 = P t f ∧
        ∀ k : Fin n, Gen (u k.castSucc) (u k.succ) := by
  intro n
  induction n with
  | zero =>
      intro f t ht
      exact ⟨fun _ => P t f, rfl, fun k => Fin.elim0 k⟩
  | succ n ih =>
      intro f t ht
      let τ : ℝ≥0 := t / 2
      have hτ : 0 < τ := by dsimp [τ]; positivity
      have hττ : τ + τ = t := add_halves t
      obtain ⟨g, hg⟩ := hreg f τ hτ
      obtain ⟨u, hu, hchain⟩ := ih g τ hτ
      have hfirst : Gen (P t f) (u 0) := by
        have hm := hP.map_gen hg τ
        have hc : P τ (P τ f) = P t f := by
          rw [← ContinuousLinearMap.comp_apply, ← hP.add, hττ]
        rwa [hc, ← hu] at hm
      refine ⟨Fin.cons (P t f) u, Fin.cons_zero _ _, ?_⟩
      intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · change Gen (P t f) (u 0)
        exact hfirst
      · change Gen (u j.castSucc) (u j.succ)
        exact hchain j

theorem c18_physical_positive_time_generator_chains
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag) :
    ∀ (n : ℕ) (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0), 0 < t →
      ∃ u v : Fin (n+1) → Lp ℂ 2 (volume : Measure (Vec d)),
        u 0 = P t f ∧ v 0 = Pdag t f ∧ ∀ k : Fin n,
          IsPhysicalComplexGeneratorPair ω.1 i ζ (u k.castSucc) (u k.succ) ∧
          IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (v k.castSucc) (v k.succ) := by
  intro n f t ht
  obtain ⟨u, hu, huchain⟩ := c18_semigroup_generator_chains
    (⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩ :
      S5Semigroup P (IsPhysicalComplexGeneratorPair ω.1 i ζ))
    (fun g s hs =>
      (c18_physical_positive_time_generator_pairs hΛ hell hsmooth hP hPdag g s hs).1)
    n f t ht
  obtain ⟨v, hv, hvchain⟩ := c18_semigroup_generator_chains
    (⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩ :
      S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ))
    (fun g s hs =>
      (c18_physical_positive_time_generator_pairs hΛ hell hsmooth hP hPdag g s hs).2)
    n f t ht
  exact ⟨u, v, hu, hv, fun k => ⟨huchain k, hvchain k⟩⟩

private theorem c18_physical_smooth_test {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∃ (v : Lp ℂ 2 (volume : Measure (Vec d)))
      (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) v H ∧
      (v : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ)) ∧
      ∀ j, (H j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (coordinateDerivative j φ x : ℂ)) := by
  have hφ2 : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).ofReal
  have hD2 (j : Fin d) :
      MemLp (fun x => (coordinateDerivative j φ x : ℂ)) 2 volume :=
    (((hφ.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
        (hφc.fderiv_apply ℝ (unitVector j))).ofReal
  let v := hφ2.toLp (fun x => (φ x : ℂ))
  let H := fun j => (hD2 j).toLp (fun x => (coordinateDerivative j φ x : ℂ))
  have hv : (v : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ)) := hφ2.coeFn_toLp
  have hH (j : Fin d) : (H j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (coordinateDerivative j φ x : ℂ)) := (hD2 j).coeFn_toLp
  refine ⟨v, H, ?_, hv, hH⟩
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) v H
    (fun x => (φ x : ℂ)) (fun j x => (coordinateDerivative j φ x : ℂ)) hv hH).mpr
  constructor
  · intro j
    simpa only [Complex.ofReal_re] using
      hasWeakPartialDerivative_of_contDiff j φ (hφ.of_le (by simp))
  · intro j
    have hzero : coordinateDerivative j (fun _ : Vec d => (0 : ℝ)) =
        fun _ => 0 := by
      funext x
      unfold coordinateDerivative
      rw [fderiv_const_apply, ContinuousLinearMap.zero_apply]
    simpa only [Complex.ofReal_im, hzero] using
      hasWeakPartialDerivative_of_contDiff j (fun _ : Vec d => (0 : ℝ)) contDiff_const

/-- The actual forward weak graph yields the smooth-test elliptic equation.
The drift remains scalar forcing involving the chosen physical gradient. -/
theorem c18_physical_generator_smooth_test_equation {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x *
      (coordinateDerivative j φ x : ℂ)) =
      -2 * (∫ x, g x * (φ x : ℂ)) +
        2 * ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * (φ x : ℂ)) := by
  obtain ⟨G₀, hG₀, hweak⟩ := hfg
  have heq := physicalH1Graph_gradient_unique volume (Or.inl rfl) f G₀ G hG₀ hG
  subst G₀
  obtain ⟨v, H, hvH, hv, hH⟩ := c18_physical_smooth_test φ hφ hφc
  have hw := hweak v H hvH
  have hm : (∫ x, g x * v x) = ∫ x, g x * (φ x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  have hp : (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * H j x) =
      ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x *
        (coordinateDerivative j φ x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hH] with x hx
    simp only [hx]
  have hb : (∫ x, (∑ j, (a x j i : ℂ) * G j x) * v x) =
      ∫ x, (∑ j, (a x j i : ℂ) * G j x) * (φ x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  rw [hm, hp, hb] at hw
  linear_combination 2 * hw

/-- The actual bilinear transpose gives the elliptic divergence forcing with
the same signed complex force and the transposed principal matrix. -/
theorem c18_physical_transpose_generator_smooth_test_equation {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x *
      (coordinateDerivative j φ x : ℂ)) =
      -2 * (∫ x, g x * (φ x : ℂ)) +
        2 * ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) *
          (coordinateDerivative j φ x : ℂ))) := by
  obtain ⟨G₀, hG₀, hweak⟩ := hfg
  have heq := physicalH1Graph_gradient_unique volume (Or.inl rfl) f G₀ G hG₀ hG
  subst G₀
  obtain ⟨v, H, hvH, hv, hH⟩ := c18_physical_smooth_test φ hφ hφc
  have hw := hweak v H hvH
  have hm : (∫ x, g x * v x) = ∫ x, g x * (φ x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  have hp : (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * H j x) =
      ∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x *
        (coordinateDerivative j φ x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hH] with x hx
    simp only [hx]
  have hb : (∫ x, f x * (∑ j, (a x j i : ℂ) * H j x)) =
      ∫ x, f x * (∑ j, (a x j i : ℂ) * (coordinateDerivative j φ x : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hH] with x hx
    simp only [hx]
  rw [hm, hp, hb] at hw
  linear_combination 2 * hw

/-- The actual structural first derivative bound controls coordinate
translation commutators, uniformly in the translation step. -/
theorem c18_smooth_coefficient_coordinate_difference_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω) (l j k : Fin d)
    (x : Vec d) (h : ℝ) :
    |ω.1 (x + h • unitVector l) j k - ω.1 x j k| ≤ M 1 * |h| := by
  let F : ℝ → ℝ := fun t => ω.1 (x + t • unitVector l) j k
  have hF (t : ℝ) : HasDerivAt F
      (coordinateDerivative l (fun y => ω.1 y j k) (x + t • unitVector l)) t := by
    have ht := ((hasDerivAt_id' t).smul_const (unitVector l)).const_add x
    have hc := (hsmooth.1.1 j k).differentiable (by simp)
    simpa only [F, coordinateDerivative, Function.comp_def, one_smul] using
      (hc _).hasFDerivAt.comp_hasDerivAt t ht
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := h)
    (fun t _ => (hF t).hasDerivWithinAt)
    (fun t _ => by
      simpa only [Real.norm_eq_abs] using
        c18_smooth_coefficient_derivative_bound hsmooth l j k (x + t • unitVector l))
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ _) (Set.mem_univ _)
  simpa [F, Real.norm_eq_abs] using hb

private theorem c18_weak_partial_derivative_translate {d : ℕ} {j : Fin d}
    {u g : Vec d → ℝ} (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hw : HasWeakPartialDerivative Set.univ j u g) (z : Vec d) :
    HasWeakPartialDerivative Set.univ j (fun x => u (x - z))
      (fun x => g (x - z)) := by
  have hz := measurePreserving_sub_right (volume : Measure (Vec d)) z
  have hu' := hu.comp_measurePreserving hz
  have hg' := hg.comp_measurePreserving hz
  have hp : PDE.HasWeakPartialDerivOn Set.univ j u g := by
    intro φ hφ hφc hφs
    exact hw.2.2 φ ⟨hφ, hφc, hφs⟩
  have ht := hp.translate z
  have hU : PDE.translateSet z (Set.univ : Set (Vec d)) = Set.univ := by
    ext x
    simp only [PDE.mem_translateSet_iff_sub_mem, Set.mem_univ]
  rw [hU] at ht
  refine ⟨locallyIntegrableOn_univ.mpr (hu'.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_univ.mpr (hg'.locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ
  exact ht φ hφ.1 hφ.2.1 hφ.2.2

/-- Translation preserves the actual physical H1 graph and all component L2
norms. These witnesses can therefore be used in the full generator equations. -/
theorem c18_physical_H1_translation {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) (z : Vec d) :
    ∃ (f' : Lp ℂ 2 (volume : Measure (Vec d)))
      (G' : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) f' G' ∧
      (f' : Vec d → ℂ) =ᵐ[volume] (fun x => f (x - z)) ∧
      (∀ j, (G' j : Vec d → ℂ) =ᵐ[volume] (fun x => G j (x - z))) ∧
      ‖f'‖ = ‖f‖ ∧ ∀ j, ‖G' j‖ = ‖G j‖ := by
  have hz := measurePreserving_sub_right (volume : Measure (Vec d)) z
  let f' := Lp.compMeasurePreserving (fun x => x - z) hz f
  let G' := fun j => Lp.compMeasurePreserving (fun x => x - z) hz (G j)
  have hf' : (f' : Vec d → ℂ) =ᵐ[volume] (fun x => f (x - z)) :=
    Lp.coeFn_compMeasurePreserving f hz
  have hG' (j : Fin d) : (G' j : Vec d → ℂ) =ᵐ[volume]
      (fun x => G j (x - z)) := Lp.coeFn_compMeasurePreserving (G j) hz
  refine ⟨f', G', ?_, hf', hG', ?_, ?_⟩
  · apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) f' G'
      (fun x => f (x - z)) (fun j x => G j (x - z)) hf' hG').mpr
    constructor
    · intro j
      exact c18_weak_partial_derivative_translate (Lp.memLp f).re
        (Lp.memLp (G j)).re (hG.1 j) z
    · intro j
      exact c18_weak_partial_derivative_translate (Lp.memLp f).im
        (Lp.memLp (G j)).im (hG.2 j) z
  · exact Lp.norm_compMeasurePreserving f hz
  · intro j
    exact Lp.norm_compMeasurePreserving (G j) hz


private theorem c18_weakPartial_const_mul {d : ℕ} {j : Fin d}
    {f g : Vec d → ℝ} (hf : HasWeakPartialDerivative Set.univ j f g) (c : ℝ) :
    HasWeakPartialDerivative Set.univ j (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨hf.1.smul c, hf.2.1.smul c, ?_⟩
  intro φ hφ
  simp only [mul_assoc, integral_const_mul]
  rw [hf.2.2 φ hφ]
  ring

private theorem c18_physicalH1_smul {d : ℕ} (c : ℂ)
    {u : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G) :
    IsPhysicalH1Graph volume (Or.inl rfl) (c • u) (fun j => c • G j) := by
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
    (c • u) (fun j => c • G j) _ _ (Lp.coeFn_smul c u)
    (fun j => Lp.coeFn_smul c (G j))]
  constructor
  · intro j
    simpa only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, sub_eq_add_neg,
      neg_mul] using Correctors.hasWeakPartialDerivative_add
        (c18_weakPartial_const_mul (hu.1 j) c.re)
        (c18_weakPartial_const_mul (hu.2 j) (-c.im))
  · intro j
    simpa only [Pi.smul_apply, smul_eq_mul, Complex.mul_im] using
      Correctors.hasWeakPartialDerivative_add
        (c18_weakPartial_const_mul (hu.2 j) c.re)
        (c18_weakPartial_const_mul (hu.1 j) c.im)

/-- A translated difference quotient of a physical H1 function remains in the
same graph, with the corresponding difference quotients of its gradients. -/
theorem c18_physical_H1_difference_quotient {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) (z : Vec d) (t : ℝ) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume] (fun x => (t : ℂ)⁻¹ * (f (x - z) - f x)) ∧
      ∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (t : ℂ)⁻¹ * (G j (x - z) - G j x)) := by
  obtain ⟨f', G', hG', hf', hG'ae, _, _⟩ := c18_physical_H1_translation hG z
  refine ⟨(t : ℂ)⁻¹ • (f' - f), (fun j => (t : ℂ)⁻¹ • (G' j - G j)),
    c18_physicalH1_smul _ (c18_physicalH1_sub hG' hG), ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul ((t : ℂ)⁻¹) (f' - f), Lp.coeFn_sub f' f, hf']
      with x hs hd ht
    simp only [hs, Pi.smul_apply, hd, Pi.sub_apply, ht, smul_eq_mul]
  · intro j
    filter_upwards [Lp.coeFn_smul ((t : ℂ)⁻¹) (G' j - G j),
      Lp.coeFn_sub (G' j) (G j), hG'ae j] with x hs hd ht
    simp only [hs, Pi.smul_apply, hd, Pi.sub_apply, ht, smul_eq_mul]


/-- The structural derivative bound controls the signed coefficient
quotient at every nonzero step. -/
theorem c18_smooth_coefficient_coordinate_quotient_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω) (l j k : Fin d)
    (x : Vec d) {h : ℝ} (hh : h ≠ 0) :
    |(ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h| ≤ M 1 := by
  rw [abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hh)).2
  exact c18_smooth_coefficient_coordinate_difference_bound hsmooth l j k x h

/-- Every signed spatial difference quotient of an L2 representative is in
L2. This applies in particular to each component of a physical H1 gradient. -/
theorem c18_L2_coordinate_difference_quotient_memLp {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d))) (l : Fin d) (h : ℝ) :
    MemLp (fun x => (u (x + h • unitVector l) - u x) / (h : ℂ))
      2 (volume : Measure (Vec d)) := by
  have ht := (Lp.memLp u).comp_measurePreserving
    (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l))
  have hd := ht.sub (Lp.memLp u)
  simpa only [div_eq_mul_inv, mul_comm, Pi.sub_apply, Function.comp_apply] using
    hd.const_mul ((h : ℂ)⁻¹)


/-- The coefficient commutator quotient is an actual bounded measurable
multiplier, uniformly for all nonzero signed steps. -/
theorem c18_smooth_coefficient_coordinate_quotient_memLp_top {d : ℕ}
    {M : ℕ → ℝ} {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    MemLp (fun x => (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ))
      ∞ (volume : Measure (Vec d)) := by
  have hc : Continuous (fun x : Vec d =>
      (ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h) :=
    (((hsmooth.1.1 j k).continuous.comp (continuous_id.add continuous_const)).sub
      (hsmooth.1.1 j k).continuous).div_const h
  apply memLp_top_of_bound (Complex.continuous_ofReal.comp hc).aestronglyMeasurable (M 1)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
      c18_smooth_coefficient_coordinate_quotient_bound hsmooth l j k x hh


/-- Whole-space summation by parts for the actual complex L2 representatives.
The opposite shifts retain the sign of the real difference step. -/
theorem c18_L2_difference_quotient_integration_by_parts {d : ℕ}
    {u v : Vec d → ℂ} (hU : MemLp u 2 volume) (hV : MemLp v 2 volume)
    (z : Vec d) (h : ℝ) :
    (∫ x, ((u (x + z) - u x) / (h : ℂ)) * v x) =
      ∫ x, u x * ((v (x - z) - v x) / (h : ℂ)) := by
  have hp := measurePreserving_add_right (volume : Measure (Vec d)) z
  have hm := measurePreserving_sub_right (volume : Measure (Vec d)) z
  have hu := hU.comp_measurePreserving hp
  have hv := hV.comp_measurePreserving hm
  have h1 : Integrable (fun x => u (x + z) * v x) :=
    hu.integrable_mul hV
  have h2 : Integrable (fun x => u x * v x) :=
    hU.integrable_mul hV
  have h3 : Integrable (fun x => u x * v (x - z)) :=
    hU.integrable_mul hv
  have hchange := hp.integral_comp (Homeomorph.addRight z).measurableEmbedding
    (fun y : Vec d => u y * v (y - z))
  have hshift : (∫ x, u (x + z) * v x) = ∫ x, u x * v (x - z) := by
    simpa only [add_sub_cancel_right] using hchange
  have hl : (fun x => ((u (x + z) - u x) / (h : ℂ)) * v x) =
      (fun x => (u (x + z) * v x - u x * v x) * (h : ℂ)⁻¹) := by
    funext x
    simp only [div_eq_mul_inv]
    ring
  have hr : (fun x => u x * ((v (x - z) - v x) / (h : ℂ))) =
      (fun x => (u x * v (x - z) - u x * v x) * (h : ℂ)⁻¹) := by
    funext x
    simp only [div_eq_mul_inv]
    ring
  rw [hl, hr, integral_mul_const, integral_mul_const, integral_sub h1 h2,
    integral_sub h3 h2, hshift]


/-- The forward weak graph tested with the signed backward H1 quotient. -/
theorem c18_physical_generator_backward_quotient_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (l : Fin d) (h : ℝ) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (v (x - h • unitVector l) - v x)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (H j (x - h • unitVector l) - H j x))) ∧
      (∫ x, g x * q x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * Q j x) +
        ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * q x) := by
  obtain ⟨G₀, hG₀, hweak⟩ := hfg
  have heq := physicalH1Graph_gradient_unique volume (Or.inl rfl) f G₀ G hG₀ hG
  subst G₀
  obtain ⟨q, Q, hqQ, hq, hQ⟩ :=
    c18_physical_H1_difference_quotient hH (h • unitVector l) h
  exact ⟨q, Q, hqQ, hq, hQ, hweak q Q hqQ⟩

/-- The transpose weak graph tested with the signed backward H1 quotient. -/
theorem c18_physical_transpose_generator_backward_quotient_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (l : Fin d) (h : ℝ) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (v (x - h • unitVector l) - v x)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (H j (x - h • unitVector l) - H j x))) ∧
      (∫ x, g x * q x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * Q j x) +
        ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) * Q j x)) := by
  obtain ⟨G₀, hG₀, hweak⟩ := hfg
  have heq := physicalH1Graph_gradient_unique volume (Or.inl rfl) f G₀ G hG₀ hG
  subst G₀
  obtain ⟨q, Q, hqQ, hq, hQ⟩ :=
    c18_physical_H1_difference_quotient hH (h • unitVector l) h
  exact ⟨q, Q, hqQ, hq, hQ, hweak q Q hqQ⟩


/-- A fixed-step quotient is bounded on complex L2. This provides the
continuity needed to pass an H1 approximation through the quotient. -/
theorem c18_L2_coordinate_difference_quotient_norm_bound {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d))) (l : Fin d) (h : ℝ) :
    ∃ q : Lp ℂ 2 (volume : Measure (Vec d)),
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (u (x + h • unitVector l) - u x) / (h : ℂ)) ∧
      ‖q‖ ≤ |h|⁻¹ * (2 * ‖u‖) := by
  let z : Vec d := h • unitVector l
  let hp := measurePreserving_add_right (volume : Measure (Vec d)) z
  let v := Lp.compMeasurePreserving (fun x => x + z) hp u
  let q := (h : ℂ)⁻¹ • (v - u)
  refine ⟨q, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul ((h : ℂ)⁻¹) (v - u),
      Lp.coeFn_sub v u, Lp.coeFn_compMeasurePreserving u hp] with x hs hd hv
    change v x = u (x + z) at hv
    simp only [q, hs, Pi.smul_apply, hd, Pi.sub_apply, hv, smul_eq_mul,
      div_eq_mul_inv, mul_comm, z]
  · have hv : ‖v‖ = ‖u‖ := Lp.norm_compMeasurePreserving u hp
    have hsub : ‖v - u‖ ≤ 2 * ‖u‖ := by
      calc
        ‖v - u‖ ≤ ‖v‖ + ‖u‖ := norm_sub_le _ _
        _ = 2 * ‖u‖ := by rw [hv]; ring
    calc
      ‖q‖ = |h|⁻¹ * ‖v - u‖ := by
        simp only [q, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |h|⁻¹ * (2 * ‖u‖) := mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr (abs_nonneg h))


/-- Whole-space real Sobolev representatives have the supported approximation
needed by the difference-quotient estimate, with the same weak gradient. -/
private theorem c18_real_h1_supported_approximation {d : ℕ}
    (u : PDE.W1pFunction (Set.univ : Set (Vec d)) 2) :
    ∃ v : Homogenization.H10Function (Set.univ : Set (Vec d)),
      v.toH1Function.toFun = u.toFun ∧ v.toH1Function.grad = u.grad := by
  obtain ⟨a⟩ := u.hasSupportedSmoothApproximation_univ (by norm_num) (by norm_num)
  let w : Homogenization.H1Function (Set.univ : Set (Vec d)) :=
    { toFun := u.toFun
      grad := u.grad
      memL2 := u.memLp
      gradMemL2 := u.gradMemLp
      hasWeakGradient := by
        intro i φ hφ hc hs
        simpa only [PDE.basisVec, Homogenization.basisVec] using
          u.hasWeakGradient i φ hφ hc hs }
  refine ⟨{ toH1Function := w
            approx := a.approx
            approx_smooth := a.approx_smooth
            approx_hasCompactSupport := a.approx_hasCompactSupport
            approx_support_subset := a.approx_tsupport_subset
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, rfl, rfl⟩
  · change Filter.Tendsto (fun n => eLpNorm (a.approx n - u.toFun) 2
        (PDE.volumeOn Set.univ)) Filter.atTop (𝓝 0)
    exact a.tendsto_value
  · intro i
    simpa only [PDE.volumeOn, PDE.basisVec, Homogenization.basisVec] using a.tendsto_grad i

/-- The coordinate quotient of a real whole-space H1 representative is
controlled by the same weak derivative, with constant one. -/
private theorem c18_real_h1_coordinate_quotient_bound {d : ℕ}
    (u : PDE.W1pFunction (Set.univ : Set (Vec d)) 2)
    (i : Fin d) (h : ℝ) (hh : h ≠ 0) :
    eLpNorm (fun x => (u.toFun (x + h • unitVector i) - u.toFun x) / h)
      2 (volume : Measure (Vec d)) ≤
      eLpNorm (fun x => u.grad x i) 2 (volume : Measure (Vec d)) := by
  obtain ⟨v, hv, hgrad⟩ := c18_real_h1_supported_approximation u
  have hb := Homogenization.WeakPoissonEquationOn.eLpNorm_h10_backwardDifferenceQuotient_le_eLpNorm_grad
      MeasurableSet.univ v (Set.subset_univ _) (neg_ne_zero.mpr hh) i
  rw [hv, hgrad, Measure.restrict_univ] at hb
  convert hb using 1
  congr 1
  funext x
  simp only [Homogenization.euclideanBackwardDifferenceQuotient,
    Homogenization.euclideanCoordShift, Homogenization.basisVec, unitVector,
    neg_neg, div_neg]
  ring

/-- The real estimate applies directly to the project's weak-derivative
formulation, preserving the supplied representatives. -/
private theorem c18_real_weak_coordinate_quotient_bound {d : ℕ}
    (f : Vec d → ℝ) (G : Fin d → Vec d → ℝ)
    (hf : MemLp f 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hw : ∀ j, HasWeakPartialDerivative Set.univ j f (G j))
    (i : Fin d) (h : ℝ) (hh : h ≠ 0) :
    eLpNorm (fun x => (f (x + h • unitVector i) - f x) / h) 2 volume ≤
      eLpNorm (G i) 2 volume := by
  let u : PDE.W1pFunction (Set.univ : Set (Vec d)) 2 :=
    { toFun := f
      grad := fun x j => G j x
      memLp := by simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hf
      gradMemLp := by
        intro j
        simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hG j
      hasWeakGradient := by
        intro j φ hφ hc hs
        simpa only [PDE.basisVec, unitVector, coordinateDerivative] using
          (hw j).2.2 φ ⟨hφ, hc, hs⟩ }
  exact c18_real_h1_coordinate_quotient_bound u i h hh

/-- Each real component of the actual physical graph obeys the sharp
coordinate quotient estimate for its own weak derivative. -/
private theorem c18_physical_h1_component_quotient_bounds {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (i : Fin d) (h : ℝ) (hh : h ≠ 0) :
    (eLpNorm (fun x => ((f (x + h • unitVector i)).re - (f x).re) / h) 2 volume ≤
      eLpNorm (fun x => (G i x).re) 2 volume) ∧
    (eLpNorm (fun x => ((f (x + h • unitVector i)).im - (f x).im) / h) 2 volume ≤
      eLpNorm (fun x => (G i x).im) 2 volume) := by
  have hfre : MemLp (fun x => (f x).re) 2 volume := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp f)
  have hfim : MemLp (fun x => (f x).im) 2 volume := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.comp_memLp' (Lp.memLp f)
  have hGre : ∀ j, MemLp (fun x => (G j x).re) 2 volume := by
    intro j
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp (G j))
  have hGim : ∀ j, MemLp (fun x => (G j x).im) 2 volume := by
    intro j
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.comp_memLp' (Lp.memLp (G j))
  exact ⟨c18_real_weak_coordinate_quotient_bound _ _ hfre hGre hG.1 i h hh,
    c18_real_weak_coordinate_quotient_bound _ _ hfim hGim hG.2 i h hh⟩

/-- The squared complex L2 norm is the sum of its component energies. -/
private theorem c18_complex_L2_square_components {d : ℕ}
    (v : Vec d → ℂ) (hv : MemLp v 2 volume) :
    (eLpNorm v 2 volume).toReal ^ 2 =
      (eLpNorm (fun x => (v x).re) 2 volume).toReal ^ 2 +
      (eLpNorm (fun x => (v x).im) 2 volume).toReal ^ 2 := by
  have hr : MemLp (fun x => (v x).re) 2 volume := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using Complex.reCLM.comp_memLp' hv
  have hi : MemLp (fun x => (v x).im) 2 volume := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using Complex.imCLM.comp_memLp' hv
  have hri : Integrable (fun x => (v x).re ^ 2) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using hr.norm.integrable_sq
  have hii : Integrable (fun x => (v x).im ^ 2) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using hi.norm.integrable_sq
  rw [PDE.toReal_eLpNorm_two_sq_eq_integral_sq hr,
    PDE.toReal_eLpNorm_two_sq_eq_integral_sq hi, ← integral_add hri hii]
  rw [← eLpNorm_norm v hv.aestronglyMeasurable,
    PDE.toReal_eLpNorm_two_sq_eq_integral_sq hv.norm]
  congr 1 with x
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The physical H1 coordinate quotient is controlled by the same weak
coordinate derivative with the sharp constant one. -/
theorem c18_physical_H1_coordinate_difference_quotient_bound
    {d : ℕ} {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ((eLpNorm (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ))
      2 (volume : Measure (Vec d))).toReal) ≤ ‖G l‖ := by
  let q : Vec d → ℂ := fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)
  have hq : MemLp q 2 volume := c18_L2_coordinate_difference_quotient_memLp f l h
  have hGr : MemLp (fun x => (G l x).re) 2 volume := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp (G l))
  have hGi : MemLp (fun x => (G l x).im) 2 volume := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.comp_memLp' (Lp.memLp (G l))
  have hqr : (fun x => (q x).re) =
      (fun x => ((f (x + h • unitVector l)).re - (f x).re) / h) := by
    funext x
    simp only [q, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
      Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hqi : (fun x => (q x).im) =
      (fun x => ((f (x + h • unitVector l)).im - (f x).im) / h) := by
    funext x
    simp only [q, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  have hc := c18_physical_h1_component_quotient_bounds hG l h hh
  have hr := ENNReal.toReal_mono hGr.eLpNorm_ne_top hc.1
  have hi := ENNReal.toReal_mono hGi.eLpNorm_ne_top hc.2
  have hqeq := c18_complex_L2_square_components q hq
  rw [hqr, hqi] at hqeq
  have hGeq := c18_complex_L2_square_components (G l) (Lp.memLp (G l))
  have hnonqr : 0 ≤ (eLpNorm (fun x => ((f (x + h • unitVector l)).re - (f x).re) / h) 2 volume).toReal := ENNReal.toReal_nonneg
  have hnonqi : 0 ≤ (eLpNorm (fun x => ((f (x + h • unitVector l)).im - (f x).im) / h) 2 volume).toReal := ENNReal.toReal_nonneg
  have hnonq : 0 ≤ (eLpNorm q 2 volume).toReal := ENNReal.toReal_nonneg
  have hnonGr : 0 ≤ (eLpNorm (fun x => (G l x).re) 2 volume).toReal := ENNReal.toReal_nonneg
  have hnonGi : 0 ≤ (eLpNorm (fun x => (G l x).im) 2 volume).toReal := ENNReal.toReal_nonneg
  have hnonG : 0 ≤ (eLpNorm (G l) 2 volume).toReal := ENNReal.toReal_nonneg
  change (eLpNorm q 2 volume).toReal ≤ ‖G l‖
  rw [Lp.norm_def]
  nlinarith


/-- The sharp coordinate quotient estimate for the actual translated L2 class. -/
theorem c18_physical_H1_Lp_coordinate_difference_quotient_bound
    {d : ℕ} {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ‖(h : ℂ)⁻¹ •
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) f - f)‖
      ≤ ‖G l‖ := by
  let hp := measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)
  let v := Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l) hp f
  have hae : ((h : ℂ)⁻¹ • (v - f) : Lp ℂ 2 (volume : Measure (Vec d))) =ᵐ[volume]
      (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) := by
    filter_upwards [Lp.coeFn_smul ((h : ℂ)⁻¹) (v - f), Lp.coeFn_sub v f,
      Lp.coeFn_compMeasurePreserving f hp] with x hs hd hv
    change v x = f (x + h • unitVector l) at hv
    simp only [hs, Pi.smul_apply, hd, Pi.sub_apply, hv, smul_eq_mul,
      div_eq_mul_inv, mul_comm]
  change ‖(h : ℂ)⁻¹ • (v - f)‖ ≤ ‖G l‖
  rw [Lp.norm_def, eLpNorm_congr_ae hae]
  exact c18_physical_H1_coordinate_difference_quotient_bound hG l h hh


/-- Strong quotient convergence passes through approximation in the supplied
coordinate derivative, with the estimate uniform over nonzero steps. -/
private theorem c18_physical_H1_quotient_limit_of_approximation
    {d : ℕ} {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) (l : Fin d)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ (v : Lp ℂ 2 (volume : Measure (Vec d)))
        (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl) v H ∧ ‖G l - H l‖ < ε ∧
        Filter.Tendsto (fun h : ℝ => (h : ℂ)⁻¹ •
          (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
            (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) v - v))
          (𝓝[≠] (0 : ℝ)) (𝓝 (H l))) :
    Filter.Tendsto (fun h : ℝ => (h : ℂ)⁻¹ •
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) f - f))
      (𝓝[≠] (0 : ℝ)) (𝓝 (G l)) := by
  let T : ℝ → Lp ℂ 2 (volume : Measure (Vec d)) → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun h u => (h : ℂ)⁻¹ •
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) u - u)
  change Filter.Tendsto (fun h => T h f) (𝓝[≠] (0 : ℝ)) (𝓝 (G l))
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨v, H, hH, hgrad, hlim⟩ := happrox (ε / 4) (by positivity)
  have hlim' : Filter.Tendsto (fun h => T h v) (𝓝[≠] (0 : ℝ)) (𝓝 (H l)) := hlim
  filter_upwards [Metric.tendsto_nhds.1 hlim' (ε / 2) (by positivity),
    @self_mem_nhdsWithin ℝ _ 0 ({0}ᶜ)] with h hclose hh
  have hh' : h ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
  have hbound := c18_physical_H1_Lp_coordinate_difference_quotient_bound
    (c18_physicalH1_sub hG hH) l h hh'
  have hT : T h (f - v) = T h f - T h v := by
    dsimp only [T]
    simp only [map_sub, smul_sub]
    abel
  change ‖T h (f - v)‖ ≤ ‖G l - H l‖ at hbound
  rw [hT, ← dist_eq_norm] at hbound
  have hgrad' : dist (H l) (G l) < ε / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hgrad
  calc
    dist (T h f) (G l) ≤ dist (T h f) (T h v) + dist (T h v) (G l) :=
      dist_triangle _ _ _
    _ ≤ dist (T h f) (T h v) + (dist (T h v) (H l) + dist (H l) (G l)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε := by linarith


/-- A smooth signed coordinate quotient is the average of its coordinate
 derivative along the segment joining the two translated points. -/
private theorem c18_smooth_coordinate_quotient_eq_integral {d : ℕ}
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (l : Fin d) (x : Vec d) (h : ℝ) (hh : h ≠ 0) :
    (φ (x + h • unitVector l) - φ x) / h =
      ∫ t in (0 : ℝ)..1, coordinateDerivative l φ (x + (t * h) • unitVector l) := by
  let D : ℝ → ℝ := fun t => coordinateDerivative l φ (x + (t * h) • unitVector l)
  have hD : Continuous D := by
    have hc : Continuous (fun y : Vec d => coordinateDerivative l φ y) := by
      exact (hφ.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)
    exact hc.comp (((continuous_id.mul_const h).smul continuous_const).const_add x)
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => φ (x + (s * h) • unitVector l))
      (h * D t) t := by
    have ht := ((hasDerivAt_id t).mul_const h).smul_const (unitVector l) |>.const_add x
    have hf := ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t ht
    simpa only [D, coordinateDerivative, map_smul, smul_eq_mul, mul_comm,
      mul_one, Function.comp_def, id_eq] using hf
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hline t)
      ((hD.const_mul h).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hft
  simp only [one_mul, zero_mul, zero_smul, add_zero] at hft
  apply (div_eq_iff hh).2
  simpa only [D, mul_comm] using hft.symm


/-- A smooth coordinate quotient converges pointwise for signed steps. -/
private theorem c18_smooth_coordinate_quotient_tendsto {d : ℕ}
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (l : Fin d) (x : Vec d) :
    Filter.Tendsto (fun h : ℝ => (φ (x + h • unitVector l) - φ x) / h)
      (𝓝[≠] (0 : ℝ)) (𝓝 (coordinateDerivative l φ x)) := by
  have hline : HasDerivAt (fun t : ℝ => x + t • unitVector l) (unitVector l) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (unitVector l)).const_add x
  have hφ' : HasFDerivAt φ (fderiv ℝ φ x) ((fun t : ℝ => x + t • unitVector l) 0) := by
    simpa using ((hφ.differentiable (by simp)) x).hasFDerivAt
  have h := (hφ'.comp_hasDerivAt 0 hline).tendsto_slope_zero
  simpa [Function.comp_def, coordinateDerivative, div_eq_mul_inv, mul_comm] using h


/-- Smooth compact support gives one bound for all signed coordinate
quotients and the corresponding coordinate derivative. -/
private theorem c18_smooth_coordinate_quotient_uniform_bound {d : ℕ}
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (l : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (h : ℝ),
      ‖(φ (x + h • unitVector l) - φ x) / h‖ ≤ C ∧
      ‖coordinateDerivative l φ x‖ ≤ C := by
  have hd : Continuous (coordinateDerivative l φ) := by
    exact (hφ.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC, hbound⟩ :=
    ((hφc.fderiv_apply ℝ (unitVector l)).isCompact_range hd).isBounded.exists_pos_norm_le
  refine ⟨C, hC.le, ?_⟩
  intro x h
  have hD (y : Vec d) : ‖coordinateDerivative l φ y‖ ≤ C :=
    hbound _ ⟨y, rfl⟩
  refine ⟨?_, hD x⟩
  by_cases hh : h = 0
  · simp [hh, hC.le]
  · rw [c18_smooth_coordinate_quotient_eq_integral φ hφ l x h hh]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C)
      (f := fun t => coordinateDerivative l φ (x + (t * h) • unitVector l))
      (fun t _ => hD _)
    simpa using hb


/-- For small signed steps, both the quotient and derivative vanish outside
one fixed ball. -/
private theorem c18_smooth_coordinate_quotient_fixed_support {d : ℕ}
    (φ : Vec d → ℝ) (hφc : HasCompactSupport φ) (l : Fin d) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : Vec d) (h : ℝ),
      |h| ≤ 1 → R < ‖x‖ →
      (φ (x + h • unitVector l) - φ x) / h = 0 ∧
      coordinateDerivative l φ x = 0 := by
  obtain ⟨R, hR, hsupport⟩ := hφc.isBounded.exists_pos_norm_le
  refine ⟨R + 1, by positivity, ?_⟩
  intro x h hh hx
  have hu : ‖unitVector l‖ ≤ 1 := by
    simp only [unitVector, Pi.norm_single, norm_one, le_refl]
  have hs : ‖h • unitVector l‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |h| * ‖unitVector l‖ ≤ |h| * 1 := mul_le_mul_of_nonneg_left hu (abs_nonneg h)
      _ ≤ 1 := by simpa using hh
  have hxout : x ∉ tsupport φ := by
    intro hm
    have := hsupport x hm
    linarith
  have hyout : x + h • unitVector l ∉ tsupport φ := by
    intro hm
    have hy := hsupport _ hm
    have ht : ‖x‖ ≤ ‖x + h • unitVector l‖ + ‖h • unitVector l‖ := by
      calc
        ‖x‖ = ‖(x + h • unitVector l) - h • unitVector l‖ := by simp
        _ ≤ ‖x + h • unitVector l‖ + ‖h • unitVector l‖ := norm_sub_le _ _
    linarith
  constructor
  · simp [image_eq_zero_of_notMem_tsupport hxout,
      image_eq_zero_of_notMem_tsupport hyout]
  · simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxout]


/-- Smooth compactly supported real tests have the strong complex L2
coordinate quotient limit for their physical graph. -/
private theorem c18_smooth_physical_coordinate_quotient_tendsto {d : ℕ}
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (l : Fin d)
    (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : (v : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ)))
    (hH : (H l : Vec d → ℂ) =ᵐ[volume]
      (fun x => (coordinateDerivative l φ x : ℂ))) :
    Filter.Tendsto (fun h : ℝ => (h : ℂ)⁻¹ •
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) v - v))
      (𝓝[≠] (0 : ℝ)) (𝓝 (H l)) := by
  obtain ⟨C, hC, hbound⟩ := c18_smooth_coordinate_quotient_uniform_bound φ hφ hφc l
  obtain ⟨R, hR, hsupp⟩ := c18_smooth_coordinate_quotient_fixed_support φ hφc l
  let K : Set (Vec d) := Metric.closedBall 0 R
  let b : Vec d → ℝ := K.indicator (fun _ => 2 * C)
  have hb : Integrable (fun x => b x ^ 2) (volume : Measure (Vec d)) := by
    have hi : Integrable (K.indicator (fun _ : Vec d => (2 * C) ^ 2))
        (volume : Measure (Vec d)) :=
      (integrableOn_const (isCompact_closedBall (0 : Vec d) R).measure_ne_top).integrable_indicator
        measurableSet_closedBall
    convert hi using 1
    funext x
    by_cases hx : x ∈ K <;> simp [b, hx]
  apply tendsto_complexLp_of_dominated
    (F := fun h x => (((φ (x + h • unitVector l) - φ x) / h : ℝ) : ℂ))
    (hf := hH) (b := b) ?_ hb ?_ ?_
  · intro h
    let hp := measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)
    let w := Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l) hp v
    filter_upwards [Lp.coeFn_smul ((h : ℂ)⁻¹) (w - v), Lp.coeFn_sub w v,
      Lp.coeFn_compMeasurePreserving v hp, hv, hp.quasiMeasurePreserving.ae hv]
      with x hs hd hw hvx hvy
    change w x = v (x + h • unitVector l) at hw
    change ((h : ℂ)⁻¹ • (w - v) : Lp ℂ 2 volume) x =
      (((φ (x + h • unitVector l) - φ x) / h : ℝ) : ℂ)
    simp only [hs, Pi.smul_apply, hd, Pi.sub_apply, hw, hvx, hvy, smul_eq_mul,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_mul,
      div_eq_mul_inv, mul_comm]
  · have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), |h| ≤ 1 := by
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with h hh
      have : |h| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hh
      exact this.le
    filter_upwards [hsmall] with h hh
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · have hq := (hbound x h).1
      have hd := (hbound x h).2
      have hsum := norm_sub_le ((φ (x + h • unitVector l) - φ x) / h)
        (coordinateDerivative l φ x)
      simp only [← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real]
      have : ‖(φ (x + h • unitVector l) - φ x) / h - coordinateDerivative l φ x‖ ≤ 2 * C := by linarith
      simpa [b, hx] using this
    · have hxR : R < ‖x‖ := by simpa [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      obtain ⟨hq, hd⟩ := hsupp x h hh hxR
      simp [b, hx, ← Complex.ofReal_div, hq, hd]
  · filter_upwards [] with x
    exact (Complex.continuous_ofReal.tendsto _).comp
      (c18_smooth_coordinate_quotient_tendsto φ hφ l x)


/-- Quotient convergence is stable under the complex linear combinations used
 to combine the real and imaginary smooth approximations. -/
private theorem c18_physical_quotient_limit_sub_smul {d : ℕ}
    (v w : Lp ℂ 2 (volume : Measure (Vec d)))
    (H J : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (l : Fin d) (c : ℂ)
    (hv : Filter.Tendsto (fun h : ℝ => (h : ℂ)⁻¹ •
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) v - v))
      (𝓝[≠] (0 : ℝ)) (𝓝 (H l)))
    (hw : Filter.Tendsto (fun h : ℝ => (h : ℂ)⁻¹ •
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) w - w))
      (𝓝[≠] (0 : ℝ)) (𝓝 (J l))) :
    Filter.Tendsto (fun h : ℝ => (h : ℂ)⁻¹ •
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l))
        (v - c • w) - (v - c • w)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (H l - c • J l)) := by
  have ht := hv.sub (hw.const_smul c)
  convert ht using 1
  funext h
  have hs : Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
      (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l))
      (c • w) = c • Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
      (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) w := by
    exact (Lp.compMeasurePreservingₗ ℂ _ _).map_smul c w
  simp only [map_sub, hs, smul_sub, smul_smul]
  module


/-- Whole-space weak Sobolev data admit smooth compactly supported
approximations of both the value and the supplied derivatives. -/
private theorem c18_real_weak_supported_smooth_approximation {d : ℕ}
    (f : Vec d → ℝ) (G : Fin d → Vec d → ℝ)
    (hf : MemLp f 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hw : ∀ j, HasWeakPartialDerivative Set.univ j f (G j)) :
    ∃ a : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (a n)) ∧
      (∀ n, HasCompactSupport (a n)) ∧
      Filter.Tendsto (fun n => eLpNorm (a n - f) 2 volume) Filter.atTop (𝓝 0) ∧
      ∀ j, Filter.Tendsto (fun n => eLpNorm
        (fun x => fderiv ℝ (a n) x (unitVector j) - G j x) 2 volume)
        Filter.atTop (𝓝 0) := by
  let u : PDE.W1pFunction (Set.univ : Set (Vec d)) 2 :=
    { toFun := f
      grad := fun x j => G j x
      memLp := by simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hf
      gradMemLp := by
        intro j
        simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hG j
      hasWeakGradient := by
        intro j φ hφ hc hs
        simpa only [PDE.basisVec, unitVector, coordinateDerivative] using
          (hw j).2.2 φ ⟨hφ, hc, hs⟩ }
  obtain ⟨a⟩ := u.hasSupportedSmoothApproximation_univ (by norm_num) (by norm_num)
  refine ⟨a.approx, a.approx_smooth, a.approx_hasCompactSupport, ?_, ?_⟩
  · simpa only [PDE.volumeOn, Measure.restrict_univ] using a.tendsto_value
  · intro j
    simpa only [PDE.volumeOn, Measure.restrict_univ, PDE.basisVec, unitVector] using
      a.tendsto_grad j

/-- Both components of the supplied physical graph have smooth approximations
whose coordinate gradients converge to the corresponding supplied gradients. -/
private theorem c18_physical_components_smooth_approximation {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) :
    ∃ a b : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (a n) ∧ HasCompactSupport (a n)) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (b n) ∧ HasCompactSupport (b n)) ∧
      (∀ j, Filter.Tendsto (fun n => eLpNorm
        (fun x => fderiv ℝ (a n) x (unitVector j) - (G j x).re) 2 volume)
        Filter.atTop (𝓝 0)) ∧
      (∀ j, Filter.Tendsto (fun n => eLpNorm
        (fun x => fderiv ℝ (b n) x (unitVector j) - (G j x).im) 2 volume)
        Filter.atTop (𝓝 0)) := by
  have hfre : MemLp (fun x => (f x).re) 2 volume := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp f)
  have hfim : MemLp (fun x => (f x).im) 2 volume := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.comp_memLp' (Lp.memLp f)
  have hGre : ∀ j, MemLp (fun x => (G j x).re) 2 volume := by
    intro j
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp (G j))
  have hGim : ∀ j, MemLp (fun x => (G j x).im) 2 volume := by
    intro j
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.comp_memLp' (Lp.memLp (G j))
  obtain ⟨a, ha, hac, _, hag⟩ :=
    c18_real_weak_supported_smooth_approximation _ _ hfre hGre hG.1
  obtain ⟨b, hb, hbc, _, hbg⟩ :=
    c18_real_weak_supported_smooth_approximation _ _ hfim hGim hG.2
  exact ⟨a, b, fun n => ⟨ha n, hac n⟩, fun n => ⟨hb n, hbc n⟩, hag, hbg⟩

/-- The actual coordinate difference quotients converge to the supplied
physical weak derivative in complex L2. -/
theorem c18_physical_H1_coordinate_difference_quotient_tendsto {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) (l : Fin d) :
    Filter.Tendsto (fun h : ℝ => (h : ℂ)⁻¹ •
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) f - f))
      (𝓝[≠] (0 : ℝ)) (𝓝 (G l)) := by
  apply c18_physical_H1_quotient_limit_of_approximation hG l
  intro ε hε
  obtain ⟨a, b, ha, hb, hag, hbg⟩ := c18_physical_components_smooth_approximation hG
  have hta := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hag l)
  have htb := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hbg l)
  have hea := Metric.tendsto_nhds.1 hta (ε / 2) (by positivity)
  have heb := Metric.tendsto_nhds.1 htb (ε / 2) (by positivity)
  obtain ⟨n, hn⟩ := (hea.and heb).exists
  have hna : (eLpNorm (fun x => fderiv ℝ (a n) x (unitVector l) - (G l x).re)
      2 volume).toReal < ε / 2 := by
    simpa only [Function.comp_apply, ENNReal.toReal_zero, Real.dist_eq, sub_zero,
      abs_of_nonneg ENNReal.toReal_nonneg] using hn.1
  have hnb : (eLpNorm (fun x => fderiv ℝ (b n) x (unitVector l) - (G l x).im)
      2 volume).toReal < ε / 2 := by
    simpa only [Function.comp_apply, ENNReal.toReal_zero, Real.dist_eq, sub_zero,
      abs_of_nonneg ENNReal.toReal_nonneg] using hn.2
  obtain ⟨v, A, hvgraph, hv, hA⟩ := c18_physical_smooth_test (a n) (ha n).1 (ha n).2
  obtain ⟨w, B, hwgraph, hw, hB⟩ := c18_physical_smooth_test (b n) (hb n).1 (hb n).2
  let H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) := fun j => A j - (-Complex.I) • B j
  refine ⟨v - (-Complex.I) • w, H,
    c18_physicalH1_sub hvgraph (c18_physicalH1_smul (-Complex.I) hwgraph), ?_, ?_⟩
  · have hr : (fun x => ((H l - G l) x).re) =ᵐ[volume]
        (fun x => fderiv ℝ (a n) x (unitVector l) - (G l x).re) := by
      filter_upwards [Lp.coeFn_sub (H l) (G l), Lp.coeFn_sub (A l) ((-Complex.I) • B l),
        Lp.coeFn_smul (-Complex.I) (B l), hA l, hB l] with x hsub hsub' hsm hax hbx
      simp only [H, hsub, Pi.sub_apply, hsub', hsm, Pi.smul_apply, hax, hbx,
        smul_eq_mul, coordinateDerivative, Complex.sub_re, Complex.mul_re,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im] 
      ring
    have hi : (fun x => ((H l - G l) x).im) =ᵐ[volume]
        (fun x => fderiv ℝ (b n) x (unitVector l) - (G l x).im) := by
      filter_upwards [Lp.coeFn_sub (H l) (G l), Lp.coeFn_sub (A l) ((-Complex.I) • B l),
        Lp.coeFn_smul (-Complex.I) (B l), hA l, hB l] with x hsub hsub' hsm hax hbx
      simp only [H, hsub, Pi.sub_apply, hsub', hsm, Pi.smul_apply, hax, hbx,
        smul_eq_mul, coordinateDerivative, Complex.sub_im, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hsq := c18_complex_L2_square_components (H l - G l) (Lp.memLp (H l - G l))
    rw [eLpNorm_congr_ae hr, eLpNorm_congr_ae hi] at hsq
    have hnorm : 0 ≤ ‖H l - G l‖ := norm_nonneg _
    have hna0 := ENNReal.toReal_nonneg (a := eLpNorm
      (fun x => fderiv ℝ (a n) x (unitVector l) - (G l x).re) 2 volume)
    have hnb0 := ENNReal.toReal_nonneg (a := eLpNorm
      (fun x => fderiv ℝ (b n) x (unitVector l) - (G l x).im) 2 volume)
    rw [← Lp.norm_def] at hsq
    rw [norm_sub_rev]
    nlinarith [sq_nonneg (ε / 2 - (eLpNorm
      (fun x => fderiv ℝ (a n) x (unitVector l) - (G l x).re) 2 volume).toReal),
      sq_nonneg (ε / 2 - (eLpNorm
      (fun x => fderiv ℝ (b n) x (unitVector l) - (G l x).im) 2 volume).toReal)]
  · exact c18_physical_quotient_limit_sub_smul v w A B l (-Complex.I)
      (c18_smooth_physical_coordinate_quotient_tendsto (a n) (ha n).1 (ha n).2 l v A hv (hA l))
      (c18_smooth_physical_coordinate_quotient_tendsto (b n) (hb n).1 (hb n).2 l w B hw (hB l))

/-- Translation in a coordinate direction differentiates to the supplied weak derivative. -/
theorem c18_physical_H1_translation_hasDerivAt {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) (l : Fin d) :
    HasDerivAt (fun h : ℝ =>
      Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector l)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l)) f)
      (G l) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hz : Lp.compMeasurePreserving (fun x : Vec d => x + (0 : ℝ) • unitVector l)
      (measurePreserving_add_right (volume : Measure (Vec d)) ((0 : ℝ) • unitVector l)) f = f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving f
      (measurePreserving_add_right (volume : Measure (Vec d)) ((0 : ℝ) • unitVector l))] with x hx
    simpa using hx
  convert c18_physical_H1_coordinate_difference_quotient_tendsto hG l using 1
  funext h
  simp only [slope_def_module, sub_zero, hz, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  rfl

end EinsteinFull
