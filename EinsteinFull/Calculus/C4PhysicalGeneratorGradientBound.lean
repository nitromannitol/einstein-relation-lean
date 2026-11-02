import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Calculus.S5CoefficientSupport
import EinsteinFull.Calculus.S5EnergySupport
import EinsteinFull.Calculus.PhysicalDomainSupport
import EinsteinFull.Work.W6.PhysicalLocalEnergySupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- The actual complex physical generator graph controls its Euclidean H1 gradient
by the L2 graph norm, with an explicit quadratic force term. -/
theorem physical_complex_generator_gradient_bound
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) u G ∧
      (∑ j, ‖G j‖ ^ 2) ≤ 4*Λ*‖u‖*‖g‖ +
        4*((d : ℝ)+1)^2*Λ^4*‖ζ‖^2*‖u‖^2 := by
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
  have hRe := (Complex.re_le_norm (-(inner ℂ u g))).trans (by
    simpa only [norm_neg] using norm_inner_le_norm (𝕜 := ℂ) u g)
  have hrealint := integral_re hT
  simp only [RCLike.re_eq_complex_re] at hrealint
  simp only [Pi.add_apply, Pi.neg_apply, RCLike.re_eq_complex_re] at hi
  rw [integral_const_mul, hNeq, integral_add (f := fun x => -((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re)
      (g := fun x => ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u x‖ ^ 2)
      hT.re.neg (hU.const_mul _),
    integral_neg, hrealint, hTeq, hpair, integral_const_mul,
    ← physicalL2_norm_sq] at hi
  have hbound : (∑ j, ‖G j‖ ^ 2) ≤
      4 * Λ * ‖u‖ * ‖g‖ + 4 * (d : ℝ) * Λ ^ 4 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * Λ by positivity)
    have he : 4 * Λ * (1 / (4 * Λ)) = 1 := by field_simp
    simp only [← mul_assoc, he, one_mul] at hm
    have hr : -(inner ℂ u g).re ≤ ‖u‖ * ‖g‖ := hRe
    nlinarith only [hm, mul_le_mul_of_nonneg_left hr (show 0 ≤ 4 * Λ by positivity)]
  apply hbound.trans
  have hd : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  gcongr
end EinsteinFull.Blueprint
