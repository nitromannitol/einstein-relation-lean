import EinsteinFull.Calculus.RadialPrimitiveSupport
import EinsteinFull.Calculus.ComplexRadialGeneratorSupport
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport

/-!
# Truncated nonlinear energy along the actual stationary evolution

The primitive energy is differentiable on the full complex L2 space. On the
full generator domain, its right derivative is controlled by the anisotropic
nonlinear generator estimate. Gronwall gives a rate independent of both radial
cutoffs. Removing those cutoffs and extending to arbitrary Lp data are separate
steps. Continuity of the primitive integral also extends this truncated bound
from generator-domain data to every L2 datum.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private theorem realL2_inner_eq_re {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : Lp ℂ 2 μ) : inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

/-- Every full generator pair satisfies the primitive energy rate estimate, with
a coefficient depending on the exponent and structural parameters only. -/
theorem IsComplexGeneratorPair.radialTruncation_energy_rate
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hL := lipschitzWith_radialTruncation hε hR ha
    let hz : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    inner ℝ (hL.compLp hz f) g ≤
      ((2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
        (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2)) *
          (∫ ω, radialTruncationPrimitive ε R a (f ω) ∂reducedLaw Q) := by
  dsimp only
  let K := Real.exp (2 * Λ₀) * Λ₀
  let C := (d : ℝ) * K * (‖ζ‖ * K) ^ 2
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨G, v, H, _, _, hv, _, hb⟩ := hfg.forced_radialTruncation_coercive hε hR ha
  have hvEq : v = (lipschitzWith_radialTruncation hε hR ha).compLp
      (by simp only [smul_zero]) f :=
    Lp.ext (hv.trans ((lipschitzWith_radialTruncation hε hR ha).coeFn_compLp
      (by simp only [smul_zero]) f).symm)
  have he : 0 ≤ (K⁻¹ / 4) *
      (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) *
        (∑ j, ‖G j ω‖ ^ 2) ∂reducedLaw Q) := by
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro ω
    apply mul_nonneg
      (Real.rpow_nonneg (radialTruncationBase_pos_le hε hR (sq_nonneg ‖f ω‖)).1.le _)
    exact Finset.sum_nonneg fun j _ => sq_nonneg ‖G j ω‖
  have hm : (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) * ‖f ω‖ ^ 2
      ∂reducedLaw Q) ≤ (2 * (1 + a)) *
      (∫ ω, radialTruncationPrimitive ε R a (f ω) ∂reducedLaw Q) := by
    rw [← integral_const_mul]
    apply integral_mono (integrable_radialTruncation_mass (reducedLaw Q) f hε hR ha)
      ((integrable_radialTruncationPrimitive (reducedLaw Q) f hε hR ha).const_mul _)
    exact fun ω => radialTruncation_mass_le_primitive hε hR ha (f ω)
  rw [← hvEq, realL2_inner_eq_re]
  have hi : (inner ℂ v g).re ≤ C *
      (∫ ω, radialTruncationWeight ε R a (‖f ω‖ ^ 2) * ‖f ω‖ ^ 2 ∂reducedLaw Q) := by
    linarith only [hb, he]
  calc
    _ ≤ _ := hi.trans (mul_le_mul_of_nonneg_left hm hC)
    _ = _ := by dsimp only [C, K]; ring

/-- The actual full-domain semigroup orbit has the literal nonlinear energy right derivative. -/
theorem IsComplexEnvironmentSemigroup.hasDerivWithinAt_radialTruncation_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a)
    (s : ℝ) (hs : 0 ≤ s) :
    let hL := lipschitzWith_radialTruncation hε hR ha
    let hz : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    HasDerivWithinAt
      (fun r => ∫ ω, radialTruncationPrimitive ε R a (P r.toNNReal f ω) ∂reducedLaw Q)
      (inner ℝ (hL.compLp hz (P s.toNNReal f)) (P s.toNNReal g)) (Ici s) s :=
  HasDerivWithinAt.integral_radialTruncationPrimitive
    (hP.hasDerivWithinAt_orbit hfg s hs) hε hR ha

/-- The forward truncated energy grows with leading constant one and a
quadratic force rate uniform in both truncation parameters. -/
theorem IsComplexEnvironmentSemigroup.radialTruncation_energy_growth
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (t : ℝ≥0) :
    (∫ ω, radialTruncationPrimitive ε R a (P t f ω) ∂reducedLaw Q) ≤
      (∫ ω, radialTruncationPrimitive ε R a (f ω) ∂reducedLaw Q) *
        Real.exp (((2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2)) * (t : ℝ)) := by
  let hL := lipschitzWith_radialTruncation hε hR ha
  let hz : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
    by simp only [smul_zero]
  let E (s : ℝ) := ∫ ω, radialTruncationPrimitive ε R a (P s.toNNReal f ω) ∂reducedLaw Q
  let D (s : ℝ) := inner ℝ (hL.compLp hz (P s.toNNReal f)) (P s.toNNReal g)
  let C := (2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
    (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2)
  have hF : Continuous (fun u : Lp ℂ 2 (reducedLaw Q) =>
      ∫ ω, radialTruncationPrimitive ε R a (u ω) ∂reducedLaw Q) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasFDerivAt_integral_radialTruncationPrimitive (reducedLaw Q) u hε hR ha).continuousAt
  have hE : Continuous E := hF.comp ((hP.2.2.1 f).comp continuous_real_toNNReal)
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt E (D s) (Ici s) s :=
    hP.hasDerivWithinAt_radialTruncation_energy hfg hε hR ha s hs
  have hr (s : ℝ) : D s ≤ C * E s :=
    (hP.map_generator hfg s.toNNReal).radialTruncation_energy_rate hε hR ha
  have hb := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := D) (δ := E 0) (K := C) (ε := 0) (a := 0) (b := (t : ℝ))
    hE.continuousOn (fun s hs _ hr => (hd s hs.1).liminf_right_slope_le hr)
    le_rfl (fun s _ => by simpa only [add_zero] using hr s)
    (t : ℝ) ⟨t.property, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hb
  simpa only [E, C, Real.toNNReal_zero, Real.toNNReal_coe, hP.1,
    ContinuousLinearMap.id_apply] using hb

/-- Resolvent approximation removes the generator-domain condition while the
cutoff parameters remain fixed. No higher-moment premise is required. -/
theorem IsComplexEnvironmentSemigroup.radialTruncation_energy_growth_all
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (t : ℝ≥0) :
    (∫ ω, radialTruncationPrimitive ε R a (P t f ω) ∂reducedLaw Q) ≤
      (∫ ω, radialTruncationPrimitive ε R a (f ω) ∂reducedLaw Q) *
        Real.exp (((2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2)) * (t : ℝ)) := by
  have hF : Continuous (fun u : Lp ℂ 2 (reducedLaw Q) =>
      ∫ ω, radialTruncationPrimitive ε R a (u ω) ∂reducedLaw Q) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasFDerivAt_integral_radialTruncationPrimitive (reducedLaw Q) u hε hR ha).continuousAt
  have hu := tendsto_forcedComplexResolventApproximation Q i ζ f
  exact le_of_tendsto_of_tendsto
    (hF.continuousAt.tendsto.comp ((P t).continuous.tendsto f |>.comp hu))
    ((hF.continuousAt.tendsto.comp hu).mul_const _)
    (Eventually.of_forall fun n => hP.radialTruncation_energy_growth
      (forcedComplexYosida_graph Q i ζ n f) hε hR ha t)

end EinsteinFull
