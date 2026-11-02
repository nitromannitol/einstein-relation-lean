import EinsteinFull.Calculus.ComplexForceSemigroupSupport
import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniqueness for the complete stationary complex semigroup predicate

The semigroup law transports the full generator graph and gives right
derivatives of domain orbits. Shifted dissipativity and the scalar right
derivative Gronwall inequality give uniqueness, first on that dense domain.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Any family with the full frozen generator preserves that generator graph. -/
theorem IsComplexEnvironmentSemigroup.map_generator {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ≥0) : IsComplexGeneratorPair Q i ζ (P t f) (P t g) := by
  apply (hP.2.2.2 _ _).mp
  have h := ((P t).continuous.tendsto g).comp ((hP.2.2.2 f g).mpr hfg)
  convert h using 1
  ext s
  simp only [Function.comp_apply, map_smul, map_sub]
  have hc : P t (P s f) = P s (P t f) := by
    rw [← ContinuousLinearMap.comp_apply, ← hP.2.1, add_comm, hP.2.1,
      ContinuousLinearMap.comp_apply]
  rw [hc]

/-- Full generator-domain orbits of any such family have the expected right derivative. -/
theorem IsComplexEnvironmentSemigroup.hasDerivWithinAt_orbit {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => P (Real.toNNReal s) f)
      (P (Real.toNNReal t) g) (Ici t) t := by
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mpr
  have he : Tendsto (fun s : ℝ => Real.toNNReal (s-t))
      (𝓝[>] t) (𝓝[>] (0 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Function.comp_def, id_eq, sub_self, Real.toNNReal_zero] using
        (continuous_real_toNNReal.comp (continuous_id.fun_sub (continuous_const (y := t)))).tendsto t
          |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact Real.toNNReal_pos.mpr (sub_pos.mpr hs)
  have h := (((P (Real.toNNReal t)).continuous.tendsto g).comp
    ((hP.2.2.2 f g).mpr hfg)).comp he
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  change t < s at hs
  have hs0 : 0 ≤ s := ht.trans hs.le
  have ha : Real.toNNReal t + Real.toNNReal (s-t) = Real.toNNReal s := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left ht,
      max_eq_left (sub_nonneg.mpr hs.le), max_eq_left hs0]
    ring
  simp only [Function.comp_apply]
  rw [map_smul, map_sub]
  simp only [slope_def_module,
    Real.coe_toNNReal', max_eq_left (sub_nonneg.mpr hs.le),
    RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
  rw [← ContinuousLinearMap.comp_apply, ← hP.2.1, ha]
  rfl

private theorem realL2_inner_eq_re {d : ℕ} (Q : Measure (FieldPair d)) (f g : Lp ℂ 2 Q) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

/-- Two complete frozen semigroups agree on every full generator-domain datum. -/
theorem IsComplexEnvironmentSemigroup.eq_apply_of_generator {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i ζ R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ≥0) : P t f = R t f := by
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal f - R s.toNNReal f
  let v : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal g - R s.toNNReal g
  have hu : Continuous u :=
    ((hP.2.2.1 f).comp continuous_real_toNNReal).sub
      ((hR.2.2.1 f).comp continuous_real_toNNReal)
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt u (v s) (Ici s) s :=
    (hP.hasDerivWithinAt_orbit hfg s hs).sub (hR.hasDerivWithinAt_orbit hfg s hs)
  have hg (s : ℝ) : IsComplexGeneratorPair Q i ζ (u s) (v s) := by
    simpa only [neg_one_smul, ← sub_eq_add_neg] using
      (hP.map_generator hfg s.toNNReal).add ((hR.map_generator hfg s.toNNReal).smul (-1))
  have he : u 0 = 0 := by
    simp only [u, Real.toNNReal_zero, hP.1, hR.1, ContinuousLinearMap.id_apply, sub_self]
  have hb := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun s => ‖u s‖^2) (f' := fun s => 2 * inner ℝ (u s) (v s))
    (δ := 0) (K := 2 * complexForceShift d Λ₀ ζ) (ε := 0)
    (a := 0) (b := (t : ℝ)) (hu.norm.pow 2).continuousOn
    (fun s hs _ hr => ((hd s hs.1).norm_sq).liminf_right_slope_le hr)
    (by change ‖u 0‖ ^ 2 ≤ 0; rw [he, norm_zero]; norm_num)
    (fun s _ => by
      rw [realL2_inner_eq_re, add_zero]
      have hb := (hg s).forced_re_inner_le
      nlinarith only [hb])
    (t : ℝ) ⟨t.property, le_rfl⟩
  rw [gronwallBound_ε0_δ0] at hb
  have hz : u (t : ℝ) = 0 := norm_eq_zero.mp (by nlinarith only [hb, norm_nonneg (u (t : ℝ))])
  simpa only [u, Real.toNNReal_coe, sub_eq_zero] using hz

/-- The complete frozen generator and strong continuity determine the entire family. -/
theorem IsComplexEnvironmentSemigroup.unique {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i ζ R) : P = R := by
  funext t
  apply ContinuousLinearMap.ext
  have he : (P t : _ → _) = (R t : _ → _) :=
    Continuous.ext_on (dense_complexGenerator_domain Q i ζ) (P t).continuous (R t).continuous
      (by rintro f ⟨g, hfg⟩; exact hP.eq_apply_of_generator hR hfg t)
  exact congr_fun he

/-- Every family satisfying the frozen predicate is the actual constructed forced evolution. -/
theorem IsComplexEnvironmentSemigroup.eq_forcedComplexEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) : P = forcedComplexEvolution Q i ζ :=
  hP.unique (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ)

/-- The proved structural growth bound holds for every family in the frozen predicate. -/
theorem IsComplexEnvironmentSemigroup.norm_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) :
    ‖P t‖ ≤ Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) := by
  rw [hP.eq_forcedComplexEvolution]
  exact norm_forcedComplexEvolution_le Q i ζ t

end EinsteinFull
