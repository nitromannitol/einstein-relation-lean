import EinsteinFull.Calculus.RadialPrimitiveSupport
import EinsteinFull.Calculus.ComplexTransposeResolventSupport
import Mathlib.Analysis.ODE.Gronwall

/-!
# Truncated nonlinear energy for the actual bilinear transpose evolution

The primitive energy is differentiable on the full complex L2 space. On the
full generator domain, its right derivative is controlled by the anisotropic
nonlinear generator estimate. Gronwall gives a rate independent of both radial
cutoffs. Removing those cutoffs and extending to arbitrary Lp data are separate
steps. Injectivity of the forward resolvent proves density of the complete transpose
domain; continuity extends this truncated bound to every L2 datum.
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

/-- The actual transpose resolvent has dense range, because the actual forward
resolvent is injective. Conjugation transports the Hilbert-adjoint range. -/
theorem denseRange_complexTranspose_forcedComplexResolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) :
    DenseRange (complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs)) := by
  let A := forcedComplexResolvent Q i ζ s hs
  let J := complexL2Conjugation (reducedLaw Q)
  have hk : LinearMap.ker A.toLinearMap = ⊥ :=
    (LinearMap.ker_eq_bot (f := A.toLinearMap)).mpr (forcedComplexResolvent_injective Q i ζ s hs)
  have hr : (LinearMap.range (ContinuousLinearMap.adjoint A).toLinearMap).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff,
      ContinuousLinearMap.orthogonal_range, ContinuousLinearMap.adjoint_adjoint, hk]
  have hA : DenseRange (ContinuousLinearMap.adjoint A) := by
    change Dense (LinearMap.range (ContinuousLinearMap.adjoint A).toLinearMap : Set (Lp ℂ 2 (reducedLaw Q)))
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hr]
    rfl
  have hJ : Function.Surjective J := fun u =>
    ⟨J u, complexL2Conjugation_involutive (reducedLaw Q) u⟩
  exact hJ.denseRange.comp (hA.comp hJ.denseRange (ContinuousLinearMap.adjoint A).continuous)
    J.continuous

/-- Density of the complete horizontal H1 transpose weak-generator domain. -/
theorem dense_complexTransposeGenerator_domain {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    Dense {f : Lp ℂ 2 (reducedLaw Q) | ∃ g, IsComplexTransposeGeneratorPair Q i ζ f g} := by
  let s := complexForceShift d Λ₀ ζ + 1
  have hs : complexForceShift d Λ₀ ζ < s := by dsimp only [s]; linarith
  apply (denseRange_complexTranspose_forcedComplexResolvent Q i ζ s hs).mono
  rintro f ⟨u, rfl⟩
  exact ⟨_, complexL2Transpose_forcedComplexResolvent_spec Q i ζ s hs u⟩

/-- Vector FTC gives the right derivative of each actual full-domain transpose
orbit at every nonnegative time, including zero. -/
theorem IsComplexTransposeSemigroup.hasDerivWithinAt_orbit
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (s : ℝ) (hs : 0 ≤ s) :
    HasDerivWithinAt (fun r : ℝ => T r.toNNReal f)
      (T s.toNNReal g) (Ici s) s := by
  have hc : Continuous (fun r : ℝ => T r.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hh := (hd.add_const f).hasDerivWithinAt (s := Ici s)
  apply hh.congr
  · intro r hr
    have hr0 : 0 ≤ r := hs.trans hr
    have he := hT.integral_orbit_eq_sub hP hfg r.toNNReal
    rw [Real.coe_toNNReal r hr0] at he
    exact (eq_sub_iff_add_eq.mp he).symm
  · have he := hT.integral_orbit_eq_sub hP hfg s.toNNReal
    rw [Real.coe_toNNReal s hs] at he
    exact (eq_sub_iff_add_eq.mp he).symm

/-- Every full generator pair satisfies the primitive energy rate estimate, with
a coefficient depending on the exponent and structural parameters only. -/
theorem IsComplexTransposeGeneratorPair.radialTruncation_energy_rate
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hL := lipschitzWith_radialTruncation hε hR ha
    let hz : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    inner ℝ (hL.compLp hz f) g ≤
      ((2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
        (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2)) *
          (∫ ω, radialTruncationPrimitive ε R a (f ω) ∂reducedLaw Q) := by
  dsimp only
  let K := Real.exp (2 * Λ₀) * Λ₀
  let C := (d : ℝ) * K * (‖ζ‖ * K * (1 + 2 * a)) ^ 2
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨G, v, H, _, _, hv, _, hb⟩ := hfg.radialTruncation_coercive hε hR ha
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
theorem IsComplexTransposeSemigroup.hasDerivWithinAt_radialTruncation_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a)
    (s : ℝ) (hs : 0 ≤ s) :
    let hL := lipschitzWith_radialTruncation hε hR ha
    let hz : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    HasDerivWithinAt
      (fun r => ∫ ω, radialTruncationPrimitive ε R a (T r.toNNReal f ω) ∂reducedLaw Q)
      (inner ℝ (hL.compLp hz (T s.toNNReal f)) (T s.toNNReal g)) (Ici s) s :=
  HasDerivWithinAt.integral_radialTruncationPrimitive
    (hT.hasDerivWithinAt_orbit hP hfg s hs) hε hR ha

/-- The transpose truncated energy grows with leading constant one and a
quadratic force rate uniform in both truncation parameters. -/
theorem IsComplexTransposeSemigroup.radialTruncation_energy_growth
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (t : ℝ≥0) :
    (∫ ω, radialTruncationPrimitive ε R a (T t f ω) ∂reducedLaw Q) ≤
      (∫ ω, radialTruncationPrimitive ε R a (f ω) ∂reducedLaw Q) *
        Real.exp (((2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2)) * (t : ℝ)) := by
  let hL := lipschitzWith_radialTruncation hε hR ha
  let hz : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
    by simp only [smul_zero]
  let E (s : ℝ) := ∫ ω, radialTruncationPrimitive ε R a (T s.toNNReal f ω) ∂reducedLaw Q
  let D (s : ℝ) := inner ℝ (hL.compLp hz (T s.toNNReal f)) (T s.toNNReal g)
  let C := (2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
    (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2)
  have hF : Continuous (fun u : Lp ℂ 2 (reducedLaw Q) =>
      ∫ ω, radialTruncationPrimitive ε R a (u ω) ∂reducedLaw Q) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasFDerivAt_integral_radialTruncationPrimitive (reducedLaw Q) u hε hR ha).continuousAt
  have hE : Continuous E := hF.comp ((hT.continuous_apply hP f).comp continuous_real_toNNReal)
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt E (D s) (Ici s) s :=
    hT.hasDerivWithinAt_radialTruncation_energy hP hfg hε hR ha s hs
  have hr (s : ℝ) : D s ≤ C * E s :=
    (hT.map_generator hP hfg s.toNNReal).radialTruncation_energy_rate hε hR ha
  have hb := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := D) (δ := E 0) (K := C) (ε := 0) (a := 0) (b := (t : ℝ))
    hE.continuousOn (fun s hs _ hr => (hd s hs.1).liminf_right_slope_le hr)
    le_rfl (fun s _ => by simpa only [add_zero] using hr s)
    (t : ℝ) ⟨t.property, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hb
  have hzero : T 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (reducedLaw Q)) := by
    have he := congrFun hT.eq_complexL2Transpose 0
    simpa only [hP.1, complexL2Transpose_id] using he
  simpa only [E, C, Real.toNNReal_zero, Real.toNNReal_coe, hzero,
    ContinuousLinearMap.id_apply] using hb

/-- Dense transpose resolvent range removes the generator-domain condition while the
cutoff parameters remain fixed. No higher-moment premise is required. -/
theorem IsComplexTransposeSemigroup.radialTruncation_energy_growth_all
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    {ε R a : ℝ} (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (t : ℝ≥0) :
    (∫ ω, radialTruncationPrimitive ε R a (T t f ω) ∂reducedLaw Q) ≤
      (∫ ω, radialTruncationPrimitive ε R a (f ω) ∂reducedLaw Q) *
        Real.exp (((2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2)) * (t : ℝ)) := by
  have hF : Continuous (fun u : Lp ℂ 2 (reducedLaw Q) =>
      ∫ ω, radialTruncationPrimitive ε R a (u ω) ∂reducedLaw Q) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasFDerivAt_integral_radialTruncationPrimitive (reducedLaw Q) u hε hR ha).continuousAt
  have hclosed : IsClosed {u : Lp ℂ 2 (reducedLaw Q) |
      (∫ ω, radialTruncationPrimitive ε R a (T t u ω) ∂reducedLaw Q) ≤
        (∫ ω, radialTruncationPrimitive ε R a (u ω) ∂reducedLaw Q) *
          Real.exp (((2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
            (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2)) * (t : ℝ))} :=
    isClosed_le (hF.comp (T t).continuous) (hF.mul continuous_const)
  exact (dense_complexTransposeGenerator_domain Q i ζ).induction
    (by rintro u ⟨v, huv⟩; exact hT.radialTruncation_energy_growth hP huv hε hR ha t)
    hclosed f

end EinsteinFull
