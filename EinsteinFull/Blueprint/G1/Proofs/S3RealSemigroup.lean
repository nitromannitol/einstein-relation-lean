import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Frozen.ComplexTransposeSemigroup

/-!
# Real force semigroups commute with complex conjugation

For a real force `lam`, every family satisfying the frozen predicate
`IsComplexEnvironmentSemigroup Q i (lam : ℂ)` commutes with the conjugation of
`L²(reducedLaw Q)`, hence preserves real-valued classes; the same holds for any
transpose family `IsComplexTransposeSemigroup Q P Pdag`. The proof conjugates the
family, checks the frozen predicate for `conj ζ = ζ`, and applies
`IsComplexEnvironmentSemigroup.unique`.
-/

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull

open EinsteinRelation

section Star

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lpStar_apply_ae (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, (star f : Lp ℂ 2 μ) x = starRingEnd ℂ (f x) :=
  (Lp.coeFn_star f).mono fun x hx => by simpa only [Pi.star_apply, Complex.star_def] using hx

theorem lpStar_add (f g : Lp ℂ 2 μ) : star (f + g) = star f + star g := by
  apply Lp.ext
  filter_upwards [lpStar_apply_ae (f + g), Lp.coeFn_add f g, Lp.coeFn_add (star f) (star g),
    lpStar_apply_ae f, lpStar_apply_ae g] with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.add_apply, map_add]

theorem lpStar_sub (f g : Lp ℂ 2 μ) : star (f - g) = star f - star g := by
  apply Lp.ext
  filter_upwards [lpStar_apply_ae (f - g), Lp.coeFn_sub f g, Lp.coeFn_sub (star f) (star g),
    lpStar_apply_ae f, lpStar_apply_ae g] with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.sub_apply, map_sub]

theorem lpStar_smul (c : ℂ) (f : Lp ℂ 2 μ) : star (c • f) = starRingEnd ℂ c • star f := by
  apply Lp.ext
  filter_upwards [lpStar_apply_ae (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul (starRingEnd ℂ c) (star f), lpStar_apply_ae f] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.smul_apply, smul_eq_mul, map_mul]

theorem lpStar_eq_compLpL (u : Lp ℂ 2 μ) :
    Complex.conjCLE.toContinuousLinearMap.compLpL 2 μ u = (star u : Lp ℂ 2 μ) := by
  apply Lp.ext
  filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL u,
    Lp.coeFn_star u] with ω ha hb
  change (Star.star u) ω = Star.star (u ω) at hb
  refine ha.trans (Eq.trans ?_ hb.symm)
  rfl

theorem lpStar_continuous : Continuous (star : Lp ℂ 2 μ → Lp ℂ 2 μ) := by
  have h : (star : Lp ℂ 2 μ → Lp ℂ 2 μ) =
      fun u => Complex.conjCLE.toContinuousLinearMap.compLpL 2 μ u :=
    funext fun u => (lpStar_eq_compLpL u).symm
  rw [h]
  exact (Complex.conjCLE.toContinuousLinearMap.compLpL 2 μ).continuous

theorem lpStar_tendsto_iff {ι : Type*} {l : Filter ι} {u : ι → Lp ℂ 2 μ} {g : Lp ℂ 2 μ} :
    Tendsto (fun x => star (u x)) l (𝓝 (star g)) ↔ Tendsto u l (𝓝 g) :=
  ⟨fun h => by
      have h' := ((lpStar_continuous (μ := μ)).tendsto (star g)).comp h
      simpa only [Function.comp_def, star_star] using h',
    fun h => ((lpStar_continuous (μ := μ)).tendsto g).comp h⟩

theorem lpStar_integral_mul (u w : Lp ℂ 2 μ) :
    ∫ x, (star u : Lp ℂ 2 μ) x * w x ∂μ =
      starRingEnd ℂ (∫ x, u x * (star w : Lp ℂ 2 μ) x ∂μ) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [lpStar_apply_ae u, lpStar_apply_ae w] with x h1 h2
  rw [h1, h2, map_mul, starRingEnd_self_apply]

theorem lpStar_integral_mul' (u w : Lp ℂ 2 μ) :
    ∫ x, u x * (star w : Lp ℂ 2 μ) x ∂μ =
      starRingEnd ℂ (∫ x, (star u : Lp ℂ 2 μ) x * w x ∂μ) := by
  rw [lpStar_integral_mul, starRingEnd_self_apply]

theorem lpStar_inner_eq_integral (f g : Lp ℂ 2 μ) :
    inner ℂ (star f) g = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with ω hω
  change (star f) ω = star (f ω) at hω
  simp only [hω, RCLike.inner_apply, Complex.star_def, starRingEnd_self_apply]
  ring

end Star

/-- Conjugation of a bounded `ℂ`-linear operator: `f ↦ conj (P (conj f))`. -/
noncomputable def conjConj {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ where
  toFun f := star (P (star f))
  map_add' f g := by rw [lpStar_add, map_add, lpStar_add]
  map_smul' c f := by
    simp only [RingHom.id_apply, lpStar_smul, map_smul, starRingEnd_self_apply]
  cont := (lpStar_continuous).comp (P.continuous.comp lpStar_continuous)

theorem conjConj_apply {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (f : Lp ℂ 2 μ) :
    conjConj P f = star (P (star f)) := rfl

/-- Conjugation maps generator pairs for `ζ` to generator pairs for `conj ζ`. -/
theorem isComplexGeneratorPair_star {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (h : IsComplexGeneratorPair Q i ζ f g) :
    IsComplexGeneratorPair Q i (starRingEnd ℂ ζ) (star f) (star g) := by
  obtain ⟨Gf, hGf, hg⟩ := h
  refine ⟨fun k => star (Gf k), fun k => (hGf k).star, ?_⟩
  intro v Gv hv
  have hv' : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (star v) (fun k => star (Gv k)) := fun k => (hv k).star
  have key := hg (star v) (fun k => star (Gv k)) hv'
  beta_reduce at key
  have e1 : ∫ ω, (star g : Lp ℂ 2 (reducedLaw Q)) ω * v ω ∂reducedLaw Q =
      starRingEnd ℂ (∫ ω, g ω * (star v : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) :=
    lpStar_integral_mul g v
  have e2 : ∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * (star (Gf k) : Lp ℂ 2 (reducedLaw Q)) ω *
        Gv j ω ∂reducedLaw Q =
      starRingEnd ℂ (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * Gf k ω *
        (star (Gv j) : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) := by
    rw [← integral_conj]
    apply integral_congr_ae
    have hk := ae_all_iff.mpr fun k => lpStar_apply_ae (μ := reducedLaw Q) (Gf k)
    have hj := ae_all_iff.mpr fun j => lpStar_apply_ae (μ := reducedLaw Q) (Gv j)
    filter_upwards [hk, hj] with ω hk hj
    simp only [map_sum, map_mul, Complex.conj_ofReal, hk, hj, starRingEnd_self_apply]
  have e3 : ∫ ω, (∑ j, (ω.1 0 j i : ℂ) * (star (Gf j) : Lp ℂ 2 (reducedLaw Q)) ω) * v ω
        ∂reducedLaw Q =
      starRingEnd ℂ (∫ ω, (∑ j, (ω.1 0 j i : ℂ) * Gf j ω) *
        (star v : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) := by
    rw [← integral_conj]
    apply integral_congr_ae
    have hk := ae_all_iff.mpr fun k => lpStar_apply_ae (μ := reducedLaw Q) (Gf k)
    filter_upwards [hk, lpStar_apply_ae (μ := reducedLaw Q) v] with ω hk hv
    simp only [map_sum, map_mul, Complex.conj_ofReal, hk, hv, starRingEnd_self_apply]
  rw [e1, e2, e3, key]
  simp only [map_add, map_mul, map_neg, map_div₀, map_one, map_ofNat]

/-- Conjugating a semigroup for `ζ` gives a semigroup for `conj ζ`. -/
theorem isComplexEnvironmentSemigroup_conjConj {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) :
    IsComplexEnvironmentSemigroup Q i (starRingEnd ℂ ζ) (fun t => conjConj (P t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro f
    rw [conjConj_apply, hP.1]
    simp only [ContinuousLinearMap.id_apply, star_star]
  · intro s t
    apply ContinuousLinearMap.ext
    intro f
    rw [conjConj_apply, hP.2.1 s t]
    change star (P s (P t (star f))) = star (P s (star (star (P t (star f)))))
    rw [star_star]
  · intro f
    exact lpStar_continuous.comp (hP.2.2.1 (star f))
  · intro f g
    have key : ∀ t : ℝ≥0, star (((t : ℝ) : ℂ)⁻¹ • (conjConj (P t) f - f)) =
        ((t : ℝ) : ℂ)⁻¹ • (P t (star f) - star f) := by
      intro t
      rw [lpStar_smul, lpStar_sub, conjConj_apply, star_star]
      simp only [map_inv₀, Complex.conj_ofReal]
    have hfun : (fun t : ℝ≥0 => star (((t : ℝ) : ℂ)⁻¹ • (conjConj (P t) f - f))) =
        fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t (star f) - star f) := funext key
    have h1 := hP.2.2.2 (star f) (star g)
    rw [← lpStar_tendsto_iff (g := g), hfun, h1]
    constructor
    · intro h
      simpa only [star_star] using isComplexGeneratorPair_star h
    · intro h
      simpa only [starRingEnd_self_apply] using isComplexGeneratorPair_star h

/-- For a real force every family in the frozen predicate commutes with conjugation. -/
theorem IsComplexEnvironmentSemigroup.map_star_of_real {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) : P t (star f) = star (P t f) := by
  have h1 := isComplexEnvironmentSemigroup_conjConj hP
  rw [Complex.conj_ofReal] at h1
  have h2 : P t (star f) = star (P t (star (star f))) :=
    DFunLike.congr_fun (congrFun (hP.unique h1) t) (star f)
  rw [star_star] at h2
  exact h2

/-- A real-valued class stays real-valued under a real-force semigroup. -/
theorem IsComplexEnvironmentSemigroup.star_apply_of_real {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P) (t : ℝ≥0)
    {f : Lp ℂ 2 (reducedLaw Q)} (hf : star f = f) : star (P t f) = P t f := by
  rw [← hP.map_star_of_real t f, hf]

/-- The transpose family of a real-force semigroup commutes with conjugation. -/
theorem IsComplexTransposeSemigroup.map_star {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {lam : ℝ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P)
    (hT : IsComplexTransposeSemigroup Q P Pdag) (t : ℝ≥0)
    (g : Lp ℂ 2 (reducedLaw Q)) : Pdag t (star g) = star (Pdag t g) := by
  apply ext_inner_left ℂ
  intro v
  rw [← star_star v, lpStar_inner_eq_integral, lpStar_inner_eq_integral]
  generalize star v = f
  calc ∫ ω, f ω * (Pdag t (star g)) ω ∂reducedLaw Q
      = ∫ ω, (P t f) ω * (star g : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q :=
        (hT t f (star g)).symm
    _ = starRingEnd ℂ (∫ ω, (star (P t f) : Lp ℂ 2 (reducedLaw Q)) ω * g ω
        ∂reducedLaw Q) := lpStar_integral_mul' (P t f) g
    _ = starRingEnd ℂ (∫ ω, (P t (star f)) ω * g ω ∂reducedLaw Q) := by
        rw [hP.map_star_of_real t f]
    _ = starRingEnd ℂ (∫ ω, (star f : Lp ℂ 2 (reducedLaw Q)) ω * (Pdag t g) ω
        ∂reducedLaw Q) := by rw [hT t (star f) g]
    _ = ∫ ω, f ω * (star (Pdag t g) : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q :=
        (lpStar_integral_mul' f (Pdag t g)).symm

end EinsteinFull
