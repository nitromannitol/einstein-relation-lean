import EinsteinRelation.Entropy.DivergenceFromFisher

/-!
# Weak horizontal gradients vanish on the zero set of the field

For a scalar field `f` with weak horizontal gradient `Df` (`HasWeakHorizontalGradient`), the
gradient vanishes almost everywhere on `{f = 0}`. This is the property that the premise `hzero`
of `divergence_bound_of_fisher_occupation` assumes.

The argument tests the weak identity against bounded horizontal cores, using the profiles
`truncProfile l r = r * exp (-(l * r ^ 2))`. Their derivatives are bounded by `2`, the profiles
are bounded by `1` for `1 ≤ l`, and the derivatives converge to the indicator of `{r = 0}` as
`l → ∞`. Dominated convergence and the `L¹` uniqueness on bounded cores then give the vanishing.

The chain rule for these profiles is the one input this module does not prove. It is isolated as
`HasWeakChainRule`, which says that composition with a profile preserves the weak gradient. A
proof needs mollification along the horizontal translation group for the weak notion, which the
repository does not yet provide. The module proves the reduction `hzero_of_weakChainRule`, from
which the premise `hzero` follows once the chain rule is supplied.
-/

open MeasureTheory Filter
open scoped Topology
open EinsteinRelation.Carriers

namespace EinsteinRelation.Entropy

/-! ### The truncation profiles -/

/-- The profile `r ↦ r exp (-(l r²))`. Its derivative is `truncDeriv l`, it vanishes at `0`, and it
is bounded by `1` once `1 ≤ l`. -/
noncomputable def truncProfile (l r : ℝ) : ℝ := r * Real.exp (-(l * r ^ 2))

/-- The derivative of `truncProfile l`: `(1 - 2 l r²) exp (-(l r²))`. -/
noncomputable def truncDeriv (l r : ℝ) : ℝ := (1 - 2 * (l * r ^ 2)) * Real.exp (-(l * r ^ 2))

theorem hasDerivAt_truncProfile (l r : ℝ) :
    HasDerivAt (truncProfile l) (truncDeriv l r) r := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r :=
    (hasDerivAt_pow 2 r).congr_deriv (by norm_num)
  have hlin : HasDerivAt (fun x : ℝ => -(l * x ^ 2)) (-(l * (2 * r))) r :=
    (hpow.const_mul l).neg
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(l * x ^ 2)))
      (Real.exp (-(l * r ^ 2)) * (-(l * (2 * r)))) r :=
    hlin.exp
  have hprod : HasDerivAt (fun x : ℝ => x * Real.exp (-(l * x ^ 2)))
      (1 * Real.exp (-(l * r ^ 2)) + r * (Real.exp (-(l * r ^ 2)) * (-(l * (2 * r))))) r :=
    (hasDerivAt_id' r).mul hexp
  exact hprod.congr_deriv (by unfold truncDeriv; ring)

theorem continuous_truncProfile (l : ℝ) : Continuous (truncProfile l) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_truncProfile l r).continuousAt

theorem continuous_truncDeriv (l : ℝ) : Continuous (truncDeriv l) := by
  show Continuous (fun r : ℝ => (1 - 2 * (l * r ^ 2)) * Real.exp (-(l * r ^ 2)))
  fun_prop

/-- The scalar inequality `(1 + t) e^{-t} ≤ 1`. -/
theorem exp_neg_mul_le_one (t : ℝ) : (1 + t) * Real.exp (-t) ≤ 1 := by
  calc (1 + t) * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp t]) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem abs_mul_exp_neg_sq_le_one (x : ℝ) : |x| * Real.exp (-(x ^ 2)) ≤ 1 := by
  have hx : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]
  calc |x| * Real.exp (-(x ^ 2)) ≤ (1 + x ^ 2) * Real.exp (-(x ^ 2)) :=
        mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ ≤ 1 := exp_neg_mul_le_one (x ^ 2)

theorem abs_truncProfile_le_one {l : ℝ} (hl : 1 ≤ l) (r : ℝ) : |truncProfile l r| ≤ 1 := by
  unfold truncProfile
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-(l * r ^ 2)) ≤ Real.exp (-(r ^ 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg r)])
  calc |r| * Real.exp (-(l * r ^ 2)) ≤ |r| * Real.exp (-(r ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg r)
    _ ≤ 1 := abs_mul_exp_neg_sq_le_one r

theorem abs_truncDeriv_le_two {l : ℝ} (hl : 0 ≤ l) (r : ℝ) : |truncDeriv l r| ≤ 2 := by
  have ht : 0 ≤ l * r ^ 2 := mul_nonneg hl (sq_nonneg r)
  have hb : |1 - 2 * (l * r ^ 2)| ≤ 2 * (1 + l * r ^ 2) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold truncDeriv
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |1 - 2 * (l * r ^ 2)| * Real.exp (-(l * r ^ 2))
      ≤ 2 * (1 + l * r ^ 2) * Real.exp (-(l * r ^ 2)) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = 2 * ((1 + l * r ^ 2) * Real.exp (-(l * r ^ 2))) := by ring
    _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left (exp_neg_mul_le_one _) (by norm_num)
    _ = 2 := by norm_num

theorem tendsto_mul_sq_atTop {r : ℝ} (hr : r ≠ 0) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * r ^ 2) atTop atTop := by
  have hr2 : 0 < r ^ 2 := by positivity
  refine tendsto_atTop_atTop.2 fun b => ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (b / r ^ 2)
  refine ⟨N, fun n hn => ?_⟩
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : b / r ^ 2 * r ^ 2 = b := div_mul_cancel₀ b hr2.ne'
  have h2 : b / r ^ 2 * r ^ 2 ≤ (n : ℝ) * r ^ 2 :=
    mul_le_mul_of_nonneg_right (hN.trans hnN) hr2.le
  show b ≤ ((n : ℝ) + 1) * r ^ 2
  nlinarith [sq_nonneg r]

/-- Pointwise limit of the profiles along `l = n + 1`: they tend to `0`. -/
theorem tendsto_truncProfile (r : ℝ) :
    Tendsto (fun n : ℕ => truncProfile ((n : ℝ) + 1) r) atTop (𝓝 0) := by
  by_cases hr : r = 0
  · subst hr
    have h0 : (fun n : ℕ => truncProfile ((n : ℝ) + 1) 0) = fun _ => 0 := by
      funext n
      simp [truncProfile]
    rw [h0]
    exact tendsto_const_nhds
  · have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_mul_sq_atTop hr)).const_mul r
    rw [mul_zero] at h
    exact h

/-- Pointwise limit of the derivatives along `l = n + 1`: they tend to the indicator of `{r = 0}`. -/
theorem tendsto_truncDeriv (r : ℝ) :
    Tendsto (fun n : ℕ => truncDeriv ((n : ℝ) + 1) r) atTop (𝓝 (if r = 0 then 1 else 0)) := by
  by_cases hr : r = 0
  · subst hr
    have h0 : (fun n : ℕ => truncDeriv ((n : ℝ) + 1) 0) = fun _ => 1 := by
      funext n
      simp [truncDeriv]
    rw [h0, if_pos (rfl : (0 : ℝ) = 0)]
    exact tendsto_const_nhds
  · rw [if_neg hr]
    have h1 : Tendsto (fun t : ℝ => t ^ 1 * Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h0 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have hφ : Tendsto (fun t : ℝ => Real.exp (-t) - 2 * (t ^ 1 * Real.exp (-t)))
        atTop (𝓝 0) := by
      have h := h0.sub (h1.const_mul 2)
      rw [mul_zero, sub_zero] at h
      exact h
    refine Filter.Tendsto.congr (fun n => ?_) (hφ.comp (tendsto_mul_sq_atTop hr))
    simp only [Function.comp_apply, truncDeriv, pow_one]
    ring

/-! ### The weak chain rule -/

/-- The weak horizontal chain rule for a scalar profile `g`: whenever `f` has weak horizontal
gradient `Df`, the composition `g ∘ f` has weak horizontal gradient `g'(f) Df`.

This is the input that the zero-set argument consumes. It is not proved in this module; the
module reduces the zero-set property to it. -/
def HasWeakChainRule {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q) (g : ℝ → ℝ) :
    Prop :=
  ∀ (f : FieldPair d → ℝ) (Df : FieldPair d → Vec d), HasWeakHorizontalGradient Q hQ f Df →
    HasWeakHorizontalGradient Q hQ (fun w => g (f w)) (fun w i => deriv g (f w) * Df w i)

/-! ### Pairing with bounded horizontal cores -/

/-- The weak identity for `truncProfile l ∘ f`, tested against a bounded horizontal core `H`. -/
theorem integral_truncProfile_pairing {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} {l : ℝ} (hchain : HasWeakChainRule Q hQ (truncProfile l))
    {f : FieldPair d → ℝ} {Df : FieldPair d → Vec d} (hf : HasWeakHorizontalGradient Q hQ f Df)
    (i : Fin d) {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, truncProfile l (f ω) * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, truncDeriv l (f ω) * (Df ω i * H ω) ∂Q) := by
  have hW := (hchain f Df hf).2.2 i ((hH.memLp Q 2).toLp H)
    ((hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H))
    (hH.isHorizontallySmoothTest Q hQ) (hH.hasHorizontalLpDerivative_toLp Q hQ i)
  have hG : ∀ᵐ ω ∂Q, ((hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H)) ω =
      horizontalDerivative i H ω :=
    (hH.memLp_derivative Q 2 i).coeFn_toLp
  have hF : ∀ᵐ ω ∂Q, ((hH.memLp Q 2).toLp H) ω = H ω := (hH.memLp Q 2).coeFn_toLp
  have e1 : (∫ ω, truncProfile l (f ω) * horizontalDerivative i H ω ∂Q) =
      ∫ ω, truncProfile l (f ω) * ((hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H)) ω
        ∂Q := by
    apply integral_congr_ae
    filter_upwards [hG] with ω hω
    rw [hω]
  have e2 : (∫ ω, truncDeriv l (f ω) * (Df ω i * H ω) ∂Q) =
      ∫ ω, deriv (truncProfile l) (f ω) * Df ω i * ((hH.memLp Q 2).toLp H) ω ∂Q := by
    apply integral_congr_ae
    filter_upwards [hF] with ω hω
    rw [hω, (hasDerivAt_truncProfile l (f ω)).deriv]
    ring
  rw [e1, e2]
  exact hW

/-- The integral of `1_{f = 0} Df_i H` vanishes for every bounded horizontal core `H`. The
argument tests the chain rule against the truncations `truncProfile (n + 1)`: the left side is
bounded by a constant (the derivative of `H` is bounded), the right side converges to the
indicator, and the two agree up to sign. -/
theorem integral_zero_set_pairing {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} (hchain : ∀ l : ℝ, 0 ≤ l → HasWeakChainRule Q hQ (truncProfile l))
    {f : FieldPair d → ℝ} {Df : FieldPair d → Vec d} (hf : HasWeakHorizontalGradient Q hQ f Df)
    (i : Fin d) {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, (if f ω = 0 then (1 : ℝ) else 0) * (Df ω i * H ω) ∂Q) = 0 := by
  obtain ⟨B, -, hB⟩ := hH.bound_orbit
  obtain ⟨M, -, hM⟩ := hH.bound_derivative i
  have hHb : ∀ᵐ ω ∂Q, ‖H ω‖ ≤ B :=
    Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, orbit_zero] using hB ω 0
  have hint : Integrable (fun ω => Df ω i * H ω) Q :=
    (hf.2.1 i).mul_bdd hH.1.aestronglyMeasurable hHb
  have hbound : ∀ n : ℕ, ∀ᵐ ω ∂Q,
      ‖truncDeriv ((n : ℝ) + 1) (f ω) * (Df ω i * H ω)‖ ≤ 2 * ‖Df ω i * H ω‖ := fun n =>
    Filter.Eventually.of_forall fun ω => by
      rw [norm_mul, Real.norm_eq_abs (truncDeriv ((n : ℝ) + 1) (f ω))]
      exact mul_le_mul_of_nonneg_right
        (abs_truncDeriv_le_two (l := (n : ℝ) + 1) (by positivity) (f ω)) (norm_nonneg _)
  -- The derivative side converges to the indicator of `{f = 0}`.
  have hbn : Tendsto (fun n : ℕ => ∫ ω, truncDeriv ((n : ℝ) + 1) (f ω) * (Df ω i * H ω) ∂Q)
      atTop (𝓝 (∫ ω, (if f ω = 0 then (1 : ℝ) else 0) * (Df ω i * H ω) ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => 2 * ‖Df ω i * H ω‖) ?_ ?_ hbound ?_
    · intro n
      exact ((continuous_truncDeriv ((n : ℝ) + 1)).comp_aestronglyMeasurable
        hf.1.aestronglyMeasurable).mul hint.aestronglyMeasurable
    · exact hint.norm.const_mul 2
    · exact Filter.Eventually.of_forall fun ω =>
        (tendsto_truncDeriv (f ω)).mul_const (Df ω i * H ω)
  -- The profile side converges to `0`, since `|truncProfile| ≤ 1` and it tends to `0` pointwise.
  have han : Tendsto (fun n : ℕ => ∫ ω, truncProfile ((n : ℝ) + 1) (f ω) *
      horizontalDerivative i H ω ∂Q) atTop (𝓝 (∫ _ : FieldPair d, (0 : ℝ) ∂Q)) := by
    have hbd : ∀ n : ℕ, ∀ᵐ ω ∂Q,
        ‖truncProfile ((n : ℝ) + 1) (f ω) * horizontalDerivative i H ω‖ ≤ M := fun n =>
      Filter.Eventually.of_forall fun ω => by
        have h1 := abs_truncProfile_le_one (l := (n : ℝ) + 1)
          (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (f ω)
        have h2 : |horizontalDerivative i H ω| ≤ M := hM ω 0
        rw [Real.norm_eq_abs, abs_mul]
        calc |truncProfile ((n : ℝ) + 1) (f ω)| * |horizontalDerivative i H ω| ≤ 1 * M :=
              mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = M := one_mul M
    refine tendsto_integral_of_dominated_convergence (fun _ => M) ?_ (integrable_const M) hbd ?_
    · intro n
      exact ((continuous_truncProfile ((n : ℝ) + 1)).comp_aestronglyMeasurable
        hf.1.aestronglyMeasurable).mul (hH.measurable_derivative i).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        have h := (tendsto_truncProfile (f ω)).mul_const (horizontalDerivative i H ω)
        rwa [zero_mul] at h
  rw [integral_zero] at han
  have hid : ∀ n : ℕ, (∫ ω, truncProfile ((n : ℝ) + 1) (f ω) * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, truncDeriv ((n : ℝ) + 1) (f ω) * (Df ω i * H ω) ∂Q) := fun n =>
    integral_truncProfile_pairing (hchain ((n : ℝ) + 1) (by positivity)) hf i hH
  have hb0 : Tendsto (fun n : ℕ => ∫ ω, truncDeriv ((n : ℝ) + 1) (f ω) * (Df ω i * H ω) ∂Q)
      atTop (𝓝 0) := by
    have h := han.neg
    rw [neg_zero] at h
    refine Filter.Tendsto.congr (fun n => ?_) h
    show -(∫ ω, truncProfile ((n : ℝ) + 1) (f ω) * horizontalDerivative i H ω ∂Q) =
      ∫ ω, truncDeriv ((n : ℝ) + 1) (f ω) * (Df ω i * H ω) ∂Q
    rw [hid n, neg_neg]
  exact tendsto_nhds_unique hbn hb0

/-! ### The zero set of the gradient -/

/-- The `i`-th coordinate of the weak gradient vanishes almost everywhere on `{f = 0}`. The proof
packages `1_{f = 0} Df_i` as an `L¹` class, which pairs to zero with every bounded core, and
applies the `L¹` uniqueness of the horizontal cores. -/
theorem ae_zero_set_coord {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} (hchain : ∀ l : ℝ, 0 ≤ l → HasWeakChainRule Q hQ (truncProfile l))
    {f : FieldPair d → ℝ} {Df : FieldPair d → Vec d} (hf : HasWeakHorizontalGradient Q hQ f Df)
    (i : Fin d) : ∀ᵐ ω ∂Q, f ω = 0 → Df ω i = 0 := by
  obtain ⟨fm, hfm, hfae⟩ : ∃ fm : FieldPair d → ℝ, Measurable fm ∧ f =ᵐ[Q] fm :=
    ⟨hf.1.aestronglyMeasurable.mk f, hf.1.aestronglyMeasurable.measurable_mk,
      hf.1.aestronglyMeasurable.ae_eq_mk⟩
  have hS : MeasurableSet {ω : FieldPair d | fm ω = 0} :=
    hfm (measurableSet_singleton (0 : ℝ))
  have hu : Integrable (Set.indicator {ω : FieldPair d | fm ω = 0} (fun ω => Df ω i)) Q :=
    (hf.2.1 i).indicator hS
  have hg : (Integrable.toL1 _ hu : Lp ℝ 1 Q) = 0 := by
    refine eq_zero_of_horizontalCore_pairing_eq_zero_l1 Q hQ _ (fun H hH => ?_)
    refine Eq.trans ?_ (integral_zero_set_pairing hchain hf i hH)
    apply integral_congr_ae
    filter_upwards [Integrable.coeFn_toL1 hu, hfae] with ω hω hfω
    rw [hω, hfω]
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> ring
  have hae0 : ∀ᵐ ω ∂Q, Set.indicator {ω : FieldPair d | fm ω = 0} (fun ω => Df ω i) ω = 0 := by
    filter_upwards [Integrable.coeFn_toL1 hu, Lp.coeFn_zero ℝ 1 Q] with ω hω hz
    rw [← hω, hg]
    exact hz
  filter_upwards [hae0, hfae] with ω h0 hfω
  intro hfz
  have hm : fm ω = 0 := by
    rw [← hfω]
    exact hfz
  rw [Set.indicator_of_mem (show ω ∈ {ω : FieldPair d | fm ω = 0} from hm)] at h0
  exact h0

/-- A weak horizontal gradient vanishes almost everywhere on the zero set of its field. -/
theorem ae_zero_set_gradient {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} (hchain : ∀ l : ℝ, 0 ≤ l → HasWeakChainRule Q hQ (truncProfile l))
    {f : FieldPair d → ℝ} {Df : FieldPair d → Vec d} (hf : HasWeakHorizontalGradient Q hQ f Df) :
    ∀ᵐ ω ∂Q, f ω = 0 → Df ω = 0 := by
  have hall : ∀ᵐ ω ∂Q, ∀ i : Fin d, f ω = 0 → Df ω i = 0 :=
    ae_all_iff.2 fun i => ae_zero_set_coord hchain hf i
  filter_upwards [hall] with ω hω hz
  funext i
  exact hω i hz

/-- The premise `hzero` of `divergence_bound_of_fisher_occupation`, reduced to the weak chain rule
for the truncation profiles `truncProfile l` with `0 ≤ l`. Once that chain rule is proved for every
environment law, this gives `hzero` in the exact form the divergence bound consumes. -/
theorem hzero_of_weakChainRule {d : ℕ} {Λ₀ r₀ : ℝ}
    (hchain : ∀ (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (reducedReferenceLaw Q))
      (l : ℝ), 0 ≤ l → HasWeakChainRule (reducedReferenceLaw Q) hQ (truncProfile l)) :
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (reducedReferenceLaw Q))
      (rho : FieldPair d → ℝ) (Drho : FieldPair d → Vec d),
      HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho →
        ∀ᵐ w ∂(reducedReferenceLaw Q), rho w = 0 → Drho w = 0 :=
  fun Q hQ _ _ hW => ae_zero_set_gradient (hchain Q hQ) hW

/-- Lemma 4.2, first assertion (`paper/main.tex:619–633`), with the premise `hzero` of
`divergence_bound_of_fisher_occupation` replaced by the weak horizontal chain rule for the
truncation profiles. The chain rule is not proved in this module; it is the single remaining input,
and `hzero_of_weakChainRule` gives the reduction. -/
theorem divergence_bound_of_fisher_occupation' (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (hFisher : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
      ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∀ (P : QuenchedPathLaws d)
        (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
        IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
      ∀ s : {r : ℝ // 0 < r}, ∀ rho : FieldPair d → ℝ,
        IsReducedLaplaceDensity Q.measure P origin_probability s rho →
        ∃ Drho : FieldPair d → Vec d,
          HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho ∧
          Integrable (fun w => euclideanNorm (Drho w)) (reducedReferenceLaw Q) ∧
          (∫⁻ w, ENNReal.ofReal
              (if rho w = 0 then 0 else dot (Drho w) ((w.1 0).mulVec (Drho w)) / rho w)
              ∂(reducedReferenceLaw Q)) ≤
            ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2))
    (hOcc : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
      ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
      ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
        ∀ (P : QuenchedPathLaws d)
          (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
          IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
        ∀ G : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
          MemLp G (ENNReal.ofReal p) (reducedReferenceLaw Q) →
        ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
          (∫⁻ z : FieldPair d × Path d,
              (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal |G (reducedObservationAt t.toNNReal z)|)
            ∂(annealedCoordinateJoint Q.measure P origin_probability)) ≤
              ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q) ∧
          ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity Q.measure P origin_probability s rho →
            (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(reducedReferenceLaw Q)) ≤
              ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q))
    (hchain : ∀ (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (reducedReferenceLaw Q))
      (l : ℝ), 0 ≤ l → HasWeakChainRule (reducedReferenceLaw Q) hQ (truncProfile l)) :
    ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
    ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
      ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∀ (P : QuenchedPathLaws d)
        (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
        IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
      ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
      ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity Q.measure P origin_probability s rho →
      ∀ Drho : FieldPair d → Vec d,
        HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho →
      ∀ F : FieldPair d → Vec d,
        Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] F →
        MemLp (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
          (reducedReferenceLaw Q) →
        Integrable (fun w => dot (Drho w) (F w)) (reducedReferenceLaw Q) ∧
          (ENNReal.ofReal (abs (∫ w, dot (Drho w) (F w) ∂(reducedReferenceLaw Q))) ≤
            ENNReal.ofReal (C * lam) *
              eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
                (reducedReferenceLaw Q)) :=
  divergence_bound_of_fisher_occupation d hd Λ₀ r₀ hFisher hOcc (hzero_of_weakChainRule hchain)

end EinsteinRelation.Entropy
