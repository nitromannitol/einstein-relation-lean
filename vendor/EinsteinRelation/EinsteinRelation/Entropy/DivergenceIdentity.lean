import EinsteinRelation.Entropy.DivergenceFromFisher

/-!
# Lemma 4.2, second assertion: passage to the limit

Source: `paper/main.tex` lines 634–638 (`entropy.divergence`, second assertion). The second
assertion says that `E[ρ_s D·F] = -E[Dρ_s·F]` when `D·F` is in `L^{2p}`. The divergence `h`
enters only through the weak identity `HasWeakHorizontalDivergence`, which tests against
horizontally smooth fields. The weak gradient identity of `HasWeakHorizontalGradient` has the
same test class. Neither definition gives the identity for an arbitrary `L^{2p}` field, so the
argument needs horizontally smooth approximants `T n` of `F` whose horizontal divergences
`∑ᵢ D n i` converge to `h`. This file proves the argument from such approximants. The
approximation itself is the interface `HorizontalSmoothApproximation`, which is not yet
constructed.

The proof has three parts:

* integration by parts for each approximant, from the weak gradient identity of `ρ`
  (`integral_rho_mul_sum_eq`);
* the two error bounds: the occupation bound (Proposition 3.2) for the residual
  `h - ∑ᵢ D n i`, and the first-assertion bound (`first_assertion_bound_on_ball`, from
  Lemma 4.1 and Proposition 3.2) for `F - T n`;
* the limit `n → ∞`, which turns the two bounds into the identity
  (`divergence_identity_of_approximation`).
-/

open MeasureTheory Filter
open scoped Topology
open EinsteinRelation.Carriers

namespace EinsteinRelation.Entropy

/-! ### The approximation interface -/

/-- Horizontally smooth approximants of an `L^{2p}` field `F` with weak divergence `h`, localized
on `U`. The family `T n` consists of horizontally smooth tests whose coordinate derivatives are
`D n i`. The fields `F - T n` and the residuals `h - ∑ᵢ D n i` are measurable for the local
σ-algebra of `U` up to null sets, and both converge in the norms that the occupation and
first-assertion bounds control. This is the horizontal regularization step of `main.tex`
634–638. It is an explicit interface because the repository does not yet construct such
approximants. -/
def HorizontalSmoothApproximation {d : ℕ} (μ : Measure (FieldPair d)) (hμ : IsStationary μ)
    (U : Set (Vec d)) (p : ℝ) (F : FieldPair d → Vec d) (h : FieldPair d → ℝ) : Prop :=
  ∃ T D : ℕ → Fin d → Lp ℝ 2 μ,
    (∀ n i, IsHorizontallySmoothTest μ hμ (T n i) ∧
      HasHorizontalLpDerivative μ hμ i (T n i) (D n i)) ∧
    (∀ n, ∃ G : FieldPair d → Vec d, Measurable[localSigma U] G ∧
      (fun ω => fun i => F ω i - (T n i) ω) =ᵐ[μ] G) ∧
    (∀ n, MemLp (fun ω => euclideanNorm (fun i => F ω i - (T n i) ω))
      (ENNReal.ofReal (2 * p)) μ) ∧
    Tendsto (fun n => eLpNorm (fun ω => euclideanNorm (fun i => F ω i - (T n i) ω))
      (ENNReal.ofReal (2 * p)) μ) atTop (𝓝 0) ∧
    (∀ n, ∃ g : FieldPair d → ℝ, Measurable[localSigma U] g ∧
      (fun ω => h ω - ∑ i, (D n i) ω) =ᵐ[μ] g) ∧
    (∀ n, MemLp (fun ω => h ω - ∑ i, (D n i) ω) (ENNReal.ofReal p) μ) ∧
    Tendsto (fun n => eLpNorm (fun ω => h ω - ∑ i, (D n i) ω) (ENNReal.ofReal p) μ)
      atTop (𝓝 0)

/-! ### Elementary facts about horizontally smooth tests -/

/-- A horizontally smooth test is essentially bounded. -/
theorem isHorizontallySmoothTest_ae_bound {d : ℕ} {μ : Measure (FieldPair d)}
    {hμ : IsStationary μ} {F : Lp ℝ 2 μ} (hF : IsHorizontallySmoothTest μ hμ F) :
    ∃ M : ℝ, ∀ᵐ ω ∂μ, |F ω| ≤ M := by
  obtain ⟨G, hG, M, hM⟩ := hF []
  have hGF : G = F := hG
  rw [hGF] at hM
  exact ⟨M, hM⟩

/-- The horizontal derivative of a horizontally smooth test is essentially bounded. -/
theorem isHorizontallySmoothTest_ae_bound_deriv {d : ℕ} {μ : Measure (FieldPair d)}
    {hμ : IsStationary μ} {F G : Lp ℝ 2 μ} {i : Fin d} (hF : IsHorizontallySmoothTest μ hμ F)
    (hG : HasHorizontalLpDerivative μ hμ i F G) : ∃ M : ℝ, ∀ᵐ ω ∂μ, |G ω| ≤ M := by
  obtain ⟨G', hG', M, hM⟩ := hF [i]
  have hG'' : ∃ F', HasIteratedHorizontalLpDerivative μ hμ [] F F' ∧
      HasHorizontalLpDerivative μ hμ i F' G' := hG'
  obtain ⟨F', hF'0, hF'1⟩ := hG''
  have hF'eq : F' = F := hF'0
  rw [hF'eq] at hF'1
  have hGG : G' = G := HasHorizontalLpDerivative.unique hF'1 hG
  rw [hGG] at hM
  exact ⟨M, hM⟩

/-- Integrability of `ρ · G` when `G` is the horizontal derivative of a bounded test. -/
theorem integrable_rho_mul_derivative {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ}
    {ρ : FieldPair d → ℝ} (hρ : Integrable ρ μ) {F G : Lp ℝ 2 μ} {i : Fin d}
    (hF : IsHorizontallySmoothTest μ hμ F) (hG : HasHorizontalLpDerivative μ hμ i F G) :
    Integrable (fun ω => ρ ω * G ω) μ := by
  obtain ⟨M, hM⟩ := isHorizontallySmoothTest_ae_bound_deriv hF hG
  exact hρ.mul_bdd (Lp.aestronglyMeasurable G)
    (hM.mono fun ω hω => by rw [Real.norm_eq_abs]; exact hω)

/-- Integrability of `f · F` when `F` is a horizontally smooth test and `f` is integrable. -/
theorem integrable_mul_test {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ}
    {f : FieldPair d → ℝ} (hf : Integrable f μ) {F : Lp ℝ 2 μ}
    (hF : IsHorizontallySmoothTest μ hμ F) : Integrable (fun ω => f ω * F ω) μ := by
  obtain ⟨M, hM⟩ := isHorizontallySmoothTest_ae_bound hF
  exact hf.mul_bdd (Lp.aestronglyMeasurable F)
    (hM.mono fun ω hω => by rw [Real.norm_eq_abs]; exact hω)

/-! ### Real and extended-real helpers -/

/-- The Euclidean pairing is linear in its second argument. -/
theorem dot_sub_vec {d : ℕ} (x y z : Vec d) :
    dot x (fun i => y i - z i) = dot x y - dot x z := by
  simp only [dot, mul_sub, Finset.sum_sub_distrib]

/-- Integrability from a finite lower Lebesgue integral of the absolute value. -/
theorem integrable_of_lintegral_abs_lt' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hfin : ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ < ⊤) :
    Integrable f μ := by
  refine ⟨hf, ?_⟩
  unfold HasFiniteIntegral
  simpa only [Real.enorm_eq_ofReal_abs] using hfin

/-- Extended-real bound on the absolute value of an integral. -/
theorem abs_integral_ofReal_le_of_lintegral_le' {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) {M : ENNReal} (h : ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ ≤ M) :
    ENNReal.ofReal |∫ ω, f ω ∂μ| ≤ M := by
  calc ENNReal.ofReal |∫ ω, f ω ∂μ| = ‖∫ ω, f ω ∂μ‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ ω, ‖f ω‖ₑ ∂μ := enorm_integral_le_lintegral_enorm f
    _ = ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ := lintegral_congr fun ω => Real.enorm_eq_ofReal_abs _
    _ ≤ M := h

/-! ### Integration by parts for horizontally smooth approximants -/

/-- Integration by parts against the weak gradient of `ρ`, for a finite family of horizontally
smooth tests `T i` with derivatives `D i`: `E[ρ ∑ᵢ D_i] = -E[Dρ · T]`. -/
theorem integral_rho_mul_sum_eq {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ}
    {ρ : FieldPair d → ℝ} {Dρ : FieldPair d → Vec d} (hW : HasWeakHorizontalGradient μ hμ ρ Dρ)
    (T D : Fin d → Lp ℝ 2 μ)
    (hTD : ∀ i, IsHorizontallySmoothTest μ hμ (T i) ∧ HasHorizontalLpDerivative μ hμ i (T i) (D i)) :
    (∫ ω, (ρ ω * ∑ i, (D i) ω) ∂μ) = -∫ ω, dot (Dρ ω) (fun i => (T i) ω) ∂μ := by
  have hDint : ∀ i, Integrable (fun ω => ρ ω * (D i) ω) μ := fun i =>
    integrable_rho_mul_derivative hW.1 (hTD i).1 (hTD i).2
  have hTint : ∀ i, Integrable (fun ω => Dρ ω i * (T i) ω) μ := fun i =>
    integrable_mul_test (hW.2.1 i) (hTD i).1
  have e1 : (∫ ω, (ρ ω * ∑ i, (D i) ω) ∂μ) = ∑ i, ∫ ω, ρ ω * (D i) ω ∂μ := by
    rw [← integral_finset_sum Finset.univ fun i _ => hDint i]
    congr 1
    funext ω
    rw [Finset.mul_sum]
  have e2 : (∫ ω, dot (Dρ ω) (fun i => (T i) ω) ∂μ) = ∑ i, ∫ ω, Dρ ω i * (T i) ω ∂μ := by
    rw [← integral_finset_sum Finset.univ fun i _ => hTint i]
    rfl
  rw [e1, e2, Finset.sum_congr rfl fun i _ => hW.2.2 i (T i) (D i) (hTD i).1 (hTD i).2,
    Finset.sum_neg_distrib]

/-! ### The limit passage -/

/-- Lemma 4.2, second assertion, from horizontally smooth approximants. The occupation bound
`hocc` is the `ρ`-part of Proposition 3.2 on the ball `U`, and `hdiv` is the first assertion of
Lemma 4.2 on `U`. Both are taken as hypotheses here. The weak divergence enters only through
`happ`. -/
theorem divergence_identity_of_approximation {d : ℕ} {μ : Measure (FieldPair d)}
    {hμ : IsStationary μ} {U : Set (Vec d)} {p K K' : ℝ} {ρ : FieldPair d → ℝ}
    (hρ0 : ∀ w, 0 ≤ ρ w) {Dρ : FieldPair d → Vec d}
    (hW : HasWeakHorizontalGradient μ hμ ρ Dρ)
    (hocc : ∀ G : FieldPair d → ℝ, Measurable[localSigma U] G → MemLp G (ENNReal.ofReal p) μ →
      ∫⁻ ω, ENNReal.ofReal (ρ ω) * ENNReal.ofReal |G ω| ∂μ ≤
        ENNReal.ofReal K * eLpNorm G (ENNReal.ofReal p) μ)
    (hdiv : ∀ G : FieldPair d → Vec d, Measurable[localSigma U] G →
      MemLp (fun ω => euclideanNorm (G ω)) (ENNReal.ofReal (2 * p)) μ →
      Integrable (fun ω => dot (Dρ ω) (G ω)) μ ∧
        ENNReal.ofReal |∫ ω, dot (Dρ ω) (G ω) ∂μ| ≤
          ENNReal.ofReal K' * eLpNorm (fun ω => euclideanNorm (G ω)) (ENNReal.ofReal (2 * p)) μ)
    {F : FieldPair d → Vec d} {h : FieldPair d → ℝ}
    (happ : HorizontalSmoothApproximation μ hμ U p F h) :
    Integrable (fun ω => ρ ω * h ω) μ ∧
      (∫ ω, ρ ω * h ω ∂μ) = -∫ ω, dot (Dρ ω) (F ω) ∂μ := by
  unfold HorizontalSmoothApproximation at happ
  obtain ⟨T, D, hTD, hGrep, hTmem, hTconv, hres, hresmem, hresconv⟩ := happ
  choose G hGm hGae using hGrep
  choose g hgm hgae using hres
  -- The residual `ρ (h - ∑ D n i)` is integrable, with the occupation bound.
  have hL : ∀ n, ∫⁻ ω, ENNReal.ofReal |ρ ω * (h ω - ∑ i, (D n i) ω)| ∂μ ≤
      ENNReal.ofReal K * eLpNorm (fun ω => h ω - ∑ i, (D n i) ω) (ENNReal.ofReal p) μ := by
    intro n
    have hfac : ∀ ω, ENNReal.ofReal |ρ ω * (h ω - ∑ i, (D n i) ω)| =
        ENNReal.ofReal (ρ ω) * ENNReal.ofReal |h ω - ∑ i, (D n i) ω| := fun ω => by
      rw [abs_mul, abs_of_nonneg (hρ0 ω), ENNReal.ofReal_mul (hρ0 ω)]
    have hae : (fun ω => h ω - ∑ i, (D n i) ω) =ᵐ[μ] g n := hgae n
    have hlin : ∫⁻ ω, ENNReal.ofReal (ρ ω) * ENNReal.ofReal |h ω - ∑ i, (D n i) ω| ∂μ =
        ∫⁻ ω, ENNReal.ofReal (ρ ω) * ENNReal.ofReal |g n ω| ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ω hω
      show ENNReal.ofReal (ρ ω) * ENNReal.ofReal |h ω - ∑ i, (D n i) ω| =
        ENNReal.ofReal (ρ ω) * ENNReal.ofReal |g n ω|
      rw [show h ω - ∑ i, (D n i) ω = g n ω from hω]
    rw [lintegral_congr hfac, hlin, eLpNorm_congr_ae hae]
    exact hocc (g n) (hgm n) (MemLp.ae_eq hae (hresmem n))
  have hres_int : ∀ n, Integrable (fun ω => ρ ω * (h ω - ∑ i, (D n i) ω)) μ := by
    intro n
    refine integrable_of_lintegral_abs_lt'
      (hW.1.aestronglyMeasurable.mul (hresmem n).aestronglyMeasurable) ?_
    exact lt_of_le_of_lt (hL n)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 (hresmem n).eLpNorm_ne_top))
  -- The divergence part `ρ ∑ D n i` and the pairing `Dρ · T n` are integrable.
  have hrS_int : ∀ n, Integrable (fun ω => ρ ω * ∑ i, (D n i) ω) μ := by
    intro n
    have hfun : (fun ω => ρ ω * ∑ i, (D n i) ω) = fun ω => ∑ i, ρ ω * (D n i) ω := by
      funext ω
      rw [Finset.mul_sum]
    rw [hfun]
    exact integrable_finset_sum Finset.univ fun i _ =>
      integrable_rho_mul_derivative hW.1 (hTD n i).1 (hTD n i).2
  have hdot_int : ∀ n, Integrable (fun ω => dot (Dρ ω) (fun i => (T n i) ω)) μ := by
    intro n
    have hsum := integrable_finset_sum (μ := μ) Finset.univ fun i _ =>
      integrable_mul_test (hW.2.1 i) (hTD n i).1
    exact hsum
  -- Membership of the vector differences, and the identification of the pairings.
  have hEqG : ∀ n, (fun ω => euclideanNorm (fun i => F ω i - (T n i) ω)) =ᵐ[μ]
      (fun ω => euclideanNorm (G n ω)) := by
    intro n
    filter_upwards [hGae n] with ω hω
    show euclideanNorm (fun i => F ω i - (T n i) ω) = euclideanNorm (G n ω)
    rw [show G n ω = fun i => F ω i - (T n i) ω from hω.symm]
  have hMemG : ∀ n, MemLp (fun ω => euclideanNorm (G n ω)) (ENNReal.ofReal (2 * p)) μ :=
    fun n => MemLp.ae_eq (hEqG n) (hTmem n)
  have hdotF : ∀ n, (fun ω => dot (Dρ ω) (F ω)) =ᵐ[μ]
      (fun ω => dot (Dρ ω) (G n ω) + dot (Dρ ω) (fun i => (T n i) ω)) := by
    intro n
    filter_upwards [hGae n] with ω hω
    have hGω : G n ω = fun i => F ω i - (T n i) ω := hω.symm
    show dot (Dρ ω) (F ω) = dot (Dρ ω) (G n ω) + dot (Dρ ω) (fun i => (T n i) ω)
    rw [hGω, dot_sub_vec]
    ring
  -- Integration by parts for each approximant, split along the residual.
  have hkey : ∀ n, (∫ ω, ρ ω * h ω ∂μ) + ∫ ω, dot (Dρ ω) (F ω) ∂μ =
      (∫ ω, ρ ω * (h ω - ∑ i, (D n i) ω) ∂μ) + ∫ ω, dot (Dρ ω) (G n ω) ∂μ := by
    intro n
    have hpt : (fun ω => ρ ω * h ω) =
        fun ω => ρ ω * (h ω - ∑ i, (D n i) ω) + ρ ω * ∑ i, (D n i) ω := by
      funext ω
      ring
    rw [hpt, integral_add (hres_int n) (hrS_int n), integral_congr_ae (hdotF n),
      integral_add (hdiv (G n) (hGm n) (hMemG n)).1 (hdot_int n),
      integral_rho_mul_sum_eq hW (T n) (D n) (hTD n)]
    ring
  -- The two error terms, bounded by the occupation and first-assertion estimates.
  have hA : ∀ n, ENNReal.ofReal |∫ ω, ρ ω * (h ω - ∑ i, (D n i) ω) ∂μ| ≤
      ENNReal.ofReal K * eLpNorm (fun ω => h ω - ∑ i, (D n i) ω) (ENNReal.ofReal p) μ :=
    fun n => abs_integral_ofReal_le_of_lintegral_le' μ (fun ω => ρ ω * (h ω - ∑ i, (D n i) ω))
      (hL n)
  have hB : ∀ n, ENNReal.ofReal |∫ ω, dot (Dρ ω) (G n ω) ∂μ| ≤
      ENNReal.ofReal K' * eLpNorm (fun ω => euclideanNorm (fun i => F ω i - (T n i) ω))
        (ENNReal.ofReal (2 * p)) μ := by
    intro n
    have h1 := (hdiv (G n) (hGm n) (hMemG n)).2
    rw [← eLpNorm_congr_ae (hEqG n)] at h1
    exact h1
  have hbound : ∀ n, ENNReal.ofReal |(∫ ω, ρ ω * h ω ∂μ) + ∫ ω, dot (Dρ ω) (F ω) ∂μ| ≤
      ENNReal.ofReal K * eLpNorm (fun ω => h ω - ∑ i, (D n i) ω) (ENNReal.ofReal p) μ +
        ENNReal.ofReal K' * eLpNorm (fun ω => euclideanNorm (fun i => F ω i - (T n i) ω))
          (ENNReal.ofReal (2 * p)) μ := by
    intro n
    rw [hkey n]
    calc ENNReal.ofReal |(∫ ω, ρ ω * (h ω - ∑ i, (D n i) ω) ∂μ) +
          ∫ ω, dot (Dρ ω) (G n ω) ∂μ|
        ≤ ENNReal.ofReal (|∫ ω, ρ ω * (h ω - ∑ i, (D n i) ω) ∂μ| +
            |∫ ω, dot (Dρ ω) (G n ω) ∂μ|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ ≤ ENNReal.ofReal |∫ ω, ρ ω * (h ω - ∑ i, (D n i) ω) ∂μ| +
            ENNReal.ofReal |∫ ω, dot (Dρ ω) (G n ω) ∂μ| := ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add (hA n) (hB n)
  -- The right-hand side tends to zero along the approximants.
  have hlim : Tendsto (fun n => ENNReal.ofReal K *
        eLpNorm (fun ω => h ω - ∑ i, (D n i) ω) (ENNReal.ofReal p) μ +
      ENNReal.ofReal K' *
        eLpNorm (fun ω => euclideanNorm (fun i => F ω i - (T n i) ω)) (ENNReal.ofReal (2 * p)) μ)
      atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hresconv
      (Or.inr ENNReal.ofReal_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K') hTconv
      (Or.inr ENNReal.ofReal_ne_top)
    simpa only [mul_zero, add_zero] using h1.add h2
  have hzero : ENNReal.ofReal |(∫ ω, ρ ω * h ω ∂μ) + ∫ ω, dot (Dρ ω) (F ω) ∂μ| ≤ 0 :=
    ge_of_tendsto' hlim hbound
  have hX : |(∫ ω, ρ ω * h ω ∂μ) + ∫ ω, dot (Dρ ω) (F ω) ∂μ| ≤ 0 :=
    ENNReal.ofReal_eq_zero.1 (le_antisymm hzero zero_le)
  have hsum0 : (∫ ω, ρ ω * h ω ∂μ) + ∫ ω, dot (Dρ ω) (F ω) ∂μ = 0 := abs_nonpos_iff.1 hX
  have hint : Integrable (fun ω => ρ ω * h ω) μ := by
    refine ((hres_int 0).add (hrS_int 0)).congr (Filter.Eventually.of_forall fun ω => ?_)
    show ρ ω * (h ω - ∑ i, (D 0 i) ω) + ρ ω * ∑ i, (D 0 i) ω = ρ ω * h ω
    ring
  exact ⟨hint, by linarith⟩

/-! ### The first-assertion input from the twin premises -/

/-- The first-assertion bound on the ball `{|x| < l / λ}`, derived from the Fisher bound of
Lemma 4.1 (`hFis`), the occupation bound of Proposition 3.2 (`hC`, at the squared field), and the
vanishing of the gradient on `{ρ = 0}` (`hzero`). This is the `hdiv` hypothesis of
`divergence_identity_of_approximation`. -/
theorem first_assertion_bound_on_ball {d : ℕ} {Λ₀ r₀ l p C : ℝ} (hC0 : 0 ≤ C)
    (hp0 : 0 ≤ p) (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (reducedReferenceLaw Q))
    {lam : ℝ} (hl0 : 0 < lam) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    {s : {r : ℝ // 0 < r}} (hs : s.1 ≤ lam ^ 2)
    {rho : FieldPair d → ℝ} (hrho : IsReducedLaplaceDensity Q.measure P origin_probability s rho)
    {Drho : FieldPair d → Vec d}
    (hW : HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho)
    (hzero : ∀ᵐ w ∂(reducedReferenceLaw Q), rho w = 0 → Drho w = 0)
    (hFis : ∃ Drho₀ : FieldPair d → Vec d,
      HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho₀ ∧
      Integrable (fun w => euclideanNorm (Drho₀ w)) (reducedReferenceLaw Q) ∧
      (∫⁻ w, ENNReal.ofReal
          (if rho w = 0 then 0 else dot (Drho₀ w) ((w.1 0).mulVec (Drho₀ w)) / rho w)
          ∂(reducedReferenceLaw Q)) ≤ ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2))
    (hC : ∀ G : FieldPair d → ℝ, Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
      MemLp G (ENNReal.ofReal p) (reducedReferenceLaw Q) →
      (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(reducedReferenceLaw Q)) ≤
        ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
          eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q)) :
    ∀ G : FieldPair d → Vec d, Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
      MemLp (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) →
      Integrable (fun w => dot (Drho w) (G w)) (reducedReferenceLaw Q) ∧
        ENNReal.ofReal |∫ w, dot (Drho w) (G w) ∂(reducedReferenceLaw Q)| ≤
          ENNReal.ofReal (2 * sourceReducedBound Λ₀ * Real.sqrt (2 * C) * lam) *
            eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p))
              (reducedReferenceLaw Q) := by
  obtain ⟨Drho₀, hW₀, -, hK₀⟩ := hFis
  intro G hGloc hGmem
  have hGm : Measurable G := measurable_of_localSigma_vec hGloc
  have hGsq : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}]
      (fun w => euclideanSq (G w)) := measurable_euclideanSq_vec.comp hGloc
  have hGsqmem : MemLp (fun w => euclideanSq (G w)) (ENNReal.ofReal p)
      (reducedReferenceLaw Q) := memLp_euclideanSq_of _ hGm hp0 hGmem
  have hOccRaw := hC (fun w => euclideanSq (G w)) hGsq hGsqmem
  exact divergence_fixed_bound Q hl0 hs hrho.1 hrho.2.1 hW hW₀ hzero hK₀ hGm hp0 hC0 hGmem
    hOccRaw

end EinsteinRelation.Entropy
