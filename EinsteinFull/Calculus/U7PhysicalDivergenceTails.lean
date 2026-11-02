import EinsteinFull.Calculus.C7ForcedLocalityRetainedCore
import EinsteinFull.Calculus.SqrtBetaSupport
import EinsteinFull.Calculus.ComplexHighExponentAnalyticSupport
import EinsteinFull.Calculus.S5OffDiagonalSupport
import EinsteinFull.Calculus.U4PhysicalComplexC1Smoothing

open MeasureTheory EinsteinRelation
open scoped NNReal ENNReal Topology

namespace EinsteinFull
open Blueprint

/-- The positive-time evolution of a distributional divergence, defined by
transposition of the actual physical transpose gradient. -/
noncomputable def u7PhysicalEvolvedDivergence
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (s : ℝ) (F : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    Lp ℂ 2 (volume : Measure (Vec d)) :=
  if hs : 0 < s then
    (Blueprint.c7_physical_evolved_divergence hΛ hell hsmooth hP hPdag
      s.toNNReal (Real.toNNReal_pos.mpr hs)).choose_spec.choose F
  else 0

/-- The selected divergence evolution has the actual transpose-gradient pairing. -/
theorem u7_physical_evolved_divergence_pairing
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    {s : ℝ} (hs : 0 < s) :
    ∃ T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      (Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ g, IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal g) (T g)) ∧
      ∀ F : Fin d → Lp ℂ 2 (volume : Measure (Vec d)), ∀ g,
        (∫ x, u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s F x * g x) =
          -∑ j, ∫ x, F j x * T g j x := by
  let h := Blueprint.c7_physical_evolved_divergence hΛ hell hsmooth hP hPdag
    s.toNNReal (Real.toNNReal_pos.mpr hs)
  refine ⟨h.choose, h.choose_spec.choose_spec.1, ?_⟩
  intro F g
  simpa only [u7PhysicalEvolvedDivergence, dite_eq_left hs] using h.choose_spec.choose_spec.2 F g

/-- Fieldwise Gaussian tail for the actual transpose gradient. -/
theorem u7_physical_transpose_gradient_offdiagonal
    (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (_hell : IsElliptic Λ ω.1) (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (_hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
    ∀ (s : ℝ≥0), 0 < s → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ x ∂volume, ρ / 2 ≤ euclideanNorm (x - z) → g x = 0) →
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s g) G ∧
      Real.sqrt (∑ j : Fin d,
        ((eLpNorm ({x : Vec d | ρ ≤ euclideanNorm (x - z)}.indicator
          (fun x => G j x)) 2 volume).toReal) ^ 2) ≤
        C * ((Real.sqrt (s : ℝ))⁻¹ + ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * (s : ℝ) - c * ρ ^ 2 / (s : ℝ)) * ‖g‖ := by
  let A : ℝ := 16 * Λ ^ 3 + 8 * Λ ^ 2 * (160 * Λ ^ 4 + 4) + 8
  let N : ℝ := 42 * Λ ^ 3 + 1
  have hΛ0 : 0 < Λ := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨Real.sqrt A + N / 2 + 1, 9 / (200 * N), ?_, by positivity, ?_⟩
  · have := Real.sqrt_nonneg A
    linarith
  intro ω hell i ζ P Pdag hPdag s hs z ρ hρ g hg
  have hs' : 0 < (s : ℝ) := NNReal.coe_pos.mpr hs
  have hmeas : ∀ j k, Measurable fun x => ω.1 x j k := fun j k =>
    (ω.1.continuous.matrix_elem j k).measurable
  have ha := fun j k => memLp_complex_elliptic_entry volume ω.1 Λ hΛ0 hell
    (fun j k => ω.1.continuous.matrix_elem j k) j k
  obtain ⟨G, hG, hb⟩ := Blueprint.c7_transpose_radial_gradient_tail ω.1 i ζ ha hΛ
    (s5Elliptic_of_isElliptic hΛ hell) hmeas P Pdag hPdag z hρ
    (show 0 ≤ 3 * ρ / (10 * N * (s : ℝ)) by positivity) s hs' g hg
  refine ⟨G, hG, hb.trans ?_⟩
  have hK := Blueprint.c7_weightedGradientConst_le (q := 3 * ρ / (10 * N * (s : ℝ))) hΛ ζ hs'
  change Blueprint.c7WeightedGradientConst Λ _ _ _ ≤ (A / (s : ℝ)) *
    Real.exp (N * ((_ ^ 2 + ‖ζ‖ ^ 2) * (s : ℝ))) at hK
  have hsq := Real.sqrt_le_sqrt hK
  have h1 := mul_le_mul_of_nonneg_left hsq
    (Real.exp_pos (-(3 * (3 * ρ / (10 * N * (s : ℝ))) * ρ / 10))).le
  calc _ ≤ _ := mul_le_mul_of_nonneg_right h1 (norm_nonneg g)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Blueprint.c7_radial_tail_arith (A := A) (N := N) (x := ‖ζ‖)
        (s := (s : ℝ)) (ρ := ρ) hA hN (norm_nonneg ζ) hs') (norm_nonneg g)

/-- L2 Cauchy--Schwarz for a vector field supported in a measurable set. -/
theorem u7_physical_supported_pairing_le
    {d : ℕ} (E : Set (Vec d)) (hE : MeasurableSet E)
    (F G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ j, ∀ᵐ x ∂volume, x ∉ E → F j x = 0) :
    ‖∑ j, ∫ x, F j x * G j x‖ ≤
      Real.sqrt (∑ j, ‖F j‖ ^ 2) *
      Real.sqrt (∑ j, ((eLpNorm (E.indicator (fun x => G j x)) 2 volume).toReal) ^ 2) := by
  let H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) := fun j =>
    ((Lp.memLp (G j)).indicator hE).toLp (E.indicator (fun x => G j x))
  have heq (j : Fin d) : (∫ x, F j x * G j x) = ∫ x, F j x * H j x := by
    apply integral_congr_ae
    filter_upwards [hF j, ((Lp.memLp (G j)).indicator hE).coeFn_toLp] with x hx hh
    rw [hh]
    by_cases h : x ∈ E
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h, hx h]
  have hnorm (j : Fin d) : ‖H j‖ =
      (eLpNorm (E.indicator (fun x => G j x)) 2 volume).toReal := by
    simp only [H, Lp.norm_toLp]
  calc
    _ ≤ ∑ j, ‖∫ x, F j x * G j x‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖F j‖ * ‖H j‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [heq j, ← inner_complexL2Conjugation_eq_integral_mul]
      simpa only [norm_complexL2Conjugation] using
        norm_inner_le_norm (complexL2Conjugation volume (F j)) (H j)
    _ ≤ Real.sqrt (∑ j, ‖F j‖ ^ 2) * Real.sqrt (∑ j, ‖H j‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = _ := by simp only [hnorm]

private theorem u7_cancel_nonneg {a b : ℝ} (hb : 0 ≤ b)
    (h : a * a ≤ b * a) : a ≤ b := by
  by_cases ha : a ≤ 0
  · exact ha.trans hb
  · nlinarith

/-- The actual evolved divergence has a Gaussian off-diagonal L2 bound. -/
theorem u7_physical_evolved_divergence_offdiagonal
    (d : ℕ) (_hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ)
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
    ∀ (s : ℝ), 0 < s → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ F : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j, ∀ᵐ x ∂volume, euclideanNorm (x-z) < ρ → F j x = 0) →
      (eLpNorm ({x : Vec d | euclideanNorm (x-z) < ρ/2}.indicator
        (fun x => u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s F x))
        2 volume).toReal ≤
      C * ((Real.sqrt s)⁻¹ + ‖ζ‖) * Real.exp (C * ‖ζ‖^2 * s - c * ρ^2/s) *
        Real.sqrt (∑ j, ‖F j‖^2) := by
  obtain ⟨C, c, hC, hc, htail⟩ := u7_physical_transpose_gradient_offdiagonal d Λ hΛ
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω M hell hsmooth i ζ P Pdag hP hPdag s hs z ρ hρ F hF
  let E : Set (Vec d) := {x | ρ ≤ euclideanNorm (x-z)}
  let B : Set (Vec d) := {x | euclideanNorm (x-z) < ρ/2}
  have hn : Continuous (fun x : Vec d => euclideanNorm (x-z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hE : MeasurableSet E := (isClosed_le continuous_const hn).measurableSet
  have hB : MeasurableSet B := (isOpen_lt hn continuous_const).measurableSet
  let U := u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s F
  let hV : MemLp (B.indicator (fun x => U x)) 2 volume := (Lp.memLp U).indicator hB
  let V := hV.toLp (B.indicator (fun x => U x))
  let g := complexL2Conjugation volume V
  have hg : ∀ᵐ x ∂volume, ρ/2 ≤ euclideanNorm (x-z) → g x = 0 := by
    filter_upwards [hV.coeFn_toLp, Lp.coeFn_star V] with x hv hgx hx
    have hxB : x ∉ B := not_lt.mpr hx
    change (star V) x = star (V x) at hgx
    change (complexL2Conjugation volume V) x = 0
    rw [complexL2Conjugation_apply, hgx, hv, Set.indicator_of_notMem hxB]
    simp
  obtain ⟨T, hT, hp⟩ := u7_physical_evolved_divergence_pairing hΛ hell hsmooth hP hPdag hs
  obtain ⟨G, hG, hbound⟩ := htail ω hell i ζ P Pdag hPdag s.toNNReal
    (Real.toNNReal_pos.mpr hs) z ρ hρ g hg
  have hTG : T g = G := physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ (hT g) hG
  have hF' : ∀ j, ∀ᵐ x ∂volume, x ∉ E → F j x = 0 := by
    intro j
    filter_upwards [hF j] with x hx hxE
    exact hx (lt_of_not_ge hxE)
  have hpair := u7_physical_supported_pairing_le E hE F G hF'
  have heq : (∫ x, U x * g x) = ∫ x, V x * g x := by
    apply integral_congr_ae
    filter_upwards [hV.coeFn_toLp, Lp.coeFn_star V] with x hv hgx
    change (star V) x = star (V x) at hgx
    by_cases hx : x ∈ B
    · rw [hv, Set.indicator_of_mem hx]
    · have hv0 : V x = 0 := by rw [hv, Set.indicator_of_notMem hx]
      change U x * (complexL2Conjugation volume V) x = _
      rw [complexL2Conjugation_apply, hgx, hv0]
      simp
  have hself : ‖∫ x, U x * g x‖ = ‖V‖ ^ 2 := by
    rw [heq, ← inner_complexL2Conjugation_eq_integral_mul]
    change ‖inner ℂ (complexL2Conjugation volume V) (complexL2Conjugation volume V)‖ = _
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm,
      norm_complexL2Conjugation]
  have hmain : ‖V‖ ^ 2 ≤ Real.sqrt (∑ j, ‖F j‖ ^ 2) *
      (C * ((Real.sqrt s)⁻¹ + ‖ζ‖) * Real.exp (C * ‖ζ‖^2*s-c*ρ^2/s) * ‖V‖) := by
    have hp' := hp F g
    change (∫ x, U x * g x) = _ at hp'
    rw [hTG] at hp'
    have hh : ‖V‖ ^ 2 ≤ Real.sqrt (∑ j, ‖F j‖ ^ 2) *
        Real.sqrt (∑ j, ((eLpNorm (E.indicator (fun x => G j x)) 2 volume).toReal) ^ 2) := by
      rw [← hself, hp', norm_neg]
      exact hpair
    have hb : Real.sqrt (∑ j, ((eLpNorm (E.indicator (fun x => G j x)) 2 volume).toReal) ^ 2) ≤
        C * ((Real.sqrt s)⁻¹ + ‖ζ‖) * Real.exp (C * ‖ζ‖^2*s-c*ρ^2/s) * ‖V‖ := by
      simpa only [Real.coe_toNNReal _ hs.le, g, norm_complexL2Conjugation, E] using hbound
    exact hh.trans (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _))
  have hvnorm : ‖V‖ = (eLpNorm (B.indicator (fun x => U x)) 2 volume).toReal := by
    exact Lp.norm_toLp _ _
  rw [← hvnorm]
  have hmain' : ‖V‖ * ‖V‖ ≤
      (C * ((Real.sqrt s)⁻¹ + ‖ζ‖) * Real.exp (C * ‖ζ‖^2*s-c*ρ^2/s) *
        Real.sqrt (∑ j, ‖F j‖^2)) * ‖V‖ := by
    calc
      _ ≤ Real.sqrt (∑ j, ‖F j‖^2) *
          (C * ((Real.sqrt s)⁻¹ + ‖ζ‖) * Real.exp (C * ‖ζ‖^2*s-c*ρ^2/s) * ‖V‖) := by
        simpa only [pow_two] using hmain
      _ = _ := by ring
  apply u7_cancel_nonneg _ hmain'
  exact mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hC)
    (add_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg s)) (norm_nonneg ζ)))
    (Real.exp_pos _).le) (Real.sqrt_nonneg _)

/-- Restriction of an L2 function to the inner Euclidean ball. -/
noncomputable def u7DivergenceBallRestriction {d : ℕ} (z : Vec d) (ρ : ℝ)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) : Lp ℂ 2 (volume : Measure (Vec d)) :=
  ((Lp.memLp u).indicator (show MeasurableSet {x : Vec d | euclideanNorm (x-z) < ρ/2} by
    have hn : Continuous (fun x : Vec d => euclideanNorm (x-z)) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact (isOpen_lt hn continuous_const).measurableSet)).toLp
      ({x : Vec d | euclideanNorm (x-z) < ρ/2}.indicator (fun x => u x))

/-- The norm of the restriction is the localized L2 norm. -/
theorem u7_divergenceBallRestriction_norm {d : ℕ} (z : Vec d) (ρ : ℝ)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖u7DivergenceBallRestriction z ρ u‖ =
      (eLpNorm ({x : Vec d | euclideanNorm (x-z) < ρ/2}.indicator
        (fun x => u x)) 2 volume).toReal := by
  exact Lp.norm_toLp _ _

/-- Restriction to the ball does not increase the L2 norm. -/
theorem u7_divergenceBallRestriction_norm_le {d : ℕ} (z : Vec d) (ρ : ℝ)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖u7DivergenceBallRestriction z ρ u‖ ≤ ‖u‖ := by
  rw [u7_divergenceBallRestriction_norm, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.memLp u).eLpNorm_ne_top
  apply eLpNorm_indicator_le
  have hn : Continuous (fun x : Vec d => euclideanNorm (x-z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  exact (isOpen_lt hn continuous_const).measurableSet

/-- Restriction is a contraction on L2. -/
theorem u7_divergenceBallRestriction_dist_le {d : ℕ} (z : Vec d) (ρ : ℝ)
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    dist (u7DivergenceBallRestriction z ρ u) (u7DivergenceBallRestriction z ρ v) ≤
      dist u v := by
  let B : Set (Vec d) := {x | euclideanNorm (x-z) < ρ/2}
  have hB : MeasurableSet B := by
    have hn : Continuous (fun x : Vec d => euclideanNorm (x-z)) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact (isOpen_lt hn continuous_const).measurableSet
  have he : u7DivergenceBallRestriction z ρ (u-v) =
      u7DivergenceBallRestriction z ρ u - u7DivergenceBallRestriction z ρ v := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (u-v)).indicator hB).coeFn_toLp,
      ((Lp.memLp u).indicator hB).coeFn_toLp,
      ((Lp.memLp v).indicator hB).coeFn_toLp, Lp.coeFn_sub u v,
      Lp.coeFn_sub (u7DivergenceBallRestriction z ρ u)
        (u7DivergenceBallRestriction z ρ v)] with x huv hu hv hsub hsub'
    change (u7DivergenceBallRestriction z ρ (u-v)) x = B.indicator (fun x => (u-v) x) x at huv
    change (u7DivergenceBallRestriction z ρ u) x = B.indicator (fun x => u x) x at hu
    change (u7DivergenceBallRestriction z ρ v) x = B.indicator (fun x => v x) x at hv
    rw [hsub', huv]
    change _ = (u7DivergenceBallRestriction z ρ u) x - (u7DivergenceBallRestriction z ρ v) x
    rw [hu, hv]
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx, hsub, Pi.sub_apply]
    · simp only [Set.indicator_of_notMem hx, sub_self]
  rw [dist_eq_norm, dist_eq_norm, ← he]
  exact u7_divergenceBallRestriction_norm_le z ρ (u-v)

/-- The ball restriction is continuous in L2. -/
theorem u7_divergenceBallRestriction_continuous {d : ℕ} (z : Vec d) (ρ : ℝ) :
    Continuous (u7DivergenceBallRestriction (d := d) z ρ) := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro u v
  simpa using u7_divergenceBallRestriction_dist_le z ρ u v

/-- Positive-time divergence evolution intertwines with the forward semigroup. -/
theorem u7_physical_evolved_divergence_semigroup
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (a b : ℝ≥0) (hb : 0 < b)
    (F : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag (a+b : ℝ≥0) F =
      P a (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag b F) := by
  have hb' : 0 < (b : ℝ) := NNReal.coe_pos.mpr hb
  have hab : 0 < ((a+b : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (add_pos_of_nonneg_of_pos (bot_le : 0 ≤ a) hb)
  obtain ⟨T, hT, hp⟩ := u7_physical_evolved_divergence_pairing hΛ hell hsmooth hP hPdag hab
  obtain ⟨S, hS, hq⟩ := u7_physical_evolved_divergence_pairing hΛ hell hsmooth hP hPdag hb'
  have hconv (x : ℝ≥0) : (x : ℝ).toNNReal = x := by simp
  apply (Function.LeftInverse.injective (show Function.LeftInverse
    (complexL2Conjugation volume) (complexL2Conjugation volume) from fun f => by
      simp [complexL2Conjugation_apply]))
  apply ext_inner_right ℂ
  intro g
  rw [inner_complexL2Conjugation_eq_integral_mul, inner_complexL2Conjugation_eq_integral_mul,
    hp F g, hPdag.2.2.2.2 a _ g, hq F (Pdag a g)]
  have hg : T g = S (Pdag a g) := by
    apply physicalH1Graph_gradient_unique volume (Or.inl rfl) (Pdag (a+b) g)
    · simpa only [hconv] using hT g
    · have hs := hS (Pdag a g)
      simp only [hconv] at hs
      have hv : Pdag (a+b) g = Pdag b (Pdag a g) := by
        rw [add_comm a b, hPdag.2.1]
        rfl
      rw [hv]
      exact hs
  rw [hg]

/-- The evolved divergence is strongly continuous at every positive time. -/
theorem u7_physical_evolved_divergence_continuousOn
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (F : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    ContinuousOn (fun s : ℝ => u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s F)
      (Set.Ioi 0) := by
  intro s hs
  have hs0 : 0 < s := hs
  have hb : 0 < s / 2 := by linarith
  let U := u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag
  have hc : Continuous (fun r : ℝ => P (r - s / 2).toNNReal (U (s / 2) F)) :=
    (hP.2.2.1 _).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have he : (fun r : ℝ => U r F) =ᶠ[𝓝 s]
      (fun r : ℝ => P (r - s / 2).toNNReal (U (s / 2) F)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show s / 2 < s by linarith)] with r hr
    have hr0 : 0 ≤ r - s / 2 := sub_nonneg.mpr hr.le
    have hsum : (((r - s / 2).toNNReal + (s / 2).toNNReal : ℝ≥0) : ℝ) = r := by
      simp only [NNReal.coe_add, Real.coe_toNNReal _ hr0, Real.coe_toNNReal _ hb.le]
      ring
    simpa only [hsum, Real.coe_toNNReal _ hb.le, U] using
      u7_physical_evolved_divergence_semigroup hΛ hell hsmooth hP hPdag
        (r - s / 2).toNNReal (s / 2).toNNReal (Real.toNNReal_pos.mpr hb) F
  exact (hc.continuousAt.congr_of_eventuallyEq he).continuousWithinAt

/-- Time integration of the actual localized divergence retains the Gaussian tail. -/
theorem u7_physical_evolved_divergence_local_time_integral
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ)
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
    ∀ (t : ℝ), 0 < t → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ F : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j, ∀ᵐ x ∂volume, euclideanNorm (x-z) < ρ → F j x = 0) →
      let v : ℝ → Lp ℂ 2 (volume : Measure (Vec d)) := fun s =>
        u7DivergenceBallRestriction z ρ
          (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s F)
      IntegrableOn v (Set.Ioo 0 t) ∧
      ‖∫ s in Set.Ioo 0 t, v s‖ ≤
        C * (Real.sqrt t + ‖ζ‖ * t) *
          Real.exp (C * ‖ζ‖^2 * t - c * ρ^2/t) * Real.sqrt (∑ j, ‖F j‖^2) := by
  obtain ⟨C, c, hC, hc, htail⟩ :=
    u7_physical_evolved_divergence_offdiagonal d hd Λ hΛ
  refine ⟨2*C, c, by linarith, hc, ?_⟩
  intro ω M hell hsmooth i ζ P Pdag hP hPdag t ht z ρ hρ F hF v
  let A := Real.sqrt (∑ j, ‖F j‖^2)
  let E := Real.exp (C * ‖ζ‖^2*t - c*ρ^2/t)
  let K := C * E * A
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by linarith) hE) hA
  have hv : ContinuousOn v (Set.Ioo 0 t) := by
    apply (u7_divergenceBallRestriction_continuous z ρ).comp_continuousOn
    exact (u7_physical_evolved_divergence_continuousOn hΛ hell hsmooth hP hPdag F).mono
      (fun _ hs => hs.1)
  have hroot : IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹) (Set.Ioo 0 t) := by
    exact (intervalIntegrable_inv_sqrt ht.le).1.mono_set Set.Ioo_subset_Ioc_self
  have hconst : IntegrableOn (fun _ : ℝ => ‖ζ‖) (Set.Ioo 0 t) := by
    exact (intervalIntegrable_const).1.mono_set Set.Ioo_subset_Ioc_self
  have hmajor : IntegrableOn (fun s : ℝ => K * ((Real.sqrt s)⁻¹ + ‖ζ‖))
      (Set.Ioo 0 t) := (hroot.add hconst).const_mul K
  have hbound : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ‖v s‖ ≤ K * ((Real.sqrt s)⁻¹ + ‖ζ‖) := by
    intro s hs
    have hexp : Real.exp (C * ‖ζ‖^2*s - c*ρ^2/s) ≤ E := by
      apply Real.exp_le_exp.mpr
      have htime := mul_le_mul_of_nonneg_left hs.2.le
        (mul_nonneg (by linarith : 0 ≤ C) (sq_nonneg ‖ζ‖))
      have hspace := div_le_div_of_nonneg_left (mul_nonneg hc.le (sq_nonneg ρ)) hs.1 hs.2.le
      exact sub_le_sub htime hspace
    have hp := htail ω M hell hsmooth i ζ P Pdag hP hPdag s hs.1 z ρ hρ F hF
    change ‖u7DivergenceBallRestriction z ρ
      (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s F)‖ ≤ _
    rw [u7_divergenceBallRestriction_norm]
    calc
      _ ≤ C * ((Real.sqrt s)⁻¹ + ‖ζ‖) *
          Real.exp (C * ‖ζ‖^2*s-c*ρ^2/s) * A := hp
      _ ≤ C * ((Real.sqrt s)⁻¹ + ‖ζ‖) * E * A := by
        gcongr
      _ = K * ((Real.sqrt s)⁻¹ + ‖ζ‖) := by dsimp [K]; ring
  have hvi : IntegrableOn v (Set.Ioo 0 t) := by
    apply hmajor.mono'
    · have : SecondCountableTopologyEither ℝ (Lp ℂ 2 (volume : Measure (Vec d))) :=
        secondCountableTopologyEither_of_left ℝ _
      exact hv.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hbound s hs
  refine ⟨hvi, ?_⟩
  have hint : (∫ s in Set.Ioo (0 : ℝ) t, K * ((Real.sqrt s)⁻¹ + ‖ζ‖)) =
      K * (2 * Real.sqrt t + ‖ζ‖ * t) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (intervalIntegrable_inv_sqrt ht.le) intervalIntegrable_const,
      integral_inv_sqrt ht.le]
    all_goals (simp; ring)
    all_goals exact Or.inl trivial
  calc
    ‖∫ s in Set.Ioo 0 t, v s‖ ≤ ∫ s in Set.Ioo 0 t, ‖v s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Set.Ioo 0 t, K * ((Real.sqrt s)⁻¹ + ‖ζ‖) := by
      apply integral_mono_ae hvi.norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hbound s hs
    _ = K * (2 * Real.sqrt t + ‖ζ‖ * t) := hint
    _ ≤ (2*C) * (Real.sqrt t + ‖ζ‖ * t) *
        Real.exp ((2*C) * ‖ζ‖^2*t-c*ρ^2/t) * A := by
      have he : E ≤ Real.exp ((2*C) * ‖ζ‖^2*t-c*ρ^2/t) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ C * ‖ζ‖^2 * t := by positivity
        linarith
      dsimp [K]
      have hsqrt := Real.sqrt_nonneg t
      have hz : 0 ≤ ‖ζ‖ * t := mul_nonneg (norm_nonneg ζ) ht.le
      have hCE : 0 ≤ C * E * A := mul_nonneg (mul_nonneg (by linarith) hE) hA
      calc
        C * E * A * (2 * Real.sqrt t + ‖ζ‖ * t) ≤
            C * E * A * (2 * (Real.sqrt t + ‖ζ‖ * t)) := by gcongr; linarith
        _ ≤ C * Real.exp ((2*C) * ‖ζ‖^2*t-c*ρ^2/t) * A *
            (2 * (Real.sqrt t + ‖ζ‖ * t)) := by gcongr
        _ = _ := by ring


/-- Joint strong continuity of the actual physical semigroup. -/
theorem u7_physical_semigroup_joint_continuous
    {d : ℕ} {Λ : ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P) :
    Continuous (fun tf : ℝ≥0 × Lp ℂ 2 (volume : Measure (Vec d)) => P tf.1 tf.2) := by
  let k : ℝ := 5 * Λ ^ 3 * ‖ζ‖ ^ 2
  apply continuous_family_of_dense_exp_envelope P (fun t => k * (t : ℝ))
    (continuous_const.mul NNReal.continuous_coe) Set.univ dense_univ
  · intro f _
    exact hP.2.2.1 f
  · intro t
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    intro f
    have h := s5_weighted_forward (s5Elliptic_of_isElliptic hΛ hell)
      (fun j l => (ω.1.continuous.matrix_elem j l).measurable) i ζ hP t 0
      (ψ := fun _ => 0) (by intro x y; simpa only [sub_self, abs_zero] using (show 0 ≤ euclideanNorm (x-y) from Real.sqrt_nonneg _)) f (by simpa using Lp.memLp f)
    simpa only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul, zero_pow (by decide : (2 : ℕ) ≠ 0),
      add_zero, ← Lp.norm_def, k] using h.2

/-- The divergence evolution is jointly continuous for continuous time-dependent data. -/
theorem u7_physical_evolved_divergence_continuousOn_time_data
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (t : ℝ) (F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ j, ContinuousOn (fun s => F s j) (Set.Icc 0 t)) :
    ContinuousOn (fun s : ℝ => u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))
      (Set.Ioo 0 t) := by
  have hf : ContinuousOn F (Set.Ioo 0 t) :=
    (continuousOn_pi.mpr hF).mono (fun _ hs => ⟨hs.1.le, hs.2.le⟩)
  intro s hs
  have hb : 0 < s / 2 := by linarith [hs.1]
  let L := (Blueprint.c7_physical_evolved_divergence hΛ hell hsmooth hP hPdag
    (s / 2).toNNReal (Real.toNNReal_pos.mpr hb)).choose_spec.choose
  have hL : ∀ G, L G = u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag (s / 2) G := by
    intro G
    simp only [u7PhysicalEvolvedDivergence, dite_eq_left hb, L]
  have hc : ContinuousOn (fun r : ℝ => P (r - s / 2).toNNReal (L (F r))) (Set.Ioo 0 t) := by
    exact (u7_physical_semigroup_joint_continuous hΛ hell hP).comp_continuousOn
      (((continuous_real_toNNReal.comp (continuous_id.sub continuous_const)).continuousOn).prodMk
        (L.continuous.comp_continuousOn hf))
  apply (hc s hs).congr_of_eventuallyEq_of_mem ?_ hs
  filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show s / 2 < s by linarith))] with r hr
  have hr0 : 0 ≤ r - s / 2 := sub_nonneg.mpr hr.le
  have hsum : (((r - s / 2).toNNReal + (s / 2).toNNReal : ℝ≥0) : ℝ) = r := by
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hr0, Real.coe_toNNReal _ hb.le]
    ring
  rw [hL]
  simpa only [hsum, Real.coe_toNNReal _ hb.le] using
    (u7_physical_evolved_divergence_semigroup hΛ hell hsmooth hP hPdag
      (r - s / 2).toNNReal (s / 2).toNNReal (Real.toNNReal_pos.mpr hb) (F r))

/-- The divergence evolution is jointly continuous for continuous time-dependent data. -/
theorem u7_physical_evolved_divergence_continuousOn_open_time_data
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (t : ℝ) (F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ j, ContinuousOn (fun s => F s j) (Set.Ioo 0 t)) :
    ContinuousOn (fun s : ℝ => u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))
      (Set.Ioo 0 t) := by
  have hf : ContinuousOn F (Set.Ioo 0 t) := continuousOn_pi.mpr hF
  intro s hs
  have hb : 0 < s / 2 := by linarith [hs.1]
  let L := (Blueprint.c7_physical_evolved_divergence hΛ hell hsmooth hP hPdag
    (s / 2).toNNReal (Real.toNNReal_pos.mpr hb)).choose_spec.choose
  have hL : ∀ G, L G = u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag (s / 2) G := by
    intro G
    simp only [u7PhysicalEvolvedDivergence, dite_eq_left hb, L]
  have hc : ContinuousOn (fun r : ℝ => P (r - s / 2).toNNReal (L (F r))) (Set.Ioo 0 t) := by
    exact (u7_physical_semigroup_joint_continuous hΛ hell hP).comp_continuousOn
      (((continuous_real_toNNReal.comp (continuous_id.sub continuous_const)).continuousOn).prodMk
        (L.continuous.comp_continuousOn hf))
  apply (hc s hs).congr_of_eventuallyEq_of_mem ?_ hs
  filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show s / 2 < s by linarith))] with r hr
  have hr0 : 0 ≤ r - s / 2 := sub_nonneg.mpr hr.le
  have hsum : (((r - s / 2).toNNReal + (s / 2).toNNReal : ℝ≥0) : ℝ) = r := by
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hr0, Real.coe_toNNReal _ hb.le]
    ring
  rw [hL]
  simpa only [hsum, Real.coe_toNNReal _ hb.le] using
    (u7_physical_evolved_divergence_semigroup hΛ hell hsmooth hP hPdag
      (r - s / 2).toNNReal (s / 2).toNNReal (Real.toNNReal_pos.mpr hb) (F r))

/-- A continuous time-dependent supported vector field obeys the same localized integral bound. -/
theorem u7_physical_time_dependent_divergence_local_integral
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ)
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
    ∀ (t : ℝ), 0 < t → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j, ContinuousOn (fun s => F s j) (Set.Icc 0 t)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ s ∈ Set.Icc 0 t, Real.sqrt (∑ j, ‖F s j‖^2) ≤ B) →
      (∀ s ∈ Set.Icc 0 t, ∀ j, ∀ᵐ x ∂volume, euclideanNorm (x-z) < ρ → F s j x = 0) →
      let v : ℝ → Lp ℂ 2 (volume : Measure (Vec d)) := fun s =>
        u7DivergenceBallRestriction z ρ
          (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))
      IntegrableOn v (Set.Ioo 0 t) ∧
      ‖∫ s in Set.Ioo 0 t, v s‖ ≤
        C * (Real.sqrt t + ‖ζ‖ * t) *
          Real.exp (C * ‖ζ‖^2 * t - c * ρ^2/t) * B := by
  obtain ⟨C, c, hC, hc, htail⟩ :=
    u7_physical_evolved_divergence_offdiagonal d hd Λ hΛ
  refine ⟨2*C, c, by linarith, hc, ?_⟩
  intro ω M hell hsmooth i ζ P Pdag hP hPdag t ht z ρ hρ F hF B hB hFb hFs v
  let A := B
  let E := Real.exp (C * ‖ζ‖^2*t - c*ρ^2/t)
  let K := C * E * A
  have hA : 0 ≤ A := hB
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by linarith) hE) hA
  have hv : ContinuousOn v (Set.Ioo 0 t) := by
    apply (u7_divergenceBallRestriction_continuous z ρ).comp_continuousOn
    exact u7_physical_evolved_divergence_continuousOn_time_data hΛ hell hsmooth hP hPdag t F hF
  have hroot : IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹) (Set.Ioo 0 t) := by
    exact (intervalIntegrable_inv_sqrt ht.le).1.mono_set Set.Ioo_subset_Ioc_self
  have hconst : IntegrableOn (fun _ : ℝ => ‖ζ‖) (Set.Ioo 0 t) := by
    exact (intervalIntegrable_const).1.mono_set Set.Ioo_subset_Ioc_self
  have hmajor : IntegrableOn (fun s : ℝ => K * ((Real.sqrt s)⁻¹ + ‖ζ‖))
      (Set.Ioo 0 t) := (hroot.add hconst).const_mul K
  have hbound : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ‖v s‖ ≤ K * ((Real.sqrt s)⁻¹ + ‖ζ‖) := by
    intro s hs
    have hexp : Real.exp (C * ‖ζ‖^2*s - c*ρ^2/s) ≤ E := by
      apply Real.exp_le_exp.mpr
      have htime := mul_le_mul_of_nonneg_left hs.2.le
        (mul_nonneg (by linarith : 0 ≤ C) (sq_nonneg ‖ζ‖))
      have hspace := div_le_div_of_nonneg_left (mul_nonneg hc.le (sq_nonneg ρ)) hs.1 hs.2.le
      exact sub_le_sub htime hspace
    have hp := htail ω M hell hsmooth i ζ P Pdag hP hPdag s hs.1 z ρ hρ (F s) (hFs s ⟨hs.1.le, hs.2.le⟩)
    change ‖u7DivergenceBallRestriction z ρ
      (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))‖ ≤ _
    rw [u7_divergenceBallRestriction_norm]
    calc
      _ ≤ C * ((Real.sqrt s)⁻¹ + ‖ζ‖) *
          Real.exp (C * ‖ζ‖^2*s-c*ρ^2/s) * Real.sqrt (∑ j, ‖F s j‖^2) := hp
      _ ≤ C * ((Real.sqrt s)⁻¹ + ‖ζ‖) * E * A := by
        gcongr
        exact hFb s ⟨hs.1.le, hs.2.le⟩
      _ = K * ((Real.sqrt s)⁻¹ + ‖ζ‖) := by dsimp [K]; ring
  have hvi : IntegrableOn v (Set.Ioo 0 t) := by
    apply hmajor.mono'
    · have : SecondCountableTopologyEither ℝ (Lp ℂ 2 (volume : Measure (Vec d))) :=
        secondCountableTopologyEither_of_left ℝ _
      exact hv.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hbound s hs
  refine ⟨hvi, ?_⟩
  have hint : (∫ s in Set.Ioo (0 : ℝ) t, K * ((Real.sqrt s)⁻¹ + ‖ζ‖)) =
      K * (2 * Real.sqrt t + ‖ζ‖ * t) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (intervalIntegrable_inv_sqrt ht.le) intervalIntegrable_const,
      integral_inv_sqrt ht.le]
    all_goals (simp; ring)
    all_goals exact Or.inl trivial
  calc
    ‖∫ s in Set.Ioo 0 t, v s‖ ≤ ∫ s in Set.Ioo 0 t, ‖v s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Set.Ioo 0 t, K * ((Real.sqrt s)⁻¹ + ‖ζ‖) := by
      apply integral_mono_ae hvi.norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hbound s hs
    _ = K * (2 * Real.sqrt t + ‖ζ‖ * t) := hint
    _ ≤ (2*C) * (Real.sqrt t + ‖ζ‖ * t) *
        Real.exp ((2*C) * ‖ζ‖^2*t-c*ρ^2/t) * A := by
      have he : E ≤ Real.exp ((2*C) * ‖ζ‖^2*t-c*ρ^2/t) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ C * ‖ζ‖^2 * t := by positivity
        linarith
      dsimp [K]
      have hsqrt := Real.sqrt_nonneg t
      have hz : 0 ≤ ‖ζ‖ * t := mul_nonneg (norm_nonneg ζ) ht.le
      have hCE : 0 ≤ C * E * A := mul_nonneg (mul_nonneg (by linarith) hE) hA
      calc
        C * E * A * (2 * Real.sqrt t + ‖ζ‖ * t) ≤
            C * E * A * (2 * (Real.sqrt t + ‖ζ‖ * t)) := by gcongr; linarith
        _ ≤ C * Real.exp ((2*C) * ‖ζ‖^2*t-c*ρ^2/t) * A *
            (2 * (Real.sqrt t + ‖ζ‖ * t)) := by gcongr
        _ = _ := by ring


/-- Singular endpoint data retain the localized Gaussian divergence bound. -/
theorem u7_physical_singular_time_data_divergence_local_integral
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ)
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
    ∀ (t : ℝ), 0 < t → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j, ContinuousOn (fun s => F s j) (Set.Ioo 0 t)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ s ∈ Set.Ioo 0 t, Real.sqrt (∑ j, ‖F s j‖^2) ≤ (Real.sqrt (t-s))⁻¹ * B) →
      (∀ s ∈ Set.Ioo 0 t, ∀ j, ∀ᵐ x ∂volume, euclideanNorm (x-z) < ρ → F s j x = 0) →
      let v : ℝ → Lp ℂ 2 (volume : Measure (Vec d)) := fun s =>
        u7DivergenceBallRestriction z ρ
          (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))
      IntegrableOn v (Set.Ioo 0 t) ∧
      ‖∫ s in Set.Ioo 0 t, v s‖ ≤
        C * (1 + ‖ζ‖ * Real.sqrt t) *
          Real.exp (C * ‖ζ‖^2 * t - c * ρ^2/t) * B := by
  obtain ⟨C, c, hC, hc, htail⟩ := u7_physical_evolved_divergence_offdiagonal d hd Λ hΛ
  refine ⟨4*C, c, by linarith, hc, ?_⟩
  intro ω M hell hsmooth i ζ P Pdag hP hPdag t ht z ρ hρ F hF B hB hFb hFs v
  let E := Real.exp (C * ‖ζ‖^2*t - c*ρ^2/t)
  let K := C * E * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hv : ContinuousOn v (Set.Ioo 0 t) := by
    apply (u7_divergenceBallRestriction_continuous z ρ).comp_continuousOn
    exact u7_physical_evolved_divergence_continuousOn_open_time_data hΛ hell hsmooth hP hPdag t F hF
  have hi := intervalIntegrable_inv_sqrt_mul_inv_sqrt_sub ht
  have hj : IntervalIntegrable (fun s : ℝ => (Real.sqrt (t-s))⁻¹) volume 0 t := by
    simpa only [sub_zero, sub_self] using ((intervalIntegrable_inv_sqrt ht.le).comp_sub_left t).symm
  have hmajor : IntegrableOn (fun s : ℝ => K * ((Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹ + ‖ζ‖ * (Real.sqrt (t-s))⁻¹)) (Set.Ioo 0 t) := by
    exact ((hi.add (hj.const_mul ‖ζ‖)).const_mul K).1.mono_set Set.Ioo_subset_Ioc_self
  have hbound : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ‖v s‖ ≤ K * ((Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹ + ‖ζ‖ * (Real.sqrt (t-s))⁻¹) := by
    intro s hs
    have hexp : Real.exp (C * ‖ζ‖^2*s - c*ρ^2/s) ≤ E := by
      apply Real.exp_le_exp.mpr
      have htime := mul_le_mul_of_nonneg_left hs.2.le
        (mul_nonneg (by linarith : 0 ≤ C) (sq_nonneg ‖ζ‖))
      have hspace := div_le_div_of_nonneg_left (mul_nonneg hc.le (sq_nonneg ρ)) hs.1 hs.2.le
      exact sub_le_sub htime hspace
    have hp := htail ω M hell hsmooth i ζ P Pdag hP hPdag s hs.1 z ρ hρ (F s) (hFs s hs)
    change ‖u7DivergenceBallRestriction z ρ (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))‖ ≤ _
    rw [u7_divergenceBallRestriction_norm]
    calc
      _ ≤ C * ((Real.sqrt s)⁻¹ + ‖ζ‖) * Real.exp (C * ‖ζ‖^2*s-c*ρ^2/s) * Real.sqrt (∑ j, ‖F s j‖^2) := hp
      _ ≤ C * ((Real.sqrt s)⁻¹ + ‖ζ‖) * E * ((Real.sqrt (t-s))⁻¹ * B) := by
        gcongr
        exact hFb s hs
      _ = _ := by dsimp [K]; ring
  have hvi : IntegrableOn v (Set.Ioo 0 t) := by
    apply hmajor.mono'
    · have : SecondCountableTopologyEither ℝ (Lp ℂ 2 (volume : Measure (Vec d))) := secondCountableTopologyEither_of_left ℝ _
      exact hv.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hbound s hs
  refine ⟨hvi, ?_⟩
  have hjval : (∫ s in (0 : ℝ)..t, (Real.sqrt (t-s))⁻¹) = 2 * Real.sqrt t := by
    change (∫ s in (0 : ℝ)..t, (fun x => (Real.sqrt x)⁻¹) (t-s)) = _
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => (Real.sqrt x)⁻¹) t]
    simpa only [sub_self, sub_zero] using integral_inv_sqrt ht.le
  have hint : (∫ s in Set.Ioo (0 : ℝ) t, K * ((Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹ + ‖ζ‖ * (Real.sqrt (t-s))⁻¹)) ≤ K * (4 + ‖ζ‖ * (2 * Real.sqrt t)) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi (hj.const_mul ‖ζ‖),
      intervalIntegral.integral_const_mul, hjval]
    exact mul_le_mul_of_nonneg_left (add_le_add (integral_inv_sqrt_mul_inv_sqrt_sub_le ht) le_rfl) hK
  calc
    ‖∫ s in Set.Ioo 0 t, v s‖ ≤ ∫ s in Set.Ioo 0 t, ‖v s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Set.Ioo 0 t, K * ((Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹ + ‖ζ‖ * (Real.sqrt (t-s))⁻¹) := by
      apply integral_mono_ae hvi.norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hbound s hs
    _ ≤ K * (4 + ‖ζ‖ * (2 * Real.sqrt t)) := hint
    _ ≤ (4*C) * (1 + ‖ζ‖ * Real.sqrt t) * Real.exp ((4*C) * ‖ζ‖^2*t-c*ρ^2/t) * B := by
      have he : E ≤ Real.exp ((4*C) * ‖ζ‖^2*t-c*ρ^2/t) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ C * ‖ζ‖^2 * t := by positivity
        linarith
      have hz : 0 ≤ ‖ζ‖ * Real.sqrt t := mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg t)
      calc
        K * (4 + ‖ζ‖ * (2 * Real.sqrt t)) ≤ K * (4 * (1 + ‖ζ‖ * Real.sqrt t)) := by gcongr; linarith
        _ ≤ C * Real.exp ((4*C) * ‖ζ‖^2*t-c*ρ^2/t) * B * (4 * (1 + ‖ζ‖ * Real.sqrt t)) := by dsimp [K]; gcongr
        _ = _ := by ring

/-- The endpoint estimate in the form used by the Duhamel limit. -/
theorem u7_finish_physical_singular_time_data_divergence_local_integral
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ)
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
    ∀ (t : ℝ), 0 < t → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j, ContinuousOn (fun s => F s j) (Set.Ioo 0 t)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ s ∈ Set.Ioo 0 t, Real.sqrt (∑ j, ‖F s j‖^2) ≤ (Real.sqrt (t-s))⁻¹ * B) →
      (∀ s ∈ Set.Ioo 0 t, ∀ j, ∀ᵐ x ∂volume, euclideanNorm (x-z) < ρ → F s j x = 0) →
      let v : ℝ → Lp ℂ 2 (volume : Measure (Vec d)) := fun s =>
        u7DivergenceBallRestriction z ρ
          (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))
      IntegrableOn v (Set.Ioo 0 t) ∧
      ‖∫ s in Set.Ioo 0 t, v s‖ ≤
        C * (1 + ‖ζ‖ * Real.sqrt t) *
          Real.exp (C * ‖ζ‖^2 * t - c * ρ^2/t) * B :=
  u7_physical_singular_time_data_divergence_local_integral d hd Λ hΛ

/-- Integrals over intervals approaching both endpoints converge in the target norm. -/
theorem u7_integral_truncated_endpoints_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {t : ℝ} {v : ℝ → E} (hv : IntegrableOn v (Set.Ioo 0 t))
    {a b : ℕ → ℝ} (ha : Filter.Tendsto a Filter.atTop (nhds 0))
    (hb : Filter.Tendsto b Filter.atTop (nhds t))
    (hab : ∀ n, 0 ≤ a n ∧ b n ≤ t) :
    Filter.Tendsto (fun n => ∫ s in Set.Ioo (a n) (b n), v s) Filter.atTop
      (nhds (∫ s in Set.Ioo 0 t, v s)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 t)
  let F : ℕ → ℝ → E := fun n => (Set.Ioo (a n) (b n)).indicator v
  have hvμ : Integrable v μ := hv
  have hcover := aecover_Ioo_of_Ioo (μ := volume) ha hb
  have hmeas : ∀ n, AEStronglyMeasurable (F n) μ := fun n =>
    hv.aestronglyMeasurable.indicator measurableSet_Ioo
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖v x‖ := fun n =>
    ae_of_all _ fun x => norm_indicator_le_norm_self _ _
  have hF : ∀ n, Integrable (F n) μ := fun n =>
    hvμ.mono (hmeas n) (hbound n)
  have hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (v x)) :=
    hcover.ae_tendsto_indicator v
  have hnorm : Filter.Tendsto (fun n => ENNReal.toReal <|
      ∫⁻ x, ENNReal.ofReal ‖F n x - v x‖ ∂μ) Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_lintegral_norm_of_dominated_convergence hmeas hvμ.norm.hasFiniteIntegral hbound hlim)
  have hL1 : Filter.Tendsto (fun n => (hF n).toL1 (F n)) Filter.atTop
      (nhds (hvμ.toL1 v)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    convert! hnorm with n
    rw [L1.norm_def]
    congr 1
    refine lintegral_congr_ae ?_
    rw [← Integrable.toL1_sub]
    refine ((hF n).sub hvμ).coeFn_toL1.mono fun x hx => ?_
    dsimp only
    rw [hx, ofReal_norm, Pi.sub_apply]
  have h := L1.continuous_integral.tendsto (hvμ.toL1 v) |>.comp hL1
  have h' : Filter.Tendsto (fun n => ∫ x, F n x ∂μ) Filter.atTop
      (nhds (∫ x, v x ∂μ)) := by
    simpa only [Function.comp_def, integral_eq _ (hF _), integral_eq _ hvμ] using h
  apply h'.congr
  intro n
  have hsub : Set.Ioo (a n) (b n) ⊆ Set.Ioo (0 : ℝ) t := by
    intro x hx
    exact ⟨lt_of_le_of_lt (hab n).1 hx.1, lt_of_lt_of_le hx.2 (hab n).2⟩
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_left.mpr hsub]

/-- The truncated evolved-divergence integral converges under its explicit
integrability condition. -/
theorem u7_evolved_divergence_truncated_endpoints_tendsto
    {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ) (ω : FieldPair d) (M : ℕ → ℝ)
    (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (t : ℝ) (z : Vec d) (ρ : ℝ)
    (F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IntegrableOn (fun s => u7DivergenceBallRestriction z ρ
      (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))) (Set.Ioo 0 t))
    {a b : ℕ → ℝ} (ha : Filter.Tendsto a Filter.atTop (nhds 0))
    (hb : Filter.Tendsto b Filter.atTop (nhds t))
    (hab : ∀ n, 0 ≤ a n ∧ b n ≤ t) :
    Filter.Tendsto (fun n => ∫ s in Set.Ioo (a n) (b n),
      u7DivergenceBallRestriction z ρ
        (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s)))
      Filter.atTop (nhds (∫ s in Set.Ioo 0 t,
        u7DivergenceBallRestriction z ρ
          (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s)))) :=
  u7_integral_truncated_endpoints_tendsto hv ha hb hab


/-- The forward weak-form estimate retains part of its elliptic coercivity. -/
theorem u7_forward_pointwise_dissipation {Λ N B ρ q : ℝ}
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (hN : 0 ≤ N) (hB : B ≤ 2 * q * ρ) (hB0 : 0 ≤ B)
    (T1 T2 T3 u ζ : ℂ)
    (h1 : Λ⁻¹ * N ^ 2 ≤ T1.re)
    (h2 : ‖T2‖ ≤ 2 * Λ * B * N) (h3 : ‖T3‖ ≤ 2 * Λ * N) :
    (-(1 / 2 : ℂ) * ((ρ : ℂ) * T1 + (starRingEnd ℂ) u * T2) +
      ζ * (T3 * (ρ : ℂ) * (starRingEnd ℂ) u)).re +
      (Λ⁻¹ / 4) * ρ * N ^ 2 ≤
      (5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (ρ * ‖u‖ ^ 2) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hinv : (2 * Λ)⁻¹ = Λ⁻¹ / 2 := by
    simp only [mul_inv_rev, div_eq_mul_inv]
  have h1' : (2 * Λ)⁻¹ * N ^ 2 ≤
      (T1 - ((Λ⁻¹ * N ^ 2 / 2 : ℝ) : ℂ)).re := by
    rw [hinv]
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have h2' : ‖T2‖ ≤ 2 * (2 * Λ) * B * N := by
    nlinarith [mul_nonneg (mul_nonneg hΛ0 hB0) hN]
  have h3' : ‖T3‖ ≤ 2 * (2 * Λ) * N := by
    nlinarith [mul_nonneg hΛ0 hN]
  have h := s5_alg_forward (Λ := 2 * Λ) (by linarith) hρ hN hB
    (T1 - ((Λ⁻¹ * N ^ 2 / 2 : ℝ) : ℂ)) T2 T3 u ζ h1' h2' h3'
  have heq :
      (-(1 / 2 : ℂ) * ((ρ : ℂ) *
        (T1 - ((Λ⁻¹ * N ^ 2 / 2 : ℝ) : ℂ)) + (starRingEnd ℂ) u * T2) +
        ζ * (T3 * (ρ : ℂ) * (starRingEnd ℂ) u)).re =
      (-(1 / 2 : ℂ) * ((ρ : ℂ) * T1 + (starRingEnd ℂ) u * T2) +
        ζ * (T3 * (ρ : ℂ) * (starRingEnd ℂ) u)).re +
        (Λ⁻¹ / 4) * ρ * N ^ 2 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
      Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
    ring
  rw [heq] at h
  exact h

/-- Retained coercivity for the actual forward weak-form integrand. -/
theorem u7_forward_pointwise_integrand_dissipation {d : ℕ}
    {A : Fin d → Fin d → ℝ} {Λ : ℝ} (h : S5Elliptic A Λ)
    (X : Fin d → ℂ) (u : ℂ) (D : Fin d → ℝ) (ρ q : ℝ) (i : Fin d) (ζ : ℂ)
    (hρ : 0 ≤ ρ) (hD : s5Nrm D ≤ 2 * q * ρ) :
    (-(1 / 2 : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) +
      ζ * ((∑ j, (A j i : ℂ) * X j) * (ρ : ℂ) * (starRingEnd ℂ) u)).re +
      (Λ⁻¹ / 4) * ρ * s5CNrm X ^ 2 ≤
    (5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (ρ * ‖u‖ ^ 2) := by
  have hsplit : (∑ j, ∑ k, (A j k : ℂ) * X k *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) =
      (ρ : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)) +
        (starRingEnd ℂ) u * (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * X k) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  have hm : ∑ j, ‖X j‖ ^ 2 = s5CNrm X ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)).symm
  have h1 : Λ⁻¹ * s5CNrm X ^ 2 ≤
      (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)).re := by
    rw [← hm]
    exact s5_coercive h X
  exact u7_forward_pointwise_dissipation h.one_le hρ (s5CNrm_nonneg X) hD
    (s5Nrm_nonneg D) _ _ _ u ζ h1 (s5_cbil_norm_le h D X) (s5_row_norm_le h i X)

/-- Weighted forward generator energy with its physical gradient retained. -/
theorem u7_forward_energy_dissipation {d : ℕ} {a : Vec d → Mat d} {Λ B q : ℝ} {φ : Vec d → ℝ}
    (hell : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (hφ : S5Weight φ B q) (i : Fin d) (ζ : ℂ)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
    IsPhysicalH1Graph volume (Or.inl rfl) f G ∧
    (inner ℂ (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f)
        (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g)).re +
      (Λ⁻¹ / 4) * (∑ j, ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G j)‖ ^ 2) ≤
      (5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) *
        ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f‖ ^ 2 := by
  obtain ⟨Gf, hGf, hweak⟩ := hfg
  refine ⟨Gf, hGf, ?_⟩
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_mul_smooth (fun x => φ x * φ x)
    hφ.sq_smooth hφ.memLp_sq hφ.memLp_sq_deriv (star f) (fun j => star (Gf j))
    (s5_isPhysicalH1Graph_star f Gf hGf)
  have hid := hweak w J hw
  have hwr' : (w : Vec d → ℂ) =ᵐ[volume] fun x =>
      ((φ x * φ x : ℝ) : ℂ) * (starRingEnd ℂ) (f x) := by
    filter_upwards [hwr, Lp.coeFn_star f] with x h1 h2
    rw [h1, h2]
    try rfl
  have hin := s5_inner_eq hφ f g w hwr'
  have hbound : ∀ j k x, ‖((a x j k : ℝ) : ℂ)‖ ≤ Λ := fun j k x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hell x).entry_abs_le j k
  have hcm : ∀ j k, Measurable fun x => ((a x j k : ℝ) : ℂ) := fun j k =>
    Complex.measurable_ofReal.comp (hmeas j k)
  have hS1 : Integrable (fun x => ∑ j, ∑ k, ((a x j k : ℝ) : ℂ) * Gf k x * J j x) volume :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      s5_integrable_coef (hcm j k) (hbound j k) (Gf k) (J j)
  have hS2 : Integrable (fun x => (∑ j, ((a x j i : ℝ) : ℂ) * Gf j x) * w x) volume := by
    have e : (fun x => (∑ j, ((a x j i : ℝ) : ℂ) * Gf j x) * w x) =
        fun x => ∑ j, ((a x j i : ℝ) : ℂ) * Gf j x * w x := by
      funext x
      rw [Finset.sum_mul]
    rw [e]
    exact integrable_finsetSum _ fun j _ =>
      s5_integrable_coef (hcm j i) (hbound j i) (Gf j) w
  have hTint : Integrable (fun x => -(1 / 2 : ℂ) *
      (∑ j, ∑ k, ((a x j k : ℝ) : ℂ) * Gf k x * J j x) +
      ζ * ((∑ j, ((a x j i : ℝ) : ℂ) * Gf j x) * w x)) volume :=
    (hS1.const_mul _).add (hS2.const_mul _)
  have hint : ∫ x, g x * w x = ∫ x, (-(1 / 2 : ℂ) *
      (∑ j, ∑ k, ((a x j k : ℝ) : ℂ) * Gf k x * J j x) +
      ζ * ((∑ j, ((a x j i : ℝ) : ℂ) * Gf j x) * w x)) := by
    rw [hid, integral_add (hS1.const_mul _) (hS2.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hin, hint]
  refine c7_integrate_weighted_gradient_estimate hφ f Gf _
    (5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) (Λ⁻¹ / 4) hTint ?_
  have hJa : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, (J j : Vec d → ℂ) x =
      ((φ x * φ x : ℝ) : ℂ) * (starRingEnd ℂ) (Gf j x) +
        (starRingEnd ℂ) (f x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hJr j, Lp.coeFn_star (Gf j), Lp.coeFn_star f] with x h1 h2 h3
    rw [h1, h2, h3]
    try rfl
  have hGn : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j,
      ‖(s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (Gf j) : Lp ℂ 2 volume) x‖ ^ 2 =
        (φ x * φ x) * ‖Gf j x‖ ^ 2 := by
    rw [ae_all_iff]
    intro j
    exact s5_norm_sq_pt hφ (Gf j)
  filter_upwards [hJa, hwr', s5_norm_sq_pt hφ f, hGn] with x hJx hwx hnorm hGx
  have key := u7_forward_pointwise_integrand_dissipation (hell x) (fun k => Gf k x) (f x)
    (fun j => coordinateDerivative j (fun y => φ y * φ y) x) (φ x * φ x) q i ζ
    (mul_self_nonneg _) (hφ.sq_grad x)
  have hs : s5CNrm (fun k => Gf k x) ^ 2 = ∑ k, ‖Gf k x‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  simp only [hJx, hwx, hnorm, hGx, ← Finset.mul_sum, hs] at ⊢ key
  simpa only [mul_assoc] using key

/-- Integrated weighted physical gradient along the forward generator orbit. -/
theorem u7_forward_orbit_integrated_weighted_gradient
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ t : ℝ≥0,
        (Λ⁻¹ / 4) * (∫ s in (0 : ℝ)..(t : ℝ),
          ∑ j, ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G s j)‖ ^ 2) ≤
          (‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f‖ ^ 2 -
            ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (P t f)‖ ^ 2) / 2 +
          (5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) *
            (∫ s in (0 : ℝ)..(t : ℝ),
              ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (P s.toNNReal f)‖ ^ 2) := by
  have hsem : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  obtain ⟨G, hG, hGc⟩ := physical_generator_orbit_continuous_gradient a i ζ ha
    (by linarith : 0 < Λ) (Filter.Eventually.of_forall hell)
    (fun s : ℝ => P s.toNNReal f) (fun s : ℝ => P s.toNNReal g)
    ((hsem.cont f).comp continuous_real_toNNReal)
    ((hsem.cont g).comp continuous_real_toNNReal)
    (fun s => hsem.map_gen hfg s.toNNReal)
  refine ⟨G, hG, hGc, fun t => c7_integrated_weighted_gradient_energy hsem
    (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound) hfg G hGc
    (Λ⁻¹ / 4) (5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) ?_ t⟩
  intro s
  obtain ⟨H, hH, hc⟩ := u7_forward_energy_dissipation hell hmeas hφ i ζ
    (hsem.map_gen hfg s.toNNReal)
  have he := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (P s.toNNReal f) H (G s) hH (hG s)
  rw [he] at hc
  linarith only [hc]

/-- The forward weighted orbit has a uniform integrated L² bound. -/
theorem u7_forward_weighted_orbit_integral
    {d : ℕ} {a : Vec d → Mat d} {Λ B q : ℝ} {φ : Vec d → ℝ}
    (hΛ : 0 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (hφ : S5Weight φ B q) (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    (∫ s in (0 : ℝ)..(t : ℝ), ‖W (P s.toNNReal f)‖ ^ 2) ≤
      (t : ℝ) * (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2 := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hsem : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  have hc : Continuous (fun s : ℝ => ‖W (P s.toNNReal f)‖ ^ 2) :=
    ((W.continuous.comp ((hsem.cont f).comp continuous_real_toNNReal)).norm).pow 2
  have hp : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ),
      ‖W (P s.toNNReal f)‖ ^ 2 ≤ (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2 := by
    intro s hs
    have hg := s5_forward_growth hell hmeas hφ i ζ hP f s.toNNReal
    rw [← s5Mul_norm volume hφ.measurable hφ.B_nonneg hφ.bound,
      ← s5Mul_norm volume hφ.measurable hφ.B_nonneg hφ.bound] at hg
    have he : Real.exp (k * s) ≤ Real.exp (k * (t : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hk)
    have hs' : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs.1
    rw [hs'] at hg
    have hn := hg.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
    nlinarith [norm_nonneg (W (P s.toNNReal f)), Real.exp_pos (k * (t : ℝ)), norm_nonneg (W f)]
  have hci : IntervalIntegrable (fun s : ℝ => ‖W (P s.toNNReal f)‖ ^ 2)
      volume 0 (t : ℝ) := hc.intervalIntegrable _ _
  have hcst : IntervalIntegrable (fun _ : ℝ => (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2)
      volume 0 (t : ℝ) := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on t.property hci hcst hp
  simpa using h

/-- Explicit integrated weighted forward-gradient bound. -/
theorem u7_forward_orbit_integrated_weighted_gradient_explicit
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ t : ℝ≥0,
        (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖W (G s j)‖ ^ 2) ≤
          4 * Λ * (‖W f‖ ^ 2 / 2 + H * (t : ℝ) *
            (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2) := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  have hΛpos : 0 < Λ := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨G, hG, hGc, hbound⟩ :=
    u7_forward_orbit_integrated_weighted_gradient a i ζ ha hΛ hell hmeas hφ P hP hfg
  refine ⟨G, hG, hGc, fun t => ?_⟩
  have hi := u7_forward_weighted_orbit_integral (by linarith : 0 ≤ Λ)
    hell hmeas hφ i ζ P hP f t
  have hb := hbound t
  change (Λ⁻¹ / 4) * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖W (G s j)‖ ^ 2) ≤
    (‖W f‖ ^ 2 - ‖W (P t f)‖ ^ 2) / 2 + H *
      (∫ s in (0 : ℝ)..(t : ℝ), ‖W (P s.toNNReal f)‖ ^ 2) at hb
  change (∫ s in (0 : ℝ)..(t : ℝ), ‖W (P s.toNNReal f)‖ ^ 2) ≤
    (t : ℝ) * (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2 at hi
  have hc : (Λ⁻¹ / 4) * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖W (G s j)‖ ^ 2) ≤
      ‖W f‖ ^ 2 / 2 + H * ((t : ℝ) * (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hi hH, sq_nonneg ‖W (P t f)‖]
  have hd := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4 * Λ by positivity)
  have hinv : Λ * Λ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hΛpos)
  have hleft (x : ℝ) : 4 * Λ * (Λ⁻¹ / 4 * x) = x := by
    calc
      4 * Λ * (Λ⁻¹ / 4 * x) = (Λ * Λ⁻¹) * x := by ring
      _ = x := by rw [hinv, one_mul]
  rw [hleft] at hd
  change (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖W (G s j)‖ ^ 2) ≤
    4 * Λ * (‖W f‖ ^ 2 / 2 + H * (t : ℝ) *
      (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2)
  convert hd using 1; ring


/-- The weighted principal-energy derivative of the forward twice-domain orbit. -/
theorem u7_forward_D2_weighted_principal_energy_derivative
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexGeneratorPair a i ζ g h) :
    ∃ G H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal g) (H s)) ∧
      (∀ j, Continuous (fun s => H s j)) ∧
      ∀ s, HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G r k)) x *
          star ((s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G r j)) x)).re)
        (2 * (∫ x, ∑ j, ∑ k,
          (a x j k : ℂ) * (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G s k)) x *
            star ((s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (H s j)) x)).re) s := by
  obtain ⟨G, H, hG, hH, hder, hcont⟩ :=
    c18_physical_D2_orbit_gradient a i ζ ha hΛ hA P hP hfg hgh
  have hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j := by
    filter_upwards [hA] with x hx
    exact hx.symm
  exact ⟨G, H, hG, hH, hcont, fun s =>
    c7_weighted_principal_energy_hasDerivAt a ha hsym hφ G (H s) s (hder s)⟩

/-- The forward drift is controlled by weighted gradient and generator norms. -/
theorem u7_forward_weighted_force_column_norm_le {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (g : Lp ℂ 2 (volume : Measure (Vec d))) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    ‖ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) *
      (((φ x * φ x : ℝ) : ℂ) * star (g x)))‖ ≤
      (((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * (∑ j, ‖W (G j)‖ ^ 2) +
        (1 / 4 : ℝ) * ‖W g‖ ^ 2 := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  have he : (∫ x, (∑ j, (a x j i : ℂ) * G j x) *
        (((φ x * φ x : ℝ) : ℂ) * star (g x))) =
      ∫ x, (∑ j, (a x j i : ℂ) * W (G j) x) * star (W g x) := by
    apply integral_congr_ae
    filter_upwards [s5Mul_coe volume hφ.measurable hφ.B_nonneg hφ.bound g,
      ae_all_iff.mpr (fun j => s5Mul_coe volume hφ.measurable hφ.B_nonneg hφ.bound (G j))]
      with x hg hG
    simp only [W, hg, hG, star_mul, Complex.star_def, Complex.conj_ofReal,
      Complex.ofReal_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact c18_physical_force_column_norm_le a i ζ ha hΛ hA (fun j => W (G j)) (W g)

/-- The actual forward weak graph tested against the weighted generator image. -/
theorem u7_forward_weighted_generator_test {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q) :
    (∫ x, g x * (((φ x * φ x : ℝ) : ℂ) * star (g x))) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) +
      ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) *
        (((φ x * φ x : ℝ) : ℂ) * star (g x))) := by
  obtain ⟨K, hK, hwk⟩ := hug
  have hKG := physicalH1Graph_gradient_unique volume (Or.inl rfl) u K G hK hu
  rw [hKG] at hwk
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_mul_smooth (fun x => φ x * φ x)
    hφ.sq_smooth hφ.memLp_sq hφ.memLp_sq_deriv (star g) (fun j => star (H j))
    (s5_isPhysicalH1Graph_star g H hg)
  have ht := hwk w J hw
  have hl : (∫ x, g x * w x) =
      ∫ x, g x * (((φ x * φ x : ℝ) : ℂ) * star (g x)) := by
    apply integral_congr_ae
    filter_upwards [hwr, Lp.coeFn_star g] with x hwx hs
    rw [hwx, hs]
    rfl
  have hr : (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * J j x) =
      ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hJr, ae_all_iff.mpr (fun j => Lp.coeFn_star (H j)),
      Lp.coeFn_star g] with x hj hh hgx
    simp only [hj, hh, hgx, Pi.star_apply]
  have hf : (∫ x, (∑ j, (a x j i : ℂ) * G j x) * w x) =
      ∫ x, (∑ j, (a x j i : ℂ) * G j x) *
        (((φ x * φ x : ℝ) : ℂ) * star (g x)) := by
    apply integral_congr_ae
    filter_upwards [hwr, Lp.coeFn_star g] with x hwx hs
    rw [hwx, hs]
    rfl
  rwa [hl, hr, hf] at ht

/-- Testing the forward graph identifies the weighted generator energy. -/
theorem u7_forward_weighted_generator_norm {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q) :
    ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g‖ ^ 2 =
      (-(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) +
      ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) *
        (((φ x * φ x : ℝ) : ℂ) * star (g x)))).re := by
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_mul_smooth (fun x => φ x * φ x)
    hφ.sq_smooth hφ.memLp_sq hφ.memLp_sq_deriv (star g) (fun j => star (H j))
    (s5_isPhysicalH1Graph_star g H hg)
  have hwr' : (w : Vec d → ℂ) =ᵐ[volume] fun x =>
      ((φ x * φ x : ℝ) : ℂ) * (starRingEnd ℂ) (g x) := by
    filter_upwards [hwr, Lp.coeFn_star g] with x h1 h2
    rw [h1, h2]
    rfl
  have hi := s5_inner_eq hφ g g w hwr'
  have hl : (∫ x, g x * w x) =
      ∫ x, g x * (((φ x * φ x : ℝ) : ℂ) * star (g x)) := by
    apply integral_congr_ae
    filter_upwards [hwr'] with x hwx
    rw [hwx]
    rfl
  rw [hl, u7_forward_weighted_generator_test a i ζ hug G H hu hg hφ] at hi
  have hr := congrArg Complex.re hi
  have hn : (inner ℂ (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g)
      (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g)).re =
      ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa only [RCLike.re_eq_complex_re] using
      (RCLike.re_ofReal_pow (K := ℂ) ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g‖ 2)
  rwa [hn] at hr

/-- The weighted forward principal-energy cross term obeys a Davies bound. -/
theorem u7_forward_weighted_energy_cross_le {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ) {Λ : ℝ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * (W (G k)) x * star ((W (H j)) x)).re ≤
      ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
        2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * (∑ j, ‖W (G j)‖ ^ 2) := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  have hn := u7_forward_weighted_generator_norm a i ζ hug G H hu hg hφ
  have hf := u7_forward_weighted_force_column_norm_le a i ζ ha hΛ hA hφ G g
  have ht := c7_davies_shifted_energy_test_integral a ha hφ i (0 : ℂ) g G H
  have hc := c7_davies_shifted_energy_commutator_integral a ha hA hφ i (0 : ℂ) g G
  have hw := c7_davies_shifted_cross_weight_identity a i (0 : ℂ) u g G H hφ
  dsimp only at hw hc
  simp only [mul_zero, ite_self, sub_zero, star_zero, zero_mul,
    add_zero, norm_zero] at ht hc
  have hKzero (j : Fin d) :
      (if j = i then (0 : ℂ) • s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound else 0) =
        (0 : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume) := by
    by_cases h : j = i
    · simp only [h, ↓reduceIte]
      exact zero_smul ℂ (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound)
    · simp only [h, ↓reduceIte]
  simp only [mul_zero, hKzero, zero_apply, sub_zero,
    zero_smul, ite_self, zero_mul] at hw
  have hs (z : ℂ) : (-(1 / 2 : ℂ) * z).re = -(1 / 2 : ℝ) * z.re := by simp
  rw [Complex.add_re, hs] at hn
  have htr := congrArg Complex.re ht
  simp only [Complex.sub_re] at htr
  have hcr : -(∫ x, star (g x) * (∑ j, ∑ k, (a x j k : ℂ) * G k x *
      (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))).re ≤
      ‖∫ x, star (g x) * (∑ j, ∑ k, (a x j k : ℂ) * G k x *
        (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hfr := Complex.re_le_norm (ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) *
    (((φ x * φ x : ℝ) : ℂ) * star (g x))))
  dsimp only [W] at hf hc hw ⊢
  rw [hw]
  nlinarith only [hn, hf, hc, htr, hcr, hfr,
    sq_nonneg ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g‖]

/-- Positive-time weighted forward principal energy has a structural growth rate. -/
theorem u7_forward_D2_weighted_energy_derivative_le
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexGeneratorPair a i ζ g h) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let K := (1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
      2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      ∀ s, 0 < s → ∃ v : ℝ,
        HasDerivAt (fun r => (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
          (W (G r k)) x * star ((W (G r j)) x)).re) v s ∧
        v ≤ 2 * K * Λ * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
          (W (G s k)) x * star ((W (G s j)) x)).re := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let K := (1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
    2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsem : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  obtain ⟨G, H, hG, hH, hHc, hd⟩ :=
    u7_forward_D2_weighted_principal_energy_derivative a i ζ ha hΛ hA hφ P hP hfg hgh
  refine ⟨G, hG, ?_⟩
  intro s hs
  refine ⟨_, hd s, ?_⟩
  have hc := u7_forward_weighted_energy_cross_le a i ζ ha hΛ hA
    (hsem.map_gen hfg s.toNNReal) (G s) (H s) (hG s hs.le) (hH s) hφ
  have hp := c18_physical_principal_energy_coercive a ha hΛ hA (fun j => W (G s j))
  have hm := mul_le_mul_of_nonneg_left hp hK
  dsimp only [W, K] at hc hm ⊢
  nlinarith only [hc, hm]

/-- The forward weighted principal energy grows at a structural exponential rate. -/
theorem u7_forward_D2_weighted_energy_growth
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexGeneratorPair a i ζ g h) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let K := (1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
      2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      ∀ (t₀ t : ℝ), 0 < t₀ → t₀ ≤ t →
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * (W (G t k)) x *
          star ((W (G t j)) x)).re ≤
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * (W (G t₀ k)) x *
          star ((W (G t₀ j)) x)).re * Real.exp (2 * K * Λ * (t - t₀)) := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let K := (1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
    2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2
  obtain ⟨G, hG, hd⟩ :=
    u7_forward_D2_weighted_energy_derivative_le a i ζ ha hΛ hA hφ P hP hfg hgh
  refine ⟨G, hG, ?_⟩
  intro t₀ t ht₀ htt
  let E (s : ℝ) := (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
    (W (G s k)) x * star ((W (G s j)) x)).re
  let C := 2 * K * Λ
  have hder (s : ℝ) (hs : 0 < s) : HasDerivAt E (deriv E s) s ∧
      deriv E s ≤ C * E s := by
    obtain ⟨v, hv, hb⟩ := hd s hs
    have he : HasDerivAt E v s := hv
    rw [he.deriv]
    exact ⟨he, hb⟩
  have hc : ContinuousOn E (Set.Icc t₀ t) := by
    intro s hs
    exact (hder s (lt_of_lt_of_le ht₀ hs.1)).1.continuousAt.continuousWithinAt
  have hb := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := deriv E) (δ := E t₀) (K := C) (ε := 0) (a := t₀) (b := t)
    hc (fun s hs _ hr => ((hder s (lt_of_lt_of_le ht₀ hs.1)).1.hasDerivWithinAt).liminf_right_slope_le hr)
    le_rfl (fun s hs => by simpa only [add_zero] using (hder s (lt_of_lt_of_le ht₀ hs.1)).2)
    t ⟨htt, le_rfl⟩
  rw [gronwallBound_ε0] at hb
  exact hb

/-- Positive-time forward principal energy is bounded by the integrated gradient. -/
theorem u7_forward_weighted_energy_endpoint_explicit
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexGeneratorPair a i ζ g h) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let C := 2 * ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
      2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * Λ
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
        ((t : ℝ) / 2) * ((∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
          (W (G (t : ℝ) k)) x * star ((W (G (t : ℝ) j)) x)).re * Real.exp (-C * t)) ≤
        Λ * (4 * Λ * (‖W f‖ ^ 2 / 2 + H * (t : ℝ) *
          (Real.exp (k * t) * ‖W f‖) ^ 2)) := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let C := 2 * ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
    2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * Λ
  have hΛpos : 0 < Λ := by linarith
  have hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ := Filter.Eventually.of_forall hell
  obtain ⟨G, hG, hGc, hbound⟩ :=
    u7_forward_orbit_integrated_weighted_gradient_explicit a i ζ ha hΛ hell hmeas hφ P hP hfg
  obtain ⟨D, hD, hd⟩ :=
    u7_forward_D2_weighted_energy_derivative_le a i ζ ha hΛpos hA hφ P hP hfg hgh
  obtain ⟨R, hR, hr⟩ :=
    u7_forward_D2_weighted_energy_growth a i ζ ha hΛpos hA hφ P hP hfg hgh
  have hDG (s : ℝ) (hs : 0 ≤ s) : D s = G s :=
    physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ (hD s hs) (hG s)
  have hRG (s : ℝ) (hs : 0 ≤ s) : R s = G s :=
    physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ (hR s hs) (hG s)
  let E (s : ℝ) := (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
    (W (D s k)) x * star ((W (D s j)) x)).re
  let A (s : ℝ) := ∑ j, ‖W (G s j)‖ ^ 2
  refine ⟨G, hG, fun t ht => ?_⟩
  have hE : ContinuousOn E (Set.Icc ((t : ℝ) / 2) t) := by
    intro s hs
    have hspos : 0 < s := by linarith [hs.1]
    obtain ⟨v, hv, _⟩ := hd s hspos
    exact hv.continuousAt.continuousWithinAt
  have hEn : ∀ s ∈ Set.Icc ((t : ℝ) / 2) t, 0 ≤ E s := by
    intro s hs
    have hc := c18_physical_principal_energy_coercive a ha hΛpos hA (fun j => W (D s j))
    have hn : 0 ≤ ∑ j, ‖W (D s j)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    change _ ≤ Λ * E s at hc
    nlinarith only [hc, hn, hΛpos]
  have hg : ∀ s ∈ Set.Icc ((t : ℝ) / 2) t,
      E t ≤ E s * Real.exp (C * ((t : ℝ) - s)) := by
    intro s hs
    have hspos : 0 < s := by linarith [hs.1]
    have hh := hr s t hspos hs.2
    rw [hRG s hspos.le, hRG t t.property] at hh
    simpa only [E, hDG s hspos.le, hDG t t.property] using hh
  have hAc : Continuous A := by
    dsimp [A]
    exact continuous_finsetSum _ (fun j _ => ((W.continuous.comp (hGc j)).norm).pow 2)
  have hupper : ∀ s ∈ Set.Icc ((t : ℝ) / 2) t, E s ≤ Λ * (A s + 0) := by
    intro s hs
    have hs0 : 0 ≤ s := by linarith [hs.1]
    have hu := c18_physical_principal_energy_upper a ha hA (fun j => W (G s j))
    simpa only [E, A, hDG s hs0, add_zero] using hu
  have he := c7_energy_endpoint_of_integrated_bounds E A (fun _ => 0) C Λ t _ 0
    (by dsimp [C]; positivity) hΛpos.le ht hE hEn hg hAc.continuousOn continuousOn_const
    (fun s _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (fun _ _ => le_rfl)
    hupper (hbound t) (by simp)
  simpa only [E, hDG t t.property, add_zero] using he

/-- The weighted gradient endpoint for forward twice-generator-domain data. -/
theorem u7_forward_D2_weighted_gradient_endpoint_explicit
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexGeneratorPair a i ζ g h) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let C := 2 * ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
      2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * Λ
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (P s.toNNReal f) (G s)) ∧
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
        (∑ j, ‖W (G (t : ℝ) j)‖ ^ 2) ≤
        Λ * ((2 / (t : ℝ)) * Real.exp (C * t) *
          (Λ * (4 * Λ * (‖W f‖ ^ 2 / 2 + H * (t : ℝ) *
            (Real.exp (k * t) * ‖W f‖) ^ 2)))) := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let C := 2 * ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
    2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * Λ
  have hΛpos : 0 < Λ := by linarith
  have hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ := Filter.Eventually.of_forall hell
  obtain ⟨G, hG, hb⟩ :=
    u7_forward_weighted_energy_endpoint_explicit a i ζ ha hΛ hell hmeas hφ P hP hfg hgh
  refine ⟨G, hG, fun t ht => ?_⟩
  let E := (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * (W (G (t : ℝ) k)) x *
    star ((W (G (t : ℝ) j)) x)).re
  let R := Λ * (4 * Λ * (‖W f‖ ^ 2 / 2 + H * (t : ℝ) *
    (Real.exp (k * t) * ‖W f‖) ^ 2))
  have henergy : ((t : ℝ) / 2) * (E * Real.exp (-C * t)) ≤ R := hb t ht
  have hexp : Real.exp (-C * t) * Real.exp (C * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hEt : E ≤ (2 / (t : ℝ)) * Real.exp (C * t) * R := by
    have hm := mul_le_mul_of_nonneg_right henergy (Real.exp_pos (C * t)).le
    have hm' : ((t : ℝ) / 2) * E ≤ R * Real.exp (C * t) := by
      calc
        _ = (((t : ℝ) / 2) * (E * Real.exp (-C * t))) * Real.exp (C * t) := by
          calc
            _ = ((t : ℝ) / 2) * E * (Real.exp (-C * t) * Real.exp (C * t)) := by rw [hexp, mul_one]
            _ = _ := by ring
        _ ≤ _ := hm
    have ht' : 0 < (t : ℝ) / 2 := by positivity
    have hd : E ≤ (R * Real.exp (C * t)) / ((t : ℝ) / 2) :=
      (le_div_iff₀ ht').2 (by simpa only [mul_comm E ((t : ℝ) / 2)] using hm')
    calc
      E ≤ (R * Real.exp (C * t)) / ((t : ℝ) / 2) := hd
      _ = (2 / (t : ℝ)) * Real.exp (C * t) * R := by ring
  have hco := c18_physical_principal_energy_coercive a ha hΛpos hA (fun j => W (G (t : ℝ) j))
  exact hco.trans (mul_le_mul_of_nonneg_left hEt hΛpos.le)

/-- The squared localized coordinate norms equal the localized gradient energy. -/
theorem u7_localized_gradient_energy_eq {d : ℕ} (E : Set (Vec d))
    (hE : MeasurableSet E) (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∑ j, ((eLpNorm (E.indicator (fun x => G j x)) 2 volume).toReal) ^ 2) =
      ∫ x in E, ∑ j, ‖G j x‖ ^ 2 := by
  have hm (j : Fin d) : MemLp (fun x => G j x) 2 (volume.restrict E) :=
    (Lp.memLp (G j)).mono_measure Measure.restrict_le_self
  rw [integral_finsetSum _ (fun j _ => (hm j).integrable_norm_pow (by norm_num))]
  apply Finset.sum_congr rfl
  intro j _
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hE]
  rw [← eLpNorm_norm (fun x => G j x) (hm j).aestronglyMeasurable]
  exact PDE.toReal_eLpNorm_two_sq_eq_integral_sq (hm j).norm

/-- The actual transpose gradient tail in restricted-integral form. -/
theorem u7_physical_transpose_gradient_off_diagonal_integral
    (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (hell : IsElliptic Λ ω.1) (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
    ∀ (t : ℝ≥0), 0 < t → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ x ∂volume, ρ / 2 ≤ euclideanNorm (x - z) → f x = 0) →
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (Pdag t f) G ∧
      Real.sqrt (∫ x in {x : Vec d | ρ ≤ euclideanNorm (x-z)},
        ∑ j, ‖G j x‖ ^ 2 ∂volume) ≤
      C * ((Real.sqrt (t : ℝ))⁻¹ + ‖ζ‖) *
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) * ‖f‖ := by
  obtain ⟨C, c, hC, hc, htail⟩ := u7_physical_transpose_gradient_offdiagonal d Λ hΛ
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω hell i ζ P Pdag hPdag t ht z ρ hρ f hf
  obtain ⟨G, hG, hb⟩ := htail ω hell i ζ P Pdag hPdag t ht z ρ hρ f hf
  have hn : Continuous (fun x : Vec d => euclideanNorm (x - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hE : MeasurableSet {x : Vec d | ρ ≤ euclideanNorm (x - z)} :=
    (isClosed_le continuous_const hn).measurableSet
  refine ⟨G, hG, ?_⟩
  rwa [← u7_localized_gradient_energy_eq _ hE G]

private theorem u7_cauchy_of_norm_sq_bound
    {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
    (V : ℕ → E) (f : ℕ → H) (hf : CauchySeq f) (C : ℝ)
    (hbound : ∀ n m, ‖V n - V m‖ ^ 2 ≤ C * ‖f n - f m‖ ^ 2) :
    CauchySeq V := by
  have hfc : Filter.Tendsto (fun nm : ℕ × ℕ => ‖f nm.1 - f nm.2‖)
      Filter.atTop (nhds 0) := by
    simpa only [dist_eq_norm] using cauchySeq_iff_tendsto_dist_atTop_0.mp hf
  have hsq : Filter.Tendsto (fun nm : ℕ × ℕ => ‖V nm.1 - V nm.2‖ ^ 2)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun nm : ℕ × ℕ => sq_nonneg ‖V nm.1 - V nm.2‖)
      (fun nm : ℕ × ℕ => hbound nm.1 nm.2)
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using (hfc.pow 2).const_mul C
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, dist_eq_norm, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using h

private theorem u7_gen_sub
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

private theorem u7_physicalH1_sub {d : ℕ}
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

private theorem u7_pi_norm_sq_le_sum {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (G : Fin d → E) : ‖G‖ ^ 2 ≤ ∑ j, ‖G j‖ ^ 2 := by
  have hn : 0 ≤ ∑ j, ‖G j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : ‖G‖ ≤ Real.sqrt (∑ j, ‖G j‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    apply (Real.le_sqrt (norm_nonneg _) hn).mpr
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖G k‖) (Finset.mem_univ j)
  have hsq := sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _) |>.mpr hb
  rwa [Real.sq_sqrt hn] at hsq

/-- A weighted gradient estimate on the twice-generator domain passes to all
forward data through the closed physical H¹ graph. The unweighted estimate
supplies the Cauchy property of the gradients. -/
theorem u7_forward_weighted_gradient_of_D2 {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (W : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (K₀ K : ℝ) (t : ℝ≥0)
    (hD₀ : ∀ f g h, IsPhysicalComplexGeneratorPair a i ζ f g →
      IsPhysicalComplexGeneratorPair a i ζ g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G ∧
        (∑ j, ‖G j‖ ^ 2) ≤ K₀ * ‖f‖ ^ 2)
    (hD : ∀ f g h, IsPhysicalComplexGeneratorPair a i ζ f g →
      IsPhysicalComplexGeneratorPair a i ζ g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G ∧
        (∑ j, ‖W (G j)‖ ^ 2) ≤ K * ‖W f‖ ^ 2)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G ∧
      (∑ j, ‖W (G j)‖ ^ 2) ≤ K * ‖W f‖ ^ 2 := by
  classical
  let Gen := IsPhysicalComplexGeneratorPair a i ζ
  have hp : S5Semigroup P Gen := ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  let D2 : Set (Lp ℂ 2 (volume : Measure (Vec d))) := {u | ∃ v w, Gen u v ∧ Gen v w}
  have hfirst (u v : Lp ℂ 2 (volume : Measure (Vec d))) (huv : Gen u v) :
      u ∈ closure D2 := by
    obtain ⟨F, G, H, hgen, hF, _⟩ := c18_physical_generator_D2_approx a i ζ P hP huv
    apply mem_closure_of_tendsto hF
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ⟨G δ, H δ, hgen δ hδ⟩
  have hdense : Dense D2 := by
    intro u
    obtain ⟨F, G, hgen, hF⟩ := hp.exists_gen_approx u
    apply isClosed_closure.mem_of_tendsto hF
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hfirst (F δ) (G δ) (hgen δ hδ)
  have hall : ∀ u v w, Gen u v → Gen v w → ∀ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (P t u) G →
      (∑ j, ‖G j‖ ^ 2) ≤ K₀ * ‖u‖ ^ 2 ∧ (∑ j, ‖W (G j)‖ ^ 2) ≤ K * ‖W u‖ ^ 2 := by
    intro u v w huv hvw G hG
    obtain ⟨G₁, hG₁, hb₁⟩ := hD₀ u v w huv hvw
    obtain ⟨G₂, hG₂, hb₂⟩ := hD u v w huv hvw
    have e₁ := physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ hG₁ hG
    have e₂ := physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ hG₂ hG
    subst e₁ e₂
    exact ⟨hb₁, hb₂⟩
  obtain ⟨F, hF, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense f)
  change ∀ n, ∃ v w, Gen (F n) v ∧ Gen v w at hF
  choose g h hg hh using hF
  choose G hG _ using fun n => hD (F n) (g n) (h n) (hg n) (hh n)
  have hdiff (n m : ℕ) : ‖G n - G m‖ ^ 2 ≤ K₀ * ‖F n - F m‖ ^ 2 := by
    have hsub : IsPhysicalH1Graph volume (Or.inl rfl)
        (P t (F n - F m)) (fun j => G n j - G m j) := by
      simpa only [map_sub] using u7_physicalH1_sub (hG n) (hG m)
    have hb' := (hall (F n - F m) (g n - g m) (h n - h m)
      (u7_gen_sub hp (hg n) (hg m)) (u7_gen_sub hp (hh n) (hh m)) _ hsub).1
    exact (u7_pi_norm_sq_le_sum (G n - G m)).trans hb'
  have hC : CauchySeq G := u7_cauchy_of_norm_sq_bound G F hlim.cauchySeq K₀ hdiff
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨V, physicalH1Graph_of_tendsto volume (Or.inl rfl)
    (fun n => (P t (F n), G n)) (P t f, V) hG ?_, ?_⟩
  · exact (((P t).continuous.tendsto f).comp hlim).prodMk_nhds hV
  · have hl : Filter.Tendsto (fun n => ∑ j, ‖W (G n j)‖ ^ 2) Filter.atTop
        (nhds (∑ j, ‖W (V j)‖ ^ 2)) := by
      apply tendsto_finsetSum
      intro j _
      have hj : Filter.Tendsto (fun n => G n j) Filter.atTop (nhds (V j)) :=
        (continuous_apply j).continuousAt.tendsto.comp hV
      exact ((W.continuous.tendsto _).comp hj).norm.pow 2
    have hr : Filter.Tendsto (fun n => K * ‖W (F n)‖ ^ 2) Filter.atTop
        (nhds (K * ‖W f‖ ^ 2)) :=
      (((W.continuous.tendsto f).comp hlim).norm.pow 2).const_mul K
    exact le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall fun n => by
      exact (hall (F n) (g n) (h n) (hg n) (hh n) (G n) (hG n)).2)

/-- Forward weighted gradient bound extended from the twice-generator domain. -/
theorem u7_forward_weighted_gradient_endpoint
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (K₀ : ℝ)
    (hD₀ : ∀ f g h, IsPhysicalComplexGeneratorPair a i ζ f g →
      IsPhysicalComplexGeneratorPair a i ζ g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G ∧
        (∑ j, ‖G j‖ ^ 2) ≤ K₀ * ‖f‖ ^ 2)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let C := 2 * ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
      2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * Λ
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G ∧
      (∑ j, ‖W (G j)‖ ^ 2) ≤
        (Λ * ((2 / (t : ℝ)) * Real.exp (C * t) *
          (Λ * (4 * Λ * (1 / 2 + H * (t : ℝ) * Real.exp (k * t) ^ 2))))) *
          ‖W f‖ ^ 2 := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let C := 2 * ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
    2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * Λ
  let K := Λ * ((2 / (t : ℝ)) * Real.exp (C * t) *
    (Λ * (4 * Λ * (1 / 2 + H * (t : ℝ) * Real.exp (k * t) ^ 2))))
  apply u7_forward_weighted_gradient_of_D2 a i ζ P hP W K₀ K t hD₀ ?_ f
  intro u v w huv hvw
  obtain ⟨G, hG, hb⟩ :=
    u7_forward_D2_weighted_gradient_endpoint_explicit a i ζ ha hΛ hell hmeas hφ P hP huv hvw
  refine ⟨G t, ?_, ?_⟩
  · simpa only [Real.toNNReal_coe] using hG t
  · have h := hb t ht
    change (∑ j, ‖W (G (t : ℝ) j)‖ ^ 2) ≤ _ at h
    convert h using 1; dsimp [K, W, H, k, C]; ring

/-- Explicit forward weighted-gradient endpoint constant. -/
noncomputable def u7ForwardWeightedGradientConst (d : ℕ) (Λ q : ℝ) (ζ : ℂ) (t : ℝ) : ℝ :=
  let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let C := 2 * ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
    2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * Λ
  Λ * ((2 / t) * Real.exp (C * t) *
    (Λ * (4 * Λ * (1 / 2 + H * t * Real.exp (k * t) ^ 2))))

/-- A radial exponential weight turns the weighted gradient endpoint into an
outer Gaussian-type tail for data supported in the inner ball. -/
theorem u7_forward_radial_gradient_tail
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (z : Vec d) {ρ q : ℝ} (hρ : 0 < ρ) (hq : 0 ≤ q)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (g : Lp ℂ 2 (volume : Measure (Vec d)))
    (hg : ∀ᵐ x ∂volume, ρ / 2 < euclideanNorm (x - z) → g x = 0) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (P t g) G ∧
      Real.sqrt (∑ j : Fin d,
        ((eLpNorm ({x : Vec d | ρ ≤ euclideanNorm (x - z)}.indicator
          (fun x => G j x)) 2 volume).toReal) ^ 2) ≤
        Real.exp (-(3 * q * ρ / 10)) *
          Real.sqrt (u7ForwardWeightedGradientConst d Λ q ζ t) * ‖g‖ := by
  let ψ : Vec d → ℝ := fun x => ρ * euclideanSq (x - z) / (ρ ^ 2 + euclideanSq (x - z))
  have hφ : S5Weight (fun x => Real.exp (q * ψ x)) (Real.exp (q * ρ)) q :=
    c7_radial_exp_s5Weight z hρ hq
  obtain ⟨_, hvalues, _, hinner, houter⟩ := c7_bounded_radial_weight_geometry z hρ
  have hD₀ := u4Quant_forward_D2_gradient_at_time a i ζ ha (by linarith : 0 < Λ)
    (Filter.Eventually.of_forall hell) P hP t (by exact_mod_cast ht)
  obtain ⟨G, hG, hb⟩ := u7_forward_weighted_gradient_endpoint a i ζ ha hΛ hell hmeas hφ
    P hP t ht (u4QuantGradientConstant d Λ ‖ζ‖ 0 t) hD₀ g
  change (∑ j, ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G j)‖ ^ 2) ≤
    u7ForwardWeightedGradientConst d Λ q ζ t *
      ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g‖ ^ 2 at hb
  refine ⟨G, hG, ?_⟩
  set W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound with hWdef
  have hWg : ‖W g‖ ≤ Real.exp (q * ρ / 5) * ‖g‖ := by
    apply c7_s5Mul_norm_le_of_ae _ _ _ (Real.exp_pos _).le
    filter_upwards [hg] with x hx hgx
    have hlt : euclideanNorm (x - z) ≤ ρ / 2 := by
      by_contra hcon
      exact hgx (hx (not_le.mp hcon))
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_left (hinner x hlt) hq
      linarith)
  have hn : Continuous (fun x : Vec d => euclideanNorm (x - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hE : MeasurableSet {x : Vec d | ρ ≤ euclideanNorm (x - z)} :=
    (isClosed_le continuous_const hn).measurableSet
  have hc : 0 < Real.exp (q * ρ / 2) := Real.exp_pos _
  have hj (j : Fin d) : (eLpNorm ({x : Vec d | ρ ≤ euclideanNorm (x - z)}.indicator
      (fun x => G j x)) 2 volume).toReal ≤ (Real.exp (q * ρ / 2))⁻¹ * ‖W (G j)‖ := by
    apply c7_indicator_eLpNorm_le_weighted hφ.measurable hφ.B_nonneg hφ.bound hc hE
    intro x hx
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_left (houter x hx) hq
      linarith)
  have hsum : (∑ j : Fin d, ((eLpNorm ({x : Vec d | ρ ≤ euclideanNorm (x - z)}.indicator
      (fun x => G j x)) 2 volume).toReal) ^ 2) ≤
      ((Real.exp (q * ρ / 2))⁻¹) ^ 2 * (∑ j, ‖W (G j)‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [← mul_pow]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hj j) 2
  calc Real.sqrt _ ≤ Real.sqrt (((Real.exp (q * ρ / 2))⁻¹) ^ 2 *
          (u7ForwardWeightedGradientConst d Λ q ζ t * ‖W g‖ ^ 2)) :=
        Real.sqrt_le_sqrt (hsum.trans (mul_le_mul_of_nonneg_left hb (sq_nonneg _)))
    _ = (Real.exp (q * ρ / 2))⁻¹ * (Real.sqrt (u7ForwardWeightedGradientConst d Λ q ζ t) * ‖W g‖) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hc.le),
          Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ (Real.exp (q * ρ / 2))⁻¹ * (Real.sqrt (u7ForwardWeightedGradientConst d Λ q ζ t) *
          (Real.exp (q * ρ / 5) * ‖g‖)) := by
        gcongr
    _ = _ := by
        have : Real.exp (-(3 * q * ρ / 10)) = (Real.exp (q * ρ / 2))⁻¹ * Real.exp (q * ρ / 5) := by
          rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
        rw [this]; ring


/-- The forward endpoint constant has a structural Gaussian-weight bound. -/
theorem u7_forward_weightedGradientConst_le {d : ℕ} {Λ q : ℝ} (hΛ : 1 ≤ Λ)
    (ζ : ℂ) {t : ℝ} (ht : 0 < t) :
    u7ForwardWeightedGradientConst d Λ q ζ t ≤
      ((4 * Λ ^ 3 + 320 * Λ ^ 6) / t) *
        Real.exp (((26 + 4 * ((d : ℝ) + 1)) * Λ ^ 3 + 1) *
          ((q ^ 2 + ‖ζ‖ ^ 2) * t)) := by
  have hΛ0 : 0 < Λ := by linarith
  let κ := (q ^ 2 + ‖ζ‖ ^ 2) * t
  let D := (16 + 4 * ((d : ℝ) + 1)) * Λ ^ 3
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE1 : Real.exp ((2 * ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
      2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * Λ) * t) ≤ Real.exp (D * κ) := by
    apply Real.exp_le_exp.mpr
    dsimp [D, κ]
    have h1 : 0 ≤ 4 * ((d : ℝ) + 1) * Λ ^ 3 * q ^ 2 * t := by positivity
    have h2 : 0 ≤ 16 * Λ ^ 3 * ‖ζ‖ ^ 2 * t := by positivity
    nlinarith
  have hE2 : Real.exp (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2) * t) ^ 2 =
      Real.exp (10 * Λ ^ 3 * κ) := by
    rw [sq, ← Real.exp_add]; congr 1; dsimp [κ]; ring
  have hK : u7ForwardWeightedGradientConst d Λ q ζ t * t =
      8 * Λ ^ 3 * Real.exp ((2 * ((1 / 2 : ℝ) * (2 * Λ * (2 * q)) ^ 2 +
        2 * ((d : ℝ) + 1) * Λ ^ 2 * ‖ζ‖ ^ 2) * Λ) * t) *
          (1 / 2 + 40 * Λ ^ 3 * κ * Real.exp (10 * Λ ^ 3 * κ)) := by
    unfold u7ForwardWeightedGradientConst
    dsimp only
    rw [hE2]
    dsimp [κ]
    field_simp [ne_of_gt ht]; ring
  have hE1' : 1 ≤ Real.exp (D * κ) := Real.one_le_exp (by positivity)
  have hE2' : 1 ≤ Real.exp (10 * Λ ^ 3 * κ) := Real.one_le_exp (by positivity)
  have hκe : κ ≤ Real.exp κ := by linarith [Real.add_one_le_exp κ]
  have hκe1 : 1 ≤ Real.exp κ := Real.one_le_exp hκ
  have hX : Real.exp (((26 + 4 * ((d : ℝ) + 1)) * Λ ^ 3 + 1) *
      ((q ^ 2 + ‖ζ‖ ^ 2) * t)) =
      Real.exp (D * κ) * Real.exp (10 * Λ ^ 3 * κ) * Real.exp κ := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [D, κ]; ring
  generalize Real.exp (D * κ) = E1 at hE1 hE1' hX
  generalize Real.exp (10 * Λ ^ 3 * κ) = E2 at hK hE2' hX
  generalize Real.exp κ = E3 at hκe hκe1 hX
  have hE2nn : 0 ≤ E2 := by linarith
  have h23 : 1 ≤ E2 * E3 := one_le_mul_of_one_le_of_one_le hE2' hκe1
  have hE1X : E1 ≤ E1 * E2 * E3 := by
    have := mul_le_mul_of_nonneg_left h23 (by linarith : 0 ≤ E1)
    nlinarith
  have hκX : κ * E2 * E1 ≤ E1 * E2 * E3 := by
    have := mul_le_mul_of_nonneg_right hκe (mul_nonneg (by linarith : 0 ≤ E2) (by linarith : 0 ≤ E1))
    nlinarith
  have hfinal : u7ForwardWeightedGradientConst d Λ q ζ t * t ≤
      (4 * Λ ^ 3 + 320 * Λ ^ 6) * (E1 * E2 * E3) := by
    rw [hK]
    have hinner : 0 ≤ 1 / 2 + 40 * Λ ^ 3 * κ * E2 := by positivity
    have hfirst := mul_le_mul_of_nonneg_left hE1 (by positivity : 0 ≤ 8 * Λ ^ 3)
    have hprod := mul_le_mul_of_nonneg_right hfirst hinner
    have hleft := mul_le_mul_of_nonneg_left hE1X (by positivity : 0 ≤ 4 * Λ ^ 3)
    have hright := mul_le_mul_of_nonneg_left hκX (by positivity : 0 ≤ 320 * Λ ^ 6)
    nlinarith
  rw [hX, div_mul_eq_mul_div, le_div_iff₀ ht]
  linarith

/-- Uniform positive-time Gaussian localization of the actual forward gradient. -/
theorem u7_physical_gradient_off_diagonal
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ)
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
      (t : ℝ≥0), 0 < t → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ x ∂volume, ρ / 2 < euclideanNorm (x-z) → f x = 0) →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G ∧
        Real.sqrt (∫ x in {x : Vec d | ρ ≤ euclideanNorm (x-z)},
          ∑ j, ‖G j x‖^2 ∂volume) ≤
          C * ((Real.sqrt (t : ℝ))⁻¹ + ‖ζ‖) *
            Real.exp (C * ‖ζ‖^2*(t : ℝ) - c*ρ^2/(t : ℝ)) * ‖f‖ := by
  let A : ℝ := 4 * Λ ^ 3 + 320 * Λ ^ 6
  let N : ℝ := (26 + 4 * ((d : ℝ) + 1)) * Λ ^ 3 + 1
  have hΛ0 : 0 < Λ := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨Real.sqrt A + N / 2 + 1, 9 / (200 * N), ?_, by positivity, ?_⟩
  · have := Real.sqrt_nonneg A
    linarith
  intro ω M hell hsmooth i ζ P Pdag hP hPdag t ht z ρ hρ f hf
  have ht' : 0 < (t : ℝ) := NNReal.coe_pos.mpr ht
  have hmeas : ∀ j k, Measurable fun x => ω.1 x j k := fun j k =>
    (ω.1.continuous.matrix_elem j k).measurable
  have ha := fun j k => memLp_complex_elliptic_entry volume ω.1 Λ hΛ0 hell
    (fun j k => ω.1.continuous.matrix_elem j k) j k
  obtain ⟨G, hG, hb⟩ := u7_forward_radial_gradient_tail ω.1 i ζ ha hΛ
    (s5Elliptic_of_isElliptic hΛ hell) hmeas P hP z hρ
    (show 0 ≤ 3 * ρ / (10 * N * (t : ℝ)) by positivity) t ht' f hf
  have hn : Continuous (fun x : Vec d => euclideanNorm (x - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hE : MeasurableSet {x : Vec d | ρ ≤ euclideanNorm (x - z)} :=
    (isClosed_le continuous_const hn).measurableSet
  refine ⟨G, hG, ?_⟩
  rw [← u7_localized_gradient_energy_eq _ hE G]
  refine hb.trans ?_
  have hK := u7_forward_weightedGradientConst_le (d := d)
    (q := 3 * ρ / (10 * N * (t : ℝ))) hΛ ζ ht'
  change u7ForwardWeightedGradientConst d Λ _ _ _ ≤ (A / (t : ℝ)) *
    Real.exp (N * ((_ ^ 2 + ‖ζ‖ ^ 2) * (t : ℝ))) at hK
  have hsq := Real.sqrt_le_sqrt hK
  have h1 := mul_le_mul_of_nonneg_left hsq
    (Real.exp_pos (-(3 * (3 * ρ / (10 * N * (t : ℝ))) * ρ / 10))).le
  calc _ ≤ _ := mul_le_mul_of_nonneg_right h1 (norm_nonneg f)
    _ ≤ _ := mul_le_mul_of_nonneg_right (c7_radial_tail_arith (A := A) (N := N) (x := ‖ζ‖)
        (s := (t : ℝ)) (ρ := ρ) hA hN (norm_nonneg ζ) ht') (norm_nonneg f)


/-- Singular-time data yield the bounded limit of the truncated divergence integrals. -/
theorem u7_singular_divergence_truncated_endpoints
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ)
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
    ∀ (t : ℝ), 0 < t → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j, ContinuousOn (fun s => F s j) (Set.Ioo 0 t)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ s ∈ Set.Ioo 0 t, Real.sqrt (∑ j, ‖F s j‖^2) ≤ (Real.sqrt (t-s))⁻¹ * B) →
      (∀ s ∈ Set.Ioo 0 t, ∀ j, ∀ᵐ x ∂volume, euclideanNorm (x-z) < ρ → F s j x = 0) →
      ∀ a b : ℕ → ℝ, Filter.Tendsto a Filter.atTop (nhds 0) →
      Filter.Tendsto b Filter.atTop (nhds t) →
      (∀ n, 0 ≤ a n ∧ b n ≤ t) →
      let v : ℝ → Lp ℂ 2 (volume : Measure (Vec d)) := fun s =>
        u7DivergenceBallRestriction z ρ
          (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))
      Filter.Tendsto (fun n => ∫ s in Set.Ioo (a n) (b n), v s) Filter.atTop
          (nhds (∫ s in Set.Ioo 0 t, v s)) ∧
      ‖∫ s in Set.Ioo 0 t, v s‖ ≤
        C * (1 + ‖ζ‖ * Real.sqrt t) *
          Real.exp (C * ‖ζ‖^2 * t - c * ρ^2/t) * B := by
  obtain ⟨C, c, hC, hc, h⟩ := u7_physical_singular_time_data_divergence_local_integral d hd Λ hΛ
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω M hell hsmooth i ζ P Pdag hP hPdag t ht z ρ hρ F hF B hB hFb hFs a b ha hb hab v
  obtain ⟨hv, hbound⟩ := h ω M hell hsmooth i ζ P Pdag hP hPdag t ht z ρ hρ F hF B hB hFb hFs
  exact ⟨u7_integral_truncated_endpoints_tendsto hv ha hb hab, hbound⟩


/-- A positive-time gradient operator represents every shifted orbit and its
normalized time integral. -/
theorem u7_forward_shifted_gradient_and_average
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (t : ℝ≥0) (ht : 0 < t) (ε : ℝ)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        (Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ s : ℝ, IsPhysicalH1Graph volume (Or.inl rfl)
        (P (t + s.toNNReal) f) (T (P s.toNNReal f))) ∧
      Continuous (fun s : ℝ => T (P s.toNNReal f)) ∧
      IsPhysicalH1Graph volume (Or.inl rfl)
        (((ε : ℂ)⁻¹) • ∫ s in (0 : ℝ)..ε, P (t + s.toNNReal) f)
        (((ε : ℂ)⁻¹) • ∫ s in (0 : ℝ)..ε, T (P s.toNNReal f)) := by
  obtain ⟨T, hT⟩ := Blueprint.c7_physical_gradient_operator hΛ hell hsmooth hP hPdag
    P (by simp) t ht
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hP.2.2.1 f).comp continuous_real_toNNReal
  have hi : IntervalIntegrable (fun s : ℝ => P s.toNNReal f) volume 0 ε :=
    hu.intervalIntegrable _ _
  refine ⟨T, ?_, T.continuous.comp hu, ?_⟩
  · intro s
    simpa only [hP.2.1, ContinuousLinearMap.comp_apply] using hT (P s.toNNReal f)
  · have hv := hT (((ε : ℂ)⁻¹) • ∫ s in (0 : ℝ)..ε, P s.toNNReal f)
    rw [map_smul, ← (P t).intervalIntegral_comp_comm hi,
      map_smul, ← T.intervalIntegral_comp_comm hi] at hv
    convert hv using 1
    congr 2
    funext s
    rw [hP.2.1]
    rfl

/-- Uniform comparison of the Gaussian gradient envelope on a doubled time interval. -/
theorem u7_gradient_envelope_on_doubled_interval
    (C c x ρ t s R : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (ht : 0 < t) (hts : t ≤ s) (hst : s ≤ 2 * t) (hR : 0 ≤ R) :
    C * ((Real.sqrt s)⁻¹ + x) *
        Real.exp (C * x ^ 2 * s - c * ρ ^ 2 / s) * R ≤
      (2 * C) * ((Real.sqrt t)⁻¹ + x) *
        Real.exp ((2 * C) * x ^ 2 * t - (c / 2) * ρ ^ 2 / t) * R := by
  have hs : 0 < s := lt_of_lt_of_le ht hts
  have hroot : (Real.sqrt s)⁻¹ ≤ (Real.sqrt t)⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.mpr hs) (Real.sqrt_pos.mpr ht)).2
      (Real.sqrt_le_sqrt hts)
  have hdecay : c * ρ ^ 2 / (2 * t) ≤ c * ρ ^ 2 / s :=
    div_le_div_of_nonneg_left (mul_nonneg hc (sq_nonneg ρ)) hs hst
  have hdecay' : (c / 2) * ρ ^ 2 / t ≤ c * ρ ^ 2 / s := by
    convert hdecay using 1 <;> field_simp [ne_of_gt ht]
  have hforce : C * x ^ 2 * s ≤ (2 * C) * x ^ 2 * t := by
    nlinarith [mul_le_mul_of_nonneg_left hst (mul_nonneg hC (sq_nonneg x))]
  have hexp : Real.exp (C * x ^ 2 * s - c * ρ ^ 2 / s) ≤
      Real.exp ((2 * C) * x ^ 2 * t - (c / 2) * ρ ^ 2 / t) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpre : C * ((Real.sqrt s)⁻¹ + x) ≤
      (2 * C) * ((Real.sqrt t)⁻¹ + x) := by
    have h := mul_le_mul_of_nonneg_left (add_le_add_right hroot x) hC
    have hn : 0 ≤ C * ((Real.sqrt t)⁻¹ + x) := by positivity
    nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hpre hexp (Real.exp_pos _).le (by positivity)) hR

/-- Localized gradient energy is the norm of a bounded linear map into an
ℓ²-product of physical L² spaces. -/
theorem u7_localized_gradient_linear_map {d : ℕ}
    (E : Set (Vec d)) (hE : MeasurableSet E) :
    ∃ L : (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) →L[ℂ]
        (PiLp 2 fun _ : Fin d => Lp ℂ 2 (volume : Measure (Vec d))),
      ∀ G, ‖L G‖ = Real.sqrt (∫ x in E, ∑ j, ‖G j x‖ ^ 2) := by
  classical
  let w : Vec d → ℝ := E.indicator (fun _ => 1)
  have hw : Measurable w := measurable_const.indicator hE
  have hwbound : ∀ x, |w x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ E
    · simp [w, hx]
    · simp [w, hx]
  let W := s5Mul (volume : Measure (Vec d)) hw (by norm_num) hwbound
  let L : (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) →L[ℂ]
      (PiLp 2 fun _ : Fin d => Lp ℂ 2 (volume : Measure (Vec d))) :=
    (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin d => Lp ℂ 2 (volume : Measure (Vec d)))).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi (fun j => W.comp (ContinuousLinearMap.proj j)))
  refine ⟨L, ?_⟩
  intro G
  have hW (j : Fin d) : ‖W (G j)‖ =
      (eLpNorm (E.indicator (fun x => G j x)) 2 volume).toReal := by
    rw [s5Mul_norm]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ E
    · simp [w, hx]
    · simp [w, hx]
  rw [← u7_localized_gradient_energy_eq E hE G]
  change ‖(WithLp.toLp 2 (fun j => W (G j)) :
    PiLp 2 fun _ : Fin d => Lp ℂ 2 (volume : Measure (Vec d)))‖ = _
  rw [PiLp.norm_eq_of_L2]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by rw [hW j])

/-- The actual positive-time average retains the Gaussian localized gradient bound. -/
theorem u7_physical_time_averaged_gradient_off_diagonal
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ)
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
      (t : ℝ≥0), 0 < t → ∀ ε : ℝ, 0 < ε → ε ≤ (t : ℝ) →
      ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ x ∂volume, ρ / 2 < euclideanNorm (x-z) → f x = 0) →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl)
          (((ε : ℂ)⁻¹) • ∫ s in (0 : ℝ)..ε, P (t + s.toNNReal) f) G ∧
        Real.sqrt (∫ x in {x : Vec d | ρ ≤ euclideanNorm (x-z)},
          ∑ j, ‖G j x‖^2 ∂volume) ≤
          C * ((Real.sqrt (t : ℝ))⁻¹ + ‖ζ‖) *
            Real.exp (C * ‖ζ‖^2*(t : ℝ) - c*ρ^2/(t : ℝ)) * ‖f‖ := by
  obtain ⟨C, c, hC, hc, htail⟩ := u7_physical_gradient_off_diagonal d hd Λ hΛ
  refine ⟨2 * C, c / 2, by linarith, by positivity, ?_⟩
  intro ω M hell hsmooth i ζ P Pdag hP hPdag t ht ε hε hεt z ρ hρ f hf
  obtain ⟨T, hT, hTc, hTavg⟩ :=
    u7_forward_shifted_gradient_and_average hΛ hell hsmooth hP hPdag t ht ε f
  let E : Set (Vec d) := {x | ρ ≤ euclideanNorm (x-z)}
  have hE : MeasurableSet E := by
    have hn : Continuous (fun x : Vec d => euclideanNorm (x-z)) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact (isClosed_le continuous_const hn).measurableSet
  obtain ⟨L, hL⟩ := u7_localized_gradient_linear_map E hE
  let B : ℝ := (2 * C) * ((Real.sqrt (t : ℝ))⁻¹ + ‖ζ‖) *
    Real.exp ((2 * C) * ‖ζ‖^2 * (t : ℝ) - (c / 2) * ρ^2 / (t : ℝ)) * ‖f‖
  have hb : ∀ s ∈ Set.uIoc (0 : ℝ) ε, ‖L (T (P s.toNNReal f))‖ ≤ B := by
    intro s hs
    have hs' : s ∈ Set.Ioc (0 : ℝ) ε := by
      simpa only [Set.uIoc_of_le hε.le] using hs
    have hs0 : 0 ≤ s := hs'.1.le
    have htt : 0 < (t : ℝ) := NNReal.coe_pos.mpr ht
    have hts : (t : ℝ) ≤ ((t + s.toNNReal : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_add, Real.coe_toNNReal _ hs0]
      linarith
    have hst : ((t + s.toNNReal : ℝ≥0) : ℝ) ≤ 2 * (t : ℝ) := by
      simp only [NNReal.coe_add, Real.coe_toNNReal _ hs0]
      linarith [hs'.2]
    have hpos : 0 < t + s.toNNReal := lt_of_lt_of_le ht (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ s.toNNReal))
    obtain ⟨H, hH, hHb⟩ := htail ω M hell hsmooth i ζ P Pdag hP hPdag
      (t + s.toNNReal) hpos z ρ hρ f hf
    have heq := physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ (hT s) hH
    rw [hL, heq]
    exact hHb.trans (u7_gradient_envelope_on_doubled_interval C c ‖ζ‖ ρ (t : ℝ)
      ((t + s.toNNReal : ℝ≥0) : ℝ) ‖f‖ (by linarith) hc.le (norm_nonneg ζ)
      htt hts hst (norm_nonneg f))
  have hi : IntervalIntegrable (fun s : ℝ => T (P s.toNNReal f)) volume 0 ε :=
    hTc.intervalIntegrable _ _
  have hbound : ‖L (∫ s in (0 : ℝ)..ε, T (P s.toNNReal f))‖ ≤ B * ε := by
    rw [← L.intervalIntegral_comp_comm hi]
    simpa only [sub_zero, abs_of_pos hε] using
      (intervalIntegral.norm_integral_le_of_norm_le_const hb)
  refine ⟨((ε : ℂ)⁻¹) • ∫ s in (0 : ℝ)..ε, T (P s.toNNReal f), hTavg, ?_⟩
  rw [← hL, map_smul, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hε]
  calc
    ε⁻¹ * ‖L (∫ s in (0 : ℝ)..ε, T (P s.toNNReal f))‖ ≤ ε⁻¹ * (B * ε) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hε.le)
    _ = B := by field_simp [ne_of_gt hε]


/-- Continuous pairings preserve the singular-time endpoint limit and bound. -/
theorem u7_singular_divergence_truncated_endpoints_pairing
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ)
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
    ∀ (t : ℝ), 0 < t → ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j, ContinuousOn (fun s => F s j) (Set.Ioo 0 t)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ s ∈ Set.Ioo 0 t, Real.sqrt (∑ j, ‖F s j‖^2) ≤ (Real.sqrt (t-s))⁻¹ * B) →
      (∀ s ∈ Set.Ioo 0 t, ∀ j, ∀ᵐ x ∂volume, euclideanNorm (x-z) < ρ → F s j x = 0) →
      ∀ a b : ℕ → ℝ, Filter.Tendsto a Filter.atTop (nhds 0) →
      Filter.Tendsto b Filter.atTop (nhds t) →
      (∀ n, 0 ≤ a n ∧ b n ≤ t) →
      let v : ℝ → Lp ℂ 2 (volume : Measure (Vec d)) := fun s =>
        u7DivergenceBallRestriction z ρ
          (u7PhysicalEvolvedDivergence hΛ hell hsmooth hP hPdag s (F s))
      ∀ ell : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      Filter.Tendsto (fun n => ell (∫ s in Set.Ioo (a n) (b n), v s)) Filter.atTop
          (nhds (ell (∫ s in Set.Ioo 0 t, v s))) ∧
      ‖ell (∫ s in Set.Ioo 0 t, v s)‖ ≤
        ‖ell‖ * (C * (1 + ‖ζ‖ * Real.sqrt t) *
          Real.exp (C * ‖ζ‖^2 * t - c * ρ^2/t) * B) := by
  obtain ⟨C, c, hC, hc, h⟩ := u7_singular_divergence_truncated_endpoints d hd Λ hΛ
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω M hell hsmooth i ζ P Pdag hP hPdag t ht z ρ hρ F hF B hB hFb hFs a b ha hb hab v ell
  obtain ⟨htend, hbound⟩ := h ω M hell hsmooth i ζ P Pdag hP hPdag t ht z ρ hρ F hF B hB hFb hFs a b ha hb hab
  exact ⟨ell.continuous.tendsto _ |>.comp htend,
    (ell.le_opNorm _).trans (mul_le_mul_of_nonneg_left hbound (norm_nonneg ell))⟩

end EinsteinFull
