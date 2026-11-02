import EinsteinFull.Calculus.C19FirstUnitGradientProjection

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The actual retained transpose evolution supplies one jointly local scalar
primitive with the Gaussian error of the original stationary primitive. -/
theorem c19_actual_local_transpose_primitive_comparison
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ L K c : ℝ, 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β →
    ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ‖ζ‖ ≤ 2 →
    ∀ ρ : ℝ, 1 ≤ ρ → ∃ H : FieldPair d → Vec d → ℂ,
      @Measurable _ _ ((localSigma {x : Vec d | euclideanNorm x < ρ}).prod
        inferInstance) inferInstance (Function.uncurry H) ∧
      Measurable (Function.uncurry H) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
          ‖(∫ s in Icc (0 : ℝ) 1, Pdag s.toNNReal (β ⟨0, by omega⟩))
            (translate x ω) - H ω x‖ ^ 2) ∧
        (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖(∫ s in Icc (0 : ℝ) 1, Pdag s.toNNReal (β ⟨0, by omega⟩))
            (translate x ω) - H ω x‖ ^ 2) ≤ K * Real.exp (-c * ρ ^ 2) := by
  let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
  let L := 64 * Λ ^ 3
  have hΛ : 1 ≤ Λ := one_le_mul_of_one_le_of_one_le
    (Real.one_le_exp (by linarith [D.one_le_ellipticity])) D.one_le_ellipticity
  have hLp : 0 < L := by dsimp only [L]; positivity
  obtain ⟨Cχ, hCχ, hcut⟩ := short_time_compatible_euclidean_cutoffs d
  obtain ⟨K, c, hK, hc, hdecay⟩ :=
    c19_transpose_retained_scalar_gaussian_decay d hd D L le_rfl hLp Cχ hCχ.le
  refine ⟨L, K, c, hLp, hK, hc, ?_⟩
  intro Q hQ β hβ ζ P Pdag hP hPd hζ ρ hρ
  obtain ⟨χ, θ, hχ, hθ, hcχ, hcθ, hχb, hθb, hχone, hχzero, hθzero,
    hθone, hχsupport, hθsupport, hχder, hθder⟩ := hcut ρ (zero_lt_one.trans_le hρ)
  let U := {x : Vec d | euclideanNorm x < ρ}
  have hsupport : ∀ x, x ∉ U → χ x = 0 := by
    intro x hx
    exact hχzero x (by have hh : ρ ≤ euclideanNorm x := not_lt.mp hx; linarith)
  obtain ⟨fr, V, hfr, hV, hefr, hactual⟩ :=
    short_time_transpose_cutoff_measurable_evolution χ hχ hcχ U hsupport Λ hΛ
      ⟨0, by omega⟩ ζ
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) :=
    Lp.SecondCountableTopology
  let v : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun ω => ∫ s in Icc (0 : ℝ) 1, V ω s.toNNReal
  have hv : @StronglyMeasurable _ _ _ (localSigma U) v := by
    let : MeasurableSpace (FieldPair d) := localSigma U
    have hm : @StronglyMeasurable _ _ _ ((localSigma U).prod inferInstance)
        (fun p : FieldPair d × ℝ => V p.1 p.2.toNNReal) :=
      hV.stronglyMeasurable.comp_measurable
        (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd))
    exact hm.integral_prod_right'
  obtain ⟨H, hH, heH⟩ := @c19_joint_l2_representative (FieldPair d) (Vec d)
    (localSigma U) inferInstance volume v hv
  have hmId : @Measurable (FieldPair d) (FieldPair d) inferInstance (localSigma U) id :=
    fun s hs => Probability.localSigma_le_borel U s hs
  have hmProd : @Measurable (FieldPair d × Vec d) (FieldPair d × Vec d)
      inferInstance ((localSigma U).prod inferInstance) id :=
    (hmId.comp measurable_fst).prodMk measurable_snd
  have hHb : Measurable H := hH.comp hmProd
  have hfrb : StronglyMeasurable fr := (hfr.comp hmId).stronglyMeasurable
  have hVb : StronglyMeasurable (Function.uncurry V) :=
    (hV.comp ((hmId.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  obtain ⟨M, _, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hinit : ∀ᵐ ω ∂reducedLaw Q, (fr ω : Vec d → ℂ) =ᵐ[volume]
      fun x => (((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
        (fun y => (ForcedLocality.retainedPair χ ω).1 y k ⟨0, by omega⟩) x : ℝ) : ℂ) := by
    filter_upwards [hsmooth Q hQ] with ω hsω
    exact hefr ω hsω.1
  have hact : ∀ᵐ ω ∂reducedLaw Q,
      ∃ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1
          ⟨0, by omega⟩ ζ Pr Tr ∧ ∀ s, V ω s = Tr s (fr ω) := by
    filter_upwards [c19_retained_coefficients_admissible Q] with ω hω
    obtain ⟨Pr, Tr, hPr, hTr, _, _, heV⟩ := hactual ω (hω χ hχb).2
    exact ⟨Pr, Tr, hTr, heV⟩
  have hplateau : ∀ x, euclideanSq x < (ρ / 4) ^ 2 → χ x = 1 := by
    intro x hx
    apply hχone
    change Real.sqrt (euclideanSq x) ≤ ρ / 4
    exact (Real.sqrt_le_iff).mpr ⟨by positivity, hx.le⟩
  have hdec := hdecay Q hQ β hβ ⟨0, by omega⟩ ζ P Pdag hP hPd hζ
    χ hχ hχb ρ hρ hplateau hχzero hχder fr V hfrb hVb hinit hact 1 (by norm_num)
  simp only [NNReal.coe_one] at hdec
  refine ⟨fun ω x => H (ω, x), hH, hHb, ?_⟩
  filter_upwards [hdec] with ω hω
  have he : (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
      ‖(∫ s in Icc (0 : ℝ) 1, Pdag s.toNNReal (β ⟨0, by omega⟩))
        (translate x ω) - H (ω, x)‖ ^ 2) =ᵐ[volume]
      (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(∫ s in Icc (0 : ℝ) 1, Pdag s.toNNReal (β ⟨0, by omega⟩))
          (translate x ω) - v ω x‖ ^ 2) := by
    filter_upwards [heH ω] with x hx
    rw [hx]
  exact ⟨hω.1.1.congr he.symm, (integral_congr_ae he).trans_le hω.1.2⟩

/-- Scalar observations use the same Euclidean projection transfer by repeating
the scalar in every coordinate and then selecting one coordinate of the error. -/
theorem c19_scalar_projection_error_of_gaussian_local_error
    {d : ℕ} (i : Fin d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℂ 2 (reducedLaw Q)) (U S : Set (Vec d)) (R L ε : ℝ)
    (hL : 0 < L) (hS : MeasurableSet S) (hvol : 0 < volume S)
    (hvoltop : volume S ≠ ∞) (hsmall : ∀ x ∈ S, euclideanSq x ≤ 1)
    (hshift : ∀ x ∈ S, ∀ y ∈ U, -x + y ∈ {z : Vec d | euclideanNorm z < R})
    (H : FieldPair d → Vec d → ℂ)
    (hH : @Measurable _ _ ((localSigma U).prod inferInstance) inferInstance
      (Function.uncurry H))
    (hHb : Measurable (Function.uncurry H))
    (herror : ∀ᵐ ω ∂reducedLaw Q,
      Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖f (translate x ω) - H ω x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖f (translate x ω) - H ω x‖ ^ 2) ≤ ε) :
    ‖f - C9ShortTimeLocality.localProjection Q R f‖ ≤
      2 * Real.sqrt ((Real.exp (2 / L) / (volume S).toReal) * ((d : ℝ) * ε)) := by
  have he : ∀ᵐ ω ∂reducedLaw Q,
      Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ∑ _j : Fin d, ‖f (translate x ω) - H ω x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ∑ _j : Fin d, ‖f (translate x ω) - H ω x‖ ^ 2) ≤ (d : ℝ) * ε := by
    filter_upwards [herror] with ω hω
    have heq : (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ∑ _j : Fin d, ‖f (translate x ω) - H ω x‖ ^ 2) =
        (fun x => (d : ℝ) * (Real.exp (-euclideanSq x / L) ^ 2 *
          ‖f (translate x ω) - H ω x‖ ^ 2)) := by
      funext x
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [heq]
    exact ⟨hω.1.const_mul _, (integral_const_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left hω.2 (Nat.cast_nonneg d))⟩
  have hHv : @Measurable (FieldPair d × Vec d) (Fin d → ℂ)
      ((localSigma U).prod inferInstance) inferInstance
      (fun p _j => H p.1 p.2) := by
    let : MeasurableSpace (FieldPair d) := localSigma U
    exact Measurable.of_eval fun _ => hH
  have hp := c19_projection_error_of_gaussian_local_error Q (fun _j => f)
    U S R L ((d : ℝ) * ε) hL hS hvol hvoltop hsmall hshift
    (fun ω x _j => H ω x) hHv
    (Measurable.of_eval fun _ => hHb) he
  apply le_trans _ hp
  calc
    ‖f - C9ShortTimeLocality.localProjection Q R f‖ =
        Real.sqrt (‖f - C9ShortTimeLocality.localProjection Q R f‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ _j : Fin d, ‖f - C9ShortTimeLocality.localProjection Q R f‖ ^ 2) :=
      Real.sqrt_le_sqrt (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

/-- The force-weighted first-unit transpose primitive has a structural Gaussian
localization error for the joint coefficient and clock projection. -/
theorem c19_first_unit_transpose_projection_error : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ‖ζ‖ ≤ 2 → ∀ n : ℕ, 1 ≤ n → ‖((-2 * ζ) • (∫ s in Set.Icc (0 : ℝ) 1, transposeEndpoint Q ⟨0, by omega⟩ Pdag β s.toNNReal)) - C9ShortTimeLocality.localProjection Q (C * (n : ℝ)) ((-2 * ζ) • (∫ s in Set.Icc (0 : ℝ) 1, transposeEndpoint Q ⟨0, by omega⟩ Pdag β s.toNNReal))‖ ≤ C * Real.exp (-c * (n : ℝ) ^ 2) := by
  intro d hd D
  obtain ⟨L, K, c₀, hL, hK, hc₀, hlocalerror⟩ :=
    c19_actual_local_transpose_primitive_comparison d hd D
  let S := PDE.euclideanBall (0 : PDE.Vec d) 1
  let A := Real.exp (2 / L) / (volume S).toReal
  let C := 2 + 8 * Real.sqrt (A * ((d : ℝ) * K))
  have hA : 0 < A := div_pos (Real.exp_pos _) (ENNReal.toReal_pos
    (PDE.volume_euclideanBall_pos _ zero_lt_one).ne'
    (PDE.volume_euclideanBall_ne_top _ zero_le_one))
  have hC : 2 ≤ C := by dsimp only [C]; linarith [Real.sqrt_nonneg (A * ((d : ℝ) * K))]
  refine ⟨C, c₀ / 2, by linarith, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd hζ n hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨H, hH, hHb, he⟩ := hlocalerror Q hQ β hβ ζ P Pdag hP hPd hζ (n : ℝ) hn'
  have hsq : ∀ x ∈ S, euclideanSq x < 1 := by
    intro x hx
    simpa only [S, PDE.euclideanBall, Set.mem_ofPred_eq, PDE.euclideanSqDist,
      sub_zero, PDE.vecNormSq, PDE.vecDot, euclideanSq, dot, one_pow] using hx
  have hsmall : ∀ x ∈ S, euclideanSq x ≤ 1 := fun x hx => (hsq x hx).le
  have hshift : ∀ x ∈ S, ∀ y ∈ {z : Vec d | euclideanNorm z < (n : ℝ)},
      -x + y ∈ {z : Vec d | euclideanNorm z < C * (n : ℝ)} := by
    intro x hx y hy
    have hx' : euclideanNorm x < 1 := by
      change Real.sqrt (euclideanSq x) < 1
      exact (Real.sqrt_lt' zero_lt_one).mpr (by simpa only [one_pow] using hsq x hx)
    have htri := TimeChange.euclideanNorm_add_le (-x) y
    rw [Entropy.euclideanNorm_neg'] at htri
    change euclideanNorm y < (n : ℝ) at hy
    change euclideanNorm (-x + y) < C * (n : ℝ)
    nlinarith
  let u := ∫ s in Icc (0 : ℝ) 1, Pdag s.toNNReal (β ⟨0, by omega⟩)
  have hp := c19_scalar_projection_error_of_gaussian_local_error ⟨0, by omega⟩ Q u
    {x : Vec d | euclideanNorm x < (n : ℝ)} S (C * (n : ℝ)) L
    (K * Real.exp (-c₀ * (n : ℝ) ^ 2)) hL
    (PDE.isOpen_euclideanBall _ _).measurableSet
    (PDE.volume_euclideanBall_pos _ zero_lt_one)
    (PDE.volume_euclideanBall_ne_top _ zero_le_one) hsmall hshift H hH hHb he
  have hexp : Real.sqrt (Real.exp (-c₀ * (n : ℝ) ^ 2)) =
      Real.exp (-(c₀ / 2) * (n : ℝ) ^ 2) := by
    rw [← Real.exp_half]
    congr 1
    ring
  have hroot : ‖u - C9ShortTimeLocality.localProjection Q (C * (n : ℝ)) u‖ ≤
      2 * Real.sqrt (A * ((d : ℝ) * K)) * Real.exp (-(c₀ / 2) * (n : ℝ) ^ 2) := by
    apply hp.trans_eq
    change 2 * Real.sqrt (A * ((d : ℝ) * (K * Real.exp (-c₀ * (n : ℝ) ^ 2)))) = _
    rw [← mul_assoc (d : ℝ), ← mul_assoc, Real.sqrt_mul (by positivity), hexp]
    ring
  change ‖(-2 * ζ) • u - C9ShortTimeLocality.localProjection Q (C * (n : ℝ))
    ((-2 * ζ) • u)‖ ≤ _
  rw [map_smul, ← smul_sub, norm_smul]
  have hforce : ‖(-2 : ℂ) * ζ‖ ≤ 4 := by
    rw [norm_mul]
    norm_num only [norm_neg, Complex.norm_ofNat]
    linarith
  calc
    _ ≤ 4 * (2 * Real.sqrt (A * ((d : ℝ) * K)) *
        Real.exp (-(c₀ / 2) * (n : ℝ) ^ 2)) :=
      mul_le_mul hforce hroot (norm_nonneg _) (by norm_num)
    _ = (8 * Real.sqrt (A * ((d : ℝ) * K))) *
        Real.exp (-(c₀ / 2) * (n : ℝ) ^ 2) := by ring
    _ ≤ C * Real.exp (-(c₀ / 2) * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (Real.exp_nonneg _)

end EinsteinFull.Blueprint
