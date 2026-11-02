import EinsteinFull.Calculus.CLForwardLocality
import EinsteinFull.Calculus.CLTransposeComparison
import EinsteinFull.Calculus.C8EndpointTransposeProjection

/-! Large-time locality of the transpose endpoint, `paper/main.tex:715`, and
generic scalar and gradient local observations from a locally measurable
retained family with a differentiable orbit error. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull
open EinsteinRelation Blueprint

/-- A locally measurable retained family whose orbit error is differentiable and
small on the ball of radius two gives a local approximation of the class. -/
theorem clr_scalar_locality_of_family {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ρ εF : ℝ) (hεF : 0 ≤ εF) (U : Lp ℂ 2 (reducedLaw Q))
    (Vt : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hVt : @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
      (borel _) Vt)
    (hE : ∀ᵐ ω ∂reducedLaw Q, ∃ E : Vec d → ℂ, Differentiable ℝ E ∧
      (fun x => U (translate x ω) - Vt ω x) =ᵐ[volume] E ∧
      ∀ x, euclideanNorm x ≤ 2 →
        ‖E x‖ + Real.sqrt (∑ j, ‖fderiv ℝ E x (unitVector j)‖ ^ 2) ≤ εF) :
    ∃ V : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ ≤ 2 * εF := by
  refine c25_local_observation_of_retained_spatial_bound Q ρ εF 1 hεF one_pos U U
    (Lp.stronglyMeasurable _).measurable (ae_of_all _ fun _ => rfl) Vt hVt ?_
  filter_upwards [hE] with ω hEω
  obtain ⟨E, -, hEae, hEb⟩ := hEω
  filter_upwards [ae_restrict_of_ae hEae,
    ae_restrict_mem (PDE.isOpen_euclideanBall _ _).measurableSet] with x h1 hxB
  have hx1 : euclideanNorm x < 1 := clr_mem_unit_ball hxB
  have hx2 : euclideanNorm x ≤ 2 := le_of_lt (lt_trans hx1 (by norm_num))
  rw [h1]
  exact le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (hEb x hx2)

/-- The same family gives local approximations of every component of an actual
horizontal gradient of the class. -/
theorem clr_gradient_locality_of_family {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ρ εF : ℝ) (hεF : 0 ≤ εF) (W0 : Lp ℂ 2 (reducedLaw Q))
    (Vt : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hVt : @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
      (borel _) Vt)
    (hE : ∀ᵐ ω ∂reducedLaw Q, ∃ E : Vec d → ℂ, Differentiable ℝ E ∧
      (fun x => W0 (translate x ω) - Vt ω x) =ᵐ[volume] E ∧
      ∀ x, euclideanNorm x ≤ 2 →
        ‖E x‖ + Real.sqrt (∑ j, ‖fderiv ℝ E x (unitVector j)‖ ^ 2) ≤ εF)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) W0 G)
    (j : Fin d) :
    ∃ H : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ H ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖G j ω - H ω‖ ≤ 2 * (2 * εF) := by
  let := reducedLaw_probability Q
  set hs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hsdef
  have hspos (n : ℕ) : 0 < hs n := by simp only [hsdef]; positivity
  have hsle (n : ℕ) : hs n ≤ 1 := by
    simp only [hsdef]
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hstend : Tendsto hs atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
      exact (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden
    · exact Eventually.of_forall fun n => ne_of_gt (hspos n)
  let Qs := reducedLaw_stationary Q
  let U : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n =>
    ((hs n : ℝ) : ℂ)⁻¹ • (complexTranslation (reducedLaw Q) Qs (hs n • unitVector j) (W0) -
      W0)
  have hUlim : Tendsto U atTop (𝓝 (G j)) := (hG j).comp hstend
  have h2ε : 0 ≤ 2 * εF := by positivity
  apply clr_local_observation_of_tendsto Q ρ h2ε (G j) U hUlim
  intro n
  set h := hs n with hhdef
  have hh0 : 0 < h := hspos n
  have hh1 : h ≤ 1 := hsle n
  have hmp := measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector j)
  let Tl : Lp ℂ 2 (volume : Measure (Vec d)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
    Lp.compMeasurePreservingₗᵢ (p := 2) ℂ (fun x : Vec d => x + h • unitVector j) hmp
  let Vn : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) := fun ω =>
    ((h : ℝ) : ℂ)⁻¹ • (Tl (Vt ω) - Vt ω)
  have hVn : @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
      (borel _) Vn := by
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
    have hc0 : Continuous (fun L : Lp ℂ 2 (volume : Measure (Vec d)) => Tl L - L) :=
      Tl.continuous.sub continuous_id
    have hc : Continuous (fun L : Lp ℂ 2 (volume : Measure (Vec d)) =>
        ((h : ℝ) : ℂ)⁻¹ • (Tl L - L)) := hc0.const_smul (((h : ℝ) : ℂ)⁻¹)
    exact hc.measurable.comp hVt
  let F0 : FieldPair d → ℂ := fun ω => (W0) ω
  have hF0 : Measurable F0 := (Lp.stronglyMeasurable _).measurable
  let Fn : FieldPair d → ℂ := fun ω =>
    ((h : ℝ) : ℂ)⁻¹ * (F0 (translate (h • unitVector j) ω) - F0 ω)
  have hFn : Measurable Fn := by
    apply Measurable.const_mul
    exact (hF0.comp (Probability.continuous_translate.measurable.comp
      (measurable_const.prodMk measurable_id))).sub hF0
  have heFn : Fn =ᵐ[reducedLaw Q] (U n : FieldPair d → ℂ) := by
    filter_upwards [Lp.coeFn_smul (((h : ℝ) : ℂ)⁻¹)
        (complexTranslation (reducedLaw Q) Qs (h • unitVector j) (W0) - W0),
      Lp.coeFn_sub (complexTranslation (reducedLaw Q) Qs (h • unitVector j) (W0)) (W0),
      coeFn_complexTranslation (reducedLaw Q) Qs (h • unitVector j) (W0)] with ω h1 h2 h3
    change Fn ω = (((h : ℝ) : ℂ)⁻¹ • (complexTranslation (reducedLaw Q) Qs (h • unitVector j)
      (W0) - W0)) ω
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3]
    rfl
  refine c25_local_observation_of_retained_spatial_bound Q ρ εF 1 hεF one_pos (U n) Fn hFn
    heFn Vn hVn ?_
  filter_upwards [hE] with ω hEω
  obtain ⟨E, hEd, hEae, hEb⟩ := hEω
  have hEae' : (fun x => (W0) (translate (x + h • unitVector j) ω) -
      Vt ω (x + h • unitVector j)) =ᵐ[volume] fun x => E (x + h • unitVector j) :=
    hmp.quasiMeasurePreserving.ae_eq_comp hEae
  have hVnc : (Vn ω : Vec d → ℂ) =ᵐ[volume] fun x =>
      ((h : ℝ) : ℂ)⁻¹ * (Vt ω (x + h • unitVector j) - Vt ω x) := by
    filter_upwards [Lp.coeFn_smul (((h : ℝ) : ℂ)⁻¹) (Tl (Vt ω) - Vt ω),
      Lp.coeFn_sub (Tl (Vt ω)) (Vt ω), Lp.coeFn_compMeasurePreserving (Vt ω) hmp]
      with x h1 h2 h3
    change (((h : ℝ) : ℂ)⁻¹ • (Tl (Vt ω) - Vt ω)) x = _
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply]
    change ((h : ℝ) : ℂ)⁻¹ • ((Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector j)
      hmp (Vt ω)) x - (Vt ω) x) = _
    rw [h3]
    rfl
  have hgradb : ∀ y, euclideanNorm y ≤ 2 → ‖fderiv ℝ E y (unitVector j)‖ ≤ εF := by
    intro y hy
    have hj : ‖fderiv ℝ E y (unitVector j)‖ ≤
        Real.sqrt (∑ k : Fin d, ‖fderiv ℝ E y (unitVector k)‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun k _ => sq_nonneg
        ‖fderiv ℝ E y (unitVector k)‖) (Finset.mem_univ j))
    have := hEb y hy
    linarith [norm_nonneg (E y)]
  filter_upwards [ae_restrict_of_ae hEae, ae_restrict_of_ae hEae', ae_restrict_of_ae hVnc,
    ae_restrict_mem (PDE.isOpen_euclideanBall _ _).measurableSet] with x h1 h2 h3 hxB
  have hx1 : euclideanNorm x < 1 := clr_mem_unit_ball hxB
  have hinc := clr_coordinate_increment_le hEd j hgradb hx1.le hh0.le hh1
  have htr : translate (h • unitVector j) (translate x ω) =
      translate (x + h • unitVector j) ω := by
    rw [translate_add, add_comm]
  have hkey : Fn (translate x ω) - Vn ω x =
      ((h : ℝ) : ℂ)⁻¹ * (E (x + h • unitVector j) - E x) := by
    rw [h3]
    change ((h : ℝ) : ℂ)⁻¹ * ((W0) (translate (h • unitVector j) (translate x ω)) -
      (W0) (translate x ω)) - _ = _
    rw [htr]
    have e1 : E (x + h • unitVector j) = (W0) (translate (x + h • unitVector j) ω) -
        Vt ω (x + h • unitVector j) := h2.symm
    have e2 : E x = (W0) (translate x ω) - Vt ω x := h1.symm
    rw [e1, e2]
    ring
  rw [hkey, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
  calc h⁻¹ * ‖E (x + h • unitVector j) - E x‖ ≤ h⁻¹ * (εF * h) :=
        mul_le_mul_of_nonneg_left hinc (inv_nonneg.mpr hh0.le)
    _ = εF := by field_simp


/-- The far part of a Gaussian kernel integral of bounded data vanishing on a
ball of radius `r`, at centres within distance `r/2`. -/
theorem clr_far_kernel_tail_vanish {d : ℕ} (K : Vec d → Vec d → ℂ) (h : Vec d → ℂ)
    {A c t B r : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hK : ∀ x y, ‖K x y‖ ≤ A * Real.exp (-(c * euclideanNorm (x - y) ^ 2 / t)))
    (hh : ∀ᵐ y ∂volume, ‖h y‖ ≤ B) (hvan : ∀ᵐ y ∂volume, euclideanNorm y < r → h y = 0)
    (x : Vec d) (hx : euclideanNorm x ≤ r / 2)
    (hmeas : AEStronglyMeasurable (fun y => K x y * h y) volume) :
    Integrable (fun y => K x y * h y) volume ∧
    ‖∫ y, K x y * h y‖ ≤
      A * B * Real.exp (-(c * r ^ 2 / (8 * t))) * Real.sqrt (Real.pi / (c / (2 * t))) ^ d := by
  have hb : 0 < c / (2 * t) := by positivity
  apply clr_integral_le_gaussian_mass _ x _ _ hb hmeas
  filter_upwards [hh, hvan] with y hy hvy
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hK x y)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hB : 0 ≤ B := (norm_nonneg _).trans hy
  by_cases hyr : euclideanNorm y < r
  · rw [hvy hyr, mul_zero, norm_zero]
    positivity
  · have hy' : r ≤ euclideanNorm y := le_of_not_gt hyr
    have htri : euclideanNorm y ≤ euclideanNorm (y - x) + euclideanNorm x := by
      have h0 := TimeChange.euclideanNorm_add_le (y - x) x
      simpa only [sub_add_cancel] using h0
    have hs : euclideanNorm (y - x) = euclideanNorm (x - y) := by
      have h0 := TimeChange.euclideanNorm_smul (-1 : ℝ) (x - y)
      simpa [neg_sub] using h0
    rw [hs] at htri
    have hfar : r / 2 ≤ euclideanNorm (x - y) := by linarith
    have hr0 : 0 ≤ r / 2 := le_trans (by unfold euclideanNorm; exact Real.sqrt_nonneg _) hx
    have hsq : r ^ 2 / 4 ≤ euclideanNorm (x - y) ^ 2 := by
      nlinarith [pow_le_pow_left₀ hr0 hfar 2]
    have hsplit : Real.exp (-(c * euclideanNorm (x - y) ^ 2 / t)) ≤
        Real.exp (-(c * r ^ 2 / (8 * t))) *
          Real.exp (-(c / (2 * t)) * euclideanNorm (x - y) ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : c * r ^ 2 / (8 * t) ≤ c * euclideanNorm (x - y) ^ 2 / (2 * t) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ c * (8 * t))]
      have h2 : c * euclideanNorm (x - y) ^ 2 / t =
          c * euclideanNorm (x - y) ^ 2 / (2 * t) +
            (c / (2 * t)) * euclideanNorm (x - y) ^ 2 := by
        field_simp
        ring
      rw [h2]
      linarith
    calc ‖K x y * h y‖ = ‖K x y‖ * ‖h y‖ := norm_mul _ _
      _ ≤ (A * Real.exp (-(c * euclideanNorm (x - y) ^ 2 / t))) * B :=
          mul_le_mul (hK x y) hy (norm_nonneg _) (by positivity)
      _ ≤ (A * (Real.exp (-(c * r ^ 2 / (8 * t))) *
            Real.exp (-(c / (2 * t)) * euclideanNorm (x - y) ^ 2))) * B := by
          gcongr
      _ = A * B * Real.exp (-(c * r ^ 2 / (8 * t))) *
            Real.exp (-(c / (2 * t)) * euclideanNorm (x - y) ^ 2) := by ring

/-- A coordinate of a vector is bounded by its Euclidean norm. -/
theorem clr_abs_apply_le_euclideanNorm {d : ℕ} (v : Vec d) (j : Fin d) :
    |v j| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have := Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  simpa [sq] using this

/-- The reduced drift of a field with derivative bounds is bounded. -/
theorem clr_drift_bound_of_smooth {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (h : IsSmoothWithBounds M ω) (i : Fin d) (x : Vec d) :
    |(1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j (fun y => ω.1 y j i) x| ≤ d * M 1 := by
  obtain ⟨A, B, hA, hB, hAB, h1, -⟩ := h.2 1 le_rfl
  have hentry (j : Fin d) : |coordinateDerivative j (fun y => ω.1 y j i) x| ≤ A := by
    have hb := h1 x (fun _ => unitVector j) (unitVector i)
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
      euclideanNorm_unitVector, mul_one] at hb
    have hc := clr_abs_apply_le_euclideanNorm
      (Matrix.mulVec (fun a b => iteratedFDeriv ℝ 1 (fun y => ω.1 y a b) x
        (fun _ => unitVector j)) (unitVector i)) j
    have hmv : (Matrix.mulVec (fun a b => iteratedFDeriv ℝ 1 (fun y => ω.1 y a b) x
        (fun _ => unitVector j)) (unitVector i)) j =
        coordinateDerivative j (fun y => ω.1 y j i) x := by
      simp only [Matrix.mulVec, dotProduct, unitVector, iteratedFDeriv_one_apply]
      rw [Finset.sum_eq_single i]
      · simp [coordinateDerivative, unitVector]
      · intro b _ hb; simp [hb]
      · simp
    rw [hmv] at hc
    exact hc.trans hb
  have hsum : |∑ j : Fin d, coordinateDerivative j (fun y => ω.1 y j i) x| ≤ d * A := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin d, |coordinateDerivative j (fun y => ω.1 y j i) x|
        ≤ ∑ _j : Fin d, A := Finset.sum_le_sum fun j _ => hentry j
      _ = d * A := by simp
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : (d : ℝ) * A ≤ d * M 1 := mul_le_mul_of_nonneg_left (by linarith) hd0
  nlinarith [abs_nonneg (∑ j : Fin d, coordinateDerivative j (fun y => ω.1 y j i) x)]

/-- The actual transpose endpoint orbit of bounded stationary data is the
convolution with the swapped physical kernel, which carries the deterministic
Gaussian bounds. -/
theorem clr_transpose_orbit_kernel (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (B : ℝ), 0 ≤ B → (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) →
    ∀ (i : Fin d) (ζ : ℂ),
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ᵐ ω ∂reducedLaw Q,
      ∃ (S Sdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)))
        (H : ℝ≥0 → Vec d → Vec d → ℂ),
        IsPhysicalComplexSemigroup ω.1 i ζ S ∧
        IsPhysicalComplexTransposeSemigroup ω.1 i ζ S Sdag ∧
        (∀ g : Lp ℂ 2 (volume : Measure (Vec d)),
          (Sdag t g : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, H t x y * g y) ∧
        (∀ x y, ‖H t x y‖ ≤ C * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * euclideanNorm (x - y) ^ 2 / (t : ℝ))) ∧
        (∀ x, Continuous (fun y => H t x y)) ∧
        (∀ᵐ y ∂volume, ‖f (translate y ω)‖ ≤ B) ∧
        ((fun x => (Pdag t f) (translate x ω)) =ᵐ[volume]
          fun x => ∫ y, H t x y * f (translate y ω)) ∧
        (∀ x y (j : Fin d), ‖fderiv ℝ (fun z => H t z y) x (unitVector j)‖ ≤
          C * (2 + (t : ℝ)) ^ N *
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * euclideanNorm (x - y) ^ 2 / (t : ℝ))) ∧
        (∀ (h : Vec d → ℂ) (B' : ℝ), 0 ≤ B' → AEStronglyMeasurable h volume →
          (∀ᵐ y ∂volume, ‖h y‖ ≤ B') →
          Differentiable ℝ (fun x => ∫ y, H t x y * h y) ∧ ∀ x : Vec d,
            Integrable (fun y => H t x y * h y) ∧
            ∀ j : Fin d,
              Integrable (fun y => fderiv ℝ (fun z => H t z y) x (unitVector j) * h y) ∧
              fderiv ℝ (fun x => ∫ y, H t x y * h y) x (unitVector j) =
                ∫ y, fderiv ℝ (fun z => H t z y) x (unitVector j) * h y) := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  set Λa : ℝ := Real.exp (2 * D.ellipticity) * D.ellipticity with hΛadef
  have hΛa : 1 ≤ Λa := by
    have he : 1 ≤ Real.exp (2 * D.ellipticity) :=
      Real.one_le_exp (by linarith [D.one_le_ellipticity])
    rw [hΛadef]; nlinarith [D.one_le_ellipticity]
  obtain ⟨M, -, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  obtain ⟨C, c, N, hC, hc, hdet⟩ := clr_det_point_kernel_unit_all d hd Λa hΛa M
  refine ⟨C, c, N, hC, hc, ?_⟩
  intro Q hQ f B hB hf i ζ P Pdag hP hPdag t ht
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  obtain ⟨S, Sdag, hpair, _hm, _hSm, hSdagm⟩ :=
    crudeEnergy_ae_exists_measurable_physical_pair Q i ζ
  have hSdag := hpair.mono fun _ h => h.2
  obtain ⟨F, _hFm, hF, hconv⟩ :=
    crudeEnergy_exists_transpose_cutoff_gaussian_approximation_allLp hP hPdag f S Sdag
      hSdag hSdagm
  let L : ℝ := 64 * (Real.exp (2 * D.ellipticity) * D.ellipticity) ^ 3
  have happrox := hconv (t : ℝ) L (by linarith) (le_refl _)
  have horbit := ae_ae_stationary_orbit_le (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable f).measurable.norm hf
  filter_upwards [c4_ae_reduced_physical_elliptic Q, hsmooth Q hQ, horbit, hpair, hF, happrox]
    with ω hellω hsmω hfω hpairω hFω haω
  obtain ⟨K, hK, hreg⟩ := hdet ω hellω hsmω i ζ (S ω) (Sdag ω) hpairω.1 hpairω.2
  have hfm : AEStronglyMeasurable (fun y : Vec d => f (translate y ω)) volume :=
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hreg' := hreg (fun t x y => K t y x) (by simp) t ht
  have hb := hreg'.2.2 (fun y => f (translate y ω)) B hB hfm hfω
  have hKb : ∀ x y, ‖K t y x‖ ≤ C * (2 + (t : ℝ)) ^ N *
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * euclideanNorm (x - y) ^ 2 / (t : ℝ)) := by
    intro x y
    have h := hreg'.2.1 x y
    have h1 : 0 ≤ Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K t y z) x (unitVector j)‖ ^ 2) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K t z x) y (unitVector j)‖ ^ 2) :=
      Real.sqrt_nonneg _
    linarith
  have hKc : ∀ x, Continuous (fun y => K t y x) := by
    intro x
    have hc2 := hreg'.1.continuous
    exact hc2.comp (continuous_const.prodMk continuous_id)
  have hKg : ∀ x y (j : Fin d), ‖fderiv ℝ (fun z => K t y z) x (unitVector j)‖ ≤
      C * (2 + (t : ℝ)) ^ N *
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * euclideanNorm (x - y) ^ 2 / (t : ℝ)) := by
    intro x y j
    have h := hreg'.2.1 x y
    have hj : ‖fderiv ℝ (fun z => K t y z) x (unitVector j)‖ ≤
        Real.sqrt (∑ k : Fin d, ‖fderiv ℝ (fun z => K t y z) x (unitVector k)‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun k _ => sq_nonneg
        ‖fderiv ℝ (fun z => K t y z) x (unitVector k)‖) (Finset.mem_univ j))
    have h1 : 0 ≤ ‖K t y x‖ := norm_nonneg _
    have h2 : 0 ≤ Real.sqrt (∑ k : Fin d, ‖fderiv ℝ (fun z => K t z x) y (unitVector k)‖ ^ 2) :=
      Real.sqrt_nonneg _
    linarith
  have hdat : ∀ (h : Vec d → ℂ) (B' : ℝ), 0 ≤ B' → AEStronglyMeasurable h volume →
      (∀ᵐ y ∂volume, ‖h y‖ ≤ B') →
      Differentiable ℝ (fun x => ∫ y, K t y x * h y) ∧ ∀ x : Vec d,
        Integrable (fun y => K t y x * h y) ∧
        ∀ j : Fin d,
          Integrable (fun y => fderiv ℝ (fun z => K t y z) x (unitVector j) * h y) ∧
          fderiv ℝ (fun x => ∫ y, K t y x * h y) x (unitVector j) =
            ∫ y, fderiv ℝ (fun z => K t y z) x (unitVector j) * h y := by
    intro h B' hB' hm hhB
    have hb' := hreg'.2.2 h B' hB' hm hhB
    exact ⟨hb'.1, fun x => ⟨(hb'.2 x).1, fun j => (hb'.2 x).2.1 j⟩⟩
  have hSk : ∀ g : Lp ℂ 2 (volume : Measure (Vec d)),
      (Sdag ω t g : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K t y x * g y := by
    intro g
    have htpos : 0 < t := by exact_mod_cast (show (0 : ℝ) < t by linarith)
    exact (hK t htpos g).2.2
  refine ⟨S ω, Sdag ω, fun t x y => K t y x, hpairω.1, hpairω.2, hSk, hKb, hKc, hfω, ?_,
    hKg, hdat⟩
  apply crudeEnergy_physical_cutoff_kernel_identification hK.transpose
    (show 0 < t by exact_mod_cast (show (0 : ℝ) < t by linarith)) hFω
    (ae_of_all _ fun x => (hb.2 x).1) L
  · simpa using haω.1
  · simpa using haω.2

/-- For one environment: the transpose orbit minus the retained transpose
evolution is almost everywhere a differentiable function with value and gradient
bounds on the ball of radius two. The retained datum agrees with the orbit
datum on the retained ball. -/
theorem clr_transpose_retained_orbit_C1_error (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M M' : ℕ → ℝ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 → IsSmoothWithBounds M' ω' →
    ∀ (i : Fin d) (ζ : ℂ),
    ∀ (S Sdag Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ S →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ S Sdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ Pr →
      IsPhysicalComplexTransposeSemigroup ω'.1 i ζ Pr Prdag →
    ∀ (H : ℝ≥0 → Vec d → Vec d → ℂ) (t : ℝ≥0) (A k : ℝ), 1 ≤ (t : ℝ) → 0 < k →
      (∀ g : Lp ℂ 2 (volume : Measure (Vec d)),
        (Sdag t g : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, H t x y * g y) →
      (∀ x y, ‖H t x y‖ ≤ A * Real.exp (-(k * euclideanNorm (x - y) ^ 2 / t))) →
      (∀ x y (j : Fin d), ‖fderiv ℝ (fun z => H t z y) x (unitVector j)‖ ≤
        A * Real.exp (-(k * euclideanNorm (x - y) ^ 2 / t))) →
      (∀ (h : Vec d → ℂ) (B' : ℝ), 0 ≤ B' → AEStronglyMeasurable h volume →
        (∀ᵐ y ∂volume, ‖h y‖ ≤ B') →
        Differentiable ℝ (fun x => ∫ y, H t x y * h y) ∧ ∀ x : Vec d,
          Integrable (fun y => H t x y * h y) ∧
          ∀ j : Fin d,
            Integrable (fun y => fderiv ℝ (fun z => H t z y) x (unitVector j) * h y) ∧
            fderiv ℝ (fun x => ∫ y, H t x y * h y) x (unitVector j) =
              ∫ y, fderiv ℝ (fun z => H t z y) x (unitVector j) * h y) →
    ∀ (g : Vec d → ℂ) (B B' : ℝ), 0 ≤ B → 0 ≤ B' → AEStronglyMeasurable g volume →
      (∀ᵐ y ∂volume, ‖g y‖ ≤ B) →
    ∀ (r : ℝ), 12 ≤ r → (∀ x, euclideanNorm x < r → ω'.1 x = ω.1 x) →
    ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)), (∀ᵐ y ∂volume, ‖fr y‖ ≤ B') →
      (∀ᵐ y ∂volume, euclideanNorm y < r → fr y = g y) →
    ∀ o : Vec d → ℂ, o =ᵐ[volume] (fun x => ∫ y, H t x y * g y) →
    ∃ E : Vec d → ℂ, Differentiable ℝ E ∧
      (fun x => o x - (Prdag t fr) x) =ᵐ[volume] E ∧
      ∀ x, euclideanNorm x ≤ 2 →
        ‖E x‖ + Real.sqrt (∑ j, ‖fderiv ℝ E x (unitVector j)‖ ^ 2) ≤
          (1 + d) * (A * (B + B') * Real.exp (-(k * r ^ 2 / (8 * t))) *
            Real.sqrt (Real.pi / (k / (2 * t))) ^ d) +
          C * (2 + (t : ℝ)) * Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ 2 / t) * ‖fr‖ := by
  obtain ⟨C, c, hC, hc, hpt⟩ := clr_transpose_pointwise_all d Λ hΛ M M'
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω ω' hell hsmooth hell' hsmooth' i ζ S Sdag Pr Prdag hS hSdag hPr hPrdag H t A k
    ht hk hSk hKb hKg hdat g B B' hB hB' hg hgB r hr hagree fr hfrB hfrg o ho
  have htpos : 0 < (t : ℝ) := by linarith
  have htt : ((t : ℝ)).toNNReal = t := Real.toNNReal_coe
  obtain ⟨w, hwC1, hwae, hwb⟩ := hpt ω ω' hell hsmooth hell' hsmooth' i ζ S Sdag Pr Prdag
    hS hSdag hPr hPrdag 0 r (by linarith) (fun x hx => hagree x (by simpa using hx))
    (t : ℝ) ht fr
  rw [htt] at hwae
  have hwd : Differentiable ℝ w := hwC1.differentiable one_ne_zero
  have hfrm : AEStronglyMeasurable (fun y => fr y) volume := (Lp.aestronglyMeasurable fr)
  obtain ⟨hdg, hig⟩ := hdat g B hB hg hgB
  obtain ⟨hdf, hif⟩ := hdat (fun y => fr y) B' hB' hfrm hfrB
  have hhm : AEStronglyMeasurable (fun y => g y - fr y) volume := hg.sub hfrm
  have hhB : ∀ᵐ y ∂volume, ‖g y - fr y‖ ≤ B + B' := by
    filter_upwards [hgB, hfrB] with y h1 h2
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hvan : ∀ᵐ y ∂volume, euclideanNorm y < r → g y - fr y = 0 := by
    filter_upwards [hfrg] with y hy hyr
    rw [hy hyr, sub_self]
  obtain ⟨-, hi1⟩ := hdat (fun y => g y - fr y) (B + B') (by positivity) hhm hhB
  set ug : Vec d → ℂ := fun x => ∫ y, H t x y * g y with hugdef
  set uf : Vec d → ℂ := fun x => ∫ y, H t x y * fr y with hufdef
  let T : Vec d → ℂ := fun x => ug x - uf x
  have hTd : Differentiable ℝ T := hdg.sub hdf
  have hTval (x : Vec d) : T x = ∫ y, H t x y * (g y - fr y) := by
    change (∫ y, H t x y * g y) - (∫ y, H t x y * fr y) = _
    rw [← integral_sub (hig x).1 (hif x).1]
    congr 1; funext y; ring
  have hTder (x : Vec d) (j : Fin d) : fderiv ℝ T x (unitVector j) =
      ∫ y, fderiv ℝ (fun z => H t z y) x (unitVector j) * (g y - fr y) := by
    change fderiv ℝ (fun x => ug x - uf x) x (unitVector j) = _
    have hfun : (fun x => ug x - uf x) = ug - uf := rfl
    rw [hfun, fderiv_sub (hdg x) (hdf x), sub_apply, ((hig x).2 j).2,
      ((hif x).2 j).2, ← integral_sub ((hig x).2 j).1 ((hif x).2 j).1]
    congr 1; funext y; ring
  refine ⟨fun x => T x - w x, hTd.sub hwd, ?_, ?_⟩
  · have hsub := Lp.coeFn_sub (Prdag t fr) (Sdag t fr)
    filter_upwards [ho, hwae, hSk fr, hsub] with x hox hwx hSx hsx
    have hw' : w x = (Prdag t fr) x - (Sdag t fr) x := by rw [hwx, hsx, Pi.sub_apply]
    change o x - (Prdag t fr) x = (ug x - uf x) - w x
    rw [hw', hox, hSx]
    ring
  · intro x hx
    have hx' : euclideanNorm x ≤ r / 2 := by linarith
    set τ := A * (B + B') * Real.exp (-(k * r ^ 2 / (8 * t))) *
      Real.sqrt (Real.pi / (k / (2 * t))) ^ d with hτdef
    obtain ⟨-, htail⟩ := clr_far_kernel_tail_vanish (fun x y => H t x y) (fun y => g y - fr y)
      hk htpos hKb hhB hvan x hx' (hi1 x).1.aestronglyMeasurable
    rw [← hτdef] at htail
    have hτ0 : 0 ≤ τ := (norm_nonneg _).trans htail
    have hTx : ‖T x‖ ≤ τ := by rw [hTval]; exact htail
    have hTj (j : Fin d) : ‖fderiv ℝ T x (unitVector j)‖ ≤ τ := by
      rw [hTder]
      obtain ⟨-, h⟩ := clr_far_kernel_tail_vanish
        (fun x y => fderiv ℝ (fun z => H t z y) x (unitVector j)) (fun y => g y - fr y)
        hk htpos (fun x y => hKg x y j) hhB hvan x hx' ((hi1 x).2 j).1.aestronglyMeasurable
      rw [← hτdef] at h
      exact h
    have hwx := hwb x (by simp only [sub_zero]; linarith)
    set Wb := C * (2 + (t : ℝ)) * Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ 2 / t) * ‖fr‖
    have hTg : Real.sqrt (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) ≤ d * τ := by
      have h2 : (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) ≤ (d * τ) ^ 2 := by
        calc (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) ≤ ∑ _j : Fin d, τ ^ 2 :=
              Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hTj j) 2
          _ = d * τ ^ 2 := by simp
          _ ≤ (d * τ) ^ 2 := by
              rcases Nat.eq_zero_or_pos d with h | h
              · simp [h]
              · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h
                nlinarith [sq_nonneg τ]
      calc Real.sqrt (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) ≤ Real.sqrt ((d * τ) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = d * τ := Real.sqrt_sq (by positivity)
    have hderE (j : Fin d) : fderiv ℝ (fun x => T x - w x) x (unitVector j) =
        fderiv ℝ T x (unitVector j) - fderiv ℝ w x (unitVector j) := by
      have hfun : (fun x => T x - w x) = T - w := rfl
      rw [hfun, fderiv_sub (hTd x) (hwd x), sub_apply]
    have hgradE : Real.sqrt (∑ j, ‖fderiv ℝ (fun x => T x - w x) x (unitVector j)‖ ^ 2) ≤
        Real.sqrt (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) +
          Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2) := by
      refine le_trans ?_ (clr_sqrt_sum_sq_add_le (fun j => ‖fderiv ℝ T x (unitVector j)‖)
        (fun j => ‖fderiv ℝ w x (unitVector j)‖))
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro j _
      rw [hderE]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
    have hval : ‖T x - w x‖ ≤ τ + ‖w x‖ := (norm_sub_le _ _).trans (by linarith)
    calc ‖T x - w x‖ + Real.sqrt (∑ j, ‖fderiv ℝ (fun x => T x - w x) x (unitVector j)‖ ^ 2)
        ≤ (τ + ‖w x‖) + (d * τ + Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2)) := by
          linarith [hgradE, hTg]
      _ = (1 + d) * τ + (‖w x‖ + Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2)) := by
          ring
      _ ≤ (1 + d) * τ + Wb := by linarith [hwx]

/-- The retained drift vanishes on an open region where the cutoff vanishes. -/
theorem clr_retainedPair_drift_zero {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    {U : Set (Vec d)} (hU : IsOpen U) (hχ : ∀ y ∈ U, χ y = 0) {x : Vec d} (hx : x ∈ U)
    (i : Fin d) :
    (1 / 2 : ℝ) * ∑ j : Fin d,
        coordinateDerivative j (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x = 0 := by
  have hz (j : Fin d) :
      coordinateDerivative j (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x = 0 := by
    have he : (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) =ᶠ[𝓝 x]
        (fun _ => (1 : Mat d) j i) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact congrArg (fun A : Mat d => A j i)
        (ForcedLocality.retainedPair_fixed_at χ ω (hχ y hy)).1
    have hd : HasFDerivAt (fun y => (ForcedLocality.retainedPair χ ω).1 y j i)
        (0 : Vec d →L[ℝ] ℝ) x :=
      (hasFDerivAt_const ((1 : Mat d) j i) x).congr_of_eventuallyEq he
    change fderiv ℝ (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x (unitVector j) = 0
    rw [hd.fderiv, zero_apply]
  simp [hz]

/-- The locally measurable retained family of the transpose endpoint with
bounded force at large time, and the differentiable error of the actual orbit
on the ball of radius two. -/
theorem clr_transpose_retained_family
    (hcut : node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ (C₁ c₁ C₂ c₂ B₀ B₁ : ℝ) (N₁ : ℕ), 1 ≤ C₁ ∧ 0 < c₁ ∧ 1 ≤ C₂ ∧ 0 < c₂ ∧
      0 < B₀ ∧ 0 ≤ B₁ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ ρ : ℝ, 480 ≤ ρ →
    ∃ Vt : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
        (borel _) Vt ∧
      ∀ᵐ ω ∂reducedLaw Q, ∃ E : Vec d → ℂ, Differentiable ℝ E ∧
        (fun x => (Pdag t (β ⟨0, by omega⟩)) (translate x ω) - Vt ω x) =ᵐ[volume] E ∧
        ∀ x, euclideanNorm x ≤ 2 →
          ‖E x‖ + Real.sqrt (∑ j, ‖fderiv ℝ E x (unitVector j)‖ ^ 2) ≤
            (1 + d) * (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t) * (B₀ + B₁) *
              Real.exp (-(c₁ * (ρ / 40) ^ 2 / (8 * t))) *
              Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d) +
            C₂ * (2 + (t : ℝ)) * Real.exp (C₂ * ‖ζ‖ ^ 2 * t - c₂ * (ρ / 40) ^ 2 / t) *
              (B₁ * Real.sqrt (Real.exp 1 *
                Real.sqrt (Real.pi / (1 / (4 * (ρ / 20) ^ 2))) ^ d)) := by
  obtain ⟨Λc, Mc, Kc, hΛc, hMKc, χf, hχf, hret⟩ := hcut d D
  obtain ⟨C₁, c₁, N₁, hC₁, hc₁, hbridge⟩ := clr_transpose_orbit_kernel d hd D
  obtain ⟨B₀, hB₀, hdata⟩ := clr_initial_data_bound_all d hd D
  obtain ⟨M, -, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  set Λa : ℝ := Real.exp (2 * D.ellipticity) * D.ellipticity with hΛadef
  have hΛa : 1 ≤ Λa := by
    have he : 1 ≤ Real.exp (2 * D.ellipticity) :=
      Real.one_le_exp (by linarith [D.one_le_ellipticity])
    rw [hΛadef]; nlinarith [D.one_le_ellipticity]
  set Λ : ℝ := max Λa Λc with hΛdef
  have hΛ : 1 ≤ Λ := hΛa.trans (le_max_left _ _)
  obtain ⟨C₂, c₂, hC₂, hc₂, herr1⟩ := clr_transpose_retained_orbit_C1_error d Λ hΛ M Mc
  have hMc1 : 0 ≤ Mc 1 := (hMKc 1 le_rfl).1.le
  have hB₁ : 0 ≤ (d : ℝ) * Mc 1 := mul_nonneg (Nat.cast_nonneg d) hMc1
  refine ⟨C₁, c₁, C₂, c₂, B₀, d * Mc 1, N₁, hC₁, hc₁, hC₂, hc₂, hB₀, hB₁, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht ρ hρ
  let := reducedLaw_probability Q
  set r : ℝ := ρ / 40 with hrdef
  have hr12 : 12 ≤ r := by rw [hrdef]; linarith
  have hr1 : 1 ≤ r := by linarith
  obtain ⟨hχs, hχb, hχone, hχzero, -⟩ := hχf 0 r hr1
  let χ : C(Vec d, ℝ) := ⟨χf 0 r, hχs.continuous⟩
  have hχone' : ∀ y, euclideanNorm y ≤ r → χ y = 1 := fun y hy =>
    hχone y (by simpa using hy)
  have hχzero' : ∀ y, 2 * r ≤ euclideanNorm y → χ y = 0 := fun y hy =>
    hχzero y (by simpa using hy)
  have hcompact : HasCompactSupport χ := clr_hasCompactSupport_of_ball χ (2 * r) hχzero'
  let U : Set (Vec d) := {x : Vec d | euclideanNorm x < ρ}
  have hχU : ∀ x, x ∉ U → χ x = 0 := by
    intro x hx
    apply hχzero'
    simp only [U, Set.mem_ofPred_eq, not_lt] at hx
    linarith
  have hχsm : ContDiff ℝ (⊤ : ℕ∞) χ := hχs
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun k _ => (continuous_apply k).mul (continuous_apply k))
  obtain ⟨fr, Vf, hfrm, hVm, hefr, hact⟩ :=
    short_time_transpose_cutoff_measurable_evolution χ hχsm hcompact U hχU Λ hΛ
      ⟨0, by omega⟩ ζ
  have hVt : @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
      (borel _) (fun ω => Vf ω t) := hVm.comp (measurable_id.prodMk measurable_const)
  have hfB : ∀ᵐ ω ∂reducedLaw Q, ‖β ⟨0, by omega⟩ ω‖ ≤ B₀ :=
    (hdata Q hQ β a μ hβ ha hμ ζ).2.1 ⟨0, by omega⟩
  have hsp := short_time_transpose_drift_spatial_identification hβ ⟨0, by omega⟩
  refine ⟨fun ω => Vf ω t, hVt, ?_⟩
  filter_upwards [hbridge Q hQ (β ⟨0, by omega⟩) B₀ hB₀.le hfB ⟨0, by omega⟩ ζ P Pdag hP
    hPdag t ht, hret Q hQ, c4_ae_reduced_physical_elliptic Q, hsmooth Q hQ, hsp]
    with ω hbr hretω hellω hsmω hspω
  obtain ⟨S, Sdag, H, hS, hSdag, hSk, hKb, hKc, hgB, ho, hKg, hdat⟩ := hbr
  obtain ⟨ωloc, h1, h2, -, -, hellloc, -, hsmloc⟩ := hretω 0 r hr1
  have hloc : ωloc = ForcedLocality.retainedPair χ ω := by
    apply Prod.ext
    · ext x : 1
      rw [h1 x]
      rfl
    · ext x : 1
      rw [h2 x]
      rfl
  rw [hloc] at hellloc hsmloc
  have hellΛ : IsElliptic Λ ω.1 :=
    Calculus.S1.isElliptic_mono (by linarith) (le_max_left _ _) hellω
  have hellΛr : IsElliptic Λ (ForcedLocality.retainedPair χ ω).1 :=
    Calculus.S1.isElliptic_mono (by linarith) (le_max_right _ _) hellloc
  have hgood : ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    fun x => s5Elliptic_of_isElliptic hΛ hellΛr x
  obtain ⟨Pr, Prdag, hPr, hPrdag, -, -, hVeq⟩ := hact ω hgood
  have hfrB : ∀ᵐ y ∂volume, ‖fr ω y‖ ≤ d * Mc 1 := by
    filter_upwards [hefr ω hsmω.1] with y hy
    rw [hy, Complex.norm_real, Real.norm_eq_abs]
    exact clr_drift_bound_of_smooth hsmloc ⟨0, by omega⟩ y
  have hO : IsOpen {y : Vec d | euclideanNorm y < r} := isOpen_lt hnorm continuous_const
  have hfrg : ∀ᵐ y ∂volume, euclideanNorm y < r →
      fr ω y = β ⟨0, by omega⟩ (translate y ω) := by
    filter_upwards [hefr ω hsmω.1, hspω] with y h1 h2 hy
    rw [h1, h2]
    exact congrArg (fun q : ℝ => (q : ℂ)) (ForcedLocality.retainedPair_drift χ ω hO
      (fun y hy => hχone' y (le_of_lt hy)) hy _)
  have hO2 : IsOpen {y : Vec d | 2 * r < euclideanNorm y} := isOpen_lt continuous_const hnorm
  have hfr0 : ∀ᵐ y ∂volume, 2 * r < euclideanNorm y → fr ω y = 0 := by
    filter_upwards [hefr ω hsmω.1] with y hy hyr
    rw [hy]
    have := clr_retainedPair_drift_zero χ ω hO2 (fun y hy => hχzero' y (le_of_lt hy)) hyr
      ⟨0, by omega⟩
    rw [this, Complex.ofReal_zero]
  let χ' : Vec d → ℝ := fun y => if euclideanNorm y < 4 * r then 1 else 0
  have hχ'b : ∀ y, 0 ≤ χ' y ∧ χ' y ≤ 1 := by
    intro y; by_cases hy : euclideanNorm y < 4 * r <;> simp [χ', hy]
  have hχ'0 : ∀ y, 2 * (2 * r) ≤ euclideanNorm y → χ' y = 0 := by
    intro y hy
    have : ¬ euclideanNorm y < 4 * r := by linarith
    simp [χ', this]
  have hfrχ : (fr ω : Vec d → ℂ) =ᵐ[volume] fun y => (χ' y : ℂ) * fr ω y := by
    filter_upwards [hfr0] with y hy
    by_cases hy4 : euclideanNorm y < 4 * r
    · simp [χ', hy4]
    · have : 2 * r < euclideanNorm y := by linarith [not_lt.mp hy4]
      rw [hy this]; simp
  have hfrn := clr_cutoff_data_norm_le (fr ω) χ' (fun y => fr ω y) (by linarith : 0 < 2 * r)
    hfrχ hfrB hχ'b hχ'0
  have hagree : ∀ x, euclideanNorm x < r → (ForcedLocality.retainedPair χ ω).1 x = ω.1 x :=
    fun x hx => (ForcedLocality.retainedPair_eq_at χ ω (hχone' x hx.le)).1
  have hgm : AEStronglyMeasurable (fun y : Vec d => β ⟨0, by omega⟩ (translate y ω)) volume :=
    ((Lp.stronglyMeasurable _).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hexp (x y : Vec d) : C₁ * (2 + (t : ℝ)) ^ N₁ *
      Real.exp (C₁ * ‖ζ‖ ^ 2 * (t : ℝ) - c₁ * euclideanNorm (x - y) ^ 2 / (t : ℝ)) =
      (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t)) *
        Real.exp (-(c₁ * euclideanNorm (x - y) ^ 2 / t)) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  have hKb' : ∀ x y, ‖H t x y‖ ≤ (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t)) *
      Real.exp (-(c₁ * euclideanNorm (x - y) ^ 2 / t)) := fun x y =>
    (hKb x y).trans (le_of_eq (hexp x y))
  have hKg' : ∀ x y (j : Fin d), ‖fderiv ℝ (fun z => H t z y) x (unitVector j)‖ ≤
      (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t)) *
        Real.exp (-(c₁ * euclideanNorm (x - y) ^ 2 / t)) := fun x y j =>
    (hKg x y j).trans (le_of_eq (hexp x y))
  obtain ⟨E, hEd, hEae, hEb⟩ := herr1 ω (ForcedLocality.retainedPair χ ω) hellΛ hsmω hellΛr
    hsmloc ⟨0, by omega⟩ ζ S Sdag Pr Prdag hS hSdag hPr hPrdag H t _ c₁ ht hc₁ hSk hKb'
    hKg' hdat (fun y => β ⟨0, by omega⟩ (translate y ω)) B₀ (d * Mc 1) hB₀.le hB₁ hgm hgB
    r hr12 hagree (fr ω) hfrB hfrg (fun x => (Pdag t (β ⟨0, by omega⟩)) (translate x ω)) ho
  refine ⟨E, hEd, ?_, ?_⟩
  · simpa only [hVeq t] using hEae
  · intro x hx
    refine (hEb x hx).trans ?_
    have hr2 : 2 * r = ρ / 20 := by rw [hrdef]; ring
    rw [hr2] at hfrn
    exact add_le_add (le_of_eq rfl) (mul_le_mul_of_nonneg_left hfrn (by positivity))

end EinsteinFull
