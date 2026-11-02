import EinsteinFull.Calculus.U4PhysicalGeneratorH2

open EinsteinRelation MeasureTheory
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull

/-- Compactness step for third weak derivatives of a supplied Hessian.
The quotient estimate is the analytic input still needed from the differentiated
physical generator equation. -/
theorem u4h3_physical_H3_of_hessian_quotient_bounds {d : ℕ}
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hfirst : ∀ j, (∑ k, ‖H j k‖ ^ 2) ≤ E)
    (hquotient : ∀ (j l : Fin d) (h : ℝ), 0 < |h| → |h| ≤ 1 →
      (∑ k, ((eLpNorm
        (fun x => (H j k (x + h • unitVector l) - H j k x) / (h : ℂ))
        2 (volume : Measure (Vec d))).toReal) ^ 2) ≤ B * E) :
    ∃ K : Fin d → Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j k, IsPhysicalH1Graph volume (Or.inl rfl) (H j k) (K j k)) ∧
      (∑ j, ∑ k, ∑ l, ‖K j k l‖ ^ 2) ≤
        (d : ℝ) * (1 + (d : ℝ) * (1 + B)) * E := by
  classical
  have hex : ∀ j, ∃ K : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ k, IsPhysicalH1Graph volume (Or.inl rfl) (H j k) (K k)) ∧
      (∑ k, ∑ l, ‖K k l‖ ^ 2) ≤ (1 + (d : ℝ) * (1 + B)) * E := by
    intro j
    obtain ⟨K, hK, hb⟩ := u4h2_physical_H2_of_separate_energy_bounds
      (G j) (H j) (hH j) 1 B E (by positivity) hB hE
      (by simpa using hfirst j) (hquotient j)
    refine ⟨K, hK, ?_⟩
    have hn : 0 ≤ ∑ k, ‖H j k‖ ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    linarith
  choose K hK hb using hex
  refine ⟨K, hK, ?_⟩
  calc
    (∑ j, ∑ k, ∑ l, ‖K j k l‖ ^ 2) ≤
        ∑ _j : Fin d, (1 + (d : ℝ) * (1 + B)) * E :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = (d : ℝ) * (1 + (d : ℝ) * (1 + B)) * E := by simp; ring

private theorem u4h3_unit_euclidean {d : ℕ} (i : Fin d) :
    euclideanNorm (unitVector i) = 1 := by
  change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

/-- The second structural derivative controls each mixed coordinate derivative
of the actual physical coefficient field. -/
theorem u4h3_coefficient_second_derivative_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l m j k : Fin d) (x : Vec d) :
    |coordinateDerivative l (coordinateDerivative m (fun y => ω.1 y j k)) x| ≤ M 2 := by
  let v : Fin 2 → Vec d := Fin.cons (unitVector l) (fun _ => unitVector m)
  have hv : ∀ t, euclideanNorm (v t) = 1 := by
    intro t
    refine Fin.cases ?_ (fun s => ?_) t
    · exact u4h3_unit_euclidean l
    · exact u4h3_unit_euclidean m
  obtain ⟨A, B, _, hB, hAB, hA, _⟩ := hsmooth.2 2 (by norm_num)
  have hb := hA x v (unitVector k)
  simp only [hv, Finset.prod_const_one, u4h3_unit_euclidean, mul_one] at hb
  have hc := Regeneration.coordinate_abs_le_euclideanNorm
    (Matrix.mulVec (fun j k => iteratedFDeriv ℝ 2
      (fun y => ω.1 y j k) x v) (unitVector k)) j
  have he (N : Mat d) : (N.mulVec (unitVector k)) j = N j k := by
    change dotProduct (fun q => N j q) (Pi.single k 1) = _
    rw [dotProduct_single, mul_one]
  erw [he] at hc
  have hid : coordinateDerivative l (coordinateDerivative m (fun y => ω.1 y j k)) x =
      iteratedFDeriv ℝ 2 (fun y => ω.1 y j k) x v := by
    rw [iteratedFDeriv_two_apply]
    change fderiv ℝ (fun y => fderiv ℝ (fun z => ω.1 z j k) y (unitVector m)) x
      (unitVector l) = _
    have hd := ((contDiff_infty_iff_fderiv.mp (hsmooth.1.1 j k)).2.differentiable (by simp)) x
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp [v]
  rw [hid]
  exact (hc.trans hb).trans (by linarith)

/-- Coordinate translations of a first coefficient derivative are uniformly
controlled by the actual second structural derivative bound. -/
theorem u4h3_coefficient_derivative_translation_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l m j k : Fin d) (x : Vec d) (h : ℝ) :
    |coordinateDerivative m (fun y => ω.1 y j k) (x + h • unitVector l) -
      coordinateDerivative m (fun y => ω.1 y j k) x| ≤ M 2 * |h| := by
  let D := coordinateDerivative m (fun y => ω.1 y j k)
  let F : ℝ → ℝ := fun t => D (x + t • unitVector l)
  have hD : ContDiff ℝ (⊤ : ℕ∞) D :=
    (contDiff_infty_iff_fderiv.mp (hsmooth.1.1 j k)).2.clm_apply contDiff_const
  have hF (t : ℝ) : HasDerivAt F
      (coordinateDerivative l D (x + t • unitVector l)) t := by
    have ht := ((hasDerivAt_id' t).smul_const (unitVector l)).const_add x
    simpa only [F, coordinateDerivative, Function.comp_def, one_smul] using
      ((hD.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t ht)
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := h)
    (fun t _ => (hF t).hasDerivWithinAt)
    (fun t _ => by
      simpa only [D, Real.norm_eq_abs] using
        u4h3_coefficient_second_derivative_bound hsmooth l m j k (x + t • unitVector l))
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ _) (Set.mem_univ _)
  simpa [F, D, Real.norm_eq_abs] using hb

/-- Mixed coefficient differences obey the structural second derivative bound,
with both signed translation steps retained. -/
theorem u4h3_coefficient_mixed_difference_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l m j k : Fin d) (x : Vec d) (h s : ℝ) :
    |(ω.1 ((x + s • unitVector m) + h • unitVector l) j k -
        ω.1 (x + s • unitVector m) j k) -
      (ω.1 (x + h • unitVector l) j k - ω.1 x j k)| ≤
        (M 2 * |h|) * |s| := by
  let F : ℝ → ℝ := (fun t => ω.1 ((x + t • unitVector m) + h • unitVector l) j k) -
    (fun t => ω.1 (x + t • unitVector m) j k)
  have hF (t : ℝ) : HasDerivAt F
      (coordinateDerivative m (fun y => ω.1 y j k) ((x + t • unitVector m) + h • unitVector l) -
       coordinateDerivative m (fun y => ω.1 y j k) (x + t • unitVector m)) t := by
    have ht := ((hasDerivAt_id' t).smul_const (unitVector m)).const_add x
    have hc := (hsmooth.1.1 j k).differentiable (by simp)
    have hleft := (hc ((x + t • unitVector m) + h • unitVector l)).hasFDerivAt.comp_hasDerivAt t
      (ht.add_const (h • unitVector l))
    have hright := (hc (x + t • unitVector m)).hasFDerivAt.comp_hasDerivAt t ht
    simpa only [F, coordinateDerivative, Function.comp_def, one_smul, Pi.sub_apply] using hleft.sub hright
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := s)
    (fun t _ => (hF t).hasDerivWithinAt)
    (fun t _ => by
      simpa only [Real.norm_eq_abs] using
        u4h3_coefficient_derivative_translation_bound hsmooth l m j k (x + t • unitVector m) h)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ _) (Set.mem_univ _)
  simpa [F, Real.norm_eq_abs] using hb

/-- The normalized mixed coefficient commutator is bounded uniformly in both
nonzero signed steps. -/
theorem u4h3_coefficient_mixed_quotient_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l m j k : Fin d) (x : Vec d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0) :
    |((ω.1 ((x + s • unitVector m) + h • unitVector l) j k -
        ω.1 (x + s • unitVector m) j k) -
      (ω.1 (x + h • unitVector l) j k - ω.1 x j k)) / h / s| ≤ M 2 := by
  rw [abs_div, abs_div]
  calc
    _ ≤ ((M 2 * |h|) * |s|) / |h| / |s| :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right
          (u4h3_coefficient_mixed_difference_bound hsmooth l m j k x h s) (abs_nonneg h))
        (abs_nonneg s)
    _ = M 2 := by field_simp

/-- A mixed coefficient commutator acts on physical L² with norm controlled
by the structural second derivative bound. -/
theorem u4h3_coefficient_mixed_quotient_multiplier {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l m j k : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) j k -
           ω.1 (x + s • unitVector m) j k -
          (ω.1 (x + h • unitVector l) j k - ω.1 x j k)) / h / s : ℝ) : ℂ) * u x) ∧
      ‖v‖ ≤ M 2 * ‖u‖ := by
  let w : Vec d → ℝ := fun x =>
    (ω.1 ((x + s • unitVector m) + h • unitVector l) j k -
      ω.1 (x + s • unitVector m) j k -
      (ω.1 (x + h • unitVector l) j k - ω.1 x j k)) / h / s
  have hw : Measurable w := by
    apply Continuous.measurable
    exact (((((hsmooth.1.1 j k).continuous.comp
      ((continuous_id.add continuous_const).add continuous_const)).sub
      ((hsmooth.1.1 j k).continuous.comp (continuous_id.add continuous_const))).sub
      (((hsmooth.1.1 j k).continuous.comp (continuous_id.add continuous_const)).sub
        (hsmooth.1.1 j k).continuous)).div_const h).div_const s
  have hM : 0 ≤ M 2 := by
    obtain ⟨A, B, hA, hB, hAB, _⟩ := hsmooth.2 2 (by norm_num)
    linarith
  have hb : ∀ x, |w x| ≤ M 2 := fun x =>
    u4h3_coefficient_mixed_quotient_bound hsmooth l m j k x hh hs
  let v := (s5_memLp_mul hw hb u).toLp (fun x => (w x : ℂ) * u x)
  refine ⟨v, (s5_memLp_mul hw hb u).coeFn_toLp, ?_⟩
  rw [Lp.norm_toLp, Lp.norm_def]
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Vec d)))
      (f := fun x => (w x : ℂ) * u x) (g := (u : Vec d → ℂ)) (c := M 2)
      ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)) 2
  calc (eLpNorm (fun x => (w x : ℂ) * u x) 2 volume).toReal
      ≤ (ENNReal.ofReal (M 2) * eLpNorm (u : Vec d → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u)) he
    _ = M 2 * (eLpNorm (u : Vec d → ℂ) 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

/-- The mixed coefficient commutator has an integrable L² pairing and the
uniform structural bound needed by the second energy estimate. -/
theorem u4h3_coefficient_mixed_quotient_pairing {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l m j k : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    let w : Vec d → ℝ := fun x =>
      (ω.1 ((x + s • unitVector m) + h • unitVector l) j k -
        ω.1 (x + s • unitVector m) j k -
        (ω.1 (x + h • unitVector l) j k - ω.1 x j k)) / h / s
    Integrable (fun x => (w x : ℂ) * u x * star (v x)) volume ∧
      ‖∫ x, (w x : ℂ) * u x * star (v x)‖ ≤ M 2 * ‖u‖ * ‖v‖ := by
  dsimp only
  obtain ⟨z, hz, hbound⟩ :=
    u4h3_coefficient_mixed_quotient_multiplier hsmooth l m j k hh hs u
  have hpair : (∫ x, (((ω.1 ((x + s • unitVector m) + h • unitVector l) j k -
      ω.1 (x + s • unitVector m) j k -
      (ω.1 (x + h • unitVector l) j k - ω.1 x j k)) / h / s : ℝ) : ℂ) *
      u x * star (v x)) = inner ℂ v z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    simp only [RCLike.inner_apply, Complex.star_def]
    rw [hx]
  constructor
  · apply ((Lp.memLp z).integrable_mul (Lp.memLp v).star).congr
    filter_upwards [hz] with x hx
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [hx]
  · rw [hpair]
    calc
      ‖inner ℂ v z‖ ≤ ‖v‖ * ‖z‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (M 2 * ‖u‖) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ = M 2 * ‖u‖ * ‖v‖ := by ring


/-- Two backward quotients of an H1 test are admissible in the actual
forward generator weak equation. The intermediate representatives retain
the supplied test gradient. -/
theorem u4h3_forward_double_backward_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {V : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hV : IsPhysicalH1Graph volume (Or.inl rfl) v V)
    (l m : Fin d) (h s : ℝ) :
    ∃ (r t : Lp ℂ 2 (volume : Measure (Vec d)))
      (R T : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) r R ∧
      IsPhysicalH1Graph volume (Or.inl rfl) t T ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (s : ℂ)⁻¹ * (v (x - s • unitVector m) - v x)) ∧
      (∀ j, (R j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (s : ℂ)⁻¹ * (V j (x - s • unitVector m) - V j x))) ∧
      (t : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x)) ∧
      (∀ j, (T j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (R j (x - h • unitVector l) - R j x))) ∧
      (∫ x, g x * t x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * T j x) +
        ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * t x) := by
  obtain ⟨r, R, hrR, hr, hR⟩ :=
    c18_physical_H1_difference_quotient hV (s • unitVector m) s
  obtain ⟨t, T, htT, ht, hT, hw⟩ :=
    c18_physical_generator_backward_quotient_test hfg hG hrR l h
  exact ⟨r, t, R, T, hrR, htT, hr, hR, ht, hT, hw⟩

/-- The same twice-quotiented test is admissible for the transpose weak
generator equation, including its divergence-form force term. -/
theorem u4h3_transpose_double_backward_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {V : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hV : IsPhysicalH1Graph volume (Or.inl rfl) v V)
    (l m : Fin d) (h s : ℝ) :
    ∃ (r t : Lp ℂ 2 (volume : Measure (Vec d)))
      (R T : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) r R ∧
      IsPhysicalH1Graph volume (Or.inl rfl) t T ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (s : ℂ)⁻¹ * (v (x - s • unitVector m) - v x)) ∧
      (∀ j, (R j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (s : ℂ)⁻¹ * (V j (x - s • unitVector m) - V j x))) ∧
      (t : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x)) ∧
      (∀ j, (T j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (R j (x - h • unitVector l) - R j x))) ∧
      (∫ x, g x * t x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * T j x) +
        ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) * T j x)) := by
  obtain ⟨r, R, hrR, hr, hR⟩ :=
    c18_physical_H1_difference_quotient hV (s • unitVector m) s
  obtain ⟨t, T, htT, ht, hT, hw⟩ :=
    c18_physical_transpose_generator_backward_quotient_test hfg hG hrR l h
  exact ⟨r, t, R, T, hrR, htT, hr, hR, ht, hT, hw⟩

/-- Two signed summation-by-parts steps transfer a twice-backward test
quotient to the actual L2 coefficient-times-gradient representative. -/
theorem u4h3_double_quotient_integration_by_parts {d : ℕ}
    {u : Vec d → ℂ} (hu : MemLp u 2 (volume : Measure (Vec d)))
    (v r : Lp ℂ 2 (volume : Measure (Vec d)))
    (l m : Fin d) (h s : ℝ)
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (s : ℂ)⁻¹ * (v (x - s • unitVector m) - v x))) :
    (∫ x, u x * ((r (x - h • unitVector l) - r x) / (h : ℂ))) =
      ∫ x, (((u ((x + s • unitVector m) + h • unitVector l) -
        u (x + s • unitVector m)) / (h : ℂ) -
        (u (x + h • unitVector l) - u x) / (h : ℂ)) / (s : ℂ)) * v x := by
  let q : Vec d → ℂ := fun x => (u (x + h • unitVector l) - u x) / (h : ℂ)
  have ht := hu.comp_measurePreserving
    (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l))
  have hq : MemLp q 2 (volume : Measure (Vec d)) := by
    simpa only [q, div_eq_mul_inv, mul_comm, Pi.sub_apply, Function.comp_apply] using
      (ht.sub hu).const_mul ((h : ℂ)⁻¹)
  have hi₁ := c18_L2_difference_quotient_integration_by_parts hu (Lp.memLp r)
    (h • unitVector l) h
  have hi₂ := c18_L2_difference_quotient_integration_by_parts hq (Lp.memLp v)
    (s • unitVector m) s
  calc
    _ = ∫ x, q x * r x := by simpa only [q] using hi₁.symm
    _ = ∫ x, q x * ((v (x - s • unitVector m) - v x) / (s : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [hr] with x hx
      simp only [hx, div_eq_mul_inv, mul_comm]
    _ = _ := by simpa only [q] using hi₂.symm

/-- The exact second difference product rule, including both first-order
commutators and the mixed second coefficient difference. -/
theorem u4h3_double_quotient_product_rule {d : ℕ}
    (a u : Vec d → ℂ) (x z w : Vec d) (h s : ℝ) :
    (((a ((x + w) + z) * u ((x + w) + z) - a (x + w) * u (x + w)) /
        (h : ℂ) - (a (x + z) * u (x + z) - a x * u x) / (h : ℂ)) / (s : ℂ)) =
      a ((x + w) + z) * (((u ((x + w) + z) - u (x + w)) / (h : ℂ) -
        (u (x + z) - u x) / (h : ℂ)) / (s : ℂ)) +
      ((a ((x + w) + z) - a (x + w)) / (h : ℂ)) *
        ((u (x + w) - u x) / (s : ℂ)) +
      ((a ((x + w) + z) - a (x + z)) / (s : ℂ)) *
        ((u (x + z) - u x) / (h : ℂ)) +
      (((a ((x + w) + z) - a (x + w)) / (h : ℂ) -
        (a (x + z) - a x) / (h : ℂ)) / (s : ℂ)) * u x := by
  simp only [div_eq_mul_inv]
  ring

/-- The principal pairing in a twice-backward generator test equals the
translated principal term plus all three coefficient commutators. This uses
the actual intermediate L² representatives from the admissible test. -/
theorem u4h3_double_backward_principal_pairing {d : ℕ}
    (a : Vec d → ℂ) (ha : MemLp a ∞ (volume : Measure (Vec d)))
    (u v r t : Lp ℂ 2 (volume : Measure (Vec d)))
    (l m : Fin d) (h s : ℝ)
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (s : ℂ)⁻¹ * (v (x - s • unitVector m) - v x)))
    (ht : (t : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x))) :
    (∫ x, a x * u x * t x) =
      ∫ x, (a ((x + s • unitVector m) + h • unitVector l) *
        (((u ((x + s • unitVector m) + h • unitVector l) -
          u (x + s • unitVector m)) / (h : ℂ) -
          (u (x + h • unitVector l) - u x) / (h : ℂ)) / (s : ℂ)) +
        ((a ((x + s • unitVector m) + h • unitVector l) -
          a (x + s • unitVector m)) / (h : ℂ)) *
          ((u (x + s • unitVector m) - u x) / (s : ℂ)) +
        ((a ((x + s • unitVector m) + h • unitVector l) -
          a (x + h • unitVector l)) / (s : ℂ)) *
          ((u (x + h • unitVector l) - u x) / (h : ℂ)) +
        (((a ((x + s • unitVector m) + h • unitVector l) -
          a (x + s • unitVector m)) / (h : ℂ) -
          (a (x + h • unitVector l) - a x) / (h : ℂ)) / (s : ℂ)) * u x) * v x := by
  have hp : MemLp (fun x => a x * u x) 2 (volume : Measure (Vec d)) := by
    change MemLp (a * (u : Vec d → ℂ)) 2 (volume : Measure (Vec d))
    exact ha.mul (r := 2) (Lp.memLp u)
  have hi := u4h3_double_quotient_integration_by_parts hp v r l m h s hr
  calc
    _ = ∫ x, (a x * u x) * ((r (x - h • unitVector l) - r x) / (h : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [ht] with x hx
      rw [hx]
      simp only [div_eq_mul_inv]
      ring
    _ = ∫ x, (((a ((x + s • unitVector m) + h • unitVector l) *
          u ((x + s • unitVector m) + h • unitVector l) -
          a (x + s • unitVector m) * u (x + s • unitVector m)) / (h : ℂ) -
          (a (x + h • unitVector l) * u (x + h • unitVector l) - a x * u x) /
          (h : ℂ)) / (s : ℂ)) * v x := hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [u4h3_double_quotient_product_rule a (u : Vec d → ℂ) x
        (h • unitVector l) (s • unitVector m) h s]

/-- Two backward tests on the forcing term cost one derivative of the
forcing and one derivative of the original test. -/
theorem u4h3_double_backward_forcing_bound {d : ℕ}
    (g v r t : Lp ℂ 2 (volume : Measure (Vec d)))
    (J V : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hJ : IsPhysicalH1Graph volume (Or.inl rfl) g J)
    (hV : IsPhysicalH1Graph volume (Or.inl rfl) v V)
    (l m : Fin d) (h s : ℝ) (hh : h ≠ 0) (hs : s ≠ 0)
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (s : ℂ)⁻¹ * (v (x - s • unitVector m) - v x)))
    (ht : (t : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x))) :
    ‖∫ x, g x * t x‖ ≤ ‖J l‖ * ‖V m‖ := by
  obtain ⟨q, Q, hqQ, hq, hQ, hnorm⟩ :=
    c23_physical_forward_difference_quotient_graph hJ l h
  have hqb : ‖q‖ ≤ ‖J l‖ := c23_forward_difference_quotient_norm_le hJ l h hh hq
  have hrb : ‖r‖ ≤ ‖V m‖ := c23_backward_test_norm_le hV m s hs hr
  have hi := c18_L2_difference_quotient_integration_by_parts
    (Lp.memLp g) (Lp.memLp r) (h • unitVector l) h
  have heq : (∫ x, g x * t x) = ∫ x, q x * r x := by
    calc
      _ = ∫ x, g x * ((r (x - h • unitVector l) - r x) / (h : ℂ)) := by
        apply integral_congr_ae
        filter_upwards [ht] with x hx
        simp only [hx, div_eq_mul_inv, mul_comm]
      _ = ∫ x, ((g (x + h • unitVector l) - g x) / (h : ℂ)) * r x := hi.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hq] with x hx
        rw [hx]
  have hp : (∫ x, q x * r x) = inner ℂ (star r) q := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star r] with x hx
    simp only [hx, RCLike.inner_apply, Pi.star_apply, Complex.star_def,
      Complex.conj_conj, mul_comm]
  rw [heq, hp]
  calc
    ‖inner ℂ (star r) q‖ ≤ ‖star r‖ * ‖q‖ := norm_inner_le_norm _ _
    _ ≤ ‖V m‖ * ‖J l‖ := by
      rw [c23_L2_norm_star]
      exact mul_le_mul hrb hqb (norm_nonneg _) (norm_nonneg _)
    _ = ‖J l‖ * ‖V m‖ := mul_comm _ _

/-- The forcing contribution in the conjugate double-quotient energy test. -/
theorem u4h3_double_backward_energy_forcing_bound {d : ℕ}
    (g q r t : Lp ℂ 2 (volume : Measure (Vec d)))
    (J Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hJ : IsPhysicalH1Graph volume (Or.inl rfl) g J)
    (hqQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (l m : Fin d) (h s : ℝ) (hh : h ≠ 0) (hs : s ≠ 0)
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (s : ℂ)⁻¹ * ((star q) (x - s • unitVector m) - (star q) x)))
    (ht : (t : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x))) :
    ‖∫ x, g x * t x‖ ≤ ‖J l‖ * ‖Q m‖ := by
  have hb := u4h3_double_backward_forcing_bound g (star q) r t J
    (fun j => star (Q j)) hJ (physicalH1Graph_star q Q hqQ) l m h s hh hs hr ht
  simpa only [c23_L2_norm_star] using hb

/-- First differences of each supplied gradient component are controlled by
the corresponding supplied Hessian, in either differentiation direction. -/
theorem u4h3_gradient_quotient_family {d : ℕ}
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (m : Fin d) (s : ℝ) (hs : s ≠ 0) :
    ∃ V : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j, (V j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + s • unitVector m) - G j x) / (s : ℂ))) ∧
      ∀ j, ‖V j‖ ≤ ‖H j m‖ := by
  have hex : ∀ j, ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + s • unitVector m) - G j x) / (s : ℂ)) ∧
      ‖v‖ ≤ ‖H j m‖ := by
    intro j
    obtain ⟨v, V, _, hv, _, _⟩ :=
      c23_physical_forward_difference_quotient_graph (hH j) m s
    exact ⟨v, hv, c23_forward_difference_quotient_norm_le (hH j) m s hs hv⟩
  choose V hV hbound using hex
  exact ⟨V, hV, hbound⟩

/-- Successive forward quotients retain both supplied gradients. Their scalar
part is uniformly controlled by the corresponding supplied Hessian entry. -/
theorem u4h3_double_forward_graph {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (l m : Fin d) (h s : ℝ) (hh : h ≠ 0) (hs : s ≠ 0) :
    ∃ (q₀ q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q₀ Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q₀ Q₀ ∧
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q₀ : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) ∧
      (∀ j, (Q₀ j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (q₀ (x + s • unitVector m) - q₀ x) / (s : ℂ)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (Q₀ j (x + s • unitVector m) - Q₀ j x) / (s : ℂ))) ∧
      (∀ j, ‖Q₀ j‖ ≤ ‖H j l‖) ∧ ‖q‖ ≤ ‖H m l‖ := by
  obtain ⟨q₀, Q₀, hq₀Q₀, hq₀, hQ₀, _⟩ :=
    c23_physical_forward_difference_quotient_graph hG l h
  obtain ⟨q, Q, hqQ, hq, hQ, _⟩ :=
    c23_physical_forward_difference_quotient_graph hq₀Q₀ m s
  have hb : ∀ j, ‖Q₀ j‖ ≤ ‖H j l‖ := fun j =>
    c23_forward_difference_quotient_norm_le (hH j) l h hh (hQ₀ j)
  exact ⟨q₀, q, Q₀, Q, hq₀Q₀, hqQ, hq₀, hQ₀, hq, hQ, hb,
    (c23_forward_difference_quotient_norm_le hq₀Q₀ m s hs hq).trans (hb m)⟩


/-- The representative of a successive forward quotient agrees with the
explicit mixed quotient of the original L² function. -/
theorem u4h3_double_forward_quotient_ae {d : ℕ}
    (u u₀ u₁ : Lp ℂ 2 (volume : Measure (Vec d)))
    (l m : Fin d) (h s : ℝ)
    (hu₀ : (u₀ : Vec d → ℂ) =ᵐ[volume]
      (fun x => (u (x + h • unitVector l) - u x) / (h : ℂ)))
    (hu₁ : (u₁ : Vec d → ℂ) =ᵐ[volume]
      (fun x => (u₀ (x + s • unitVector m) - u₀ x) / (s : ℂ))) :
    (u₁ : Vec d → ℂ) =ᵐ[volume]
      (fun x => ((u ((x + s • unitVector m) + h • unitVector l) -
        u (x + s • unitVector m)) / (h : ℂ) -
        (u (x + h • unitVector l) - u x) / (h : ℂ)) / (s : ℂ)) := by
  have ht := (measurePreserving_add_right (volume : Measure (Vec d))
    (s • unitVector m)).quasiMeasurePreserving.ae_eq_comp hu₀
  filter_upwards [hu₀, hu₁, ht] with x h₀ h₁ ht
  simp only [Function.comp_apply] at ht
  rw [h₁, ht, h₀]

/-- The principal term in a twice-backward test uses the actual successive
forward quotient representative, with the coefficient commutators explicit. -/
theorem u4h3_double_backward_principal_pairing_graph {d : ℕ}
    (a : Vec d → ℂ) (ha : MemLp a ∞ (volume : Measure (Vec d)))
    (u u₀ u₁ v r t : Lp ℂ 2 (volume : Measure (Vec d)))
    (l m : Fin d) (h s : ℝ)
    (hu₀ : (u₀ : Vec d → ℂ) =ᵐ[volume]
      (fun x => (u (x + h • unitVector l) - u x) / (h : ℂ)))
    (hu₁ : (u₁ : Vec d → ℂ) =ᵐ[volume]
      (fun x => (u₀ (x + s • unitVector m) - u₀ x) / (s : ℂ)))
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (s : ℂ)⁻¹ * (v (x - s • unitVector m) - v x)))
    (ht : (t : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x))) :
    (∫ x, a x * u x * t x) =
      ∫ x, (a ((x + s • unitVector m) + h • unitVector l) * u₁ x +
        ((a ((x + s • unitVector m) + h • unitVector l) -
          a (x + s • unitVector m)) / (h : ℂ)) *
          ((u (x + s • unitVector m) - u x) / (s : ℂ)) +
        ((a ((x + s • unitVector m) + h • unitVector l) -
          a (x + h • unitVector l)) / (s : ℂ)) *
          ((u (x + h • unitVector l) - u x) / (h : ℂ)) +
        (((a ((x + s • unitVector m) + h • unitVector l) -
          a (x + s • unitVector m)) / (h : ℂ) -
          (a (x + h • unitVector l) - a x) / (h : ℂ)) / (s : ℂ)) * u x) * v x := by
  rw [u4h3_double_backward_principal_pairing a ha u v r t l m h s hr ht]
  apply integral_congr_ae
  filter_upwards [u4h3_double_forward_quotient_ae u u₀ u₁ l m h s hu₀ hu₁] with x hx
  rw [hx]


/-- The actual forward generator equation tested against the conjugate of
its successive forward quotient, with the principal pairing identified. -/
theorem u4h3_forward_double_quotient_energy_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (l m : Fin d) (h s : ℝ) (hh : h ≠ 0) (hs : s ≠ 0) :
    ∃ (q₀ q r t : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q₀ Q R T : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (∀ j, (Q₀ j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (Q₀ j (x + s • unitVector m) - Q₀ j x) / (s : ℂ))) ∧
      (∀ j, ‖Q₀ j‖ ≤ ‖H j l‖) ∧ ‖q‖ ≤ ‖H m l‖ ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (s : ℂ)⁻¹ * ((star q) (x - s • unitVector m) - (star q) x)) ∧
      (t : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x)) ∧
      (∫ x, g x * t x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * T j x) +
        ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * t x) ∧
      ∀ j k, (∫ x, (a x j k : ℂ) * G k x * T j x) =
        ∫ x, ((a ((x + s • unitVector m) + h • unitVector l) j k : ℂ) * Q k x +
          (((a ((x + s • unitVector m) + h • unitVector l) j k : ℂ) -
            (a (x + s • unitVector m) j k : ℂ)) / (h : ℂ)) *
            ((G k (x + s • unitVector m) - G k x) / (s : ℂ)) +
          (((a ((x + s • unitVector m) + h • unitVector l) j k : ℂ) -
            (a (x + h • unitVector l) j k : ℂ)) / (s : ℂ)) *
            ((G k (x + h • unitVector l) - G k x) / (h : ℂ)) +
          ((((a ((x + s • unitVector m) + h • unitVector l) j k : ℂ) -
            (a (x + s • unitVector m) j k : ℂ)) / (h : ℂ) -
            ((a (x + h • unitVector l) j k : ℂ) - (a x j k : ℂ)) / (h : ℂ)) /
            (s : ℂ)) * G k x) * (star (Q j)) x := by
  obtain ⟨q₀, q, Q₀, Q, _, hqQ, _, hQ₀, _, hQ, hb₀, hbq⟩ :=
    u4h3_double_forward_graph hG hH l m h s hh hs
  obtain ⟨r, t, R, T, _, _, hr, hR, ht, hT, hw⟩ :=
    u4h3_forward_double_backward_test hfg hG (physicalH1Graph_star q Q hqQ) l m h s
  refine ⟨q₀, q, r, t, Q₀, Q, R, T, hqQ, hQ₀, hQ, hb₀, hbq, hr, ht, hw, ?_⟩
  intro j k
  exact u4h3_double_backward_principal_pairing_graph (fun x => (a x j k : ℂ))
    (ha j k) (G k) (Q₀ k) (Q k) (star (Q j)) (R j) (T j) l m h s
    (hQ₀ k) (hQ k) (hR j) (hT j)


/-- The actual transpose generator equation tested against the conjugate of
its successive forward quotient, with the principal pairing identified. -/
theorem u4h3_transpose_double_quotient_energy_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (l m : Fin d) (h s : ℝ) (hh : h ≠ 0) (hs : s ≠ 0) :
    ∃ (q₀ q r t : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q₀ Q R T : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (∀ j, (Q₀ j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (Q₀ j (x + s • unitVector m) - Q₀ j x) / (s : ℂ))) ∧
      (∀ j, ‖Q₀ j‖ ≤ ‖H j l‖) ∧ ‖q‖ ≤ ‖H m l‖ ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (s : ℂ)⁻¹ * ((star q) (x - s • unitVector m) - (star q) x)) ∧
      (t : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x)) ∧
      (∫ x, g x * t x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * T j x) +
        ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) * T j x)) ∧
      ∀ j k, (∫ x, (a x k j : ℂ) * G k x * T j x) =
        ∫ x, ((a ((x + s • unitVector m) + h • unitVector l) k j : ℂ) * Q k x +
          (((a ((x + s • unitVector m) + h • unitVector l) k j : ℂ) -
            (a (x + s • unitVector m) k j : ℂ)) / (h : ℂ)) *
            ((G k (x + s • unitVector m) - G k x) / (s : ℂ)) +
          (((a ((x + s • unitVector m) + h • unitVector l) k j : ℂ) -
            (a (x + h • unitVector l) k j : ℂ)) / (s : ℂ)) *
            ((G k (x + h • unitVector l) - G k x) / (h : ℂ)) +
          ((((a ((x + s • unitVector m) + h • unitVector l) k j : ℂ) -
            (a (x + s • unitVector m) k j : ℂ)) / (h : ℂ) -
            ((a (x + h • unitVector l) k j : ℂ) - (a x k j : ℂ)) / (h : ℂ)) /
            (s : ℂ)) * G k x) * (star (Q j)) x := by
  obtain ⟨q₀, q, Q₀, Q, _, hqQ, _, hQ₀, _, hQ, hb₀, hbq⟩ :=
    u4h3_double_forward_graph hG hH l m h s hh hs
  obtain ⟨r, t, R, T, _, _, hr, hR, ht, hT, hw⟩ :=
    u4h3_transpose_double_backward_test hfg hG (physicalH1Graph_star q Q hqQ) l m h s
  refine ⟨q₀, q, r, t, Q₀, Q, R, T, hqQ, hQ₀, hQ, hb₀, hbq, hr, ht, hw, ?_⟩
  intro j k
  exact u4h3_double_backward_principal_pairing_graph (fun x => (a x k j : ℂ))
    (ha k j) (G k) (Q₀ k) (Q k) (star (Q j)) (R j) (T j) l m h s
    (hQ₀ k) (hQ k) (hR j) (hT j)

/-- The transpose energy test retains the forward and backward quotient representatives. -/
theorem u4h3_transpose_double_quotient_energy_test_with_representatives {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (l m : Fin d) (h s : ℝ) (hh : h ≠ 0) (hs : s ≠ 0) :
    ∃ (q₀ q r t : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q₀ Q R T : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q₀ : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (q₀ (x + s • unitVector m) - q₀ x) / (s : ℂ)) ∧
      (∀ j, (R j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (s : ℂ)⁻¹ * ((star (Q j)) (x - s • unitVector m) - (star (Q j)) x))) ∧
      (∀ j, (T j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (R j (x - h • unitVector l) - R j x))) ∧
      (∀ j, (Q₀ j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (Q₀ j (x + s • unitVector m) - Q₀ j x) / (s : ℂ))) ∧
      (∀ j, ‖Q₀ j‖ ≤ ‖H j l‖) ∧ ‖q‖ ≤ ‖H m l‖ ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (s : ℂ)⁻¹ * ((star q) (x - s • unitVector m) - (star q) x)) ∧
      (t : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x)) ∧
      (∫ x, g x * t x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * T j x) +
        ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) * T j x)) ∧
      ∀ j k, (∫ x, (a x k j : ℂ) * G k x * T j x) =
        ∫ x, ((a ((x + s • unitVector m) + h • unitVector l) k j : ℂ) * Q k x +
          (((a ((x + s • unitVector m) + h • unitVector l) k j : ℂ) -
            (a (x + s • unitVector m) k j : ℂ)) / (h : ℂ)) *
            ((G k (x + s • unitVector m) - G k x) / (s : ℂ)) +
          (((a ((x + s • unitVector m) + h • unitVector l) k j : ℂ) -
            (a (x + h • unitVector l) k j : ℂ)) / (s : ℂ)) *
            ((G k (x + h • unitVector l) - G k x) / (h : ℂ)) +
          ((((a ((x + s • unitVector m) + h • unitVector l) k j : ℂ) -
            (a (x + s • unitVector m) k j : ℂ)) / (h : ℂ) -
            ((a (x + h • unitVector l) k j : ℂ) - (a x k j : ℂ)) / (h : ℂ)) /
            (s : ℂ)) * G k x) * (star (Q j)) x := by
  obtain ⟨q₀, q, Q₀, Q, _, hqQ, hq₀, hQ₀, hq, hQ, hb₀, hbq⟩ :=
    u4h3_double_forward_graph hG hH l m h s hh hs
  obtain ⟨r, t, R, T, _, _, hr, hR, ht, hT, hw⟩ :=
    u4h3_transpose_double_backward_test hfg hG (physicalH1Graph_star q Q hqQ) l m h s
  refine ⟨q₀, q, r, t, Q₀, Q, R, T, hqQ, hq₀, hq, hR, hT, hQ₀, hQ, hb₀, hbq, hr, ht, hw, ?_⟩
  intro j k
  exact u4h3_double_backward_principal_pairing_graph (fun x => (a x k j : ℂ))
    (ha k j) (G k) (Q₀ k) (Q k) (star (Q j)) (R j) (T j) l m h s
    (hQ₀ k) (hQ k) (hR j) (hT j)


/-- The mixed coefficient commutators are integrable and uniformly bounded
when summed over both coefficient indices, including transposed indices. -/
theorem u4h3_mixed_commutator_sum_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l m : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (p q : Fin d → Fin d → Fin d)
    (G Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    let F : Fin d → Fin d → Vec d → ℂ := fun j k x =>
      (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) -
        ω.1 (x + s • unitVector m) (p j k) (q j k) -
        (ω.1 (x + h • unitVector l) (p j k) (q j k) -
          ω.1 x (p j k) (q j k))) / h / s : ℝ) : ℂ) * G k x * star (Q j x)
    (∀ j k, Integrable (F j k) volume) ∧
      ‖∑ j, ∑ k, ∫ x, F j k x‖ ≤
        M 2 * (∑ k, ‖G k‖) * (∑ j, ‖Q j‖) := by
  dsimp only
  constructor
  · intro j k
    exact (u4h3_coefficient_mixed_quotient_pairing hsmooth l m (p j k) (q j k)
      hh hs (G k) (Q j)).1
  · calc
      ‖∑ j, ∑ k, ∫ x,
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) -
          ω.1 (x + s • unitVector m) (p j k) (q j k) -
          (ω.1 (x + h • unitVector l) (p j k) (q j k) -
            ω.1 x (p j k) (q j k))) / h / s : ℝ) : ℂ) *
          G k x * star (Q j x)‖ ≤
          ∑ j, ∑ k, ‖∫ x,
            (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) -
              ω.1 (x + s • unitVector m) (p j k) (q j k) -
              (ω.1 (x + h • unitVector l) (p j k) (q j k) -
                ω.1 x (p j k) (q j k))) / h / s : ℝ) : ℂ) *
              G k x * star (Q j x)‖ := by
        exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
      _ ≤ ∑ j, ∑ k, M 2 * ‖G k‖ * ‖Q j‖ := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        exact (u4h3_coefficient_mixed_quotient_pairing hsmooth l m (p j k) (q j k)
          hh hs (G k) (Q j)).2
      _ = M 2 * (∑ k, ‖G k‖) * (∑ j, ‖Q j‖) := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum]

/-- First coefficient commutators remain bounded after an arbitrary
translation, for either coefficient index order. -/
theorem u4h3_translated_commutator_sum_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l : Fin d) {h : ℝ} (hh : h ≠ 0) (z : Vec d)
    (p q : Fin d → Fin d → Fin d)
    (G Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    let F : Fin d → Fin d → Vec d → ℂ := fun j k x =>
      (((ω.1 ((x + z) + h • unitVector l) (p j k) (q j k) -
        ω.1 (x + z) (p j k) (q j k)) / h : ℝ) : ℂ) * G k x * star (Q j x)
    (∀ j k, Integrable (F j k) volume) ∧
      ‖∑ j, ∑ k, ∫ x, F j k x‖ ≤
        M 1 * (∑ k, ‖G k‖) * (∑ j, ‖Q j‖) := by
  dsimp only
  let b : Fin d → Fin d → Vec d → ℝ := fun j k x =>
    (ω.1 ((x + z) + h • unitVector l) (p j k) (q j k) -
      ω.1 (x + z) (p j k) (q j k)) / h
  have hb : ∀ j k, Measurable (b j k) := by
    intro j k
    exact ((((hsmooth.1.1 (p j k) (q j k)).continuous.comp
      ((continuous_id.add continuous_const).add continuous_const)).sub
      ((hsmooth.1.1 (p j k) (q j k)).continuous.comp
        (continuous_id.add continuous_const))).div_const h).measurable
  have hbound : ∀ j k x, |b j k x| ≤ M 1 := by
    intro j k x
    exact c18_smooth_coefficient_coordinate_quotient_bound hsmooth l (p j k) (q j k) (x + z) hh
  have hM : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  have hi : ∀ j k, Integrable (fun x => (b j k x : ℂ) * G k x * star (Q j x)) volume := by
    intro j k
    let w := (s5_memLp_mul (hb j k) (hbound j k) (G k)).toLp
      (fun x => (b j k x : ℂ) * G k x)
    apply ((Lp.memLp w).integrable_mul (Lp.memLp (Q j)).star).congr
    filter_upwards [(s5_memLp_mul (hb j k) (hbound j k) (G k)).coeFn_toLp] with x hx
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [hx]
  constructor
  · exact hi
  · calc
      ‖∑ j, ∑ k, ∫ x, (b j k x : ℂ) * G k x * star (Q j x)‖ ≤
          ∑ j, ∑ k, ‖∫ x, (b j k x : ℂ) * G k x * star (Q j x)‖ := by
        exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
      _ ≤ ∑ j, ∑ k, M 1 * ‖G k‖ * ‖Q j‖ := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        exact c23_bounded_real_coefficient_pairing (b j k) (hb j k) (M 1) hM
          (hbound j k) (G k) (Q j)
      _ = M 1 * (∑ k, ‖G k‖) * (∑ j, ‖Q j‖) := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum]


/-- A translated elliptic coefficient has a uniform single-index pairing
bound, including integrability of each term. -/
theorem u4h3_translated_elliptic_single_sum_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) (z : Vec d)
    (p q : Fin d → Fin d) (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∀ j, Integrable (fun x => (ω.1 (x + z) (p j) (q j) : ℂ) *
      u x * star (Q j x)) volume) ∧
      ‖∑ j, ∫ x, (ω.1 (x + z) (p j) (q j) : ℂ) *
        u x * star (Q j x)‖ ≤ Λ * ‖u‖ * (∑ j, ‖Q j‖) := by
  have hb (j : Fin d) : Measurable (fun x => ω.1 (x + z) (p j) (q j)) :=
    ((hsmooth.1.1 (p j) (q j)).continuous.comp (continuous_id.add continuous_const)).measurable
  have hbound (j : Fin d) (x : Vec d) : |ω.1 (x + z) (p j) (q j)| ≤ Λ :=
    (s5Elliptic_of_isElliptic hΛ hell (x + z)).entry_abs_le (p j) (q j)
  constructor
  · intro j
    let w := (s5_memLp_mul (hb j) (hbound j) u).toLp
      (fun x => (ω.1 (x + z) (p j) (q j) : ℂ) * u x)
    apply ((Lp.memLp w).integrable_mul (Lp.memLp (Q j)).star).congr
    filter_upwards [(s5_memLp_mul (hb j) (hbound j) u).coeFn_toLp] with x hx
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [hx]
  · calc
      ‖∑ j, ∫ x, (ω.1 (x + z) (p j) (q j) : ℂ) * u x * star (Q j x)‖ ≤
          ∑ j, ‖∫ x, (ω.1 (x + z) (p j) (q j) : ℂ) * u x * star (Q j x)‖ := norm_sum_le _ _
      _ ≤ ∑ j, Λ * ‖u‖ * ‖Q j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact c23_elliptic_entry_pairing_bound hΛ hell hsmooth (p j) (q j) z u (Q j)
      _ = Λ * ‖u‖ * (∑ j, ‖Q j‖) := by rw [Finset.mul_sum]

/-- A single-index translated coefficient commutator pairs integrably with
an L² function and is bounded uniformly in the translation and step. -/
theorem u4h3_translated_commutator_single_sum_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l : Fin d) {h : ℝ} (hh : h ≠ 0) (z : Vec d)
    (p q : Fin d → Fin d) (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    let F : Fin d → Vec d → ℂ := fun j x =>
      (((ω.1 ((x + z) + h • unitVector l) (p j) (q j) -
        ω.1 (x + z) (p j) (q j)) / h : ℝ) : ℂ) * u x * star (Q j x)
    (∀ j, Integrable (F j) volume) ∧
      ‖∑ j, ∫ x, F j x‖ ≤ M 1 * ‖u‖ * (∑ j, ‖Q j‖) := by
  dsimp only
  let b : Fin d → Vec d → ℝ := fun j x =>
    (ω.1 ((x + z) + h • unitVector l) (p j) (q j) -
      ω.1 (x + z) (p j) (q j)) / h
  have hb : ∀ j, Measurable (b j) := by
    intro j
    exact ((((hsmooth.1.1 (p j) (q j)).continuous.comp
      ((continuous_id.add continuous_const).add continuous_const)).sub
      ((hsmooth.1.1 (p j) (q j)).continuous.comp
        (continuous_id.add continuous_const))).div_const h).measurable
  have hbound : ∀ j x, |b j x| ≤ M 1 := by
    intro j x
    exact c18_smooth_coefficient_coordinate_quotient_bound hsmooth l (p j) (q j) (x + z) hh
  have hM : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  constructor
  · intro j
    let w := (s5_memLp_mul (hb j) (hbound j) u).toLp (fun x => (b j x : ℂ) * u x)
    apply ((Lp.memLp w).integrable_mul (Lp.memLp (Q j)).star).congr
    filter_upwards [(s5_memLp_mul (hb j) (hbound j) u).coeFn_toLp] with x hx
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [hx]
  · calc
      ‖∑ j, ∫ x, (b j x : ℂ) * u x * star (Q j x)‖ ≤
          ∑ j, ‖∫ x, (b j x : ℂ) * u x * star (Q j x)‖ := norm_sum_le _ _
      _ ≤ ∑ j, M 1 * ‖u‖ * ‖Q j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact c23_bounded_real_coefficient_pairing (b j) (hb j) (M 1) hM
          (hbound j) u (Q j)
      _ = M 1 * ‖u‖ * (∑ j, ‖Q j‖) := by rw [Finset.mul_sum]

/-- A mixed coefficient commutator paired with one L² function is controlled
uniformly when summed over the transpose drift index. -/
theorem u4h3_mixed_commutator_single_sum_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l m : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (p q : Fin d → Fin d) (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    let F : Fin d → Vec d → ℂ := fun j x =>
      (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (q j) -
        ω.1 (x + s • unitVector m) (p j) (q j) -
        (ω.1 (x + h • unitVector l) (p j) (q j) - ω.1 x (p j) (q j))) /
          h / s : ℝ) : ℂ) * u x * star (Q j x)
    (∀ j, Integrable (F j) volume) ∧
      ‖∑ j, ∫ x, F j x‖ ≤ M 2 * ‖u‖ * (∑ j, ‖Q j‖) := by
  dsimp only
  constructor
  · intro j
    exact (u4h3_coefficient_mixed_quotient_pairing hsmooth l m (p j) (q j) hh hs u (Q j)).1
  · calc
      ‖∑ j, ∫ x, (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (q j) -
        ω.1 (x + s • unitVector m) (p j) (q j) -
        (ω.1 (x + h • unitVector l) (p j) (q j) - ω.1 x (p j) (q j))) /
          h / s : ℝ) : ℂ) * u x * star (Q j x)‖ ≤
          ∑ j, ‖∫ x, (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (q j) -
        ω.1 (x + s • unitVector m) (p j) (q j) -
        (ω.1 (x + h • unitVector l) (p j) (q j) - ω.1 x (p j) (q j))) /
          h / s : ℝ) : ℂ) * u x * star (Q j x)‖ := norm_sum_le _ _
      _ ≤ ∑ j, M 2 * ‖u‖ * ‖Q j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (u4h3_coefficient_mixed_quotient_pairing hsmooth l m (p j) (q j) hh hs u (Q j)).2
      _ = M 2 * ‖u‖ * (∑ j, ‖Q j‖) := by rw [Finset.mul_sum]


/-- Both first-order coefficient commutators are bounded by the supplied
Hessian, uniformly in the two difference steps and coefficient orientation. -/
theorem u4h3_first_commutators_hessian_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (l m : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (p q : Fin d → Fin d → Fin d) :
    ∃ V W : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ k, (V k : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G k (x + s • unitVector m) - G k x) / (s : ℂ))) ∧
      (∀ k, (W k : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G k (x + h • unitVector l) - G k x) / (h : ℂ))) ∧
      ‖∑ j, ∑ k, ∫ x,
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) -
          ω.1 (x + s • unitVector m) (p j k) (q j k)) / h : ℝ) : ℂ) *
          V k x * star (Q j x)‖ ≤ M 1 * (∑ k, ‖H k m‖) * (∑ j, ‖Q j‖) ∧
      ‖∑ j, ∑ k, ∫ x,
        (((ω.1 ((x + h • unitVector l) + s • unitVector m) (p j k) (q j k) -
          ω.1 (x + h • unitVector l) (p j k) (q j k)) / s : ℝ) : ℂ) *
          W k x * star (Q j x)‖ ≤ M 1 * (∑ k, ‖H k l‖) * (∑ j, ‖Q j‖) := by
  obtain ⟨V, hV, hVb⟩ := u4h3_gradient_quotient_family G H hH m s hs
  obtain ⟨W, hW, hWb⟩ := u4h3_gradient_quotient_family G H hH l h hh
  have hM : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  have hQ : 0 ≤ ∑ j, ‖Q j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hVsum : (∑ k, ‖V k‖) ≤ ∑ k, ‖H k m‖ :=
    Finset.sum_le_sum (fun k _ => hVb k)
  have hWsum : (∑ k, ‖W k‖) ≤ ∑ k, ‖H k l‖ :=
    Finset.sum_le_sum (fun k _ => hWb k)
  refine ⟨V, W, hV, hW, ?_, ?_⟩
  · exact (u4h3_translated_commutator_sum_bound hsmooth l hh
      (s • unitVector m) p q V Q).2.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVsum hM) hQ)
  · exact (u4h3_translated_commutator_sum_bound hsmooth m hs
      (h • unitVector l) p q W Q).2.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWsum hM) hQ)


/-- The forward force in the twice-differenced energy test is controlled by
    the supplied Hessian and the gradient of the twice-differenced function. -/
theorem u4h3_forward_double_force_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) (i l m : Fin d) {h s : ℝ}
    (hh : h ≠ 0) (hs : s ≠ 0)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    {q r t : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (s : ℂ)⁻¹ * ((star q) (x - s • unitVector m) - (star q) x)))
    (ht : (t : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * (r (x - h • unitVector l) - r x))) :
    ‖∫ x, (∑ j, (ω.1 x j i : ℂ) * G j x) * t x‖ ≤
      (Λ * (∑ j, ‖H j l‖) + M 1 * (∑ j, ‖G j‖)) * ‖Q m‖ := by
  obtain ⟨W, hW, hWb⟩ := u4h3_gradient_quotient_family G H hH l h hh
  have ht' : (t : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * ((star (star r)) (x - h • unitVector l) - (star (star r)) x)) := by
    simpa only [star_star] using ht
  have hrb : ‖r‖ ≤ ‖Q m‖ := by
    simpa only [c23_L2_norm_star] using
      c23_backward_test_norm_le (physicalH1Graph_star q Q hQ) m s hs hr
  have ha : ∀ j, MemLp (fun x => (ω.1 x j i : ℂ)) ∞ volume := fun j =>
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous) j i
  have hint : ∀ j, Integrable (fun x => (ω.1 x j i : ℂ) * G j x * t x) volume :=
    fun j => ((ha j).mul (r := 2) (Lp.memLp (G j))).integrable_mul (Lp.memLp t)
  have heq : (∫ x, (∑ j, (ω.1 x j i : ℂ) * G j x) * t x) =
      ∑ j, ∫ x, (ω.1 x j i : ℂ) * G j x * t x := by
    calc
      _ = ∫ x, ∑ j, (ω.1 x j i : ℂ) * G j x * t x := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Finset.sum_mul]
      _ = _ := integral_finsetSum _ (fun j _ => hint j)
  have hterm (j : Fin d) : ‖∫ x, (ω.1 x j i : ℂ) * G j x * t x‖ ≤
      (Λ * ‖W j‖ + M 1 * ‖G j‖) * ‖r‖ := by
    have hb := c23_transpose_force_component_bound hΛ hell hsmooth i j l hh
      (G j) (W j) (star r) t (hW j) ht'
    have he : (∫ x, G j x * ((ω.1 x j i : ℂ) * t x)) =
        ∫ x, (ω.1 x j i : ℂ) * G j x * t x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    rw [he, c23_L2_norm_star] at hb
    exact hb
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hM : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  have hsum : (∑ j, ‖W j‖) ≤ ∑ j, ‖H j l‖ :=
    Finset.sum_le_sum (fun j _ => hWb j)
  have hcoef : 0 ≤ Λ * (∑ j, ‖H j l‖) + M 1 * (∑ j, ‖G j‖) := by positivity
  rw [heq]
  calc
    ‖∑ j, ∫ x, (ω.1 x j i : ℂ) * G j x * t x‖ ≤
        ∑ j, ‖∫ x, (ω.1 x j i : ℂ) * G j x * t x‖ := norm_sum_le _ _
    _ ≤ ∑ j, (Λ * ‖W j‖ + M 1 * ‖G j‖) * ‖r‖ :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = (Λ * (∑ j, ‖W j‖) + M 1 * (∑ j, ‖G j‖)) * ‖r‖ := by
      simp only [add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ (Λ * (∑ j, ‖H j l‖) + M 1 * (∑ j, ‖G j‖)) * ‖r‖ :=
      mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hsum hΛ0) (le_refl (M 1 * ∑ j, ‖G j‖))) (norm_nonneg _)
    _ ≤ (Λ * (∑ j, ‖H j l‖) + M 1 * (∑ j, ‖G j‖)) * ‖Q m‖ :=
      mul_le_mul_of_nonneg_left hrb hcoef

/-- The scalar first quotients in the transpose drift commutators are
controlled by the supplied gradient, uniformly in both difference steps. -/
theorem u4h3_transpose_first_commutators_gradient_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    {f q₀ : Lp ℂ 2 (volume : Measure (Vec d))}
    (G Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l m : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (hq₀ : (q₀ : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)))
    (p q : Fin d → Fin d) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + s • unitVector m) - f x) / (s : ℂ)) ∧
      ‖∑ j, ∫ x,
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (q j) -
          ω.1 (x + s • unitVector m) (p j) (q j)) / h : ℝ) : ℂ) *
            v x * star (Q j x)‖ ≤ M 1 * ‖G m‖ * (∑ j, ‖Q j‖) ∧
      ‖∑ j, ∫ x,
        (((ω.1 ((x + h • unitVector l) + s • unitVector m) (p j) (q j) -
          ω.1 (x + h • unitVector l) (p j) (q j)) / s : ℝ) : ℂ) *
            q₀ x * star (Q j x)‖ ≤ M 1 * ‖G l‖ * (∑ j, ‖Q j‖) := by
  obtain ⟨v, V, _, hv, _, _⟩ :=
    c23_physical_forward_difference_quotient_graph hG m s
  have hvb : ‖v‖ ≤ ‖G m‖ := c23_forward_difference_quotient_norm_le hG m s hs hv
  have hq₀b : ‖q₀‖ ≤ ‖G l‖ := c23_forward_difference_quotient_norm_le hG l h hh hq₀
  have hM : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  have hQ : 0 ≤ ∑ j, ‖Q j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  refine ⟨v, hv, ?_, ?_⟩
  · exact (u4h3_translated_commutator_single_sum_bound hsmooth l hh
      (s • unitVector m) p q v Q).2.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvb hM) hQ)
  · exact (u4h3_translated_commutator_single_sum_bound hsmooth m hs
      (h • unitVector l) p q q₀ Q).2.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq₀b hM) hQ)


/-- The four terms of the twice-differenced transpose drift are jointly
bounded by the supplied gradient and Hessian. -/
theorem u4h3_transpose_drift_expansion_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    {f q₀ q : Lp ℂ 2 (volume : Measure (Vec d))}
    (G Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l m : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (hq₀ : (q₀ : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)))
    (p r : Fin d → Fin d) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + s • unitVector m) - f x) / (s : ℂ)) ∧
      ‖∑ j, ∫ x,
        ((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (r j) : ℂ) * q x +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (r j) -
          ω.1 (x + s • unitVector m) (p j) (r j)) / h : ℝ) : ℂ) * v x +
        (((ω.1 ((x + h • unitVector l) + s • unitVector m) (p j) (r j) -
          ω.1 (x + h • unitVector l) (p j) (r j)) / s : ℝ) : ℂ) * q₀ x +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (r j) -
          ω.1 (x + s • unitVector m) (p j) (r j) -
          (ω.1 (x + h • unitVector l) (p j) (r j) - ω.1 x (p j) (r j))) /
          h / s : ℝ) : ℂ) * f x) * star (Q j x)‖ ≤
        (Λ * ‖q‖ + M 1 * ‖G m‖ + M 1 * ‖G l‖ + M 2 * ‖f‖) *
          (∑ j, ‖Q j‖) := by
  obtain ⟨v, hv, hvb, hq₀b⟩ :=
    u4h3_transpose_first_commutators_gradient_bound hsmooth G Q hG l m hh hs hq₀ p r
  let A : Fin d → Vec d → ℂ := fun j x =>
    (ω.1 (x + (s • unitVector m + h • unitVector l)) (p j) (r j) : ℂ) * q x * star (Q j x)
  let B : Fin d → Vec d → ℂ := fun j x =>
    (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (r j) -
      ω.1 (x + s • unitVector m) (p j) (r j)) / h : ℝ) : ℂ) * v x * star (Q j x)
  let C : Fin d → Vec d → ℂ := fun j x =>
    (((ω.1 ((x + h • unitVector l) + s • unitVector m) (p j) (r j) -
      ω.1 (x + h • unitVector l) (p j) (r j)) / s : ℝ) : ℂ) * q₀ x * star (Q j x)
  let D : Fin d → Vec d → ℂ := fun j x =>
    (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (r j) -
      ω.1 (x + s • unitVector m) (p j) (r j) -
      (ω.1 (x + h • unitVector l) (p j) (r j) - ω.1 x (p j) (r j))) / h / s : ℝ) : ℂ) * f x * star (Q j x)
  have ha := u4h3_translated_elliptic_single_sum_bound hΛ hell hsmooth
    (s • unitVector m + h • unitVector l) p r q Q
  have hb := u4h3_translated_commutator_single_sum_bound hsmooth l hh
    (s • unitVector m) p r v Q
  have hc := u4h3_translated_commutator_single_sum_bound hsmooth m hs
    (h • unitVector l) p r q₀ Q
  have hd := u4h3_mixed_commutator_single_sum_bound hsmooth l m hh hs p r f Q
  refine ⟨v, hv, ?_⟩
  have heq : (∑ j, ∫ x,
        ((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (r j) : ℂ) * q x +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (r j) -
          ω.1 (x + s • unitVector m) (p j) (r j)) / h : ℝ) : ℂ) * v x +
        (((ω.1 ((x + h • unitVector l) + s • unitVector m) (p j) (r j) -
          ω.1 (x + h • unitVector l) (p j) (r j)) / s : ℝ) : ℂ) * q₀ x +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j) (r j) -
          ω.1 (x + s • unitVector m) (p j) (r j) -
          (ω.1 (x + h • unitVector l) (p j) (r j) - ω.1 x (p j) (r j))) /
          h / s : ℝ) : ℂ) * f x) * star (Q j x)) =
      (∑ j, ∫ x, A j x) + (∑ j, ∫ x, B j x) +
        (∑ j, ∫ x, C j x) + (∑ j, ∫ x, D j x) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hai : Integrable (A j) volume := ha.1 j
    have hbi : Integrable (B j) volume := hb.1 j
    have hci : Integrable (C j) volume := hc.1 j
    have hdi : Integrable (D j) volume := hd.1 j
    calc
      _ = ∫ x, (A j + B j + C j + D j) x := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [A, B, C, D, Pi.add_apply, add_mul, add_assoc]
      _ = _ := by
        simp only [Pi.add_apply]
        have h₁ := integral_add ((hai.add hbi).add hci) hdi
        have h₂ := integral_add (hai.add hbi) hci
        have h₃ := integral_add hai hbi
        simp only [Pi.add_apply] at h₁ h₂ h₃
        rw [h₁, h₂, h₃]
  rw [heq]
  calc
    _ ≤ ‖∑ j, ∫ x, A j x‖ + ‖∑ j, ∫ x, B j x‖ +
        ‖∑ j, ∫ x, C j x‖ + ‖∑ j, ∫ x, D j x‖ := by
      have h₁ := norm_add_le ((∑ j, ∫ x, A j x) + (∑ j, ∫ x, B j x) +
        (∑ j, ∫ x, C j x)) (∑ j, ∫ x, D j x)
      have h₂ := norm_add_le ((∑ j, ∫ x, A j x) + (∑ j, ∫ x, B j x))
        (∑ j, ∫ x, C j x)
      have h₃ := norm_add_le (∑ j, ∫ x, A j x) (∑ j, ∫ x, B j x)
      linarith
    _ ≤ Λ * ‖q‖ * (∑ j, ‖Q j‖) + M 1 * ‖G m‖ * (∑ j, ‖Q j‖) +
        M 1 * ‖G l‖ * (∑ j, ‖Q j‖) + M 2 * ‖f‖ * (∑ j, ‖Q j‖) := by
      exact add_le_add (add_le_add (add_le_add ha.2 hvb) hq₀b) hd.2
    _ = _ := by ring


/-- The transpose drift tested against the double backward quotient is
controlled by the gradient, the double quotient, and the energy gradient. -/
theorem u4h3_transpose_drift_pairing_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) (i : Fin d)
    (ha : ∀ j, MemLp (fun x => (ω.1 x j i : ℂ)) ∞ volume)
    {f q₀ q : Lp ℂ 2 (volume : Measure (Vec d))}
    (G Q R T : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l m : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (hq₀ : (q₀ : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)))
    (hq : (q : Vec d → ℂ) =ᵐ[volume]
      (fun x => (q₀ (x + s • unitVector m) - q₀ x) / (s : ℂ)))
    (hR : ∀ j, (R j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (s : ℂ)⁻¹ * ((star (Q j)) (x - s • unitVector m) - (star (Q j)) x)))
    (hT : ∀ j, (T j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * (R j (x - h • unitVector l) - R j x))) :
    ‖∑ j, ∫ x, (ω.1 x j i : ℂ) * f x * T j x‖ ≤
      (Λ * ‖q‖ + M 1 * ‖G m‖ + M 1 * ‖G l‖ + M 2 * ‖f‖) *
        (∑ j, ‖Q j‖) := by
  obtain ⟨v, hv, hb⟩ := u4h3_transpose_drift_expansion_bound hΛ hell hsmooth
    G Q hG l m hh hs hq₀ (fun j => j) (fun _ => i)
  have heq : (∑ j, ∫ x, (ω.1 x j i : ℂ) * f x * T j x) =
      ∑ j, ∫ x,
        ((ω.1 ((x + s • unitVector m) + h • unitVector l) j i : ℂ) * q x +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) j i -
          ω.1 (x + s • unitVector m) j i) / h : ℝ) : ℂ) * v x +
        (((ω.1 ((x + h • unitVector l) + s • unitVector m) j i -
          ω.1 (x + h • unitVector l) j i) / s : ℝ) : ℂ) * q₀ x +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) j i -
          ω.1 (x + s • unitVector m) j i -
          (ω.1 (x + h • unitVector l) j i - ω.1 x j i)) / h / s : ℝ) : ℂ) * f x) *
          star (Q j x) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [u4h3_double_backward_principal_pairing_graph
      (fun x => (ω.1 x j i : ℂ)) (ha j) f q₀ q (star (Q j)) (R j) (T j)
      l m h s hq₀ hq (hR j) (hT j)]
    apply integral_congr_ae
    filter_upwards [hv, hq₀, Lp.coeFn_star (Q j)] with x hvx hqx hstar
    rw [hvx, hqx, hstar]
    have hcomm : (x + s • unitVector m) + h • unitVector l =
        (x + h • unitVector l) + s • unitVector m := by abel
    simp only [← hcomm, Complex.ofReal_sub, Complex.ofReal_div, sub_div, Pi.star_apply]
  rw [heq]
  exact hb

/-- Absorb a square-root energy term while retaining a uniform multiple of
    the supplied data energy. -/
theorem u4h3_absorb_sqrt_energy (A B E X : ℝ)
    (hE : 0 ≤ E) (hX : 0 ≤ X)
    (h : X ≤ A * E + B * Real.sqrt E * Real.sqrt X) :
    X ≤ (2 * A + B ^ 2) * E := by
  have he := Real.sq_sqrt hE
  have hx := Real.sq_sqrt hX
  have hn := sq_nonneg (B * Real.sqrt E - Real.sqrt X)
  nlinarith [he, hx]


/-- A uniform energy bound for actual double quotient graphs controls the
quotient of the supplied Hessian, by compactness and uniqueness of gradients. -/
theorem u4h3_hessian_quotient_of_double_quotient_bound {d : ℕ}
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (l m : Fin d) (h : ℝ) (hh : h ≠ 0)
    (q₀ : Lp ℂ 2 (volume : Measure (Vec d)))
    (Q₀ : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hq₀ : IsPhysicalH1Graph volume (Or.inl rfl) q₀ Q₀)
    (hQ₀ : ∀ j, (Q₀ j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ)))
    (C : ℝ) (hC : 0 ≤ C)
    (hdouble : ∀ n, ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (q₀ (x + Blueprint.C3SublinearC1.mollifierScale n • unitVector m) - q₀ x) /
          (Blueprint.C3SublinearC1.mollifierScale n : ℂ)) ∧
      (∑ j, ‖Q j‖ ^ 2) ≤ C) :
    (∑ k, ((eLpNorm
      (fun x => (H m k (x + h • unitVector l) - H m k x) / (h : ℂ))
      2 (volume : Measure (Vec d))).toReal) ^ 2) ≤ C + ‖H m l‖ ^ 2 := by
  classical
  let s := Blueprint.C3SublinearC1.mollifierScale
  have hs := u4h2_quotient_scale_properties
  choose q Q hgraph hq hb using hdouble
  have hn : 0 ≤ C + ‖H m l‖ ^ 2 := by positivity
  have hqbound (n : ℕ) : ‖q n‖ ≤ ‖H m l‖ := by
    have hsne : s n ≠ 0 := abs_pos.mp (hs.1 n).1
    exact (c23_forward_difference_quotient_norm_le hq₀ m (s n) hsne (hq n)).trans
      (c23_forward_difference_quotient_norm_le (hH m) l h hh (hQ₀ m))
  have hbound (n : ℕ) : ‖q n‖ ^ 2 + (∑ j, ‖Q n j‖ ^ 2) ≤
      (Real.sqrt (C + ‖H m l‖ ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt hn]
    nlinarith [hqbound n, norm_nonneg (q n), norm_nonneg (H m l), hb n]
  obtain ⟨K, hK, hKb⟩ := u4h2_physical_H1_of_actual_quotients q₀ Q₀ m hq₀
    hs.2 q Q (Real.sqrt (C + ‖H m l‖ ^ 2)) (Real.sqrt_nonneg _) hq hbound hgraph
  obtain ⟨v, W, hW, hv, _, heq⟩ := c23_physical_forward_difference_quotient_graph (hH m) l h
  have hv' : Q₀ m = v := Lp.ext ((hQ₀ m).trans hv.symm)
  rw [← hv'] at hW
  have hKW := physicalH1Graph_gradient_unique volume (Or.inl rfl) (Q₀ m) K W hK hW
  rw [Real.sq_sqrt hn, hKW] at hKb
  simpa only [heq] using hKb

/-- The three coefficient errors in the differentiated principal term have
one uniform bound, for either orientation of the matrix coefficients. -/
theorem u4h3_principal_commutators_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (l m : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (p q : Fin d → Fin d → Fin d) :
    ∃ V W : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ k, (V k : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G k (x + s • unitVector m) - G k x) / (s : ℂ))) ∧
      (∀ k, (W k : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G k (x + h • unitVector l) - G k x) / (h : ℂ))) ∧
      ‖(∑ j, ∑ k, ∫ x,
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) -
          ω.1 (x + s • unitVector m) (p j k) (q j k)) / h : ℝ) : ℂ) *
          V k x * star (Q j x)) +
        (∑ j, ∑ k, ∫ x,
        (((ω.1 ((x + h • unitVector l) + s • unitVector m) (p j k) (q j k) -
          ω.1 (x + h • unitVector l) (p j k) (q j k)) / s : ℝ) : ℂ) *
          W k x * star (Q j x)) +
        (∑ j, ∑ k, ∫ x,
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) -
          ω.1 (x + s • unitVector m) (p j k) (q j k) -
          (ω.1 (x + h • unitVector l) (p j k) (q j k) -
            ω.1 x (p j k) (q j k))) / h / s : ℝ) : ℂ) *
          G k x * star (Q j x))‖ ≤
        (M 1 * (∑ k, ‖H k m‖) + M 1 * (∑ k, ‖H k l‖) +
          M 2 * (∑ k, ‖G k‖)) * (∑ j, ‖Q j‖) := by
  obtain ⟨V, W, hV, hW, hB, hC⟩ :=
    u4h3_first_commutators_hessian_bound hsmooth G H hH Q l m hh hs p q
  have hD := (u4h3_mixed_commutator_sum_bound hsmooth l m hh hs p q G Q).2
  refine ⟨V, W, hV, hW, ?_⟩
  apply le_trans (norm_add_le _ _)
  apply le_trans (add_le_add (norm_add_le _ _) (le_refl _))
  convert add_le_add (add_le_add hB hC) hD using 1 <;> ring


/-- The expanded twice-differenced principal pairing differs from its
translated coercive part by the uniformly bounded coefficient commutators. -/
theorem u4h3_principal_expansion_error_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (l m : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (p q : Fin d → Fin d → Fin d) :
    ‖(∑ j, ∑ k, ∫ x,
        ((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) : ℂ) * Q k x +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) : ℂ) -
          (ω.1 (x + s • unitVector m) (p j k) (q j k) : ℂ)) / (h : ℂ)) *
          ((G k (x + s • unitVector m) - G k x) / (s : ℂ)) +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) : ℂ) -
          (ω.1 (x + h • unitVector l) (p j k) (q j k) : ℂ)) / (s : ℂ)) *
          ((G k (x + h • unitVector l) - G k x) / (h : ℂ)) +
        ((((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) : ℂ) -
          (ω.1 (x + s • unitVector m) (p j k) (q j k) : ℂ)) / (h : ℂ) -
          ((ω.1 (x + h • unitVector l) (p j k) (q j k) : ℂ) -
          (ω.1 x (p j k) (q j k) : ℂ)) / (h : ℂ)) / (s : ℂ)) * G k x) *
          (star (Q j)) x) -
      (∑ j, ∑ k, ∫ x, (ω.1 (x + (s • unitVector m + h • unitVector l))
        (p j k) (q j k) : ℂ) * Q k x * star (Q j x))‖ ≤
      (M 1 * (∑ k, ‖H k m‖) + M 1 * (∑ k, ‖H k l‖) +
        M 2 * (∑ k, ‖G k‖)) * (∑ j, ‖Q j‖) := by
  obtain ⟨V, W, hV, hW, hbound⟩ :=
    u4h3_principal_commutators_bound hsmooth G H hH Q l m hh hs p q
  let A : Fin d → Fin d → Vec d → ℂ := fun j k x =>
    (ω.1 (x + (s • unitVector m + h • unitVector l)) (p j k) (q j k) : ℂ) * Q k x * star (Q j x)
  let B : Fin d → Fin d → Vec d → ℂ := fun j k x =>
    (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) -
      ω.1 (x + s • unitVector m) (p j k) (q j k)) / h : ℝ) : ℂ) * V k x * star (Q j x)
  let C : Fin d → Fin d → Vec d → ℂ := fun j k x =>
    (((ω.1 ((x + h • unitVector l) + s • unitVector m) (p j k) (q j k) -
      ω.1 (x + h • unitVector l) (p j k) (q j k)) / s : ℝ) : ℂ) * W k x * star (Q j x)
  let D : Fin d → Fin d → Vec d → ℂ := fun j k x =>
    (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) -
      ω.1 (x + s • unitVector m) (p j k) (q j k) -
      (ω.1 (x + h • unitVector l) (p j k) (q j k) - ω.1 x (p j k) (q j k))) / h / s : ℝ) : ℂ) * G k x * star (Q j x)
  have ha (j k : Fin d) : Integrable (A j k) volume :=
    (u4h3_translated_elliptic_single_sum_bound hΛ hell hsmooth
      (s • unitVector m + h • unitVector l) (fun j => p j k) (fun j => q j k) (Q k) Q).1 j
  have hb : ∀ j k, Integrable (B j k) volume :=
    (u4h3_translated_commutator_sum_bound hsmooth l hh (s • unitVector m) p q V Q).1
  have hc : ∀ j k, Integrable (C j k) volume :=
    (u4h3_translated_commutator_sum_bound hsmooth m hs (h • unitVector l) p q W Q).1
  have hd : ∀ j k, Integrable (D j k) volume :=
    (u4h3_mixed_commutator_sum_bound hsmooth l m hh hs p q G Q).1
  have heq : (∑ j, ∑ k, ∫ x,
        ((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) : ℂ) * Q k x +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) : ℂ) -
          (ω.1 (x + s • unitVector m) (p j k) (q j k) : ℂ)) / (h : ℂ)) *
          ((G k (x + s • unitVector m) - G k x) / (s : ℂ)) +
        (((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) : ℂ) -
          (ω.1 (x + h • unitVector l) (p j k) (q j k) : ℂ)) / (s : ℂ)) *
          ((G k (x + h • unitVector l) - G k x) / (h : ℂ)) +
        ((((ω.1 ((x + s • unitVector m) + h • unitVector l) (p j k) (q j k) : ℂ) -
          (ω.1 (x + s • unitVector m) (p j k) (q j k) : ℂ)) / (h : ℂ) -
          ((ω.1 (x + h • unitVector l) (p j k) (q j k) : ℂ) -
          (ω.1 x (p j k) (q j k) : ℂ)) / (h : ℂ)) / (s : ℂ)) * G k x) *
          (star (Q j)) x) =
      (∑ j, ∑ k, ∫ x, A j k x) + (∑ j, ∑ k, ∫ x, B j k x) +
        (∑ j, ∑ k, ∫ x, C j k x) + (∑ j, ∑ k, ∫ x, D j k x) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    calc
      _ = ∫ x, (A j k + B j k + C j k + D j k) x := by
        apply integral_congr_ae
        filter_upwards [hV k, hW k, Lp.coeFn_star (Q j)] with x hv hw hstar
        change (star (Q j) : Lp ℂ 2 (volume : Measure (Vec d))) x = star (Q j x) at hstar
        simp only [A, B, C, D, Pi.add_apply, hstar, hv, hw,
          Complex.ofReal_sub, Complex.ofReal_div, sub_div, add_mul, add_assoc]
        congr 2 <;> congr 1 <;> simp only [add_assoc, add_comm, add_left_comm]
      _ = _ := by
        have h₁ := integral_add (((ha j k).add (hb j k)).add (hc j k)) (hd j k)
        have h₂ := integral_add ((ha j k).add (hb j k)) (hc j k)
        have h₃ := integral_add (ha j k) (hb j k)
        simp only [Pi.add_apply] at h₁ h₂ h₃ ⊢
        rw [h₁, h₂, h₃]
  rw [heq]
  have hident : (∑ j, ∑ k, ∫ x, A j k x) + (∑ j, ∑ k, ∫ x, B j k x) +
        (∑ j, ∑ k, ∫ x, C j k x) + (∑ j, ∑ k, ∫ x, D j k x) -
        (∑ j, ∑ k, ∫ x, A j k x) =
      (∑ j, ∑ k, ∫ x, B j k x) + (∑ j, ∑ k, ∫ x, C j k x) +
        (∑ j, ∑ k, ∫ x, D j k x) := by ring
  change ‖(∑ j, ∑ k, ∫ x, A j k x) + (∑ j, ∑ k, ∫ x, B j k x) +
    (∑ j, ∑ k, ∫ x, C j k x) + (∑ j, ∑ k, ∫ x, D j k x) -
    (∑ j, ∑ k, ∫ x, A j k x)‖ ≤ _
  rw [hident]
  exact hbound


/-- Rewrite the principal term in the weak equation as its individual
    integrable coefficient pairings. -/
theorem u4h3_principal_integral_sum {d : ℕ} {a : Vec d → Mat d}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (G T : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (p q : Fin d → Fin d → Fin d) :
    (∫ x, ∑ j, ∑ k, (a x (p j k) (q j k) : ℂ) * G k x * T j x) =
      ∑ j, ∑ k, ∫ x, (a x (p j k) (q j k) : ℂ) * G k x * T j x := by
  have hint (j k : Fin d) : Integrable
      (fun x => (a x (p j k) (q j k) : ℂ) * G k x * T j x) volume :=
    ((ha (p j k) (q j k)).mul (r := 2) (Lp.memLp (G k))).integrable_mul
      (Lp.memLp (T j))
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
  simp_rw [integral_finsetSum _ (fun k _ => hint _ k)]

/-- The translated principal energy is coercive in either generator orientation,
    even when expressed as a sum of individual pairings. -/
theorem u4h3_translated_principal_energy {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (z : Vec d)
    (transpose : Bool) :
    Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
      (∑ j, ∑ k, ∫ x,
        (ω.1 (x + z) (if transpose then k else j) (if transpose then j else k) : ℂ) *
          Q k x * star (Q j x)).re := by
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  have hint : ∀ j k, Integrable (fun x =>
      (ω.1 (x + z) (if transpose then k else j) (if transpose then j else k) : ℂ) *
        Q k x * star (Q j x)) volume := by
    intro j k
    exact (u4h3_translated_elliptic_single_sum_bound hΛ hell hsmooth z
      (fun j => if transpose then k else j) (fun j => if transpose then j else k)
      (Q k) Q).1 j
  have hsum : (∫ x, ∑ j, ∑ k,
      (ω.1 (x + z) (if transpose then k else j) (if transpose then j else k) : ℂ) *
        Q k x * star (Q j x)) =
      ∑ j, ∑ k, ∫ x,
        (ω.1 (x + z) (if transpose then k else j) (if transpose then j else k) : ℂ) *
          Q k x * star (Q j x) := by
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
    simp_rw [integral_finsetSum _ (fun k _ => hint _ k)]
  cases transpose with
  | false =>
    have hc := c23_translated_principal_coercivity ω.1 ha hA Q z
    simp only [Bool.false_eq_true, ↓reduceIte] at hsum ⊢
    rw [← hsum]
    exact hc
  | true =>
    have hc := c23_translated_transpose_principal_coercivity ω.1 ha hA Q z
    simp only [↓reduceIte] at hsum ⊢
    rw [← hsum]
    exact hc

/-- A bound on the principal expansion error transfers coercivity to the
    expanded pairing. -/
theorem u4h3_energy_of_principal_error {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (z : Vec d)
    (transpose : Bool) (P : ℂ) (E : ℝ)
    (herror : ‖P - (∑ j, ∑ k, ∫ x,
      (ω.1 (x + z) (if transpose then k else j) (if transpose then j else k) : ℂ) *
        Q k x * star (Q j x))‖ ≤ E) :
    Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤ ‖P‖ + E := by
  let A : ℂ := ∑ j, ∑ k, ∫ x,
    (ω.1 (x + z) (if transpose then k else j) (if transpose then j else k) : ℂ) *
      Q k x * star (Q j x)
  have hc : Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤ A.re :=
    u4h3_translated_principal_energy hΛ hell hsmooth Q z transpose
  change ‖P - A‖ ≤ E at herror
  have hn : ‖A‖ ≤ ‖P‖ + E := by
    calc
      ‖A‖ = ‖P - (P - A)‖ := by congr 1 <;> ring
      _ ≤ ‖P‖ + ‖P - A‖ := norm_sub_le _ _
      _ ≤ ‖P‖ + E := add_le_add_right herror ‖P‖
  exact hc.trans ((Complex.re_le_norm A).trans hn)

/-- Coercivity from the weak identity, with the forcing and drift terms
    kept explicit for their separate estimates. -/
theorem u4h3_energy_of_weak_identity {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (z : Vec d)
    (transpose : Bool) (P F D ζ : ℂ) (E : ℝ)
    (herror : ‖P - (∑ j, ∑ k, ∫ x,
      (ω.1 (x + z) (if transpose then k else j) (if transpose then j else k) : ℂ) *
        Q k x * star (Q j x))‖ ≤ E)
    (hweak : F = -(1 / 2 : ℂ) * P + ζ * D) :
    Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤ 2 * (‖F‖ + ‖ζ‖ * ‖D‖) + E := by
  have hp : P = 2 * (ζ * D - F) := by linear_combination 2 * hweak
  have hn : ‖P‖ ≤ 2 * (‖F‖ + ‖ζ‖ * ‖D‖) := by
    rw [hp, norm_mul]
    have hh := norm_sub_le (ζ * D) F
    rw [norm_mul] at hh
    norm_num at ⊢
    nlinarith
  have hc := u4h3_energy_of_principal_error hΛ hell hsmooth Q z transpose P E herror
  linarith

/-- The principal term in the double-quotient weak equation differs from
its translated coercive energy by the controlled coefficient commutators. -/
theorem u4h3_double_quotient_principal_error {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (Q₀ Q R T : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (l m : Fin d) {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0)
    (hQ₀ : ∀ j, (Q₀ j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ)))
    (hQ : ∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (Q₀ j (x + s • unitVector m) - Q₀ j x) / (s : ℂ)))
    (hR : ∀ j, (R j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (s : ℂ)⁻¹ * ((star (Q j)) (x - s • unitVector m) - (star (Q j)) x)))
    (hT : ∀ j, (T j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * (R j (x - h • unitVector l) - R j x)))
    (transpose : Bool) :
    ‖(∫ x, ∑ j, ∑ k,
        (ω.1 x (if transpose then k else j) (if transpose then j else k) : ℂ) * G k x * T j x) -
      (∑ j, ∑ k, ∫ x,
        (ω.1 (x + (s • unitVector m + h • unitVector l))
          (if transpose then k else j) (if transpose then j else k) : ℂ) *
          Q k x * star (Q j x))‖ ≤
      (M 1 * (∑ k, ‖H k m‖) + M 1 * (∑ k, ‖H k l‖) +
        M 2 * (∑ k, ‖G k‖)) * (∑ j, ‖Q j‖) := by
  let p : Fin d → Fin d → Fin d := fun j k => if transpose then k else j
  let q : Fin d → Fin d → Fin d := fun j k => if transpose then j else k
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  rw [u4h3_principal_integral_sum ha G T p q]
  have heach (j k : Fin d) := u4h3_double_backward_principal_pairing_graph
    (fun x => (ω.1 x (p j k) (q j k) : ℂ)) (ha (p j k) (q j k))
    (G k) (Q₀ k) (Q k) (star (Q j)) (R j) (T j) l m h s
    (hQ₀ k) (hQ k) (hR j) (hT j)
  simp_rw [heach]
  exact u4h3_principal_expansion_error_bound hΛ hell hsmooth G H hH Q l m hh hs p q


/-- Coercive estimate for successive actual forward quotients of a forward
    generator pair, retaining the supplied first quotient. -/
theorem u4h3_forward_double_quotient_energy_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f g q₀ : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H Q₀ : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hHess : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (Hess j))
    (hJ : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (hq₀ : IsPhysicalH1Graph volume (Or.inl rfl) q₀ Q₀)
    (l m : Fin d) (h s : ℝ) (hh : h ≠ 0) (hs : s ≠ 0)
    (hQ₀ : ∀ j, (Q₀ j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (q₀ (x + s • unitVector m) - q₀ x) / (s : ℂ)) ∧
      Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
        (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * (∑ j, ‖Hess j l‖) +
          M 1 * (∑ j, ‖G j‖)) + M 1 * (∑ j, ‖Hess j m‖) +
          M 1 * (∑ j, ‖Hess j l‖) + M 2 * (∑ j, ‖G j‖)) *
          (∑ j, ‖Q j‖) := by
  obtain ⟨q, Q, hqQ, hq, hQ, _⟩ :=
    c23_physical_forward_difference_quotient_graph hq₀ m s
  obtain ⟨r, t, R, T, _, _, hr, hR, ht, hT, hw⟩ :=
    u4h3_forward_double_backward_test hfg hG (physicalH1Graph_star q Q hqQ) l m h s
  have he := u4h3_double_quotient_principal_error hΛ hell hsmooth G Hess hHess
    Q₀ Q R T l m hh hs hQ₀ hQ hR hT false
  have hc := u4h3_energy_of_weak_identity hΛ hell hsmooth Q
    (s • unitVector m + h • unitVector l) false _ _ _ ζ _ he hw
  have hf := u4h3_double_backward_energy_forcing_bound g q r t H Q hJ hqQ l m h s hh hs hr ht
  have hd := u4h3_forward_double_force_bound hΛ hell hsmooth i l m hh hs G Hess hHess hqQ hr ht
  have hsum : ‖Q m‖ ≤ ∑ j, ‖Q j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (Q j)) (Finset.mem_univ m)
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hM : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  have hcoef : 0 ≤ Λ * (∑ j, ‖Hess j l‖) + M 1 * (∑ j, ‖G j‖) := by positivity
  have hf' := hf.trans (mul_le_mul_of_nonneg_left hsum (norm_nonneg (H l)))
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hsum hcoef)
  refine ⟨q, Q, hqQ, hq, ?_⟩
  nlinarith [mul_nonneg (norm_nonneg ζ) (sub_nonneg.mpr hd')]

/-- Absorb a finite-family coercive bound into a bound independent of the
    difference-quotient steps. -/
theorem u4h3_finite_energy_absorption {d : ℕ} {Λ A : ℝ}
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hΛ : 1 ≤ Λ) (hA : 0 ≤ A)
    (h : Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤ A * (∑ j, ‖Q j‖)) :
    (∑ j, ‖Q j‖ ^ 2) ≤ (Λ * A) ^ 2 * (d : ℝ) := by
  classical
  let X : ℝ := ∑ j, ‖Q j‖ ^ 2
  let S : ℝ := ∑ j, ‖Q j‖
  let C : ℝ := (Λ * A) ^ 2 * (d : ℝ)
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcs : S ^ 2 ≤ (d : ℝ) * X := by
    dsimp [S, X]
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d => (1 : ℝ))
        (fun j => ‖Q j‖)
  have hx : X ≤ (Λ * A) * S := by
    have hh : Λ * (Λ⁻¹ * X) ≤ Λ * (A * S) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hΛpos)
    calc
      X = Λ * (Λ⁻¹ * X) := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hΛpos), one_mul]
      _ ≤ Λ * (A * S) := hh
      _ = (Λ * A) * S := by ring
  have hsq : X ^ 2 ≤ C * X := by
    calc
      X ^ 2 ≤ ((Λ * A) * S) ^ 2 :=
        (sq_le_sq₀ hX (mul_nonneg (mul_nonneg (le_of_lt hΛpos) hA) hS)).mpr hx
      _ = (Λ * A) ^ 2 * S ^ 2 := by ring
      _ ≤ (Λ * A) ^ 2 * ((d : ℝ) * X) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = C * X := by dsimp [C]; ring
  by_cases hz : X = 0
  · simpa [X, hz] using hC
  · have hp : 0 < X := lt_of_le_of_ne hX (Ne.symm hz)
    have hh : X * X ≤ C * X := by nlinarith [hsq]
    exact le_of_mul_le_mul_right hh hp

/-- A step-independent energy bound for actual forward double quotients. -/
theorem u4h3_forward_double_quotient_uniform_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f g q₀ : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H Q₀ : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hHess : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (Hess j))
    (hJ : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (hq₀ : IsPhysicalH1Graph volume (Or.inl rfl) q₀ Q₀)
    (l m : Fin d) (h s : ℝ) (hh : h ≠ 0) (hs : s ≠ 0)
    (hQ₀ : ∀ j, (Q₀ j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (q₀ (x + s • unitVector m) - q₀ x) / (s : ℂ)) ∧
      (∑ j, ‖Q j‖ ^ 2) ≤
        (Λ * (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * (∑ j, ‖Hess j l‖) +
          M 1 * (∑ j, ‖G j‖)) + M 1 * (∑ j, ‖Hess j m‖) +
          M 1 * (∑ j, ‖Hess j l‖) + M 2 * (∑ j, ‖G j‖))) ^ 2 * (d : ℝ) := by
  obtain ⟨q, Q, hqQ, hq, he⟩ :=
    u4h3_forward_double_quotient_energy_bound Hess hΛ hell hsmooth hfg hG hHess hJ hq₀ l m h s hh hs hQ₀
  have hM1 : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  have hM2 : 0 ≤ M 2 := by
    obtain ⟨A, B, hA, hB, hAB, _⟩ := hsmooth.2 2 (by norm_num)
    linarith
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hcoef : 0 ≤ 2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * (∑ j, ‖Hess j l‖) +
      M 1 * (∑ j, ‖G j‖)) + M 1 * (∑ j, ‖Hess j m‖) +
      M 1 * (∑ j, ‖Hess j l‖) + M 2 * (∑ j, ‖G j‖) := by positivity
  exact ⟨q, Q, hqQ, hq, u4h3_finite_energy_absorption Q hΛ hcoef he⟩


/-- The forward generator equation bounds difference quotients of the supplied
Hessian uniformly in the quotient step. -/
theorem u4h3_forward_hessian_quotient_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hHess : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (Hess j))
    (hJ : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (l m : Fin d) (h : ℝ) (hh : h ≠ 0) :
    (∑ k, ((eLpNorm
      (fun x => (Hess m k (x + h • unitVector l) - Hess m k x) / (h : ℂ))
      2 (volume : Measure (Vec d))).toReal) ^ 2) ≤
      (Λ * (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * (∑ j, ‖Hess j l‖) +
        M 1 * (∑ j, ‖G j‖)) + M 1 * (∑ j, ‖Hess j m‖) +
        M 1 * (∑ j, ‖Hess j l‖) + M 2 * (∑ j, ‖G j‖))) ^ 2 * (d : ℝ) +
        ‖Hess m l‖ ^ 2 := by
  obtain ⟨q₀, Q₀, hq₀, _, hQ₀, _⟩ :=
    c23_physical_forward_difference_quotient_graph hG l h
  apply u4h3_hessian_quotient_of_double_quotient_bound G Hess hHess l m h hh q₀ Q₀ hq₀ hQ₀
  · positivity
  · intro n
    exact u4h3_forward_double_quotient_uniform_bound Hess hΛ hell hsmooth hfg hG hHess hJ
      hq₀ l m h (Blueprint.C3SublinearC1.mollifierScale n) hh
      (abs_pos.mp (u4h2_quotient_scale_properties.1 n).1) hQ₀

/-- Uniform energy control for actual transpose generator double quotients. -/
theorem u4h3_transpose_double_quotient_uniform_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f g q₀ : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H Q₀ : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hHess : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (Hess j))
    (hJ : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (hq₀ : IsPhysicalH1Graph volume (Or.inl rfl) q₀ Q₀)
    (l m : Fin d) (h s : ℝ) (hh : h ≠ 0) (hs : s ≠ 0)
    (hq₀repr : (q₀ : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)))
    (hQ₀ : ∀ j, (Q₀ j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (q₀ (x + s • unitVector m) - q₀ x) / (s : ℂ)) ∧
      (∑ j, ‖Q j‖ ^ 2) ≤
        (Λ * (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * ‖Hess m l‖ +
          M 1 * ‖G m‖ + M 1 * ‖G l‖ + M 2 * ‖f‖) +
          M 1 * (∑ j, ‖Hess j m‖) + M 1 * (∑ j, ‖Hess j l‖) +
          M 2 * (∑ j, ‖G j‖))) ^ 2 * (d : ℝ) := by
  obtain ⟨q, Q, hqQ, hq, hQ, _⟩ :=
    c23_physical_forward_difference_quotient_graph hq₀ m s
  obtain ⟨r, t, R, T, _, _, hr, hR, ht, hT, hw⟩ :=
    u4h3_transpose_double_backward_test hfg hG (physicalH1Graph_star q Q hqQ) l m h s
  have he := u4h3_double_quotient_principal_error hΛ hell hsmooth G Hess hHess
    Q₀ Q R T l m hh hs hQ₀ hQ hR hT true
  have hc := u4h3_energy_of_weak_identity hΛ hell hsmooth Q
    (s • unitVector m + h • unitVector l) true _ _ _ ζ _ he hw
  have hf := u4h3_double_backward_energy_forcing_bound g q r t H Q hJ hqQ l m h s hh hs hr ht
  have ha : ∀ j, MemLp (fun x => (ω.1 x j i : ℂ)) ∞ volume := fun j =>
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous) j i
  have hd := u4h3_transpose_drift_pairing_bound hΛ hell hsmooth i ha G Q R T hG l m hh hs hq₀repr hq hR hT
  have hint : ∀ j, Integrable (fun x => (ω.1 x j i : ℂ) * f x * T j x) volume :=
    fun j => ((ha j).mul (r := 2) (Lp.memLp f)).integrable_mul (Lp.memLp (T j))
  have heq : (∫ x, f x * (∑ j, (ω.1 x j i : ℂ) * T j x)) =
      ∑ j, ∫ x, (ω.1 x j i : ℂ) * f x * T j x := by
    calc
      _ = ∫ x, ∑ j, (ω.1 x j i : ℂ) * f x * T j x := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := integral_finsetSum _ (fun j _ => hint j)
  rw [heq] at hc
  have hqbound : ‖q‖ ≤ ‖Hess m l‖ :=
    (c23_forward_difference_quotient_norm_le hq₀ m s hs hq).trans
      (c23_forward_difference_quotient_norm_le (hHess m) l h hh (hQ₀ m))
  have hsum : ‖Q m‖ ≤ ∑ j, ‖Q j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (Q j)) (Finset.mem_univ m)
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hM1 : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  have hM2 : 0 ≤ M 2 := by
    obtain ⟨A, B, hA, hB, hAB, _⟩ := hsmooth.2 2 (by norm_num)
    linarith
  have hd' : ‖∑ j, ∫ x, (ω.1 x j i : ℂ) * f x * T j x‖ ≤
      (Λ * ‖Hess m l‖ + M 1 * ‖G m‖ + M 1 * ‖G l‖ + M 2 * ‖f‖) *
        (∑ j, ‖Q j‖) := hd.trans (mul_le_mul_of_nonneg_right (by
          nlinarith [mul_nonneg hΛ0 (sub_nonneg.mpr hqbound)]) (by positivity))
  have hf' := hf.trans (mul_le_mul_of_nonneg_left hsum (norm_nonneg (H l)))
  have hcoef : 0 ≤ 2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * ‖Hess m l‖ +
      M 1 * ‖G m‖ + M 1 * ‖G l‖ + M 2 * ‖f‖) +
      M 1 * (∑ j, ‖Hess j m‖) + M 1 * (∑ j, ‖Hess j l‖) +
      M 2 * (∑ j, ‖G j‖) := by positivity
  have hb : Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
      (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * ‖Hess m l‖ +
        M 1 * ‖G m‖ + M 1 * ‖G l‖ + M 2 * ‖f‖) +
        M 1 * (∑ j, ‖Hess j m‖) + M 1 * (∑ j, ‖Hess j l‖) +
        M 2 * (∑ j, ‖G j‖)) * (∑ j, ‖Q j‖) := by
    nlinarith [mul_nonneg (norm_nonneg ζ) (sub_nonneg.mpr hd')]
  exact ⟨q, Q, hqQ, hq, u4h3_finite_energy_absorption Q hΛ hcoef hb⟩


/-- The transpose generator equation controls the supplied Hessian quotients. -/
theorem u4h3_transpose_hessian_quotient_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hHess : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (Hess j))
    (hJ : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    (l m : Fin d) (h : ℝ) (hh : h ≠ 0) :
    (∑ k, ((eLpNorm
      (fun x => (Hess m k (x + h • unitVector l) - Hess m k x) / (h : ℂ))
      2 (volume : Measure (Vec d))).toReal) ^ 2) ≤
      (Λ * (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * ‖Hess m l‖ +
        M 1 * ‖G m‖ + M 1 * ‖G l‖ + M 2 * ‖f‖) +
        M 1 * (∑ j, ‖Hess j m‖) + M 1 * (∑ j, ‖Hess j l‖) +
        M 2 * (∑ j, ‖G j‖))) ^ 2 * (d : ℝ) + ‖Hess m l‖ ^ 2 := by
  obtain ⟨q₀, Q₀, hq₀, hq₀repr, hQ₀, _⟩ :=
    c23_physical_forward_difference_quotient_graph hG l h
  apply u4h3_hessian_quotient_of_double_quotient_bound G Hess hHess l m h hh q₀ Q₀ hq₀ hQ₀
  · positivity
  · intro n
    exact u4h3_transpose_double_quotient_uniform_bound Hess hΛ hell hsmooth hfg hG hHess hJ
      hq₀ l m h (Blueprint.C3SublinearC1.mollifierScale n) hh
      (abs_pos.mp (u4h2_quotient_scale_properties.1 n).1) hq₀repr hQ₀


/-- Bounds depending on a finite pair of directions suffice for H3. -/
theorem u4h3_physical_H3_of_directional_bounds {d : ℕ}
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (C : Fin d → Fin d → ℝ) (hC : ∀ j l, 0 ≤ C j l)
    (hquotient : ∀ (j l : Fin d) (h : ℝ), 0 < |h| → |h| ≤ 1 →
      (∑ k, ((eLpNorm
        (fun x => (H j k (x + h • unitVector l) - H j k x) / (h : ℂ))
        2 (volume : Measure (Vec d))).toReal) ^ 2) ≤ C j l) :
    ∃ K : Fin d → Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ j k, IsPhysicalH1Graph volume (Or.inl rfl) (H j k) (K j k) := by
  classical
  let B : ℝ := ∑ j, ∑ l, C j l
  let E : ℝ := 1 + ∑ j, ∑ k, ‖H j k‖ ^ 2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => hC j l))
  have hE : 1 ≤ E := by
    dsimp [E]
    have h := Finset.sum_nonneg (s := Finset.univ) (fun j _ =>
      Finset.sum_nonneg (s := Finset.univ) (fun k _ => sq_nonneg ‖H j k‖))
    linarith
  have hfirst : ∀ j, (∑ k, ‖H j k‖ ^ 2) ≤ E := by
    intro j
    have h : (∑ k, ‖H j k‖ ^ 2) ≤ ∑ a, ∑ k, ‖H a k‖ ^ 2 :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun k _ => sq_nonneg ‖H a k‖)) (Finset.mem_univ j)
    dsimp [E]
    linarith
  have hq : ∀ (j l : Fin d) (h : ℝ), 0 < |h| → |h| ≤ 1 →
      (∑ k, ((eLpNorm
        (fun x => (H j k (x + h • unitVector l) - H j k x) / (h : ℂ))
        2 (volume : Measure (Vec d))).toReal) ^ 2) ≤ B * E := by
    intro j l h hh hh1
    have hc1 : C j l ≤ ∑ x, C j x :=
      Finset.single_le_sum (fun x _ => hC j x) (Finset.mem_univ l)
    have hc2 : (∑ x, C j x) ≤ B :=
      Finset.single_le_sum (fun x _ => Finset.sum_nonneg (fun y _ => hC x y)) (Finset.mem_univ j)
    have hBE : B ≤ B * E := by nlinarith
    exact (hquotient j l h hh hh1).trans (hc1.trans (hc2.trans hBE))
  obtain ⟨K, hK, _⟩ := u4h3_physical_H3_of_hessian_quotient_bounds G H hH B E hB (by linarith) hfirst hq
  exact ⟨K, hK⟩


/-- A generator pair with H2 input and H1 output has a supplied Hessian in H1. -/
theorem u4h3_generator_pair_H3 {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hHess : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (Hess j))
    (hJ : IsPhysicalH1Graph volume (Or.inl rfl) g H) :
    ∃ K : Fin d → Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ j k, IsPhysicalH1Graph volume (Or.inl rfl) (Hess j k) (K j k) := by
  rcases hfg with hf | ht
  · apply u4h3_physical_H3_of_directional_bounds G Hess hHess
      (fun m l => (Λ * (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * (∑ j, ‖Hess j l‖) +
        M 1 * (∑ j, ‖G j‖)) + M 1 * (∑ j, ‖Hess j m‖) +
        M 1 * (∑ j, ‖Hess j l‖) + M 2 * (∑ j, ‖G j‖))) ^ 2 * (d : ℝ) +
        ‖Hess m l‖ ^ 2)
    · intro m l; positivity
    · intro m l h hh _
      exact u4h3_forward_hessian_quotient_bound Hess hΛ hell hsmooth hf hG hHess hJ l m h (abs_pos.mp hh)
  · apply u4h3_physical_H3_of_directional_bounds G Hess hHess
      (fun m l => (Λ * (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * ‖Hess m l‖ +
        M 1 * ‖G m‖ + M 1 * ‖G l‖ + M 2 * ‖f‖) +
        M 1 * (∑ j, ‖Hess j m‖) + M 1 * (∑ j, ‖Hess j l‖) +
        M 2 * (∑ j, ‖G j‖))) ^ 2 * (d : ℝ) + ‖Hess m l‖ ^ 2)
    · intro m l; positivity
    · intro m l h hh _
      exact u4h3_transpose_hessian_quotient_bound Hess hΛ hell hsmooth ht hG hHess hJ l m h (abs_pos.mp hh)

end EinsteinFull
