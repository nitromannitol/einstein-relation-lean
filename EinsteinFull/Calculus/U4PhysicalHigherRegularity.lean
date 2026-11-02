import EinsteinFull.Calculus.U4PhysicalSemigroupH3

open EinsteinRelation MeasureTheory
open scoped ENNReal NNReal

namespace EinsteinFull

/-- A scaled spatial difference; choosing `c = h⁻¹` gives a difference quotient. -/
def u4HigherDifference {d : ℕ} (v : Vec d) (c : ℂ)
    (f : Vec d → ℂ) : Vec d → ℂ :=
  fun x => c * (f (x + v) - f x)

/-- Successive scaled spatial differences, in the order of the supplied list. -/
def u4HigherDifferences {d : ℕ} : List (Vec d × ℂ) → (Vec d → ℂ) → Vec d → ℂ
  | [], f => f
  | (v, c) :: rest, f => u4HigherDifferences rest (u4HigherDifference v c f)

/-- The product expansion keeps every translated coefficient term explicitly. -/
def u4HigherProductExpansion {d : ℕ} :
    List (Vec d × ℂ) → (Vec d → ℂ) → (Vec d → ℂ) → Vec d → ℂ
  | [], f, g => fun x => f x * g x
  | (v, c) :: rest, f, g => fun x =>
      u4HigherProductExpansion rest (u4HigherDifference v c f) (fun y => g (y + v)) x +
      u4HigherProductExpansion rest f (u4HigherDifference v c g) x

theorem u4HigherDifferences_add {d : ℕ} (steps : List (Vec d × ℂ))
    (f g : Vec d → ℂ) :
    u4HigherDifferences steps (fun x => f x + g x) =
      fun x => u4HigherDifferences steps f x + u4HigherDifferences steps g x := by
  induction steps generalizing f g with
  | nil => rfl
  | cons step rest ih =>
      rcases step with ⟨v, c⟩
      simp only [u4HigherDifferences]
      have h : u4HigherDifference v c (fun x => f x + g x) =
          (fun x => u4HigherDifference v c f x + u4HigherDifference v c g x) := by
        funext x
        simp only [u4HigherDifference]
        ring
      rw [h, ih]

/-- Discrete Leibniz formula at every order, retaining the translations. -/
theorem u4HigherDifferences_product {d : ℕ} (steps : List (Vec d × ℂ))
    (f g : Vec d → ℂ) :
    u4HigherDifferences steps (fun x => f x * g x) =
      u4HigherProductExpansion steps f g := by
  induction steps generalizing f g with
  | nil => rfl
  | cons step rest ih =>
      rcases step with ⟨v, c⟩
      simp only [u4HigherDifferences, u4HigherProductExpansion]
      have h : u4HigherDifference v c (fun x => f x * g x) =
          (fun x => u4HigherDifference v c f x * g (x + v) +
            f x * u4HigherDifference v c g x) := by
        funext x
        simp only [u4HigherDifference]
        ring
      rw [h, u4HigherDifferences_add, ih, ih]

/-- Backward differences are composed in the order dual to the forward list. -/
def u4HigherBackwardDifferences {d : ℕ} :
    List (Vec d × ℂ) → (Vec d → ℂ) → Vec d → ℂ
  | [], f => f
  | (v, c) :: rest, f =>
      u4HigherDifference (-v) c (u4HigherBackwardDifferences rest f)

theorem u4HigherDifference_memLp {d : ℕ} {f : Vec d → ℂ}
    (hf : MemLp f 2 (volume : Measure (Vec d))) (v : Vec d) (c : ℂ) :
    MemLp (u4HigherDifference v c f) 2 (volume : Measure (Vec d)) := by
  have ht := hf.comp_measurePreserving
    (measurePreserving_add_right (volume : Measure (Vec d)) v)
  change MemLp (fun x => c * (f (x + v) - f x)) 2 (volume : Measure (Vec d))
  simpa only [Pi.sub_apply, Function.comp_apply] using (ht.sub hf).const_mul c

theorem u4HigherBackwardDifferences_memLp {d : ℕ} (steps : List (Vec d × ℂ))
    {f : Vec d → ℂ} (hf : MemLp f 2 (volume : Measure (Vec d))) :
    MemLp (u4HigherBackwardDifferences steps f) 2 (volume : Measure (Vec d)) := by
  induction steps with
  | nil => exact hf
  | cons step rest ih =>
      rcases step with ⟨v, c⟩
      exact u4HigherDifference_memLp ih (-v) c

/-- Arbitrary-order summation by parts for actual L² representatives. -/
theorem u4HigherDifferences_integration_by_parts {d : ℕ}
    (steps : List (Vec d × ℂ)) {u v : Vec d → ℂ}
    (hu : MemLp u 2 (volume : Measure (Vec d)))
    (hv : MemLp v 2 (volume : Measure (Vec d))) :
    (∫ x, u4HigherDifferences steps u x * v x) =
      ∫ x, u x * u4HigherBackwardDifferences steps v x := by
  induction steps generalizing u with
  | nil => rfl
  | cons step rest ih =>
      rcases step with ⟨z, c⟩
      have hq := u4HigherDifference_memLp hu z c
      have hb := u4HigherBackwardDifferences_memLp rest hv
      have hi := c18_L2_difference_quotient_integration_by_parts hu hb z 1
      simp only [Complex.ofReal_one, div_one] at hi
      have hs : (∫ x, u4HigherDifference z c u x *
          u4HigherBackwardDifferences rest v x) =
          ∫ x, u x * u4HigherDifference (-z) c
            (u4HigherBackwardDifferences rest v) x := by
        calc
          _ = c * (∫ x, (u (x + z) - u x) *
              u4HigherBackwardDifferences rest v x) := by
                rw [← integral_const_mul]
                apply integral_congr_ae
                filter_upwards with x
                simp only [u4HigherDifference]
                ring
          _ = c * (∫ x, u x * (u4HigherBackwardDifferences rest v (x - z) -
              u4HigherBackwardDifferences rest v x)) := congrArg (fun a : ℂ => c * a) hi
          _ = _ := by
                rw [← integral_const_mul]
                apply integral_congr_ae
                filter_upwards with x
                simp only [u4HigherDifference, sub_eq_add_neg]
                ring
      exact (ih hq).trans hs

/-- Iterated backward quotients of an H1 test retain its supplied gradient,
with representatives matching the arbitrary-order difference pairing. -/
theorem u4Higher_backward_H1_quotients {d : ℕ}
    (steps : List (Vec d × ℝ))
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {V : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hV : IsPhysicalH1Graph volume (Or.inl rfl) v V) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        u4HigherBackwardDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) v ∧
      ∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        u4HigherBackwardDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) (V j) := by
  induction steps with
  | nil => exact ⟨v, V, hV, Filter.EventuallyEq.rfl, fun _ => Filter.EventuallyEq.rfl⟩
  | cons step rest ih =>
      rcases step with ⟨z, h⟩
      obtain ⟨r, R, hrR, hr, hR⟩ := ih
      obtain ⟨q, Q, hqQ, hq, hQ⟩ := c18_physical_H1_difference_quotient hrR z h
      refine ⟨q, Q, hqQ, ?_, ?_⟩
      · have ht := (measurePreserving_add_right (volume : Measure (Vec d)) (-z)).quasiMeasurePreserving.ae hr
        filter_upwards [hq, hr, ht] with x hx hx0 hxz
        simp only [List.map_cons, u4HigherBackwardDifferences, u4HigherDifference,
          Function.comp_apply] at *
        rw [hx, hx0]
        simpa only [sub_eq_add_neg] using congrArg (fun w : ℂ => (h : ℂ)⁻¹ * (w - _)) hxz
      · intro j
        have ht := (measurePreserving_add_right (volume : Measure (Vec d)) (-z)).quasiMeasurePreserving.ae (hR j)
        filter_upwards [hQ j, hR j, ht] with x hx hx0 hxz
        simp only [List.map_cons, u4HigherBackwardDifferences, u4HigherDifference,
          Function.comp_apply] at *
        rw [hx, hx0]
        simpa only [sub_eq_add_neg] using congrArg (fun w : ℂ => (h : ℂ)⁻¹ * (w - _)) hxz

/-- Forward differences preserve almost-everywhere equality at every order. -/
theorem u4HigherDifferences_ae {d : ℕ} (steps : List (Vec d × ℂ))
    {f g : Vec d → ℂ} (hfg : f =ᵐ[volume] g) :
    u4HigherDifferences steps f =ᵐ[volume] u4HigherDifferences steps g := by
  induction steps generalizing f g with
  | nil => exact hfg
  | cons step rest ih =>
      rcases step with ⟨z, c⟩
      apply ih
      have ht := (measurePreserving_add_right (volume : Measure (Vec d)) z).quasiMeasurePreserving.ae hfg
      filter_upwards [hfg, ht] with x hx hxt
      simp only [u4HigherDifference, Function.comp_apply] at *
      rw [hx, hxt]

/-- Forward quotients of an H1 graph retain the supplied gradient at every order. -/
theorem u4Higher_forward_H1_quotients {d : ℕ}
    (steps : List (Vec d × ℝ))
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {V : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hV : IsPhysicalH1Graph volume (Or.inl rfl) v V) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        u4HigherDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) v ∧
      ∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        u4HigherDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) (V j) := by
  induction steps generalizing v V with
  | nil => exact ⟨v, V, hV, Filter.EventuallyEq.rfl, fun _ => Filter.EventuallyEq.rfl⟩
  | cons step rest ih =>
      rcases step with ⟨z, h⟩
      obtain ⟨r, R, hrR, hr, hR⟩ := c18_physical_H1_difference_quotient hV (-z) h
      obtain ⟨q, Q, hqQ, hq, hQ⟩ := ih hrR
      refine ⟨q, Q, hqQ, ?_, ?_⟩
      · have hr' : (r : Vec d → ℂ) =ᵐ[volume]
            u4HigherDifference z (h : ℂ)⁻¹ v := by
          filter_upwards [hr] with x hx
          simpa only [u4HigherDifference, sub_neg_eq_add] using hx
        exact hq.trans (u4HigherDifferences_ae _ hr')
      · intro j
        have hR' : (R j : Vec d → ℂ) =ᵐ[volume]
            u4HigherDifference z (h : ℂ)⁻¹ (V j) := by
          filter_upwards [hR j] with x hx
          simpa only [u4HigherDifference, sub_neg_eq_add] using hx
        exact (hQ j).trans (u4HigherDifferences_ae _ hR')

/-- The actual forward generator equation accepts arbitrary-order backward quotient tests. -/
theorem u4Higher_generator_backward_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (steps : List (Vec d × ℝ)) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        u4HigherBackwardDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) v ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        u4HigherBackwardDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) (H j)) ∧
      (∫ x, g x * q x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * Q j x) +
        ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * q x) := by
  obtain ⟨G₀, hG₀, hweak⟩ := hfg
  have heq := physicalH1Graph_gradient_unique volume (Or.inl rfl) f G₀ G hG₀ hG
  subst G₀
  obtain ⟨q, Q, hqQ, hq, hQ⟩ := u4Higher_backward_H1_quotients steps hH
  exact ⟨q, Q, hqQ, hq, hQ, hweak q Q hqQ⟩

/-- The actual transpose generator equation accepts arbitrary-order backward quotient tests. -/
theorem u4Higher_transpose_generator_backward_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (steps : List (Vec d × ℝ)) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        u4HigherBackwardDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) v ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        u4HigherBackwardDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) (H j)) ∧
      (∫ x, g x * q x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * Q j x) +
        ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) * Q j x)) := by
  obtain ⟨G₀, hG₀, hweak⟩ := hfg
  have heq := physicalH1Graph_gradient_unique volume (Or.inl rfl) f G₀ G hG₀ hG
  subst G₀
  obtain ⟨q, Q, hqQ, hq, hQ⟩ := u4Higher_backward_H1_quotients steps hH
  exact ⟨q, Q, hqQ, hq, hQ, hweak q Q hqQ⟩

/-- Every positive structural derivative controls each coordinate component,
with the original order-dependent bound. -/
theorem u4Higher_coefficient_iterated_derivative_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    {n : ℕ} (hn : 1 ≤ n) (a : Fin n → Fin d) (j k : Fin d) (x : Vec d) :
    |iteratedFDeriv ℝ n (fun y => ω.1 y j k) x
      (fun t => unitVector (a t))| ≤ M n := by
  have hv (t : Fin n) : euclideanNorm (unitVector (a t)) = 1 := by
    change Real.sqrt (dotProduct (Pi.single (a t) (1 : ℝ)) (Pi.single (a t) 1)) = 1
    rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
  obtain ⟨A, B, _, hB, hAB, hA, _⟩ := hsmooth.2 n hn
  have hk : euclideanNorm (unitVector k) = 1 := by
    change Real.sqrt (dotProduct (Pi.single k (1 : ℝ)) (Pi.single k 1)) = 1
    rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
  have hb := hA x (fun t => unitVector (a t)) (unitVector k)
  simp only [hv, Finset.prod_const_one, hk, mul_one] at hb
  have hc := Regeneration.coordinate_abs_le_euclideanNorm
    (Matrix.mulVec (fun j k => iteratedFDeriv ℝ n
      (fun y => ω.1 y j k) x (fun t => unitVector (a t))) (unitVector k)) j
  have he (N : Mat d) : (N.mulVec (unitVector k)) j = N j k := by
    change dotProduct (fun q => N j q) (Pi.single k 1) = _
    rw [dotProduct_single, mul_one]
  erw [he] at hc
  exact (hc.trans hb).trans (by linarith)

/-- Translating a coordinate derivative is controlled by the next structural bound. -/
theorem u4Higher_coefficient_derivative_translation_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (n : ℕ) (a : Fin n → Fin d) (l j k : Fin d) (x : Vec d) (h : ℝ) :
    |iteratedFDeriv ℝ n (fun y => ω.1 y j k) (x + h • unitVector l)
        (fun t => unitVector (a t)) -
      iteratedFDeriv ℝ n (fun y => ω.1 y j k) x
        (fun t => unitVector (a t))| ≤ M (n + 1) * |h| := by
  let v : Fin n → Vec d := fun t => unitVector (a t)
  let D : Vec d → ℝ := fun y => iteratedFDeriv ℝ n (fun z => ω.1 z j k) y v
  let F : ℝ → ℝ := fun t => D (x + t • unitVector l)
  let w : Fin (n + 1) → Vec d :=
    fun t => unitVector ((Fin.cons l a : Fin (n + 1) → Fin d) t)
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n (fun z => ω.1 z j k)) :=
    (hsmooth.1.1 j k).differentiable_iteratedFDeriv (by
      exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top _))
  have htail : Fin.tail w = v := by
    funext t
    exact congrArg (unitVector : Fin d → Vec d)
      (Fin.cons_succ (α := fun _ : Fin (n + 1) => Fin d) l a t)
  have hF (t : ℝ) : HasDerivAt F
      (iteratedFDeriv ℝ (n + 1) (fun y => ω.1 y j k)
        (x + t • unitVector l) w) t := by
    have ht := ((hasDerivAt_id' t).smul_const (unitVector l)).const_add x
    have hD := ((hd (x + t • unitVector l)).continuousMultilinear_apply_const v).hasFDerivAt
    have hchain := hD.comp_hasDerivAt t ht
    have he : iteratedFDeriv ℝ (n + 1) (fun y => ω.1 y j k)
        (x + t • unitVector l) w = fderiv ℝ D (x + t • unitVector l) (unitVector l) := by
      simpa only [htail, w, Fin.cons_zero, D] using
        (DifferentiableAt.iteratedFDeriv_succ_apply_left' (m := w) (hd (x + t • unitVector l)))
    rw [he]
    simpa only [F, D, Function.comp_def, one_smul] using hchain
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := h)
    (fun t _ => (hF t).hasDerivWithinAt)
    (fun t _ => by
      simpa only [Real.norm_eq_abs, w] using
        u4Higher_coefficient_iterated_derivative_bound hsmooth (n := n + 1)
          (by omega) (Fin.cons l a) j k (x + t • unitVector l))
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ _) (Set.mem_univ _)
  simpa [F, D, v, Real.norm_eq_abs] using hb

/-- Mixed translations of every coordinate derivative inherit the next two
structural bounds, with both signed steps retained. -/
theorem u4Higher_coefficient_derivative_mixed_difference_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (n : ℕ) (a : Fin n → Fin d) (l m j k : Fin d) (x : Vec d) (h s : ℝ) :
    let D : Vec d → ℝ := fun y => iteratedFDeriv ℝ n (fun z => ω.1 z j k) y
      (fun t => unitVector (a t))
    |(D ((x + s • unitVector m) + h • unitVector l) - D (x + s • unitVector m)) -
      (D (x + h • unitVector l) - D x)| ≤ M (n + 2) * |h| * |s| := by
  let v : Fin n → Vec d := fun t => unitVector (a t)
  let D : Vec d → ℝ := fun y => iteratedFDeriv ℝ n (fun z => ω.1 z j k) y v
  let w : Fin (n + 1) → Vec d :=
    fun t => unitVector ((Fin.cons m a : Fin (n + 1) → Fin d) t)
  let J : Vec d → ℝ := fun y => iteratedFDeriv ℝ (n + 1) (fun z => ω.1 z j k) y w
  let F : ℝ → ℝ := (fun t => D ((x + t • unitVector m) + h • unitVector l)) -
    (fun t => D (x + t • unitVector m))
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n (fun z => ω.1 z j k)) :=
    (hsmooth.1.1 j k).differentiable_iteratedFDeriv (by
      exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top _))
  have htail : Fin.tail w = v := by
    funext t
    exact congrArg (unitVector : Fin d → Vec d)
      (Fin.cons_succ (α := fun _ : Fin (n + 1) => Fin d) m a t)
  have hD (y : Vec d) : fderiv ℝ D y (unitVector m) = J y := by
    symm
    simpa only [J, htail, w, Fin.cons_zero, D] using
      (DifferentiableAt.iteratedFDeriv_succ_apply_left' (m := w) (hd y))
  have hF (t : ℝ) : HasDerivAt F
      (J ((x + t • unitVector m) + h • unitVector l) - J (x + t • unitVector m)) t := by
    have ht := ((hasDerivAt_id' t).smul_const (unitVector m)).const_add x
    have hleft := ((hd ((x + t • unitVector m) + h • unitVector l)).continuousMultilinear_apply_const v).hasFDerivAt.comp_hasDerivAt t
      (ht.add_const (h • unitVector l))
    have hright := ((hd (x + t • unitVector m)).continuousMultilinear_apply_const v).hasFDerivAt.comp_hasDerivAt t ht
    simpa only [F, D, Function.comp_def, one_smul, hD] using hleft.sub hright
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := s)
    (fun t _ => (hF t).hasDerivWithinAt)
    (fun t _ => by
      simpa only [Real.norm_eq_abs, J, w, Nat.add_assoc] using
        u4Higher_coefficient_derivative_translation_bound hsmooth (n + 1)
          (Fin.cons m a) l j k (x + t • unitVector m) h)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ _) (Set.mem_univ _)
  simpa [F, D, v, Real.norm_eq_abs] using hb

/-- All terms in which at least one difference falls on the coefficient. -/
def u4HigherCoefficientCommutator {d : ℕ} :
    List (Vec d × ℂ) → (Vec d → ℂ) → (Vec d → ℂ) → Vec d → ℂ
  | [], _, _ => fun _ => 0
  | (z, c) :: rest, a, u => fun x =>
      u4HigherProductExpansion rest (u4HigherDifference z c a) (fun y => u (y + z)) x +
      u4HigherCoefficientCommutator rest a (u4HigherDifference z c u) x

/-- Separate the undifferenced principal coefficient from every commutator. -/
theorem u4HigherProductExpansion_principal {d : ℕ} (steps : List (Vec d × ℂ))
    (a u : Vec d → ℂ) (x : Vec d) :
    u4HigherProductExpansion steps a u x =
      a x * u4HigherDifferences steps u x +
        u4HigherCoefficientCommutator steps a u x := by
  induction steps generalizing u with
  | nil => simp [u4HigherProductExpansion, u4HigherDifferences,
      u4HigherCoefficientCommutator]
  | cons step rest ih =>
      rcases step with ⟨z, c⟩
      simp only [u4HigherProductExpansion, u4HigherDifferences,
        u4HigherCoefficientCommutator]
      rw [ih]
      ring

/-- The differentiated principal pairing for an arbitrary list of signed
spatial differences, including every coefficient commutator. -/
theorem u4Higher_backward_principal_pairing {d : ℕ}
    (steps : List (Vec d × ℂ)) (a : Vec d → ℂ)
    (ha : MemLp a ∞ (volume : Measure (Vec d)))
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, a x * u x * u4HigherBackwardDifferences steps v x) =
      ∫ x, (a x * u4HigherDifferences steps u x +
        u4HigherCoefficientCommutator steps a u x) * v x := by
  have hp : MemLp (fun x => a x * u x) 2 (volume : Measure (Vec d)) := by
    change MemLp (a * (u : Vec d → ℂ)) 2 (volume : Measure (Vec d))
    exact ha.mul (r := 2) (Lp.memLp u)
  calc
    _ = ∫ x, u4HigherDifferences steps (fun y => a y * u y) x * v x :=
      (u4HigherDifferences_integration_by_parts steps hp (Lp.memLp v)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [u4HigherDifferences_product, u4HigherProductExpansion_principal]

/-- The actual generator's backward test has all differentiated principal
pairings exposed, for either orientation of the coefficient matrix. -/
theorem u4Higher_generator_principal_pairings {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (steps : List (Vec d × ℝ)) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (∫ x, g x * q x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (ω.1 x j k : ℂ) * G k x * Q j x) +
        ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) * G j x) * q x) ∧
      ∀ j k, (∫ x, (ω.1 x j k : ℂ) * G k x * Q j x) =
        ∫ x, ((ω.1 x j k : ℂ) * u4HigherDifferences
          (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) (G k) x +
          u4HigherCoefficientCommutator
            (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹)))
            (fun y => (ω.1 y j k : ℂ)) (G k) x) * H j x := by
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  obtain ⟨q, Q, hqQ, hq, hQ, hw⟩ :=
    u4Higher_generator_backward_test hfg hG hH steps
  refine ⟨q, Q, hqQ, hw, ?_⟩
  intro j k
  calc
    _ = ∫ x, (ω.1 x j k : ℂ) * G k x *
        u4HigherBackwardDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) (H j) x := by
      apply integral_congr_ae
      filter_upwards [hQ j] with x hx
      rw [hx]
    _ = _ := u4Higher_backward_principal_pairing _ _ (ha j k) (G k) (H j)

/-- The transpose generator has the same all-order principal commutator
identity with the coefficient indices interchanged. -/
theorem u4Higher_transpose_generator_principal_pairings {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {v : Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (steps : List (Vec d × ℝ)) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (∫ x, g x * q x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (ω.1 x k j : ℂ) * G k x * Q j x) +
        ζ * (∫ x, f x * (∑ j, (ω.1 x j i : ℂ) * Q j x)) ∧
      ∀ j k, (∫ x, (ω.1 x k j : ℂ) * G k x * Q j x) =
        ∫ x, ((ω.1 x k j : ℂ) * u4HigherDifferences
          (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) (G k) x +
          u4HigherCoefficientCommutator
            (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹)))
            (fun y => (ω.1 y k j : ℂ)) (G k) x) * H j x := by
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  obtain ⟨q, Q, hqQ, hq, hQ, hw⟩ :=
    u4Higher_transpose_generator_backward_test hfg hG hH steps
  refine ⟨q, Q, hqQ, hw, ?_⟩
  intro j k
  calc
    _ = ∫ x, (ω.1 x k j : ℂ) * G k x *
        u4HigherBackwardDifferences (steps.map (fun s => (s.1, (s.2 : ℂ)⁻¹))) (H j) x := by
      apply integral_congr_ae
      filter_upwards [hQ j] with x hx
      rw [hx]
    _ = _ := u4Higher_backward_principal_pairing _ _ (ha k j) (G k) (H j)

/-- Every member of either positive-time generator chain, except the last,
has the same quantitative second-order spatial estimate. -/
theorem u4Higher_positive_time_generator_chain_H2 {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Lp ℂ 2 (volume : Measure (Vec d)))
      (t : ℝ≥0), 0 < t →
      ∃ u v : Fin (n + 1) → Lp ℂ 2 (volume : Measure (Vec d)),
        u 0 = P t f ∧ v 0 = Pdag t f ∧
        ∀ k : Fin n,
          (IsPhysicalComplexGeneratorPair ω.1 i ζ (u k.castSucc) (u k.succ) ∧
           IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (v k.castSucc) (v k.succ)) ∧
          ∀ w g, ((w = u k.castSucc ∧ g = u k.succ) ∨
                  (w = v k.castSucc ∧ g = v k.succ)) →
            ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
            ∃ H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
              IsPhysicalH1Graph volume (Or.inl rfl) w G ∧
              (∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j)) ∧
              (∑ j, ‖G j‖ ^ 2) + (∑ j, ∑ l, ‖H j l‖ ^ 2) ≤
                C * (‖w‖ ^ 2 + ‖g‖ ^ 2) := by
  obtain ⟨C, hC, hH2⟩ := u4_physical_generator_pair_H2 hΛ hell hsmooth (i := i) (ζ := ζ)
  refine ⟨C, hC, ?_⟩
  intro n f t ht
  obtain ⟨u, v, hu, hv, hchain⟩ :=
    c18_physical_positive_time_generator_chains hΛ hell hsmooth hP hPdag n f t ht
  refine ⟨u, v, hu, hv, ?_⟩
  intro k
  refine ⟨hchain k, ?_⟩
  intro w g hw
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hH2 _ _ (Or.inl (hchain k).1)
  · exact hH2 _ _ (Or.inr (hchain k).2)

/-- Forward iterated differences preserve the actual L² class. -/
theorem u4HigherDifferences_memLp {d : ℕ} (steps : List (Vec d × ℂ))
    {f : Vec d → ℂ} (hf : MemLp f 2 (volume : Measure (Vec d))) :
    MemLp (u4HigherDifferences steps f) 2 (volume : Measure (Vec d)) := by
  induction steps generalizing f with
  | nil => exact hf
  | cons step rest ih =>
      rcases step with ⟨v, c⟩
      exact ih (u4HigherDifference_memLp hf v c)

/-- The full coefficient commutator is an L² function, without discarding
any of the translated terms in the discrete Leibniz expansion. -/
theorem u4HigherCoefficientCommutator_memLp {d : ℕ}
    (steps : List (Vec d × ℂ)) {a u : Vec d → ℂ}
    (ha : MemLp a ∞ (volume : Measure (Vec d)))
    (hu : MemLp u 2 (volume : Measure (Vec d))) :
    MemLp (u4HigherCoefficientCommutator steps a u) 2
      (volume : Measure (Vec d)) := by
  have hp : MemLp (fun x => a x * u x) 2 (volume : Measure (Vec d)) := by
    change MemLp (a * u) 2 (volume : Measure (Vec d))
    exact ha.mul (r := 2) hu
  have hprincipal : MemLp (fun x => a x * u4HigherDifferences steps u x) 2
      (volume : Measure (Vec d)) := by
    change MemLp (a * u4HigherDifferences steps u) 2 (volume : Measure (Vec d))
    exact ha.mul (r := 2) (u4HigherDifferences_memLp steps hu)
  have hdiff := (u4HigherDifferences_memLp steps hp).sub hprincipal
  have heq : (fun x => u4HigherDifferences steps (fun x => a x * u x) x -
      a x * u4HigherDifferences steps u x) = u4HigherCoefficientCommutator steps a u := by
    funext x
    rw [u4HigherDifferences_product, u4HigherProductExpansion_principal]
    simp
  exact heq ▸ hdiff

/-- A signed coordinate quotient of any coefficient derivative is uniformly
controlled by the next structural derivative bound. -/
theorem u4Higher_coefficient_derivative_quotient_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (n : ℕ) (a : Fin n → Fin d) (l j k : Fin d) (x : Vec d)
    {h : ℝ} (hh : h ≠ 0) :
    |(iteratedFDeriv ℝ n (fun y => ω.1 y j k) (x + h • unitVector l)
        (fun t => unitVector (a t)) -
      iteratedFDeriv ℝ n (fun y => ω.1 y j k) x
        (fun t => unitVector (a t))) / h| ≤ M (n + 1) := by
  rw [abs_div]
  calc
    _ ≤ (M (n + 1) * |h|) / |h| :=
      div_le_div_of_nonneg_right
        (u4Higher_coefficient_derivative_translation_bound hsmooth n a l j k x h)
        (abs_nonneg h)
    _ = M (n + 1) := by field_simp

/-- A mixed signed quotient of any coefficient derivative is uniformly
controlled by the structural bound two orders higher. -/
theorem u4Higher_coefficient_derivative_mixed_quotient_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (n : ℕ) (a : Fin n → Fin d) (l m j k : Fin d) (x : Vec d)
    {h s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0) :
    let D : Vec d → ℝ := fun y => iteratedFDeriv ℝ n (fun z => ω.1 z j k) y
      (fun t => unitVector (a t))
    |((D ((x + s • unitVector m) + h • unitVector l) - D (x + s • unitVector m)) -
      (D (x + h • unitVector l) - D x)) / h / s| ≤ M (n + 2) := by
  dsimp only
  rw [abs_div, abs_div]
  calc
    _ ≤ ((M (n + 2) * |h|) * |s|) / |h| / |s| :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right
          (u4Higher_coefficient_derivative_mixed_difference_bound hsmooth n a l m j k x h s)
          (abs_nonneg h)) (abs_nonneg s)
    _ = M (n + 2) := by field_simp

/-- A coefficient-derivative difference quotient acts on complex physical L²
with a bound uniform in the signed nonzero step. -/
theorem u4Higher_coefficient_derivative_quotient_multiplier {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (n : ℕ) (a : Fin n → Fin d) (l j k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (((iteratedFDeriv ℝ n (fun y => ω.1 y j k) (x + h • unitVector l)
            (fun t => unitVector (a t)) -
          iteratedFDeriv ℝ n (fun y => ω.1 y j k) x
            (fun t => unitVector (a t))) / h : ℝ) : ℂ) * u x) ∧
      ‖v‖ ≤ M (n + 1) * ‖u‖ := by
  let D : Vec d → ℝ := fun x => iteratedFDeriv ℝ n (fun y => ω.1 y j k) x
    (fun t => unitVector (a t))
  let w : Vec d → ℝ := fun x => (D (x + h • unitVector l) - D x) / h
  have hD : Continuous D := by
    have hd : Differentiable ℝ (iteratedFDeriv ℝ n (fun y => ω.1 y j k)) :=
      (hsmooth.1.1 j k).differentiable_iteratedFDeriv (by
        exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top _))
    exact (hd.continuousMultilinear_apply_const _).continuous
  have hw : Measurable w :=
    (((hD.comp (continuous_id.add continuous_const)).sub hD).div_const h).measurable
  have hM : 0 ≤ M (n + 1) := by
    obtain ⟨A, B, hA, hB, hAB, _⟩ := hsmooth.2 (n + 1) (by omega)
    linarith
  have hb : ∀ x, |w x| ≤ M (n + 1) := fun x =>
    u4Higher_coefficient_derivative_quotient_bound hsmooth n a l j k x hh
  let v := (s5_memLp_mul hw hb u).toLp (fun x => (w x : ℂ) * u x)
  refine ⟨v, (s5_memLp_mul hw hb u).coeFn_toLp, ?_⟩
  rw [Lp.norm_toLp, Lp.norm_def]
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Vec d)))
      (f := fun x => (w x : ℂ) * u x) (g := (u : Vec d → ℂ)) (c := M (n + 1))
      ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)) 2
  calc (eLpNorm (fun x => (w x : ℂ) * u x) 2 volume).toReal
      ≤ (ENNReal.ofReal (M (n + 1)) * eLpNorm (u : Vec d → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u)) he
    _ = M (n + 1) * (eLpNorm (u : Vec d → ℂ) 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]
    _ = M (n + 1) * ‖u‖ := by rw [Lp.norm_def]

/-- The signed coordinate quotient of a coefficient entry is an L² multiplier
with the first structural derivative bound. -/
theorem u4Higher_coefficient_quotient_multiplier {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l j k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) * u x) ∧
      ‖v‖ ≤ M 1 * ‖u‖ := by
  simpa only [iteratedFDeriv_zero_apply, Nat.zero_add] using
    (u4Higher_coefficient_derivative_quotient_multiplier hsmooth 0 Fin.elim0 l j k hh u)

end EinsteinFull

#print axioms EinsteinFull.u4Higher_coefficient_derivative_quotient_multiplier
#print axioms EinsteinFull.u4Higher_coefficient_derivative_quotient_bound
#print axioms EinsteinFull.u4Higher_coefficient_derivative_mixed_quotient_bound
#print axioms EinsteinFull.u4Higher_positive_time_generator_chain_H2
#print axioms EinsteinFull.u4HigherDifferences_memLp
#print axioms EinsteinFull.u4HigherCoefficientCommutator_memLp
