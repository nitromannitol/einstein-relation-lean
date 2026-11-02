import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedBounds
import EinsteinFull.Calculus.U4PhysicalHigherRegularity
import EinsteinFull.Calculus.C24PhysicalWeakH2
import EinsteinFull.Calculus.SunaS3PhysicalPointKernel
import Mathlib.Data.Set.Finite.List

open EinsteinRelation MeasureTheory
open scoped ENNReal NNReal Topology

namespace EinsteinFull

noncomputable section

/-- Iterated real signed coordinate differences, including zero steps. -/
def u4RealCoordinateDifferences {d : ℕ} :
    List (Fin d × ℝ) → (Vec d → ℝ) → Vec d → ℝ
  | [], f => f
  | (i, h) :: rest, f =>
      u4RealCoordinateDifferences rest (fun x => (f (x + h • unitVector i) - f x) / h)

/-- Appending a difference applies it to the previous iterated difference. -/
theorem u4RealCoordinateDifferences_append {d : ℕ}
    (as bs : List (Fin d × ℝ)) (f : Vec d → ℝ) :
    u4RealCoordinateDifferences (as ++ bs) f =
      u4RealCoordinateDifferences bs (u4RealCoordinateDifferences as f) := by
  induction as generalizing f with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨i, h⟩
      simp only [List.cons_append, u4RealCoordinateDifferences]
      exact ih _

/-- Iterated coordinate differences commute with translations. -/
theorem u4RealCoordinateDifferences_translate {d : ℕ}
    (steps : List (Fin d × ℝ)) (f : Vec d → ℝ) (z x : Vec d) :
    u4RealCoordinateDifferences steps (fun y => f (y + z)) x =
      u4RealCoordinateDifferences steps f (x + z) := by
  induction steps generalizing f with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨i, h⟩
      simp only [u4RealCoordinateDifferences]
      have he : (fun y => (f (y + h • unitVector i + z) - f (y + z)) / h) =
          (fun y => (f ((y + z) + h • unitVector i) - f (y + z)) / h) := by
        funext y
        rw [add_right_comm]
      rw [he]
      exact ih (fun y => (f (y + h • unitVector i) - f y) / h)

/-- Finite differences commute with differentiation in a separate parameter. -/
theorem u4RealCoordinateDifferences_hasDerivAt {d : ℕ}
    (steps : List (Fin d × ℝ)) (F : ℝ → Vec d → ℝ) (G : Vec d → ℝ)
    (t : ℝ) (h : ∀ x, HasDerivAt (fun s => F s x) (G x) t) (x : Vec d) :
    HasDerivAt (fun s => u4RealCoordinateDifferences steps (F s) x)
      (u4RealCoordinateDifferences steps G x) t := by
  induction steps generalizing F G with
  | nil => exact h x
  | cons p rest ih =>
      rcases p with ⟨i, r⟩
      apply ih
      intro y
      exact ((h (y + r • unitVector i)).sub (h y)).div_const r

/-- The real coordinate trace of a structural derivative. -/
def u4CoefficientDerivative {d : ℕ} (ω : FieldPair d) (n : ℕ)
    (a : Fin n → Fin d) (j k : Fin d) (x : Vec d) : ℝ :=
  iteratedFDeriv ℝ n (fun y => ω.1 y j k) x (fun t => unitVector (a t))

/-- Differentiation along a coordinate adds that coordinate to the derivative. -/
theorem u4CoefficientDerivative_hasDerivAt {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (n : ℕ) (a : Fin n → Fin d) (i j k : Fin d) (x : Vec d) (t : ℝ) :
    HasDerivAt (fun s => u4CoefficientDerivative ω n a j k (x + s • unitVector i))
      (u4CoefficientDerivative ω (n + 1) (Fin.cons i a) j k
        (x + t • unitVector i)) t := by
  let v : Fin n → Vec d := fun q => unitVector (a q)
  let w : Fin (n + 1) → Vec d := fun q => unitVector ((Fin.cons i a : Fin (n + 1) → Fin d) q)
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n (fun y => ω.1 y j k)) :=
    (hsmooth.1.1 j k).differentiable_iteratedFDeriv (by
      exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top _))
  have htail : Fin.tail w = v := by
    funext q
    exact congrArg (unitVector : Fin d → Vec d)
      (Fin.cons_succ (α := fun _ : Fin (n + 1) => Fin d) i a q)
  have ht := ((hasDerivAt_id' t).smul_const (unitVector i)).const_add x
  have hD := ((hd (x + t • unitVector i)).continuousMultilinear_apply_const v).hasFDerivAt
  have hchain := hD.comp_hasDerivAt t ht
  have he : iteratedFDeriv ℝ (n + 1) (fun y => ω.1 y j k)
      (x + t • unitVector i) w =
      fderiv ℝ (fun y => iteratedFDeriv ℝ n (fun z => ω.1 z j k) y v)
        (x + t • unitVector i) (unitVector i) := by
    simpa only [htail, w, Fin.cons_zero] using
      (DifferentiableAt.iteratedFDeriv_succ_apply_left' (m := w) (hd (x + t • unitVector i)))
  change HasDerivAt (fun s => iteratedFDeriv ℝ n (fun y => ω.1 y j k)
      (x + s • unitVector i) v)
    (iteratedFDeriv ℝ (n + 1) (fun y => ω.1 y j k)
      (x + t • unitVector i) w) t
  rw [he]
  simpa only [Function.comp_def, one_smul] using hchain

/-- Every iterated signed coordinate quotient of a coefficient derivative is
bounded by the structural derivative bound at the corresponding total order. -/
theorem u4CoefficientDerivative_iterated_quotient_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (n : ℕ) (a : Fin n → Fin d) (j k : Fin d)
    (horder : 1 ≤ n + steps.length) (x : Vec d) :
    |u4RealCoordinateDifferences steps (u4CoefficientDerivative ω n a j k) x| ≤
      M (n + steps.length) := by
  induction steps using List.reverseRecOn generalizing n j k x with
  | nil =>
      simpa [u4RealCoordinateDifferences, u4CoefficientDerivative] using
        u4Higher_coefficient_iterated_derivative_bound hsmooth (n := n) (by simpa using horder) a j k x
  | append_singleton steps p ih =>
      rcases p with ⟨i, h⟩
      have hh : h ≠ 0 := hnz (i, h) (by simp)
      have hnz' : ∀ p ∈ steps, p.2 ≠ 0 := by
        intro p hp
        exact hnz p (by simp [hp])
      rw [u4RealCoordinateDifferences_append]
      change |(u4RealCoordinateDifferences steps (u4CoefficientDerivative ω n a j k)
          (x + h • unitVector i) -
        u4RealCoordinateDifferences steps (u4CoefficientDerivative ω n a j k) x) / h| ≤ _
      let F : ℝ → ℝ := fun t => u4RealCoordinateDifferences steps
        (fun y => u4CoefficientDerivative ω n a j k (y + t • unitVector i)) x
      have hF (t : ℝ) : HasDerivAt F
          (u4RealCoordinateDifferences steps
            (fun y => u4CoefficientDerivative ω (n + 1) (Fin.cons i a) j k
              (y + t • unitVector i)) x) t := by
        exact u4RealCoordinateDifferences_hasDerivAt steps _ _ t
          (fun y => u4CoefficientDerivative_hasDerivAt hsmooth n a i j k y t) x
      have hb (t : ℝ) :
          |u4RealCoordinateDifferences steps
            (fun y => u4CoefficientDerivative ω (n + 1) (Fin.cons i a) j k
              (y + t • unitVector i)) x| ≤ M (n + steps.length + 1) := by
        rw [u4RealCoordinateDifferences_translate]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih hnz' (n + 1) (Fin.cons i a) j k (by omega) (x + t • unitVector i)
      have hdiff := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := Set.univ) (x := (0 : ℝ)) (y := h)
        (fun t _ => (hF t).hasDerivWithinAt)
        (fun t _ => by simpa only [Real.norm_eq_abs] using hb t)
        (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ _) (Set.mem_univ _)
      have hdifference :
          |u4RealCoordinateDifferences steps (u4CoefficientDerivative ω n a j k)
              (x + h • unitVector i) -
            u4RealCoordinateDifferences steps (u4CoefficientDerivative ω n a j k) x| ≤
            M (n + steps.length + 1) * |h| := by
        simpa only [F, u4RealCoordinateDifferences_translate, zero_smul, add_zero,
          Real.norm_eq_abs, sub_zero] using hdiff
      rw [abs_div]
      calc
        _ ≤ (M (n + steps.length + 1) * |h|) / |h| :=
          div_le_div_of_nonneg_right hdifference (abs_nonneg h)
        _ = M (n + (steps ++ [(i, h)]).length) := by
          simp only [List.length_append, List.length_singleton]
          field_simp
          rw [Nat.add_assoc]

/-- Iterated signed differences preserve continuity. -/
theorem u4RealCoordinateDifferences_continuous {d : ℕ}
    (steps : List (Fin d × ℝ)) {f : Vec d → ℝ} (hf : Continuous f) :
    Continuous (u4RealCoordinateDifferences steps f) := by
  induction steps generalizing f with
  | nil => exact hf
  | cons p rest ih =>
      rcases p with ⟨i, h⟩
      apply ih
      exact ((hf.comp (continuous_id.add continuous_const)).sub hf).div_const h

/-- Arbitrarily many signed coefficient quotients act boundedly on physical L². -/
theorem u4CoefficientDerivative_iterated_quotient_multiplier {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (n : ℕ) (a : Fin n → Fin d) (j k : Fin d)
    (horder : 1 ≤ n + steps.length)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        ((u4RealCoordinateDifferences steps (u4CoefficientDerivative ω n a j k) x : ℝ) : ℂ) * u x) ∧
      ‖v‖ ≤ M (n + steps.length) * ‖u‖ := by
  let w := u4RealCoordinateDifferences steps (u4CoefficientDerivative ω n a j k)
  have hD : Continuous (u4CoefficientDerivative ω n a j k) := by
    have hd : Differentiable ℝ (iteratedFDeriv ℝ n (fun y => ω.1 y j k)) :=
      (hsmooth.1.1 j k).differentiable_iteratedFDeriv (by
        exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top _))
    exact (hd.continuousMultilinear_apply_const _).continuous
  have hw : Measurable w := (u4RealCoordinateDifferences_continuous steps hD).measurable
  have hM : 0 ≤ M (n + steps.length) := by
    obtain ⟨A, B, hA, hB, hAB, _⟩ := hsmooth.2 (n + steps.length) horder
    linarith
  have hb : ∀ x, |w x| ≤ M (n + steps.length) := fun x =>
    u4CoefficientDerivative_iterated_quotient_bound hsmooth steps hnz n a j k horder x
  let v := (s5_memLp_mul hw hb u).toLp (fun x => (w x : ℂ) * u x)
  refine ⟨v, (s5_memLp_mul hw hb u).coeFn_toLp, ?_⟩
  rw [Lp.norm_toLp, Lp.norm_def]
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Vec d)))
      (f := fun x => (w x : ℂ) * u x) (g := (u : Vec d → ℂ)) (c := M (n + steps.length))
      ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)) 2
  calc (eLpNorm (fun x => (w x : ℂ) * u x) 2 volume).toReal
      ≤ (ENNReal.ofReal (M (n + steps.length)) * eLpNorm (u : Vec d → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u)) he
    _ = M (n + steps.length) * (eLpNorm (u : Vec d → ℂ) 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]
    _ = M (n + steps.length) * ‖u‖ := by rw [Lp.norm_def]

/-- Real coefficient quotients agree with the complex differences used in the
actual generator commutator. -/
theorem u4RealCoordinateDifferences_ofReal {d : ℕ}
    (steps : List (Fin d × ℝ)) (f : Vec d → ℝ) (x : Vec d) :
    u4HigherDifferences (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
      (fun y => (f y : ℂ)) x = (u4RealCoordinateDifferences steps f x : ℂ) := by
  induction steps generalizing f with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨i, h⟩
      simp only [List.map_cons, u4HigherDifferences, u4RealCoordinateDifferences]
      have he : u4HigherDifference (h • unitVector i) (h : ℂ)⁻¹ (fun y => (f y : ℂ)) =
          (fun y => (((f (y + h • unitVector i) - f y) / h : ℝ) : ℂ)) := by
        funext y
        simp [u4HigherDifference, div_eq_mul_inv, mul_comm]
      rw [he, ih]

/-- Directional difference bounds retain a homogeneous bound on the full third
weak derivative, rather than only producing its existence. -/
theorem u4H3_quantitative_of_directional_bounds {d : ℕ}
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (C : Fin d → Fin d → ℝ) (hC : ∀ j l, 0 ≤ C j l)
    (hquotient : ∀ (j l : Fin d) (h : ℝ), 0 < |h| → |h| ≤ 1 →
      (∑ k, ((eLpNorm
        (fun x => (H j k (x + h • unitVector l) - H j k x) / (h : ℂ))
        2 (volume : Measure (Vec d))).toReal) ^ 2) ≤ C j l) :
    ∃ K : Fin d → Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j k, IsPhysicalH1Graph volume (Or.inl rfl) (H j k) (K j k)) ∧
      (∑ j, ∑ k, ∑ l, ‖K j k l‖ ^ 2) ≤
        (d : ℝ) * (1 + 2 * (d : ℝ)) *
          ((∑ j, ∑ k, ‖H j k‖ ^ 2) + ∑ j, ∑ l, C j l) := by
  classical
  let E : ℝ := (∑ j, ∑ k, ‖H j k‖ ^ 2) + ∑ j, ∑ l, C j l
  have hHnonneg : 0 ≤ ∑ j, ∑ k, ‖H j k‖ ^ 2 :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hCnonneg : 0 ≤ ∑ j, ∑ l, C j l :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => hC j l))
  have hE : 0 ≤ E := add_nonneg hHnonneg hCnonneg
  have hfirst (j : Fin d) : (∑ k, ‖H j k‖ ^ 2) ≤ E := by
    have hb : (∑ k, ‖H j k‖ ^ 2) ≤ ∑ j, ∑ k, ‖H j k‖ ^ 2 :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg (s := Finset.univ)
        (fun k _ => sq_nonneg ‖H a k‖)) (Finset.mem_univ j)
    dsimp [E]
    linarith
  have hc_bound (j l : Fin d) : C j l ≤ E := by
    have h1 : C j l ≤ ∑ l, C j l :=
      Finset.single_le_sum (fun l _ => hC j l) (Finset.mem_univ l)
    have h2 : (∑ l, C j l) ≤ ∑ j, ∑ l, C j l :=
      Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun l _ => hC j l))
        (Finset.mem_univ j)
    dsimp [E]
    linarith
  obtain ⟨K, hK, hb⟩ := u4h3_physical_H3_of_hessian_quotient_bounds G H hH
    1 E (by norm_num) hE hfirst (by
      intro j l h hh hh1
      simpa only [one_mul] using (hquotient j l h hh hh1).trans (hc_bound j l))
  refine ⟨K, hK, ?_⟩
  convert hb using 1 <;> dsimp [E] <;> ring

/-- The forward generator's explicit uniform Hessian-quotient energy. -/
def u4H3ForwardDirectionalEnergy {d : ℕ}
    (Λ : ℝ) (M : ℕ → ℝ) (ζ : ℂ)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (m l : Fin d) : ℝ :=
  (Λ * (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * (∑ j, ‖Hess j l‖) +
    M 1 * (∑ j, ‖G j‖)) + M 1 * (∑ j, ‖Hess j m‖) +
    M 1 * (∑ j, ‖Hess j l‖) + M 2 * (∑ j, ‖G j‖))) ^ 2 * (d : ℝ) +
    ‖Hess m l‖ ^ 2

/-- The transpose generator's explicit uniform Hessian-quotient energy. -/
def u4H3TransposeDirectionalEnergy {d : ℕ}
    (Λ : ℝ) (M : ℕ → ℝ) (ζ : ℂ)
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (m l : Fin d) : ℝ :=
  (Λ * (2 * ‖H l‖ + 2 * ‖ζ‖ * (Λ * ‖Hess m l‖ +
    M 1 * ‖G m‖ + M 1 * ‖G l‖ + M 2 * ‖f‖) +
    M 1 * (∑ j, ‖Hess j m‖) + M 1 * (∑ j, ‖Hess j l‖) +
    M 2 * (∑ j, ‖G j‖))) ^ 2 * (d : ℝ) + ‖Hess m l‖ ^ 2

/-- Both actual physical generators have quantitative third weak derivatives. -/
theorem u4H3_generator_pair_quantitative {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
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
      (∀ j k, IsPhysicalH1Graph volume (Or.inl rfl) (Hess j k) (K j k)) ∧
      (∑ j, ∑ k, ∑ l, ‖K j k l‖ ^ 2) ≤
        (d : ℝ) * (1 + 2 * (d : ℝ)) *
          ((∑ j, ∑ k, ‖Hess j k‖ ^ 2) + ∑ m, ∑ l,
            (u4H3ForwardDirectionalEnergy Λ M ζ G H Hess m l +
              u4H3TransposeDirectionalEnergy Λ M ζ f G H Hess m l)) := by
  apply u4H3_quantitative_of_directional_bounds G Hess hHess
    (fun m l => u4H3ForwardDirectionalEnergy Λ M ζ G H Hess m l +
      u4H3TransposeDirectionalEnergy Λ M ζ f G H Hess m l)
  · intro m l
    unfold u4H3ForwardDirectionalEnergy u4H3TransposeDirectionalEnergy
    positivity
  · intro m l h hh _
    have hforward : 0 ≤ u4H3ForwardDirectionalEnergy Λ M ζ G H Hess m l := by
      unfold u4H3ForwardDirectionalEnergy
      positivity
    have htranspose : 0 ≤ u4H3TransposeDirectionalEnergy Λ M ζ f G H Hess m l := by
      unfold u4H3TransposeDirectionalEnergy
      positivity
    rcases hfg with hf | ht
    · exact (u4h3_forward_hessian_quotient_bound Hess hΛ hell hsmooth hf hG hHess hJ l m h
        (abs_pos.mp hh)).trans (by dsimp [u4H3ForwardDirectionalEnergy]; linarith)
    · exact (u4h3_transpose_hessian_quotient_bound Hess hΛ hell hsmooth ht hG hHess hJ l m h
        (abs_pos.mp hh)).trans (by dsimp [u4H3TransposeDirectionalEnergy]; linarith)


/-- The explicit third-derivative energies are uniform for forces in the
prescribed complex ball. -/
theorem u4H3_directional_energy_force_uniform {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hsmooth : IsSmoothWithBounds M ω)
    (ζ : ℂ) (hζ : ‖ζ‖ ≤ 4)
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (m l : Fin d) :
    u4H3ForwardDirectionalEnergy Λ M ζ G H Hess m l +
      u4H3TransposeDirectionalEnergy Λ M ζ f G H Hess m l ≤
    u4H3ForwardDirectionalEnergy Λ M 4 G H Hess m l +
      u4H3TransposeDirectionalEnergy Λ M 4 f G H Hess m l := by
  have hM1 : 0 ≤ M 1 := by
    obtain ⟨A, B, hA, hB, hAB, _⟩ := hsmooth.2 1 (by norm_num)
    linarith
  have hM2 : 0 ≤ M 2 := by
    obtain ⟨A, B, hA, hB, hAB, _⟩ := hsmooth.2 2 (by norm_num)
    linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hζ4 : ‖ζ‖ ≤ ‖(4 : ℂ)‖ := by simpa using hζ
  unfold u4H3ForwardDirectionalEnergy u4H3TransposeDirectionalEnergy
  gcongr

/-- The third weak derivative estimate is uniform over the required force ball,
for either actual physical generator. -/
theorem u4H3_generator_pair_force_uniform {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (Hess : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hζ : ‖ζ‖ ≤ 4)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hHess : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (Hess j))
    (hJ : IsPhysicalH1Graph volume (Or.inl rfl) g H) :
    ∃ K : Fin d → Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j k, IsPhysicalH1Graph volume (Or.inl rfl) (Hess j k) (K j k)) ∧
      (∑ j, ∑ k, ∑ l, ‖K j k l‖ ^ 2) ≤
        (d : ℝ) * (1 + 2 * (d : ℝ)) *
          ((∑ j, ∑ k, ‖Hess j k‖ ^ 2) + ∑ m, ∑ l,
            (u4H3ForwardDirectionalEnergy Λ M 4 G H Hess m l +
              u4H3TransposeDirectionalEnergy Λ M 4 f G H Hess m l)) := by
  obtain ⟨K, hK, hbound⟩ :=
    u4H3_generator_pair_quantitative Hess hΛ hell hsmooth hfg hG hHess hJ
  refine ⟨K, hK, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro m _
  apply Finset.sum_le_sum
  intro l _
  exact u4H3_directional_energy_force_uniform hΛ hsmooth ζ hζ f G H Hess m l


/-- Appending complex spatial differences composes the corresponding operators. -/
theorem u4HigherDifferences_append {d : ℕ} (as bs : List (Vec d × ℂ))
    (f : Vec d → ℂ) :
    u4HigherDifferences (as ++ bs) f =
      u4HigherDifferences bs (u4HigherDifferences as f) := by
  induction as generalizing f with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨v, c⟩
      simp only [List.cons_append, u4HigherDifferences]
      exact ih _

/-- A scaled spatial difference commutes with translation. -/
theorem u4HigherDifference_translate {d : ℕ} (v z : Vec d) (c : ℂ)
    (f : Vec d → ℂ) :
    u4HigherDifference v c (fun x => f (x + z)) =
      (fun x => u4HigherDifference v c f (x + z)) := by
  funext x
  simp only [u4HigherDifference]
  rw [add_right_comm]

/-- The discrete product terms, indexed recursively by assigning each remaining
step either to the coefficient or to the function. -/
def u4HigherSplitExpansion {d : ℕ} :
    List (Vec d × ℂ) → List (Vec d × ℂ) → List (Vec d × ℂ) →
      Vec d → (Vec d → ℂ) → (Vec d → ℂ) → Vec d → ℂ
  | [], as, bs, z, a, u => fun x =>
      u4HigherDifferences as a x * u4HigherDifferences bs u (x + z)
  | (v, c) :: rest, as, bs, z, a, u => fun x =>
      u4HigherSplitExpansion rest (as ++ [(v, c)]) bs (z + v) a u x +
      u4HigherSplitExpansion rest as (bs ++ [(v, c)]) z a u x

/-- The split expansion is exactly the existing discrete product expansion,
including the shifts accumulated by coefficient differences. -/
theorem u4HigherProductExpansion_split {d : ℕ} (steps as bs : List (Vec d × ℂ))
    (z : Vec d) (a u : Vec d → ℂ) (x : Vec d) :
    u4HigherProductExpansion steps (u4HigherDifferences as a)
      (fun y => u4HigherDifferences bs u (y + z)) x =
      u4HigherSplitExpansion steps as bs z a u x := by
  induction steps generalizing as bs z with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨v, c⟩
      simp only [u4HigherProductExpansion, u4HigherSplitExpansion]
      have ha : u4HigherDifference v c (u4HigherDifferences as a) =
          u4HigherDifferences (as ++ [(v, c)]) a := by
        rw [u4HigherDifferences_append]
        rfl
      have hu : u4HigherDifference v c (fun y => u4HigherDifferences bs u (y + z)) =
          (fun y => u4HigherDifferences (bs ++ [(v, c)]) u (y + z)) := by
        rw [u4HigherDifference_translate, u4HigherDifferences_append]
        rfl
      have ht : (fun y => u4HigherDifferences bs u ((y + v) + z)) =
          (fun y => u4HigherDifferences bs u (y + (z + v))) := by
        funext y
        rw [add_assoc, add_comm v z]
      rw [ha, hu, ht, ih, ih]

/-- The coefficient commutator lists precisely the split terms in which at
least one difference hits the coefficient. -/
def u4HigherSplitCommutator {d : ℕ} :
    List (Vec d × ℂ) → List (Vec d × ℂ) → Vec d →
      (Vec d → ℂ) → (Vec d → ℂ) → Vec d → ℂ
  | [], _, _, _, _ => fun _ => 0
  | (v, c) :: rest, bs, z, a, u => fun x =>
      u4HigherSplitExpansion rest [(v, c)] bs (z + v) a u x +
      u4HigherSplitCommutator rest (bs ++ [(v, c)]) z a u x

/-- Exact all-order commutator decomposition into differentiated coefficients
and translated lower-order function differences. -/
theorem u4HigherCoefficientCommutator_split {d : ℕ}
    (steps bs : List (Vec d × ℂ)) (z : Vec d) (a u : Vec d → ℂ) (x : Vec d) :
    u4HigherCoefficientCommutator steps a
      (fun y => u4HigherDifferences bs u (y + z)) x =
      u4HigherSplitCommutator steps bs z a u x := by
  induction steps generalizing bs z with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨v, c⟩
      simp only [u4HigherCoefficientCommutator, u4HigherSplitCommutator]
      have hu : u4HigherDifference v c (fun y => u4HigherDifferences bs u (y + z)) =
          (fun y => u4HigherDifferences (bs ++ [(v, c)]) u (y + z)) := by
        rw [u4HigherDifference_translate, u4HigherDifferences_append]
        rfl
      have ht : (fun y => u4HigherDifferences bs u ((y + v) + z)) =
          (fun y => u4HigherDifferences bs u (y + (z + v))) := by
        funext y
        rw [add_assoc, add_comm v z]
      rw [hu, ht, ih]
      simpa only [u4HigherDifferences] using
        congrArg (fun t => t + u4HigherSplitCommutator rest (bs ++ [(v, c)]) z a u x)
          (u4HigherProductExpansion_split rest [(v, c)] bs (z + v) a u x)


/-- A split Leibniz term is controlled by the structural derivative bound
and the L² norm of the remaining (possibly translated) differences. -/
theorem u4Coefficient_split_term_L2_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (as : List (Fin d × ℝ)) (hnz : ∀ p ∈ as, p.2 ≠ 0)
    (bs : List (Vec d × ℂ)) (n : ℕ) (a : Fin n → Fin d) (j k : Fin d)
    (horder : 1 ≤ n + as.length) (z : Vec d)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        u4HigherDifferences (as.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          (fun y => (u4CoefficientDerivative ω n a j k y : ℂ)) x *
        u4HigherDifferences bs u (x + z)) ∧
      ‖v‖ ≤ M (n + as.length) *
        (eLpNorm (u4HigherDifferences bs u) 2 (volume : Measure (Vec d))).toReal := by
  let w := u4HigherDifferences bs (u : Vec d → ℂ)
  have hw : MemLp w 2 (volume : Measure (Vec d)) :=
    u4HigherDifferences_memLp bs (Lp.memLp u)
  have ht := hw.comp_measurePreserving
    (measurePreserving_add_right (volume : Measure (Vec d)) z)
  let W : Lp ℂ 2 (volume : Measure (Vec d)) := ht.toLp (fun x => w (x + z))
  have hW : (W : Vec d → ℂ) =ᵐ[volume] (fun x => w (x + z)) := ht.coeFn_toLp
  have hnorm : ‖W‖ = (eLpNorm w 2 (volume : Measure (Vec d))).toReal := by
    rw [Lp.norm_toLp]
    congr 1
    exact eLpNorm_comp_measurePreserving hw.aestronglyMeasurable
      (measurePreserving_add_right (volume : Measure (Vec d)) z)
  obtain ⟨v, hv, hb⟩ :=
    u4CoefficientDerivative_iterated_quotient_multiplier hsmooth as hnz n a j k horder W
  refine ⟨v, ?_, ?_⟩
  · filter_upwards [hv, hW] with x hvx hWx
    rw [hvx, hWx, u4RealCoordinateDifferences_ofReal]
  · simpa only [hnorm, w] using hb


/-- Sum of the structural L² bounds over all assignments of the remaining
coordinate differences to the coefficient or function. -/
def u4CoordinateSplitBound {d : ℕ} (M : ℕ → ℝ) (n : ℕ)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    List (Fin d × ℝ) → List (Fin d × ℝ) → List (Vec d × ℂ) → ℝ
  | [], as, bs => M (n + as.length) *
      (eLpNorm (u4HigherDifferences bs u) 2 (volume : Measure (Vec d))).toReal
  | (i, h) :: rest, as, bs =>
      u4CoordinateSplitBound M n u rest (as ++ [(i, h)]) bs +
      u4CoordinateSplitBound M n u rest as
        (bs ++ [(h • unitVector i, (h : ℂ)⁻¹)])

/-- Summing the split-term bounds gives an L² estimate for the complete
product expansion after at least one coefficient derivative has been taken. -/
theorem u4CoordinateSplitExpansion_L2_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (steps as : List (Fin d × ℝ))
    (hnz : ∀ p ∈ steps, p.2 ≠ 0) (hnzA : ∀ p ∈ as, p.2 ≠ 0)
    (bs : List (Vec d × ℂ)) (n : ℕ) (a : Fin n → Fin d) (j k : Fin d)
    (horder : 1 ≤ n + as.length) (z : Vec d)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        u4HigherSplitExpansion
          (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          (as.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) bs z
          (fun y => (u4CoefficientDerivative ω n a j k y : ℂ)) u x) ∧
      ‖v‖ ≤ u4CoordinateSplitBound M n u steps as bs := by
  induction steps generalizing as bs z with
  | nil =>
      simpa only [List.map_nil, u4HigherSplitExpansion, u4CoordinateSplitBound] using
        u4Coefficient_split_term_L2_bound hsmooth as hnzA bs n a j k horder z u
  | cons p rest ih =>
      rcases p with ⟨i, h⟩
      have hh : h ≠ 0 := hnz (i, h) (by simp)
      have hr : ∀ p ∈ rest, p.2 ≠ 0 := fun p hp => hnz p (List.mem_cons_of_mem _ hp)
      have ha : ∀ p ∈ as ++ [(i, h)], p.2 ≠ 0 := by
        intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hnzA p hp
        · exact hh
      have ho : 1 ≤ n + (as ++ [(i, h)]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      obtain ⟨v₁, hv₁, hb₁⟩ := ih (as ++ [(i, h)]) hr ha bs ho (z + h • unitVector i)
      obtain ⟨v₂, hv₂, hb₂⟩ := ih as hr hnzA
        (bs ++ [(h • unitVector i, (h : ℂ)⁻¹)]) horder z
      refine ⟨v₁ + v₂, ?_, ?_⟩
      · filter_upwards [hv₁, hv₂, Lp.coeFn_add v₁ v₂] with x hx₁ hx₂ hx
        simp only [List.map_cons, List.map_nil, u4HigherSplitExpansion, List.map_append] at hx₁ ⊢
        rw [hx]
        change v₁ x + v₂ x = _
        rw [hx₁, hx₂]
      · simpa only [u4CoordinateSplitBound] using
          (norm_add_le v₁ v₂).trans (add_le_add hb₁ hb₂)


/-- Sum of the structural L² bounds for all terms with a differentiated
coefficient in a signed coordinate commutator. -/
def u4CoordinateCommutatorBound {d : ℕ} (M : ℕ → ℝ) (n : ℕ)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    List (Fin d × ℝ) → List (Vec d × ℂ) → ℝ
  | [], _ => 0
  | (i, h) :: rest, bs =>
      u4CoordinateSplitBound M n u rest [(i, h)] bs +
      u4CoordinateCommutatorBound M n u rest
        (bs ++ [(h • unitVector i, (h : ℂ)⁻¹)])

/-- The entire signed-coordinate coefficient commutator has an explicit L²
bound in terms of structural coefficient bounds and lower differences of u. -/
theorem u4CoordinateCommutator_L2_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (bs : List (Vec d × ℂ)) (n : ℕ) (a : Fin n → Fin d) (j k : Fin d)
    (z : Vec d) (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        u4HigherCoefficientCommutator
          (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          (fun y => (u4CoefficientDerivative ω n a j k y : ℂ))
          (fun y => u4HigherDifferences bs u (y + z)) x) ∧
      ‖v‖ ≤ u4CoordinateCommutatorBound M n u steps bs := by
  have hs : ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        u4HigherSplitCommutator
          (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) bs z
          (fun y => (u4CoefficientDerivative ω n a j k y : ℂ)) u x) ∧
      ‖v‖ ≤ u4CoordinateCommutatorBound M n u steps bs := by
    induction steps generalizing bs z with
    | nil =>
        refine ⟨0, ?_, ?_⟩
        · filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (Vec d))] with x hx
          simpa only [List.map_nil, u4HigherSplitCommutator, Pi.zero_apply] using hx
        · simp [u4CoordinateCommutatorBound]
    | cons p rest ih =>
        rcases p with ⟨i, h⟩
        have hh : h ≠ 0 := hnz (i, h) (by simp)
        have hr : ∀ p ∈ rest, p.2 ≠ 0 := fun p hp => hnz p (List.mem_cons_of_mem _ hp)
        have ha : ∀ p ∈ [(i, h)], p.2 ≠ 0 := by
          intro p hp
          simp only [List.mem_singleton] at hp
          subst p
          exact hh
        obtain ⟨v₁, hv₁, hb₁⟩ := u4CoordinateSplitExpansion_L2_bound hsmooth
          rest [(i, h)] hr ha bs n a j k (by simp) (z + h • unitVector i) u
        obtain ⟨v₂, hv₂, hb₂⟩ := ih hr
          (bs ++ [(h • unitVector i, (h : ℂ)⁻¹)]) z
        refine ⟨v₁ + v₂, ?_, ?_⟩
        · filter_upwards [hv₁, hv₂, Lp.coeFn_add v₁ v₂] with x hx₁ hx₂ hx
          simp only [List.map_cons, List.map_nil, u4HigherSplitCommutator] at hx₁ ⊢
          rw [hx]
          change v₁ x + v₂ x = _
          rw [hx₁, hx₂]
        · simpa only [u4CoordinateCommutatorBound] using
            (norm_add_le v₁ v₂).trans (add_le_add hb₁ hb₂)
  obtain ⟨v, hv, hb⟩ := hs
  refine ⟨v, ?_, hb⟩
  filter_upwards [hv] with x hx
  rw [hx, u4HigherCoefficientCommutator_split]


/-- The preceding estimate applies to the actual physical matrix entry in the
generator, with no prior differences on the function. -/
theorem u4PhysicalCoefficientCommutator_L2_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (j k : Fin d) (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        u4HigherCoefficientCommutator
          (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          (fun y => (ω.1 y j k : ℂ)) u x) ∧
      ‖v‖ ≤ u4CoordinateCommutatorBound M 0 u steps [] := by
  simpa only [u4CoefficientDerivative, iteratedFDeriv_zero_apply,
    u4HigherDifferences, add_zero] using
    u4CoordinateCommutator_L2_bound hsmooth steps hnz [] 0 Fin.elim0 j k 0 u


/-- Iterated signed coordinate quotients are bounded by the corresponding
iterated weak derivative, uniformly in every nonzero step size. -/
theorem u4IteratedCoordinateQuotient_weakDerivative_bound {d N : ℕ}
    (D : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D path) (fun i => D (path ++ [i])))
    (steps : List (Fin d × ℝ)) (path : List (Fin d))
    (hnz : ∀ p ∈ steps, p.2 ≠ 0) (horder : path.length + steps.length ≤ N) :
    (eLpNorm (u4HigherDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (D path))
      2 (volume : Measure (Vec d))).toReal ≤
      ‖D (path ++ (steps.map Prod.fst).reverse)‖ := by
  induction steps using List.reverseRecOn generalizing path with
  | nil =>
      simp only [List.map_nil, List.reverse_nil, List.append_nil, u4HigherDifferences,
        ← Lp.norm_def]
      exact le_rfl
  | append_singleton steps p ih =>
      rcases p with ⟨i, h⟩
      have hh : h ≠ 0 := hnz (i, h) (by simp)
      have hn : ∀ p ∈ steps, p.2 ≠ 0 := fun p hp => hnz p (by simp [hp])
      have hpath : path.length < N := by
        simp only [List.length_append, List.length_singleton] at horder
        omega
      have hnext : (path ++ [i]).length + steps.length ≤ N := by
        simp only [List.length_append, List.length_singleton] at horder ⊢
        omega
      obtain ⟨q, Q, hqQ, hq, hQ⟩ :=
        u4Higher_forward_H1_quotients (steps.map (fun p => (p.2 • unitVector p.1, p.2)))
          (hD path hpath)
      have hq' : (q : Vec d → ℂ) =ᵐ[volume]
          u4HigherDifferences
            (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (D path) := by
        simpa only [List.map_map, Function.comp_def] using hq
      have hQ' : (Q i : Vec d → ℂ) =ᵐ[volume]
          u4HigherDifferences
            (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (D (path ++ [i])) := by
        simpa only [List.map_map, Function.comp_def] using hQ i
      have he : (fun x => (q (x + h • unitVector i) - q x) / (h : ℂ)) =ᵐ[volume]
          u4HigherDifferences
            ((steps ++ [(i, h)]).map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
            (D path) := by
        have he' := u4HigherDifferences_ae [(h • unitVector i, (h : ℂ)⁻¹)] hq'
        filter_upwards [he'] with x hx
        simp only [List.map_append, List.map_cons, List.map_nil, u4HigherDifferences_append,
          u4HigherDifferences, u4HigherDifference, div_eq_mul_inv, mul_comm] at hx ⊢
        exact hx
      calc
        _ = (eLpNorm (fun x => (q (x + h • unitVector i) - q x) / (h : ℂ))
            2 (volume : Measure (Vec d))).toReal := by rw [eLpNorm_congr_ae he]
        _ ≤ ‖Q i‖ := c18_physical_H1_coordinate_difference_quotient_bound hqQ i h hh
        _ = (eLpNorm (u4HigherDifferences
            (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
              (D (path ++ [i]))) 2 (volume : Measure (Vec d))).toReal := by
            rw [Lp.norm_def, eLpNorm_congr_ae hQ']
        _ ≤ ‖D ((path ++ [i]) ++ (steps.map Prod.fst).reverse)‖ := ih (path ++ [i]) hn hnext
        _ = _ := by simp [List.map_append, List.reverse_append, List.append_assoc]


/-- A split expansion is uniformly bounded by the coefficient and weak
  derivative bounds at the orders that actually occur in the expansion. -/
theorem u4CoordinateSplitBound_weakDerivative_bound {d N : ℕ}
    (M : ℕ → ℝ) (n : ℕ) (D : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D path) (fun i => D (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A)
    (hDB : ∀ path, path.length ≤ N → ‖D path‖ ≤ B)
    (steps as bs : List (Fin d × ℝ))
    (hnz : ∀ p ∈ steps ++ bs, p.2 ≠ 0)
    (horder : bs.length + steps.length ≤ N)
    (hM : ∀ k ≤ n + (steps.length + as.length), M k ≤ A) :
    u4CoordinateSplitBound M n (D []) steps as
      (bs.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) ≤
      (2 : ℝ) ^ steps.length * A * B := by
  induction steps generalizing as bs with
  | nil =>
      have hq := u4IteratedCoordinateQuotient_weakDerivative_bound D hD bs []
        (by simpa using hnz) (by simpa using horder)
      have hqB := hq.trans (hDB _ (by simpa using horder))
      have hm := hM (n + as.length) (by simp)
      simpa only [u4CoordinateSplitBound, List.length_nil, pow_zero, one_mul] using
        (mul_le_mul hm hqB (ENNReal.toReal_nonneg) hA)
  | cons p rest ih =>
      rcases p with ⟨i, h⟩
      have hnz₁ : ∀ p ∈ rest ++ bs, p.2 ≠ 0 := by
        intro p hp
        apply hnz p
        simp only [List.mem_append, List.mem_cons] at hp ⊢
        tauto
      have hnz₂ : ∀ p ∈ rest ++ (bs ++ [(i, h)]), p.2 ≠ 0 := by
        intro p hp
        apply hnz p
        simp only [List.mem_append, List.mem_cons] at hp ⊢
        tauto
      have ho₁ : bs.length + rest.length ≤ N := by
        simp only [List.length_cons] at horder
        omega
      have ho₂ : (bs ++ [(i, h)]).length + rest.length ≤ N := by
        simp only [List.length_cons] at horder
        simp only [List.length_append, List.length_singleton]
        omega
      have hm₁ : ∀ k ≤ n + (rest.length + (as ++ [(i, h)]).length), M k ≤ A := by
        intro k hk
        apply hM k
        simp only [List.length_cons, List.length_append, List.length_nil] at hk ⊢
        omega
      have hm₂ : ∀ k ≤ n + (rest.length + as.length), M k ≤ A := by
        intro k hk
        apply hM k
        simp only [List.length_cons] at ⊢
        omega
      have h₁ := ih (as ++ [(i, h)]) bs hnz₁ ho₁ hm₁
      have h₂ := ih as (bs ++ [(i, h)]) hnz₂ ho₂ hm₂
      simp only [List.map_append, List.map_cons, List.map_nil] at h₂
      simp only [u4CoordinateSplitBound, List.length_cons, pow_succ]
      nlinarith


/-- The full commutator needs only one fewer function derivative than
  the total number of coordinate differences. -/
theorem u4CoordinateCommutatorBound_weakDerivative_bound {d N : ℕ}
    (M : ℕ → ℝ) (n : ℕ) (D : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D path) (fun i => D (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ path, path.length ≤ N → ‖D path‖ ≤ B)
    (steps bs : List (Fin d × ℝ))
    (hnz : ∀ p ∈ steps ++ bs, p.2 ≠ 0)
    (horder : bs.length + steps.length ≤ N + 1)
    (hM : ∀ k ≤ n + steps.length, M k ≤ A) :
    u4CoordinateCommutatorBound M n (D []) steps
      (bs.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) ≤
      (2 : ℝ) ^ steps.length * A * B := by
  induction steps generalizing bs with
  | nil =>
      simpa only [u4CoordinateCommutatorBound, List.length_nil, pow_zero, one_mul] using
        (mul_nonneg hA hB)
  | cons p rest ih =>
      rcases p with ⟨i, h⟩
      have hnz₁ : ∀ p ∈ rest ++ bs, p.2 ≠ 0 := by
        intro p hp
        apply hnz p
        simp only [List.mem_append, List.mem_cons] at hp ⊢
        tauto
      have hnz₂ : ∀ p ∈ rest ++ (bs ++ [(i, h)]), p.2 ≠ 0 := by
        intro p hp
        apply hnz p
        simp only [List.mem_append, List.mem_cons] at hp ⊢
        tauto
      have ho₁ : bs.length + rest.length ≤ N := by
        simp only [List.length_cons] at horder
        omega
      have ho₂ : (bs ++ [(i, h)]).length + rest.length ≤ N + 1 := by
        simp only [List.length_cons] at horder
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hm₁ : ∀ k ≤ n + (rest.length + [(i, h)].length), M k ≤ A := by
        intro k hk
        apply hM k
        simp only [List.length_cons, List.length_nil] at hk ⊢
        omega
      have hm₂ : ∀ k ≤ n + rest.length, M k ≤ A := by
        intro k hk
        apply hM k
        simp only [List.length_cons]
        omega
      have h₁ := u4CoordinateSplitBound_weakDerivative_bound M n D hD A B hA hDB
        rest [(i, h)] bs hnz₁ ho₁ hm₁
      have h₂ := ih (bs ++ [(i, h)]) hnz₂ ho₂ hm₂
      simp only [List.map_append, List.map_cons, List.map_nil] at h₂
      simp only [u4CoordinateCommutatorBound, List.length_cons, pow_succ]
      nlinarith

/-- Quantitative L² bound for the physical coefficient commutator in terms
  of weak derivatives, uniform in all nonzero signed step sizes. -/
theorem u4PhysicalCoefficientCommutator_uniform_L2_bound {d N : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (D : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D path) (fun i => D (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ path, path.length ≤ N → ‖D path‖ ≤ B)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N + 1) (hM : ∀ k ≤ steps.length, M k ≤ A)
    (j k : Fin d) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        u4HigherCoefficientCommutator
          (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          (fun y => (ω.1 y j k : ℂ)) (D []) x) ∧
      ‖v‖ ≤ (2 : ℝ) ^ steps.length * A * B := by
  obtain ⟨v, hv, hb⟩ := u4PhysicalCoefficientCommutator_L2_bound hsmooth steps hnz j k (D [])
  refine ⟨v, hv, hb.trans ?_⟩
  simpa only [List.map_nil, List.length_nil, zero_add, List.append_nil] using
    u4CoordinateCommutatorBound_weakDerivative_bound M 0 D hD A B hA hB hDB
      steps [] (by simpa using hnz) (by simpa using horder) (by simpa using hM)


/-- The complete matrix of coefficient commutators has a uniform summed
  L² bound, as required by the differentiated principal pairing. -/
theorem u4PhysicalCoefficientCommutator_matrix_uniform_L2_bound {d N : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun i => D k (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N + 1) (hM : ∀ k ≤ steps.length, M k ≤ A) :
    ∃ V : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ j k, (V j k : Vec d → ℂ) =ᵐ[volume] (fun x =>
        u4HigherCoefficientCommutator
          (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          (fun y => (ω.1 y j k : ℂ)) (D k []) x)) ∧
      (∑ j, ∑ k, ‖V j k‖) ≤
        (d : ℝ) ^ 2 * ((2 : ℝ) ^ steps.length * A * B) := by
  classical
  have hex : ∀ j k, ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume] (fun x =>
        u4HigherCoefficientCommutator
          (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          (fun y => (ω.1 y j k : ℂ)) (D k []) x) ∧
      ‖v‖ ≤ (2 : ℝ) ^ steps.length * A * B := by
    intro j k
    exact u4PhysicalCoefficientCommutator_uniform_L2_bound hsmooth (D k) (hD k)
      A B hA hB (hDB k) steps hnz horder hM j k
  choose V hV hnorm using hex
  refine ⟨V, hV, ?_⟩
  calc
    (∑ j, ∑ k, ‖V j k‖) ≤
        ∑ _j : Fin d, ∑ _k : Fin d, ((2 : ℝ) ^ steps.length * A * B) := by
      exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hnorm j k
    _ = (d : ℝ) ^ 2 * ((2 : ℝ) ^ steps.length * A * B) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring


/-- The physical commutator contribution in the differentiated energy
  identity is integrable and bounded in either matrix orientation. -/
theorem u4PhysicalCoefficientCommutator_energy_bound {d N : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun i => D k (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N + 1) (hM : ∀ k ≤ steps.length, M k ≤ A)
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (transpose : Bool) :
    let C := fun j k x => u4HigherCoefficientCommutator
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
      (fun y => (ω.1 y (if transpose then k else j) (if transpose then j else k) : ℂ))
      (D k []) x
    (∀ j k, Integrable (fun x => C j k x * star (Q j x)) volume) ∧
    ‖∑ j, ∑ k, ∫ x, C j k x * star (Q j x)‖ ≤
      (d : ℝ) * ((2 : ℝ) ^ steps.length * A * B) * (∑ j, ‖Q j‖) := by
  classical
  dsimp only
  let C := fun j k x => u4HigherCoefficientCommutator
    (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
    (fun y => (ω.1 y (if transpose then k else j) (if transpose then j else k) : ℂ))
    (D k []) x
  have hpair : ∀ j k, Integrable (fun x => C j k x * star (Q j x)) volume ∧
      ‖∫ x, C j k x * star (Q j x)‖ ≤
        ((2 : ℝ) ^ steps.length * A * B) * ‖Q j‖ := by
    intro j k
    obtain ⟨v, hv, hb⟩ := u4PhysicalCoefficientCommutator_uniform_L2_bound
      hsmooth (D k) (hD k) A B hA hB (hDB k) steps hnz horder hM
        (if transpose then k else j) (if transpose then j else k)
    have hv' : (v : Vec d → ℂ) =ᵐ[volume] C j k := hv
    constructor
    · apply ((Lp.memLp v).integrable_mul (Lp.memLp (Q j)).star).congr
      filter_upwards [hv'] with x hx
      simp only [Pi.mul_apply, Pi.star_apply]
      rw [hx]
    · have heq : (∫ x, C j k x * star (Q j x)) = inner ℂ (Q j) v := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hv'] with x hx
        simp only [RCLike.inner_apply, Complex.star_def]
        rw [hx]
      rw [heq]
      calc
        ‖inner ℂ (Q j) v‖ ≤ ‖Q j‖ * ‖v‖ := norm_inner_le_norm _ _
        _ ≤ ‖Q j‖ * ((2 : ℝ) ^ steps.length * A * B) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = _ := by ring
  constructor
  · exact fun j k => (hpair j k).1
  · calc
      ‖∑ j, ∑ k, ∫ x, C j k x * star (Q j x)‖ ≤
          ∑ j, ∑ k, ‖∫ x, C j k x * star (Q j x)‖ :=
        le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
      _ ≤ ∑ j, ∑ _k : Fin d, (((2 : ℝ) ^ steps.length * A * B) * ‖Q j‖) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hpair j k).2))
      _ = (d : ℝ) * ((2 : ℝ) ^ steps.length * A * B) * (∑ j, ‖Q j‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Summation by parts bounds an arbitrary-order backward forcing test by
the corresponding weak derivative of the forcing and the original test. -/
theorem u4Higher_backward_forcing_weakDerivative_bound {d N : ℕ}
    (D : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D path) (fun i => D (path ++ [i])))
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N)
    (v q : Lp ℂ 2 (volume : Measure (Vec d)))
    (hq : (q : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) v) :
    ‖∫ x, D [] x * q x‖ ≤ ‖D ((steps.map Prod.fst).reverse)‖ * ‖v‖ := by
  let S := steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))
  let F := u4HigherDifferences S (D [])
  have hF : MemLp F 2 (volume : Measure (Vec d)) :=
    u4HigherDifferences_memLp S (Lp.memLp (D []))
  let w := hF.toLp F
  have hw : (w : Vec d → ℂ) =ᵐ[volume] F := hF.coeFn_toLp
  have hnorm : ‖w‖ ≤ ‖D ((steps.map Prod.fst).reverse)‖ := by
    rw [Lp.norm_toLp]
    simpa only [List.nil_append] using
      u4IteratedCoordinateQuotient_weakDerivative_bound D hD steps [] hnz (by simpa using horder)
  have heq : (∫ x, D [] x * q x) = inner ℂ (star v) w := by
    calc
      _ = ∫ x, D [] x * u4HigherBackwardDifferences S v x := by
        apply integral_congr_ae
        filter_upwards [hq] with x hx
        rw [hx]
      _ = ∫ x, F x * v x :=
        (u4HigherDifferences_integration_by_parts S (Lp.memLp (D [])) (Lp.memLp v)).symm
      _ = inner ℂ (star v) w := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hw, Lp.coeFn_star v] with x hx hs
        simp only [hx, hs, RCLike.inner_apply, Pi.star_apply, Complex.star_def,
          Complex.conj_conj, mul_comm]
  rw [heq]

  calc
    ‖inner ℂ (star v) w‖ ≤ ‖star v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * ‖D ((steps.map Prod.fst).reverse)‖ := by
      rw [c23_L2_norm_star]
      exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- Arbitrary signed backward tests of a physical coefficient product are
bounded uniformly by weak derivatives of the multiplied function. -/
theorem u4Higher_coefficient_backward_pairing_bound {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    (D : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D path) (fun i => D (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ path, path.length ≤ N → ‖D path‖ ≤ B)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N) (hM : ∀ k ≤ steps.length, M k ≤ A)
    (j k : Fin d) (v q : Lp ℂ 2 (volume : Measure (Vec d)))
    (hq : (q : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
        ((star v : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ)) :
    ‖∫ x, (ω.1 x j k : ℂ) * D [] x * q x‖ ≤
      (Λ * B + (2 : ℝ) ^ steps.length * A * B) * ‖v‖ := by
  let S := steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))
  let a : Vec d → ℂ := fun x => (ω.1 x j k : ℂ)
  let F := u4HigherDifferences S (D [])
  have ha : MemLp a ∞ (volume : Measure (Vec d)) :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous) j k
  have hF : MemLp F 2 (volume : Measure (Vec d)) :=
    u4HigherDifferences_memLp S (Lp.memLp (D []))
  let w := hF.toLp F
  have hw : (w : Vec d → ℂ) =ᵐ[volume] F := hF.coeFn_toLp
  have hwb : ‖w‖ ≤ B := by
    rw [Lp.norm_toLp]
    have hb := u4IteratedCoordinateQuotient_weakDerivative_bound D hD steps [] hnz
      (by simpa using horder)
    have hp : ((steps.map Prod.fst).reverse).length ≤ N := by simpa using horder
    have hb' : (eLpNorm F 2 (volume : Measure (Vec d))).toReal ≤
        ‖D ((steps.map Prod.fst).reverse)‖ := by
      simpa only [List.nil_append] using hb
    exact hb'.trans (hDB _ hp)
  obtain ⟨c, hc, hcb⟩ := u4PhysicalCoefficientCommutator_uniform_L2_bound
    hsmooth D hD A B hA hB hDB steps hnz (by omega) hM j k
  have hp : MemLp (fun x => a x * D [] x) 2 (volume : Measure (Vec d)) := by
    change MemLp (a * (D [] : Vec d → ℂ)) 2 volume
    exact ha.mul (r := 2) (Lp.memLp (D []))
  have hi₁ : Integrable (fun x => a x * w x * star (v x)) volume :=
    (ha.mul (r := 2) (Lp.memLp w)).integrable_mul (Lp.memLp v).star
  have hi₂ : Integrable (fun x => c x * star (v x)) volume :=
    (Lp.memLp c).integrable_mul (Lp.memLp v).star
  have he : (∫ x, (ω.1 x j k : ℂ) * D [] x * q x) =
      (∫ x, a x * w x * star (v x)) + ∫ x, c x * star (v x) := by
    calc
      _ = ∫ x, (a x * D [] x) * u4HigherBackwardDifferences S
          ((star v : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) x := by
        apply integral_congr_ae
        filter_upwards [hq] with x hx
        exact congrArg (fun z : ℂ => a x * D [] x * z) hx
      _ = ∫ x, u4HigherDifferences S (fun x => a x * D [] x) x * (star v) x :=
        (u4HigherDifferences_integration_by_parts S hp (Lp.memLp (star v))).symm
      _ = ∫ x, (a x * w x * star (v x) + c x * star (v x)) := by
        apply integral_congr_ae
        filter_upwards [hw, hc, Lp.coeFn_star v] with x hx hy hz
        change w x = u4HigherDifferences S (D []) x at hx
        change c x = u4HigherCoefficientCommutator S a (D []) x at hy
        rw [u4HigherDifferences_product, u4HigherProductExpansion_principal, ← hx, ← hy, hz]
        simp only [Pi.star_apply, add_mul]
      _ = _ := integral_add hi₁ hi₂
  have hcPair : ‖∫ x, c x * star (v x)‖ ≤ ‖c‖ * ‖v‖ := by
    have heq : (∫ x, c x * star (v x)) = inner ℂ v c := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp only [RCLike.inner_apply, Complex.star_def]
    rw [heq]
    exact (norm_inner_le_norm _ _).trans_eq (mul_comm _ _)
  rw [he]
  calc
    _ ≤ ‖∫ x, a x * w x * star (v x)‖ + ‖∫ x, c x * star (v x)‖ := norm_add_le _ _
    _ ≤ Λ * ‖w‖ * ‖v‖ + ‖c‖ * ‖v‖ :=
      add_le_add (by simpa [a] using c23_elliptic_entry_pairing_bound hΛ hell hsmooth j k 0 w v) hcPair
    _ ≤ (Λ * B + (2 : ℝ) ^ steps.length * A * B) * ‖v‖ := by
      have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
      have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwb hΛ0)
        (norm_nonneg v)
      have h₂ := mul_le_mul_of_nonneg_right hcb (norm_nonneg v)
      nlinarith only [h₁, h₂]


/-- The summed physical coefficient drift pairing obeys the same signed
quotient bound, uniformly over all spatial components. -/
theorem u4Higher_coefficient_backward_sum_bound {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ j path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D j path) (fun i => D j (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ j path, path.length ≤ N → ‖D j path‖ ≤ B)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N) (hM : ∀ k ≤ steps.length, M k ≤ A)
    (a b : Fin d → Fin d) (v q : Lp ℂ 2 (volume : Measure (Vec d)))
    (hq : (q : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
        ((star v : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ)) :
    ‖∑ j, ∫ x, (ω.1 x (a j) (b j) : ℂ) * D j [] x * q x‖ ≤
      (d : ℝ) * (Λ * B + (2 : ℝ) ^ steps.length * A * B) * ‖v‖ := by
  classical
  calc
    _ ≤ ∑ j, ‖∫ x, (ω.1 x (a j) (b j) : ℂ) * D j [] x * q x‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, (Λ * B + (2 : ℝ) ^ steps.length * A * B) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact u4Higher_coefficient_backward_pairing_bound hΛ hell hsmooth (D j) (hD j)
        A B hA hB (hDB j) steps hnz horder hM (a j) (b j) v q hq
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring


/-- The differentiated principal pairing differs from the coercive energy
by the uniformly controlled coefficient commutators. -/
theorem u4Higher_principal_energy_error {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun i => D k (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N + 1) (hM : ∀ k ≤ steps.length, M k ≤ A)
    (Q T : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (transpose : Bool)
    (hQ : ∀ k, (Q k : Vec d → ℂ) =ᵐ[volume] u4HigherDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (D k []))
    (hT : ∀ j, (T j : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
        ((star (Q j) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ)) :
    ‖(∑ j, ∑ k, ∫ x,
        (ω.1 x (if transpose then k else j) (if transpose then j else k) : ℂ) *
          D k [] x * T j x) -
      (∑ j, ∑ k, ∫ x,
        (ω.1 x (if transpose then k else j) (if transpose then j else k) : ℂ) *
          Q k x * star (Q j x))‖ ≤
      (d : ℝ) * ((2 : ℝ) ^ steps.length * A * B) * (∑ j, ‖Q j‖) := by
  classical
  let S := steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))
  let C := fun j k x => u4HigherCoefficientCommutator S
    (fun y => (ω.1 y (if transpose then k else j) (if transpose then j else k) : ℂ))
    (D k []) x
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hc := u4PhysicalCoefficientCommutator_energy_bound hsmooth D hD A B hA hB hDB
    steps hnz horder hM Q transpose
  change (∀ j k, Integrable (fun x => C j k x * star (Q j x)) volume) ∧ _ at hc
  have he (j k : Fin d) :
      (∫ x, (ω.1 x (if transpose then k else j) (if transpose then j else k) : ℂ) *
        D k [] x * T j x) =
      (∫ x, (ω.1 x (if transpose then k else j) (if transpose then j else k) : ℂ) *
        Q k x * star (Q j x)) + ∫ x, C j k x * star (Q j x) := by
    let a : Vec d → ℂ := fun x => (ω.1 x (if transpose then k else j)
      (if transpose then j else k) : ℂ)
    have hi : Integrable (fun x => a x * Q k x * star (Q j x)) volume :=
      ((ha _ _).mul (r := 2) (Lp.memLp (Q k))).integrable_mul (Lp.memLp (Q j)).star
    calc
      _ = ∫ x, a x * D k [] x * u4HigherBackwardDifferences S ((star (Q j) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) x := by
        apply integral_congr_ae
        filter_upwards [hT j] with x hx
        rw [hx]
      _ = ∫ x, (a x * u4HigherDifferences S (D k []) x + C j k x) * ((star (Q j) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) x :=
        u4Higher_backward_principal_pairing S a (ha _ _) (D k []) (star (Q j))
      _ = ∫ x, (a x * Q k x * star (Q j x) + C j k x * star (Q j x)) := by
        apply integral_congr_ae
        filter_upwards [hQ k, Lp.coeFn_star (Q j)] with x hq hs
        simp only [Pi.star_apply] at hs
        rw [← hq, hs]
        ring
      _ = _ := integral_add hi (hc.1 j k)
  have hs : (∑ j, ∑ k, ∫ x,
        (ω.1 x (if transpose then k else j) (if transpose then j else k) : ℂ) *
          D k [] x * T j x) =
      (∑ j, ∑ k, ∫ x,
        (ω.1 x (if transpose then k else j) (if transpose then j else k) : ℂ) *
          Q k x * star (Q j x)) + ∑ j, ∑ k, ∫ x, C j k x * star (Q j x) := by
    simp_rw [he, Finset.sum_add_distrib]
  rw [hs, add_sub_cancel_left]
  exact hc.2


/-- The actual forward generator gives a coercive all-order quotient energy
estimate, with its forcing and drift pairings retained for separate bounds. -/
theorem u4Higher_forward_generator_energy {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f g q : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f (fun k => D k []))
    (hqQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N + 1) (hM : ∀ k ≤ steps.length, M k ≤ A)
    (hQ : ∀ k, (Q k : Vec d → ℂ) =ᵐ[volume] u4HigherDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (D k [])) :
    ∃ (r : Lp ℂ 2 (volume : Measure (Vec d)))
      (T : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      (r : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
        (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          ((star q : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) ∧
      (∀ j, (T j : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
        (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          ((star (Q j) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ)) ∧
      Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
        2 * (‖∫ x, g x * r x‖ + ‖ζ‖ *
          ‖∫ x, (∑ j, (ω.1 x j i : ℂ) * D j [] x) * r x‖) +
        (d : ℝ) * ((2 : ℝ) ^ steps.length * A * B) * (∑ j, ‖Q j‖) := by
  let S := steps.map (fun p => (p.2 • unitVector p.1, p.2))
  obtain ⟨r, T, _, hr, hT, hw⟩ :=
    u4Higher_generator_backward_test hfg hG (physicalH1Graph_star q Q hqQ) S
  have hr' : (r : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
        ((star q : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) := by
    simpa only [S, List.map_map, Function.comp_def] using hr
  have hT' : ∀ j, (T j : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
        ((star (Q j) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) := by
    intro j
    simpa only [S, List.map_map, Function.comp_def] using hT j
  refine ⟨r, T, hr', hT', ?_⟩
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hw' : (∫ x, g x * r x) = -(1 / 2 : ℂ) *
      (∑ j, ∑ k, ∫ x, (ω.1 x j k : ℂ) * D k [] x * T j x) +
      ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) * D j [] x) * r x) := by
    rw [u4h3_principal_integral_sum ha (fun k => D k []) T (fun j _ => j) (fun _ k => k)] at hw
    exact hw
  have he := u4Higher_principal_energy_error hΛ hell hsmooth D hD A B hA hB hDB
    steps hnz horder hM Q T false hQ hT'
  have hc := u4h3_energy_of_weak_identity hΛ hell hsmooth Q 0 false _ _ _ ζ _ (by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using he) hw'
  simpa using hc

/-- The actual transpose generator gives a coercive all-order quotient energy
estimate, with its forcing and drift pairings retained for separate bounds. -/
theorem u4Higher_transpose_generator_energy {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f g q : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f (fun k => D k []))
    (hqQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N + 1) (hM : ∀ k ≤ steps.length, M k ≤ A)
    (hQ : ∀ k, (Q k : Vec d → ℂ) =ᵐ[volume] u4HigherDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (D k [])) :
    ∃ (r : Lp ℂ 2 (volume : Measure (Vec d)))
      (T : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      (r : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
        (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          ((star q : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) ∧
      (∀ j, (T j : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
        (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
          ((star (Q j) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ)) ∧
      Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
        2 * (‖∫ x, g x * r x‖ + ‖ζ‖ *
          ‖∫ x, f x * (∑ j, (ω.1 x j i : ℂ) * T j x)‖) +
        (d : ℝ) * ((2 : ℝ) ^ steps.length * A * B) * (∑ j, ‖Q j‖) := by
  let S := steps.map (fun p => (p.2 • unitVector p.1, p.2))
  obtain ⟨r, T, _, hr, hT, hw⟩ :=
    u4Higher_transpose_generator_backward_test hfg hG (physicalH1Graph_star q Q hqQ) S
  have hr' : (r : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
        ((star q : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) := by
    simpa only [S, List.map_map, Function.comp_def] using hr
  have hT' : ∀ j, (T j : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
        ((star (Q j) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) := by
    intro j
    simpa only [S, List.map_map, Function.comp_def] using hT j
  refine ⟨r, T, hr', hT', ?_⟩
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hw' : (∫ x, g x * r x) = -(1 / 2 : ℂ) *
      (∑ j, ∑ k, ∫ x, (ω.1 x k j : ℂ) * D k [] x * T j x) +
      ζ * (∫ x, f x * (∑ j, (ω.1 x j i : ℂ) * T j x)) := by
    rw [u4h3_principal_integral_sum ha (fun k => D k []) T (fun _ k => k) (fun j _ => j)] at hw
    exact hw
  have he := u4Higher_principal_energy_error hΛ hell hsmooth D hD A B hA hB hDB
    steps hnz horder hM Q T true hQ hT'
  have hc := u4h3_energy_of_weak_identity hΛ hell hsmooth Q 0 true _ _ _ ζ _ (by
    simpa only [↓reduceIte, add_zero] using he) hw'
  simpa using hc


/-- A signed backward coordinate quotient of an H1 function is bounded by
its corresponding weak derivative, uniformly over nonzero step sizes. -/
theorem u4Higher_backward_coordinate_H1_bound {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (i : Fin d) (h : ℝ) (hh : h ≠ 0)
    (q : Lp ℂ 2 (volume : Measure (Vec d)))
    (hq : (q : Vec d → ℂ) =ᵐ[volume]
      u4HigherBackwardDifferences [(h • unitVector i, (h : ℂ)⁻¹)] f) :
    ‖q‖ ≤ ‖G i‖ := by
  have he : (fun x : Vec d => (f (x + (-h) • unitVector i) - f x) / ((-h : ℝ) : ℂ)) =
      (fun x => -u4HigherBackwardDifferences [(h • unitVector i, (h : ℂ)⁻¹)] f x) := by
    funext x
    simp only [u4HigherBackwardDifferences, u4HigherDifference, neg_smul, sub_eq_add_neg,
      Complex.ofReal_neg, div_eq_mul_inv, inv_neg]
    ring
  have hb := c18_physical_H1_coordinate_difference_quotient_bound hG i (-h) (neg_ne_zero.mpr hh)
  rw [he] at hb
  rw [Lp.norm_def, eLpNorm_congr_ae hq]
  change (eLpNorm (-(u4HigherBackwardDifferences
    [(h • unitVector i, (h : ℂ)⁻¹)] f)) 2 volume).toReal ≤ ‖G i‖ at hb
  rw [eLpNorm_neg] at hb
  exact hb


/-- Backward differences compose in the order dual to the forward list. -/
theorem u4HigherBackwardDifferences_append {d : ℕ}
    (a b : List (Vec d × ℂ)) (f : Vec d → ℂ) :
    u4HigherBackwardDifferences (a ++ b) f =
      u4HigherBackwardDifferences a (u4HigherBackwardDifferences b f) := by
  induction a with
  | nil => rfl
  | cons p a ih =>
      rcases p with ⟨z, c⟩
      simp only [List.cons_append, u4HigherBackwardDifferences, ih]

/-- Backward differences preserve almost-everywhere equality. -/
theorem u4HigherBackwardDifferences_ae {d : ℕ} (steps : List (Vec d × ℂ))
    {f g : Vec d → ℂ} (hfg : f =ᵐ[volume] g) :
    u4HigherBackwardDifferences steps f =ᵐ[volume]
      u4HigherBackwardDifferences steps g := by
  induction steps with
  | nil => exact hfg
  | cons p rest ih =>
      rcases p with ⟨z, c⟩
      have ht := (measurePreserving_add_right (volume : Measure (Vec d)) (-z)).quasiMeasurePreserving.ae ih
      filter_upwards [ih, ht] with x hx hxt
      simp only [u4HigherBackwardDifferences, u4HigherDifference, Function.comp_apply] at *
      rw [hx, hxt]

/-- The generator forcing pairing loses only one fewer derivative than the
number of signed quotients, with the remaining difference controlled by H1. -/
theorem u4Higher_backward_forcing_gradient_bound {d N : ℕ}
    (D : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D path) (fun i => D (path ++ [i])))
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N) (i : Fin d) (h : ℝ) (hh : h ≠ 0)
    {q r : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hqQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (hr : (r : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      ((steps ++ [(i, h)]).map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
      ((star q : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ)) :
    ‖∫ x, D [] x * r x‖ ≤ ‖D ((steps.map Prod.fst).reverse)‖ * ‖Q i‖ := by
  have hstar := physicalH1Graph_star q Q hqQ
  obtain ⟨v, V, hvV, hv, hV⟩ :=
    c18_physical_H1_difference_quotient hstar (h • unitVector i) h
  have hv' : (v : Vec d → ℂ) =ᵐ[volume]
      u4HigherBackwardDifferences [(h • unitVector i, (h : ℂ)⁻¹)]
        ((star q : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) := by
    filter_upwards [hv] with x hx
    simpa only [u4HigherBackwardDifferences, u4HigherDifference, sub_eq_add_neg] using hx
  have hvbound := u4Higher_backward_coordinate_H1_bound hstar i h hh v hv'
  rw [c23_L2_norm_star] at hvbound
  have hr' : (r : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) v := by
    have he := (u4HigherBackwardDifferences_ae
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) hv').symm
    apply hr.trans
    simpa only [List.map_append, List.map_cons, List.map_nil,
      u4HigherBackwardDifferences_append] using he
  exact (u4Higher_backward_forcing_weakDerivative_bound D hD steps hnz horder v r hr').trans
    (mul_le_mul_of_nonneg_left hvbound (norm_nonneg _))


/-- A forward coefficient drift pairing with one more backward difference
is controlled by lower-order coefficient bounds and the test gradient. -/
theorem u4Higher_coefficient_backward_sum_gradient_bound
    {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ j path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D j path) (fun i => D j (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ j path, path.length ≤ N → ‖D j path‖ ≤ B)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N) (hM : ∀ k ≤ steps.length, M k ≤ A)
    (a b : Fin d → Fin d) (i : Fin d) (h : ℝ) (hh : h ≠ 0)
    {q r : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hqQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (hr : (r : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      ((steps ++ [(i, h)]).map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
      ((star q : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ)) :
    ‖∑ j, ∫ x, (ω.1 x (a j) (b j) : ℂ) * D j [] x * r x‖ ≤
      (d : ℝ) * (Λ * B + (2 : ℝ) ^ steps.length * A * B) * ‖Q i‖ := by
  have hstar := physicalH1Graph_star q Q hqQ
  obtain ⟨v, V, hvV, hv, hV⟩ :=
    c18_physical_H1_difference_quotient hstar (h • unitVector i) h
  have hv' : (v : Vec d → ℂ) =ᵐ[volume]
      u4HigherBackwardDifferences [(h • unitVector i, (h : ℂ)⁻¹)]
        ((star q : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) := by
    filter_upwards [hv] with x hx
    simpa only [u4HigherBackwardDifferences, u4HigherDifference, sub_eq_add_neg] using hx
  have hvbound := u4Higher_backward_coordinate_H1_bound hstar i h hh v hv'
  rw [c23_L2_norm_star] at hvbound
  have hr' : (r : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) v := by
    have he := (u4HigherBackwardDifferences_ae
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) hv').symm
    apply hr.trans
    simpa only [List.map_append, List.map_cons, List.map_nil,
      u4HigherBackwardDifferences_append] using he
  have hr'' : (r : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
        ((star (star v : Lp ℂ 2 (volume : Measure (Vec d))) :
          Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) := by
    simpa only [star_star] using hr'
  have hb := u4Higher_coefficient_backward_sum_bound hΛ hell hsmooth D hD A B hA hB
    hDB steps hnz horder hM a b (star v) r hr''
  rw [c23_L2_norm_star] at hb
  have hc : 0 ≤ (d : ℝ) * (Λ * B + (2 : ℝ) ^ steps.length * A * B) := by
    have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
    positivity
  exact hb.trans (mul_le_mul_of_nonneg_left hvbound hc)


/-- The transpose drift pairs one coefficient product with each backward
test gradient; its bound retains the sum of gradient L2 norms. -/
theorem u4Higher_coefficient_backward_transpose_sum_bound
    {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D path) (fun i => D (path ++ [i])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ path, path.length ≤ N → ‖D path‖ ≤ B)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N) (hM : ∀ k ≤ steps.length, M k ≤ A)
    (i : Fin d) (Q T : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hT : ∀ j, (T j : Vec d → ℂ) =ᵐ[volume] u4HigherBackwardDifferences
      (steps.map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)))
        ((star (Q j) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ)) :
    ‖∑ j, ∫ x, (ω.1 x j i : ℂ) * D [] x * T j x‖ ≤
      (Λ * B + (2 : ℝ) ^ steps.length * A * B) * ∑ j, ‖Q j‖ := by
  classical
  calc
    _ ≤ ∑ j, ‖∫ x, (ω.1 x j i : ℂ) * D [] x * T j x‖ := norm_sum_le _ _
    _ ≤ ∑ j, (Λ * B + (2 : ℝ) ^ steps.length * A * B) * ‖Q j‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact u4Higher_coefficient_backward_pairing_bound hΛ hell hsmooth D hD A B hA hB
        hDB steps hnz horder hM j i (Q j) (T j) (hT j)
    _ = _ := (Finset.mul_sum _ _ _).symm


/-- An actual coefficient drift pairing may be integrated coordinatewise. -/
theorem u4Higher_drift_integral_sum {d : ℕ} {a : Vec d → Mat d}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (F T : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (p q : Fin d → Fin d) :
    (∫ x, ∑ j, (a x (p j) (q j) : ℂ) * F j x * T j x) =
      ∑ j, ∫ x, (a x (p j) (q j) : ℂ) * F j x * T j x := by
  have hint (j : Fin d) : Integrable
      (fun x => (a x (p j) (q j) : ℂ) * F j x * T j x) volume :=
    ((ha (p j) (q j)).mul (r := 2) (Lp.memLp (F j))).integrable_mul
      (Lp.memLp (T j))
  rw [integral_finsetSum _ (fun j _ => hint j)]


/-- Uniform coercive estimate for arbitrary signed forward quotient orders. -/
theorem u4Higher_forward_quotient_energy_uniform {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f q : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f (J []))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f (fun k => D k []))
    (hqQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N) (l : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hM : ∀ k ≤ (steps ++ [(l, h)]).length, M k ≤ A)
    (hQ : ∀ k, (Q k : Vec d → ℂ) =ᵐ[volume] u4HigherDifferences
      ((steps ++ [(l, h)]).map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (D k [])) :
    (∑ j, ‖Q j‖ ^ 2) ≤
      (Λ * (2 * (‖J ((steps.map Prod.fst).reverse)‖ + ‖ζ‖ *
        ((d : ℝ) * (Λ * B + (2 : ℝ) ^ steps.length * A * B))) +
        (d : ℝ) * ((2 : ℝ) ^ (steps ++ [(l, h)]).length * A * B))) ^ 2 * (d : ℝ) := by
  classical
  have hnz' : ∀ p ∈ steps ++ [(l, h)], p.2 ≠ 0 := by
    intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hnz p hp
    · exact hh
  have ho' : (steps ++ [(l, h)]).length ≤ N + 1 := by simp; omega
  obtain ⟨r, T, hr, hT, he⟩ := u4Higher_forward_generator_energy hΛ hell hsmooth
    D hD A B hA hB hDB hfg hG hqQ (steps ++ [(l, h)]) hnz' ho' hM hQ
  have hf := u4Higher_backward_forcing_gradient_bound J hJ steps hnz horder l h hh hqQ hr
  have hm : ∀ k ≤ steps.length, M k ≤ A := by
    intro k hk
    apply hM k
    simp only [List.length_append, List.length_singleton]
    omega
  have hd := u4Higher_coefficient_backward_sum_gradient_bound hΛ hell hsmooth D hD
    A B hA hB hDB steps hnz horder hm id (fun _ => i) l h hh hqQ hr
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hsum : (∫ x, (∑ j, (ω.1 x j i : ℂ) * D j [] x) * r x) =
      ∑ j, ∫ x, (ω.1 x j i : ℂ) * D j [] x * r x := by
    calc
      _ = ∫ x, ∑ j, (ω.1 x j i : ℂ) * D j [] x * r x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Finset.sum_mul]
      _ = _ := u4Higher_drift_integral_sum ha (fun j => D j []) (fun _ => r) id (fun _ => i)
  rw [hsum] at he
  have hsingle : ‖Q l‖ ≤ ∑ j, ‖Q j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (Q j)) (Finset.mem_univ l)
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hc : 0 ≤ (d : ℝ) * (Λ * B + (2 : ℝ) ^ steps.length * A * B) := by positivity
  have hf' := hf.trans (mul_le_mul_of_nonneg_left hsingle (norm_nonneg _))
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hsingle hc)
  have hd'' := mul_le_mul_of_nonneg_left hd' (norm_nonneg ζ)
  simp only [id_eq] at hd''
  let C : ℝ := 2 * (‖J ((steps.map Prod.fst).reverse)‖ + ‖ζ‖ *
        ((d : ℝ) * (Λ * B + (2 : ℝ) ^ steps.length * A * B))) +
        (d : ℝ) * ((2 : ℝ) ^ (steps ++ [(l, h)]).length * A * B)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he' : Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤ C * (∑ j, ‖Q j‖) := by
    dsimp [C]
    nlinarith only [he, hf', hd'']
  exact u4h3_finite_energy_absorption Q hΛ hC he'


/-- Uniform coercive estimate for arbitrary signed transpose quotient orders. -/
theorem u4Higher_transpose_quotient_energy_uniform {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {q : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length < N + 1 →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B E : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hFB : ∀ path, path.length ≤ N + 1 → ‖F path‖ ≤ E)
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J []))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) (F []) (fun k => D k []))
    (hqQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (steps : List (Fin d × ℝ)) (hnz : ∀ p ∈ steps, p.2 ≠ 0)
    (horder : steps.length ≤ N) (l : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hM : ∀ k ≤ (steps ++ [(l, h)]).length, M k ≤ A)
    (hQ : ∀ k, (Q k : Vec d → ℂ) =ᵐ[volume] u4HigherDifferences
      ((steps ++ [(l, h)]).map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (D k [])) :
    (∑ j, ‖Q j‖ ^ 2) ≤
      (Λ * (2 * (‖J ((steps.map Prod.fst).reverse)‖ + ‖ζ‖ *
        (Λ * E + (2 : ℝ) ^ (steps ++ [(l, h)]).length * A * E)) +
        (d : ℝ) * ((2 : ℝ) ^ (steps ++ [(l, h)]).length * A * B))) ^ 2 * (d : ℝ) := by
  classical
  have hnz' : ∀ p ∈ steps ++ [(l, h)], p.2 ≠ 0 := by
    intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hnz p hp
    · exact hh
  have ho' : (steps ++ [(l, h)]).length ≤ N + 1 := by simp; omega
  obtain ⟨r, T, hr, hT, he⟩ := u4Higher_transpose_generator_energy hΛ hell hsmooth
    D hD A B hA hB hDB hfg hG hqQ (steps ++ [(l, h)]) hnz' ho' hM hQ
  have hf := u4Higher_backward_forcing_gradient_bound J hJ steps hnz horder l h hh hqQ hr
  have hd := u4Higher_coefficient_backward_transpose_sum_bound hΛ hell hsmooth F hF
    A E hA hE hFB (steps ++ [(l, h)]) hnz' ho' hM i Q T hT
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hsum : (∫ x, F [] x * (∑ j, (ω.1 x j i : ℂ) * T j x)) =
      ∑ j, ∫ x, (ω.1 x j i : ℂ) * F [] x * T j x := by
    calc
      _ = ∫ x, ∑ j, (ω.1 x j i : ℂ) * F [] x * T j x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := u4Higher_drift_integral_sum ha (fun _ => F []) T id (fun _ => i)
  rw [hsum] at he
  have hsingle : ‖Q l‖ ≤ ∑ j, ‖Q j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (Q j)) (Finset.mem_univ l)
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hf' := hf.trans (mul_le_mul_of_nonneg_left hsingle (norm_nonneg _))
  have hd' := mul_le_mul_of_nonneg_left hd (norm_nonneg ζ)
  let C : ℝ := 2 * (‖J ((steps.map Prod.fst).reverse)‖ + ‖ζ‖ *
        (Λ * E + (2 : ℝ) ^ (steps ++ [(l, h)]).length * A * E)) +
        (d : ℝ) * ((2 : ℝ) ^ (steps ++ [(l, h)]).length * A * B)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he' : Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤ C * (∑ j, ‖Q j‖) := by
    dsimp [C]
    nlinarith only [he, hf', hd']
  exact u4h3_finite_energy_absorption Q hΛ hC he'


/-- Uniform gradient energy of actual coordinate quotients yields the next
physical weak derivative, with its explicit energy bound. -/
theorem u4Higher_coordinate_derivative_of_quotient_energy {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) (i : Fin d)
    (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ (h : ℝ), 0 < |h| → |h| ≤ 1 →
      ∀ (q : Lp ℂ 2 (volume : Measure (Vec d)))
        (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q →
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector i) - f x) / (h : ℂ)) →
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector i) - G j x) / (h : ℂ))) →
      (∑ j, ‖Q j‖ ^ 2) ≤ C) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (G i) H ∧
      (∑ j, ‖H j‖ ^ 2) ≤ ‖G i‖ ^ 2 + C := by
  classical
  let s := Blueprint.C3SublinearC1.mollifierScale
  have hs := c24_quotient_scale_properties
  let R : ℝ := Real.sqrt (‖G i‖ ^ 2 + C)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = ‖G i‖ ^ 2 + C := by
    dsimp [R]
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _) hC)
  have hex : ∀ n, ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + s n • unitVector i) - f x) / (s n : ℂ)) ∧
      ‖q‖ ^ 2 + (∑ j, ‖Q j‖ ^ 2) ≤ R ^ 2 := by
    intro n
    obtain ⟨q, Q, hqG, hq, hQ⟩ :=
      c18_physical_H1_difference_quotient hG (-(s n • unitVector i)) (s n)
    have hq' : (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + s n • unitVector i) - f x) / (s n : ℂ)) := by
      simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using hq
    have hQ' (j : Fin d) : (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + s n • unitVector i) - G j x) / (s n : ℂ)) := by
      simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using hQ j
    have hn : s n ≠ 0 := abs_pos.mp (hs.1 n).1
    have hb := c18_physical_H1_coordinate_difference_quotient_bound hG i (s n) hn
    rw [← eLpNorm_congr_ae hq', ← Lp.norm_def] at hb
    have he := henergy (s n) (hs.1 n).1 (hs.1 n).2 q Q hqG hq' hQ'
    refine ⟨q, Q, hqG, hq', ?_⟩
    rw [hR2]
    nlinarith [norm_nonneg q, norm_nonneg (G i)]
  choose q Q hgraph hq hbound using hex
  obtain ⟨H, hH, hboundH⟩ :=
    c24_physical_H1_of_actual_quotients f G i hG hs.2 q Q R hR hq hbound hgraph
  exact ⟨H, hH, by simpa only [hR2] using hboundH⟩

/-- Strong L² limits of uniformly bounded physical H¹ graphs retain the
same gradient energy bound. -/
theorem u4Higher_H1_of_strong_limit {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (q : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ∑ j, ‖Q n j‖ ^ 2 ≤ C)
    (hgraph : ∀ n, IsPhysicalH1Graph volume (Or.inl rfl) (q n) (Q n))
    (hlimit : Filter.Tendsto q Filter.atTop (𝓝 u)) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) u H ∧ ∑ j, ‖H j‖ ^ 2 ≤ C := by
  let R := Real.sqrt C
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = C := Real.sq_sqrt hC
  have hweak (v : Lp ℂ 2 (volume : Measure (Vec d))) :
      Filter.Tendsto (fun n => inner ℝ (q n) v) Filter.atTop (𝓝 (inner ℝ u v)) :=
    ((continuous_id.inner (𝕜 := ℝ) continuous_const).tendsto u).comp hlimit
  obtain ⟨H, hH, hE⟩ := c24_physical_H1_of_bounded_weak_quotients u q Q R hR
    (fun n => by simpa only [hR2] using hbound n) hgraph hweak
  exact ⟨H, hH, by simpa only [hR2] using hE⟩

/-- Iterated scaled differences acting on actual L² classes. -/
def u4HigherLpDifferences {d : ℕ} : List (Vec d × ℂ) →
    Lp ℂ 2 (volume : Measure (Vec d)) → Lp ℂ 2 (volume : Measure (Vec d))
  | [], f => f
  | (z, c) :: rest, f => u4HigherLpDifferences rest
      (c • (Lp.compMeasurePreserving (fun x : Vec d => x + z)
        (measurePreserving_add_right (volume : Measure (Vec d)) z) f - f))

/-- Fixed iterated spatial differences are continuous on L². -/
theorem u4HigherLpDifferences_continuous {d : ℕ} (steps : List (Vec d × ℂ)) :
    Continuous (u4HigherLpDifferences steps : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d))) := by
  induction steps with
  | nil => exact continuous_id
  | cons p rest ih =>
      rcases p with ⟨z, c⟩
      have ht : Continuous (fun f : Lp ℂ 2 (volume : Measure (Vec d)) =>
          Lp.compMeasurePreserving (fun x : Vec d => x + z)
            (measurePreserving_add_right (volume : Measure (Vec d)) z) f) :=
        (Lp.compMeasurePreservingₗᵢ ℂ (fun x : Vec d => x + z)
          (measurePreserving_add_right (volume : Measure (Vec d)) z)).continuous
      exact ih.comp ((ht.sub continuous_id).const_smul c)

/-- The L² operator has the same representative as the pointwise iterated difference. -/
theorem u4HigherLpDifferences_ae {d : ℕ} (steps : List (Vec d × ℂ))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    (u4HigherLpDifferences steps f : Vec d → ℂ) =ᵐ[volume]
      u4HigherDifferences steps f := by
  induction steps generalizing f with
  | nil => exact Filter.EventuallyEq.rfl
  | cons p rest ih =>
      rcases p with ⟨z, c⟩
      let t := Lp.compMeasurePreserving (fun x : Vec d => x + z)
        (measurePreserving_add_right (volume : Measure (Vec d)) z) f
      let q := c • (t - f)
      have hq : (q : Vec d → ℂ) =ᵐ[volume] u4HigherDifference z c f := by
        filter_upwards [Lp.coeFn_smul c (t - f), Lp.coeFn_sub t f,
          Lp.coeFn_compMeasurePreserving f
            (measurePreserving_add_right (volume : Measure (Vec d)) z)] with x hs hd ht
        simp only [q, hs, Pi.smul_apply, hd, Pi.sub_apply, t, Function.comp_apply,
          ht, smul_eq_mul, u4HigherDifference]
      exact (ih q).trans (u4HigherDifferences_ae rest hq)

/-- Remove the first signed quotient in a uniformly energy-bounded family,
retaining every later fixed difference and the same gradient bound. -/
theorem u4Higher_remove_first_quotient {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) (i : Fin d)
    (steps : List (Vec d × ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ (h : ℝ), 0 < |h| → |h| ≤ 1 →
      ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
        (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        u4HigherDifferences ((h • unitVector i, (h : ℂ)⁻¹) :: steps) f ∧
      (∑ j, ‖Q j‖ ^ 2) ≤ C) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (u4HigherLpDifferences steps (G i)) H ∧
      (∑ j, ‖H j‖ ^ 2) ≤ C := by
  classical
  let s := Blueprint.C3SublinearC1.mollifierScale
  have hs := c24_quotient_scale_properties
  have hex := fun n => henergy (s n) (hs.1 n).1 (hs.1 n).2
  choose q Q hgraph hq hbound using hex
  let v : ℕ → Lp ℂ 2 (volume : Measure (Vec d)) := fun n =>
    (s n : ℂ)⁻¹ • (Lp.compMeasurePreserving
      (fun x : Vec d => x + s n • unitVector i)
      (measurePreserving_add_right (volume : Measure (Vec d)) (s n • unitVector i)) f - f)
  have heq (n : ℕ) : q n = u4HigherLpDifferences steps (v n) := by
    apply Lp.ext
    have hv : (v n : Vec d → ℂ) =ᵐ[volume]
        u4HigherDifference (s n • unitVector i) (s n : ℂ)⁻¹ f := by
      simpa only [v, u4HigherLpDifferences, u4HigherDifferences] using
        u4HigherLpDifferences_ae [(s n • unitVector i, (s n : ℂ)⁻¹)] f
    exact (hq n).trans ((u4HigherLpDifferences_ae steps (v n)).trans
      (u4HigherDifferences_ae steps hv)).symm
  have hvlim : Filter.Tendsto v Filter.atTop (𝓝 (G i)) := by
    exact (c18_physical_H1_coordinate_difference_quotient_tendsto hG i).comp hs.2
  have hlim : Filter.Tendsto q Filter.atTop (𝓝 (u4HigherLpDifferences steps (G i))) := by
    have hh := ((u4HigherLpDifferences_continuous steps).tendsto (G i)).comp hvlim
    exact hh.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm))
  exact u4Higher_H1_of_strong_limit _ q Q C hC hbound hgraph hlim


/-- Iteratively remove signed coordinate quotients while preserving their
uniform gradient energy bound. -/
theorem u4Higher_remove_coordinate_quotients {d : ℕ}
    (dirs : List (Fin d))
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length < dirs.length →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun i => F (path ++ [i])))
    (steps : List (Vec d × ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ pre : List (Fin d × ℝ), pre.map Prod.fst = dirs →
      (∀ p ∈ pre, 0 < |p.2| ∧ |p.2| ≤ 1) →
      ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
        (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        u4HigherDifferences (pre.map (fun p =>
          (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)) ++ steps) (F []) ∧
      (∑ j, ‖Q j‖ ^ 2) ≤ C) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (u4HigherLpDifferences steps (F dirs)) H ∧
      (∑ j, ‖H j‖ ^ 2) ≤ C := by
  induction dirs generalizing F with
  | nil =>
      obtain ⟨q, Q, hqG, hq, hQ⟩ := henergy [] rfl (by simp)
      have heq : q = u4HigherLpDifferences steps (F []) := by
        apply Lp.ext
        exact hq.trans (u4HigherLpDifferences_ae steps (F [])).symm
      exact ⟨Q, heq ▸ hqG, hQ⟩
  | cons i rest ih =>
      let F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) :=
        fun path => F (i :: path)
      have hF' : ∀ path, path.length < rest.length →
          IsPhysicalH1Graph volume (Or.inl rfl) (F' path)
            (fun j => F' (path ++ [j])) := by
        intro path hp
        simpa only [F', List.cons_append, List.length_cons] using
          hF (i :: path) (by simp only [List.length_cons]; omega)
      have he' : ∀ pre : List (Fin d × ℝ), pre.map Prod.fst = rest →
          (∀ p ∈ pre, 0 < |p.2| ∧ |p.2| ≤ 1) →
          ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
            (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
          (q : Vec d → ℂ) =ᵐ[volume]
            u4HigherDifferences (pre.map (fun p =>
              (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)) ++ steps) (F' []) ∧
          (∑ j, ‖Q j‖ ^ 2) ≤ C := by
        intro pre hp hb
        have hg : IsPhysicalH1Graph volume (Or.inl rfl) (F []) (fun j => F [j]) := by
          simpa using hF [] (by simp)
        let later := pre.map (fun p : Fin d × ℝ =>
          (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)) ++ steps
        have hu : ∀ h : ℝ, 0 < |h| → |h| ≤ 1 →
            ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
              (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
            IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
            (q : Vec d → ℂ) =ᵐ[volume]
              u4HigherDifferences ((h • unitVector i, (h : ℂ)⁻¹) :: later) (F []) ∧
            (∑ j, ‖Q j‖ ^ 2) ≤ C := by
          intro h hh hh1
          simpa only [List.map_cons, List.cons_append, Prod.fst] using
            henergy ((i, h) :: pre) (by simp [hp]) (by
              intro p hp'
              simp only [List.mem_cons] at hp'
              rcases hp' with rfl | hp'
              · exact ⟨hh, hh1⟩
              · exact hb p hp')
        obtain ⟨H, hH, hHbound⟩ :=
          u4Higher_remove_first_quotient (F []) (fun j => F [j]) hg i later C hC hu
        exact ⟨_, H, hH, u4HigherLpDifferences_ae later (F [i]), hHbound⟩
      simpa only [F'] using ih F' hF' he'


/-- Every signed quotient of the actual forward generator graph has an H¹
representative with an energy bound independent of its step sizes. -/
theorem u4Higher_forward_quotient_graph_uniform {d N n : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hJB : ∀ path, path.length = n → ‖J path‖ ≤ K)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f (J []))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f (fun k => D k []))
    (steps : List (Fin d × ℝ)) (hlen : steps.length = n) (hn : n ≤ N)
    (hnz : ∀ p ∈ steps, p.2 ≠ 0) (l : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hM : ∀ k ≤ n + 1, M k ≤ A) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume] u4HigherDifferences
        ((steps ++ [(l, h)]).map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) f ∧
      (∑ j, ‖Q j‖ ^ 2) ≤
        (Λ * (2 * (K + ‖ζ‖ * ((d : ℝ) * (Λ * B + (2 : ℝ) ^ n * A * B))) +
          (d : ℝ) * ((2 : ℝ) ^ (n + 1) * A * B))) ^ 2 * (d : ℝ) := by
  classical
  let all := steps ++ [(l, h)]
  obtain ⟨q, Q, hqQ, hq, hQ⟩ := u4Higher_forward_H1_quotients
    (all.map (fun p => (p.2 • unitVector p.1, p.2))) hG
  simp only [List.map_map, Function.comp_def] at hq hQ
  have hm : ∀ k ≤ (steps ++ [(l, h)]).length, M k ≤ A := by
    simpa only [List.length_append, List.length_singleton, hlen] using hM
  have he := u4Higher_forward_quotient_energy_uniform hΛ hell hsmooth D hD J hJ
    A B hA hB hDB hfg hG hqQ steps hnz (by omega) l h hh hm hQ
  have hj : ‖J ((steps.map Prod.fst).reverse)‖ ≤ K := hJB _ (by simp [hlen])
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have he' :
      (Λ * (2 * (‖J ((steps.map Prod.fst).reverse)‖ + ‖ζ‖ *
        ((d : ℝ) * (Λ * B + (2 : ℝ) ^ steps.length * A * B))) +
        (d : ℝ) * ((2 : ℝ) ^ (steps ++ [(l, h)]).length * A * B))) ^ 2 * (d : ℝ) ≤
      (Λ * (2 * (K + ‖ζ‖ * ((d : ℝ) * (Λ * B + (2 : ℝ) ^ n * A * B))) +
        (d : ℝ) * ((2 : ℝ) ^ (n + 1) * A * B))) ^ 2 * (d : ℝ) := by
    simp only [List.length_append, List.length_singleton, hlen]
    gcongr
  exact ⟨q, Q, hqQ, hq, he.trans he'⟩


/-- Every signed quotient of the actual transpose generator graph has an H¹
representative with an energy bound independent of its step sizes. -/
theorem u4Higher_transpose_quotient_graph_uniform {d N n : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length < N + 1 →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B E K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hFB : ∀ path, path.length ≤ N + 1 → ‖F path‖ ≤ E)
    (hJB : ∀ path, path.length = n → ‖J path‖ ≤ K)
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J []))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) (F []) (fun k => D k []))
    (steps : List (Fin d × ℝ)) (hlen : steps.length = n) (hn : n ≤ N)
    (hnz : ∀ p ∈ steps, p.2 ≠ 0) (l : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hM : ∀ k ≤ n + 1, M k ≤ A) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume] u4HigherDifferences
        ((steps ++ [(l, h)]).map (fun p => (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (F []) ∧
      (∑ j, ‖Q j‖ ^ 2) ≤
        (Λ * (2 * (K + ‖ζ‖ * (Λ * E + (2 : ℝ) ^ (n + 1) * A * E)) +
          (d : ℝ) * ((2 : ℝ) ^ (n + 1) * A * B))) ^ 2 * (d : ℝ) := by
  classical
  let all := steps ++ [(l, h)]
  obtain ⟨q, Q, hqQ, hq, hQ⟩ := u4Higher_forward_H1_quotients
    (all.map (fun p => (p.2 • unitVector p.1, p.2))) hG
  simp only [List.map_map, Function.comp_def] at hq hQ
  have hm : ∀ k ≤ (steps ++ [(l, h)]).length, M k ≤ A := by
    simpa only [List.length_append, List.length_singleton, hlen] using hM
  have he := u4Higher_transpose_quotient_energy_uniform hΛ hell hsmooth D hD F J hF hJ
    A B E hA hB hE hDB hFB hfg hG hqQ steps hnz (by omega) l h hh hm hQ
  have hj : ‖J ((steps.map Prod.fst).reverse)‖ ≤ K := hJB _ (by simp [hlen])
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have he' :
      (Λ * (2 * (‖J ((steps.map Prod.fst).reverse)‖ + ‖ζ‖ *
        (Λ * E + (2 : ℝ) ^ (steps ++ [(l, h)]).length * A * E)) +
        (d : ℝ) * ((2 : ℝ) ^ (steps ++ [(l, h)]).length * A * B))) ^ 2 * (d : ℝ) ≤
      (Λ * (2 * (K + ‖ζ‖ * (Λ * E + (2 : ℝ) ^ (n + 1) * A * E)) +
        (d : ℝ) * ((2 : ℝ) ^ (n + 1) * A * B))) ^ 2 * (d : ℝ) := by
    simp only [List.length_append, List.length_singleton, hlen]
    gcongr
  exact ⟨q, Q, hqQ, hq, he.trans he'⟩


/-- Uniform energy of one additional signed quotient extends an existing
weak-derivative chain by one coordinate, preserving that energy bound. -/
theorem u4Higher_extend_chain_from_quotient_graphs {d : ℕ}
    (dirs : List (Fin d))
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length ≤ dirs.length →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ (pre : List (Fin d × ℝ)), pre.map Prod.fst = dirs →
      (∀ p ∈ pre, 0 < |p.2| ∧ |p.2| ≤ 1) →
      ∀ (l : Fin d) (h : ℝ), 0 < |h| → |h| ≤ 1 →
      ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
        (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        u4HigherDifferences ((pre ++ [(l, h)]).map (fun p =>
          (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹))) (F []) ∧
      (∑ j, ‖Q j‖ ^ 2) ≤ C)
    (l : Fin d) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (F (dirs ++ [l])) H ∧
      (∑ j, ‖H j‖ ^ 2) ≤ C := by
  classical
  have hlast := hF dirs (le_refl _)
  have hu : ∀ h : ℝ, 0 < |h| → |h| ≤ 1 →
      ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
        (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        u4HigherDifferences [(h • unitVector l, (h : ℂ)⁻¹)] (F dirs) ∧
      (∑ j, ‖Q j‖ ^ 2) ≤ C := by
    intro h hh hh1
    let steps : List (Vec d × ℂ) := [(h • unitVector l, (h : ℂ)⁻¹)]
    have he : ∀ pre : List (Fin d × ℝ), pre.map Prod.fst = dirs →
        (∀ p ∈ pre, 0 < |p.2| ∧ |p.2| ≤ 1) →
        ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
          (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
        (q : Vec d → ℂ) =ᵐ[volume]
          u4HigherDifferences (pre.map (fun p =>
            (p.2 • unitVector p.1, (p.2 : ℂ)⁻¹)) ++ steps) (F []) ∧
        (∑ j, ‖Q j‖ ^ 2) ≤ C := by
      intro pre hp hb
      simpa only [List.map_append, List.map_singleton, steps] using henergy pre hp hb l h hh hh1
    obtain ⟨H, hH, hbound⟩ := u4Higher_remove_coordinate_quotients dirs F
      (fun path hp => hF path (le_of_lt hp)) steps C hC he
    exact ⟨_, H, hH, u4HigherLpDifferences_ae steps (F dirs), hbound⟩
  simpa only [u4HigherLpDifferences] using
    u4Higher_remove_first_quotient (F dirs) (fun j => F (dirs ++ [j])) hlast l [] C hC hu


/-- Quantitative extension of a weak-derivative chain for the actual forward
generator graph. -/
theorem u4Higher_forward_extend_chain {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (dirs : List (Fin d)) (hn : dirs.length ≤ N)
    (hF : ∀ path, path.length ≤ dirs.length →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hJB : ∀ path, path.length = dirs.length → ‖J path‖ ≤ K)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ (F []) (J []))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) (F []) (fun k => D k []))
    (hM : ∀ k ≤ dirs.length + 1, M k ≤ A) (l : Fin d) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (F (dirs ++ [l])) H ∧
      (∑ j, ‖H j‖ ^ 2) ≤
        (Λ * (2 * (K + ‖ζ‖ * ((d : ℝ) * (Λ * B + (2 : ℝ) ^ dirs.length * A * B))) +
          (d : ℝ) * ((2 : ℝ) ^ (dirs.length + 1) * A * B))) ^ 2 * (d : ℝ) := by
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  apply u4Higher_extend_chain_from_quotient_graphs dirs F hF _ (by positivity) ?_ l
  intro pre hp hb k h hh hh1
  have hlen : pre.length = dirs.length := by
    simpa only [List.length_map] using congrArg List.length hp
  have hnz : ∀ p ∈ pre, p.2 ≠ 0 := by
    intro p hp'
    exact abs_pos.mp (hb p hp').1
  exact u4Higher_forward_quotient_graph_uniform hΛ hell hsmooth D hD J hJ
    A B K hA hB hDB hJB hfg hG pre hlen hn hnz k h (abs_pos.mp hh) hM


/-- Quantitative extension of a weak-derivative chain for the actual transpose
generator graph. -/
theorem u4Higher_transpose_extend_chain {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (dirs : List (Fin d)) (hn : dirs.length ≤ N)
    (hF : ∀ path, path.length < N + 1 →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B E K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hFB : ∀ path, path.length ≤ N + 1 → ‖F path‖ ≤ E)
    (hJB : ∀ path, path.length = dirs.length → ‖J path‖ ≤ K)
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J []))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) (F []) (fun k => D k []))
    (hM : ∀ k ≤ dirs.length + 1, M k ≤ A) (l : Fin d) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (F (dirs ++ [l])) H ∧
      (∑ j, ‖H j‖ ^ 2) ≤
        (Λ * (2 * (K + ‖ζ‖ * (Λ * E + (2 : ℝ) ^ (dirs.length + 1) * A * E)) +
          (d : ℝ) * ((2 : ℝ) ^ (dirs.length + 1) * A * B))) ^ 2 * (d : ℝ) := by
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  apply u4Higher_extend_chain_from_quotient_graphs dirs F
    (fun path hp => hF path (by omega)) _ (by positivity) ?_ l
  intro pre hp hb k h hh hh1
  have hlen : pre.length = dirs.length := by
    simpa only [List.length_map] using congrArg List.length hp
  have hnz : ∀ p ∈ pre, p.2 ≠ 0 := by
    intro p hp'
    exact abs_pos.mp (hb p hp').1
  exact u4Higher_transpose_quotient_graph_uniform hΛ hell hsmooth D hD F J hF hJ
    A B E K hA hB hE hDB hFB hJB hfg hG pre hlen hn hnz k h (abs_pos.mp hh) hM


/-- Assemble compatible H¹ graphs on one full derivative layer into a single
extended derivative family, preserving all earlier entries and the energy bound. -/
theorem u4Higher_assemble_derivative_layer {d N : ℕ}
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (C : ℝ)
    (hnext : ∀ path, path.length = N →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (F path) H ∧
        (∑ j, ‖H j‖ ^ 2) ≤ C) :
    ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ N → F' path = F path) ∧
      (∀ path, path.length < N + 1 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) ∧
      (∀ path, path.length = N → ∑ j, ‖F' (path ++ [j])‖ ^ 2 ≤ C) := by
  classical
  let H : List (Fin d) → Fin d → Lp ℂ 2 (volume : Measure (Vec d)) := fun path =>
    if hp : path.length = N then Classical.choose (hnext path hp) else fun _ => 0
  have hH (path : List (Fin d)) (hp : path.length = N) :
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (H path) ∧
        (∑ j, ‖H path j‖ ^ 2) ≤ C := by
    simpa only [H, dif_pos hp] using Classical.choose_spec (hnext path hp)
  let F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) := fun path =>
    if path.length ≤ N then F path else
      match path.reverse with
      | [] => 0
      | j :: rest => H rest.reverse j
  have hold (path : List (Fin d)) (hp : path.length ≤ N) : F' path = F path := by
    simp only [F', if_pos hp]
  have hnew (path : List (Fin d)) (hp : path.length = N) (j : Fin d) :
      F' (path ++ [j]) = H path j := by
    have hlen : ¬ (path ++ [j]).length ≤ N := by simp [hp]
    simp only [F', if_neg hlen, List.reverse_append, List.reverse_singleton,
      List.cons_append, List.nil_append, List.reverse_reverse]
  refine ⟨F', hold, ?_, ?_⟩
  · intro path hp
    by_cases hn : path.length = N
    · rw [hold path (by omega)]
      simpa only [hnew path hn] using (hH path hn).1
    · have hp' : path.length < N := by omega
      have heq : (fun j => F' (path ++ [j])) = (fun j => F (path ++ [j])) := by
        funext j
        apply hold
        simp only [List.length_append, List.length_singleton]
        omega
      rw [hold path (by omega), heq]
      exact hF path hp'
  · intro path hp
    simpa only [hnew path hp] using (hH path hp).2


/-- Extend an entire derivative layer for the actual forward generator,
with the same explicit coercive bound at every path in the new layer. -/
theorem u4Higher_forward_extend_derivative_layer {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length ≤ N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hJB : ∀ path, path.length = N → ‖J path‖ ≤ K)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ (F []) (J []))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) (F []) (fun k => D k []))
    (hM : ∀ k ≤ N + 1, M k ≤ A) :
    ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ N + 1 → F' path = F path) ∧
      (∀ path, path.length < N + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) ∧
      (∀ path, path.length = N + 1 → ∑ j, ‖F' (path ++ [j])‖ ^ 2 ≤
        (Λ * (2 * (K + ‖ζ‖ * ((d : ℝ) * (Λ * B + (2 : ℝ) ^ N * A * B))) +
          (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * B))) ^ 2 * (d : ℝ)) := by
  apply u4Higher_assemble_derivative_layer F
    (fun path hp => hF path (by omega)) _ ?_
  intro path hp
  cases hr : path.reverse with
  | nil =>
      have heq : path = [] := by
        have hh := congrArg List.reverse hr
        simpa using hh
      simp [heq] at hp
  | cons l rest =>
      have heq : path = rest.reverse ++ [l] := by
        have hh := congrArg List.reverse hr
        simpa using hh
      have hlen : rest.reverse.length = N := by
        rw [heq] at hp
        simp only [List.length_append, List.length_singleton] at hp
        omega
      rw [heq]
      simpa only [hlen] using u4Higher_forward_extend_chain hΛ hell hsmooth D hD F J
        rest.reverse (by omega) (fun path hp => hF path (by omega)) hJ
        A B K hA hB hDB (by simpa only [hlen] using hJB) hfg hG
        (by simpa only [hlen] using hM) l


/-- Extend an entire derivative layer for the actual transpose generator,
with the same explicit coercive bound at every path in the new layer. -/
theorem u4Higher_transpose_extend_derivative_layer {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])))
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length < N + 1 →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B E K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B)
    (hFB : ∀ path, path.length ≤ N + 1 → ‖F path‖ ≤ E)
    (hJB : ∀ path, path.length = N → ‖J path‖ ≤ K)
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J []))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) (F []) (fun k => D k []))
    (hM : ∀ k ≤ N + 1, M k ≤ A) :
    ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ N + 1 → F' path = F path) ∧
      (∀ path, path.length < N + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) ∧
      (∀ path, path.length = N + 1 → ∑ j, ‖F' (path ++ [j])‖ ^ 2 ≤
        (Λ * (2 * (K + ‖ζ‖ * (Λ * E + (2 : ℝ) ^ (N + 1) * A * E)) +
          (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * B))) ^ 2 * (d : ℝ)) := by
  apply u4Higher_assemble_derivative_layer F hF _ ?_
  intro path hp
  cases hr : path.reverse with
  | nil =>
      have heq : path = [] := by
        have hh := congrArg List.reverse hr
        simpa using hh
      simp [heq] at hp
  | cons l rest =>
      have heq : path = rest.reverse ++ [l] := by
        have hh := congrArg List.reverse hr
        simpa using hh
      have hlen : rest.reverse.length = N := by
        rw [heq] at hp
        simp only [List.length_append, List.length_singleton] at hp
        omega
      rw [heq]
      simpa only [hlen] using u4Higher_transpose_extend_chain hΛ hell hsmooth D hD F J
        rest.reverse (by omega) hF hJ A B E K hA hB hE hDB hFB
        (by simpa only [hlen] using hJB) hfg hG (by simpa only [hlen] using hM) l


/-- A uniform energy bound on the newest layer yields a uniform bound on
individual derivatives, while retaining the bound on all preceding layers. -/
theorem u4Higher_derivative_layer_norm_bound {d N : ℕ}
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (B C : ℝ) (hC : 0 ≤ C)
    (hB : ∀ path, path.length ≤ N → ‖F path‖ ≤ B)
    (henergy : ∀ path, path.length = N →
      ∑ j, ‖F (path ++ [j])‖ ^ 2 ≤ C) :
    ∀ path, path.length ≤ N + 1 → ‖F path‖ ≤ max B (Real.sqrt C) := by
  classical
  intro path hp
  by_cases hold : path.length ≤ N
  · exact le_trans (hB path hold) (le_max_left _ _)
  · have hlen : path.length = N + 1 := by omega
    cases hr : path.reverse with
    | nil =>
        have heq : path = [] := by
          have hh := congrArg List.reverse hr
          simpa using hh
        simp [heq] at hlen
    | cons l rest =>
        have heq : path = rest.reverse ++ [l] := by
          have hh := congrArg List.reverse hr
          simpa using hh
        have hrest : rest.reverse.length = N := by
          rw [heq] at hlen
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        have hsingle : ‖F (rest.reverse ++ [l])‖ ^ 2 ≤
            ∑ j, ‖F (rest.reverse ++ [j])‖ ^ 2 := by
          exact Finset.single_le_sum (fun j _ => sq_nonneg ‖F (rest.reverse ++ [j])‖)
            (Finset.mem_univ l)
        have hsq : ‖F (rest.reverse ++ [l])‖ ^ 2 ≤ C :=
          le_trans hsingle (henergy rest.reverse hrest)
        have hsqrt : ‖F (rest.reverse ++ [l])‖ ≤ Real.sqrt C := by
          nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C,
            norm_nonneg (F (rest.reverse ++ [l]))]
        rw [heq]
        exact le_trans hsqrt (le_max_right _ _)


/-- One forward-generator regularity step, stated entirely in terms of the
existing derivative families and their uniform bounds. -/
theorem u4Higher_forward_bounded_derivative_step {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length ≤ N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hFB : ∀ path, path.length ≤ N + 1 → ‖F path‖ ≤ B)
    (hJB : ∀ path, path.length = N → ‖J path‖ ≤ K)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ (F []) (J []))
    (hM : ∀ k ≤ N + 1, M k ≤ A) :
    ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ N + 1 → F' path = F path) ∧
      (∀ path, path.length < N + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) ∧
      (∀ path, path.length ≤ N + 2 → ‖F' path‖ ≤
        max B (Real.sqrt ((Λ * (2 * (K + ‖ζ‖ *
          ((d : ℝ) * (Λ * B + (2 : ℝ) ^ N * A * B))) +
          (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * B))) ^ 2 * (d : ℝ)))) := by
  let D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun k path => F (k :: path)
  have hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])) := by
    intro k path hp
    simpa only [D, List.cons_append] using hF (k :: path) (by simp only [List.length_cons]; omega)
  have hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B := by
    intro k path hp
    exact hFB (k :: path) (by simp only [List.length_cons]; omega)
  have hG : IsPhysicalH1Graph volume (Or.inl rfl) (F []) (fun k => D k []) := by
    simpa [D] using hF [] (by simp)
  obtain ⟨F', hold, hgraph, henergy⟩ :=
    u4Higher_forward_extend_derivative_layer hΛ hell hsmooth D hD F J hF hJ
      A B K hA hB hDB hJB hfg hG hM
  refine ⟨F', hold, hgraph, ?_⟩
  have hC : 0 ≤ (Λ * (2 * (K + ‖ζ‖ *
      ((d : ℝ) * (Λ * B + (2 : ℝ) ^ N * A * B))) +
      (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * B))) ^ 2 * (d : ℝ) :=
    mul_nonneg (sq_nonneg _) (Nat.cast_nonneg d)
  apply u4Higher_derivative_layer_norm_bound F' B _ hC ?_ henergy
  intro path hp
  rw [hold path hp]
  exact hFB path hp


/-- One transpose-generator regularity step, stated entirely in terms of the
existing derivative families and their uniform bounds. -/
theorem u4Higher_transpose_bounded_derivative_step {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length ≤ N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hFB : ∀ path, path.length ≤ N + 1 → ‖F path‖ ≤ B)
    (hJB : ∀ path, path.length = N → ‖J path‖ ≤ K)
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J []))
    (hM : ∀ k ≤ N + 1, M k ≤ A) :
    ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ N + 1 → F' path = F path) ∧
      (∀ path, path.length < N + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) ∧
      (∀ path, path.length ≤ N + 2 → ‖F' path‖ ≤
        max B (Real.sqrt ((Λ * (2 * (K + ‖ζ‖ * (Λ * B + (2 : ℝ) ^ (N + 1) * A * B)) +
          (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * B))) ^ 2 * (d : ℝ)))) := by
  let D : Fin d → List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun k path => F (k :: path)
  have hD : ∀ k path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (D k path) (fun j => D k (path ++ [j])) := by
    intro k path hp
    simpa only [D, List.cons_append] using hF (k :: path) (by simp only [List.length_cons]; omega)
  have hDB : ∀ k path, path.length ≤ N → ‖D k path‖ ≤ B := by
    intro k path hp
    exact hFB (k :: path) (by simp only [List.length_cons]; omega)
  have hG : IsPhysicalH1Graph volume (Or.inl rfl) (F []) (fun k => D k []) := by
    simpa [D] using hF [] (by simp)
  obtain ⟨F', hold, hgraph, henergy⟩ :=
    u4Higher_transpose_extend_derivative_layer hΛ hell hsmooth D hD F J (fun path hp => hF path (by omega)) hJ
      A B B K hA hB hB hDB hFB hJB hfg hG hM
  refine ⟨F', hold, hgraph, ?_⟩
  have hC : 0 ≤ (Λ * (2 * (K + ‖ζ‖ * (Λ * B + (2 : ℝ) ^ (N + 1) * A * B)) +
      (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * B))) ^ 2 * (d : ℝ) :=
    mul_nonneg (sq_nonneg _) (Nat.cast_nonneg d)
  apply u4Higher_derivative_layer_norm_bound F' B _ hC ?_ henergy
  intro path hp
  rw [hold path hp]
  exact hFB path hp

/-- A finite layer of derivative paths has a common nonnegative norm bound. -/
theorem u4Higher_finite_layer_norm_bound {d : ℕ}
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d))) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ path, path.length ≤ N → ‖F path‖ ≤ B := by
  have hf := (List.finite_length_le (Fin d) N).image (fun path => ‖F path‖)
  obtain ⟨B, hB⟩ := hf.bddAbove
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro path hp
  exact le_trans (hB ⟨path, hp, rfl⟩) (le_max_right _ _)

/-- A finite initial segment of the coefficient bounds has a common
nonnegative upper bound. -/
theorem u4Higher_finite_coefficient_bound (M : ℕ → ℝ) (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k ≤ N, M k ≤ A := by
  have hf : Set.Finite {k : ℕ | k ≤ N} := (Set.finite_le_nat N)
  obtain ⟨A, hA⟩ := (hf.image M).bddAbove
  refine ⟨max 0 A, le_max_left _ _, ?_⟩
  intro k hk
  exact le_trans (hA ⟨k, hk, rfl⟩) (le_max_right _ _)

/-- One qualitative regularity step for an actual forward generator pair;
the necessary finite-layer bounds follow from the finite coordinate set. -/
theorem u4Higher_forward_derivative_step {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length ≤ N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ (F []) (J [])) :
    ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ N + 1 → F' path = F path) ∧
      (∀ path, path.length < N + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) := by
  obtain ⟨A, hA, hM⟩ := u4Higher_finite_coefficient_bound M (N + 1)
  obtain ⟨B, hB, hFB⟩ := u4Higher_finite_layer_norm_bound F (N + 1)
  obtain ⟨K, -, hJB⟩ := u4Higher_finite_layer_norm_bound J N
  obtain ⟨F', hold, hgraph, _⟩ := u4Higher_forward_bounded_derivative_step
    hΛ hell hsmooth F J hF hJ A B K hA hB hFB
    (fun path hp => hJB path (by omega)) hfg hM
  exact ⟨F', hold, hgraph⟩

/-- The same qualitative regularity step for the actual transpose generator. -/
theorem u4Higher_transpose_derivative_step {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length ≤ N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J [])) :
    ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ N + 1 → F' path = F path) ∧
      (∀ path, path.length < N + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) := by
  obtain ⟨A, hA, hM⟩ := u4Higher_finite_coefficient_bound M (N + 1)
  obtain ⟨B, hB, hFB⟩ := u4Higher_finite_layer_norm_bound F (N + 1)
  obtain ⟨K, -, hJB⟩ := u4Higher_finite_layer_norm_bound J N
  obtain ⟨F', hold, hgraph, _⟩ := u4Higher_transpose_bounded_derivative_step
    hΛ hell hsmooth F J hF hJ A B K hA hB hFB
    (fun path hp => hJB path (by omega)) hfg hM
  exact ⟨F', hold, hgraph⟩


/-- Package a second-order physical Sobolev graph as a compatible family of
coordinate derivatives on all paths of length at most two. -/
theorem u4Higher_H2_derivative_family {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j)) :
    ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      F [] = f ∧ ∀ path, path.length < 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])) := by
  let F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d))
    | [] => f
    | [j] => G j
    | j :: k :: _ => H j k
  refine ⟨F, rfl, ?_⟩
  intro path hp
  cases path with
  | nil => simpa [F] using hG
  | cons j rest =>
      cases rest with
      | nil => simpa [F] using hH j
      | cons k rest => simp at hp

/-- A finite chain of actual physical generator pairs gives a compatible
family of weak coordinate derivatives of arbitrarily high prescribed order. -/
theorem u4Higher_generator_chain_derivative_family {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (n : ℕ) (u : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (hchain : ∀ k ≤ n,
      IsPhysicalComplexGeneratorPair ω.1 i ζ (u k) (u (k + 1)) ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (u k) (u (k + 1))) :
    ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      F [] = u 0 ∧ ∀ path, path.length < n + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])) := by
  induction n generalizing u with
  | zero =>
      obtain ⟨C, hC, hH2⟩ := u4_physical_generator_pair_H2 hΛ hell hsmooth (i := i) (ζ := ζ)
      obtain ⟨G, H, hG, hH, _⟩ := hH2 (u 0) (u 1) (hchain 0 (by omega))
      exact u4Higher_H2_derivative_family (u 0) G H hG hH
  | succ n ih =>
      obtain ⟨F, hF0, hF⟩ := ih u (fun k hk => hchain k (by omega))
      let v := fun k => u (k + 1)
      have hv : ∀ k ≤ n,
          IsPhysicalComplexGeneratorPair ω.1 i ζ (v k) (v (k + 1)) ∨
          IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (v k) (v (k + 1)) := by
        intro k hk
        simpa [v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchain (k + 1) (by omega)
      obtain ⟨J, hJ0, hJ⟩ := ih v hv
      have hpair : IsPhysicalComplexGeneratorPair ω.1 i ζ (F []) (J []) ∨
          IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J []) := by
        simpa [hF0, hJ0, v] using hchain 0 (by omega)
      have hF' : ∀ path, path.length ≤ n + 1 →
          IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])) := by
        intro path hp
        exact hF path (by omega)
      have hJ' : ∀ path, path.length < n + 1 →
          IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])) := by
        intro path hp
        exact hJ path (by omega)
      obtain ⟨F', hold, hgraph⟩ := hpair.elim
        (fun hp => u4Higher_forward_derivative_step hΛ hell hsmooth F J hF' hJ' hp)
        (fun hp => u4Higher_transpose_derivative_step hΛ hell hsmooth F J hF' hJ' hp)
      refine ⟨F', ?_, ?_⟩
      · rw [hold [] (by simp), hF0]
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hgraph


/-- Reindex a finite generator chain by natural numbers, preserving the actual
weak generator relations along the part of the chain that is used. -/
theorem u4Higher_finite_generator_chain_derivative_family {d n : ℕ}
    {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (u : Fin (n + 2) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hchain : ∀ k : Fin (n + 1),
      IsPhysicalComplexGeneratorPair ω.1 i ζ (u k.castSucc) (u k.succ) ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (u k.castSucc) (u k.succ)) :
    ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      F [] = u 0 ∧ ∀ path, path.length < n + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])) := by
  let v : ℕ → Lp ℂ 2 (volume : Measure (Vec d)) := fun k =>
    u ⟨min k (n + 1), by omega⟩
  have hv : ∀ k ≤ n,
      IsPhysicalComplexGeneratorPair ω.1 i ζ (v k) (v (k + 1)) ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (v k) (v (k + 1)) := by
    intro k hk
    let q : Fin (n + 1) := ⟨k, by omega⟩
    have hq0 : q.castSucc = (⟨k, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hq1 : q.succ = (⟨k + 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hc := hchain q
    rw [hq0, hq1] at hc
    simpa [v, Nat.min_eq_left (show k ≤ n + 1 by omega),
      Nat.min_eq_left (show k + 1 ≤ n + 1 by omega)] using hc
  obtain ⟨F, hF0, hF⟩ := u4Higher_generator_chain_derivative_family
    hΛ hell hsmooth n v hv
  exact ⟨F, by simpa [v] using hF0, hF⟩

/-- Both actual physical semigroups have weak derivatives of every finite
order at every positive time, for arbitrary L² initial data. -/
theorem u4Higher_positive_time_derivative_families {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (n : ℕ) (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) (ht : 0 < t) :
    ∃ F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      F [] = P t f ∧ J [] = Pdag t f ∧
      (∀ path, path.length < n + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j]))) ∧
      (∀ path, path.length < n + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j]))) := by
  obtain ⟨u, v, hu, hv, hchain⟩ :=
    c18_physical_positive_time_generator_chains hΛ hell hsmooth hP hPdag (n + 1) f t ht
  obtain ⟨F, hF0, hF⟩ := u4Higher_finite_generator_chain_derivative_family
    hΛ hell hsmooth u (fun k => Or.inl (hchain k).1)
  obtain ⟨J, hJ0, hJ⟩ := u4Higher_finite_generator_chain_derivative_family
    hΛ hell hsmooth v (fun k => Or.inr (hchain k).2)
  exact ⟨F, J, hF0.trans hu, hJ0.trans hv, hF, hJ⟩


/-- Extract the common size of the data from the coercive square-root bound. -/
theorem u4Higher_sqrt_homogeneous (R c d : ℝ) (hR : 0 ≤ R) (hd : 0 ≤ d) :
    max R (Real.sqrt ((c * R) ^ 2 * d)) =
      max 1 (Real.sqrt (c ^ 2 * d)) * R := by
  have he : (c * R) ^ 2 * d = (c ^ 2 * d) * R ^ 2 := by ring
  rw [he, Real.sqrt_mul (by positivity : 0 ≤ c ^ 2 * d),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hR, max_mul_of_nonneg _ _ hR, one_mul]

/-- A force-uniform homogeneous bound for one forward derivative layer. -/
theorem u4Higher_forward_homogeneous_derivative_step {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length ≤ N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A R Z : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R) (hZ : ‖ζ‖ ≤ Z)
    (hFB : ∀ path, path.length ≤ N + 1 → ‖F path‖ ≤ R)
    (hJB : ∀ path, path.length = N → ‖J path‖ ≤ R)
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ (F []) (J []))
    (hM : ∀ k ≤ N + 1, M k ≤ A) :
    ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ N + 1 → F' path = F path) ∧
      (∀ path, path.length < N + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) ∧
      (∀ path, path.length ≤ N + 2 → ‖F' path‖ ≤
        max 1 (Real.sqrt ((Λ * (2 * (1 + Z * ((d : ℝ) *
          (Λ + (2 : ℝ) ^ N * A))) + (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A))) ^ 2 *
          (d : ℝ))) * R) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hZ0 : 0 ≤ Z := le_trans (norm_nonneg ζ) hZ
  obtain ⟨F', hold, hgraph, hbound⟩ := u4Higher_forward_bounded_derivative_step
    hΛ hell hsmooth F J hF hJ A R R hA hR hFB hJB hfg hM
  refine ⟨F', hold, hgraph, ?_⟩
  intro path hp
  apply le_trans (hbound path hp)
  let c := Λ * (2 * (1 + Z * ((d : ℝ) * (Λ + (2 : ℝ) ^ N * A))) +
    (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hinner : Λ * (2 * (R + ‖ζ‖ * ((d : ℝ) *
      (Λ * R + (2 : ℝ) ^ N * A * R))) +
      (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * R)) ≤ c * R := by
    have he : c * R = Λ * (2 * (R + Z * ((d : ℝ) *
        (Λ * R + (2 : ℝ) ^ N * A * R))) +
        (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * R)) := by dsimp [c]; ring
    rw [he]
    gcongr
  have hleft : 0 ≤ Λ * (2 * (R + ‖ζ‖ * ((d : ℝ) *
      (Λ * R + (2 : ℝ) ^ N * A * R))) +
      (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * R)) := by positivity
  calc
    _ ≤ max R (Real.sqrt ((c * R) ^ 2 * (d : ℝ))) := by
      apply max_le_max_left
      apply Real.sqrt_le_sqrt
      gcongr
    _ = max 1 (Real.sqrt (c ^ 2 * (d : ℝ))) * R :=
      u4Higher_sqrt_homogeneous R c d hR (Nat.cast_nonneg d)
    _ = _ := rfl

/-- A force-uniform homogeneous bound for one transpose derivative layer. -/
theorem u4Higher_transpose_homogeneous_derivative_step {d N : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ path, path.length ≤ N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j])))
    (hJ : ∀ path, path.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (J path) (fun j => J (path ++ [j])))
    (A R Z : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R) (hZ : ‖ζ‖ ≤ Z)
    (hFB : ∀ path, path.length ≤ N + 1 → ‖F path‖ ≤ R)
    (hJB : ∀ path, path.length = N → ‖J path‖ ≤ R)
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J []))
    (hM : ∀ k ≤ N + 1, M k ≤ A) :
    ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ N + 1 → F' path = F path) ∧
      (∀ path, path.length < N + 2 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) ∧
      (∀ path, path.length ≤ N + 2 → ‖F' path‖ ≤
        max 1 (Real.sqrt ((Λ * (2 * (1 + Z *
          (Λ + (2 : ℝ) ^ (N + 1) * A)) + (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A))) ^ 2 *
          (d : ℝ))) * R) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hZ0 : 0 ≤ Z := le_trans (norm_nonneg ζ) hZ
  obtain ⟨F', hold, hgraph, hbound⟩ := u4Higher_transpose_bounded_derivative_step
    hΛ hell hsmooth F J hF hJ A R R hA hR hFB hJB hfg hM
  refine ⟨F', hold, hgraph, ?_⟩
  intro path hp
  apply le_trans (hbound path hp)
  let c := Λ * (2 * (1 + Z * (Λ + (2 : ℝ) ^ (N + 1) * A)) +
    (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hinner : Λ * (2 * (R + ‖ζ‖ *
      (Λ * R + (2 : ℝ) ^ (N + 1) * A * R)) +
      (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * R)) ≤ c * R := by
    have he : c * R = Λ * (2 * (R + Z *
        (Λ * R + (2 : ℝ) ^ (N + 1) * A * R)) +
        (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * R)) := by dsimp [c]; ring
    rw [he]
    gcongr
  have hleft : 0 ≤ Λ * (2 * (R + ‖ζ‖ *
      (Λ * R + (2 : ℝ) ^ (N + 1) * A * R)) +
      (d : ℝ) * ((2 : ℝ) ^ (N + 1) * A * R)) := by positivity
  calc
    _ ≤ max R (Real.sqrt ((c * R) ^ 2 * (d : ℝ))) := by
      apply max_le_max_left
      apply Real.sqrt_le_sqrt
      gcongr
    _ = max 1 (Real.sqrt (c ^ 2 * (d : ℝ))) * R :=
      u4Higher_sqrt_homogeneous R c d hR (Nat.cast_nonneg d)
    _ = _ := rfl


/-- Uniformly propagate quantitative H² bounds through a finite chain of
physical generator pairs, allowing either orientation at each link. -/
theorem u4Higher_generator_chain_homogeneous_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (A Z : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (hZ : ‖ζ‖ ≤ Z) (hM : ∀ k ≤ n + 2, M k ≤ A)
      (u : ℕ → Lp ℂ 2 (volume : Measure (Vec d))) (R : ℝ) (hR : 0 ≤ R),
      (∀ k ≤ n, IsPhysicalComplexGeneratorPair ω.1 i ζ (u k) (u (k + 1)) ∨
        IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (u k) (u (k + 1))) →
      (∀ k ≤ n, ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
        F [] = u k ∧
        (∀ path, path.length < 2 →
          IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j]))) ∧
        (∀ path, path.length ≤ 2 → ‖F path‖ ≤ R)) →
      ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
        F [] = u 0 ∧
        (∀ path, path.length < n + 2 →
          IsPhysicalH1Graph volume (Or.inl rfl) (F path) (fun j => F (path ++ [j]))) ∧
        (∀ path, path.length ≤ n + 2 → ‖F path‖ ≤ C * R) := by
  induction n with
  | zero =>
      refine ⟨1, le_rfl, ?_⟩
      intro ω i ζ hell hsmooth hZ hM u R hR hchain hbase
      obtain ⟨F, hF0, hF, hbound⟩ := hbase 0 (by omega)
      exact ⟨F, hF0, hF, by simpa using hbound⟩
  | succ n ih =>
      obtain ⟨C, hC, ih⟩ := ih
      let B := max 1 (Real.sqrt ((Λ * (2 * (1 + Z * ((d : ℝ) *
        (Λ + (2 : ℝ) ^ (n + 1) * A))) + (d : ℝ) *
        ((2 : ℝ) ^ (n + 2) * A))) ^ 2 * (d : ℝ)))
      let D := max 1 (Real.sqrt ((Λ * (2 * (1 + Z *
        (Λ + (2 : ℝ) ^ (n + 2) * A)) + (d : ℝ) *
        ((2 : ℝ) ^ (n + 2) * A))) ^ 2 * (d : ℝ)))
      refine ⟨max B D * C, ?_, ?_⟩
      · have hBD : 1 ≤ max B D := le_trans (le_max_left 1 _) (le_max_left B D)
        nlinarith
      · intro ω i ζ hell hsmooth hZ hM u R hR hchain hbase
        have hM' : ∀ k ≤ n + 2, M k ≤ A := fun k hk => hM k (by omega)
        obtain ⟨F, hF0, hF, hFB⟩ := ih hell hsmooth hZ hM' u R hR
          (fun k hk => hchain k (by omega)) (fun k hk => hbase k (by omega))
        let v := fun k => u (k + 1)
        have hv : ∀ k ≤ n, IsPhysicalComplexGeneratorPair ω.1 i ζ (v k) (v (k + 1)) ∨
            IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (v k) (v (k + 1)) := by
          intro k hk
          simpa [v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchain (k + 1) (by omega)
        have hb : ∀ k ≤ n, ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
            F [] = v k ∧
            (∀ path, path.length < 2 → IsPhysicalH1Graph volume (Or.inl rfl)
              (F path) (fun j => F (path ++ [j]))) ∧
            (∀ path, path.length ≤ 2 → ‖F path‖ ≤ R) := by
          intro k hk
          simpa [v] using hbase (k + 1) (by omega)
        obtain ⟨J, hJ0, hJ, hJB⟩ := ih hell hsmooth hZ hM' v R hR hv hb
        have hpair : IsPhysicalComplexGeneratorPair ω.1 i ζ (F []) (J []) ∨
            IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J []) := by
          simpa [hF0, hJ0, v] using hchain 0 (by omega)
        have hF' : ∀ path, path.length ≤ n + 1 → IsPhysicalH1Graph volume
            (Or.inl rfl) (F path) (fun j => F (path ++ [j])) := by
          intro path hp; exact hF path (by omega)
        have hJ' : ∀ path, path.length < n + 1 → IsPhysicalH1Graph volume
            (Or.inl rfl) (J path) (fun j => J (path ++ [j])) := by
          intro path hp; exact hJ path (by omega)
        have hFB' : ∀ path, path.length ≤ (n + 1) + 1 → ‖F path‖ ≤ C * R := by
          intro path hp; exact hFB path (by omega)
        have hJB' : ∀ path, path.length = n + 1 → ‖J path‖ ≤ C * R := by
          intro path hp; exact hJB path (by omega)
        have hCR : 0 ≤ C * R := mul_nonneg (by linarith) hR
        have hM'' : ∀ k ≤ (n + 1) + 1, M k ≤ A := fun k hk => hM k (by omega)
        have hext : ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
            (∀ path, path.length ≤ (n + 1) + 1 → F' path = F path) ∧
            (∀ path, path.length < (n + 1) + 2 → IsPhysicalH1Graph volume
              (Or.inl rfl) (F' path) (fun j => F' (path ++ [j]))) ∧
            (∀ path, path.length ≤ (n + 1) + 2 → ‖F' path‖ ≤ max B D * (C * R)) := by
          rcases hpair with hp | hp
          · obtain ⟨F', hold, hgraph, hbound⟩ := u4Higher_forward_homogeneous_derivative_step
              hΛ hell hsmooth F J hF' hJ' A (C * R) Z hA hCR hZ hFB' hJB' hp hM''
            exact ⟨F', hold, hgraph, fun path hp => le_trans (hbound path hp)
              (mul_le_mul_of_nonneg_right (le_max_left B D) hCR)⟩
          · obtain ⟨F', hold, hgraph, hbound⟩ := u4Higher_transpose_homogeneous_derivative_step
              hΛ hell hsmooth F J hF' hJ' A (C * R) Z hA hCR hZ hFB' hJB' hp hM''
            exact ⟨F', hold, hgraph, fun path hp => le_trans (hbound path hp)
              (mul_le_mul_of_nonneg_right (le_max_right B D) hCR)⟩
        obtain ⟨F', hold, hgraph, hbound⟩ := hext
        refine ⟨F', ?_, ?_, ?_⟩
        · rw [hold [] (by simp), hF0]
        · simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hgraph
        · intro path hp
          have hh := hbound path (by omega)
          simpa only [mul_assoc] using hh


/-- Uniform H² control for either physical generator on a bounded force ball. -/
theorem u4Higher_generator_pair_uniform_H2_family {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (A Z : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (hζ : ‖ζ‖ ≤ Z) (hM : ∀ k ≤ 1, M k ≤ A)
      (f g : Lp ℂ 2 (volume : Measure (Vec d))) (R : ℝ) (hR : 0 ≤ R),
      ‖f‖ ≤ R → ‖g‖ ≤ R →
      (IsPhysicalComplexGeneratorPair ω.1 i ζ f g ∨
        IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g) →
      ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
        F [] = f ∧
        (∀ path, path.length < 2 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F path) (fun j => F (path ++ [j]))) ∧
        (∀ path, path.length ≤ 2 → ‖F path‖ ≤ C * R) := by
  let K : ℝ := 2 * (4 * Λ + 4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * Z ^ 2)
  let E : ℝ := max 1 (Real.sqrt K)
  let B : ℝ := max 1 (Real.sqrt ((Λ * (2 * (1 + Z * ((d : ℝ) *
    (Λ + (2 : ℝ) ^ 0 * A))) + (d : ℝ) * ((2 : ℝ) ^ (0 + 1) * A))) ^ 2 * (d : ℝ)))
  let D : ℝ := max 1 (Real.sqrt ((Λ * (2 * (1 + Z *
    (Λ + (2 : ℝ) ^ (0 + 1) * A)) + (d : ℝ) *
    ((2 : ℝ) ^ (0 + 1) * A))) ^ 2 * (d : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 1 ≤ E := le_max_left _ _
  have hBD : 1 ≤ max B D := le_trans (le_max_left 1 _) (le_max_left B D)
  refine ⟨max B D * E, by nlinarith, ?_⟩
  intro ω i ζ hell hsmooth hζ hM f g R hR hf hg hfg
  obtain ⟨G, hG, hfirst⟩ := u4h2_physical_generator_pair_first_gradient
    hΛ hell hsmooth f g hfg
  have hΛ0 : 0 ≤ Λ := by linarith
  have hfirst' : ∑ j, ‖G j‖ ^ 2 ≤ K * R ^ 2 := by
    calc
      _ ≤ (4 * Λ + 4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * Z ^ 2) *
          (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
            apply le_trans hfirst
            gcongr
      _ ≤ (4 * Λ + 4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * Z ^ 2) *
          (2 * R ^ 2) := by
            gcongr <;> nlinarith [norm_nonneg f, norm_nonneg g]
      _ = K * R ^ 2 := by dsimp [K]; ring
  have hGn (j : Fin d) : ‖G j‖ ≤ E * R := by
    have hj : ‖G j‖ ^ 2 ≤ K * R ^ 2 := le_trans
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖G k‖) (Finset.mem_univ j)) hfirst'
    have hs := Real.sq_sqrt hK
    have hs0 := Real.sqrt_nonneg K
    have he : Real.sqrt K ≤ E := le_max_right 1 _
    have heq : (Real.sqrt K * R) ^ 2 = K * R ^ 2 := by rw [mul_pow, hs]
    have hh : ‖G j‖ ≤ Real.sqrt K * R := by
      nlinarith [norm_nonneg (G j), mul_nonneg hs0 hR]
    exact le_trans hh (mul_le_mul_of_nonneg_right he hR)
  let F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d))
    | [] => f
    | [j] => G j
    | _ => 0
  let J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) := fun _ => g
  have hF : ∀ path, path.length ≤ 0 → IsPhysicalH1Graph volume
      (Or.inl rfl) (F path) (fun j => F (path ++ [j])) := by
    intro path hp
    cases path with
    | nil => simpa [F] using hG
    | cons j rest => simp at hp
  have hJ : ∀ path, path.length < 0 → IsPhysicalH1Graph volume
      (Or.inl rfl) (J path) (fun j => J (path ++ [j])) := by
    intro path hp; omega
  have hER : 0 ≤ E * R := mul_nonneg (by linarith) hR
  have hFB : ∀ path, path.length ≤ 0 + 1 → ‖F path‖ ≤ E * R := by
    intro path hp
    cases path with
    | nil => simpa [F] using le_trans hf (by nlinarith)
    | cons j rest =>
        cases rest with
        | nil => simpa [F] using hGn j
        | cons k rest => simp at hp
  have hJB : ∀ path, path.length = 0 → ‖J path‖ ≤ E * R := by
    intro path hp
    simpa [J] using le_trans hg (show R ≤ E * R by nlinarith)
  have hp : IsPhysicalComplexGeneratorPair ω.1 i ζ (F []) (J []) ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (F []) (J []) := by simpa [F, J] using hfg
  have hext : ∃ F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ path, path.length ≤ 1 → F' path = F path) ∧
      (∀ path, path.length < 2 → IsPhysicalH1Graph volume (Or.inl rfl)
        (F' path) (fun j => F' (path ++ [j]))) ∧
      (∀ path, path.length ≤ 2 → ‖F' path‖ ≤ max B D * (E * R)) := by
    rcases hp with hp | hp
    · obtain ⟨F', hold, hg, hb⟩ := u4Higher_forward_homogeneous_derivative_step
        hΛ hell hsmooth F J hF hJ A (E * R) Z hA hER hζ hFB hJB hp hM
      exact ⟨F', hold, hg, fun path hp => le_trans (hb path hp)
        (mul_le_mul_of_nonneg_right (le_max_left B D) hER)⟩
    · obtain ⟨F', hold, hg, hb⟩ := u4Higher_transpose_homogeneous_derivative_step
        hΛ hell hsmooth F J hF hJ A (E * R) Z hA hER hζ hFB hJB hp hM
      exact ⟨F', hold, hg, fun path hp => le_trans (hb path hp)
        (mul_le_mul_of_nonneg_right (le_max_right B D) hER)⟩
  obtain ⟨F', hold, hg, hb⟩ := hext
  refine ⟨F', ?_, hg, ?_⟩
  · simpa [F] using hold [] (by simp)
  · intro path hp
    simpa only [mul_assoc] using hb path hp


/-- Quantitative weak derivatives of every prescribed order from a uniformly
bounded finite chain of the actual physical generators. -/
theorem u4Higher_generator_chain_uniform_derivatives {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (A Z : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (hζ : ‖ζ‖ ≤ Z) (hM : ∀ k ≤ n + 2, M k ≤ A)
      (u : ℕ → Lp ℂ 2 (volume : Measure (Vec d))) (R : ℝ) (hR : 0 ≤ R),
      (∀ k ≤ n, IsPhysicalComplexGeneratorPair ω.1 i ζ (u k) (u (k + 1)) ∨
        IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (u k) (u (k + 1))) →
      (∀ k ≤ n + 1, ‖u k‖ ≤ R) →
      ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
        F [] = u 0 ∧
        (∀ path, path.length < n + 2 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F path) (fun j => F (path ++ [j]))) ∧
        (∀ path, path.length ≤ n + 2 → ‖F path‖ ≤ C * R) := by
  obtain ⟨C₀, hC₀, hbase⟩ := u4Higher_generator_pair_uniform_H2_family
    (M := M) (d := d) hΛ A Z hA
  obtain ⟨C₁, hC₁, hchain⟩ := u4Higher_generator_chain_homogeneous_bound
    (M := M) (d := d) hΛ A Z hA n
  refine ⟨C₁ * C₀, by nlinarith, ?_⟩
  intro ω i ζ hell hsmooth hζ hM u R hR hpair hsize
  have hC₀R : 0 ≤ C₀ * R := mul_nonneg (by linarith) hR
  have hb : ∀ k ≤ n, ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      F [] = u k ∧
      (∀ path, path.length < 2 → IsPhysicalH1Graph volume (Or.inl rfl)
        (F path) (fun j => F (path ++ [j]))) ∧
      (∀ path, path.length ≤ 2 → ‖F path‖ ≤ C₀ * R) := by
    intro k hk
    exact hbase hell hsmooth hζ (fun j hj => hM j (by omega)) (u k) (u (k + 1))
      R hR (hsize k (by omega)) (hsize (k + 1) (by omega)) (hpair k hk)
  obtain ⟨F, hF0, hF, hbound⟩ := hchain hell hsmooth hζ hM u (C₀ * R) hC₀R hpair hb
  refine ⟨F, hF0, hF, ?_⟩
  intro path hp
  simpa only [mul_assoc] using hbound path hp

private theorem u4Quant_pi_norm_sq_le_sum {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (G : Fin d → E) : ‖G‖ ^ 2 ≤ ∑ j, ‖G j‖ ^ 2 := by
  have hn : 0 ≤ ∑ j, ‖G j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : ‖G‖ ≤ Real.sqrt (∑ j, ‖G j‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    apply (Real.le_sqrt (norm_nonneg _) hn).mpr
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖G k‖) (Finset.mem_univ j)
  have hsq := sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _) |>.mpr hb
  rwa [Real.sq_sqrt hn] at hsq

private theorem u4Quant_integrated_gradient_bound
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (μ K : ℝ) (hμ : 0 < μ) (hK : 0 ≤ K)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (K * (t : ℝ)) * ‖f‖)
    (f : E) (G : ℝ → Fin d → E) (hG : ∀ j, Continuous (fun s => G s j))
    (t : ℝ≥0)
    (henergy : μ * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
      (‖f‖ ^ 2 - ‖P t f‖ ^ 2) / 2 +
        K * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2)) :
    (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2) ≤
      ((1 / 2 + K * (Real.exp (K * (t : ℝ)) ^ 2 * (t : ℝ))) / μ) * ‖f‖ ^ 2 := by
  have hGc : Continuous G := continuous_pi hG
  have hsc : Continuous (fun s => ∑ j, ‖G s j‖ ^ 2) :=
    continuous_finset_sum _ fun j _ => (hG j).norm.pow 2
  have huc : Continuous (fun s : ℝ => ‖P s.toNNReal f‖ ^ 2) :=
    ((hP.cont f).comp continuous_real_toNNReal).norm.pow 2
  have hsq (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (t : ℝ)) :
      ‖P s.toNNReal f‖ ^ 2 ≤ Real.exp (K * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
    have he : Real.exp (K * (s.toNNReal : ℝ)) ≤ Real.exp (K * (t : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.coe_toNNReal _ hs.1] using hs.2) hK
    have hb := (hgrowth f s.toNNReal).trans (mul_le_mul_of_nonneg_right he (norm_nonneg f))
    calc
      ‖P s.toNNReal f‖ ^ 2 ≤ (Real.exp (K * (t : ℝ)) * ‖f‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
      _ = _ := mul_pow _ _ _
  have hui : (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2) ≤
      Real.exp (K * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 * (t : ℝ) := by
    have hb := intervalIntegral.integral_mono_on (NNReal.coe_nonneg t)
      (huc.intervalIntegrable (μ := volume) 0 t) (intervalIntegrable_const (μ := volume) (c :=
        Real.exp (K * (t : ℝ)) ^ 2 * ‖f‖ ^ 2)) hsq
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hb
  have hcompare : (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2) ≤
      ∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property),
      ← integral_Icc_eq_integral_Ioc]
    exact integral_mono ((hGc.norm.pow 2).integrableOn_Icc) hsc.integrableOn_Icc
      (fun s => u4Quant_pi_norm_sq_le_sum (G s))
  have hmul := mul_le_mul_of_nonneg_left hcompare hμ.le
  have huim := mul_le_mul_of_nonneg_left hui hK
  have hfinal : μ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2) ≤
      (1 / 2 + K * (Real.exp (K * (t : ℝ)) ^ 2 * (t : ℝ))) * ‖f‖ ^ 2 := by
    nlinarith only [hmul, henergy, huim, sq_nonneg ‖P t f‖]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hμ).mpr
  nlinarith only [hfinal]

private theorem u4Quant_gradient_endpoint_bound
    {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen)
    (μ L K J : ℝ) (hμ : 0 < μ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖)
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : ∀ j, Continuous (fun s => G s j))
    (t : ℝ≥0) (ht : 0 < t)
    (henergy : μ * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
      (‖f‖ ^ 2 - ‖P t f‖ ^ 2) / 2 +
        L * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2))
    (hder : ∀ s, 0 ≤ s → ∃ q' : ℝ,
      HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * G r k x * star (G r j x)).re) q' s ∧
      q' ≤ K * (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * G s k x * star (G s j x)).re + J * ‖P s.toNNReal f‖ ^ 2) :
    (∑ j, ‖G t j‖ ^ 2) ≤
      (Λ * (Λ * (d : ℝ) *
        ((1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ) +
          J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) ^ 2) /
        ((t : ℝ) * Real.exp (-K * (t : ℝ)))) * ‖f‖ ^ 2 := by
  let q : ℝ → ℝ := fun s => (∫ x, ∑ j, ∑ k,
    (a x j k : ℂ) * G s k x * star (G s j x)).re
  let B := (1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ
  have ht' : (0 : ℝ) < t := ht
  have hqc : ContinuousOn q (Set.Icc 0 (t : ℝ)) := by
    intro s hs
    exact (hder s hs.1).choose_spec.1.continuousAt.continuousWithinAt
  have hqp (s : ℝ) : q s ≤ Λ * (d : ℝ) * ‖G s‖ ^ 2 := by
    have hb := c18_physical_principal_energy_upper a ha hA (G s)
    have hn : (∑ j, ‖G s j‖ ^ 2) ≤ (d : ℝ) * ‖G s‖ ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin d, ‖G s‖ ^ 2 := Finset.sum_le_sum fun j _ =>
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm (G s) j)
        _ = _ := by simp
    exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_left hn hΛ.le])
  have hnonneg (s : ℝ) : 0 ≤ q s := by
    have hb := c18_physical_principal_energy_coercive a ha hΛ hA (G s)
    have hn : 0 ≤ ∑ j, ‖G s j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    change (∑ j, ‖G s j‖ ^ 2) ≤ Λ * q s at hb
    nlinarith only [hb, hn, hΛ]
  have hint := u4Quant_integrated_gradient_bound hP μ L hμ hL hgrowth f G hG t henergy
  have hqi : (∫ s in (0 : ℝ)..(t : ℝ), q s) ≤
      Λ * (d : ℝ) * B * ‖f‖ ^ 2 := by
    have hgcont : Continuous (fun s => ‖G s‖ ^ 2) := (continuous_pi hG).norm.pow 2
    have hi := intervalIntegral.integral_mono_on ht'.le
      (hqc.intervalIntegrable_of_Icc (μ := volume) ht'.le)
      ((hgcont.const_mul (Λ * (d : ℝ))).intervalIntegrable (μ := volume) 0 t)
      (fun s _ => hqp s)
    rw [intervalIntegral.integral_const_mul] at hi
    have heq : (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2) =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le ht'.le, ← integral_Icc_eq_integral_Ioc]
    rw [heq] at hi
    have hm := mul_le_mul_of_nonneg_left hint
      (mul_nonneg hΛ.le (Nat.cast_nonneg d))
    calc
      _ ≤ Λ * (d : ℝ) * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2) := hi
      _ ≤ Λ * (d : ℝ) * (B * ‖f‖ ^ 2) := hm
      _ = _ := by ring
  have hsq (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      ‖P s.toNNReal f‖ ^ 2 ≤ Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
    have he : Real.exp (L * (s.toNNReal : ℝ)) ≤ Real.exp (L * (t : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.coe_toNNReal _ hs.1] using hs.2) hL
    have hb := (hgrowth f s.toNNReal).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg f))
    exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb).trans_eq (mul_pow _ _ _)
  let q' : ℝ → ℝ := fun s => if hs : 0 ≤ s then (hder s hs).choose else 0
  have hd (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) : HasDerivAt q (q' s) s := by
    dsimp [q']; rw [dif_pos hs.1]; exact (hder s hs.1).choose_spec.1
  have hb (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      q' s ≤ K * q s + J * Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
    dsimp [q']; rw [dif_pos hs.1]
    have hm := mul_le_mul_of_nonneg_left (hsq s hs) hJ
    exact (hder s hs.1).choose_spec.2.trans (by dsimp [q]; nlinarith only [hm])
  have he := c18_principal_energy_endpoint_from_integral_on q q' K
    (J * Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2) t hK (by positivity) ht'.le
    hd (fun s _ => hnonneg s) hb
  have hcoer := c18_physical_principal_energy_coercive a ha hΛ hA (G t)
  change (∑ j, ‖G t j‖ ^ 2) ≤ Λ * q t at hcoer
  have hdpos : 0 < (t : ℝ) * Real.exp (-K * (t : ℝ)) :=
    mul_pos ht' (Real.exp_pos _)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hdpos).mpr
  have he' := mul_le_mul_of_nonneg_left he hΛ.le
  have hi' := mul_le_mul_of_nonneg_left hqi hΛ.le
  have hc' := mul_le_mul_of_nonneg_right hcoer hdpos.le
  dsimp [B] at hi'
  nlinarith only [he', hi', hc']

/-- Explicit endpoint gradient constant, parameterized by the force norm. -/
noncomputable def u4QuantGradientConstant (d : ℕ) (Λ s J : ℝ) (t : ℝ≥0) : ℝ :=
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * s ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * s ^ 2
  Λ * (Λ * (d : ℝ) *
    ((1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ) +
      J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) ^ 2) /
        ((t : ℝ) * Real.exp (-K * (t : ℝ)))

theorem u4Quant_forward_D2_gradient_at_time
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P) (t : ℝ≥0) (ht : 0 < t) :
    ∀ f g h : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair a i ζ f g →
      IsPhysicalComplexGeneratorPair a i ζ g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (P t f) G ∧
        (∑ j, ‖G j‖ ^ 2) ≤ u4QuantGradientConstant d Λ ‖ζ‖ 0 t * ‖f‖ ^ 2 := by
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖ := by
    intro f t
    apply hp.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f t
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_generator_coercive a i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]
  dsimp only [u4QuantGradientConstant]
  intro f g h hfg hgh
  obtain ⟨G, hG, hGc, hder⟩ :=
    c18_physical_D2_principal_energy_bound a i ζ ha hΛ hA P hP hfg hgh
  obtain ⟨H, hH, _, henergy⟩ :=
    c18_physical_orbit_integrated_gradient a i ζ ha hΛ hA P hP hfg
  have heq : (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖H s j‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := (Set.uIcc_of_le t.property ▸ hs).1
    dsimp only
    rw [physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (P s.toNNReal f) (G s) (H s) (hG s hs') (hH s)]
  refine ⟨G t, ?_, ?_⟩
  · simpa only [Real.toNNReal_coe] using hG t t.property
  · apply u4Quant_gradient_endpoint_bound a ha hΛ hA hp μ L K 0
      hμ hL hK le_rfl hgrowth f G hGc t ht
    · rw [heq]; exact henergy t
    · simpa only [zero_mul, add_zero] using hder

theorem u4Quant_transpose_D2_gradient_at_time
    {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hsmooth : IsSmoothWithBounds M ω) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ f g h : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g →
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (Pdag t f) G ∧
        (∑ j, ‖G j‖ ^ 2) ≤ u4QuantGradientConstant d Λ ‖ζ‖ (4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2) t * ‖f‖ ^ 2 := by
  let hp : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2
  let J := 4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hgrowth : ∀ f t, ‖Pdag t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖ := by
    intro f t
    apply hp.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f t
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_transpose_generator_coercive
      ω.1 i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]
  dsimp only [u4QuantGradientConstant]
  intro f g h hfg hgh
  obtain ⟨G, hG, hGc, hder⟩ :=
    c18_physical_transpose_D2_principal_energy_bound hsmooth i ζ ha hΛ hA
      P Pdag hPdag hfg hgh
  obtain ⟨H, hH, _, henergy⟩ :=
    c18_physical_transpose_orbit_integrated_gradient ω.1 i ζ ha hΛ hA P Pdag hPdag hfg
  have heq : (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖H s j‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := (Set.uIcc_of_le t.property ▸ hs).1
    dsimp only
    rw [physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (Pdag s.toNNReal f) (G s) (H s) (hG s hs') (hH s)]
  refine ⟨G t, ?_, ?_⟩
  · simpa only [Real.toNNReal_coe] using hG t t.property
  · apply u4Quant_gradient_endpoint_bound ω.1 ha hΛ hA hp μ L K J
      hμ hL hK hJ hgrowth f G hGc t ht
    · rw [heq]; exact henergy t
    · exact hder


/-- Dissipation and integrated coercivity bound the generator endpoint.
The reference datum `F` permits a preceding semigroup time split. -/
private theorem u4Quant_generator_endpoint_from_dissipation
    {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Gen : Lp ℂ 2 (volume : Measure (Vec d)) →
      Lp ℂ 2 (volume : Measure (Vec d)) → Prop}
    (hP : S5Semigroup P Gen)
    (μ L K J ν A D : ℝ) (hμ : 0 < μ) (hL : 0 ≤ L)
    (hK : 0 ≤ K) (hJ : 0 ≤ J) (hν : 0 < ν)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖)
    (F f g : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : ∀ j, Continuous (fun s => G s j)) (t : ℝ≥0) (ht : 0 < t)
    (henergy : μ * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2) ≤
      (‖f‖ ^ 2 - ‖P t f‖ ^ 2) / 2 +
        L * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2))
    (hzero : (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G 0 k x * star (G 0 j x)).re ≤ A * ‖F‖ ^ 2)
    (hdatum : ‖f‖ ^ 2 ≤ D * ‖F‖ ^ 2)
    (hdiss : let q : ℝ → ℝ := fun s => (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * G s k x * star (G s j x)).re
      ν * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal g‖ ^ 2) ≤
        q 0 - q t + K * (∫ s in (0 : ℝ)..(t : ℝ), q s) +
          J * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2)) :
    ‖P t g‖ ^ 2 ≤
      (Real.exp (L * (t : ℝ)) ^ 2 *
        (A + (K * Λ * (d : ℝ) *
          ((1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ) +
            J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ)) * D) /
              (ν * (t : ℝ))) * ‖F‖ ^ 2 := by
  let q : ℝ → ℝ := fun s => (∫ x, ∑ j, ∑ k,
    (a x j k : ℂ) * G s k x * star (G s j x)).re
  let B := (1 / 2 + L * (Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ))) / μ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hqc : Continuous q := c18_physical_principal_form_continuous a ha G hG
  have hqp (s : ℝ) : q s ≤ Λ * (d : ℝ) * ‖G s‖ ^ 2 := by
    have hb := c18_physical_principal_energy_upper a ha hA (G s)
    have hn : (∑ j, ‖G s j‖ ^ 2) ≤ (d : ℝ) * ‖G s‖ ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin d, ‖G s‖ ^ 2 := Finset.sum_le_sum fun j _ =>
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm (G s) j)
        _ = _ := by simp
    exact hb.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hn hΛ.le)
  have hnonneg : 0 ≤ q t := by
    have hb := c18_physical_principal_energy_coercive a ha hΛ hA (G t)
    have hn : 0 ≤ ∑ j, ‖G t j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    change (∑ j, ‖G t j‖ ^ 2) ≤ Λ * q t at hb
    nlinarith only [hb, hn, hΛ]
  have hint := u4Quant_integrated_gradient_bound hP μ L hμ hL hgrowth f G hG t henergy
  have hqi : (∫ s in (0 : ℝ)..(t : ℝ), q s) ≤
      Λ * (d : ℝ) * B * ‖f‖ ^ 2 := by
    have hgcont : Continuous (fun s => ‖G s‖ ^ 2) := (continuous_pi hG).norm.pow 2
    have hi := intervalIntegral.integral_mono_on t.property
      (hqc.intervalIntegrable (μ := volume) 0 t)
      ((hgcont.const_mul (Λ * (d : ℝ))).intervalIntegrable (μ := volume) 0 t)
      (fun s _ => hqp s)
    rw [intervalIntegral.integral_const_mul] at hi
    have heq : (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2) =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ‖G s‖ ^ 2 := by
      erw [intervalIntegral.integral_of_le t.property, ← integral_Icc_eq_integral_Ioc]
      rfl
    erw [heq] at hi
    exact hi.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hint (mul_nonneg hΛ.le (Nat.cast_nonneg d)))
  have hsq (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      ‖P s.toNNReal f‖ ^ 2 ≤ Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
    have he : Real.exp (L * (s.toNNReal : ℝ)) ≤ Real.exp (L * (t : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by simpa only [Real.coe_toNNReal _ hs.1] using hs.2) hL)
    have hb := (hgrowth f s.toNNReal).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg f))
    exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb).trans_eq (mul_pow _ _ _)
  have hui : (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal f‖ ^ 2) ≤
      Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) * ‖f‖ ^ 2 := by
    have hc : Continuous (fun s : ℝ => ‖P s.toNNReal f‖ ^ 2) :=
      ((hP.cont f).comp continuous_real_toNNReal).norm.pow 2
    have hi := intervalIntegral.integral_mono_on t.property
      (hc.intervalIntegrable (μ := volume) 0 t) (intervalIntegrable_const (μ := volume)) hsq
    have hconst : (∫ _s in (0 : ℝ)..(t : ℝ),
        Real.exp (L * (t : ℝ)) ^ 2 * ‖f‖ ^ 2) =
          Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) * ‖f‖ ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring
    have hi' := hi.trans_eq hconst
    convert hi' using 1; rfl
  have hiq := mul_le_mul_of_nonneg_left hqi hK
  have hiu := mul_le_mul_of_nonneg_left hui hJ
  have hdata := mul_le_mul_of_nonneg_left hdatum
    (show 0 ≤ K * Λ * (d : ℝ) * B + J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ) by positivity)
  have hb : ν * (∫ s in (0 : ℝ)..(t : ℝ), ‖P s.toNNReal g‖ ^ 2) ≤
      (A + (K * Λ * (d : ℝ) * B +
        J * Real.exp (L * (t : ℝ)) ^ 2 * (t : ℝ)) * D) * ‖F‖ ^ 2 := by
    change ν * _ ≤ q 0 - q t + K * _ + J * _ at hdiss
    change q 0 ≤ _ at hzero
    nlinarith only [hdiss, hzero, hnonneg, hiq, hiu, hdata]
  have he := c18_semigroup_endpoint_norm_from_integral hP L hL hgrowth g t
  have he' := mul_le_mul_of_nonneg_left he hν.le
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg (Real.exp (L * (t : ℝ))))
  have ht' : (0 : ℝ) < t := ht
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hν ht')).mpr
  dsimp [B] at hb'
  nlinarith only [he', hb']

/-- Explicit generator endpoint constant after a half-time split. -/
noncomputable def u4QuantGeneratorConstant (d : ℕ) (Λ s J ν : ℝ) (t : ℝ≥0) : ℝ :=
  let τ := t / 2
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * s ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * s ^ 2
  Real.exp (L * (τ : ℝ)) ^ 2 *
    (Λ * u4QuantGradientConstant d Λ s J τ + (K * Λ * (d : ℝ) *
      ((1 / 2 + L * (Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ))) / μ) +
        J * Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ)) *
          Real.exp (L * (τ : ℝ)) ^ 2) / (ν * (τ : ℝ))

/-- A half-time split removes all dependence on the initial generator image
from the actual twice-domain generator endpoint bound. -/
theorem u4Quant_forward_D2_generator_at_time
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P) (t : ℝ≥0) (ht : 0 < t) :
    ∀ f g h : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair a i ζ f g →
      IsPhysicalComplexGeneratorPair a i ζ g h →
      ‖P t g‖ ^ 2 ≤ u4QuantGeneratorConstant d Λ ‖ζ‖ 0 3 t * ‖f‖ ^ 2 := by
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  let τ : ℝ≥0 := t / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hττ : τ + τ = t := add_halves t
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2
  let J : ℝ := 0
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hgrowth : ∀ f s, ‖P s f‖ ≤ Real.exp (L * (s : ℝ)) * ‖f‖ := by
    intro f s
    apply hp.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f s
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_generator_coercive a i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]
  let C₀ := u4QuantGradientConstant d Λ ‖ζ‖ 0 τ
  have hC₀ := u4Quant_forward_D2_gradient_at_time a i ζ ha hΛ hA P hP τ hτ
  change ∀ f g h, _ → _ → ‖_‖ ^ 2 ≤ (Real.exp (L * (τ : ℝ)) ^ 2 *
    (Λ * C₀ + (K * Λ * (d : ℝ) *
      ((1 / 2 + L * (Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ))) / μ) +
        J * Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ)) *
          Real.exp (L * (τ : ℝ)) ^ 2) / (3 * (τ : ℝ))) * ‖f‖ ^ 2
  intro f g h hfg hgh
  have hfg' := hp.map_gen hfg τ
  have hgh' := hp.map_gen hgh τ
  obtain ⟨G, hG, hGc, hdiss⟩ := c18_physical_D2_integrated_generator a i ζ ha hΛ hA P hP hfg' hgh'
  obtain ⟨H, hH, _, henergy⟩ := c18_physical_orbit_integrated_gradient a i ζ ha hΛ hA P hP hfg'
  have heq : (∫ s in (0 : ℝ)..(τ : ℝ), ∑ j, ‖G s j‖ ^ 2) =
      ∫ s in (0 : ℝ)..(τ : ℝ), ∑ j, ‖H s j‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := (Set.uIcc_of_le τ.property ▸ hs).1
    dsimp only
    rw [physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (P s.toNNReal (P τ f)) (G s) (H s) (hG s hs') (hH s)]
  obtain ⟨V, hV, hbV⟩ := hC₀ f g h hfg hgh
  have hz : G 0 = V := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (P τ f) (G 0) V
    (by simpa only [Real.toNNReal_zero, hp.zero, ContinuousLinearMap.id_apply]
      using hG 0 le_rfl) hV
  have hzero : (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * G 0 k x * star (G 0 j x)).re ≤ (Λ * C₀) * ‖f‖ ^ 2 := by
    rw [hz]
    exact (c18_physical_principal_energy_upper a ha hA V).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbV hΛ.le)
  have hdatum : ‖P τ f‖ ^ 2 ≤ Real.exp (L * (τ : ℝ)) ^ 2 * ‖f‖ ^ 2 :=
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hgrowth f τ)).trans_eq
      (mul_pow _ _ _)
  have hb := u4Quant_generator_endpoint_from_dissipation a ha hΛ hA hp
    μ L K J 3 (Λ * C₀) (Real.exp (L * (τ : ℝ)) ^ 2)
    hμ hL hK hJ (by norm_num) hgrowth f (P τ f) (P τ g) G hGc τ hτ
    (by rw [heq]; exact henergy τ) hzero hdatum
    (by simpa only [J, K, zero_mul, add_zero] using hdiss τ)
  have htcomp : P τ (P τ g) = P t g := by
    rw [← ContinuousLinearMap.comp_apply, ← hp.add, hττ]
  rwa [htcomp] at hb

/-- A half-time split removes all dependence on the initial generator image
from the actual transpose twice-domain generator endpoint bound. -/
theorem u4Quant_transpose_D2_generator_at_time
    {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hsmooth : IsSmoothWithBounds M ω) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag) (t : ℝ≥0) (ht : 0 < t) :
    ∀ f g h : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g →
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h →
      ‖Pdag t g‖ ^ 2 ≤ u4QuantGeneratorConstant d Λ ‖ζ‖ (4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2) 2 t * ‖f‖ ^ 2 := by
  let hp : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  let τ : ℝ≥0 := t / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hττ : τ + τ = t := add_halves t
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * ‖ζ‖ ^ 2
  let J : ℝ := 4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hgrowth : ∀ f s, ‖Pdag s f‖ ≤ Real.exp (L * (s : ℝ)) * ‖f‖ := by
    intro f s
    apply hp.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f s
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_transpose_generator_coercive ω.1 i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]
  let C₀ := u4QuantGradientConstant d Λ ‖ζ‖ J τ
  have hC₀ := u4Quant_transpose_D2_gradient_at_time hsmooth i ζ ha hΛ hA P Pdag hPdag τ hτ
  change ∀ f g h, _ → _ → ‖_‖ ^ 2 ≤ (Real.exp (L * (τ : ℝ)) ^ 2 *
    (Λ * C₀ + (K * Λ * (d : ℝ) *
      ((1 / 2 + L * (Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ))) / μ) +
        J * Real.exp (L * (τ : ℝ)) ^ 2 * (τ : ℝ)) *
          Real.exp (L * (τ : ℝ)) ^ 2) / (2 * (τ : ℝ))) * ‖f‖ ^ 2
  intro f g h hfg hgh
  have hfg' := hp.map_gen hfg τ
  have hgh' := hp.map_gen hgh τ
  obtain ⟨G, hG, hGc, hdiss⟩ := c18_physical_transpose_D2_integrated_generator hsmooth i ζ ha hΛ hA P Pdag hPdag hfg' hgh'
  obtain ⟨H, hH, _, henergy⟩ := c18_physical_transpose_orbit_integrated_gradient ω.1 i ζ ha hΛ hA P Pdag hPdag hfg'
  have heq : (∫ s in (0 : ℝ)..(τ : ℝ), ∑ j, ‖G s j‖ ^ 2) =
      ∫ s in (0 : ℝ)..(τ : ℝ), ∑ j, ‖H s j‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := (Set.uIcc_of_le τ.property ▸ hs).1
    dsimp only
    rw [physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (Pdag s.toNNReal (Pdag τ f)) (G s) (H s) (hG s hs') (hH s)]
  obtain ⟨V, hV, hbV⟩ := hC₀ f g h hfg hgh
  have hz : G 0 = V := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (Pdag τ f) (G 0) V
    (by simpa only [Real.toNNReal_zero, hp.zero, ContinuousLinearMap.id_apply]
      using hG 0 le_rfl) hV
  have hzero : (∫ x, ∑ j, ∑ k,
      (ω.1 x j k : ℂ) * G 0 k x * star (G 0 j x)).re ≤ (Λ * C₀) * ‖f‖ ^ 2 := by
    rw [hz]
    exact (c18_physical_principal_energy_upper ω.1 ha hA V).trans
      (by simpa only [C₀, J, mul_assoc] using mul_le_mul_of_nonneg_left hbV hΛ.le)
  have hdatum : ‖Pdag τ f‖ ^ 2 ≤ Real.exp (L * (τ : ℝ)) ^ 2 * ‖f‖ ^ 2 :=
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hgrowth f τ)).trans_eq
      (mul_pow _ _ _)
  have hb := u4Quant_generator_endpoint_from_dissipation ω.1 ha hΛ hA hp
    μ L K J 2 (Λ * C₀) (Real.exp (L * (τ : ℝ)) ^ 2)
    hμ hL hK hJ (by norm_num) hgrowth f (Pdag τ f) (Pdag τ g) G hGc τ hτ
    (by rw [heq]; exact henergy τ) hzero hdatum
    (by simpa only [J, K, zero_mul, add_zero] using hdiss τ)
  have htcomp : Pdag τ (Pdag τ g) = Pdag t g := by
    rw [← ContinuousLinearMap.comp_apply, ← hp.add, hττ]
  rwa [htcomp] at hb



/-- The explicit endpoint constants have a common bound on the signed force ball. -/
theorem u4Quant_generator_constant_force_uniform
    (d : ℕ) (Λ κ ν : ℝ) (t : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 4 →
      u4QuantGeneratorConstant d Λ s (κ * s ^ 2) ν t ≤ C := by
  have hc : Continuous (fun s : ℝ =>
      u4QuantGeneratorConstant d Λ s (κ * s ^ 2) ν t) := by
    dsimp only [u4QuantGeneratorConstant, u4QuantGradientConstant]
    simp only [div_eq_mul_inv, mul_inv_rev, ← Real.exp_neg]
    fun_prop
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 4)) hc.continuousOn
  refine ⟨max 0 (u4QuantGeneratorConstant d Λ s₀ (κ * s₀ ^ 2) ν t),
    le_max_left _ _, ?_⟩
  intro s hs hs4
  exact (hmax ⟨hs, hs4⟩).trans (le_max_right _ _)

/-- Iterating a semigroup endpoint estimate along a finite generator chain. -/
theorem u4Quant_semigroup_chain_endpoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (τ : ℝ≥0) (B : ℝ) (hB : 0 ≤ B)
    (hendpoint : ∀ f g h, Gen f g → Gen g h → ‖P τ g‖ ≤ B * ‖f‖) :
    ∀ (n : ℕ) (u : ℕ → E), (∀ k ≤ n, Gen (u k) (u (k + 1))) →
      ‖P (n • τ) (u n)‖ ≤ B ^ n * ‖u 0‖ := by
  intro n
  induction n with
  | zero =>
      intro u _
      simp [hP.zero]
  | succ n ih =>
      intro u hchain
      have hfg := hP.map_gen (hchain n (by omega)) (n • τ)
      have hgh := hP.map_gen (hchain (n + 1) (by omega)) (n • τ)
      have hb := hendpoint _ _ _ hfg hgh
      have hc : P τ (P (n • τ) (u (n + 1))) = P ((n + 1) • τ) (u (n + 1)) := by
        have ht : τ + n • τ = (n + 1) • τ := by
          simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          ring
        rw [← ContinuousLinearMap.comp_apply, ← hP.add, ht]
      rw [hc] at hb
      calc
        _ ≤ B * ‖P (n • τ) (u n)‖ := hb
        _ ≤ B * (B ^ n * ‖u 0‖) :=
          mul_le_mul_of_nonneg_left (ih u (fun k hk => hchain k (by omega))) hB
        _ = B ^ (n + 1) * ‖u 0‖ := by rw [pow_succ]; ring

#print axioms u4Quant_semigroup_chain_endpoint

/-- A common endpoint factor controls both physical generator orientations. -/
theorem u4Quant_physical_generator_endpoint_force_uniform
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} (hΛ : 0 < Λ) (τ : ℝ≥0) (hτ : 0 < τ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
      (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
      (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
      (hsmooth : IsSmoothWithBounds M ω) (hζ : ‖ζ‖ ≤ 4)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag),
      (∀ f g h, IsPhysicalComplexGeneratorPair ω.1 i ζ f g →
        IsPhysicalComplexGeneratorPair ω.1 i ζ g h → ‖P τ g‖ ≤ B * ‖f‖) ∧
      (∀ f g h, IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g →
        IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h → ‖Pdag τ g‖ ≤ B * ‖f‖) := by
  obtain ⟨C₀, hC₀, hforward⟩ := u4Quant_generator_constant_force_uniform d Λ 0 3 τ
  obtain ⟨C₁, hC₁, htranspose⟩ := u4Quant_generator_constant_force_uniform d Λ
    (4 * ((d : ℝ) * M 1) ^ 2) 2 τ
  let C := max C₀ C₁
  let B := max 1 (Real.sqrt C)
  have hC : 0 ≤ C := le_trans hC₀ (le_max_left _ _)
  have hB : 1 ≤ B := le_max_left _ _
  have hBC : C ≤ B ^ 2 := by
    have hs := Real.sq_sqrt hC
    have hb := le_max_right 1 (Real.sqrt C)
    have hs0 := Real.sqrt_nonneg C
    nlinarith
  refine ⟨B, hB, ?_⟩
  intro ω i ζ ha hA hsmooth hζ P Pdag hP hPdag
  constructor
  · intro f g h hfg hgh
    have he := u4Quant_forward_D2_generator_at_time ω.1 i ζ ha hΛ hA P hP τ hτ f g h hfg hgh
    have hc := hforward ‖ζ‖ (norm_nonneg ζ) hζ
    have hc' : u4QuantGeneratorConstant d Λ ‖ζ‖ 0 3 τ ≤ C := by
      have hc₀ : u4QuantGeneratorConstant d Λ ‖ζ‖ 0 3 τ ≤ C₀ := by
        simpa using hc
      exact hc₀.trans (le_max_left _ _)
    have hs : ‖P τ g‖ ^ 2 ≤ C * ‖f‖ ^ 2 :=
      he.trans (mul_le_mul_of_nonneg_right hc' (sq_nonneg _))
    have hh : 0 ≤ B * ‖f‖ := mul_nonneg (by linarith) (norm_nonneg f)
    nlinarith [norm_nonneg (P τ g), mul_nonneg (sub_nonneg.mpr hBC) (sq_nonneg ‖f‖)]
  · intro f g h hfg hgh
    have he := u4Quant_transpose_D2_generator_at_time hsmooth i ζ ha hΛ hA P Pdag hPdag τ hτ f g h hfg hgh
    have hc := htranspose ‖ζ‖ (norm_nonneg ζ) hζ
    have hc' : u4QuantGeneratorConstant d Λ ‖ζ‖
        (4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2) 2 τ ≤ C :=
      hc.trans (le_max_right _ _)
    have hs : ‖Pdag τ g‖ ^ 2 ≤ C * ‖f‖ ^ 2 :=
      he.trans (mul_le_mul_of_nonneg_right hc' (sq_nonneg _))
    have hh : 0 ≤ B * ‖f‖ := mul_nonneg (by linarith) (norm_nonneg f)
    nlinarith [norm_nonneg (Pdag τ g), mul_nonneg (sub_nonneg.mpr hBC) (sq_nonneg ‖f‖)]

#print axioms u4Quant_physical_generator_endpoint_force_uniform

/-- Extra time after the iterated generator steps is controlled by semigroup growth. -/
theorem u4Quant_semigroup_chain_common_time
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (τ : ℝ≥0) (B L : ℝ) (hB : 0 ≤ B)
    (hendpoint : ∀ f g h, Gen f g → Gen g h → ‖P τ g‖ ≤ B * ‖f‖)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖)
    (n k : ℕ) (u : ℕ → E) (hchain : ∀ j ≤ n, Gen (u j) (u (j + 1))) :
    ‖P ((n + k) • τ) (u n)‖ ≤
      Real.exp (L * ((k • τ : ℝ≥0) : ℝ)) * B ^ n * ‖u 0‖ := by
  have hb := u4Quant_semigroup_chain_endpoint hP τ B hB hendpoint n u hchain
  have hcomp : P ((n + k) • τ) (u n) = P (k • τ) (P (n • τ) (u n)) := by
    rw [add_nsmul, add_comm, hP.add, ContinuousLinearMap.comp_apply]
  rw [hcomp]
  calc
    _ ≤ Real.exp (L * ((k • τ : ℝ≥0) : ℝ)) * ‖P (n • τ) (u n)‖ := hgrowth _ _
    _ ≤ Real.exp (L * ((k • τ : ℝ≥0) : ℝ)) * (B ^ n * ‖u 0‖) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = _ := by ring

#print axioms u4Quant_semigroup_chain_common_time

/-- Mapping a finite generator chain by a common semigroup time preserves the
relations and bounds each generator image. -/
theorem u4Quant_mapped_generator_chain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (τ : ℝ≥0) (B L : ℝ) (hB : 0 ≤ B)
    (hendpoint : ∀ f g h, Gen f g → Gen g h → ‖P τ g‖ ≤ B * ‖f‖)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖)
    (n m : ℕ) (hm : n ≤ m) (u : ℕ → E)
    (hchain : ∀ j ≤ n, Gen (u j) (u (j + 1))) :
    (∀ j ≤ n, Gen (P (m • τ) (u j)) (P (m • τ) (u (j + 1)))) ∧
    (∀ j ≤ n, ‖P (m • τ) (u j)‖ ≤
      Real.exp (L * (((m - j) • τ : ℝ≥0) : ℝ)) * B ^ j * ‖u 0‖) := by
  constructor
  · intro j hj
    exact hP.map_gen (hchain j hj) (m • τ)
  · intro j hj
    have hjm : j ≤ m := le_trans hj hm
    have h := u4Quant_semigroup_chain_common_time hP τ B L hB hendpoint hgrowth
      j (m - j) u (fun k hk => hchain k (le_trans hk hj))
    simpa only [Nat.add_sub_of_le hjm] using h

#print axioms u4Quant_mapped_generator_chain


/-- The generator endpoint constant after removing its two small-time poles. -/
noncomputable def u4QuantRegularizedGeneratorConstant
    (d : ℕ) (Λ κ ν s t : ℝ) : ℝ :=
  let τ := t / 2
  let μ := 1 / (4 * Λ)
  let L := (d : ℝ) * Λ ^ 3 * s ^ 2
  let K := 4 * ((d : ℝ) + 1) * Λ ^ 3 * s ^ 2
  let J := κ * s ^ 2
  let E := Real.exp (L * τ) ^ 2
  E * (Λ ^ 2 * (Λ * (d : ℝ) * ((1 / 2 + L * E * τ) / μ) +
    J * E * τ ^ 2) * Real.exp (K * τ) +
    τ * (K * Λ * (d : ℝ) * ((1 / 2 + L * E * τ) / μ) +
      J * E * τ) * E) / ν

/-- The regularized endpoint expression is continuous through time zero. -/
theorem u4Quant_regularized_generator_continuous (d : ℕ) (Λ κ ν : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      u4QuantRegularizedGeneratorConstant d Λ κ ν p.1 p.2) := by
  dsimp only [u4QuantRegularizedGeneratorConstant]
  simp only [div_eq_mul_inv]
  fun_prop

/-- The regularized expression equals the original endpoint constant times
half-time squared, at strictly positive time. -/
theorem u4Quant_regularized_generator_eq (d : ℕ) (Λ κ ν s : ℝ)
    (hν : ν ≠ 0) (t : ℝ≥0) (ht : 0 < t) :
    ((t : ℝ) / 2) ^ 2 * u4QuantGeneratorConstant d Λ s (κ * s ^ 2) ν t =
      u4QuantRegularizedGeneratorConstant d Λ κ ν s t := by
  have ht0 : (t : ℝ) ≠ 0 := by positivity
  have ht' : (t : ℝ) / 2 ≠ 0 := by positivity
  dsimp [u4QuantGeneratorConstant, u4QuantGradientConstant,
    u4QuantRegularizedGeneratorConstant]
  simp only [NNReal.coe_div, NNReal.coe_ofNat, div_eq_mul_inv, mul_inv_rev,
    ← Real.exp_neg, neg_mul, neg_neg]
  field_simp [hν, ht0, ht', Real.exp_ne_zero]
  <;> ring

#print axioms u4Quant_regularized_generator_eq

/-- On the force ball and small-time interval, the endpoint constant has at
most a quadratic reciprocal-time singularity. -/
theorem u4Quant_generator_constant_small_time
    (d : ℕ) (Λ κ ν : ℝ) (hν : ν ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ), 0 ≤ s → s ≤ 4 →
      ∀ (t : ℝ≥0), 0 < t → (t : ℝ) ≤ 1 →
      ((t : ℝ) / 2) ^ 2 *
        u4QuantGeneratorConstant d Λ s (κ * s ^ 2) ν t ≤ C := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 4 ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hn : K.Nonempty := ⟨(0, 0), by simp [K]⟩
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hn
    (u4Quant_regularized_generator_continuous d Λ κ ν).continuousOn
  refine ⟨max 0 (u4QuantRegularizedGeneratorConstant d Λ κ ν p.1 p.2),
    le_max_left _ _, ?_⟩
  intro s hs hs4 t ht ht1
  rw [u4Quant_regularized_generator_eq d Λ κ ν s hν t ht]
  exact (hmax (show (s, (t : ℝ)) ∈ K from ⟨⟨hs, hs4⟩, ⟨t.property, ht1⟩⟩)).trans
    (le_max_right _ _)

#print axioms u4Quant_generator_constant_small_time

#print axioms u4Quant_regularized_generator_continuous


/-- Convert a quadratic endpoint estimate to its reciprocal-time norm bound. -/
theorem u4Quant_sqrt_endpoint_bound (a b G C B t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) (hB : 0 ≤ B)
    (hG : (t / 2) ^ 2 * G ≤ C) (hC : C ≤ B ^ 2)
    (he : a ^ 2 ≤ G * b ^ 2) :
    a ≤ (2 * B / t) * b := by
  have hp : 0 ≤ (t / 2) * a := mul_nonneg (by positivity) ha
  have hq : 0 ≤ B * b := mul_nonneg hB hb
  have h1 := mul_le_mul_of_nonneg_left he (sq_nonneg (t / 2))
  have h2 := mul_le_mul_of_nonneg_right hG (sq_nonneg b)
  have h3 := mul_le_mul_of_nonneg_right hC (sq_nonneg b)
  have h4 : (t / 2) * a ≤ B * b := by nlinarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ht).mpr
  nlinarith

#print axioms u4Quant_sqrt_endpoint_bound

/-- A force-uniform reciprocal-time endpoint bound for both orientations. -/
theorem u4Quant_physical_generator_endpoint_small_time
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} (hΛ : 0 < Λ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
      (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
      (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
      (hsmooth : IsSmoothWithBounds M ω) (hζ : ‖ζ‖ ≤ 4)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
      (τ : ℝ≥0) (hτ : 0 < τ) (hτ1 : (τ : ℝ) ≤ 1),
      (∀ f g h, IsPhysicalComplexGeneratorPair ω.1 i ζ f g →
        IsPhysicalComplexGeneratorPair ω.1 i ζ g h → ‖P τ g‖ ≤ (2 * B / (τ : ℝ)) * ‖f‖) ∧
      (∀ f g h, IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g →
        IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h → ‖Pdag τ g‖ ≤ (2 * B / (τ : ℝ)) * ‖f‖) := by
  obtain ⟨C₀, hC₀, hforward⟩ := u4Quant_generator_constant_small_time d Λ 0 3 (by norm_num)
  obtain ⟨C₁, hC₁, htranspose⟩ := u4Quant_generator_constant_small_time d Λ
    (4 * ((d : ℝ) * M 1) ^ 2) 2 (by norm_num)
  let C := max C₀ C₁
  let B := max 1 (Real.sqrt C)
  have hC : 0 ≤ C := le_trans hC₀ (le_max_left _ _)
  have hB : 1 ≤ B := le_max_left _ _
  have hBC : C ≤ B ^ 2 := by
    have hs := Real.sq_sqrt hC
    have hb := le_max_right 1 (Real.sqrt C)
    have hs0 := Real.sqrt_nonneg C
    nlinarith
  refine ⟨B, hB, ?_⟩
  intro ω i ζ ha hA hsmooth hζ P Pdag hP hPdag τ hτ hτ1
  have ht : (0 : ℝ) < τ := hτ
  constructor
  · intro f g h hfg hgh
    have he := u4Quant_forward_D2_generator_at_time ω.1 i ζ ha hΛ hA P hP τ hτ f g h hfg hgh
    have hc := hforward ‖ζ‖ (norm_nonneg ζ) hζ τ hτ hτ1
    have hc' : ((τ : ℝ) / 2) ^ 2 * u4QuantGeneratorConstant d Λ ‖ζ‖ 0 3 τ ≤ C := by
      have hc₀ : ((τ : ℝ) / 2) ^ 2 * u4QuantGeneratorConstant d Λ ‖ζ‖ 0 3 τ ≤ C₀ := by
        simpa using hc
      exact hc₀.trans (le_max_left _ _)
    exact u4Quant_sqrt_endpoint_bound _ _ _ C B τ (norm_nonneg _) (norm_nonneg _) ht
      (by linarith) hc' hBC he
  · intro f g h hfg hgh
    have he := u4Quant_transpose_D2_generator_at_time hsmooth i ζ ha hΛ hA P Pdag hPdag τ hτ f g h hfg hgh
    have hc := htranspose ‖ζ‖ (norm_nonneg ζ) hζ τ hτ hτ1
    have hc' : ((τ : ℝ) / 2) ^ 2 * u4QuantGeneratorConstant d Λ ‖ζ‖
        (4 * ((d : ℝ) * M 1) ^ 2 * ‖ζ‖ ^ 2) 2 τ ≤ C :=
      hc.trans (le_max_right _ _)
    exact u4Quant_sqrt_endpoint_bound _ _ _ C B τ (norm_nonneg _) (norm_nonneg _) ht
      (by linarith) hc' hBC he

#print axioms u4Quant_physical_generator_endpoint_small_time

/-- All mapped images in a finite chain share one time-growth bound. -/
theorem u4Quant_mapped_generator_chain_uniform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (τ : ℝ≥0) (B L : ℝ) (hB : 1 ≤ B) (hL : 0 ≤ L)
    (hendpoint : ∀ f g h, Gen f g → Gen g h → ‖P τ g‖ ≤ B * ‖f‖)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖)
    (n m : ℕ) (hm : n ≤ m) (u : ℕ → E)
    (hchain : ∀ j ≤ n, Gen (u j) (u (j + 1))) :
    ∀ j ≤ n, ‖P (m • τ) (u j)‖ ≤
      Real.exp (L * ((m • τ : ℝ≥0) : ℝ)) * B ^ n * ‖u 0‖ := by
  obtain ⟨_, hbound⟩ := u4Quant_mapped_generator_chain hP τ B L (by linarith)
    hendpoint hgrowth n m hm u hchain
  intro j hj
  have hres : (((m - j) • τ : ℝ≥0) : ℝ) ≤ ((m • τ : ℝ≥0) : ℝ) := by
    exact_mod_cast (nsmul_le_nsmul_left (show (0 : ℝ≥0) ≤ τ from bot_le) (Nat.sub_le m j))
  have he : Real.exp (L * (((m - j) • τ : ℝ≥0) : ℝ)) ≤
      Real.exp (L * ((m • τ : ℝ≥0) : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hres hL)
  have hp : B ^ j ≤ B ^ n := pow_le_pow_right₀ hB hj
  calc
    _ ≤ Real.exp (L * (((m - j) • τ : ℝ≥0) : ℝ)) * B ^ j * ‖u 0‖ := hbound j hj
    _ ≤ Real.exp (L * ((m • τ : ℝ≥0) : ℝ)) * B ^ n * ‖u 0‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul he hp (pow_nonneg (by linarith) _) (Real.exp_nonneg _)) (norm_nonneg _)

#print axioms u4Quant_mapped_generator_chain_uniform

/-- Both physical semigroups obey the same explicit force-dependent L² growth bound. -/
theorem u4Quant_physical_semigroup_growth
    {d : ℕ} {Λ : ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 0 < Λ)
    (ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume)
    (hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag) :
    ∀ f t, ‖P t f‖ ≤ Real.exp (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * (t : ℝ)) * ‖f‖ ∧
      ‖Pdag t f‖ ≤ Real.exp (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * (t : ℝ)) * ‖f‖ := by
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let μ := 1 / (4 * Λ)
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair ω.1 i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  let hpd : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  intro f t
  constructor
  · apply hp.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f t
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_generator_coercive ω.1 i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]
  · apply hpd.weighted_growth (ContinuousLinearMap.id ℂ _) L ?_ f t
    intro u v huv
    obtain ⟨G, _, hc⟩ := c18_physical_transpose_generator_coercive ω.1 i ζ ha hΛ hA huv
    have hn : 0 ≤ μ * ∑ j, ‖G j‖ ^ 2 := by positivity
    simp only [ContinuousLinearMap.id_apply]
    dsimp [μ] at hn
    dsimp [L]
    linarith only [hc, hn]

#print axioms u4Quant_physical_semigroup_growth

/-- A finite generator chain remains a bounded chain after a common time step. -/
theorem u4Quant_finite_mapped_chain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (τ : ℝ≥0) (B L : ℝ) (hB : 1 ≤ B) (hL : 0 ≤ L)
    (hendpoint : ∀ f g h, Gen f g → Gen g h → ‖P τ g‖ ≤ B * ‖f‖)
    (hgrowth : ∀ f t, ‖P t f‖ ≤ Real.exp (L * (t : ℝ)) * ‖f‖)
    (n : ℕ) (u : Fin (n + 3) → E)
    (hchain : ∀ k : Fin (n + 2), Gen (u k.castSucc) (u k.succ)) :
    ∃ v : ℕ → E,
      v 0 = P ((n + 1) • τ) (u 0) ∧
      (∀ k ≤ n, Gen (v k) (v (k + 1))) ∧
      (∀ k ≤ n + 1, ‖v k‖ ≤
        Real.exp (L * (((n + 1) • τ : ℝ≥0) : ℝ)) * B ^ (n + 1) * ‖u 0‖) := by
  let w : ℕ → E := fun k => u ⟨min k (n + 2), by omega⟩
  have hw : ∀ k ≤ n + 1, Gen (w k) (w (k + 1)) := by
    intro k hk
    let q : Fin (n + 2) := ⟨k, by omega⟩
    have hq0 : q.castSucc = (⟨k, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    have hq1 : q.succ = (⟨k + 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    have hc := hchain q
    rw [hq0, hq1] at hc
    simpa [w, Nat.min_eq_left (show k ≤ n + 2 by omega),
      Nat.min_eq_left (show k + 1 ≤ n + 2 by omega)] using hc
  let v : ℕ → E := fun k => P ((n + 1) • τ) (w k)
  have hb := u4Quant_mapped_generator_chain_uniform hP τ B L hB hL hendpoint hgrowth
    (n + 1) (n + 1) le_rfl w hw
  refine ⟨v, ?_, ?_, ?_⟩
  · simp [v, w]
  · intro k hk
    exact hP.map_gen (hw k (by omega)) ((n + 1) • τ)
  · intro k hk
    simpa [v, w] using hb k hk

#print axioms u4Quant_finite_mapped_chain

/-- Quantitative derivative families for both physical semigroups after splitting
positive time into a regularizing start and equal generator steps. -/
theorem u4Quant_physical_split_time_derivatives {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (A : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    ∃ C B : ℝ, 1 ≤ C ∧ 1 ≤ B ∧ ∀ {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (hζ : ‖ζ‖ ≤ 4) (hM : ∀ k ≤ n + 2, M k ≤ A)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
      (f : Lp ℂ 2 (volume : Measure (Vec d))) (s τ : ℝ≥0)
      (hs : 0 < s) (hτ : 0 < τ) (hτ1 : (τ : ℝ) ≤ 1),
      ∃ F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
        F [] = P (s + (n + 1) • τ) f ∧ J [] = Pdag (s + (n + 1) • τ) f ∧
        (∀ path, path.length < n + 2 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F path) (fun j => F (path ++ [j]))) ∧
        (∀ path, path.length < n + 2 → IsPhysicalH1Graph volume (Or.inl rfl)
          (J path) (fun j => J (path ++ [j]))) ∧
        (∀ path, path.length ≤ n + 2 → ‖F path‖ ≤
          C * (Real.exp (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * (((n + 1) • τ : ℝ≥0) : ℝ)) *
            (2 * B / (τ : ℝ)) ^ (n + 1) *
            (Real.exp (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * (s : ℝ)) * ‖f‖))) ∧
        (∀ path, path.length ≤ n + 2 → ‖J path‖ ≤
          C * (Real.exp (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * (((n + 1) • τ : ℝ≥0) : ℝ)) *
            (2 * B / (τ : ℝ)) ^ (n + 1) *
            (Real.exp (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * (s : ℝ)) * ‖f‖))) := by
  obtain ⟨C, hC, hder⟩ := u4Higher_generator_chain_uniform_derivatives
    (M := M) (d := d) hΛ A 4 hA n
  obtain ⟨B, hB, hend⟩ := u4Quant_physical_generator_endpoint_small_time
    (M := M) (d := d) (lt_of_lt_of_le zero_lt_one hΛ)
  refine ⟨C, B, hC, hB, ?_⟩
  intro ω i ζ hell hsmooth hζ hM P Pdag hP hPdag f s τ hs hτ hτ1
  let L := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let K := 2 * B / (τ : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hτr : (0 : ℝ) < τ := hτ
  have hK : 1 ≤ K := by
    dsimp [K]
    apply (le_div_iff₀ hτr).mpr
    nlinarith
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hAe : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  let hp : S5Semigroup P (IsPhysicalComplexGeneratorPair ω.1 i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  let hpd : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ) :=
    ⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩
  have hg := u4Quant_physical_semigroup_growth (lt_of_lt_of_le zero_lt_one hΛ)
    ha hAe P Pdag hP hPdag
  have he := hend ha hAe hsmooth hζ P Pdag hP hPdag τ hτ hτ1
  obtain ⟨u, v, hu, hv, hchain⟩ :=
    c18_physical_positive_time_generator_chains hΛ hell hsmooth hP hPdag (n + 2) f s hs
  obtain ⟨u', hu', huchain, hub⟩ := u4Quant_finite_mapped_chain hp τ K L hK hL
    he.1 (fun f t => (hg f t).1) n u (fun k => (hchain k).1)
  obtain ⟨v', hv', hvchain, hvb⟩ := u4Quant_finite_mapped_chain hpd τ K L hK hL
    he.2 (fun f t => (hg f t).2) n v (fun k => (hchain k).2)
  let R := Real.exp (L * (((n + 1) • τ : ℝ≥0) : ℝ)) * K ^ (n + 1) *
    (Real.exp (L * (s : ℝ)) * ‖f‖)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hub' : ∀ k ≤ n + 1, ‖u' k‖ ≤ R := by
    intro k hk
    apply (hub k hk).trans
    rw [hu]
    exact mul_le_mul_of_nonneg_left (hg f s).1 (by positivity)
  have hvb' : ∀ k ≤ n + 1, ‖v' k‖ ≤ R := by
    intro k hk
    apply (hvb k hk).trans
    rw [hv]
    exact mul_le_mul_of_nonneg_left (hg f s).2 (by positivity)
  obtain ⟨F, hF0, hF, hFb⟩ := hder hell hsmooth hζ hM u' R hR
    (fun k hk => Or.inl (huchain k hk)) hub'
  obtain ⟨J, hJ0, hJ, hJb⟩ := hder hell hsmooth hζ hM v' R hR
    (fun k hk => Or.inr (hvchain k hk)) hvb'
  refine ⟨F, J, ?_, ?_, hF, hJ, ?_, ?_⟩
  · rw [hF0, hu', hu, ← ContinuousLinearMap.comp_apply, ← hp.add, add_comm]
  · rw [hJ0, hv', hv, ← ContinuousLinearMap.comp_apply, ← hpd.add, add_comm]
  · simpa [R, K, L] using hFb
  · simpa [R, K, L] using hJb

#print axioms u4Quant_physical_split_time_derivatives

/-- Split every positive time into a positive initial interval and equal short
steps, with reciprocal step size controlled by the reciprocal total time. -/
theorem u4Quant_positive_time_partition (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    ∃ s τ : ℝ≥0, 0 < s ∧ 0 < τ ∧ (τ : ℝ) ≤ 1 ∧
      s + (n + 1) • τ = t ∧
      (τ : ℝ)⁻¹ = (2 * ((n : ℝ) + 2)) * (1 + (t : ℝ)⁻¹) := by
  let τ : ℝ≥0 := t / (2 * ((n : ℝ≥0) + 2) * (1 + t))
  let D : ℝ := 2 * ((n : ℝ) + 2) * (1 + (t : ℝ))
  have ht' : (0 : ℝ) < t := ht
  have hD : 0 < D := by dsimp [D]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτeq : (τ : ℝ) = (t : ℝ) / D := by
    simp [τ, D]
  have hDgt : ((n : ℝ) + 1) < D := by
    dsimp [D]
    nlinarith [mul_nonneg (Nat.cast_nonneg n) ht'.le]
  have hτ1 : (τ : ℝ) ≤ 1 := by
    rw [hτeq, div_le_one hD]
    dsimp [D]
    nlinarith [mul_nonneg (Nat.cast_nonneg n) ht'.le]
  have hsmall' : (((n + 1) • τ : ℝ≥0) : ℝ) < (t : ℝ) := by
    simp only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add,
      Nat.cast_one, hτeq, ← mul_div_assoc, div_lt_iff₀ hD]
    norm_num only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast]
    nlinarith [mul_lt_mul_of_pos_right hDgt ht']
  have hsmall : (n + 1) • τ < t := by exact_mod_cast hsmall'
  let s : ℝ≥0 := t - (n + 1) • τ
  have hs : 0 < s := by dsimp [s]; exact tsub_pos_iff_lt.mpr hsmall
  refine ⟨s, τ, hs, hτ, hτ1, ?_, ?_⟩
  · dsimp [s]
    exact tsub_add_cancel_of_le hsmall.le
  · rw [hτeq, inv_div]
    dsimp [D]
    field_simp [ne_of_gt ht']
    <;> ring

#print axioms u4Quant_positive_time_partition

/-- Absorb the time partition into a reciprocal-time polynomial and one
force-dependent exponential, with a constant independent of time and force. -/
theorem u4Quant_split_bound_algebra (n : ℕ) (C B L z t s r τ : ℝ)
    (hC : 1 ≤ C) (hB : 1 ≤ B) (hz : 0 ≤ z)
    (ht : 0 < t)
    (hsum : s + r = t)
    (hinv : τ⁻¹ = (2 * ((n : ℝ) + 2)) * (1 + t⁻¹)) :
    let K := max 1 (max L (C * (4 * B * ((n : ℝ) + 2)) ^ (n + 1)))
    C * (Real.exp (L * z * r) * (2 * B / τ) ^ (n + 1) *
      Real.exp (L * z * s)) ≤
      K * (1 + t⁻¹) ^ (n + 1) * Real.exp (K * z * t) := by
  dsimp only
  let K := max 1 (max L (C * (4 * B * ((n : ℝ) + 2)) ^ (n + 1)))
  have hK : 1 ≤ K := le_max_left _ _
  have hLK : L ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : C * (4 * B * ((n : ℝ) + 2)) ^ (n + 1) ≤ K :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hexp : Real.exp (L * z * r) * Real.exp (L * z * s) ≤
      Real.exp (K * z * t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      L * z * r + L * z * s = L * z * t := by rw [← hsum]; ring
      _ ≤ K * z * t := by gcongr
  have hfactor : 2 * B / τ = (4 * B * ((n : ℝ) + 2)) * (1 + t⁻¹) := by
    rw [div_eq_mul_inv, hinv]
    ring
  rw [hfactor, mul_pow]
  have hpow : 0 ≤ (1 + t⁻¹) ^ (n + 1) := by positivity
  have hnonneg : 0 ≤ C * (4 * B * ((n : ℝ) + 2)) ^ (n + 1) := by positivity
  calc
    C * (Real.exp (L * z * r) *
        ((4 * B * ((n : ℝ) + 2)) ^ (n + 1) * (1 + t⁻¹) ^ (n + 1)) *
        Real.exp (L * z * s)) =
      (C * (4 * B * ((n : ℝ) + 2)) ^ (n + 1)) * (1 + t⁻¹) ^ (n + 1) *
        (Real.exp (L * z * r) * Real.exp (L * z * s)) := by ring
    _ ≤ K * (1 + t⁻¹) ^ (n + 1) * Real.exp (K * z * t) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hCK hpow) hexp
        (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        (mul_nonneg (by linarith) hpow)

#print axioms u4Quant_split_bound_algebra

/-- Uniform quantitative weak-derivative bounds at every positive time. -/
theorem u4Quant_physical_positive_time_derivatives {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (A : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
      (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
      (hζ : ‖ζ‖ ≤ 4) (hM : ∀ k ≤ n + 2, M k ≤ A)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)))
      (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
      (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
      (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) (ht : 0 < t),
      ∃ F J : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
        F [] = P t f ∧ J [] = Pdag t f ∧
        (∀ path, path.length < n + 2 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F path) (fun j => F (path ++ [j]))) ∧
        (∀ path, path.length < n + 2 → IsPhysicalH1Graph volume (Or.inl rfl)
          (J path) (fun j => J (path ++ [j]))) ∧
        (∀ path, path.length ≤ n + 2 → ‖F path‖ ≤
          C * (1 + (t : ℝ)⁻¹) ^ (n + 1) *
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖) ∧
        (∀ path, path.length ≤ n + 2 → ‖J path‖ ≤
          C * (1 + (t : ℝ)⁻¹) ^ (n + 1) *
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖) := by
  obtain ⟨C, B, hC, hB, hsplit⟩ :=
    u4Quant_physical_split_time_derivatives (M := M) (d := d) hΛ A hA n
  let L : ℝ := (d : ℝ) * Λ ^ 3
  let K : ℝ := max 1 (max L (C * (4 * B * ((n : ℝ) + 2)) ^ (n + 1)))
  have hK : 1 ≤ K := le_max_left _ _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨K, hK, ?_⟩
  intro ω i ζ hell hsmooth hζ hM P Pdag hP hPdag f t ht
  obtain ⟨s, τ, hs, hτ, hτ1, hsum, hinv⟩ := u4Quant_positive_time_partition n t ht
  obtain ⟨F, J, hF0, hJ0, hF, hJ, hFb, hJb⟩ :=
    hsplit hell hsmooth hζ hM P Pdag hP hPdag f s τ hs hτ hτ1
  have halg := u4Quant_split_bound_algebra n C B L (‖ζ‖ ^ 2) t s
    (((n + 1) • τ : ℝ≥0) : ℝ) τ hC hB (sq_nonneg _) ht
    (by exact_mod_cast hsum) hinv
  have hbound : C * (Real.exp (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) *
      (((n + 1) • τ : ℝ≥0) : ℝ)) * (2 * B / (τ : ℝ)) ^ (n + 1) *
      (Real.exp (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * (s : ℝ)) * ‖f‖)) ≤
      K * (1 + (t : ℝ)⁻¹) ^ (n + 1) *
        Real.exp (K * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖ := by
    convert mul_le_mul_of_nonneg_right halg (norm_nonneg f) using 1 <;> dsimp [L, K] <;> ring
  refine ⟨F, J, ?_, ?_, hF, hJ, ?_, ?_⟩
  · rw [hsum] at hF0; exact hF0
  · rw [hsum] at hJ0; exact hJ0
  · intro path hp; exact (hFb path hp).trans hbound
  · intro path hp; exact (hJb path hp).trans hbound

#print axioms u4Quant_physical_positive_time_derivatives

/-- A finite collection of real derivative bounds has a nonnegative common bound. -/
theorem u4Quant_finite_derivative_bound (M : ℕ → ℝ) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k ≤ n, M k ≤ A := by
  induction n with
  | zero =>
      refine ⟨max 0 (M 0), le_max_left _ _, ?_⟩
      intro k hk
      have : k = 0 := by omega
      subst k
      exact le_max_right _ _
  | succ n ih =>
      obtain ⟨A, hA, hM⟩ := ih
      refine ⟨max A (M (n + 1)), hA.trans (le_max_left _ _), ?_⟩
      intro k hk
      by_cases hkn : k ≤ n
      · exact (hM k hkn).trans (le_max_left _ _)
      · have : k = n + 1 := by omega
        subst k
        exact le_max_right _ _

#print axioms u4Quant_finite_derivative_bound

/-- The quantitative derivative bounds hold on one reduced-law event, with
constants fixed before choosing the law and all later parameters. -/
theorem u4Quant_reduced_positive_time_derivatives
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (D : StructuralData d) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      F [] = S t f ∧
      (∀ path, path.length < n + 2 → IsPhysicalH1Graph volume (Or.inl rfl)
        (F path) (fun j => F (path ++ [j]))) ∧
      ∀ path, path.length ≤ n + 2 → ‖F path‖ ≤
        C * (1 + (t : ℝ)⁻¹) ^ (n + 1) *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖ := by
  obtain ⟨Λ, A₀, B₀, hΛ, _, _, _, hell⟩ :=
    Blueprint.node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  obtain ⟨M, _, hsmooth⟩ := hder d D
  obtain ⟨A, hA, hM⟩ := u4Quant_finite_derivative_bound M (n + 2)
  obtain ⟨C, hC, hpositive⟩ :=
    u4Quant_physical_positive_time_derivatives (M := M) (d := d) hΛ A hA n
  refine ⟨C, hC, ?_⟩
  intro Q hQ
  filter_upwards [(hell d D.dependenceRange Q).2.2, hsmooth Q hQ] with ω hω hsω
  intro i ζ hζ P Pdag hP hPdag S hS t ht f
  obtain ⟨F, J, hF0, hJ0, hF, hJ, hFb, hJb⟩ :=
    hpositive hω.1 hsω hζ hM P Pdag hP hPdag f t ht
  simp only [List.mem_cons, List.mem_singleton] at hS
  rcases hS with hS | hS
  · subst S
    exact ⟨F, hF0, hF, hFb⟩
  · simp at hS
    subst S
    exact ⟨J, hJ0, hJ, hJb⟩

#print axioms u4Quant_reduced_positive_time_derivatives

/-- Absorb a Sobolev embedding constant into the target polynomial and growth
constant, uniformly over positive time and the nonnegative force parameter. -/
theorem u4Quant_C1_constant_inflation (K B : ℝ) (hB : 1 ≤ B)
    (N : ℕ) (t z r : ℝ) (ht : 0 < t) (hz : 0 ≤ z) (hr : 0 ≤ r) :
    let C := max B (K * B)
    K * (B * (1 + t⁻¹) ^ N * Real.exp (B * z * t) * r) ≤
      C * (1 + t⁻¹) ^ N * (2 + t) ^ N * Real.exp (C * z * t) * r := by
  dsimp only
  let C := max B (K * B)
  have hBC : B ≤ C := le_max_left _ _
  have hKBC : K * B ≤ C := le_max_right _ _
  have hC : 0 ≤ C := by linarith
  have hp : 0 ≤ (1 + t⁻¹) ^ N := by positivity
  have hpow : 1 ≤ (2 + t) ^ N := one_le_pow₀ (by linarith)
  have hcoeff : (K * B) * (1 + t⁻¹) ^ N ≤
      C * (1 + t⁻¹) ^ N * (2 + t) ^ N := by
    calc
      _ ≤ C * (1 + t⁻¹) ^ N := mul_le_mul_of_nonneg_right hKBC hp
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hC hp) hpow
  have he : Real.exp (B * z * t) ≤ Real.exp (C * z * t) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hz) ht.le
  calc
    K * (B * (1 + t⁻¹) ^ N * Real.exp (B * z * t) * r) =
      ((K * B) * (1 + t⁻¹) ^ N * Real.exp (B * z * t)) * r := by ring
    _ ≤ (C * (1 + t⁻¹) ^ N * (2 + t) ^ N * Real.exp (C * z * t)) * r :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hcoeff he (Real.exp_nonneg _) (by positivity)) hr

/-- A coordinate difference quotient preserves the entire weak derivative chain,
with its norm controlled by the next derivative layer. -/
theorem u4Quant_quotient_derivative_chain {d N : ℕ}
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ p, p.length < N + 1 → IsPhysicalH1Graph volume (Or.inl rfl)
      (F p) (fun j => F (p ++ [j])))
    (j : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ∃ G : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
        (G p) (fun k => G (p ++ [k]))) ∧
      (∀ p, p.length ≤ N → ‖G p‖ ≤ ‖F (p ++ [j])‖) ∧
      (∀ p, (G p : Vec d → ℂ) =ᵐ[volume]
        fun x => (F p (x + h • unitVector j) - F p x) / (h : ℂ)) := by
  classical
  let T : Lp ℂ 2 (volume : Measure (Vec d)) → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun v => (h : ℂ)⁻¹ •
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector j)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector j)) v - v)
  have hT (v : Lp ℂ 2 (volume : Measure (Vec d))) :
      (T v : Vec d → ℂ) =ᵐ[volume]
        fun x => (v (x + h • unitVector j) - v x) / (h : ℂ) := by
    filter_upwards [Lp.coeFn_smul ((h : ℂ)⁻¹)
      (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector j)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector j)) v - v),
      Lp.coeFn_sub (Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector j)
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector j)) v) v,
      Lp.coeFn_compMeasurePreserving v
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector j))] with x ha hb hc
    simp only [T, ha, Pi.smul_apply, hb, Pi.sub_apply, hc, smul_eq_mul,
      div_eq_mul_inv, mul_comm, Function.comp_apply]
  refine ⟨fun p => T (F p), ?_, ?_, fun p => hT (F p)⟩
  · intro p hp
    obtain ⟨q, Q, hqQ, hq, hQ⟩ :=
      u4Higher_forward_H1_quotients [(h • unitVector j, h)] (hF p (by omega))
    simp only [List.map_cons, List.map_nil, u4HigherDifferences] at hq hQ
    have hq' : q = T (F p) := by
      apply Lp.ext
      apply hq.trans
      filter_upwards [(hT (F p)).symm] with x hx
      simpa [u4HigherDifference, div_eq_mul_inv, mul_comm] using hx
    have hQ' : Q = fun k => T (F (p ++ [k])) := by
      funext k
      apply Lp.ext
      apply (hQ k).trans
      filter_upwards [(hT (F (p ++ [k]))).symm] with x hx
      simpa [u4HigherDifference, div_eq_mul_inv, mul_comm] using hx
    simpa only [hq', hQ'] using hqQ
  · intro p hp
    exact c18_physical_H1_Lp_coordinate_difference_quotient_bound (hF p (by omega)) j h hh

/-- A Sobolev representative of a weak derivative chain has pointwise
coordinate derivatives controlled by the common weak norm. -/
theorem u4Quant_sobolev_coordinate_bound {d : ℕ}
    (C R : ℝ) (hR : 0 ≤ R)
    (hSob : ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
      (R : ℝ), 0 ≤ R →
      (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
        (F p) (fun j => F (p ++ [j]))) →
      (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
      ∃ f : BoundedContinuousFunction (Vec d) ℂ,
        ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ p, p.length < d + 4 → IsPhysicalH1Graph volume (Or.inl rfl)
      (F p) (fun j => F (p ++ [j])))
    (hFR : ∀ p, p.length ≤ d + 4 → ‖F p‖ ≤ R)
    (u : BoundedContinuousFunction (Vec d) ℂ) (hu : ContDiff ℝ 1 u)
    (hue : (u : Vec d → ℂ) =ᵐ[volume] F []) :
    ∀ x j, ‖fderiv ℝ (u : Vec d → ℂ) x (unitVector j)‖ ≤ C * R := by
  intro x j
  have hquot (h : ℝ) (hh : h ≠ 0) :
      ‖(u (x + h • unitVector j) - u x) / (h : ℂ)‖ ≤ C * R := by
    obtain ⟨G, hG, hGb, hGe⟩ := u4Quant_quotient_derivative_chain F hF j h hh
    obtain ⟨v, hv, hve, hvb⟩ := hSob G R hR hG (fun p hp =>
      (hGb p hp).trans (hFR (p ++ [j]) (by simp; omega)))
    have he : (v : Vec d → ℂ) = fun y =>
        (u (y + h • unitVector j) - u y) / (h : ℂ) := by
      apply Measure.eq_of_ae_eq (μ := (volume : Measure (Vec d))) _ v.continuous
      · exact ((u.continuous.comp (continuous_id.add continuous_const)).sub u.continuous).div_const _
      · have ht := (measurePreserving_add_right (volume : Measure (Vec d))
          (h • unitVector j)).quasiMeasurePreserving.ae_eq_comp hue
        filter_upwards [hve, hGe [], hue, ht] with y ha hb hc hd
        change u (y + h • unitVector j) = F [] (y + h • unitVector j) at hd
        exact ha.trans (hb.trans (by rw [← hc, ← hd]))
    have hvx := v.norm_coe_le_norm x
    rw [he] at hvx
    exact hvx.trans hvb
  have hd : HasDerivAt (fun t : ℝ => u (x + t • unitVector j))
      (fderiv ℝ (u : Vec d → ℂ) x (unitVector j)) 0 := by
    have hl : HasDerivAt (fun t : ℝ => x + t • unitVector j) (unitVector j) 0 := by
      simpa using (((hasDerivAt_id' (0 : ℝ)).smul_const (unitVector j)).const_add x)
    have hf := (hu.differentiable (by norm_num) x).hasFDerivAt
    have hf' : HasFDerivAt (u : Vec d → ℂ) (fderiv ℝ (u : Vec d → ℂ) x)
        (x + (0 : ℝ) • unitVector j) := by simpa using hf
    simpa only [Function.comp_def] using! hf'.comp_hasDerivAt 0 hl
  have ht := (hasDerivAt_iff_tendsto_slope_zero.mp hd).norm
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hn : h ≠ 0 := by simpa using hh
  simpa only [zero_smul, add_zero, RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_inv, smul_eq_mul, div_eq_mul_inv, mul_comm, zero_add] using! hquot h hn

/-- Conditional all-positive-time C¹ smoothing for both physical evolutions. -/
theorem u4_physical_evolution_L2_C1_of_Sobolev
    (hSobolev : ∀ (d : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∃ f : BoundedContinuousFunction (Vec d) ℂ,
          ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R)
    (_hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (_htime : Blueprint.node_e_u3A_local_u2D_timeStmt)
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < (t : ℝ) →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
      ∀ x : Vec d, ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
        C * (1 + (t : ℝ)⁻¹)^N * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖ := by
  obtain ⟨Cs, hCs, hs⟩ := hSobolev d
  obtain ⟨B, hB, hb⟩ := u4Quant_reduced_positive_time_derivatives hder d D (d + 2)
  let K : ℝ := max 1 (((d : ℝ) + 1) * Cs)
  let C : ℝ := max B (K * B)
  have hK : 1 ≤ K := le_max_left _ _
  have hC : 1 ≤ C := hB.trans (le_max_left _ _)
  refine ⟨C, d + 3, hC, ?_⟩
  intro Q hQ
  filter_upwards [hb Q hQ] with ω hω
  intro i ζ hζ P Pdag hP hPdag S hS t ht f
  have ht' : 0 < t := by exact_mod_cast ht
  obtain ⟨F, hF0, hF, hFb⟩ := hω i ζ hζ P Pdag hP hPdag S hS t ht' f
  let R : ℝ := B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
    Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hF' : ∀ p, p.length < d + 4 → IsPhysicalH1Graph volume (Or.inl rfl)
      (F p) (fun j => F (p ++ [j])) := by
    intro p hp; apply hF; omega
  have hFb' : ∀ p, p.length ≤ d + 4 → ‖F p‖ ≤ R := by
    intro p hp; apply hFb; omega
  obtain ⟨u, hu, hue, hub⟩ := hs F R hR (fun p hp => hF' p (by omega))
    (fun p hp => hFb' p (by omega))
  have hcoord := u4Quant_sobolev_coordinate_bound Cs R hR hs F hF' hFb' u hu hue
  refine ⟨u, hu, ?_, ?_⟩
  · simpa only [hF0] using hue
  · intro x
    have ha : 0 ≤ Cs * R := mul_nonneg hCs.le hR
    have hsums : (∑ j : Fin d, ‖fderiv ℝ (u : Vec d → ℂ) x (unitVector j)‖ ^ 2) ≤
        (d : ℝ) * (Cs * R) ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin d, (Cs * R) ^ 2 := Finset.sum_le_sum (fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hcoord x j) 2)
        _ = _ := by simp
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hsqrt : Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (u : Vec d → ℂ) x (unitVector j)‖ ^ 2) ≤ (d : ℝ) * (Cs * R) := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith [sq_nonneg (Cs * R)]
    have hpoint : ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (u : Vec d → ℂ) x (unitVector j)‖ ^ 2) ≤ K * R := by
      have hv := u.norm_coe_le_norm x
      have hk := le_max_right (1 : ℝ) (((d : ℝ) + 1) * Cs)
      nlinarith [mul_le_mul_of_nonneg_right hk hR]
    exact hpoint.trans (by simpa only [R, C] using
      (u4Quant_C1_constant_inflation K B hB (d + 3) (t : ℝ) (‖ζ‖ ^ 2) ‖f‖
        ht (sq_nonneg _) (norm_nonneg f)))

#print axioms u4_physical_evolution_L2_C1_of_Sobolev

#print axioms u4Quant_sobolev_coordinate_bound

#print axioms u4Quant_quotient_derivative_chain

#print axioms u4Quant_C1_constant_inflation

#print axioms u4Quant_generator_constant_force_uniform

#print axioms u4Quant_forward_D2_generator_at_time
#print axioms u4Quant_transpose_D2_generator_at_time

#print axioms u4Quant_forward_D2_gradient_at_time
#print axioms u4Quant_transpose_D2_gradient_at_time

#print axioms u4Higher_generator_chain_uniform_derivatives

#print axioms u4Higher_generator_pair_uniform_H2_family

#print axioms u4Higher_generator_chain_homogeneous_bound

end


/-- The positive-time polynomial-exponential derivative bound is integrable on compact intervals. -/
theorem u4_positive_time_polynomial_exp_bound_integrable
    (C : ℝ) (N : ℕ) (a ε T : ℝ) (hε : 0 < ε) (hT : ε ≤ T) :
    IntegrableOn (fun t : ℝ => C * (1+t⁻¹)^N * (2+t)^N * Real.exp (a*t))
      (Set.Icc ε T) := by
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc ε T) := by
    apply continuousOn_id.inv₀
    intro t ht
    have hmin : ε ≤ min t T := le_min ht.1 hT
    exact ne_of_gt (lt_of_lt_of_le hε (le_trans hmin (min_le_left _ _)))
  have hc : ContinuousOn
      (fun t : ℝ => C * (1+t⁻¹)^N * (2+t)^N * Real.exp (a*t))
      (Set.Icc ε T) := by
    exact (((continuousOn_const.mul ((continuousOn_const.add hinv).pow N)).mul
      ((continuousOn_const.add continuousOn_id).pow N)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  exact hc.integrableOn_Icc

/-- Coordinate bounds control a real-linear complex functional in Euclidean norm. -/
theorem u4_coordinate_functional_euclidean_bound
    {d : ℕ} (A : Vec d →L[ℝ] ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ j : Fin d, ‖A (Pi.single j 1)‖ ≤ M) (v : Vec d) :
    ‖A v‖ ≤ (d : ℝ) * M * euclideanNorm v := by
  have hv : (∑ j : Fin d, v j • (Pi.single j 1 : Vec d)) = v := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  calc
    ‖A v‖ = ‖∑ j : Fin d, v j • A (Pi.single j 1)‖ := by
      conv_lhs => rw [← hv]
      rw [map_sum]
      simp only [map_smul]
    _ ≤ ∑ j : Fin d, ‖v j • A (Pi.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, M * euclideanNorm v := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |v j| * ‖A (Pi.single j 1)‖ ≤ |v j| * M :=
          mul_le_mul_of_nonneg_left (hA j) (abs_nonneg _)
        _ ≤ euclideanNorm v * M := mul_le_mul_of_nonneg_right
          (Regeneration.coordinate_abs_le_euclideanNorm v j) hM
        _ = M * euclideanNorm v := mul_comm _ _
    _ = (d : ℝ) * M * euclideanNorm v := by simp [mul_assoc]


/-- Coordinate bounds control a bilinear functional in Euclidean norm. -/
theorem u4_bilinear_coordinate_euclidean_bound
    {d : ℕ} (A : Vec d →L[ℝ] (Vec d →L[ℝ] ℂ)) (M : ℝ)
    (hM : 0 ≤ M)
    (hA : ∀ i j : Fin d, ‖A (Pi.single i 1) (Pi.single j 1)‖ ≤ M)
    (u v : Vec d) :
    ‖A u v‖ ≤ (d : ℝ)^2 * M * euclideanNorm u * euclideanNorm v := by
  have hbound : ‖A.flip v u‖ ≤
      (d : ℝ) * ((d : ℝ) * M * euclideanNorm v) * euclideanNorm u := by
    apply u4_coordinate_functional_euclidean_bound (A.flip v)
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hM) (Real.sqrt_nonneg _)
    · intro i
      exact u4_coordinate_functional_euclidean_bound (A (Pi.single i 1)) M hM
        (hA i) v
  simpa only [ContinuousLinearMap.flip_apply] using (by
    convert hbound using 1 <;> ring :
      ‖A.flip v u‖ ≤ (d : ℝ)^2 * M * euclideanNorm u * euclideanNorm v)

/-- Coordinate estimates for the mixed derivative of a two-variable kernel
give its directional estimate in the Euclidean norm. -/
theorem u4_kernel_mixed_derivative_euclidean_bound
    {d : ℕ} (K : Vec d → Vec d → ℂ) (x y : Vec d) (M : ℝ)
    (hM : 0 ≤ M)
    (hK : ∀ i j : Fin d,
      ‖fderiv ℝ (fun z => fderiv ℝ (K z) y) x (Pi.single i 1)
        (Pi.single j 1)‖ ≤ M) (u v : Vec d) :
    ‖fderiv ℝ (fun z => fderiv ℝ (K z) y) x u v‖ ≤
      (d : ℝ)^2 * M * euclideanNorm u * euclideanNorm v :=
  u4_bilinear_coordinate_euclidean_bound
    (fderiv ℝ (fun z => fderiv ℝ (K z) y) x) M hM hK u v

/-- The split evaluation kernel inherits the Euclidean mixed derivative
estimate from its coordinate estimates. -/
theorem u4_split_evaluation_kernel_mixed_derivative_bound
    {d : ℕ}
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (x y : Vec d) (M : ℝ) (hM : 0 ≤ M)
    (hK : ∀ i j : Fin d,
      ‖fderiv ℝ (fun z => fderiv ℝ (fun w =>
        E z (star ((InnerProductSpace.toDual ℂ _).symm (F w)))) y) x
          (Pi.single i 1) (Pi.single j 1)‖ ≤ M) (u v : Vec d) :
    ‖fderiv ℝ (fun z => fderiv ℝ (fun w =>
      E z (star ((InnerProductSpace.toDual ℂ _).symm (F w)))) y) x u v‖ ≤
        (d : ℝ)^2 * M * euclideanNorm u * euclideanNorm v :=
  u4_kernel_mixed_derivative_euclidean_bound
    (fun z w => E z (star ((InnerProductSpace.toDual ℂ _).symm (F w))))
    x y M hM hK u v

/-- The positive-time representatives have an explicit Euclidean directional bound. -/
theorem u4_physical_evolution_L2_directional_bound_of_Sobolev
    (hSobolev : ∀ (d : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∃ f : BoundedContinuousFunction (Vec d) ℂ,
          ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R)
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (htime : Blueprint.node_e_u3A_local_u2D_timeStmt)
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < (t : ℝ) →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
      ∀ (x v : Vec d), ‖fderiv ℝ u x v‖ ≤
        (d : ℝ) * (C * (1 + (t : ℝ)⁻¹)^N * (2 + (t : ℝ))^N *
          Real.exp (C * ‖ζ‖^2 * (t : ℝ)) * ‖f‖) * euclideanNorm v := by
  obtain ⟨C, N, hC, h⟩ :=
    u4_physical_evolution_L2_C1_of_Sobolev hSobolev hoff htime hder d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ
  filter_upwards [h Q hQ] with ω hω
  intro i ζ hζ P Pdag hP hPdag S hS t ht f
  obtain ⟨u, hu, hue, hub⟩ := hω i ζ hζ P Pdag hP hPdag S hS t ht f
  refine ⟨u, hu, hue, ?_⟩
  intro x v
  let M : ℝ := C * (1 + (t : ℝ)⁻¹)^N * (2 + (t : ℝ))^N *
    Real.exp (C * ‖ζ‖^2 * (t : ℝ)) * ‖f‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  apply u4_coordinate_functional_euclidean_bound (fderiv ℝ u x) M hM
  intro j
  have hj : ‖fderiv ℝ u x (unitVector j)‖ ≤
      Real.sqrt (∑ k : Fin d, ‖fderiv ℝ u x (unitVector k)‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (Finset.single_le_sum
      (fun k _ => sq_nonneg ‖fderiv ℝ u x (unitVector k)‖) (Finset.mem_univ j))
  have hx := hub x
  have hcoord : ‖fderiv ℝ u x (unitVector j)‖ ≤ M := by
    dsimp [M]
    linarith [norm_nonneg (u x)]
  simpa [unitVector] using hcoord

/-- A uniform Euclidean gradient estimate makes the evaluation family
Lipschitz in operator norm. -/
theorem u4_evaluation_operator_euclidean_lipschitz
    {d : ℕ} (E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hreg : ∀ f, ContDiff ℝ 1 (fun x => E x f))
    (hgrad : ∀ f x, Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => E z f) x (unitVector j)‖^2) ≤ C * ‖f‖)
    (x y : Vec d) :
    ‖E x - E y‖ ≤ (d : ℝ) * C * euclideanNorm (x-y) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hC) (Real.sqrt_nonneg _))
  intro f
  have hb (z v : Vec d) : ‖fderiv ℝ (fun z => E z f) z v‖ ≤
      (d : ℝ) * (C * ‖f‖) * euclideanNorm v := by
    apply u4_coordinate_functional_euclidean_bound _ _ (mul_nonneg hC (norm_nonneg _))
    intro j
    have hj : ‖fderiv ℝ (fun z => E z f) z (unitVector j)‖ ≤
        Real.sqrt (∑ k : Fin d, ‖fderiv ℝ (fun z => E z f) z (unitVector k)‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (Finset.single_le_sum
        (fun k _ => sq_nonneg ‖fderiv ℝ (fun z => E z f) z (unitVector k)‖)
        (Finset.mem_univ j))
    simpa [unitVector] using hj.trans (hgrad f z)
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => E (y + t • (x-y)) f)
      (fderiv ℝ (fun z => E z f) (y + t • (x-y)) (x-y)) t := by
    have hline := ((hasDerivAt_id t).smul_const (x-y)).const_add y
    simpa only [Function.comp_def, id_eq, one_smul] using!
      ((hreg f).differentiable (by norm_num) (y + t • (x-y))).hasFDerivAt.comp_hasDerivAt t hline
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := 1)
    (fun t _ => (hd t).hasDerivWithinAt)
    (fun t _ => hb _ _) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ _) (Set.mem_univ _)
  simpa only [ContinuousLinearMap.sub_apply, zero_smul, add_zero, one_smul,
    add_sub_cancel, sub_zero, norm_one, mul_one, one_mul, euclideanNorm,
    mul_assoc, mul_comm, mul_left_comm] using h

#print axioms u4_evaluation_operator_euclidean_lipschitz

/-- Positive-time physical evolutions have evaluation families that are
Lipschitz in operator norm with respect to the Euclidean distance. -/
theorem u4_physical_evolution_evaluations_euclidean_lipschitz_of_Sobolev
    (hSobolev : ∀ (d : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∃ f : BoundedContinuousFunction (Vec d) ℂ,
          ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R)
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (htime : Blueprint.node_e_u3A_local_u2D_timeStmt)
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < (t : ℝ) →
    let B := C * (1 + (t : ℝ)⁻¹)^N * (2 + (t : ℝ)) ^ N *
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))
    ∃ E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      (∀ x, ‖E x‖ ≤ B) ∧
      (∀ f, (S t f : Vec d → ℂ) =ᵐ[volume] fun x => E x f) ∧
      (∀ f, ContDiff ℝ 1 (fun x => E x f)) ∧
      (∀ x y, ‖E x - E y‖ ≤ (d : ℝ) * B * euclideanNorm (x-y)) := by
  obtain ⟨C, N, hC, h⟩ :=
    u4_physical_evolution_L2_C1_of_Sobolev hSobolev hoff htime hder d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ
  filter_upwards [h Q hQ] with ω hω
  intro i ζ hζ P Pdag hP hPdag S hS t ht
  dsimp only
  let B : ℝ := C * (1 + (t : ℝ)⁻¹)^N * (2 + (t : ℝ)) ^ N *
    Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  obtain ⟨E, hE, hae, hreg, hgrad⟩ :=
    s3_evaluations_of_quantitative_C1_representatives (S t) B hB
      (fun f => hω i ζ hζ P Pdag hP hPdag S hS t ht f)
  refine ⟨E, hE, hae, hreg, ?_⟩
  intro x y
  apply u4_evaluation_operator_euclidean_lipschitz E B hB hreg
  intro f z
  linarith [hgrad f z, norm_nonneg (E z f)]

#print axioms u4_physical_evolution_evaluations_euclidean_lipschitz_of_Sobolev

/-- A continuous physical representative is uniquely determined by its
volume almost-everywhere class. -/
theorem u4_continuous_physical_representative_unique
    {d : ℕ} (f g : Vec d → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[(volume : Measure (Vec d))] g) : f = g :=
  Measure.eq_of_ae_eq hfg hf hg

/-- Differentiable evaluation choices have the same derivatives as every C¹
representative of the corresponding physical action. -/
theorem u4_physical_evaluation_derivatives_identify_representatives
    {d : ℕ}
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0)
    (E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hE : ∀ f, ContDiff ℝ 1 (fun x => E x f))
    (hEa : ∀ f, (P t f : Vec d → ℂ) =ᵐ[volume] fun x => E x f) :
    ∀ f (u : Vec d → ℂ), ContDiff ℝ 1 u →
      u =ᵐ[volume] (P t f : Vec d → ℂ) →
      ∀ (x : Vec d) (j : Fin d),
        fderiv ℝ (fun y => E y f) x (unitVector j) =
          fderiv ℝ u x (unitVector j) := by
  intro f u hu hua x j
  have heq : (fun y => E y f) = u :=
    u4_continuous_physical_representative_unique _ _ (hE f).continuous
      hu.continuous ((hEa f).symm.trans hua.symm)
  rw [heq]

/-- The S3 forward and transpose evaluation families identify derivatives of
every C¹ representative of their respective actions. -/
theorem u4_s3_evaluation_derivatives_of_representatives
    {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (P t f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖)
    (hF : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (Pdag t f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ B * ‖f‖) :
    ∃ E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      (∀ x, ‖E x‖ ≤ A) ∧ (∀ x, ‖F x‖ ≤ B) ∧
      (∀ f, (P t f : Vec d → ℂ) =ᵐ[volume] fun x => E x f) ∧
      (∀ f, (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => F x f) ∧
      (∀ f, ContDiff ℝ 1 (fun x => E x f)) ∧
      (∀ f, ContDiff ℝ 1 (fun x => F x f)) ∧
      (∀ f x, ‖E x f‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun y => E y f) x (unitVector j)‖ ^ 2) ≤ A * ‖f‖) ∧
      (∀ f x, ‖F x f‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun y => F y f) x (unitVector j)‖ ^ 2) ≤ B * ‖f‖) ∧
      (∀ f u, ContDiff ℝ 1 u → u =ᵐ[volume] (P t f : Vec d → ℂ) →
        ∀ x j, fderiv ℝ (fun y => E y f) x (unitVector j) =
          fderiv ℝ u x (unitVector j)) ∧
      (∀ f u, ContDiff ℝ 1 u → u =ᵐ[volume] (Pdag t f : Vec d → ℂ) →
        ∀ x j, fderiv ℝ (fun y => F y f) x (unitVector j) =
          fderiv ℝ u x (unitVector j)) := by
  obtain ⟨E, hEn, hEa, hEc, hEg⟩ :=
    s3_evaluations_of_quantitative_C1_representatives (P t) A hA hE
  obtain ⟨F, hFn, hFa, hFc, hFg⟩ :=
    s3_evaluations_of_quantitative_C1_representatives (Pdag t) B hB hF
  exact ⟨E, F, hEn, hFn, hEa, hFa, hEc, hFc, hEg, hFg,
    u4_physical_evaluation_derivatives_identify_representatives P t E hEc hEa,
    u4_physical_evaluation_derivatives_identify_representatives Pdag t F hFc hFa⟩

/-- Positive-time forward and transpose physical evaluations identify the
derivatives of every C¹ representative, given their C¹ smoothing estimates. -/
theorem u4_physical_positive_time_evaluation_derivatives_of_representatives
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (hrep : ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup a i ζ P →
      IsPhysicalComplexTransposeSemigroup a i ζ P Pdag →
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
      ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
        (∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
          u =ᵐ[volume] (P t f : Vec d → ℂ) ∧ ∀ x,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖) ∧
        (∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
          u =ᵐ[volume] (Pdag t f : Vec d → ℂ) ∧ ∀ x,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ B * ‖f‖)) :
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup a i ζ P →
      IsPhysicalComplexTransposeSemigroup a i ζ P Pdag →
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
      ∃ E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
        (∀ f, (P t f : Vec d → ℂ) =ᵐ[volume] fun x => E x f) ∧
        (∀ f, (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => F x f) ∧
        (∀ f, ContDiff ℝ 1 (fun x => E x f)) ∧
        (∀ f, ContDiff ℝ 1 (fun x => F x f)) ∧
        (∀ f u, ContDiff ℝ 1 u → u =ᵐ[volume] (P t f : Vec d → ℂ) →
          ∀ x, E x f = u x) ∧
        (∀ f u, ContDiff ℝ 1 u → u =ᵐ[volume] (Pdag t f : Vec d → ℂ) →
          ∀ x, F x f = u x) ∧
        (∀ f u, ContDiff ℝ 1 u → u =ᵐ[volume] (P t f : Vec d → ℂ) →
          ∀ x j, fderiv ℝ (fun y => E y f) x (unitVector j) =
            fderiv ℝ u x (unitVector j)) ∧
        (∀ f u, ContDiff ℝ 1 u → u =ᵐ[volume] (Pdag t f : Vec d → ℂ) →
          ∀ x j, fderiv ℝ (fun y => F y f) x (unitVector j) =
            fderiv ℝ u x (unitVector j)) := by
  intro P Pdag hP hPdag t ht
  obtain ⟨A, B, hA, hB, hE, hF⟩ := hrep P Pdag hP hPdag t ht
  obtain ⟨E, F, _, _, hEa, hFa, hEc, hFc, _, _, hEd, hFd⟩ :=
    u4_s3_evaluation_derivatives_of_representatives P Pdag t A B hA hB hE hF
  refine ⟨E, F, hEa, hFa, hEc, hFc, ?_, ?_, hEd, hFd⟩
  · intro f u hu hua x
    exact congrFun (u4_continuous_physical_representative_unique _ _
      (hEc f).continuous hu.continuous ((hEa f).symm.trans hua.symm)) x
  · intro f u hu hua x
    exact congrFun (u4_continuous_physical_representative_unique _ _
      (hFc f).continuous hu.continuous ((hFa f).symm.trans hua.symm)) x

#print axioms u4_physical_evaluation_derivatives_identify_representatives
#print axioms u4_s3_evaluation_derivatives_of_representatives
#print axioms u4_physical_positive_time_evaluation_derivatives_of_representatives

end EinsteinFull

#print axioms EinsteinFull.u4_bilinear_coordinate_euclidean_bound
#print axioms EinsteinFull.u4_kernel_mixed_derivative_euclidean_bound
#print axioms EinsteinFull.u4_split_evaluation_kernel_mixed_derivative_bound
#print axioms EinsteinFull.u4_physical_evolution_L2_directional_bound_of_Sobolev

#print axioms EinsteinFull.u4CoefficientDerivative_iterated_quotient_bound

#print axioms EinsteinFull.u4CoefficientDerivative_iterated_quotient_multiplier

#print axioms EinsteinFull.u4H3_generator_pair_quantitative

#print axioms EinsteinFull.u4H3_generator_pair_force_uniform

#print axioms EinsteinFull.u4HigherCoefficientCommutator_split

#print axioms EinsteinFull.u4Coefficient_split_term_L2_bound

#print axioms EinsteinFull.u4CoordinateSplitExpansion_L2_bound

#print axioms EinsteinFull.u4CoordinateCommutator_L2_bound

#print axioms EinsteinFull.u4PhysicalCoefficientCommutator_L2_bound

#print axioms EinsteinFull.u4IteratedCoordinateQuotient_weakDerivative_bound

#print axioms EinsteinFull.u4CoordinateSplitBound_weakDerivative_bound

#print axioms EinsteinFull.u4CoordinateCommutatorBound_weakDerivative_bound
#print axioms EinsteinFull.u4PhysicalCoefficientCommutator_uniform_L2_bound

#print axioms EinsteinFull.u4PhysicalCoefficientCommutator_matrix_uniform_L2_bound

#print axioms EinsteinFull.u4PhysicalCoefficientCommutator_energy_bound

#print axioms EinsteinFull.u4Higher_backward_forcing_weakDerivative_bound

#print axioms EinsteinFull.u4Higher_coefficient_backward_pairing_bound

#print axioms EinsteinFull.u4Higher_coefficient_backward_sum_bound

#print axioms EinsteinFull.u4Higher_principal_energy_error

#print axioms EinsteinFull.u4Higher_forward_generator_energy

#print axioms EinsteinFull.u4Higher_transpose_generator_energy

#print axioms EinsteinFull.u4Higher_backward_coordinate_H1_bound

#print axioms EinsteinFull.u4Higher_backward_forcing_gradient_bound

#print axioms EinsteinFull.u4Higher_coefficient_backward_sum_gradient_bound

#print axioms EinsteinFull.u4Higher_coefficient_backward_transpose_sum_bound

#print axioms EinsteinFull.u4Higher_drift_integral_sum

#print axioms EinsteinFull.u4Higher_forward_quotient_energy_uniform

#print axioms EinsteinFull.u4Higher_transpose_quotient_energy_uniform

#print axioms EinsteinFull.u4Higher_coordinate_derivative_of_quotient_energy

#print axioms EinsteinFull.u4Higher_H1_of_strong_limit

#print axioms EinsteinFull.u4HigherLpDifferences_continuous
#print axioms EinsteinFull.u4HigherLpDifferences_ae

#print axioms EinsteinFull.u4Higher_remove_first_quotient

#print axioms EinsteinFull.u4Higher_remove_coordinate_quotients

#print axioms EinsteinFull.u4Higher_forward_quotient_graph_uniform

#print axioms EinsteinFull.u4Higher_transpose_quotient_graph_uniform

#print axioms EinsteinFull.u4Higher_extend_chain_from_quotient_graphs

#print axioms EinsteinFull.u4Higher_forward_extend_chain

#print axioms EinsteinFull.u4Higher_transpose_extend_chain

#print axioms EinsteinFull.u4Higher_assemble_derivative_layer

#print axioms EinsteinFull.u4Higher_forward_extend_derivative_layer

#print axioms EinsteinFull.u4Higher_transpose_extend_derivative_layer

#print axioms EinsteinFull.u4Higher_derivative_layer_norm_bound

#print axioms EinsteinFull.u4Higher_forward_bounded_derivative_step

#print axioms EinsteinFull.u4Higher_transpose_bounded_derivative_step

#print axioms EinsteinFull.u4Higher_forward_derivative_step
#print axioms EinsteinFull.u4Higher_transpose_derivative_step

#print axioms EinsteinFull.u4Higher_generator_chain_derivative_family

#print axioms EinsteinFull.u4Higher_positive_time_derivative_families

#print axioms EinsteinFull.u4Higher_forward_homogeneous_derivative_step
#print axioms EinsteinFull.u4Higher_transpose_homogeneous_derivative_step

#print axioms EinsteinFull.u4_positive_time_polynomial_exp_bound_integrable

#print axioms EinsteinFull.u4_coordinate_functional_euclidean_bound

#print axioms EinsteinFull.u4_physical_evolution_L2_directional_bound_of_Sobolev
