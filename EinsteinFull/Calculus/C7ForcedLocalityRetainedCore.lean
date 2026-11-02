import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal
import EinsteinFull.Calculus.C7EndpointUniformProjection
import EinsteinFull.Calculus.C9ShortTimeLocality
import EinsteinFull.Calculus.C18PhysicalEvolutionSmoothing
import EinsteinFull.Calculus.S5DaviesSupport
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalAverage

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem c7_continuous_euclideanNorm {d : ℕ} :
    Continuous (fun x : Vec d => euclideanNorm x) := by
  unfold euclideanNorm euclideanSq dot
  fun_prop

private theorem c7_gaussian_elapsed_time_le {C c ρ s t : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hs : 0 < s) (hst : s ≤ t) (ζ : ℂ) :
    Real.exp (C * ‖ζ‖ ^ 2 * s - c * (ρ / 2) ^ 2 / s) ≤
      Real.exp (C * ‖ζ‖ ^ 2 * t - (c / 4) * ρ ^ 2 / t) := by
  apply Real.exp_le_exp.mpr
  have htime := mul_le_mul_of_nonneg_left hst (mul_nonneg hC (sq_nonneg ‖ζ‖))
  have htail := div_le_div_of_nonneg_left (mul_nonneg hc (sq_nonneg (ρ / 2))) hs hst
  have heq : c * (ρ / 2) ^ 2 = (c / 4) * ρ ^ 2 := by ring
  rw [heq] at htail ⊢
  exact sub_le_sub htime htail

/-- Propagate physical shell-supported data into the inner Euclidean ball.
The event precedes every force, time and datum. The Gaussian factor is uniform
over all elapsed times up to the terminal time, as required for forcing-time
integration. This uses the actual forward and bilinear transpose evolutions. -/
theorem c7_off_diagonal_shell_of_deps
    (hoff : node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r), ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ (t s : ℝ≥0), 0 < s → s ≤ t →
    ∀ (z : Vec d) (ρ : ℝ), 0 ≤ ρ →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ x ∂volume, euclideanNorm (x - z) < ρ → f x = 0) →
      MemLp ({x : Vec d | euclideanNorm (x - z) < ρ / 2}.indicator
        (fun x => S s f x)) 2 volume ∧
      (eLpNorm ({x : Vec d | euclideanNorm (x - z) < ρ / 2}.indicator
        (fun x => S s f x)) 2 volume).toReal ≤
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) * ‖f‖ := by
  obtain ⟨C, c, hC, hc, hprop⟩ := hoff d hd Λ hΛ
  refine ⟨C, c / 4, hC, by positivity, ?_⟩
  intro r Q
  filter_upwards [hprop r Q] with ω hω
  intro i ζ P Pdag hP hPdag S hS t s hs hst z ρ hρ f hf
  let E := {x : Vec d | ρ ≤ euclideanNorm (x - z)}
  let F := {x : Vec d | euclideanNorm (x - z) < ρ / 2}
  have hn : Continuous (fun x : Vec d => euclideanNorm (x - z)) :=
    c7_continuous_euclideanNorm.comp (continuous_id.sub continuous_const)
  have hE : MeasurableSet E := (isClosed_le continuous_const hn).measurableSet
  have hF : MeasurableSet F := (isOpen_lt hn continuous_const).measurableSet
  have hsep : ∀ x ∈ E, ∀ y ∈ F, ρ / 2 ≤ euclideanNorm (x - y) := by
    intro x hx y hy
    have htri := TimeChange.euclideanNorm_add_le (x - y) (y - z)
    rw [sub_add_sub_cancel] at htri
    change ρ ≤ euclideanNorm (x - z) at hx
    change euclideanNorm (y - z) < ρ / 2 at hy
    linarith
  have hsupport : ∀ᵐ x ∂volume, x ∉ E → f x = 0 := by
    filter_upwards [hf] with x hx hnot
    exact hx (lt_of_not_ge hnot)
  obtain ⟨hmem, hbound⟩ :=
    (hω i ζ P Pdag hP hPdag S hS s hs).2 E F hE hF (ρ / 2)
      (by positivity) hsep f hsupport
  refine ⟨hmem, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  exact c7_gaussian_elapsed_time_le (zero_le_one.trans hC) hc.le
    (show 0 < (s : ℝ) from hs) (show (s : ℝ) ≤ (t : ℝ) from hst) ζ

/-- The scalar shell-forcing norm is integrable in physical forcing time and
retains the terminal Gaussian factor. Measurability is required explicitly;
integrability of the propagated norm is a conclusion, so this estimate never
uses the default value of a nonintegrable Bochner integral. -/
theorem c7_off_diagonal_shell_time_integral_of_deps
    (hoff : node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r), ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ (t : ℝ≥0),
    ∀ (z : Vec d) (ρ : ℝ), 0 ≤ ρ →
    ∀ F : ℝ → Lp ℂ 2 (volume : Measure (Vec d)),
      Integrable F (volume.restrict (Set.Ioo (0 : ℝ) (t : ℝ))) →
      (∀ s ∈ Set.Ioo (0 : ℝ) (t : ℝ),
        ∀ᵐ x ∂volume, euclideanNorm (x - z) < ρ → F s x = 0) →
      let R := fun s : ℝ =>
        (eLpNorm ({x : Vec d | euclideanNorm (x - z) < ρ / 2}.indicator
          (fun x => S (Real.toNNReal ((t : ℝ) - s)) (F s) x)) 2 volume).toReal
      AEStronglyMeasurable R (volume.restrict (Set.Ioo (0 : ℝ) (t : ℝ))) →
      Integrable R (volume.restrict (Set.Ioo (0 : ℝ) (t : ℝ))) ∧
      (∫ s in Set.Ioo (0 : ℝ) (t : ℝ), R s) ≤
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) *
          ∫ s in Set.Ioo (0 : ℝ) (t : ℝ), ‖F s‖ := by
  obtain ⟨C, c, hC, hc, hprop⟩ := c7_off_diagonal_shell_of_deps hoff d hd Λ hΛ
  refine ⟨C, c, hC, hc, ?_⟩
  intro r Q
  filter_upwards [hprop r Q] with ω hω
  intro i ζ P Pdag hP hPdag S hS t z ρ hρ F hF hsupp R hR
  let A := Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))
  have hbound : ∀ᵐ s ∂volume.restrict (Set.Ioo (0 : ℝ) (t : ℝ)),
      R s ≤ A * ‖F s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hdt : 0 < Real.toNNReal ((t : ℝ) - s) :=
      Real.toNNReal_pos.mpr (sub_pos.mpr hs.2)
    have hdtt : Real.toNNReal ((t : ℝ) - s) ≤ t := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs.2.le)]
      linarith [hs.1]
    exact (hω i ζ P Pdag hP hPdag S hS t
      (Real.toNNReal ((t : ℝ) - s)) hdt hdtt z ρ hρ (F s) (hsupp s hs)).2
  have hdom := hF.norm.const_mul A
  have hRi : Integrable R (volume.restrict (Set.Ioo (0 : ℝ) (t : ℝ))) := by
    apply hdom.mono' hR
    filter_upwards [hbound] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hs
  refine ⟨hRi, ?_⟩
  calc
    (∫ s in Set.Ioo (0 : ℝ) (t : ℝ), R s) ≤
        ∫ s in Set.Ioo (0 : ℝ) (t : ℝ), A * ‖F s‖ :=
      integral_mono_ae hRi hdom hbound
    _ = A * ∫ s in Set.Ioo (0 : ℝ) (t : ℝ), ‖F s‖ := integral_const_mul A _

/-- Apply shell propagation to the actual retained coefficient-difference
sources, with one common complex gradient in their formulas. Each flux
component and the signed-force drift use the same retained environment.
The divergence-forcing evolution estimate is a further step. -/
theorem c7_actual_retained_sources_off_diagonal_of_deps
    (hoff : node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r), ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ (t s : ℝ≥0), 0 < s → s ≤ t →
    ∀ (z : Vec d) (ρ : ℝ), 0 ≤ ρ →
    ∀ χ : C(Vec d, ℝ), (∀ x, euclideanNorm (x - z) < ρ → χ x = 1) →
    ∀ (ψ : Vec d → ℝ) (X : Vec d → Fin d → ℂ) (j : Fin d),
    ∀ g ∈ [fun x => (ψ x : ℂ) *
      C9ShortTimeLocality.retainedDriftDefect χ ω x (X x) i ζ,
      fun x => (ψ x : ℂ) * C9ShortTimeLocality.retainedFluxDefect χ ω x (X x) j],
    ∀ hg : MemLp g 2 volume,
      MemLp ({x : Vec d | euclideanNorm (x - z) < ρ / 2}.indicator
        (fun x => S s (hg.toLp g) x)) 2 volume ∧
      (eLpNorm ({x : Vec d | euclideanNorm (x - z) < ρ / 2}.indicator
        (fun x => S s (hg.toLp g) x)) 2 volume).toReal ≤
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) *
          (eLpNorm g 2 volume).toReal := by
  obtain ⟨C, c, hC, hc, hprop⟩ := c7_off_diagonal_shell_of_deps hoff d hd Λ hΛ
  refine ⟨C, c, hC, hc, ?_⟩
  intro r Q
  filter_upwards [hprop r Q] with ω hω
  intro i ζ P Pdag hP hPdag S hS t s hs hst z ρ hρ χ hχ ψ X j g hgin hg
  have hgzero : ∀ x, euclideanNorm (x - z) < ρ → g x = 0 := by
    intro x hx
    have hz := C9ShortTimeLocality.retainedDefects_eq_zero χ ω (hχ x hx) (X x) i ζ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgin
    rcases hgin with rfl | rfl
    · simp only [hz.2, mul_zero]
    · simp only [hz.1 j, mul_zero]
  have hsupp : ∀ᵐ x ∂volume, euclideanNorm (x - z) < ρ → hg.toLp g x = 0 := by
    filter_upwards [hg.coeFn_toLp] with x hx hinner
    exact hx.trans (hgzero x hinner)
  have hb := hω i ζ P Pdag hP hPdag S hS t s hs hst z ρ hρ (hg.toLp g) hsupp
  simpa only [Lp.norm_toLp] using hb

private theorem c7_physicalH1_add {d : ℕ}
    {u v : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u + v) (G + H) := by
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => u x + v x) (fun j x => G j x + H j x)
    (Lp.coeFn_add _ _) (fun _ => Lp.coeFn_add _ _)).mpr
  exact ⟨fun j => by simpa only [Complex.add_re] using
      Correctors.hasWeakPartialDerivative_add (hu.1 j) (hv.1 j),
    fun j => by simpa only [Complex.add_im] using
      Correctors.hasWeakPartialDerivative_add (hu.2 j) (hv.2 j)⟩

private theorem c7_weakPartial_real_mul {d : ℕ} {j : Fin d}
    {f g : Vec d → ℝ} (h : HasWeakPartialDerivative Set.univ j f g) (c : ℝ) :
    HasWeakPartialDerivative Set.univ j (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨fun x hx => (h.1 x hx).smul c, fun x hx => (h.2.1 x hx).smul c, ?_⟩
  intro φ hφ
  simp only [mul_assoc, integral_const_mul]
  rw [h.2.2 φ hφ]
  ring

private theorem c7_physicalH1_smul {d : ℕ}
    {u : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G) (c : ℂ) :
    IsPhysicalH1Graph volume (Or.inl rfl) (c • u) (c • G) := by
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => c * u x) (fun j x => c * G j x)
    (Lp.coeFn_smul _ _) (fun _ => Lp.coeFn_smul _ _)).mpr
  constructor
  · intro j
    have h := Correctors.hasWeakPartialDerivative_add
      (c7_weakPartial_real_mul (hu.1 j) c.re)
      (c7_weakPartial_real_mul (hu.2 j) (-c.im))
    simpa only [Complex.mul_re, neg_mul, sub_eq_add_neg] using h
  · intro j
    simpa only [Complex.mul_im] using Correctors.hasWeakPartialDerivative_add
      (c7_weakPartial_real_mul (hu.2 j) c.re)
      (c7_weakPartial_real_mul (hu.1 j) c.im)

/-- Positive-time physical smoothing gives a bounded complex linear operator
whose value is the actual weak spatial gradient. This construction uses the
closed H1 graph, without asserting a quantitative or spatially weighted bound. -/
theorem c7_physical_gradient_operator
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (hS : S ∈ [P, Pdag])
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      (Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      ∀ f, IsPhysicalH1Graph volume (Or.inl rfl) (S t f) (T f) := by
  classical
  have hsm := fun f => physical_positive_time_H1 hΛ hell hsmooth hP hPdag S hS f t ht
  let V := fun f => (hsm f).choose
  have hV : ∀ f, IsPhysicalH1Graph volume (Or.inl rfl) (S t f) (V f) :=
    fun f => (hsm f).choose_spec
  let L : Lp ℂ 2 (volume : Measure (Vec d)) →ₗ[ℂ]
      (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) := {
    toFun := V
    map_add' := fun f g => physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (S t (f + g)) (V (f + g)) (V f + V g) (hV _) (by
        simpa only [map_add] using c7_physicalH1_add (hV f) (hV g))
    map_smul' := fun c f => physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (S t (c • f)) (V (c • f)) (c • V f) (hV _) (by
        simpa only [map_smul] using c7_physicalH1_smul (hV f) c) }
  refine ⟨ContinuousLinearMap.ofSeqClosedGraph (g := L) ?_, hV⟩
  intro u x y hu hy
  apply physicalH1Graph_gradient_unique volume (Or.inl rfl) (S t x) y (V x) _ (hV x)
  exact physicalH1Graph_of_tendsto volume (Or.inl rfl)
    (fun n => (S t (u n), V (u n))) (S t x, y) (fun n => hV (u n))
    ((((S t).continuous.tendsto x).comp hu).prodMk_nhds hy)

private noncomputable def c7_physical_conj {d : ℕ} :
    Lp ℂ 2 (volume : Measure (Vec d)) →L⋆[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)) where
  toFun := star
  map_add' := by
    intro f g
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g,
      Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g]
      with x hfg ha hb hf hg
    calc
      (star (f + g) : Lp ℂ 2 volume) x = star ((f + g) x) := hfg
      _ = star (f x) + star (g x) := by
        rw [ha]
        exact star_add _ _
      _ = (star f + star g : Lp ℂ 2 volume) x := by
        rw [hb]
        change star (f x) + star (g x) = (star f : Lp ℂ 2 volume) x +
          (star g : Lp ℂ 2 volume) x
        rw [hf, hg]
        simp only [Pi.star_apply]
  map_smul' := by
    intro c f
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f,
      Lp.coeFn_smul (starRingEnd ℂ c) (star f), Lp.coeFn_star f]
      with x hs hc hd hf
    calc
      (star (c • f) : Lp ℂ 2 volume) x = star ((c • f) x) := hs
      _ = star c * star (f x) := by
        rw [hc]
        change star (c * f x) = star c * star (f x)
        rw [star_mul, mul_comm]
      _ = (starRingEnd ℂ c • star f : Lp ℂ 2 volume) x := by
        rw [hd]
        change star c * star (f x) = star c * (star f : Lp ℂ 2 volume) x
        rw [hf]
        simp only [Pi.star_apply]
  cont := by
    have he : (star : Lp ℂ 2 (volume : Measure (Vec d)) → _) =
        Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume := by
      funext f
      apply Lp.ext
      filter_upwards [Lp.coeFn_star f,
        Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL (p := 2) f] with x hs hc
      exact hs.trans hc.symm
    rw [he]
    exact (Complex.conjCLE.toContinuousLinearMap.compLpL 2
      (volume : Measure (Vec d))).continuous

private theorem c7_physical_conj_involutive {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    c7_physical_conj (c7_physical_conj f) = f := star_star f

private theorem c7_physical_pairing_eq_inner {d : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, f x * g x) = inner ℂ (c7_physical_conj f) g := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with x hx
  change c7_physical_conj f x = star (f x) at hx
  simp only [hx, RCLike.inner_apply, Complex.star_def, starRingEnd_self_apply]
  ring

private noncomputable def c7_physical_bilinear_transpose {d : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)) :=
  c7_physical_conj.comp (A.adjoint.comp c7_physical_conj)

private theorem c7_physical_bilinear_transpose_apply {d : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    c7_physical_bilinear_transpose A f =
      c7_physical_conj (A.adjoint (c7_physical_conj f)) := rfl

/-- Transposition of the actual positive-time gradient defines the evolved
divergence of every L2 vector field by its bilinear dx pairing. No L2 hypothesis
on the unevolved distributional divergence is needed. -/
theorem c7_physical_evolved_divergence
    {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      (Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
    ∃ B : (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ g, IsPhysicalH1Graph volume (Or.inl rfl) (Pdag t g) (T g)) ∧
      ∀ F : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        ∀ g, (∫ x, B F x * g x) = -∑ j, ∫ x, F j x * T g j x := by
  classical
  obtain ⟨T, hT⟩ := c7_physical_gradient_operator hΛ hell hsmooth hP hPdag
    Pdag (by simp) t ht
  let B : (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)) :=
    -∑ j : Fin d, (c7_physical_bilinear_transpose
      ((ContinuousLinearMap.proj j).comp T)).comp (ContinuousLinearMap.proj j)
  refine ⟨T, B, hT, ?_⟩
  intro F g
  rw [c7_physical_pairing_eq_inner]
  simp only [B, neg_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, map_neg, map_sum, inner_neg_left, sum_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [c7_physical_bilinear_transpose_apply, c7_physical_conj_involutive,
    ContinuousLinearMap.adjoint_inner_left, ← c7_physical_pairing_eq_inner]
  rfl

/-- The transposed-gradient construction agrees with the actual forward
evolution whenever the vector field's weak divergence is an L2 class. -/
theorem c7_physical_evolved_divergence_agrees
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    (t : ℝ≥0)
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      (Fin d → Lp ℂ 2 (volume : Measure (Vec d))))
    (hT : ∀ g, IsPhysicalH1Graph volume (Or.inl rfl) (Pdag t g) (T g))
    (F : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (q u : Lp ℂ 2 (volume : Measure (Vec d)))
    (hdiv : ∀ v Gv, IsPhysicalH1Graph volume (Or.inl rfl) v Gv →
      (∫ x, q x * v x) = -∑ j, ∫ x, F j x * Gv j x)
    (hu : ∀ g, (∫ x, u x * g x) = -∑ j, ∫ x, F j x * T g j x) :
    u = P t q := by
  apply (Function.LeftInverse.injective c7_physical_conj_involutive)
  apply ext_inner_right ℂ
  intro g
  rw [← c7_physical_pairing_eq_inner, ← c7_physical_pairing_eq_inner,
    hu g, hPdag.2.2.2.2 t q g]
  exact (hdiv (Pdag t g) (T g) (hT g)).symm


/-- Bounds for the bounded rational radial weight used in the localized
energy estimate. The radius variable is nonnegative, and the constants are
independent of the coefficient field and the spatial dimension. -/
theorem c7_rational_radial_weight_bounds {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 ≤ x) :
    0 ≤ ρ * x ^ 2 / (ρ ^ 2 + x ^ 2) ∧
    ρ * x ^ 2 / (ρ ^ 2 + x ^ 2) ≤ ρ ∧
    (x ≤ ρ / 2 → ρ * x ^ 2 / (ρ ^ 2 + x ^ 2) ≤ ρ / 5) ∧
    (ρ ≤ x → ρ / 2 ≤ ρ * x ^ 2 / (ρ ^ 2 + x ^ 2)) ∧
    2 * ρ * x / (ρ ^ 2 + x ^ 2) ≤ 1 := by
  have hd : 0 < ρ ^ 2 + x ^ 2 := by positivity
  refine ⟨div_nonneg (mul_nonneg hρ.le (sq_nonneg x)) hd.le, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hρ.le (sq_nonneg ρ)]
  · intro hinner
    apply (div_le_iff₀ hd).2
    have hprod : 0 ≤ (ρ / 2 - x) * (ρ / 2 + x) :=
      mul_nonneg (by linarith) (by positivity)
    have hsq : 4 * x ^ 2 ≤ ρ ^ 2 := by nlinarith [hprod]
    nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hsq)]
  · intro houter
    apply (le_div_iff₀ hd).2
    have hprod : 0 ≤ (x - ρ) * (x + ρ) :=
      mul_nonneg (sub_nonneg.mpr houter) (by positivity)
    have hsq : ρ ^ 2 ≤ x ^ 2 := by nlinarith [hprod]
    nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hsq)]
  · apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg (ρ - x)]

/-- Differentiation of an anisotropic form after applying bounded, time-independent
operators to the orbit and its gradient. This permits the shifted weighted flux
to be formed before applying the principal-energy chain rule. -/
theorem c7_shifted_principal_energy_hasDerivAt {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    (W : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume)
    (B : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume)
    (u : ℝ → Lp ℂ 2 (volume : Measure (Vec d)))
    (g : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hu : HasDerivAt u g s) (hG : ∀ j, HasDerivAt (fun t => G t j) (H j) s) :
    HasDerivAt (fun t => (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
      ((W (G t k) - B k (u t) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) x * star (((W (G t j) - B j (u t) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) x)).re)
      (2 * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
        ((W (G s k) - B k (u s) : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) x * star (((W (H j) - B j g : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) x)).re) s := by
  apply c18_physical_principal_energy_hasDerivAt a ha hsym
    (fun t j => W (G t j) - B j (u t)) (fun j => W (H j) - B j g) s
  intro j
  have hW := (W.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hG j)
  have hB := ((B j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hu
  have hWB : HasDerivAt ((fun t => W (G t j)) - (fun t => B j (u t)))
      (W (H j) - B j g) s := by
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] using hW.sub hB
  have heq : ((fun t => W (G t j)) - (fun t => B j (u t))) =
      (fun t => W (G t j) - B j (u t)) := by
    funext t
    rfl
  rw [heq] at hWB
  exact hWB

/-- Coercivity of the shifted principal energy controls the weighted gradient
up to the explicit weight-derivative correction. -/
theorem c7_shifted_principal_energy_coercive {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (U V : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∑ j, ‖U j‖ ^ 2) ≤
      2 * Λ * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
        (U k - V k) x * star ((U j - V j) x)).re +
      2 * ∑ j, ‖V j‖ ^ 2 := by
  have hco := c18_physical_principal_energy_coercive a ha hΛ hA (fun j => U j - V j)
  have hsum : (∑ j, ‖U j‖ ^ 2) ≤
      2 * (∑ j, ‖U j - V j‖ ^ 2) + 2 * ∑ j, ‖V j‖ ^ 2 := by
    calc
      _ ≤ ∑ j, (2 * ‖U j - V j‖ ^ 2 + 2 * ‖V j‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have ht : ‖U j‖ ≤ ‖U j - V j‖ + ‖V j‖ := by
          simpa only [sub_add_cancel] using norm_add_le (U j - V j) (V j)
        nlinarith [norm_nonneg (U j), norm_nonneg (U j - V j), norm_nonneg (V j),
          sq_nonneg (‖U j - V j‖ - ‖V j‖)]
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith

/-- A bound for a continuous observation on the twice-generator domain
extends to all data by density, with the same constant. -/
theorem c7_D2_observation_bound_of_dense {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen)
    (happrox : ∀ f g, Gen f g →
      ∃ U V W : ℝ → E,
        (∀ δ, 0 < δ → Gen (U δ) (V δ) ∧ Gen (V δ) (W δ)) ∧
        Filter.Tendsto U (nhdsWithin 0 (Set.Ioi 0)) (nhds f) ∧
        Filter.Tendsto V (nhdsWithin 0 (Set.Ioi 0)) (nhds g))
    (T : E →L[ℂ] F) (W : E →L[ℂ] E) (C : ℝ)
    (hbound : ∀ f g h, Gen f g → Gen g h → ‖T f‖ ≤ C * ‖W f‖) :
    ∀ f, ‖T f‖ ≤ C * ‖W f‖ := by
  let D2 : Set E := {u | ∃ v w, Gen u v ∧ Gen v w}
  have hfirst (u v : E) (huv : Gen u v) : u ∈ closure D2 := by
    obtain ⟨U, V, W, hgen, hU, _⟩ := happrox u v huv
    apply mem_closure_of_tendsto hU
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ⟨V δ, W δ, hgen δ hδ⟩
  have hdense : Dense D2 := by
    intro u
    obtain ⟨U, V, hgen, hU⟩ := hP.exists_gen_approx u
    apply isClosed_closure.mem_of_tendsto hU
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hfirst (U δ) (V δ) (hgen δ hδ)
  intro f
  have hclosed : IsClosed {u : E | ‖T u‖ ≤ C * ‖W u‖} :=
    isClosed_le (T.continuous.norm) (continuous_const.mul W.continuous.norm)
  have hsubset : D2 ⊆ {u : E | ‖T u‖ ≤ C * ‖W u‖} := by
    rintro u ⟨v, w, huv, hvw⟩
    exact hbound u v w huv hvw
  exact closure_minimal hsubset hclosed (hdense f)

/-- Quantitative twice-domain bounds extend along the actual transpose graph. -/
theorem c7_transpose_D2_observation_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] F)
    (W : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))) (C : ℝ)
    (hbound : ∀ f g h, IsPhysicalComplexTransposeGeneratorPair a i ζ f g →
      IsPhysicalComplexTransposeGeneratorPair a i ζ g h → ‖T f‖ ≤ C * ‖W f‖) :
    ∀ f, ‖T f‖ ≤ C * ‖W f‖ := by
  apply c7_D2_observation_bound_of_dense
    (⟨hPdag.1, hPdag.2.1, hPdag.2.2.1, hPdag.2.2.2.1⟩ :
      S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair a i ζ))
    (fun u v huv => c18_physical_transpose_generator_D2_approx a i ζ P Pdag hPdag huv)
    T W C hbound

/-- The transpose pointwise estimate retains a fixed part of the principal
coercivity, with a structural cost for the force and weight gradient. -/
theorem c7_transpose_pointwise_dissipation {Λ N B ρ q : ℝ}
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (hN : 0 ≤ N) (hB : B ≤ 2 * q * ρ) (hB0 : 0 ≤ B)
    (T1 T2 T4 T5 u ζ : ℂ)
    (h1 : Λ⁻¹ * N ^ 2 ≤ T1.re)
    (h2 : ‖T2‖ ≤ 2 * Λ * B * N) (h4 : ‖T4‖ ≤ 2 * Λ * N)
    (h5 : ‖T5‖ ≤ Λ * B) :
    (-(1 / 2 : ℂ) * ((ρ : ℂ) * T1 + (starRingEnd ℂ) u * T2) +
      ζ * (u * ((ρ : ℂ) * T4 + (starRingEnd ℂ) u * T5))).re +
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
  have h4' : ‖T4‖ ≤ 2 * (2 * Λ) * N := by
    nlinarith [mul_nonneg hΛ0 hN]
  have h5' : ‖T5‖ ≤ (2 * Λ) * B := by
    nlinarith [mul_nonneg hΛ0 hB0]
  have h := s5_alg_transpose (Λ := 2 * Λ) (by linarith) hρ hN hB
    (T1 - ((Λ⁻¹ * N ^ 2 / 2 : ℝ) : ℂ)) T2 T4 T5 u ζ h1' h2' h4' h5'
  have heq :
      (-(1 / 2 : ℂ) * ((ρ : ℂ) *
        (T1 - ((Λ⁻¹ * N ^ 2 / 2 : ℝ) : ℂ)) + (starRingEnd ℂ) u * T2) +
        ζ * (u * ((ρ : ℂ) * T4 + (starRingEnd ℂ) u * T5))).re =
      (-(1 / 2 : ℂ) * ((ρ : ℂ) * T1 + (starRingEnd ℂ) u * T2) +
        ζ * (u * ((ρ : ℂ) * T4 + (starRingEnd ℂ) u * T5))).re +
        (Λ⁻¹ / 4) * ρ * N ^ 2 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
      Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
    ring
  rw [heq] at h
  exact h

/-- Retained coercivity for the actual transpose weak-form integrand. -/
theorem c7_transpose_pointwise_integrand_dissipation {d : ℕ} {A : Fin d → Fin d → ℝ} {Λ : ℝ} (h : S5Elliptic A Λ)
    (X : Fin d → ℂ) (u : ℂ) (D : Fin d → ℝ) (ρ q : ℝ) (i : Fin d) (ζ : ℂ)
    (hρ : 0 ≤ ρ) (hD : s5Nrm D ≤ 2 * q * ρ) :
    (-(1 / 2 : ℂ) * (∑ j, ∑ k, (A k j : ℂ) * X k *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) +
      ζ * (u * ∑ j, (A j i : ℂ) *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ)))).re +
      (Λ⁻¹ / 4) * ρ * s5CNrm X ^ 2 ≤
    (5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (ρ * ‖u‖ ^ 2) := by
  have hs : ∀ j k, (A k j : ℂ) = (A j k : ℂ) := fun j k => by rw [h.symm k j]
  have hsplit : (∑ j, ∑ k, (A k j : ℂ) * X k *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) =
      (ρ : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)) +
        (starRingEnd ℂ) u * (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * X k) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hs j k]; ring
  have hsplit2 : (∑ j, (A j i : ℂ) *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) =
      (ρ : ℂ) * (∑ j, (A j i : ℂ) * (starRingEnd ℂ) (X j)) +
        (starRingEnd ℂ) u * (∑ j, (D j : ℂ) * (A j i : ℂ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, hsplit2]
  have hm : ∑ j, ‖X j‖ ^ 2 = s5CNrm X ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)).symm
  have h1 : Λ⁻¹ * s5CNrm X ^ 2 ≤
      (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)).re := by
    rw [← hm]
    exact s5_coercive h X
  have h4 : ‖∑ j, (A j i : ℂ) * (starRingEnd ℂ) (X j)‖ ≤ 2 * Λ * s5CNrm X := by
    have := s5_row_norm_le h i (fun j => (starRingEnd ℂ) (X j))
    rwa [s5CNrm_conj] at this
  have h5 : ‖∑ j, (D j : ℂ) * (A j i : ℂ)‖ ≤ Λ * s5Nrm D := by
    have e : (∑ j, (D j : ℂ) * (A j i : ℂ)) = ((∑ j, D j * A j i : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact s5_row_real_le h i D
  have hB0 : 0 ≤ s5Nrm D := s5Nrm_nonneg D
  exact c7_transpose_pointwise_dissipation h.one_le hρ (s5CNrm_nonneg X) hD hB0 _ _ _ _ u ζ h1
    (s5_cbil_norm_le h D X) h4 h5


/-- Integrate a weighted transpose estimate while retaining the full gradient
term. The representatives are those of the bounded multiplier on physical L². -/
theorem c7_integrate_weighted_gradient_estimate {d : ℕ}
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (T : Vec d → ℂ) (κ α : ℝ) (hT : Integrable T volume)
    (hb : ∀ᵐ x ∂volume, (T x).re +
      α * (∑ j, ‖(s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G j) :
        Lp ℂ 2 volume) x‖ ^ 2) ≤ κ *
      ‖(s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f : Lp ℂ 2 volume) x‖ ^ 2) :
    (∫ x, T x).re + α * (∑ j, ‖s5Mul volume hφ.measurable hφ.B_nonneg
      hφ.bound (G j)‖ ^ 2) ≤
      κ * ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f‖ ^ 2 := by
  have hGi : ∀ j, Integrable (fun x => ‖(s5Mul volume hφ.measurable
      hφ.B_nonneg hφ.bound (G j) : Lp ℂ 2 volume) x‖ ^ 2) volume :=
    fun j => (Lp.memLp _).norm.integrable_sq
  have hFi : Integrable (fun x => ‖(s5Mul volume hφ.measurable
      hφ.B_nonneg hφ.bound f : Lp ℂ 2 volume) x‖ ^ 2) volume :=
    (Lp.memLp _).norm.integrable_sq
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun j _ => hGi j)
  have hi := integral_mono_ae (hT.re.add (hsum.const_mul α)) (hFi.const_mul κ) hb
  simp only [Pi.add_apply] at hi
  rw [integral_add hT.re (hsum.const_mul α), integral_const_mul,
    integral_finsetSum _ (fun j _ => hGi j), integral_const_mul] at hi
  simp only [RCLike.re_eq_complex_re] at hi
  have hre : (∫ x, T x).re = ∫ x, (T x).re := by
    have h := Complex.reCLM.integral_comp_comm hT
    simpa only [Complex.reCLM_apply] using h.symm
  rw [hre]
  simpa only [← physicalL2_norm_sq] using hi

/-- Weighted energy retains the physical gradient for a transpose generator pair. -/
theorem c7_transpose_energy_dissipation {d : ℕ} {a : Vec d → Mat d} {Λ B q : ℝ} {φ : Vec d → ℝ}
    (hell : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (hφ : S5Weight φ B q) (i : Fin d) (ζ : ℂ)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
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
  have hS1 : Integrable (fun x => ∑ j, ∑ k, ((a x k j : ℝ) : ℂ) * Gf k x * J j x) volume :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      s5_integrable_coef (hcm k j) (hbound k j) (Gf k) (J j)
  have hS2 : Integrable (fun x => f x * (∑ j, ((a x j i : ℝ) : ℂ) * J j x)) volume := by
    have e : (fun x => f x * (∑ j, ((a x j i : ℝ) : ℂ) * J j x)) =
        fun x => ∑ j, ((a x j i : ℝ) : ℂ) * J j x * f x := by
      funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun j _ =>
      s5_integrable_coef (hcm j i) (hbound j i) (J j) f
  have hTint : Integrable (fun x => -(1 / 2 : ℂ) *
      (∑ j, ∑ k, ((a x k j : ℝ) : ℂ) * Gf k x * J j x) +
      ζ * (f x * (∑ j, ((a x j i : ℝ) : ℂ) * J j x))) volume :=
    (hS1.const_mul _).add (hS2.const_mul _)
  have hint : ∫ x, g x * w x = ∫ x, (-(1 / 2 : ℂ) *
      (∑ j, ∑ k, ((a x k j : ℝ) : ℂ) * Gf k x * J j x) +
      ζ * (f x * (∑ j, ((a x j i : ℝ) : ℂ) * J j x))) := by
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
  filter_upwards [hJa, s5_norm_sq_pt hφ f, hGn] with x hJx hnorm hGx
  have key := c7_transpose_pointwise_integrand_dissipation (hell x) (fun k => Gf k x) (f x)
    (fun j => coordinateDerivative j (fun y => φ y * φ y) x) (φ x * φ x) q i ζ
    (mul_self_nonneg _) (hφ.sq_grad x)
  have hs : s5CNrm (fun k => Gf k x) ^ 2 = ∑ k, ‖Gf k x‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  simp only [hJx, hnorm, hGx, ← Finset.mul_sum, hs] at ⊢ key
  simpa only [mul_assoc] using key


/-- Energy identity after applying a fixed bounded multiplier to the actual orbit. -/
theorem c7_semigroup_weighted_energy_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (M : E →L[ℂ] E) {f g : E} (hfg : Gen f g) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ),
      2 * (inner ℂ (M (P s.toNNReal f)) (M (P s.toNNReal g))).re) =
        ‖M (P t f)‖ ^ 2 - ‖M f‖ ^ 2 := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  have hu : Continuous (fun s : ℝ => M (P s.toNNReal f)) :=
    M.continuous.comp ((hP.cont f).comp continuous_real_toNNReal)
  have hv : Continuous (fun s : ℝ => M (P s.toNNReal g)) :=
    M.continuous.comp ((hP.cont g).comp continuous_real_toNNReal)
  have hder : ∀ s ∈ Set.Ioo (0 : ℝ) (t : ℝ),
      HasDerivWithinAt (fun r : ℝ => ‖M (P r.toNNReal f)‖ ^ 2)
        (2 * (inner ℂ (M (P s.toNNReal f)) (M (P s.toNNReal g))).re) (Set.Ioi s) s := by
    intro s hs
    let Mr : E →L[ℝ] E := M.restrictScalars ℝ
    have hd := Mr.hasFDerivAt.comp_hasDerivWithinAt s
      (hP.hasDerivWithinAt_orbit hfg s hs.1.le)
    have hn := hd.norm_sq
    change HasDerivWithinAt (fun r : ℝ => ‖M (P r.toNNReal f)‖ ^ 2)
      (2 * (inner ℂ (M (P s.toNNReal f)) (M (P s.toNNReal g))).re) (Set.Ici s) s at hn
    exact hn.mono Set.Ioi_subset_Ici_self
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (show (0 : ℝ) ≤ (t : ℝ) from t.property) (hu.norm.pow 2).continuousOn
    hder (((Complex.continuous_re.comp (hu.inner (𝕜 := ℂ) hv)).const_mul 2).intervalIntegrable 0 t)
  simpa only [Pi.pow_apply, Real.toNNReal_coe, Real.toNNReal_zero, hP.zero,
    ContinuousLinearMap.id_apply] using hi

/-- Integrate the coercive estimate for a boundedly weighted orbit. -/
theorem c7_integrated_weighted_gradient_energy
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}
    (hP : S5Semigroup P Gen) (M : E →L[ℂ] E) {f g : E} (hfg : Gen f g)
    (G : ℝ → Fin d → E) (hG : ∀ j, Continuous (fun s => G s j)) (μ K : ℝ)
    (hcoer : ∀ s : ℝ, μ * (∑ j, ‖M (G s j)‖ ^ 2) ≤
      -(inner ℂ (M (P s.toNNReal f)) (M (P s.toNNReal g))).re + K * ‖M (P s.toNNReal f)‖ ^ 2)
    (t : ℝ≥0) :
    μ * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖M (G s j)‖ ^ 2) ≤
      (‖M f‖ ^ 2 - ‖M (P t f)‖ ^ 2) / 2 +
        K * (∫ s in (0 : ℝ)..(t : ℝ), ‖M (P s.toNNReal f)‖ ^ 2) := by
  have hu : Continuous (fun s : ℝ => M (P s.toNNReal f)) :=
    M.continuous.comp ((hP.cont f).comp continuous_real_toNNReal)
  have hv : Continuous (fun s : ℝ => M (P s.toNNReal g)) :=
    M.continuous.comp ((hP.cont g).comp continuous_real_toNNReal)
  have hc := Complex.continuous_re.comp (hu.inner (𝕜 := ℂ) hv)
  have hn : Continuous (fun s => ∑ j, ‖M (G s j)‖ ^ 2) :=
    continuous_finset_sum _ fun j _ => (M.continuous.comp (hG j)).norm.pow 2
  have hleft := (hn.const_mul μ).intervalIntegrable (μ := (volume : Measure ℝ))
    (0 : ℝ) (t : ℝ)
  have hneg : IntervalIntegrable
      (fun s : ℝ => -(inner ℂ (M (P s.toNNReal f)) (M (P s.toNNReal g))).re)
      volume 0 t := hc.neg.intervalIntegrable 0 t
  have hK : IntervalIntegrable (fun s : ℝ => K * ‖M (P s.toNNReal f)‖ ^ 2)
      volume 0 t := ((hu.norm.pow 2).const_mul K).intervalIntegrable 0 t
  have hright := hneg.add hK
  have hi := intervalIntegral.integral_mono
    (show (0 : ℝ) ≤ (t : ℝ) from t.property) hleft hright hcoer
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hneg hK,
    intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hi
  have he := c7_semigroup_weighted_energy_identity hP M hfg t
  rw [intervalIntegral.integral_const_mul] at he
  nlinarith only [hi, he]


/-- The actual transpose orbit has an integrated weighted gradient bound. -/
theorem c7_transpose_orbit_integrated_weighted_gradient
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ t : ℝ≥0,
        (Λ⁻¹ / 4) * (∫ s in (0 : ℝ)..(t : ℝ),
          ∑ j, ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G s j)‖ ^ 2) ≤
          (‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f‖ ^ 2 -
            ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (S t f)‖ ^ 2) / 2 +
          (5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) *
            (∫ s in (0 : ℝ)..(t : ℝ),
              ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (S s.toNNReal f)‖ ^ 2) := by
  have hsem : S5Semigroup S (IsPhysicalComplexTransposeGeneratorPair a i ζ) :=
    ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
  obtain ⟨G, hG, hGc⟩ := physical_transpose_generator_orbit_continuous_gradient a i ζ ha
    (by linarith : 0 < Λ) (Filter.Eventually.of_forall hell)
    (fun s : ℝ => S s.toNNReal f) (fun s : ℝ => S s.toNNReal g)
    ((hsem.cont f).comp continuous_real_toNNReal)
    ((hsem.cont g).comp continuous_real_toNNReal)
    (fun s => hsem.map_gen hfg s.toNNReal)
  refine ⟨G, hG, hGc, fun t => c7_integrated_weighted_gradient_energy hsem
    (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound) hfg G hGc
    (Λ⁻¹ / 4) (5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) ?_ t⟩
  intro s
  obtain ⟨H, hH, hc⟩ := c7_transpose_energy_dissipation hell hmeas hφ i ζ
    (hsem.map_gen hfg s.toNNReal)
  have he := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    (S s.toNNReal f) H (G s) hH (hG s)
  rw [he] at hc
  linarith only [hc]

/-- The principal energy of the boundedly weighted gradient has the actual
mixed-form derivative, with no spatial derivative of the coefficients. -/
theorem c7_weighted_principal_energy_hasDerivAt {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ)
    (hG : ∀ j, HasDerivAt (fun r => G r j) (H j) s) :
    HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
      (a x j k : ℂ) * (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G r k)) x *
        star ((s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G r j)) x)).re)
      (2 * (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G s k)) x *
          star ((s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (H j)) x)).re) s := by
  apply c18_physical_principal_energy_hasDerivAt a ha hsym
  intro j
  exact (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt s (hG j)

/-- A twice-domain transpose orbit has the weighted principal-energy derivative
with the gradient of its actual generator image. -/
theorem c7_transpose_D2_weighted_principal_energy_derivative
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair a i ζ g h) :
    ∃ G H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal g) (H s)) ∧
      (∀ j, Continuous (fun s => H s j)) ∧
      ∀ s, HasDerivAt (fun r => (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G r k)) x *
          star ((s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G r j)) x)).re)
        (2 * (∫ x, ∑ j, ∑ k,
          (a x j k : ℂ) * (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G s k)) x *
            star ((s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (H s j)) x)).re) s := by
  obtain ⟨G, H, hG, hH, hder, hcont⟩ :=
    c18_physical_transpose_D2_orbit_gradient a i ζ ha hΛ hA P S hS hfg hgh
  have hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j := by
    filter_upwards [hA] with x hx
    exact hx.symm
  exact ⟨G, H, hG, hH, hcont, fun s =>
    c7_weighted_principal_energy_hasDerivAt a ha hsym hφ G (H s) s (hder s)⟩

/-- The actual twice-domain transpose orbit admits the shifted principal-energy
derivative at positive times, for bounded time-independent multipliers. -/
theorem c7_transpose_D2_shifted_principal_energy_derivative
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (W : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (B : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair a i ζ g h) :
    ∃ G H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal g) (H s)) ∧
      (∀ j, Continuous (fun s => H s j)) ∧
      ∀ (s : ℝ), 0 < s → HasDerivAt (fun t : ℝ => (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
        (W (G t k) - B k (S t.toNNReal f)) x *
          star ((W (G t j) - B j (S t.toNNReal f)) x)).re)
        (2 * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
          (W (G s k) - B k (S s.toNNReal f)) x *
            star ((W (H s j) - B j (S s.toNNReal g)) x)).re) s := by
  obtain ⟨G, H, hG, hH, hder, hcont⟩ :=
    c18_physical_transpose_D2_orbit_gradient a i ζ ha hΛ hA P S hS hfg hgh
  have hsem : S5Semigroup S (IsPhysicalComplexTransposeGeneratorPair a i ζ) :=
    ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
  have hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j := by
    filter_upwards [hA] with x hx
    exact hx.symm
  refine ⟨G, H, hG, hH, hcont, fun s hs => ?_⟩
  have hc : Continuous (fun t : ℝ => S t.toNNReal g) :=
    (hsem.cont g).comp continuous_real_toNNReal
  have he (t : ℝ) (ht : 0 ≤ t) :
      f + (∫ r in (0 : ℝ)..t, S r.toNNReal g) = S t.toNNReal f := by
    have hd : ∀ r ∈ Set.Ioo (0 : ℝ) t,
        HasDerivWithinAt (fun q : ℝ => S q.toNNReal f)
          (S r.toNNReal g) (Set.Ioi r) r := by
      intro r hr
      exact (hsem.hasDerivWithinAt_orbit hfg r hr.1.le).mono Set.Ioi_subset_Ici_self
    have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
      ((hsem.cont f).comp continuous_real_toNNReal).continuousOn hd
      (hc.intervalIntegrable (μ := volume) 0 t)
    rw [hi]
    simp only [Function.comp_apply, Real.toNNReal_zero, hsem.zero, ContinuousLinearMap.id_apply]
    abel
  have hu : HasDerivAt (fun t : ℝ => S t.toNNReal f) (S s.toNNReal g) s := by
    apply ((hc.integral_hasStrictDerivAt 0 s).hasDerivAt.const_add f).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (he t ht.le).symm
  exact c7_shifted_principal_energy_hasDerivAt a ha hsym W B
    (fun t => S t.toNNReal f) (S s.toNNReal g) G (H s) s hu (hder s)

/-- The transpose drift is the divergence of the same anisotropic flux as
its principal part, shifted in the force direction. -/
theorem c7_transpose_shifted_flux_algebra {d : ℕ} (a : Mat d)
    (hsym : ∀ j k, a j k = a k j) (i : Fin d) (ζ u : ℂ)
    (G V : Fin d → ℂ) :
    (∑ j, ∑ k, (a k j : ℂ) *
      (G k - if k = i then 2 * ζ * u else 0) * V j) =
      (∑ j, ∑ k, (a k j : ℂ) * G k * V j) -
        2 * ζ * (u * (∑ j, (a j i : ℂ) * V j)) := by
  have h : ∀ j, (∑ k, (a k j : ℂ) *
      (G k - if k = i then 2 * ζ * u else 0) * V j) =
      (∑ k, (a k j : ℂ) * G k * V j) - (a i j : ℂ) * (2 * ζ * u) * V j := by
    intro j
    have hp : ∀ k, (a k j : ℂ) *
        (G k - if k = i then 2 * ζ * u else 0) * V j =
        (a k j : ℂ) * G k * V j -
          if k = i then (a i j : ℂ) * (2 * ζ * u) * V j else 0 := by
      intro k
      split_ifs with hk
      · subst k
        ring
      · ring
    simp only [hp, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [h, Finset.sum_sub_distrib]
  have he : (∑ j, (a i j : ℂ) * (2 * ζ * u) * V j) =
      2 * ζ * (u * (∑ j, (a j i : ℂ) * V j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym i j]
    ring
  rw [he]

/-- Weak generator identity with the transpose drift absorbed into a shifted
flux, without differentiating the coefficient field. -/
theorem c7_transpose_generator_shifted_flux {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) u G ∧
      ∀ v V, IsPhysicalH1Graph volume (Or.inl rfl) v V →
        (∫ x, g x * v x) = -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
          (a x k j : ℂ) * (G k x - if k = i then 2 * ζ * u x else 0) * V j x) := by
  obtain ⟨G, hG, hw⟩ := hug
  refine ⟨G, hG, fun v V hv => ?_⟩
  have hP : Integrable (fun x => ∑ j, ∑ k, (a x k j : ℂ) * G k x * V j x) volume :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      ((ha k j).fun_mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (V j))
  have hD : Integrable (fun x => u x * (∑ j, (a x j i : ℂ) * V j x)) volume := by
    have he : (fun x => u x * (∑ j, (a x j i : ℂ) * V j x)) =
        fun x => ∑ j, ((a x j i : ℂ) * V j x) * u x := by
      funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [he]
    exact integrable_finsetSum _ fun j _ =>
      ((ha j i).fun_mul (r := 2) (Lp.memLp (V j))).integrable_mul (Lp.memLp u)
  have hi : (∫ x, ∑ j, ∑ k, (a x k j : ℂ) *
      (G k x - if k = i then 2 * ζ * u x else 0) * V j x) =
      (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * V j x) -
        2 * ζ * (∫ x, u x * (∑ j, (a x j i : ℂ) * V j x)) := by
    calc
      _ = ∫ x, ((∑ j, ∑ k, (a x k j : ℂ) * G k x * V j x) -
          2 * ζ * (u x * (∑ j, (a x j i : ℂ) * V j x))) := by
        apply integral_congr_ae
        filter_upwards [hsym] with x hx
        exact c7_transpose_shifted_flux_algebra (a x) hx i ζ (u x)
          (fun k => G k x) (fun j => V j x)
      _ = _ := by rw [integral_sub hP (hD.const_mul _), integral_const_mul]
  rw [hi, hw v V hv]
  ring

/-- The shifted transpose identity can use any representative of the actual
physical gradient. -/
theorem c7_transpose_generator_shifted_flux_of_graph {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (V : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v V) :
    (∫ x, g x * v x) = -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
      (a x k j : ℂ) * (G k x - if k = i then 2 * ζ * u x else 0) * V j x) := by
  obtain ⟨K, hK, hw⟩ := c7_transpose_generator_shifted_flux a i ζ ha hsym hug
  have he := physicalH1Graph_gradient_unique volume (Or.inl rfl) u K G hK hu
  rw [← he]
  exact hw v V hv

/-- The shifted flux is tested against the squared-weight conjugate of the
actual generator image, retaining the weight-gradient term. -/
theorem c7_transpose_shifted_flux_weighted_generator_test {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q) :
    (∫ x, g x * (((φ x * φ x : ℝ) : ℂ) * star (g x))) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) *
        (G k x - if k = i then 2 * ζ * u x else 0) *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) := by
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_mul_smooth (fun x => φ x * φ x)
    hφ.sq_smooth hφ.memLp_sq hφ.memLp_sq_deriv (star g) (fun j => star (H j))
    (s5_isPhysicalH1Graph_star g H hg)
  have ht := c7_transpose_generator_shifted_flux_of_graph a i ζ ha hsym hug G hu w J hw
  have hl : (∫ x, g x * w x) =
      ∫ x, g x * (((φ x * φ x : ℝ) : ℂ) * star (g x)) := by
    apply integral_congr_ae
    filter_upwards [hwr, Lp.coeFn_star g] with x hwx hs
    rw [hwx, hs]
    rfl
  have hr : (∫ x, ∑ j, ∑ k, (a x k j : ℂ) *
        (G k x - if k = i then 2 * ζ * u x else 0) * J j x) =
      ∫ x, ∑ j, ∑ k, (a x k j : ℂ) *
        (G k x - if k = i then 2 * ζ * u x else 0) *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hJr, ae_all_iff.mpr (fun j => Lp.coeFn_star (H j)),
      Lp.coeFn_star g] with x hj hh hgx
    simp only [hj, hh, hgx, Pi.star_apply]
  rw [hl, hr] at ht
  exact ht

/-- The D² transpose energy identity specialized to a Davies multiplier and
its force-direction shift. -/
theorem c7_transpose_D2_davies_shifted_energy_derivative
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair a i ζ g h) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
      fun j => if j = i then (2 * ζ) • W else 0
    ∃ G H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal g) (H s)) ∧
      (∀ j, Continuous (fun s => H s j)) ∧
      ∀ (s : ℝ), 0 < s → HasDerivAt (fun t : ℝ => (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
        (W (G t k) - K k (S t.toNNReal f)) x *
          star ((W (G t j) - K j (S t.toNNReal f)) x)).re)
        (2 * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
          (W (G s k) - K k (S s.toNNReal f)) x *
            star ((W (H s j) - K j (S s.toNNReal g)) x)).re) s := by
  exact c7_transpose_D2_shifted_principal_energy_derivative a i ζ ha hΛ hA
    (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound)
    (fun j => if j = i then (2 * ζ) • (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound) else 0)
    P S hS hfg hgh

/-- The squared weighted generator norm is the real part of the shifted
transpose flux tested against the squared-weight conjugate generator. -/
theorem c7_transpose_shifted_flux_weighted_generator_norm {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q) :
    ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g‖ ^ 2 =
      (-(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) *
        (G k x - if k = i then 2 * ζ * u x else 0) *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)))).re := by
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
    filter_upwards [hwr', Lp.coeFn_star g] with x hwx hs
    rw [hwx]
    rfl
  rw [hl, c7_transpose_shifted_flux_weighted_generator_test a i ζ ha hsym hug G H hu hg hφ] at hi
  have hr := congrArg Complex.re hi
  have hn : (inner ℂ (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g)
      (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g)).re =
      ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa only [RCLike.re_eq_complex_re] using
      (RCLike.re_ofReal_pow (K := ℂ) ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g‖ 2)
  rw [hn] at hr
  exact hr

/-- The shifted-energy cross term differs from the squared-weight test by
precisely the weight-gradient and force-direction commutators. -/
theorem c7_shifted_energy_test_algebra {d : ℕ} (A : Fin d → Fin d → ℂ)
    (i : Fin d) (c ρ g : ℂ) (X H D : Fin d → ℂ) :
    (∑ j, ∑ k, A j k * X k * (ρ * star (H j - if j = i then c * g else 0))) =
      (∑ j, ∑ k, A j k * X k * (ρ * star (H j) + star g * D j)) -
        star g * ((∑ j, ∑ k, A j k * X k * D j) +
          ρ * star c * (∑ k, A i k * X k)) := by
  classical
  have h : ∀ j k, A j k * X k * (ρ * star (H j - if j = i then c * g else 0)) =
      A j k * X k * (ρ * star (H j) + star g * D j) -
        star g * (A j k * X k * D j +
          if j = i then ρ * star c * (A i k * X k) else 0) := by
    intro j k
    split_ifs with hj
    · subst j
      simp only [star_sub, star_mul]
      ring
    · simp only [sub_zero]
      ring
  have hs : (∑ j, ∑ k, if j = i then ρ * star c * (A i k * X k) else 0) =
      ρ * star c * (∑ k, A i k * X k) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum]
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, hs]

/-- Ellipticity bounds both commutators by the shifted flux and the weighted
generator value, with no derivatives of the coefficient field. -/
theorem c7_shifted_energy_commutator_norm {d : ℕ}
    {A : Fin d → Fin d → ℝ} {Λ : ℝ} (hA : S5Elliptic A Λ)
    (i : Fin d) (c g : ℂ) (ρ : ℝ) (X : Fin d → ℂ) (D : Fin d → ℝ) :
    ‖star g * ((∑ j, ∑ k, (A j k : ℂ) * X k * (D j : ℂ)) +
      (ρ : ℂ) * star c * (∑ k, (A i k : ℂ) * X k))‖ ≤
      (2 * Λ * (s5Nrm D + |ρ| * ‖c‖) * s5CNrm X) * ‖g‖ := by
  have hbil : ‖∑ j, ∑ k, (A j k : ℂ) * X k * (D j : ℂ)‖ ≤
      2 * Λ * s5Nrm D * s5CNrm X := by
    have he : (∑ j, ∑ k, (A j k : ℂ) * X k * (D j : ℂ)) =
        ∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * X k := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he]
    exact s5_cbil_norm_le hA D X
  have hrow : ‖∑ k, (A i k : ℂ) * X k‖ ≤ 2 * Λ * s5CNrm X := by
    have he : (∑ k, (A i k : ℂ) * X k) = ∑ k, (A k i : ℂ) * X k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hA.symm i k]
    rw [he]
    exact s5_row_norm_le hA i X
  have hc : ‖(ρ : ℂ) * star c * (∑ k, (A i k : ℂ) * X k)‖ ≤
      (|ρ| * ‖c‖) * (2 * Λ * s5CNrm X) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
    exact mul_le_mul_of_nonneg_left hrow (mul_nonneg (abs_nonneg ρ) (norm_nonneg c))
  calc
    _ ≤ ‖g‖ * (‖∑ j, ∑ k, (A j k : ℂ) * X k * (D j : ℂ)‖ +
        ‖(ρ : ℂ) * star c * (∑ k, (A i k : ℂ) * X k)‖) := by
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg g)
    _ ≤ ‖g‖ * (2 * Λ * s5Nrm D * s5CNrm X +
        (|ρ| * ‖c‖) * (2 * Λ * s5CNrm X)) :=
      mul_le_mul_of_nonneg_left (add_le_add hbil hc) (norm_nonneg g)
    _ = _ := by ring

/-- The Davies weight controls both shifted-energy commutators by the
squared weight, the shifted flux, and the generator value. -/
theorem c7_davies_shifted_energy_commutator_norm {d : ℕ}
    {A : Fin d → Fin d → ℝ} {Λ : ℝ} (hA : S5Elliptic A Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (x : Vec d) (i : Fin d) (c g : ℂ) (X : Fin d → ℂ) :
    ‖star g * ((∑ j, ∑ k, (A j k : ℂ) * X k *
      (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) +
      ((φ x * φ x : ℝ) : ℂ) * star c * (∑ k, (A i k : ℂ) * X k))‖ ≤
      (2 * Λ * ((2 * q + ‖c‖) * (φ x * φ x)) * s5CNrm X) * ‖g‖ := by
  have hΛ : 0 ≤ Λ := by linarith [hA.one_le]
  have hρ : 0 ≤ φ x * φ x := mul_self_nonneg _
  have hgrad := hφ.sq_grad x
  have hX := s5CNrm_nonneg X
  have hbase := c7_shifted_energy_commutator_norm hA i c g (φ x * φ x) X
    (fun j => coordinateDerivative j (fun y => φ y * φ y) x)
  rw [abs_of_nonneg hρ] at hbase
  calc
    _ ≤ (2 * Λ * (s5Nrm (fun j => coordinateDerivative j
        (fun y => φ y * φ y) x) + (φ x * φ x) * ‖c‖) * s5CNrm X) * ‖g‖ := hbase
    _ ≤ (2 * Λ * (2 * q * (φ x * φ x) + (φ x * φ x) * ‖c‖) *
        s5CNrm X) * ‖g‖ := by
      gcongr
    _ = _ := by ring

/-- Young's inequality absorbs half the weighted generator density and leaves
only the weighted shifted-flux density. -/
theorem c7_davies_shifted_energy_commutator_young {d : ℕ}
    {A : Fin d → Fin d → ℝ} {Λ : ℝ} (hA : S5Elliptic A Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (x : Vec d) (i : Fin d) (c g : ℂ) (X : Fin d → ℂ) :
    ‖star g * ((∑ j, ∑ k, (A j k : ℂ) * X k *
      (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) +
      ((φ x * φ x : ℝ) : ℂ) * star c * (∑ k, (A i k : ℂ) * X k))‖ ≤
      (1 / 2 : ℝ) * (φ x * φ x) * ‖g‖ ^ 2 +
      (1 / 2 : ℝ) * (2 * Λ * (2 * q + ‖c‖)) ^ 2 *
        (φ x * φ x) * s5CNrm X ^ 2 := by
  have hb := c7_davies_shifted_energy_commutator_norm hA hφ x i c g X
  have hsq := mul_nonneg (mul_self_nonneg (φ x))
    (sq_nonneg (‖g‖ - (2 * Λ * (2 * q + ‖c‖)) * s5CNrm X))
  nlinarith [hsq]

/-- Integrated Davies commutator estimate on the actual weighted L² classes. -/
theorem c7_davies_shifted_energy_commutator_integral {d : ℕ}
    (a : Vec d → Mat d) {Λ : ℝ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (i : Fin d) (c : ℂ) (g : Lp ℂ 2 (volume : Measure (Vec d)))
    (X : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    ‖∫ x, star (g x) * ((∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) +
      ((φ x * φ x : ℝ) : ℂ) * star c * (∑ k, (a x i k : ℂ) * X k x))‖ ≤
      (1 / 2 : ℝ) * ‖W g‖ ^ 2 +
      (1 / 2 : ℝ) * (2 * Λ * (2 * q + ‖c‖)) ^ 2 *
        (∑ j, ‖W (X j)‖ ^ 2) := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let C : ℝ := (1 / 2 : ℝ) * (2 * Λ * (2 * q + ‖c‖)) ^ 2
  let F : Vec d → ℂ := fun x => star (g x) * ((∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) +
      ((φ x * φ x : ℝ) : ℂ) * star c * (∑ k, (a x i k : ℂ) * X k x))
  have hleft : MemLp (fun x => ∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) 2 volume :=
    memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun k _ =>
      ((ha j k).fun_mul (r := 2) (Lp.memLp (X k))).fun_mul (r := 2) (hφ.memLp_sq_deriv j)
  have hrow : MemLp (fun x => ∑ k, (a x i k : ℂ) * X k x) 2 volume :=
    memLp_finsetSum _ fun k _ => (ha i k).fun_mul (r := 2) (Lp.memLp (X k))
  have hright : MemLp (fun x => ((φ x * φ x : ℝ) : ℂ) * star c *
      (∑ k, (a x i k : ℂ) * X k x)) 2 volume :=
    by simpa only [mul_comm (star c)] using
      ((hφ.memLp_sq).const_mul (star c)).fun_mul (r := 2) hrow
  have hF : Integrable F volume := (Lp.memLp g).star.integrable_mul (hleft.add hright)
  have hN : Integrable (fun x => ∑ j, ‖W (X j) x‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (W (X j))).norm.integrable_sq
  have hg : Integrable (fun x => ‖W g x‖ ^ 2) volume := (Lp.memLp (W g)).norm.integrable_sq
  have hp : ∀ᵐ x ∂volume, ‖F x‖ ≤ (1 / 2 : ℝ) * ‖W g x‖ ^ 2 +
      C * (∑ j, ‖W (X j) x‖ ^ 2) := by
    filter_upwards [hA, s5Mul_coe volume hφ.measurable hφ.B_nonneg hφ.bound g,
      ae_all_iff.mpr (fun j => s5Mul_coe volume hφ.measurable hφ.B_nonneg hφ.bound (X j))]
      with x hx hwg hwX
    have hb := c7_davies_shifted_energy_commutator_young hx hφ x i c (g x) (fun k => X k x)
    have hnorm : s5CNrm (fun k => X k x) ^ 2 = ∑ k, ‖X k x‖ ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
    simp only [W, hwg, hwX, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs, ← Finset.mul_sum, hnorm] at *
    dsimp [F, C] at *
    simp only [norm_mul]
    nlinarith
  have hi := integral_mono_ae hF.norm ((hg.const_mul (1 / 2 : ℝ)).add (hN.const_mul C)) hp
  simp only [Pi.add_apply] at hi
  have hNeq : (∫ x, ∑ j, ‖W (X j) x‖ ^ 2) = ∑ j, ‖W (X j)‖ ^ 2 := by
    rw [integral_finsetSum _ fun j _ => (Lp.memLp (W (X j))).norm.integrable_sq]
    exact Finset.sum_congr rfl fun j _ => (physicalL2_norm_sq volume (W (X j))).symm
  rw [integral_add (hg.const_mul (1 / 2 : ℝ)) (hN.const_mul C),
    integral_const_mul, integral_const_mul, hNeq, ← physicalL2_norm_sq] at hi
  exact (norm_integral_le_integral_norm (μ := volume) F).trans hi

/-- The integrated shifted energy cross term is the squared-weight test
minus its explicit commutator, for L² flux and generator representatives. -/
theorem c7_davies_shifted_energy_test_integral {d : ℕ}
    (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (i : Fin d) (c : ℂ) (g : Lp ℂ 2 (volume : Measure (Vec d)))
    (X H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (((φ x * φ x : ℝ) : ℂ) * star (H j x - if j = i then c * g x else 0))) =
      (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * X k x *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) -
      (∫ x, star (g x) * ((∑ j, ∑ k, (a x j k : ℂ) * X k x *
        (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) +
        ((φ x * φ x : ℝ) : ℂ) * star c * (∑ k, (a x i k : ℂ) * X k x))) := by
  have hJ (j : Fin d) : MemLp (fun x => ((φ x * φ x : ℝ) : ℂ) * star (H j x) +
      star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) 2 volume := by
    apply MemLp.add ((hφ.memLp_sq).fun_mul (r := 2) (Lp.memLp (H j)).star)
    simpa only [Pi.star_apply, mul_comm] using (hφ.memLp_sq_deriv j).fun_mul (r := 2) (Lp.memLp g).star
  have hT : Integrable (fun x => ∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
        star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) volume :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      ((ha j k).fun_mul (r := 2) (Lp.memLp (X k))).integrable_mul (hJ j)
  have hleft : MemLp (fun x => ∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) 2 volume :=
    memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun k _ =>
      ((ha j k).fun_mul (r := 2) (Lp.memLp (X k))).fun_mul (r := 2) (hφ.memLp_sq_deriv j)
  have hrow : MemLp (fun x => ∑ k, (a x i k : ℂ) * X k x) 2 volume :=
    memLp_finsetSum _ fun k _ => (ha i k).fun_mul (r := 2) (Lp.memLp (X k))
  have hright : MemLp (fun x => ((φ x * φ x : ℝ) : ℂ) * star c *
      (∑ k, (a x i k : ℂ) * X k x)) 2 volume := by
    simpa only [mul_comm (star c)] using
      ((hφ.memLp_sq).const_mul (star c)).fun_mul (r := 2) hrow
  have hF : Integrable (fun x => star (g x) * ((∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) +
      ((φ x * φ x : ℝ) : ℂ) * star c * (∑ k, (a x i k : ℂ) * X k x))) volume :=
    (Lp.memLp g).star.integrable_mul (hleft.add hright)
  calc
    _ = ∫ x, ((∑ j, ∑ k, (a x j k : ℂ) * X k x *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) -
        star (g x) * ((∑ j, ∑ k, (a x j k : ℂ) * X k x *
          (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) +
          ((φ x * φ x : ℝ) : ℂ) * star c * (∑ k, (a x i k : ℂ) * X k x))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => c7_shifted_energy_test_algebra
        (fun j k => (a x j k : ℂ)) i c ((φ x * φ x : ℝ) : ℂ) (g x)
        (fun k => X k x) (fun j => H j x)
        (fun j => (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))
    _ = _ := integral_sub hT hF

/-- The actual transpose generator turns the weighted shifted-energy cross
term into generator dissipation and the explicit commutator. -/
theorem c7_transpose_shifted_energy_cross_identity {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let X : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
      fun k => G k - if k = i then (2 * ζ) • u else 0
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (((φ x * φ x : ℝ) : ℂ) * star (H j x - if j = i then (2 * ζ) * g x else 0))).re =
      -2 * ‖W g‖ ^ 2 -
      (∫ x, star (g x) * ((∑ j, ∑ k, (a x j k : ℂ) * X k x *
        (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) +
        ((φ x * φ x : ℝ) : ℂ) * star (2 * ζ) * (∑ k, (a x i k : ℂ) * X k x))).re := by
  let X : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun k => G k - if k = i then (2 * ζ) • u else 0
  have hX (k : Fin d) : ∀ᵐ x ∂volume, X k x = G k x -
      if k = i then (2 * ζ) * u x else 0 := by
    by_cases hk : k = i
    · subst k
      filter_upwards [Lp.coeFn_sub (G i) ((2 * ζ) • u), Lp.coeFn_smul (2 * ζ) u] with x hs hm
      simpa [X, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hs.trans (by simp [hm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
    · filter_upwards [] with x
      simp [X, hk]
  have ht : (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * X k x *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ))) =
      ∫ x, ∑ j, ∑ k, (a x k j : ℂ) *
        (G k x - if k = i then 2 * ζ * u x else 0) *
        (((φ x * φ x : ℝ) : ℂ) * star (H j x) +
          star (g x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [hsym, ae_all_iff.mpr hX] with x hs hx
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hx k, hs j k]
  have hi := c7_davies_shifted_energy_test_integral a ha hφ i (2 * ζ) g X H
  rw [ht] at hi
  have hn := c7_transpose_shifted_flux_weighted_generator_norm a i ζ ha hsym hug G H hu hg hφ
  have hs (z : ℂ) : (-(1 / 2 : ℂ) * z).re = -(1 / 2 : ℝ) * z.re := by
    simp
  rw [hs] at hn
  have hr := congrArg Complex.re hi
  simp only [Complex.sub_re] at hr
  dsimp only
  linarith

/-- The actual transpose generator dissipates the shifted energy up to a
uniform Davies commutator bound. -/
theorem c7_transpose_shifted_energy_cross_le {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ) {Λ : ℝ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let X : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
      fun k => G k - if k = i then (2 * ζ) • u else 0
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (((φ x * φ x : ℝ) : ℂ) * star (H j x - if j = i then (2 * ζ) * g x else 0))).re ≤
      -(3 / 2 : ℝ) * ‖W g‖ ^ 2 +
      (1 / 2 : ℝ) * (2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 *
        (∑ j, ‖W (X j)‖ ^ 2) := by
  let X : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun k => G k - if k = i then (2 * ζ) • u else 0
  have hsym : ∀ᵐ x ∂volume, ∀ j k, a x j k = a x k j := by
    filter_upwards [hA] with x hx
    exact hx.symm
  have hi := c7_transpose_shifted_energy_cross_identity a i ζ ha hsym hug G H hu hg hφ
  have hb := c7_davies_shifted_energy_commutator_integral a ha hA hφ i (2 * ζ) g X
  let F : ℂ := ∫ x, star (g x) * ((∑ j, ∑ k, (a x j k : ℂ) * X k x *
        (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) +
        ((φ x * φ x : ℝ) : ℂ) * star (2 * ζ) * (∑ k, (a x i k : ℂ) * X k x))
  have hr : -F.re ≤ ‖F‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  dsimp only [F] at hr
  dsimp only at hi hb ⊢
  linarith


/-- Multiplication by the Davies weight commutes with the shifted flux, and
its quadratic cross term has the unweighted integral representation. -/
theorem c7_davies_shifted_cross_weight_identity {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (u g : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
      fun j => if j = i then (2 * ζ) • W else 0
    let X : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
      fun j => G j - if j = i then (2 * ζ) • u else 0
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * (W (G k) - K k u) x *
      star ((W (H j) - K j g) x)) =
    ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (((φ x * φ x : ℝ) : ℂ) * star (H j x - if j = i then (2 * ζ) * g x else 0)) := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
    fun j => if j = i then (2 * ζ) • W else 0
  let X : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun j => G j - if j = i then (2 * ζ) • u else 0
  let Y : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun j => H j - if j = i then (2 * ζ) • g else 0
  have hWX (j : Fin d) : W (G j) - K j u = W (X j) := by
    by_cases hj : j = i <;> simp [X, K, hj, map_sub, map_smul]
  have hWY (j : Fin d) : W (H j) - K j g = W (Y j) := by
    by_cases hj : j = i <;> simp [Y, K, hj, map_sub, map_smul]
  have hY (j : Fin d) : ∀ᵐ x ∂volume, Y j x = H j x -
      if j = i then (2 * ζ) * g x else 0 := by
    by_cases hj : j = i
    · subst j
      filter_upwards [Lp.coeFn_sub (H i) ((2 * ζ) • g), Lp.coeFn_smul (2 * ζ) g] with x hs hm
      simpa [Y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hs.trans (by simp [hm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
    · filter_upwards [] with x
      simp [Y, hj]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun j => s5Mul_coe volume hφ.measurable hφ.B_nonneg hφ.bound (X j)),
    ae_all_iff.mpr (fun j => s5Mul_coe volume hφ.measurable hφ.B_nonneg hφ.bound (Y j)),
    ae_all_iff.mpr hY] with x hx hy hz
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [hWX k, hWY j, hx k, hy j, hz j]
  simp only [star_mul, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring


/-- The Davies shifted-flux cross term is controlled by the same principal
energy, with a constant depending only on ellipticity, force and weight. -/
theorem c7_transpose_shifted_energy_cross_principal_le {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ) {Λ : ℝ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hg : IsPhysicalH1Graph volume (Or.inl rfl) g H)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let X : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
      fun k => G k - if k = i then (2 * ζ) • u else 0
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * X k x *
      (((φ x * φ x : ℝ) : ℂ) * star (H j x - if j = i then (2 * ζ) * g x else 0))).re ≤
      -(3 / 2 : ℝ) * ‖W g‖ ^ 2 +
      (1 / 2 : ℝ) * (2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 * Λ *
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * (W (X k)) x * star ((W (X j)) x)).re := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let X : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun k => G k - if k = i then (2 * ζ) • u else 0
  have hc := c7_transpose_shifted_energy_cross_le a i ζ ha hA hug G H hu hg hφ
  have hp := c18_physical_principal_energy_coercive a ha hΛ hA (fun j => W (X j))
  have hm := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg (2 * Λ * (2 * q + ‖2 * ζ‖))))
  dsimp only [W, X] at hc hp hm ⊢
  nlinarith only [hc, hm]


/-- The shifted principal energy of a twice-generator-domain transpose orbit
satisfies a uniform Davies differential inequality at positive times. -/
theorem c7_transpose_D2_davies_shifted_energy_derivative_le
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair a i ζ g h) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
      fun j => if j = i then (2 * ζ) • W else 0
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      ∀ (s : ℝ), 0 < s → ∃ q' : ℝ,
        HasDerivAt (fun t : ℝ => (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
          (W (G t k) - K k (S t.toNNReal f)) x *
            star ((W (G t j) - K j (S t.toNNReal f)) x)).re) q' s ∧
        q' ≤ (2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 * Λ *
          (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
            (W (G s k) - K k (S s.toNNReal f)) x *
              star ((W (G s j) - K j (S s.toNNReal f)) x)).re := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
    fun j => if j = i then (2 * ζ) • W else 0
  have hsem : S5Semigroup S (IsPhysicalComplexTransposeGeneratorPair a i ζ) :=
    ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
  obtain ⟨G, H, hG, hH, hHc, hd⟩ :=
    c7_transpose_D2_davies_shifted_energy_derivative a i ζ ha hΛ hA hφ P S hS hfg hgh
  refine ⟨G, hG, ?_⟩
  intro s hs
  refine ⟨_, hd s hs, ?_⟩
  let u := S s.toNNReal f
  let v := S s.toNNReal g
  have hWX (j : Fin d) : W (G s j - if j = i then (2 * ζ) • u else 0) =
      W (G s j) - K j u := by
    by_cases hj : j = i <;> simp [K, hj, map_sub, map_smul]
  dsimp only [W, K, u] at hWX
  have hc := c7_transpose_shifted_energy_cross_principal_le a i ζ ha hΛ hA
    (hsem.map_gen hfg s.toNNReal) (G s) (H s) (hG s hs.le) (hH s) hφ
  have hi := c7_davies_shifted_cross_weight_identity a i ζ u v (G s) (H s) hφ
  dsimp only at hc hi
  rw [← hi] at hc
  dsimp only [u, v, W, K] at hc ⊢
  simp only [hWX] at hc
  nlinarith only [hc, sq_nonneg ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (S s.toNNReal g)‖]


/-- The actual shifted transpose energy obeys exponential growth control
between positive times, uniformly in coefficient derivatives. -/
theorem c7_transpose_D2_davies_shifted_energy_growth
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair a i ζ g h) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
      fun j => if j = i then (2 * ζ) • W else 0
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, 0 ≤ s → IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      ∀ (t₀ t : ℝ), 0 < t₀ → t₀ ≤ t →
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
          (W (G t k) - K k (S t.toNNReal f)) x *
            star ((W (G t j) - K j (S t.toNNReal f)) x)).re ≤
        (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
          (W (G t₀ k) - K k (S t₀.toNNReal f)) x *
            star ((W (G t₀ j) - K j (S t₀.toNNReal f)) x)).re *
          Real.exp (((2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 * Λ) * (t - t₀)) := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
    fun j => if j = i then (2 * ζ) • W else 0
  obtain ⟨G, hG, hd⟩ :=
    c7_transpose_D2_davies_shifted_energy_derivative_le a i ζ ha hΛ hA hφ P S hS hfg hgh
  refine ⟨G, hG, ?_⟩
  intro t₀ t ht₀ htt
  let E (s : ℝ) := (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
    (W (G s k) - K k (S s.toNNReal f)) x *
      star ((W (G s j) - K j (S s.toNNReal f)) x)).re
  let C := (2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 * Λ
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


/-- The shifted principal energy is bounded by the weighted gradient and shift. -/
theorem c7_shifted_principal_energy_upper {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (U V : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
      (U k - V k) x * star ((U j - V j) x)).re ≤
      2 * Λ * ((∑ j, ‖U j‖ ^ 2) + ∑ j, ‖V j‖ ^ 2) := by
  have hb := c18_physical_principal_energy_upper a ha hA (fun j => U j - V j)
  have hs : (∑ j, ‖U j - V j‖ ^ 2) ≤
      2 * ((∑ j, ‖U j‖ ^ 2) + ∑ j, ‖V j‖ ^ 2) := by
    calc
      _ ≤ ∑ j, (2 * ‖U j‖ ^ 2 + 2 * ‖V j‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have ht := norm_sub_le (U j) (V j)
        nlinarith [norm_nonneg (U j - V j), norm_nonneg (U j), norm_nonneg (V j),
          sq_nonneg (‖U j‖ - ‖V j‖)]
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  nlinarith only [hb, mul_le_mul_of_nonneg_left hs hΛ]

/-- The force shift has exactly one nonzero coordinate. -/
theorem c7_shifted_force_norm_sq {d : ℕ} (i : Fin d) (ζ : ℂ)
    (W : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∑ j : Fin d, ‖(if j = i then (2 * ζ) • W u else 0)‖ ^ 2) =
      ‖2 * ζ‖ ^ 2 * ‖W u‖ ^ 2 := by
  classical
  rw [Finset.sum_eq_single i]
  · simp [norm_smul, mul_pow]
  · intro j hj hji
    simp [hji]
  · simp

/-- Positive-time growth converts an interval energy integral to an endpoint bound. -/
theorem c7_positive_time_energy_endpoint (q : ℝ → ℝ) (K t : ℝ)
    (hK : 0 ≤ K) (ht : 0 < t)
    (hc : ContinuousOn q (Set.Icc (t / 2) t))
    (hn : ∀ s ∈ Set.Icc (t / 2) t, 0 ≤ q s)
    (hg : ∀ s ∈ Set.Icc (t / 2) t,
      q t ≤ q s * Real.exp (K * (t - s))) :
    (t / 2) * (q t * Real.exp (-K * t)) ≤ ∫ s in (t / 2)..t, q s := by
  have hhalf : t / 2 < t := by linarith
  have hc' : ContinuousOn q (Set.uIcc (t / 2) t) := by
    simpa [Set.uIcc_of_le hhalf.le] using hc
  obtain ⟨s, hs, he⟩ := exists_eq_interval_average (ne_of_lt hhalf) hc'
  rw [Set.uIoo_of_lt hhalf] at hs
  have hs' : s ∈ Set.Icc (t / 2) t := ⟨hs.1.le, hs.2.le⟩
  have hb : q t * Real.exp (-K * t) ≤ q s := by
    calc
      _ ≤ (q s * Real.exp (K * (t - s))) * Real.exp (-K * t) :=
        mul_le_mul_of_nonneg_right (hg s hs') (Real.exp_pos _).le
      _ = q s * Real.exp (-K * s) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2 <;> ring
      _ ≤ q s := mul_le_of_le_one_right (hn s hs')
        (Real.exp_le_one_iff.mpr (by nlinarith [hs'.1]))
  rw [interval_average_eq_div] at he
  have hden : 0 < t - t / 2 := by linarith
  have he' := (eq_div_iff hden.ne').mp he
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ t / 2 by linarith)
  nlinarith only [hm, he']


/-- Transfer positive-time energy growth to full-interval gradient and force bounds. -/
theorem c7_energy_endpoint_of_integrated_bounds
    (E A F : ℝ → ℝ) (K L t a b : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (ht : 0 < t)
    (hE : ContinuousOn E (Set.Icc (t / 2) t))
    (hEn : ∀ s ∈ Set.Icc (t / 2) t, 0 ≤ E s)
    (hg : ∀ s ∈ Set.Icc (t / 2) t,
      E t ≤ E s * Real.exp (K * (t - s)))
    (hA : ContinuousOn A (Set.Icc 0 t)) (hF : ContinuousOn F (Set.Icc 0 t))
    (hAn : ∀ s ∈ Set.Icc 0 t, 0 ≤ A s)
    (hFn : ∀ s ∈ Set.Icc 0 t, 0 ≤ F s)
    (hupper : ∀ s ∈ Set.Icc (t / 2) t, E s ≤ L * (A s + F s))
    (ha : (∫ s in (0 : ℝ)..t, A s) ≤ a)
    (hb : (∫ s in (0 : ℝ)..t, F s) ≤ b) :
    (t / 2) * (E t * Real.exp (-K * t)) ≤ L * (a + b) := by
  have h0 : (0 : ℝ) ≤ t / 2 := by linarith
  have hhalf : t / 2 ≤ t := by linarith
  have hsub : Set.Icc (t / 2) t ⊆ Set.Icc 0 t := fun _ hs => ⟨le_trans h0 hs.1, hs.2⟩
  have hiE : IntervalIntegrable E volume (t / 2) t := hE.intervalIntegrable_of_Icc hhalf
  have hiA : IntervalIntegrable A volume 0 t := hA.intervalIntegrable_of_Icc ht.le
  have hiF : IntervalIntegrable F volume 0 t := hF.intervalIntegrable_of_Icc ht.le
  have hiAs : IntervalIntegrable A volume (t / 2) t :=
    (hA.mono hsub).intervalIntegrable_of_Icc hhalf
  have hiFs : IntervalIntegrable F volume (t / 2) t :=
    (hF.mono hsub).intervalIntegrable_of_Icc hhalf
  have hmain := c7_positive_time_energy_endpoint E K t hK ht hE hEn hg
  have hpoint := intervalIntegral.integral_mono_on hhalf hiE ((hiAs.add hiFs).const_mul L) hupper
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hiAs hiFs] at hpoint
  have hposA : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) t)] A := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    exact hAn s ⟨hs.1.le, hs.2⟩
  have hposF : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) t)] F := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    exact hFn s ⟨hs.1.le, hs.2⟩
  have hsubA := intervalIntegral.integral_mono_interval h0 hhalf le_rfl hposA hiA
  have hsubF := intervalIntegral.integral_mono_interval h0 hhalf le_rfl hposF hiF
  have hsum : (∫ s in (t / 2)..t, A s) + (∫ s in (t / 2)..t, F s) ≤ a + b := by
    linarith only [hsubA, hsubF, ha, hb]
  exact hmain.trans (hpoint.trans (mul_le_mul_of_nonneg_left hsum hL))

/-- Integrate the uniform weighted transpose-orbit growth estimate. -/
theorem c7_transpose_weighted_orbit_integral
    {d : ℕ} {a : Vec d → Mat d} {Λ B q : ℝ} {φ : Vec d → ℝ}
    (hΛ : 0 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (hφ : S5Weight φ B q) (i : Fin d) (ζ : ℂ)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    (∫ s in (0 : ℝ)..(t : ℝ), ‖W (S s.toNNReal f)‖ ^ 2) ≤
      (t : ℝ) * (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2 := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hsem : S5Semigroup S (IsPhysicalComplexTransposeGeneratorPair a i ζ) :=
    ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
  have hc : Continuous (fun s : ℝ => ‖W (S s.toNNReal f)‖ ^ 2) :=
    ((W.continuous.comp ((hsem.cont f).comp continuous_real_toNNReal)).norm).pow 2
  have hp : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ),
      ‖W (S s.toNNReal f)‖ ^ 2 ≤ (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2 := by
    intro s hs
    have hg := s5_transpose_growth hell hmeas hφ i ζ hS f s.toNNReal
    rw [← s5Mul_norm volume hφ.measurable hφ.B_nonneg hφ.bound,
      ← s5Mul_norm volume hφ.measurable hφ.B_nonneg hφ.bound] at hg
    have he : Real.exp (k * s) ≤ Real.exp (k * (t : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hk)
    have hs' : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs.1
    rw [hs'] at hg
    have hn := hg.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
    nlinarith [norm_nonneg (W (S s.toNNReal f)), Real.exp_pos (k * (t : ℝ)), norm_nonneg (W f)]
  have hci : IntervalIntegrable (fun s : ℝ => ‖W (S s.toNNReal f)‖ ^ 2)
      volume 0 (t : ℝ) := hc.intervalIntegrable _ _
  have hcst : IntervalIntegrable (fun _ : ℝ => (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2)
      volume 0 (t : ℝ) := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on t.property hci hcst hp
  simpa using h

/-- An explicit integrated weighted gradient bound for the transpose orbit. -/
theorem c7_transpose_orbit_integrated_weighted_gradient_explicit
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
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
    c7_transpose_orbit_integrated_weighted_gradient a i ζ ha hΛ hell hmeas hφ P S hS hfg
  refine ⟨G, hG, hGc, fun t => ?_⟩
  have hi := c7_transpose_weighted_orbit_integral (by linarith : 0 ≤ Λ)
    hell hmeas hφ i ζ P S hS f t
  have hb := hbound t
  change (Λ⁻¹ / 4) * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖W (G s j)‖ ^ 2) ≤
    (‖W f‖ ^ 2 - ‖W (S t f)‖ ^ 2) / 2 + H *
      (∫ s in (0 : ℝ)..(t : ℝ), ‖W (S s.toNNReal f)‖ ^ 2) at hb
  change (∫ s in (0 : ℝ)..(t : ℝ), ‖W (S s.toNNReal f)‖ ^ 2) ≤
    (t : ℝ) * (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2 at hi
  have hc : (Λ⁻¹ / 4) * (∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖W (G s j)‖ ^ 2) ≤
      ‖W f‖ ^ 2 / 2 + H * ((t : ℝ) * (Real.exp (k * (t : ℝ)) * ‖W f‖) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hi hH, sq_nonneg ‖W (S t f)‖]
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
  convert hd using 1 <;> ring


/-- Positive-time shifted energy bound for the actual twice-domain transpose orbit. -/
theorem c7_transpose_shifted_energy_endpoint_explicit
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair a i ζ g h) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
      fun j => if j = i then (2 * ζ) • W else 0
    let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let C := (2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 * Λ
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
        ((t : ℝ) / 2) * ((∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
          (W (G (t : ℝ) k) - K k (S t f)) x *
          star ((W (G (t : ℝ) j) - K j (S t f)) x)).re * Real.exp (-C * t)) ≤
        2 * Λ * (4 * Λ * (‖W f‖ ^ 2 / 2 + H * (t : ℝ) *
          (Real.exp (k * t) * ‖W f‖) ^ 2) + ‖2 * ζ‖ ^ 2 *
          ((t : ℝ) * (Real.exp (k * t) * ‖W f‖) ^ 2)) := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
    fun j => if j = i then (2 * ζ) • W else 0
  let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let C := (2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 * Λ
  have hΛpos : 0 < Λ := by linarith
  have hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ := Filter.Eventually.of_forall hell
  have hsem : S5Semigroup S (IsPhysicalComplexTransposeGeneratorPair a i ζ) :=
    ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
  obtain ⟨G, hG, hGc, hbound⟩ :=
    c7_transpose_orbit_integrated_weighted_gradient_explicit a i ζ ha hΛ hell hmeas hφ P S hS hfg
  obtain ⟨D, hD, hd⟩ :=
    c7_transpose_D2_davies_shifted_energy_derivative_le a i ζ ha hΛpos hA hφ P S hS hfg hgh
  obtain ⟨R, hR, hr⟩ :=
    c7_transpose_D2_davies_shifted_energy_growth a i ζ ha hΛpos hA hφ P S hS hfg hgh
  have hDG (s : ℝ) (hs : 0 ≤ s) : D s = G s :=
    physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ (hD s hs) (hG s)
  have hRG (s : ℝ) (hs : 0 ≤ s) : R s = G s :=
    physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ (hR s hs) (hG s)
  let E (s : ℝ) := (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
    (W (D s k) - K k (S s.toNNReal f)) x *
      star ((W (D s j) - K j (S s.toNNReal f)) x)).re
  let A (s : ℝ) := ∑ j, ‖W (G s j)‖ ^ 2
  let F (s : ℝ) := ‖2 * ζ‖ ^ 2 * ‖W (S s.toNNReal f)‖ ^ 2
  refine ⟨G, hG, fun t ht => ?_⟩
  have hE : ContinuousOn E (Set.Icc ((t : ℝ) / 2) t) := by
    intro s hs
    have hspos : 0 < s := by linarith [hs.1]
    obtain ⟨v, hv, _⟩ := hd s hspos
    exact hv.continuousAt.continuousWithinAt
  have hEn : ∀ s ∈ Set.Icc ((t : ℝ) / 2) t, 0 ≤ E s := by
    intro s hs
    have hc := c18_physical_principal_energy_coercive a ha hΛpos hA
      (fun j => W (D s j) - K j (S s.toNNReal f))
    have hn : 0 ≤ ∑ j, ‖W (D s j) - K j (S s.toNNReal f)‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
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
  have hFc : Continuous F := by
    dsimp [F]
    exact continuous_const.mul (((W.continuous.comp ((hsem.cont f).comp continuous_real_toNNReal)).norm).pow 2)
  have hupper : ∀ s ∈ Set.Icc ((t : ℝ) / 2) t, E s ≤ 2 * Λ * (A s + F s) := by
    intro s hs
    have hs0 : 0 ≤ s := by linarith [hs.1]
    have hu := c7_shifted_principal_energy_upper a ha hΛpos.le hA
      (fun j => W (G s j)) (fun j => K j (S s.toNNReal f))
    have hf : (∑ j, ‖K j (S s.toNNReal f)‖ ^ 2) = F s := by
      have hK (j : Fin d) : K j (S s.toNNReal f) =
          (if j = i then (2 * ζ) • W (S s.toNNReal f) else 0) := by
        by_cases hj : j = i <;> simp [K, hj]
      simpa only [hK, F] using c7_shifted_force_norm_sq i ζ W (S s.toNNReal f)
    simpa only [E, A, hDG s hs0, hf] using hu
  have ha' := hbound t
  have hb' := c7_transpose_weighted_orbit_integral hΛpos.le hell hmeas hφ i ζ P S hS f t
  have hb : (∫ s in (0 : ℝ)..(t : ℝ), F s) ≤
      ‖2 * ζ‖ ^ 2 * ((t : ℝ) * (Real.exp (k * t) * ‖W f‖) ^ 2) := by
    dsimp [F]
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hb' (sq_nonneg _)
  have he := c7_energy_endpoint_of_integrated_bounds E A F C (2 * Λ) t _ _
    (by dsimp [C]; positivity) (by positivity) ht hE hEn hg hAc.continuousOn hFc.continuousOn
    (fun s _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hupper ha' hb
  simpa only [E, hDG t t.property, Real.toNNReal_coe] using he


/-- A weighted gradient endpoint for data in the twice-generator domain. -/
theorem c7_transpose_D2_weighted_gradient_endpoint_explicit
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    {f g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hgh : IsPhysicalComplexTransposeGeneratorPair a i ζ g h) :
    let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
    let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
    let C := (2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 * Λ
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (S s.toNNReal f) (G s)) ∧
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
        (∑ j, ‖W (G (t : ℝ) j)‖ ^ 2) ≤
        2 * Λ * ((2 / (t : ℝ)) * Real.exp (C * t) *
          (2 * Λ * (4 * Λ * (‖W f‖ ^ 2 / 2 + H * (t : ℝ) *
            (Real.exp (k * t) * ‖W f‖) ^ 2) + ‖2 * ζ‖ ^ 2 *
            ((t : ℝ) * (Real.exp (k * t) * ‖W f‖) ^ 2)))) +
        2 * ‖2 * ζ‖ ^ 2 * (Real.exp (k * t) * ‖W f‖) ^ 2 := by
  let W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound
  let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 volume :=
    fun j => if j = i then (2 * ζ) • W else 0
  let H := 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let k := 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)
  let C := (2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 * Λ
  have hΛpos : 0 < Λ := by linarith
  have hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ := Filter.Eventually.of_forall hell
  obtain ⟨G, hG, hb⟩ :=
    c7_transpose_shifted_energy_endpoint_explicit a i ζ ha hΛ hell hmeas hφ P S hS hfg hgh
  refine ⟨G, hG, fun t ht => ?_⟩
  let E := (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
    (W (G (t : ℝ) k) - K k (S t f)) x *
      star ((W (G (t : ℝ) j) - K j (S t f)) x)).re
  let R := 2 * Λ * (4 * Λ * (‖W f‖ ^ 2 / 2 + H * (t : ℝ) *
    (Real.exp (k * t) * ‖W f‖) ^ 2) + ‖2 * ζ‖ ^ 2 *
    ((t : ℝ) * (Real.exp (k * t) * ‖W f‖) ^ 2))
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
  have hco := c7_shifted_principal_energy_coercive a ha hΛpos hA
    (fun j => W (G (t : ℝ) j)) (fun j => K j (S t f))
  have hf : (∑ j, ‖K j (S t f)‖ ^ 2) = ‖2 * ζ‖ ^ 2 * ‖W (S t f)‖ ^ 2 := by
    have hK (j : Fin d) : K j (S t f) =
        (if j = i then (2 * ζ) • W (S t f) else 0) := by
      by_cases hj : j = i <;> simp [K, hj]
    simpa only [hK] using c7_shifted_force_norm_sq i ζ W (S t f)
  rw [hf] at hco
  have hg := s5_transpose_growth hell hmeas hφ i ζ hS f t
  rw [← s5Mul_norm volume hφ.measurable hφ.B_nonneg hφ.bound,
    ← s5Mul_norm volume hφ.measurable hφ.B_nonneg hφ.bound] at hg
  have hsq : ‖W (S t f)‖ ^ 2 ≤ (Real.exp (k * t) * ‖W f‖) ^ 2 := by
    nlinarith [norm_nonneg (W (S t f)), Real.exp_pos (k * t), norm_nonneg (W f)]
  have h1 := mul_le_mul_of_nonneg_left hEt (show 0 ≤ 2 * Λ by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * ‖2 * ζ‖ ^ 2 by positivity)
  change (∑ j, ‖W (G (t : ℝ) j)‖ ^ 2) ≤
    2 * Λ * ((2 / (t : ℝ)) * Real.exp (C * t) * R) +
      2 * ‖2 * ζ‖ ^ 2 * (Real.exp (k * t) * ‖W f‖) ^ 2
  change (∑ j, ‖W (G (t : ℝ) j)‖ ^ 2) ≤
    2 * Λ * E + 2 * (‖2 * ζ‖ ^ 2 * ‖W (S t f)‖ ^ 2) at hco
  nlinarith only [hco, h1, h2]

private theorem c7_cauchy_of_norm_sq_bound
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

private theorem c7_gen_sub
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

private theorem c7_physicalH1_sub {d : ℕ}
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

private theorem c7_pi_norm_sq_le_sum {d : ℕ} {E : Type*} [NormedAddCommGroup E]
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
transpose data through the closed physical H¹ graph. The unweighted estimate
supplies the Cauchy property of the gradients. -/
theorem c7_transpose_weighted_gradient_of_D2 {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    (W : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (K₀ K : ℝ) (t : ℝ≥0)
    (hD₀ : ∀ f g h, IsPhysicalComplexTransposeGeneratorPair a i ζ f g →
      IsPhysicalComplexTransposeGeneratorPair a i ζ g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (S t f) G ∧
        (∑ j, ‖G j‖ ^ 2) ≤ K₀ * ‖f‖ ^ 2)
    (hD : ∀ f g h, IsPhysicalComplexTransposeGeneratorPair a i ζ f g →
      IsPhysicalComplexTransposeGeneratorPair a i ζ g h →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (S t f) G ∧
        (∑ j, ‖W (G j)‖ ^ 2) ≤ K * ‖W f‖ ^ 2)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (S t f) G ∧
      (∑ j, ‖W (G j)‖ ^ 2) ≤ K * ‖W f‖ ^ 2 := by
  classical
  let Gen := IsPhysicalComplexTransposeGeneratorPair a i ζ
  have hP : S5Semigroup S Gen := ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
  let D2 : Set (Lp ℂ 2 (volume : Measure (Vec d))) := {u | ∃ v w, Gen u v ∧ Gen v w}
  have hfirst (u v : Lp ℂ 2 (volume : Measure (Vec d))) (huv : Gen u v) :
      u ∈ closure D2 := by
    obtain ⟨F, G, H, hgen, hF, _⟩ := c18_physical_transpose_generator_D2_approx a i ζ P S hS huv
    apply mem_closure_of_tendsto hF
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ⟨G δ, H δ, hgen δ hδ⟩
  have hdense : Dense D2 := by
    intro u
    obtain ⟨F, G, hgen, hF⟩ := hP.exists_gen_approx u
    apply isClosed_closure.mem_of_tendsto hF
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hfirst (F δ) (G δ) (hgen δ hδ)
  have hall : ∀ u v w, Gen u v → Gen v w → ∀ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (S t u) G →
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
        (S t (F n - F m)) (fun j => G n j - G m j) := by
      simpa only [map_sub] using c7_physicalH1_sub (hG n) (hG m)
    have hb' := (hall (F n - F m) (g n - g m) (h n - h m)
      (c7_gen_sub hP (hg n) (hg m)) (c7_gen_sub hP (hh n) (hh m)) _ hsub).1
    exact (c7_pi_norm_sq_le_sum (G n - G m)).trans hb'
  have hC : CauchySeq G := c7_cauchy_of_norm_sq_bound G F hlim.cauchySeq K₀ hdiff
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨V, physicalH1Graph_of_tendsto volume (Or.inl rfl)
    (fun n => (S t (F n), G n)) (S t f, V) hG ?_, ?_⟩
  · exact (((S t).continuous.tendsto f).comp hlim).prodMk_nhds hV
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
/-- Multiplication by a bounded real weight, applied to data supported where the
weight is at most `c`, is bounded by `c` times the data norm. -/
theorem c7_s5Mul_norm_le_of_ae {d : ℕ} {w : Vec d → ℝ} (hw : Measurable w) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, |w x| ≤ B) {c : ℝ} (hc : 0 ≤ c)
    (g : Lp ℂ 2 (volume : Measure (Vec d)))
    (h : ∀ᵐ x ∂volume, g x ≠ 0 → |w x| ≤ c) :
    ‖s5Mul volume hw hB0 hB g‖ ≤ c * ‖g‖ := by
  rw [s5Mul_norm volume hw hB0 hB, Lp.norm_def]
  have h2 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Vec d)))
    (f := fun x => (w x : ℂ) * g x) (g := (g : Vec d → ℂ)) (c := c)
    ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable g))
    (by
      filter_upwards [h] with x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hg : g x = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_right (hx hg) (norm_nonneg _)) 2
  calc (eLpNorm (fun x => (w x : ℂ) * g x) 2 volume).toReal
      ≤ (ENNReal.ofReal c * eLpNorm (g : Vec d → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top g)) h2
    _ = c * (eLpNorm (g : Vec d → ℂ) 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- Where the weight is at least `c > 0`, the data is controlled by the weighted
data with the reciprocal constant. -/
theorem c7_indicator_eLpNorm_le_weighted {d : ℕ} {w : Vec d → ℝ} (hw : Measurable w)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, |w x| ≤ B) {c : ℝ} (hc : 0 < c)
    {E : Set (Vec d)} (hE : MeasurableSet E) (hwE : ∀ x ∈ E, c ≤ |w x|)
    (G : Lp ℂ 2 (volume : Measure (Vec d))) :
    (eLpNorm (E.indicator (fun x => G x)) 2 volume).toReal ≤
      c⁻¹ * ‖s5Mul volume hw hB0 hB G‖ := by
  rw [s5Mul_norm volume hw hB0 hB]
  have h2 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Vec d)))
    (f := E.indicator (fun x => G x)) (g := fun x => (w x : ℂ) * G x) (c := c⁻¹)
    ((Lp.aestronglyMeasurable G).indicator hE)
    (Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 : 1 ≤ c⁻¹ * |w x| := by
          rw [← div_eq_inv_mul, one_le_div hc]
          exact hwE x hx
        nlinarith [norm_nonneg (G x : ℂ)]
      · rw [Set.indicator_of_notMem hx]
        simp only [norm_zero]
        positivity) 2
  have hne : eLpNorm (fun x => (w x : ℂ) * G x) 2 volume ≠ ⊤ :=
    (s5_memLp_mul hw hB G).eLpNorm_lt_top.ne
  calc (eLpNorm (E.indicator (fun x => G x)) 2 volume).toReal
      ≤ (ENNReal.ofReal c⁻¹ * eLpNorm (fun x => (w x : ℂ) * G x) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne) h2
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le)]

/-- The explicit constant of the weighted transpose gradient endpoint, written
with `q` the weight-gradient parameter, `ζ` the force and `t` the time. -/
noncomputable def c7WeightedGradientConst (Λ q : ℝ) (ζ : ℂ) (t : ℝ) : ℝ :=
  (8 * Λ ^ 2 / t) * Real.exp ((2 * Λ * (2 * q + ‖2 * ζ‖)) ^ 2 * Λ * t) *
      (4 * Λ * (1 / 2 + 5 * (2 * Λ) ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2) * t *
        Real.exp (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2) * t) ^ 2) + ‖2 * ζ‖ ^ 2 *
        (t * Real.exp (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2) * t) ^ 2)) +
    2 * ‖2 * ζ‖ ^ 2 * Real.exp (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2) * t) ^ 2

/-- The weighted gradient endpoint for arbitrary transpose data, with an
explicit constant independent of coefficient derivatives. -/
theorem c7_transpose_weighted_gradient_endpoint
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B q : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    {φ : Vec d → ℝ} (hφ : S5Weight φ B q)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (S t f) G ∧
      (∑ j, ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound (G j)‖ ^ 2) ≤
        c7WeightedGradientConst Λ q ζ t *
          ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f‖ ^ 2 := by
  have hone : S5Weight (fun _ : Vec d => (1 : ℝ)) 1 0 :=
    ⟨contDiff_const, zero_le_one, le_rfl, by simp, fun x => by
      simp [s5Nrm, coordinateDerivative]⟩
  have hW₁ : ∀ x : Lp ℂ 2 (volume : Measure (Vec d)),
      ‖s5Mul volume hone.measurable hone.B_nonneg hone.bound x‖ = ‖x‖ := by
    intro x
    rw [s5Mul_norm, Lp.norm_def]
    simp
  refine c7_transpose_weighted_gradient_of_D2 a i ζ P S hS _
    (c7WeightedGradientConst Λ 0 ζ t) (c7WeightedGradientConst Λ q ζ t) t ?_ ?_ f
  · intro f g h hfg hgh
    obtain ⟨G, hG, hb⟩ := c7_transpose_D2_weighted_gradient_endpoint_explicit a i ζ ha hΛ
      hell hmeas hone P S hS hfg hgh
    refine ⟨G (t : ℝ), by simpa only [Real.toNNReal_coe] using hG (t : ℝ), ?_⟩
    have := hb t ht
    simp only [hW₁] at this
    refine this.trans (le_of_eq ?_)
    simp only [c7WeightedGradientConst]
    ring
  · intro f g h hfg hgh
    obtain ⟨G, hG, hb⟩ := c7_transpose_D2_weighted_gradient_endpoint_explicit a i ζ ha hΛ
      hell hmeas hφ P S hS hfg hgh
    refine ⟨G (t : ℝ), by simpa only [Real.toNNReal_coe] using hG (t : ℝ), ?_⟩
    refine (hb t ht).trans (le_of_eq ?_)
    simp only [c7WeightedGradientConst]
    ring

/-- A radial exponential weight turns the weighted gradient endpoint into an
outer Gaussian-type tail for data supported in the inner ball. -/
theorem c7_transpose_radial_gradient_tail
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (hell : ∀ x, S5Elliptic (a x) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (P S : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hS : IsPhysicalComplexTransposeSemigroup a i ζ P S)
    (z : Vec d) {ρ q : ℝ} (hρ : 0 < ρ) (hq : 0 ≤ q)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (g : Lp ℂ 2 (volume : Measure (Vec d)))
    (hg : ∀ᵐ x ∂volume, ρ / 2 ≤ euclideanNorm (x - z) → g x = 0) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (S t g) G ∧
      Real.sqrt (∑ j : Fin d,
        ((eLpNorm ({x : Vec d | ρ ≤ euclideanNorm (x - z)}.indicator
          (fun x => G j x)) 2 volume).toReal) ^ 2) ≤
        Real.exp (-(3 * q * ρ / 10)) *
          Real.sqrt (c7WeightedGradientConst Λ q ζ t) * ‖g‖ := by
  let ψ : Vec d → ℝ := fun x => ρ * euclideanSq (x - z) / (ρ ^ 2 + euclideanSq (x - z))
  have hφ : S5Weight (fun x => Real.exp (q * ψ x)) (Real.exp (q * ρ)) q :=
    c7_radial_exp_s5Weight z hρ hq
  obtain ⟨_, hvalues, _, hinner, houter⟩ := c7_bounded_radial_weight_geometry z hρ
  obtain ⟨G, hG, hb⟩ := c7_transpose_weighted_gradient_endpoint a i ζ ha hΛ hell hmeas hφ
    P S hS t ht g
  refine ⟨G, hG, ?_⟩
  set W := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound with hWdef
  have hWg : ‖W g‖ ≤ Real.exp (q * ρ / 5) * ‖g‖ := by
    apply c7_s5Mul_norm_le_of_ae _ _ _ (Real.exp_pos _).le
    filter_upwards [hg] with x hx hgx
    have hlt : euclideanNorm (x - z) < ρ / 2 := by
      by_contra hcon
      exact hgx (hx (not_lt.mp hcon))
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_left (hinner x hlt.le) hq
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
          (c7WeightedGradientConst Λ q ζ t * ‖W g‖ ^ 2)) :=
        Real.sqrt_le_sqrt (hsum.trans (mul_le_mul_of_nonneg_left hb (sq_nonneg _)))
    _ = (Real.exp (q * ρ / 2))⁻¹ * (Real.sqrt (c7WeightedGradientConst Λ q ζ t) * ‖W g‖) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hc.le),
          Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ (Real.exp (q * ρ / 2))⁻¹ * (Real.sqrt (c7WeightedGradientConst Λ q ζ t) *
          (Real.exp (q * ρ / 5) * ‖g‖)) := by
        gcongr
    _ = _ := by
        have : Real.exp (-(3 * q * ρ / 10)) = (Real.exp (q * ρ / 2))⁻¹ * Real.exp (q * ρ / 5) := by
          rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
        rw [this]; ring

/-- The explicit weighted gradient constant is bounded by a structural multiple of
`t⁻¹ exp (N (q² + ‖ζ‖²) t)`. -/
theorem c7_weightedGradientConst_le {Λ q : ℝ} (hΛ : 1 ≤ Λ) (ζ : ℂ) {t : ℝ}
    (ht : 0 < t) :
    c7WeightedGradientConst Λ q ζ t ≤
      ((16 * Λ ^ 3 + 8 * Λ ^ 2 * (160 * Λ ^ 4 + 4) + 8) / t) *
        Real.exp ((42 * Λ ^ 3 + 1) * ((q ^ 2 + ‖ζ‖ ^ 2) * t)) := by
  have hΛ0 : 0 < Λ := by linarith
  have hn : ‖(2 : ℂ) * ζ‖ = 2 * ‖ζ‖ := by simp
  obtain ⟨x, hx⟩ : ∃ x, x = ‖ζ‖ := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = (q ^ 2 + x ^ 2) * t := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ norm_nonneg ζ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hE1 : Real.exp ((2 * Λ * (2 * q + 2 * x)) ^ 2 * Λ * t) ≤ Real.exp (32 * Λ ^ 3 * κ) := by
    apply Real.exp_le_exp.mpr
    have : 32 * Λ ^ 3 * κ - (2 * Λ * (2 * q + 2 * x)) ^ 2 * Λ * t =
        16 * Λ ^ 3 * t * (q - x) ^ 2 := by rw [hκ]; ring
    have : 0 ≤ 16 * Λ ^ 3 * t * (q - x) ^ 2 := by positivity
    linarith
  have hE2 : Real.exp (5 * Λ ^ 3 * (q ^ 2 + x ^ 2) * t) ^ 2 = Real.exp (10 * Λ ^ 3 * κ) := by
    rw [sq, ← Real.exp_add]; congr 1; rw [hκ]; ring
  have hK : c7WeightedGradientConst Λ q ζ t * t =
      8 * Λ ^ 2 * Real.exp ((2 * Λ * (2 * q + 2 * x)) ^ 2 * Λ * t) *
        (4 * Λ * (1 / 2 + 5 * (2 * Λ) ^ 3 * (q ^ 2 + x ^ 2) * t *
          Real.exp (10 * Λ ^ 3 * κ)) + (2 * x) ^ 2 * (t * Real.exp (10 * Λ ^ 3 * κ))) +
        2 * (2 * x) ^ 2 * t * Real.exp (10 * Λ ^ 3 * κ) := by
    unfold c7WeightedGradientConst
    rw [hn, ← hx, hE2]
    field_simp
  have hE2' : 1 ≤ Real.exp (10 * Λ ^ 3 * κ) := Real.one_le_exp (by positivity)
  have hX : Real.exp ((42 * Λ ^ 3 + 1) * ((q ^ 2 + x ^ 2) * t)) =
      Real.exp (32 * Λ ^ 3 * κ) * Real.exp (10 * Λ ^ 3 * κ) * Real.exp κ := by
    rw [← Real.exp_add, ← Real.exp_add, ← hκ]; congr 1; ring
  have hE1' : 1 ≤ Real.exp (32 * Λ ^ 3 * κ) := Real.one_le_exp (by positivity)
  have hκe : κ ≤ Real.exp κ := by linarith [Real.add_one_le_exp κ]
  have hκe1 : 1 ≤ Real.exp κ := Real.one_le_exp hκ0
  rw [← hx]
  generalize Real.exp ((42 * Λ ^ 3 + 1) * ((q ^ 2 + x ^ 2) * t)) = X at hX ⊢
  generalize Real.exp (32 * Λ ^ 3 * κ) = E1 at hE1 hE1' hX
  generalize Real.exp (10 * Λ ^ 3 * κ) = E2 at hK hE2' hX
  generalize Real.exp κ = E3 at hκe hκe1 hX
  have hXe : X = E1 * E2 * E3 := by exact hX
  have hxt : x ^ 2 * t ≤ κ := by rw [hκ]; nlinarith [mul_nonneg (sq_nonneg q) ht.le]
  have hE1nn : 0 ≤ E1 := by linarith
  have hE2nn : 0 ≤ E2 := by linarith
  have h23 : 1 ≤ E2 * E3 := one_le_mul_of_one_le_of_one_le hE2' hκe1
  have hE1X : E1 ≤ X := by
    rw [hXe, mul_assoc]; nlinarith [mul_le_mul_of_nonneg_left h23 hE1nn]
  have hkapX : κ * E2 * E1 ≤ X := by
    have := mul_le_mul_of_nonneg_right hκe (mul_nonneg hE2nn hE1nn)
    rw [hXe]; linarith [this]
  have hkapX' : κ * E2 ≤ X := by
    have h1 := mul_le_mul_of_nonneg_right hκe hE2nn
    have h2 := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ E1 by linarith) (mul_nonneg hE2nn (by linarith : (0:ℝ) ≤ E3))
    rw [hXe]; nlinarith [h1, h2]
  have hinner : 4 * Λ * (1 / 2 + 5 * (2 * Λ) ^ 3 * (q ^ 2 + x ^ 2) * t * E2) +
      (2 * x) ^ 2 * (t * E2) = 2 * Λ + (160 * Λ ^ 4 * (q ^ 2 + x ^ 2) * t + 4 * (x ^ 2 * t)) * E2 := by
    ring
  have hfinal : c7WeightedGradientConst Λ q ζ t * t ≤
      (16 * Λ ^ 3 + 8 * Λ ^ 2 * (160 * Λ ^ 4 + 4) + 8) * X := by
    rw [hK, hinner]
    have e1 : 8 * Λ ^ 2 * Real.exp ((2 * Λ * (2 * q + 2 * x)) ^ 2 * Λ * t) ≤ 8 * Λ ^ 2 * E1 := by
      exact mul_le_mul_of_nonneg_left hE1 (by positivity)
    have hc : 0 ≤ 2 * Λ + (160 * Λ ^ 4 * (q ^ 2 + x ^ 2) * t + 4 * (x ^ 2 * t)) * E2 := by positivity
    have hst : (160 * Λ ^ 4 * (q ^ 2 + x ^ 2) * t + 4 * (x ^ 2 * t)) ≤ (160 * Λ ^ 4 + 4) * κ := by
      rw [hκ]; nlinarith [mul_nonneg (pow_nonneg hΛ0.le 4) (mul_nonneg (add_nonneg (sq_nonneg q) (sq_nonneg x)) ht.le)]
    have h2 : 8 * Λ ^ 2 * E1 * (2 * Λ + (160 * Λ ^ 4 * (q ^ 2 + x ^ 2) * t + 4 * (x ^ 2 * t)) * E2) ≤
        8 * Λ ^ 2 * E1 * (2 * Λ + (160 * Λ ^ 4 + 4) * κ * E2) := by
      gcongr
    have h3a := mul_le_mul_of_nonneg_left hE1X (by positivity : (0:ℝ) ≤ 16 * Λ ^ 3)
    have h3b := mul_le_mul_of_nonneg_left hkapX
      (by positivity : (0:ℝ) ≤ 8 * Λ ^ 2 * (160 * Λ ^ 4 + 4))
    have h3 : 8 * Λ ^ 2 * E1 * (2 * Λ + (160 * Λ ^ 4 + 4) * κ * E2) =
        16 * Λ ^ 3 * E1 + 8 * Λ ^ 2 * (160 * Λ ^ 4 + 4) * (κ * E2 * E1) := by ring
    have h4 : 2 * (2 * x) ^ 2 * t * E2 ≤ 8 * X := by
      have h6 := mul_le_mul_of_nonneg_right hxt hE2nn
      have e : 2 * (2 * x) ^ 2 * t * E2 = 8 * ((x ^ 2 * t) * E2) := by ring
      rw [e]
      have h7 : (x ^ 2 * t) * E2 ≤ X := h6.trans hkapX'
      linarith
    have h5 := mul_le_mul_of_nonneg_right e1 hc
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ ht]
  linarith

/-- Real-variable optimization of the radial gap against the quadratic cost. -/
theorem c7_radial_tail_arith {A N x s ρ : ℝ} (hA : 0 < A) (hN : 0 < N) (hx : 0 ≤ x)
    (hs : 0 < s) :
    Real.exp (-(3 * (3 * ρ / (10 * N * s)) * ρ / 10)) *
        Real.sqrt ((A / s) * Real.exp (N * (((3 * ρ / (10 * N * s)) ^ 2 + x ^ 2) * s))) ≤
      (Real.sqrt A + N / 2 + 1) * ((Real.sqrt s)⁻¹ + x) *
        Real.exp ((Real.sqrt A + N / 2 + 1) * x ^ 2 * s - (9 / (200 * N)) * ρ ^ 2 / s) := by
  have hgap := c7_radial_gap_optimized (A := N / 2) (t := s) (ρ := ρ) (by positivity) hs
  dsimp only at hgap
  have hq : 3 * ρ / (20 * (N / 2) * s) = 3 * ρ / (10 * N * s) := by
    field_simp; ring
  rw [hq] at hgap
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  obtain ⟨q, hqd⟩ : ∃ q, q = 3 * ρ / (10 * N * s) := ⟨_, rfl⟩
  rw [← hqd] at hgap ⊢
  have e1 : Real.sqrt ((A / s) * Real.exp (N * ((q ^ 2 + x ^ 2) * s))) =
      Real.sqrt A * (Real.sqrt s)⁻¹ * Real.exp (N / 2 * ((q ^ 2 + x ^ 2) * s)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ hs.le, ← div_eq_mul_inv,
      ← Real.exp_half]
    congr 2
    ring
  rw [e1]
  have e2 : Real.exp (-(3 * q * ρ / 10)) * (Real.sqrt A * (Real.sqrt s)⁻¹ *
      Real.exp (N / 2 * ((q ^ 2 + x ^ 2) * s))) =
      Real.sqrt A * (Real.sqrt s)⁻¹ *
        Real.exp (N / 2 * x ^ 2 * s - (9 / (200 * N)) * ρ ^ 2 / s) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    have : (9 / (200 * N)) * ρ ^ 2 / s = 9 * ρ ^ 2 / (400 * (N / 2) * s) := by
      field_simp; ring
    rw [this]
    linarith
  rw [e2]
  have hC : Real.sqrt A ≤ Real.sqrt A + N / 2 + 1 := by linarith
  have hinv : 0 < (Real.sqrt s)⁻¹ := inv_pos.mpr hss
  have hexp : Real.exp (N / 2 * x ^ 2 * s - (9 / (200 * N)) * ρ ^ 2 / s) ≤
      Real.exp ((Real.sqrt A + N / 2 + 1) * x ^ 2 * s - (9 / (200 * N)) * ρ ^ 2 / s) := by
    apply Real.exp_le_exp.mpr
    have : N / 2 * x ^ 2 * s ≤ (Real.sqrt A + N / 2 + 1) * x ^ 2 * s := by
      have := mul_nonneg (sq_nonneg x) hs.le
      nlinarith
    linarith
  calc Real.sqrt A * (Real.sqrt s)⁻¹ *
        Real.exp (N / 2 * x ^ 2 * s - (9 / (200 * N)) * ρ ^ 2 / s)
      ≤ (Real.sqrt A + N / 2 + 1) * ((Real.sqrt s)⁻¹ + x) *
        Real.exp ((Real.sqrt A + N / 2 + 1) * x ^ 2 * s - (9 / (200 * N)) * ρ ^ 2 / s) := by
        apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
        apply mul_le_mul hC (by linarith) hinv.le (by positivity)

/-- Uniform Gaussian outer bound for the transpose gradient at positive time,
for data supported in a ball of half the radius. -/
theorem c7_transpose_gradient_off_diagonal_of_deps
    (_hoff : node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (d : ℕ) (_hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r), ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
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
  obtain ⟨Λ', hΛ'⟩ : ∃ L, L = Real.exp (2 * Λ) * Λ := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := by linarith
  have hΛ1 : 1 ≤ Λ' := by
    rw [hΛ']
    have := Real.one_le_exp (by linarith : 0 ≤ 2 * Λ)
    nlinarith
  obtain ⟨A, hAd⟩ : ∃ A, A = 16 * Λ' ^ 3 + 8 * Λ' ^ 2 * (160 * Λ' ^ 4 + 4) + 8 := ⟨_, rfl⟩
  obtain ⟨N, hNd⟩ : ∃ N, N = 42 * Λ' ^ 3 + 1 := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAd]; positivity
  have hN : 0 < N := by rw [hNd]; positivity
  refine ⟨Real.sqrt A + N / 2 + 1, 9 / (200 * N), ?_, by positivity, ?_⟩
  · have := Real.sqrt_nonneg A
    linarith
  intro r Q
  filter_upwards [c4_ae_reduced_physical_elliptic Q] with ω hell
  rw [← hΛ'] at hell
  intro i ζ P Pdag _ hPdag s hs z ρ hρ g hg
  have hs' : 0 < (s : ℝ) := NNReal.coe_pos.mpr hs
  have hΛ'0 : 0 < Λ' := by linarith
  have hmeas : ∀ j k, Measurable fun x => ω.1 x j k := fun j k =>
    (ω.1.continuous.matrix_elem j k).measurable
  have ha := fun j k => memLp_complex_elliptic_entry volume ω.1 Λ' hΛ'0 hell
    (fun j k => ω.1.continuous.matrix_elem j k) j k
  obtain ⟨G, hG, hb⟩ := c7_transpose_radial_gradient_tail ω.1 i ζ ha hΛ1
    (s5Elliptic_of_isElliptic hΛ1 hell) hmeas P Pdag hPdag z hρ
    (show 0 ≤ 3 * ρ / (10 * N * (s : ℝ)) by positivity) s hs' g hg
  refine ⟨G, hG, hb.trans ?_⟩
  have hK := c7_weightedGradientConst_le (q := 3 * ρ / (10 * N * (s : ℝ))) hΛ1 ζ hs'
  rw [← hAd, ← hNd] at hK
  have hsq := Real.sqrt_le_sqrt hK
  have h1 := mul_le_mul_of_nonneg_left hsq
    (Real.exp_pos (-(3 * (3 * ρ / (10 * N * (s : ℝ))) * ρ / 10))).le
  calc _ ≤ _ := mul_le_mul_of_nonneg_right h1 (norm_nonneg g)
    _ ≤ _ := mul_le_mul_of_nonneg_right (c7_radial_tail_arith (A := A) (N := N) (x := ‖ζ‖)
        (s := (s : ℝ)) (ρ := ρ) hA hN (norm_nonneg ζ) hs') (norm_nonneg g)

end EinsteinFull.Blueprint
