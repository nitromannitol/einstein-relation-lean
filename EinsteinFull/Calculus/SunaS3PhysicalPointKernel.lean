import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Calculus.C18PhysicalValueSmoothing
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

open MeasureTheory
open scoped ComplexConjugate NNReal BigOperators

namespace EinsteinFull
open EinsteinRelation

/-- A bounded complex-linear functional on physical L² has a bilinear integral
representation. The conjugation is absorbed into the selected coefficient, so
this is the convention used for the physical transpose kernel. -/
theorem s3_bounded_evaluation_riesz {d : ℕ}
    (L : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) :
    ∃ g : Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        Integrable (fun y => conj (g y) * f y) ∧
        L f = ∫ y, conj (g y) * f y := by
  refine ⟨(InnerProductSpace.toDual ℂ _).symm L, fun f => ?_⟩
  constructor
  · simpa [RCLike.inner_apply, mul_comm] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
        ((InnerProductSpace.toDual ℂ _).symm L) f)
  · rw [← InnerProductSpace.toDual_symm_apply (x := f) (y := L),
      MeasureTheory.L2.inner_def]
    congr 1
    funext y
    simp [RCLike.inner_apply, mul_comm]

/-- Riesz representation commutes with composition by a bounded L² operator.
This is the Hilbert-space factorization used when a semigroup time is split. -/
theorem s3_evaluation_riesz_comp {d : ℕ}
    (L : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) :
    (InnerProductSpace.toDual ℂ _).symm (L.comp T) =
      T.adjoint ((InnerProductSpace.toDual ℂ _).symm L) := by
  apply ext_inner_right ℂ
  intro f
  rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.adjoint_inner_left,
    InnerProductSpace.toDual_symm_apply]
  rfl

/-- The Hilbert adjoint corresponding to the physical bilinear transpose is
obtained by conjugating on both sides. -/
theorem s3_adjoint_of_bilinear_transpose {d : ℕ}
    (T U : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (h : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, T f x * g x) = ∫ x, f x * U g x)
    (g : Lp ℂ 2 (volume : Measure (Vec d))) :
    T.adjoint g = star (U (star g)) := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def]
  calc
    (∫ x, inner ℂ (g x) (T f x)) = ∫ x, T f x * (star g) x := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_star g] with x hx
      simp [RCLike.inner_apply, hx, mul_comm]
    _ = ∫ x, f x * U (star g) x := h f (star g)
    _ = ∫ x, inner ℂ ((star (U (star g))) x) (f x) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_star (U (star g))] with x hx
      simp [RCLike.inner_apply, hx, mul_comm]

/-- Splitting an evaluated L² action through a bilinear transpose gives a
literal integrable kernel row. The transpose acts on the conjugated Riesz
vector; the resulting product has no extra conjugation. -/
theorem s3_evaluation_comp_bilinear_transpose {d : ℕ}
    (L : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (T U : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (h : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, T f x * g x) = ∫ x, f x * U g x)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    let g := (InnerProductSpace.toDual ℂ _).symm L
    Integrable (fun y => U (star g) y * f y) ∧
      L (T f) = ∫ y, U (star g) y * f y := by
  let g := (InnerProductSpace.toDual ℂ _).symm L
  have hadj : T.adjoint g = star (U (star g)) :=
    s3_adjoint_of_bilinear_transpose T U h g
  have hi : Integrable (fun y => conj ((T.adjoint g) y) * f y) := by
    simpa [RCLike.inner_apply, mul_comm] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (T.adjoint g) f)
  have heq : (fun y => conj ((T.adjoint g) y) * f y) =ᵐ[volume]
      fun y => U (star g) y * f y := by
    rw [hadj]
    filter_upwards [Lp.coeFn_star (U (star g))] with y hy
    simp [hy, mul_comm]
  constructor
  · exact hi.congr heq
  · calc
      L (T f) = inner ℂ g (T f) :=
        (InnerProductSpace.toDual_symm_apply (x := T f) (y := L)).symm
      _ = inner ℂ (T.adjoint g) f :=
        (ContinuousLinearMap.adjoint_inner_left T f g).symm
      _ = ∫ y, conj ((T.adjoint g) y) * f y := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards with y
        simp [RCLike.inner_apply, mul_comm]
      _ = ∫ y, U (star g) y * f y := integral_congr_ae heq

/-- Conjugating the Riesz vectors produces the symmetric bilinear pairing
needed to select one kernel for both the forward and transpose actions. -/
theorem s3_riesz_bilinear_symmetry {d : ℕ}
    (L M : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) :
    L (star ((InnerProductSpace.toDual ℂ _).symm M)) =
      M (star ((InnerProductSpace.toDual ℂ _).symm L)) := by
  rw [← InnerProductSpace.toDual_symm_apply
      (x := star ((InnerProductSpace.toDual ℂ _).symm M)) (y := L),
    ← InnerProductSpace.toDual_symm_apply
      (x := star ((InnerProductSpace.toDual ℂ _).symm L)) (y := M),
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star ((InnerProductSpace.toDual ℂ _).symm L),
    Lp.coeFn_star ((InnerProductSpace.toDual ℂ _).symm M)] with x hx hy
  simp [RCLike.inner_apply, hx, hy, mul_comm]

/-- A bounded point-evaluation family for one half of the evolution yields
integrable rows representing the action at the doubled time. -/
theorem s3_semigroup_split_forward_rows {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (s : ℝ≥0)
    (hsplit : P (s + s) = (P s).comp (P s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hE : ∀ f, (P s f : Vec d → ℂ) =ᵐ[volume] fun x => E x f)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    let K := fun x y => Pdag s (star ((InnerProductSpace.toDual ℂ _).symm (E x))) y
    (∀ x, Integrable (fun y => K x y * f y)) ∧
      (P (s + s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y := by
  constructor
  · intro x
    exact (s3_evaluation_comp_bilinear_transpose (E x) (P s) (Pdag s) htranspose f).1
  · have haction : P (s + s) f = P s (P s f) := by
      rw [hsplit]
      rfl
    rw [haction]
    filter_upwards [hE (P s f)] with x hx
    exact hx.trans (s3_evaluation_comp_bilinear_transpose
      (E x) (P s) (Pdag s) htranspose f).2

/-- Forward and transpose bounded evaluations select one kernel for the
split evolution. Sectionwise almost-everywhere equalities provide the literal
integrability and both actions. -/
theorem s3_semigroup_split_compatible_rows {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ≥0)
    (hsplit : P (s + s) = (P s).comp (P s))
    (hsplitdag : Pdag (s + s) = (Pdag s).comp (Pdag s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hE : ∀ f, (P s f : Vec d → ℂ) =ᵐ[volume] fun x => E x f)
    (hF : ∀ f, (Pdag s f : Vec d → ℂ) =ᵐ[volume] fun x => F x f) :
    ∃ K : Vec d → Vec d → ℂ,
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P (s + s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag (s + s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y) := by
  let K : Vec d → Vec d → ℂ := fun x y =>
    E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
  have hrow (x : Vec d) :
      (fun y => Pdag s (star ((InnerProductSpace.toDual ℂ _).symm (E x))) y)
        =ᵐ[volume] K x := by
    filter_upwards [hF (star ((InnerProductSpace.toDual ℂ _).symm (E x)))] with y hy
    exact hy.trans (s3_riesz_bilinear_symmetry (F y) (E x))
  have hcol (x : Vec d) :
      (fun y => P s (star ((InnerProductSpace.toDual ℂ _).symm (F x))) y)
        =ᵐ[volume] fun y => K y x := hE _
  have htranspose' : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, Pdag s f x * g x) = ∫ x, f x * P s g x := by
    intro f g
    simpa only [mul_comm] using (htranspose g f).symm
  refine ⟨K, fun f => ?_⟩
  have hf := s3_semigroup_split_forward_rows P Pdag s hsplit htranspose E hE f
  have hb := s3_semigroup_split_forward_rows Pdag P s hsplitdag htranspose' F hF f
  constructor
  · constructor
    · filter_upwards with x
      exact (hf.1 x).congr ((hrow x).mul (Filter.EventuallyEq.rfl))
    · filter_upwards [hf.2] with x hx
      exact hx.trans (integral_congr_ae ((hrow x).mul (Filter.EventuallyEq.rfl)))
  · constructor
    · filter_upwards with x
      exact (hb.1 x).congr ((hcol x).mul (Filter.EventuallyEq.rfl))
    · filter_upwards [hb.2] with x hx
      exact hx.trans (integral_congr_ae ((hcol x).mul (Filter.EventuallyEq.rfl)))

/-- The explicit Riesz pairing has compatible forward and transpose rows. -/
theorem s3_semigroup_split_explicit_compatible_rows {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ≥0)
    (hsplit : P (s + s) = (P s).comp (P s))
    (hsplitdag : Pdag (s + s) = (Pdag s).comp (Pdag s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hE : ∀ f, (P s f : Vec d → ℂ) =ᵐ[volume] fun x => E x f)
    (hF : ∀ f, (Pdag s f : Vec d → ℂ) =ᵐ[volume] fun x => F x f) :
    let K : Vec d → Vec d → ℂ := fun x y =>
      E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P (s + s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag (s + s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y) := by
  dsimp only
  let K : Vec d → Vec d → ℂ := fun x y =>
    E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
  have hrow (x : Vec d) :
      (fun y => Pdag s (star ((InnerProductSpace.toDual ℂ _).symm (E x))) y)
        =ᵐ[volume] K x := by
    filter_upwards [hF (star ((InnerProductSpace.toDual ℂ _).symm (E x)))] with y hy
    exact hy.trans (s3_riesz_bilinear_symmetry (F y) (E x))
  have hcol (x : Vec d) :
      (fun y => P s (star ((InnerProductSpace.toDual ℂ _).symm (F x))) y)
        =ᵐ[volume] fun y => K y x := hE _
  have htranspose' : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, Pdag s f x * g x) = ∫ x, f x * P s g x := by
    intro f g
    simpa only [mul_comm] using (htranspose g f).symm
  intro f
  have hf := s3_semigroup_split_forward_rows P Pdag s hsplit htranspose E hE f
  have hb := s3_semigroup_split_forward_rows Pdag P s hsplitdag htranspose' F hF f
  constructor
  · constructor
    · filter_upwards with x
      exact (hf.1 x).congr ((hrow x).mul (Filter.EventuallyEq.rfl))
    · filter_upwards [hf.2] with x hx
      exact hx.trans (integral_congr_ae ((hrow x).mul (Filter.EventuallyEq.rfl)))
  · constructor
    · filter_upwards with x
      exact (hb.1 x).congr ((hcol x).mul (Filter.EventuallyEq.rfl))
    · filter_upwards [hb.2] with x hx
      exact hx.trans (integral_congr_ae ((hcol x).mul (Filter.EventuallyEq.rfl)))

#print axioms s3_semigroup_split_explicit_compatible_rows

/-- The split Riesz kernel is controlled by the norms of its two evaluation
functionals. -/
theorem s3_bilinear_evaluation_kernel_norm_le {d : ℕ}
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (x y : Vec d) :
    ‖E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))‖ ≤ ‖E x‖ * ‖F y‖ := by
  have hs (u : Lp ℂ 2 (volume : Measure (Vec d))) : ‖star u‖ = ‖u‖ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star u), eLpNorm_star]
  have h := (E x).le_opNorm (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
  rw [hs, (InnerProductSpace.toDual ℂ _).symm.norm_map] at h
  exact h

#print axioms s3_bilinear_evaluation_kernel_norm_le

private theorem s3_physicalLp_star_add {d : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) : star (f + g) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g, Lp.coeFn_star f,
    Lp.coeFn_star g, Lp.coeFn_add (star f) (star g)] with x h1 h2 h3 h4 h5
  simpa only [Pi.star_apply, Pi.add_apply, h1, h2, h3, h4, h5, star_add]

private theorem s3_physicalLp_star_smul {d : ℕ}
    (c : ℂ) (f : Lp ℂ 2 (volume : Measure (Vec d))) : star (c • f) = star c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f, Lp.coeFn_star f,
    Lp.coeFn_smul (star c) (star f)] with x h1 h2 h3 h4
  simpa only [Pi.star_apply, Pi.smul_apply, h1, h2, h3, h4, star_smul]

/-- The conjugated Riesz map is complex-linear and norm-preserving. -/
noncomputable def s3BilinearRieszMap {d : ℕ} :
    (Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)) := by
  let L : (Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)) :=
    { toFun := fun f => star ((InnerProductSpace.toDual ℂ _).symm f)
      map_add' := by intro f g; simp [s3_physicalLp_star_add]
      map_smul' := by
        intro c f
        rw [map_smulₛₗ, s3_physicalLp_star_smul]
        simp }
  have h (f : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) : ‖L f‖ ≤ 1 * ‖f‖ := by
    change ‖star ((InnerProductSpace.toDual ℂ _).symm f)‖ ≤ 1 * ‖f‖
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star _), eLpNorm_star, ← Lp.norm_def,
      (InnerProductSpace.toDual ℂ _).symm.norm_map, one_mul]
  exact L.mkContinuous 1 h

#print axioms s3BilinearRieszMap

/-- Norm-C¹ forward and transpose evaluation maps yield a jointly C¹ split
kernel through the bounded bilinear Riesz pairing. -/
theorem s3_bilinear_evaluation_kernel_jointly_C1 {d : ℕ}
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hE : ContDiff ℝ 1 E) (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (fun z : Vec d × Vec d =>
      E z.1 (star ((InnerProductSpace.toDual ℂ _).symm (F z.2)))) := by
  have hleft : ContDiff ℝ 1 (fun z : Vec d × Vec d => (E z.1).restrictScalars ℝ) :=
    (ContinuousLinearMap.restrictScalarsL ℂ (Lp ℂ 2 (volume : Measure (Vec d)))
      ℂ ℝ ℝ).contDiff.comp (hE.comp contDiff_fst)
  have hright : ContDiff ℝ 1 (fun z : Vec d × Vec d => s3BilinearRieszMap (F z.2)) :=
    (s3BilinearRieszMap.restrictScalars ℝ).contDiff.comp (hF.comp contDiff_snd)
  simpa [s3BilinearRieszMap] using hleft.clm_apply hright

#print axioms s3_bilinear_evaluation_kernel_jointly_C1

/-- The bilinear Riesz kernel inherits spatial regularity in each variable
from regular representatives of the forward and transpose actions. -/
theorem s3_bilinear_evaluation_kernel_separately_C1 {d : ℕ}
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hE : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ ∀ x, E x f = u x)
    (hF : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ ∀ x, F x f = u x) :
    let K := fun x y => E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
    (∀ y, ContDiff ℝ 1 (fun x => K x y)) ∧
      ∀ x, ContDiff ℝ 1 (fun y => K x y) := by
  constructor
  · intro y
    obtain ⟨u, hu, he⟩ := hE (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
    have heq : (fun x => E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))) = u :=
      funext he
    rw [heq]
    exact hu
  · intro x
    obtain ⟨u, hu, he⟩ := hF (star ((InnerProductSpace.toDual ℂ _).symm (E x)))
    have heq : (fun y => E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))) = u := by
      funext y
      exact (s3_riesz_bilinear_symmetry (E x) (F y)).trans (he y)
    rw [heq]
    exact hu

#print axioms s3_bilinear_evaluation_kernel_separately_C1

/-- Quantitative C¹ representatives determine one bounded evaluation family,
with the original Euclidean gradient estimate for every input. -/
theorem s3_evaluations_of_quantitative_C1_representatives {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (C : ℝ) (hC : 0 ≤ C)
    (hrep : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ C * ‖f‖) :
    ∃ E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      (∀ x, ‖E x‖ ≤ C) ∧
      (∀ f, (T f : Vec d → ℂ) =ᵐ[volume] fun x => E x f) ∧
      (∀ f, ContDiff ℝ 1 (fun x => E x f)) ∧
      (∀ f x, ‖E x f‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => E z f) x (unitVector j)‖ ^ 2) ≤ C * ‖f‖) := by
  classical
  have hc : ∀ f, ∃ u : Vec d → ℂ, Continuous u ∧
      u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ x, ‖u x‖ ≤ C * ‖f‖ := by
    intro f
    obtain ⟨u, hu, he, hb⟩ := hrep f
    refine ⟨u, hu.continuous, he, fun x => ?_⟩
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (hb x)
  have hpoint (x : Vec d) := c18_point_evaluation_of_continuous_representatives T x C hC hc
  let E := fun x => Classical.choose (hpoint x)
  have heval (f : Lp ℂ 2 (volume : Measure (Vec d))) :
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
        u =ᵐ[volume] (T f : Vec d → ℂ) ∧
        (∀ x, E x f = u x) ∧ ∀ x,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ C * ‖f‖ := by
    obtain ⟨u, hu, he, hb⟩ := hrep f
    exact ⟨u, hu, he, fun x => (Classical.choose_spec (hpoint x)).2 f u hu.continuous he, hb⟩
  refine ⟨E, fun x => (Classical.choose_spec (hpoint x)).1, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨u, hu, he, hE, hb⟩ := heval f
    filter_upwards [he] with x hx
    exact hx.symm.trans (hE x).symm
  · intro f
    obtain ⟨u, hu, he, hE, hb⟩ := heval f
    rw [funext hE]
    exact hu
  · intro f x
    obtain ⟨u, hu, he, hE, hb⟩ := heval f
    have heq : (fun z => E z f) = u := funext hE
    rw [hE x, heq]
    exact hb x

#print axioms s3_evaluations_of_quantitative_C1_representatives

/-- Derivative bounds for the two evaluation families transfer to the
corresponding spatial derivatives of the split Riesz kernel. -/
theorem s3_bilinear_evaluation_kernel_derivative_bounds {d : ℕ}
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (A B : ℝ)
    (hE : ∀ f x v, ‖fderiv ℝ (fun z => E z f) x v‖ ≤ A * ‖f‖ * ‖v‖)
    (hF : ∀ f y v, ‖fderiv ℝ (fun z => F z f) y v‖ ≤ B * ‖f‖ * ‖v‖)
    (x y v : Vec d) :
    ‖fderiv ℝ (fun z => E z (star ((InnerProductSpace.toDual ℂ _).symm (F y)))) x v‖ ≤
        A * ‖F y‖ * ‖v‖ ∧
    ‖fderiv ℝ (fun z => E x (star ((InnerProductSpace.toDual ℂ _).symm (F z)))) y v‖ ≤
        B * ‖E x‖ * ‖v‖ := by
  have hs (L : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) :
      ‖star ((InnerProductSpace.toDual ℂ _).symm L)‖ = ‖L‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star _), eLpNorm_star,
      ← Lp.norm_def, (InnerProductSpace.toDual ℂ _).symm.norm_map]
  constructor
  · simpa only [hs] using hE (star ((InnerProductSpace.toDual ℂ _).symm (F y))) x v
  · have heq : (fun z => E x (star ((InnerProductSpace.toDual ℂ _).symm (F z)))) =
        (fun z => F z (star ((InnerProductSpace.toDual ℂ _).symm (E x)))) := by
      funext z
      exact s3_riesz_bilinear_symmetry (E x) (F z)
    rw [heq]
    simpa only [hs] using hF (star ((InnerProductSpace.toDual ℂ _).symm (E x))) y v

#print axioms s3_bilinear_evaluation_kernel_derivative_bounds

/-- Euclidean gradient estimates transfer directly to both variables of the
same split kernel, without replacing the Euclidean sum by a coordinate norm. -/
theorem s3_bilinear_evaluation_kernel_euclidean_gradient_bounds {d : ℕ}
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (A B : ℝ)
    (hE : ∀ f x, Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => E z f) x (unitVector j)‖ ^ 2) ≤ A * ‖f‖)
    (hF : ∀ f y, Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => F z f) y (unitVector j)‖ ^ 2) ≤ B * ‖f‖)
    (x y : Vec d) :
    Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z =>
      E z (star ((InnerProductSpace.toDual ℂ _).symm (F y)))) x (unitVector j)‖ ^ 2) ≤
        A * ‖F y‖ ∧
    Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z =>
      E x (star ((InnerProductSpace.toDual ℂ _).symm (F z)))) y (unitVector j)‖ ^ 2) ≤
        B * ‖E x‖ := by
  have hs (L : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) :
      ‖star ((InnerProductSpace.toDual ℂ _).symm L)‖ = ‖L‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star _), eLpNorm_star,
      ← Lp.norm_def, (InnerProductSpace.toDual ℂ _).symm.norm_map]
  constructor
  · simpa only [hs] using hE (star ((InnerProductSpace.toDual ℂ _).symm (F y))) x
  · have heq : (fun z => E x (star ((InnerProductSpace.toDual ℂ _).symm (F z)))) =
        (fun z => F z (star ((InnerProductSpace.toDual ℂ _).symm (E x)))) := by
      funext z
      exact s3_riesz_bilinear_symmetry (E x) (F z)
    rw [heq]
    simpa only [hs] using hF (star ((InnerProductSpace.toDual ℂ _).symm (E x))) y

#print axioms s3_bilinear_evaluation_kernel_euclidean_gradient_bounds

/-- Quantitative C¹ smoothing for a forward and transpose half-step gives
compatible kernel rows and Euclidean gradient bounds for both variables. -/
theorem s3_quantitative_C1_split_kernel {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ≥0)
    (hsplit : P (s + s) = (P s).comp (P s))
    (hsplitdag : Pdag (s + s) = (Pdag s).comp (Pdag s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (P s f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖)
    (hF : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (Pdag s f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ B * ‖f‖) :
    ∃ K : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P (s + s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag (s + s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) ∧
      (∀ y, ContDiff ℝ 1 (fun x => K x y)) ∧
      (∀ x, ContDiff ℝ 1 (fun y => K x y)) ∧
      ∀ x y, ‖K x y‖ ≤ A * B ∧
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) ≤ A * B ∧
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤ A * B := by
  obtain ⟨E, hEn, hEa, hEc, hEb⟩ :=
    s3_evaluations_of_quantitative_C1_representatives (P s) A hA hE
  obtain ⟨F, hFn, hFa, hFc, hFb⟩ :=
    s3_evaluations_of_quantitative_C1_representatives (Pdag s) B hB hF
  let K : Vec d → Vec d → ℂ := fun x y =>
    E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
  have hEs : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ ∀ x, E x f = u x :=
    fun f => ⟨fun x => E x f, hEc f, fun _ => rfl⟩
  have hFs : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ ∀ x, F x f = u x :=
    fun f => ⟨fun x => F x f, hFc f, fun _ => rfl⟩
  have hEg : ∀ f x, Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => E z f) x (unitVector j)‖ ^ 2) ≤ A * ‖f‖ := by
    intro f x
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hEb f x)
  have hFg : ∀ f y, Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => F z f) y (unitVector j)‖ ^ 2) ≤ B * ‖f‖ := by
    intro f y
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hFb f y)
  refine ⟨K, s3_semigroup_split_explicit_compatible_rows P Pdag s hsplit hsplitdag
    htranspose E F hEa hFa, (s3_bilinear_evaluation_kernel_separately_C1 E F hEs hFs).1,
    (s3_bilinear_evaluation_kernel_separately_C1 E F hEs hFs).2, ?_⟩
  intro x y
  have hg := s3_bilinear_evaluation_kernel_euclidean_gradient_bounds E F A B hEg hFg x y
  have hnorm : ‖E x‖ * ‖F y‖ ≤ A * B :=
    mul_le_mul (hEn x) (hFn y) (norm_nonneg _) hA
  refine ⟨(s3_bilinear_evaluation_kernel_norm_le E F x y).trans hnorm, ?_, ?_⟩
  · exact hg.1.trans (mul_le_mul_of_nonneg_left (hFn y) hA)
  · exact hg.2.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left (hEn x) hB)

#print axioms s3_quantitative_C1_split_kernel

/-- Quantitative positive-time C¹ smoothing assembles into one compatible
kernel, with separate spatial C¹ regularity and uniform gradient bounds. -/
theorem s3_quantitative_C1_kernel_of_positive_time_representatives {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hsplit : ∀ s t, P (s + t) = (P s).comp (P t))
    (hsplitdag : ∀ s t, Pdag (s + t) = (Pdag s).comp (Pdag t))
    (htranspose : ∀ (s : ℝ≥0) (f g : Lp ℂ 2 (volume : Measure (Vec d))),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (C : ℝ≥0 → ℝ) (hC : ∀ s, 0 ≤ C s)
    (hrep : ∀ s : ℝ≥0, 0 < s → ∀ T ∈ [P s, Pdag s],
      ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
        u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ x,
        ‖u x‖ + Real.sqrt (∑ j : Fin d,
          ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ C s * ‖f‖) :
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ,
      IsPhysicalComplexKernel P Pdag K ∧
      ∀ t : ℝ≥0, 0 < t →
        (∀ y, ContDiff ℝ 1 (fun x => K t x y)) ∧
        (∀ x, ContDiff ℝ 1 (fun y => K t x y)) ∧
        ∀ x y, ‖K t x y‖ ≤ C (t / 2) * C (t / 2) ∧
          Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖ ^ 2) ≤
            C (t / 2) * C (t / 2) ∧
          Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K t x z) y (unitVector j)‖ ^ 2) ≤
            C (t / 2) * C (t / 2) := by
  classical
  have htime (t : ℝ≥0) : ∃ K : Vec d → Vec d → ℂ, 0 < t →
      ((∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) ∧
      (∀ y, ContDiff ℝ 1 (fun x => K x y)) ∧
      (∀ x, ContDiff ℝ 1 (fun y => K x y)) ∧
      ∀ x y, ‖K x y‖ ≤ C (t / 2) * C (t / 2) ∧
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) ≤
          C (t / 2) * C (t / 2) ∧
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤
          C (t / 2) * C (t / 2)) := by
    by_cases ht : 0 < t
    · have hh : 0 < t / 2 := div_pos ht (by norm_num)
      obtain ⟨K, hk⟩ := s3_quantitative_C1_split_kernel P Pdag (t / 2)
        (hsplit _ _) (hsplitdag _ _) (htranspose _) (C (t / 2)) (C (t / 2))
        (hC _) (hC _) (hrep _ hh _ (by simp)) (hrep _ hh _ (by simp))
      simp only [add_halves] at hk
      exact ⟨K, fun _ => hk⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  refine ⟨fun t => Classical.choose (htime t), ?_, ?_⟩
  · intro t ht f
    exact (Classical.choose_spec (htime t) ht).1 f
  · intro t ht
    exact (Classical.choose_spec (htime t) ht).2

#print axioms s3_quantitative_C1_kernel_of_positive_time_representatives

/-- Bounded evaluations at every positive time assemble into a kernel for the
entire evolution. The kernel at zero is irrelevant to the kernel relation. -/
theorem s3_kernel_of_positive_time_evaluations {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hsplit : ∀ s t, P (s + t) = (P s).comp (P t))
    (hsplitdag : ∀ s t, Pdag (s + t) = (Pdag s).comp (Pdag t))
    (htranspose : ∀ (s : ℝ≥0) (f g : Lp ℂ 2 (volume : Measure (Vec d))),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (heval : ∀ s : ℝ≥0, 0 < s →
      ∃ E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
        (∀ f, (P s f : Vec d → ℂ) =ᵐ[volume] fun x => E x f) ∧
        (∀ f, (Pdag s f : Vec d → ℂ) =ᵐ[volume] fun x => F x f)) :
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ, IsPhysicalComplexKernel P Pdag K := by
  classical
  have htime (t : ℝ≥0) : ∃ K : Vec d → Vec d → ℂ, 0 < t →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y) := by
    by_cases ht : 0 < t
    · have hh : 0 < t / 2 := div_pos ht (by norm_num)
      obtain ⟨E, F, hE, hF⟩ := heval (t / 2) hh
      have h := s3_semigroup_split_compatible_rows P Pdag (t / 2)
        (hsplit _ _) (hsplitdag _ _) (htranspose _) E F hE hF
      simp only [add_halves] at h
      exact ⟨Classical.choose h, fun _ => Classical.choose_spec h⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  exact ⟨fun t => Classical.choose (htime t),
    fun t ht => Classical.choose_spec (htime t) ht⟩

/-- Continuous bounded representatives of both actions supply the point
functionals required for the split-kernel construction. -/
theorem s3_kernel_of_positive_time_continuous_representatives {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hsplit : ∀ s t, P (s + t) = (P s).comp (P t))
    (hsplitdag : ∀ s t, Pdag (s + t) = (Pdag s).comp (Pdag t))
    (htranspose : ∀ (s : ℝ≥0) (f g : Lp ℂ 2 (volume : Measure (Vec d))),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (hrep : ∀ s : ℝ≥0, 0 < s → ∀ T ∈ [P s, Pdag s],
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ∃ u : Vec d → ℂ, Continuous u ∧
        u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ x, ‖u x‖ ≤ C * ‖f‖) :
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ, IsPhysicalComplexKernel P Pdag K := by
  classical
  apply s3_kernel_of_positive_time_evaluations P Pdag hsplit hsplitdag htranspose
  intro s hs
  obtain ⟨C, hC, hE⟩ := hrep s hs (P s) (by simp)
  obtain ⟨D, hD, hF⟩ := hrep s hs (Pdag s) (by simp)
  have hE' (x : Vec d) := c18_point_evaluation_of_continuous_representatives
    (P s) x C hC hE
  have hF' (x : Vec d) := c18_point_evaluation_of_continuous_representatives
    (Pdag s) x D hD hF
  let E := fun x => Classical.choose (hE' x)
  let F := fun x => Classical.choose (hF' x)
  refine ⟨E, F, ?_, ?_⟩
  · intro f
    obtain ⟨u, hu, he, _⟩ := hE f
    have h := fun x => (Classical.choose_spec (hE' x)).2 f u hu he
    filter_upwards [he] with x hx
    exact hx.symm.trans (h x).symm
  · intro f
    obtain ⟨u, hu, he, _⟩ := hF f
    have h := fun x => (Classical.choose_spec (hF' x)).2 f u hu he
    filter_upwards [he] with x hx
    exact hx.symm.trans (h x).symm

/-- C¹ representatives of both actions yield a single compatible kernel
whose positive-time sections are C¹ in each spatial variable. -/
theorem s3_separately_C1_kernel_of_positive_time_representatives {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hsplit : ∀ s t, P (s + t) = (P s).comp (P t))
    (hsplitdag : ∀ s t, Pdag (s + t) = (Pdag s).comp (Pdag t))
    (htranspose : ∀ (s : ℝ≥0) (f g : Lp ℂ 2 (volume : Measure (Vec d))),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (hrep : ∀ s : ℝ≥0, 0 < s → ∀ T ∈ [P s, Pdag s],
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
        u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ x, ‖u x‖ ≤ C * ‖f‖) :
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ,
      IsPhysicalComplexKernel P Pdag K ∧
      ∀ t : ℝ≥0, 0 < t →
        (∀ y, ContDiff ℝ 1 (fun x => K t x y)) ∧
        ∀ x, ContDiff ℝ 1 (fun y => K t x y) := by
  classical
  have htime (t : ℝ≥0) : ∃ K : Vec d → Vec d → ℂ, 0 < t →
      ((∀ y, ContDiff ℝ 1 (fun x => K x y)) ∧
        (∀ x, ContDiff ℝ 1 (fun y => K x y))) ∧
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y) := by
    by_cases ht : 0 < t
    · have hh : 0 < t / 2 := div_pos ht (by norm_num)
      obtain ⟨C, hC, hE⟩ := hrep (t / 2) hh (P (t / 2)) (by simp)
      obtain ⟨D, hD, hF⟩ := hrep (t / 2) hh (Pdag (t / 2)) (by simp)
      have hEc : ∀ f, ∃ u : Vec d → ℂ, Continuous u ∧
          u =ᵐ[volume] (P (t / 2) f : Vec d → ℂ) ∧ ∀ x, ‖u x‖ ≤ C * ‖f‖ := by
        intro f
        obtain ⟨u, hu, he, hb⟩ := hE f
        exact ⟨u, hu.continuous, he, hb⟩
      have hFc : ∀ f, ∃ u : Vec d → ℂ, Continuous u ∧
          u =ᵐ[volume] (Pdag (t / 2) f : Vec d → ℂ) ∧ ∀ x, ‖u x‖ ≤ D * ‖f‖ := by
        intro f
        obtain ⟨u, hu, he, hb⟩ := hF f
        exact ⟨u, hu.continuous, he, hb⟩
      have hE' (x : Vec d) := c18_point_evaluation_of_continuous_representatives
        (P (t / 2)) x C hC hEc
      have hF' (x : Vec d) := c18_point_evaluation_of_continuous_representatives
        (Pdag (t / 2)) x D hD hFc
      let E := fun x => Classical.choose (hE' x)
      let F := fun x => Classical.choose (hF' x)
      have hEr : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ ∀ x, E x f = u x := by
        intro f
        obtain ⟨u, hu, he, _⟩ := hE f
        exact ⟨u, hu, fun x => (Classical.choose_spec (hE' x)).2 f u hu.continuous he⟩
      have hFr : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ ∀ x, F x f = u x := by
        intro f
        obtain ⟨u, hu, he, _⟩ := hF f
        exact ⟨u, hu, fun x => (Classical.choose_spec (hF' x)).2 f u hu.continuous he⟩
      have hEa (f : Lp ℂ 2 (volume : Measure (Vec d))) :
          (P (t / 2) f : Vec d → ℂ) =ᵐ[volume] fun x => E x f := by
        obtain ⟨u, hu, he, _⟩ := hE f
        filter_upwards [he] with x hx
        exact hx.symm.trans ((Classical.choose_spec (hE' x)).2 f u hu.continuous he).symm
      have hFa (f : Lp ℂ 2 (volume : Measure (Vec d))) :
          (Pdag (t / 2) f : Vec d → ℂ) =ᵐ[volume] fun x => F x f := by
        obtain ⟨u, hu, he, _⟩ := hF f
        filter_upwards [he] with x hx
        exact hx.symm.trans ((Classical.choose_spec (hF' x)).2 f u hu.continuous he).symm
      let K : Vec d → Vec d → ℂ := fun x y =>
        E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
      have hk := s3_semigroup_split_explicit_compatible_rows P Pdag (t / 2)
        (hsplit _ _) (hsplitdag _ _) (htranspose _) E F hEa hFa
      simp only [add_halves] at hk
      exact ⟨K, fun _ => ⟨s3_bilinear_evaluation_kernel_separately_C1 E F hEr hFr, hk⟩⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  refine ⟨fun t => Classical.choose (htime t), ?_, ?_⟩
  · intro t ht f
    exact (Classical.choose_spec (htime t) ht).2 f
  · intro t ht
    exact (Classical.choose_spec (htime t) ht).1

#print axioms s3_separately_C1_kernel_of_positive_time_representatives

/-- Uniform derivative bounds on scalar evaluations control the evaluation map
in operator norm. This upgrades pointwise regularity to norm continuity. -/
theorem s3_evaluation_operator_norm_sub_le {d : ℕ}
    (E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ f, Differentiable ℝ (fun x => E x f))
    (hb : ∀ f x, ‖fderiv ℝ (fun y => E y f) x‖ ≤ C * ‖f‖)
    (x y : Vec d) : ‖E y - E x‖ ≤ C * ‖y - x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro f
  have h : ‖E y f - E x f‖ ≤ (C * ‖f‖) * ‖y - x‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hd f z) (fun z _ => hb f z) (Set.mem_univ x) (Set.mem_univ y)
  simpa only [ContinuousLinearMap.sub_apply, mul_assoc, mul_comm, mul_left_comm] using h

#print axioms s3_evaluation_operator_norm_sub_le

/-- Norm-smooth positive-time evaluations produce one compatible kernel with
jointly C¹ spatial sections at every positive time. -/
theorem s3_jointly_C1_kernel_of_positive_time_evaluations {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hsplit : ∀ s t, P (s + t) = (P s).comp (P t))
    (hsplitdag : ∀ s t, Pdag (s + t) = (Pdag s).comp (Pdag t))
    (htranspose : ∀ (s : ℝ≥0) (f g : Lp ℂ 2 (volume : Measure (Vec d))),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (heval : ∀ s : ℝ≥0, 0 < s →
      ∃ E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
        (∀ f, (P s f : Vec d → ℂ) =ᵐ[volume] fun x => E x f) ∧
        (∀ f, (Pdag s f : Vec d → ℂ) =ᵐ[volume] fun x => F x f) ∧
        ContDiff ℝ 1 E ∧ ContDiff ℝ 1 F) :
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ,
      IsPhysicalComplexKernel P Pdag K ∧
      ∀ t : ℝ≥0, 0 < t → ContDiff ℝ 1 (fun z : Vec d × Vec d => K t z.1 z.2) := by
  classical
  have htime (t : ℝ≥0) : ∃ K : Vec d → Vec d → ℂ, 0 < t →
      (ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2) ∧
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) := by
    by_cases ht : 0 < t
    · have hh : 0 < t / 2 := div_pos ht (by norm_num)
      obtain ⟨E, F, hE, hF, hEc, hFc⟩ := heval (t / 2) hh
      let K : Vec d → Vec d → ℂ := fun x y =>
        E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
      have hk := s3_semigroup_split_explicit_compatible_rows P Pdag (t / 2)
        (hsplit _ _) (hsplitdag _ _) (htranspose _) E F hE hF
      simp only [add_halves] at hk
      exact ⟨K, fun _ => ⟨s3_bilinear_evaluation_kernel_jointly_C1 E F hEc hFc, hk⟩⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  refine ⟨fun t => Classical.choose (htime t), ?_, ?_⟩
  · intro t ht f
    exact (Classical.choose_spec (htime t) ht).2 f
  · intro t ht
    exact (Classical.choose_spec (htime t) ht).1

#print axioms s3_jointly_C1_kernel_of_positive_time_evaluations

#print axioms s3_kernel_of_positive_time_continuous_representatives
#print axioms s3_kernel_of_positive_time_evaluations
#print axioms s3_bounded_evaluation_riesz
#print axioms s3_evaluation_riesz_comp
#print axioms s3_adjoint_of_bilinear_transpose
#print axioms s3_evaluation_comp_bilinear_transpose
#print axioms s3_riesz_bilinear_symmetry
#print axioms s3_semigroup_split_forward_rows
#print axioms s3_semigroup_split_compatible_rows

/-- The Euclidean coordinate gradient bound controls the operator norm of the
real derivative on the project's coordinate carrier. -/
theorem s3_fderiv_norm_le_of_coordinate_gradient {d : ℕ}
    (u : Vec d → ℂ) (x : Vec d) (A : ℝ) (hA : 0 ≤ A)
    (hgrad : Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A) :
    ‖fderiv ℝ u x‖ ≤ (d : ℝ) * A := by
  classical
  have hcoord (j : Fin d) : ‖fderiv ℝ u x (unitVector j)‖ ≤ A := by
    have hs : ‖fderiv ℝ u x (unitVector j)‖ ^ 2 ≤
        ∑ k : Fin d, ‖fderiv ℝ u x (unitVector k)‖ ^ 2 :=
      Finset.single_le_sum (f := fun k : Fin d => ‖fderiv ℝ u x (unitVector k)‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hs' := Real.sqrt_le_sqrt hs
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs'
    exact hs'.trans hgrad
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hA)
  intro z
  have hz : z = ∑ j : Fin d, z j • unitVector j := by
    ext i
    simp [unitVector, Finset.sum_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = ‖∑ j : Fin d, z j • fderiv ℝ u x (unitVector j)‖ := by
      conv_lhs => rw [hz, map_sum]
      simp_rw [map_smul]
    _ ≤ ∑ j : Fin d, ‖z j • fderiv ℝ u x (unitVector j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, ‖z‖ * A := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm z j) (hcoord j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Quantitative scalar C¹ evaluations vary Lipschitz continuously in the
operator norm. This supplies the strong continuity needed in the split kernel. -/
theorem s3_quantitative_evaluations_lipschitz {d : ℕ}
    (E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ f, ContDiff ℝ 1 (fun x => E x f))
    (hb : ∀ f x, ‖E x f‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun y => E y f) x (unitVector j)‖ ^ 2) ≤ C * ‖f‖) :
    ∀ x y, ‖E y - E x‖ ≤ ((d : ℝ) * C) * ‖y - x‖ := by
  intro x y
  exact s3_evaluation_operator_norm_sub_le E ((d : ℝ) * C)
    (mul_nonneg (Nat.cast_nonneg _) hC)
    (fun f => (hd f).differentiable (by norm_num))
    (fun f z => by
      have hg : Real.sqrt (∑ j : Fin d,
          ‖fderiv ℝ (fun y => E y f) z (unitVector j)‖ ^ 2) ≤ C * ‖f‖ := by
        linarith [hb f z, norm_nonneg (E z f)]
      have h' := s3_fderiv_norm_le_of_coordinate_gradient (fun y => E y f) z
        (C * ‖f‖) (mul_nonneg hC (norm_nonneg _)) hg
      simpa only [mul_assoc] using h') x y

#print axioms s3_quantitative_evaluations_lipschitz

/-- Quantitative scalar evaluations are continuous as maps into the space of
bounded operators. -/
theorem s3_quantitative_evaluations_continuous {d : ℕ}
    (E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ f, ContDiff ℝ 1 (fun x => E x f))
    (hb : ∀ f x, ‖E x f‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun y => E y f) x (unitVector j)‖ ^ 2) ≤ C * ‖f‖) :
    Continuous E := by
  rw [Metric.continuous_iff]
  intro x ε hε
  let D : ℝ := (d : ℝ) * C
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hC
  have hD' : 0 < D + 1 := by linarith
  refine ⟨ε / (D + 1), div_pos hε hD', ?_⟩
  intro y hy
  rw [dist_eq_norm] at hy ⊢
  have h := s3_quantitative_evaluations_lipschitz E C hC hd hb x y
  change ‖E y - E x‖ ≤ D * ‖y - x‖ at h
  have hy' := (lt_div_iff₀ hD').mp hy
  nlinarith [norm_nonneg (y - x)]

/-- Quantitative smoothing yields one split kernel with both physical actions,
separately C¹ sections and joint spatial continuity. -/
theorem s3_quantitative_C1_jointly_continuous_split_kernel {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ≥0)
    (hsplit : P (s + s) = (P s).comp (P s))
    (hsplitdag : Pdag (s + s) = (Pdag s).comp (Pdag s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (P s f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖)
    (hF : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (Pdag s f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ B * ‖f‖) :
    ∃ K : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P (s + s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag (s + s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) ∧
      Continuous (fun z : Vec d × Vec d => K z.1 z.2) ∧
      (∀ y, ContDiff ℝ 1 (fun x => K x y)) ∧
      (∀ x, ContDiff ℝ 1 (fun y => K x y)) ∧
      ∀ x y, ‖K x y‖ ≤ A * B ∧
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) ≤ A * B ∧
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤ A * B := by
  obtain ⟨E, hEn, hEa, hEc, hEb⟩ :=
    s3_evaluations_of_quantitative_C1_representatives (P s) A hA hE
  obtain ⟨F, hFn, hFa, hFc, hFb⟩ :=
    s3_evaluations_of_quantitative_C1_representatives (Pdag s) B hB hF
  let K : Vec d → Vec d → ℂ := fun x y =>
    E x (star ((InnerProductSpace.toDual ℂ _).symm (F y)))
  have hEs : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ ∀ x, E x f = u x :=
    fun f => ⟨fun x => E x f, hEc f, fun _ => rfl⟩
  have hFs : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ ∀ x, F x f = u x :=
    fun f => ⟨fun x => F x f, hFc f, fun _ => rfl⟩
  have hEg : ∀ f x, Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => E z f) x (unitVector j)‖ ^ 2) ≤ A * ‖f‖ := by
    intro f x
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hEb f x)
  have hFg : ∀ f y, Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => F z f) y (unitVector j)‖ ^ 2) ≤ B * ‖f‖ := by
    intro f y
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hFb f y)
  have hEt := s3_quantitative_evaluations_continuous E A hA hEc hEb
  have hFt := s3_quantitative_evaluations_continuous F B hB hFc hFb
  have hleft : Continuous (fun z : Vec d × Vec d => (E z.1).restrictScalars ℝ) :=
    (ContinuousLinearMap.restrictScalarsL ℂ (Lp ℂ 2 (volume : Measure (Vec d)))
      ℂ ℝ ℝ).continuous.comp (hEt.comp continuous_fst)
  have hright : Continuous (fun z : Vec d × Vec d => s3BilinearRieszMap (F z.2)) :=
    (s3BilinearRieszMap.restrictScalars ℝ).continuous.comp (hFt.comp continuous_snd)
  have hK : Continuous (fun z : Vec d × Vec d => K z.1 z.2) := by
    simpa [K, s3BilinearRieszMap] using hleft.clm_apply hright
  refine ⟨K, s3_semigroup_split_explicit_compatible_rows P Pdag s hsplit hsplitdag
    htranspose E F hEa hFa, hK, (s3_bilinear_evaluation_kernel_separately_C1 E F hEs hFs).1,
    (s3_bilinear_evaluation_kernel_separately_C1 E F hEs hFs).2, ?_⟩
  intro x y
  have hg := s3_bilinear_evaluation_kernel_euclidean_gradient_bounds E F A B hEg hFg x y
  have hnorm : ‖E x‖ * ‖F y‖ ≤ A * B :=
    mul_le_mul (hEn x) (hFn y) (norm_nonneg _) hA
  refine ⟨(s3_bilinear_evaluation_kernel_norm_le E F x y).trans hnorm, ?_, ?_⟩
  · exact hg.1.trans (mul_le_mul_of_nonneg_left (hFn y) hA)
  · exact hg.2.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left (hEn x) hB)

#print axioms s3_quantitative_C1_jointly_continuous_split_kernel

end EinsteinFull
