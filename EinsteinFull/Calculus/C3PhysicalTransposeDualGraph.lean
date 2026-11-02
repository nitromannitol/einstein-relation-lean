import EinsteinFull.Calculus.C3PhysicalBilinearTranspose
import EinsteinFull.Calculus.C4PhysicalGeneratorGradientBound
import EinsteinFull.Calculus.PhysicalDomainSupport
import EinsteinFull.Calculus.S5CoefficientSupport
import EinsteinFull.Calculus.PhysicalH1ClosedGraphSupport
import EinsteinRelation.Correctors.WeakPartialAddition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
-- Variational graph arguments adapted locally from c2's checked private lemmas.
private theorem c3t_entry_bound {d : ℕ} {A : Mat d} {Λ : ℝ}
    (hA : S5Elliptic A Λ) (j k : Fin d) : |A j k| ≤ Λ := by
  have h := s5Bil_abs_le hA (Pi.single j 1) (Pi.single k 1)
  simpa [s5Bil, s5Nrm, Pi.single_apply, ite_mul, mul_ite] using h

private def c3t_physicalCoefficientMul {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (j k : Fin d) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 ((ha j k).toLp _)

private theorem c3t_physicalCoefficientMul_coe {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (j k : Fin d)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    c3t_physicalCoefficientMul a ha j k f =ᵐ[volume] fun x => (a x j k : ℂ) * f x := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((ha j k).toLp _) f
  filter_upwards [(ha j k).coeFn_toLp, hm] with x hx hmx
  simpa only [c3t_physicalCoefficientMul, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hx] using hmx

private theorem c3t_physicalCoefficientMul_bound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (j k : Fin d)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖c3t_physicalCoefficientMul a ha j k u‖ ≤ Λ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hA, c3t_physicalCoefficientMul_coe a ha j k u] with x hx hu
  rw [hu, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using c3t_entry_bound hx j k)
    (norm_nonneg _)

private theorem c3t_weakPartial_smul {d : ℕ} {U : Set (Vec d)} {j : Fin d}
    {f g : Vec d → ℝ} (h : HasWeakPartialDerivative U j f g) (c : ℝ) :
    HasWeakPartialDerivative U j (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨fun x hx => (h.1 x hx).smul c,
    fun x hx => (h.2.1 x hx).smul c, ?_⟩
  intro φ hφ
  simp only [mul_assoc, integral_const_mul]
  rw [h.2.2 φ hφ]
  ring

private def c3t_physicalGraph (d : ℕ) :
    Submodule ℝ (PiLp 2 (fun _ : Option (Fin d) => Lp ℂ 2 (volume : Measure (Vec d)))) where
  carrier := {u | IsPhysicalH1Graph volume (Or.inl rfl) (u none) (fun j => u (some j))}
  zero_mem' := by
    apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
      (fun _ => 0) (fun _ _ => 0) (Lp.coeFn_zero _ _ _) (fun _ => Lp.coeFn_zero _ _ _)).mpr
    constructor <;> intro j <;>
      exact ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, by intros; simp⟩
  add_mem' := by
    intro u v hu hv
    apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
      (fun x => u none x + v none x)
      (fun j x => u (some j) x + v (some j) x)
      (Lp.coeFn_add _ _) (fun _ => Lp.coeFn_add _ _)).mpr
    constructor
    · intro j
      simpa only [Complex.add_re] using Correctors.hasWeakPartialDerivative_add (hu.1 j) (hv.1 j)
    · intro j
      simpa only [Complex.add_im] using Correctors.hasWeakPartialDerivative_add (hu.2 j) (hv.2 j)
  smul_mem' := by
    intro c u hu
    apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
      (fun x => c • u none x) (fun j x => c • u (some j) x)
      (Lp.coeFn_smul _ _) (fun _ => Lp.coeFn_smul _ _)).mpr
    constructor
    · intro j
      simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using c3t_weakPartial_smul (hu.1 j) c
    · intro j
      simpa only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using c3t_weakPartial_smul (hu.2 j) c

private theorem c3t_physicalGraph_closed (d : ℕ) :
    IsClosed (c3t_physicalGraph d : Set
      (PiLp 2 (fun _ : Option (Fin d) => Lp ℂ 2 (volume : Measure (Vec d))))) := by
  let T : PiLp 2 (fun _ : Option (Fin d) => Lp ℂ 2 (volume : Measure (Vec d))) →
      Lp ℂ 2 (volume : Measure (Vec d)) × (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :=
    fun u => (u none, fun j => u (some j))
  have hT : Continuous T := (PiLp.continuous_apply 2 _ none).prodMk
    (continuous_pi fun j => PiLp.continuous_apply 2 _ (some j))
  exact (isClosed_physicalH1Graph volume (Or.inl rfl)).preimage hT

private theorem c3t_physicalGraph_norm_sq {d : ℕ} (u : c3t_physicalGraph d) :
    ‖u‖ ^ 2 = ‖u.val none‖ ^ 2 + ∑ j : Fin d, ‖u.val (some j)‖ ^ 2 := by
  rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2, univ_option,
    Finset.sum_insertNone]

private def c3t_physicalGraphEval {d : ℕ} (o : Option (Fin d)) :
    c3t_physicalGraph d →L[ℝ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin d) => Lp ℂ 2 (volume : Measure (Vec d))) o).comp
    (c3t_physicalGraph d).subtypeL

private instance c3t_physicalGraph_complete (d : ℕ) :
    CompleteSpace (c3t_physicalGraph d) :=
  (c3t_physicalGraph_closed d).completeSpace_coe

private theorem c3t_physical_energy_lowerBound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    Λ⁻¹ * ∑ j, ‖G j‖ ^ 2 ≤
      ∑ j, ∑ k, inner ℝ (G j) (c3t_physicalCoefficientMul a ha j k (G k)) := by
  have hint (j k : Fin d) : Integrable
      (fun x => star (G j x) * (a x j k : ℂ) * G k x) volume := by
    have hp := ((Lp.memLp (G j)).star.integrable_mul (Lp.memLp (G k))).mul_of_top_right
      (ha j k)
    convert hp using 1
    ext x
    simp only [Pi.mul_apply, Pi.star_apply]
    ring
  have hsum : (∫ x, ∑ j, ∑ k, star (G j x) * (a x j k : ℂ) * G k x) =
      ∑ j, ∑ k, inner ℂ (G j) (c3t_physicalCoefficientMul a ha j k (G k)) := by
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum _ (fun k _ => hint j k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [c3t_physicalCoefficientMul_coe a ha j k (G k)] with x hx
    simp only [hx, RCLike.inner_apply, Complex.star_def]
    ring
  have hreal (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
      inner ℝ u v = (inner ℂ u v).re := by
    rw [L2.inner_def, L2.inner_def]
    exact integral_re (L2.integrable_inner (𝕜 := ℂ) u v)
  have hn (u : Lp ℂ 2 (volume : Measure (Vec d))) :
      ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hN := integrable_finsetSum Finset.univ (fun j _ => (Lp.memLp (G j)).norm.integrable_sq)
  have hB := integrable_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hint j k))
  have hle : ∀ᵐ x ∂volume, Λ⁻¹ * ∑ j, ‖G j x‖ ^ 2 ≤
      (∑ j, ∑ k, star (G j x) * (a x j k : ℂ) * G k x).re := by
    filter_upwards [hA] with x hx
    convert s5_coercive hx (fun j => G j x) using 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    simp only [starRingEnd_apply]
    ring
  have hi := integral_mono_ae (hN.const_mul Λ⁻¹) hB.re hle
  rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
    (Lp.memLp (G j)).norm.integrable_sq), integral_re hB, hsum] at hi
  change Λ⁻¹ * (∑ j, ∫ x, ‖G j x‖ ^ 2) ≤
    (∑ j, ∑ k, inner ℂ (G j) (c3t_physicalCoefficientMul a ha j k (G k))).re at hi
  simpa only [hn, Complex.re_sum, hreal] using hi

private def c3t_physicalShiftedForm {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) :
    c3t_physicalGraph d →L[ℝ] c3t_physicalGraph d →L[ℝ] ℝ :=
  let E := c3t_physicalGraphEval (d := d)
  let I : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ] ℝ := innerSL ℝ
  let C := fun j k => (c3t_physicalCoefficientMul a ha j k).restrictScalars ℝ
  s • I.bilinearComp (E none) (E none) + (1 / 2 : ℝ) •
    ∑ j : Fin d, ∑ k : Fin d,
      (I.bilinearComp (E (some j)) ((C j k).comp (E (some k)))).flip -
    (I.bilinearComp (E none) (ζ • ∑ j : Fin d, (C j i).comp (E (some j)))).flip

private theorem c3t_physicalShiftedForm_apply {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (u v : c3t_physicalGraph d) :
    c3t_physicalShiftedForm a ha i ζ s u v =
      s * inner ℝ (u.val none) (v.val none) +
      (1 / 2 : ℝ) * ∑ j, ∑ k,
        inner ℝ (v.val (some j)) (c3t_physicalCoefficientMul a ha j k (u.val (some k))) -
      inner ℝ (v.val none) (ζ • ∑ j, c3t_physicalCoefficientMul a ha j i (u.val (some j))) := by
  simp only [c3t_physicalShiftedForm, add_apply,
    sub_apply, smul_apply,
    sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', c3t_physicalGraphEval,
    PiLp.proj_apply, Submodule.subtypeL_apply, smul_eq_mul]
  rfl

private theorem c3t_physical_drift_absorption {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (u : c3t_physicalGraph d) :
    |inner ℝ (u.val none) (ζ • ∑ j,
      c3t_physicalCoefficientMul a ha j i (u.val (some j)))| ≤
      (Λ⁻¹ / 4) * ∑ j : Fin d, ‖u.val (some j)‖ ^ 2 +
        (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * ‖u.val none‖ ^ 2 := by
  have hy (x y : ℝ) : x * y ≤ (Λ⁻¹ / 4) * x ^ 2 + Λ * y ^ 2 := by
    have hid : (Λ⁻¹ / 4) * x ^ 2 + Λ * y ^ 2 - x * y =
        (4 * Λ)⁻¹ * (x - 2 * Λ * y) ^ 2 := by
      field_simp [ne_of_gt hΛ]
      ring
    exact sub_nonneg.mp (hid ▸ mul_nonneg (by positivity) (sq_nonneg _))
  have hc (j : Fin d) :=
    c3t_physicalCoefficientMul_bound a ha hA j i (u.val (some j))
  have hd : ‖ζ • ∑ j, c3t_physicalCoefficientMul a ha j i (u.val (some j))‖ ≤
      ‖ζ‖ * ∑ j : Fin d, Λ * ‖u.val (some j)‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hc j)) (norm_nonneg _)
  calc
    _ ≤ ‖u.val none‖ * ‖ζ • ∑ j,
        c3t_physicalCoefficientMul a ha j i (u.val (some j))‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u.val none‖ * (‖ζ‖ * ∑ j : Fin d, Λ * ‖u.val (some j)‖) :=
      mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ∑ j : Fin d, ‖u.val (some j)‖ * (‖ζ‖ * Λ * ‖u.val none‖) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j : Fin d, ((Λ⁻¹ / 4) * ‖u.val (some j)‖ ^ 2 +
        Λ * (‖ζ‖ * Λ * ‖u.val none‖) ^ 2) :=
      Finset.sum_le_sum fun j _ => hy _ _
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum]; ring

private theorem c3t_physicalShiftedForm_coercive {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (_hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) (u : c3t_physicalGraph d) :
    min (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (Λ⁻¹ / 4) * ‖u‖ ^ 2 ≤
      c3t_physicalShiftedForm a ha i ζ s u u := by
  have henergy := c3t_physical_energy_lowerBound a ha hA (fun j => u.val (some j))
  have hdrift := c3t_physical_drift_absorption a ha hΛ hA i ζ u
  have hn : 0 ≤ ∑ j : Fin d, ‖u.val (some j)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm := add_le_add
    (mul_le_mul_of_nonneg_right
      (min_le_left (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (Λ⁻¹ / 4))
      (sq_nonneg ‖u.val none‖))
    (mul_le_mul_of_nonneg_right
      (min_le_right (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (Λ⁻¹ / 4)) hn)
  rw [← mul_add, ← c3t_physicalGraph_norm_sq] at hm
  rw [c3t_physicalShiftedForm_apply, real_inner_self_eq_norm_sq]
  have hd := (le_abs_self _).trans hdrift
  nlinarith only [hm, henergy, hd]

private theorem c3t_physicalShiftedForm_isCoercive {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) :
    IsCoercive (c3t_physicalShiftedForm a ha i ζ s) := by
  refine ⟨min (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (Λ⁻¹ / 4),
    lt_min (sub_pos.mpr hs) (by positivity), fun u => ?_⟩
  have h := c3t_physicalShiftedForm_coercive a ha hΛ hA i ζ s hs u
  nlinarith only [h]

private def c3t_physicalGraphResolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ] c3t_physicalGraph d :=
  (c3t_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp (c3t_physicalGraphEval (d := d) none).adjoint

private theorem c3t_physicalGraphResolvent_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (v : c3t_physicalGraph d) :
    c3t_physicalShiftedForm a ha i ζ s
      (c3t_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs) v =
      inner ℝ rhs (v.val none) := by
  let hB := c3t_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs
  have hb := hB.continuousLinearEquivOfBilin_apply
    (c3t_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs) v
  change inner ℝ (hB.continuousLinearEquivOfBilin
    (hB.continuousLinearEquivOfBilin.symm ((c3t_physicalGraphEval none).adjoint rhs))) v = _ at hb
  rw [hB.continuousLinearEquivOfBilin.apply_symm_apply] at hb
  exact hb.symm.trans ((c3t_physicalGraphEval none).adjoint_inner_left v rhs)

private def c3t_physicalGraphComplexSmul {d : ℕ} (c : ℂ)
    (u : c3t_physicalGraph d) : c3t_physicalGraph d := by
  refine ⟨c • u.val, ?_⟩
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => c * u.val none x) (fun j x => c * u.val (some j) x)
    (Lp.coeFn_smul _ _) (fun _ => Lp.coeFn_smul _ _)).mpr
  constructor
  · intro j
    have h := Correctors.hasWeakPartialDerivative_add
      (c3t_weakPartial_smul (u.property.1 j) c.re)
      (c3t_weakPartial_smul (u.property.2 j) (-c.im))
    simpa only [Complex.mul_re, neg_mul, sub_eq_add_neg] using h
  · intro j
    have h := Correctors.hasWeakPartialDerivative_add
      (c3t_weakPartial_smul (u.property.2 j) c.re)
      (c3t_weakPartial_smul (u.property.1 j) c.im)
    simpa only [Complex.mul_im] using h

private def c3t_physicalGraphStar {d : ℕ} (u : c3t_physicalGraph d) :
    c3t_physicalGraph d := by
  refine ⟨WithLp.toLp 2 (fun o => star (u.val o)), ?_⟩
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => star (u.val none x)) (fun j x => star (u.val (some j) x))
    (Lp.coeFn_star _) (fun _ => Lp.coeFn_star _)).mpr
  constructor
  · simpa only [Complex.star_def, Complex.conj_re] using u.property.1
  · intro j
    simpa only [Complex.star_def, Complex.conj_im, neg_one_mul] using
      c3t_weakPartial_smul (u.property.2 j) (-1)

private def c3t_physicalResolventExpression {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : c3t_physicalGraph d) : ℂ :=
  (s : ℂ) * inner ℂ (v.val none) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
    ∑ j, ∑ k, inner ℂ (v.val (some j)) (c3t_physicalCoefficientMul a ha j k (u.val (some k))) -
    inner ℂ (v.val none) (ζ • ∑ j, c3t_physicalCoefficientMul a ha j i (u.val (some j)))

private theorem c3t_physical_realInner {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) : inner ℝ u v = (inner ℂ u v).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) u v)

private theorem c3t_physicalShiftedForm_eq_re {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : c3t_physicalGraph d) :
    c3t_physicalShiftedForm a ha i ζ s u v = (c3t_physicalResolventExpression a ha i ζ s u v).re := by
  rw [c3t_physicalShiftedForm_apply]
  simp only [c3t_physical_realInner, c3t_physicalResolventExpression,
    Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_sum]
  rw [show (inner ℂ (u.val none) (v.val none)).re =
    (inner ℂ (v.val none) (u.val none)).re from inner_re_symm (𝕜 := ℂ) _ _]

private theorem c3t_physicalResolventExpression_I {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : c3t_physicalGraph d) :
    c3t_physicalResolventExpression a ha i ζ s u (c3t_physicalGraphComplexSmul Complex.I v) =
      -Complex.I * c3t_physicalResolventExpression a ha i ζ s u v := by
  simp only [c3t_physicalResolventExpression, c3t_physicalGraphComplexSmul,
    PiLp.smul_apply, inner_smul_left, Complex.conj_I, ← Finset.mul_sum]
  ring

private theorem c3t_physicalGraphResolvent_complex_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) (rhs : Lp ℂ 2 (volume : Measure (Vec d)))
    (v : c3t_physicalGraph d) :
    c3t_physicalResolventExpression a ha i ζ s (c3t_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs) v =
      inner ℂ (v.val none) rhs := by
  apply Complex.ext
  · have h := c3t_physicalGraphResolvent_spec a ha hΛ hA i ζ s hs rhs v
    rw [c3t_physicalShiftedForm_eq_re, c3t_physical_realInner] at h
    exact h.trans (inner_re_symm (𝕜 := ℂ) _ _)
  · have h := c3t_physicalGraphResolvent_spec a ha hΛ hA i ζ s hs rhs
      (c3t_physicalGraphComplexSmul Complex.I v)
    rw [c3t_physicalShiftedForm_eq_re, c3t_physicalResolventExpression_I,
      c3t_physical_realInner] at h
    change (-Complex.I * c3t_physicalResolventExpression a ha i ζ s _ v).re =
      (inner ℂ rhs (Complex.I • v.val none)).re at h
    rw [inner_smul_right] at h
    simp only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] at h
    have him : (inner ℂ rhs (v.val none)).im = -(inner ℂ (v.val none) rhs).im :=
      inner_im_symm (𝕜 := ℂ) _ _
    linarith only [h, him]

private theorem c3t_physicalResolventExpression_smul {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (c : ℂ) (u v : c3t_physicalGraph d) :
    c3t_physicalResolventExpression a ha i ζ s (c3t_physicalGraphComplexSmul c u) v =
      c * c3t_physicalResolventExpression a ha i ζ s u v := by
  simp only [c3t_physicalResolventExpression, c3t_physicalGraphComplexSmul,
    PiLp.smul_apply, map_smul, inner_smul_right, ← Finset.smul_sum,
    smul_comm ζ c, ← Finset.mul_sum]
  ring

private theorem c3t_physical_energy_inner {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, ∑ j, ∑ k, star (G j x) * (a x j k : ℂ) * H k x) =
      ∑ j, ∑ k, inner ℂ (G j) (c3t_physicalCoefficientMul a ha j k (H k)) := by
  have hint (j k : Fin d) : Integrable
      (fun x => star (G j x) * (a x j k : ℂ) * H k x) volume := by
    have hp := ((Lp.memLp (G j)).star.integrable_mul (Lp.memLp (H k))).mul_of_top_right
      (ha j k)
    convert hp using 1
    ext x
    simp only [Pi.mul_apply, Pi.star_apply]
    ring
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun k _ => hint j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [c3t_physicalCoefficientMul_coe a ha j k (H k)] with x hx
  simp only [hx, RCLike.inner_apply, Complex.star_def]
  ring

private theorem c3t_physical_inner_star {d : ℕ}
    (v f : Lp ℂ 2 (volume : Measure (Vec d))) :
    inner ℂ (star v) f = ∫ x, v x * f x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star v] with x hx
  change (star v) x = star (v x) at hx
  simp only [hx, RCLike.inner_apply, Complex.star_def, starRingEnd_self_apply]
  ring

private theorem c3t_physical_drift_inner {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    inner ℂ (star v) (ζ • ∑ j, c3t_physicalCoefficientMul a ha j i (G j)) =
      ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * v x) := by
  have hint (j : Fin d) : Integrable
      (fun x => (a x j i : ℂ) * G j x * v x) volume := by
    have hp := ((Lp.memLp (G j)).integrable_mul (Lp.memLp v)).mul_of_top_right (ha j i)
    convert hp using 1
    ext x
    simp only [Pi.mul_apply]
    ring
  rw [inner_smul_right, inner_sum]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [c3t_physical_inner_star]
  apply integral_congr_ae
  filter_upwards [c3t_physicalCoefficientMul_coe a ha j i (G j)] with x hx
  rw [hx]
  ring

private theorem c3t_physicalGraphResolvent_generator {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) (rhs : Lp ℂ 2 (volume : Measure (Vec d))) :
    let u := c3t_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs
    IsPhysicalComplexGeneratorPair a i ζ (u.val none) ((s : ℂ) • u.val none - rhs) := by
  let u := c3t_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs
  refine ⟨fun j => u.val (some j), u.property, ?_⟩
  intro v Gv hv
  let w0 : c3t_physicalGraph d :=
    ⟨WithLp.toLp 2 (fun o => o.elim v Gv), hv⟩
  let w := c3t_physicalGraphStar w0
  have ht := c3t_physicalGraphResolvent_complex_spec a ha hΛ hA i ζ s hs rhs w
  change (s : ℂ) * inner ℂ (star v) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
    (∑ j, ∑ k, inner ℂ (star (Gv j)) (c3t_physicalCoefficientMul a ha j k (u.val (some k)))) -
    inner ℂ (star v) (ζ • ∑ j, c3t_physicalCoefficientMul a ha j i (u.val (some j))) =
    inner ℂ (star v) rhs at ht
  rw [← c3t_physical_energy_inner, c3t_physical_drift_inner] at ht
  simp only [c3t_physical_inner_star] at ht
  have hE : (∫ x, ∑ j, ∑ k, star ((star (Gv j) : Lp ℂ 2 (volume : Measure (Vec d))) x) *
      (a x j k : ℂ) * u.val (some k) x) =
      ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * u.val (some k) x * Gv j x := by
    apply integral_congr_ae
    have hgrad : ∀ᵐ x ∂volume, ∀ j, (star (Gv j) : Lp ℂ 2 (volume : Measure (Vec d))) x =
        star (Gv j x) := ae_all_iff.mpr fun j => Lp.coeFn_star (Gv j)
    filter_upwards [hgrad] with x hx
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hx j, star_star]
    ring
  rw [hE] at ht
  have hm : (∫ x, ((s : ℂ) • u.val none - rhs : Lp ℂ 2 (volume : Measure (Vec d))) x * v x) =
      (s : ℂ) * (∫ x, v x * u.val none x) - ∫ x, v x * rhs x := by
    calc
      _ = ∫ x, (s : ℂ) * (v x * u.val none x) - v x * rhs x := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub ((s : ℂ) • u.val none) rhs,
          Lp.coeFn_smul (s : ℂ) (u.val none)] with x hx hy
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx hy
        rw [hx, hy]
        ring
      _ = _ := by
        have h1 : Integrable (fun x => (s : ℂ) * (v x * u.val none x)) volume :=
          ((Lp.memLp v).integrable_mul (Lp.memLp (u.val none))).const_mul _
        have h2 : Integrable (fun x => v x * rhs x) volume :=
          (Lp.memLp v).integrable_mul (Lp.memLp rhs)
        rw [integral_sub h1 h2, integral_const_mul]
  rw [hm]
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf] at ht
  linear_combination ht

private noncomputable def c3t_physicalAdjointGraphResolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ] c3t_physicalGraph d :=
  (c3t_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.adjoint.comp
    (c3t_physicalGraphEval (d := d) none).adjoint

private theorem c3t_physicalAdjointGraphResolvent_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (v : c3t_physicalGraph d) :
    c3t_physicalShiftedForm a ha i ζ s v
      (c3t_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs rhs) =
      inner ℝ rhs (v.val none) := by
  let B := (c3t_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs).continuousLinearEquivOfBilin
  let S := c3t_physicalGraphEval (d := d) none
  rw [← (c3t_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs).continuousLinearEquivOfBilin_apply]
  rw [real_inner_comm]
  change inner ℝ (B.symm.toContinuousLinearMap.adjoint (S.adjoint rhs)) (B v) = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (S.adjoint rhs) (B.symm (B v)) = _
  rw [B.symm_apply_apply, S.adjoint_inner_left]
  rfl

private theorem c3t_physicalAdjointGraphResolvent_complex_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (v : c3t_physicalGraph d) :
    c3t_physicalResolventExpression a ha i ζ s v
      (c3t_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs rhs) =
      inner ℂ rhs (v.val none) := by
  apply Complex.ext
  · have h := c3t_physicalAdjointGraphResolvent_spec a ha hΛ hA i ζ s hs rhs v
    rw [c3t_physicalShiftedForm_eq_re, c3t_physical_realInner] at h
    exact h
  · have h := c3t_physicalAdjointGraphResolvent_spec a ha hΛ hA i ζ s hs rhs
      (c3t_physicalGraphComplexSmul Complex.I v)
    rw [c3t_physicalShiftedForm_eq_re, c3t_physicalResolventExpression_smul,
      c3t_physical_realInner] at h
    change (Complex.I * c3t_physicalResolventExpression a ha i ζ s v _).re =
      (inner ℂ rhs (Complex.I • v.val none)).re at h
    rw [inner_smul_right] at h
    simpa only [Complex.I_mul_re, neg_neg] using congrArg Neg.neg h

private def c3t_pair {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) : ℂ := ∫ x, u x * v x

private theorem c3t_pair_comm {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) : c3t_pair u v = c3t_pair v u := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => mul_comm _ _

private theorem c3t_pair_smul_sub {d : ℕ} (s : ℂ)
    (u v w : Lp ℂ 2 (volume : Measure (Vec d))) :
    c3t_pair (s • u - v) w = s * c3t_pair u w - c3t_pair v w := by
  calc
    _ = ∫ x, s * (u x * w x) - v x * w x := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (s • u) v, Lp.coeFn_smul s u] with x hx hy
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx hy
      rw [hx, hy]
      ring
    _ = _ := by
      have h1 : Integrable (fun x => s * (u x * w x)) volume :=
        ((Lp.memLp u).integrable_mul (Lp.memLp w)).const_mul s
      have h2 : Integrable (fun x => v x * w x) volume :=
        (Lp.memLp v).integrable_mul (Lp.memLp w)
      rw [integral_sub h1 h2, integral_const_mul]
      rfl

private theorem c3t_graphStar_star {d : ℕ} (u : c3t_physicalGraph d) :
    c3t_physicalGraphStar (c3t_physicalGraphStar u) = u := by
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  funext o
  exact star_star (u.val o)

private def c3t_bilinear {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (u v : c3t_physicalGraph d) : ℂ :=
  c3t_physicalResolventExpression a ha i ζ s u (c3t_physicalGraphStar v)

private theorem c3t_bilinear_apply {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (u v : c3t_physicalGraph d) :
    c3t_bilinear a ha i ζ s u v =
      (s : ℂ) * c3t_pair (u.val none) (v.val none) +
      (1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
        (a x j k : ℂ) * u.val (some k) x * v.val (some j) x) -
      ζ * (∫ x, (∑ j, (a x j i : ℂ) * u.val (some j) x) * v.val none x) := by
  change (s : ℂ) * inner ℂ (star (v.val none)) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
    (∑ j, ∑ k, inner ℂ (star (v.val (some j)))
      (c3t_physicalCoefficientMul a ha j k (u.val (some k)))) -
    inner ℂ (star (v.val none))
      (ζ • ∑ j, c3t_physicalCoefficientMul a ha j i (u.val (some j))) = _
  rw [← c3t_physical_energy_inner, c3t_physical_drift_inner]
  simp only [c3t_physical_inner_star]
  rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by norm_num]
  rw [show (∫ x, v.val none x * u.val none x) = c3t_pair (u.val none) (v.val none)
    from c3t_pair_comm _ _]
  congr 2
  congr 1
  apply integral_congr_ae
  have hgrad : ∀ᵐ x ∂volume, ∀ j,
      (star (v.val (some j)) : Lp ℂ 2 (volume : Measure (Vec d))) x =
        star (v.val (some j) x) := ae_all_iff.mpr fun j => Lp.coeFn_star _
  filter_upwards [hgrad] with x hx
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hx j, star_star]
  ring

private theorem c3t_forward_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (v : c3t_physicalGraph d) :
    c3t_bilinear a ha i ζ s (c3t_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs) v =
      c3t_pair rhs (v.val none) := by
  have h := c3t_physicalGraphResolvent_complex_spec a ha hΛ hA i ζ s hs rhs
    (c3t_physicalGraphStar v)
  change c3t_bilinear a ha i ζ s _ v = inner ℂ (star (v.val none)) rhs at h
  rw [c3t_physical_inner_star] at h
  exact h.trans (c3t_pair_comm _ _)

private def c3t_transposeResolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) : c3t_physicalGraph d :=
  c3t_physicalGraphStar (c3t_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs (star rhs))

private theorem c3t_transpose_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (v : c3t_physicalGraph d) :
    c3t_bilinear a ha i ζ s v (c3t_transposeResolvent a ha hΛ hA i ζ s hs rhs) =
      c3t_pair (v.val none) rhs := by
  unfold c3t_bilinear c3t_transposeResolvent
  rw [c3t_graphStar_star, c3t_physicalAdjointGraphResolvent_complex_spec,
    c3t_physical_inner_star]
  exact c3t_pair_comm _ _

private theorem c3t_transpose_generator {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (w : c3t_physicalGraph d)
    (hw : ∀ u, c3t_bilinear a ha i ζ s u w = c3t_pair (u.val none) rhs) :
    IsPhysicalComplexTransposeGeneratorPair a i ζ (w.val none)
      ((s : ℂ) • w.val none - rhs) := by
  refine ⟨fun j => w.val (some j), w.property, ?_⟩
  intro v Gv hv
  let u : c3t_physicalGraph d := ⟨WithLp.toLp 2 (fun o => o.elim v Gv), hv⟩
  have h := hw u
  rw [c3t_bilinear_apply] at h
  change (s : ℂ) * c3t_pair v (w.val none) +
    (1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * Gv k x * w.val (some j) x) -
    ζ * (∫ x, (∑ j, (a x j i : ℂ) * Gv j x) * w.val none x) = c3t_pair v rhs at h
  have hE : (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * Gv k x * w.val (some j) x) =
      ∫ x, ∑ j, ∑ k, (a x k j : ℂ) * w.val (some k) x * Gv j x := by
    congr 1
    ext x
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hD : (∫ x, (∑ j, (a x j i : ℂ) * Gv j x) * w.val none x) =
      ∫ x, w.val none x * (∑ j, (a x j i : ℂ) * Gv j x) := by
    congr 1
    ext x
    ring
  rw [hE, hD] at h
  change c3t_pair ((s : ℂ) • w.val none - rhs) v = _
  rw [c3t_pair_smul_sub, c3t_pair_comm (w.val none) v, c3t_pair_comm rhs v]
  linear_combination h

/-- The literal transpose weak graph is the full dual graph for the bilinear dx pairing. -/
theorem physical_complex_transpose_generator_iff_dual
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    IsPhysicalComplexTransposeGeneratorPair a i ζ f g ↔
      ∀ u v : Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexGeneratorPair a i ζ u v →
          (∫ x : Vec d, v x * f x) = ∫ x : Vec d, u x * g x := by
  constructor
  · intro hf u v huv
    exact physical_complex_generator_bilinear huv hf
  · intro hdual
    let s : ℝ := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + 1
    have hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s := lt_add_one _
    let rhs := (s : ℂ) • f - g
    let w := c3t_transposeResolvent a ha hΛ hA i ζ s hs rhs
    have hw (u : c3t_physicalGraph d) :
        c3t_bilinear a ha i ζ s u w = c3t_pair (u.val none) rhs :=
      c3t_transpose_spec a ha hΛ hA i ζ s hs rhs u
    have hfw : f = w.val none := by
      apply ext_inner_left ℂ
      intro z
      let q := star z
      let u := c3t_physicalGraphResolvent a ha hΛ hA i ζ s hs q
      have hg := c3t_physicalGraphResolvent_generator a ha hΛ hA i ζ s hs q
      have hd := hdual (u.val none) ((s : ℂ) • u.val none - q) hg
      change c3t_pair ((s : ℂ) • u.val none - q) f = c3t_pair (u.val none) g at hd
      rw [c3t_pair_smul_sub] at hd
      have hr : c3t_pair (u.val none) rhs =
          (s : ℂ) * c3t_pair (u.val none) f - c3t_pair (u.val none) g := by
        rw [c3t_pair_comm, c3t_pair_smul_sub, c3t_pair_comm f, c3t_pair_comm g]
      have he := c3t_forward_spec a ha hΛ hA i ζ s hs q w
      have hq : c3t_pair q f = c3t_pair q (w.val none) := by
        rw [← he, hw, hr]
        linear_combination -hd
      have hzf : inner ℂ z f = c3t_pair q f := by
        simpa only [q, star_star, c3t_pair] using c3t_physical_inner_star q f
      have hzw : inner ℂ z (w.val none) = c3t_pair q (w.val none) := by
        simpa only [q, star_star, c3t_pair] using c3t_physical_inner_star q (w.val none)
      exact hzf.trans (hq.trans hzw.symm)
    have hgraph := c3t_transpose_generator a ha i ζ s rhs w hw
    rw [← hfw] at hgraph
    have he : (s : ℂ) • f - rhs = g := by
      dsimp [rhs]
      abel
    rwa [he] at hgraph

end EinsteinFull.Blueprint
