import EinsteinRelation.Clock.HeatCubeMasses
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Continuous

/-!
# Heat-kernel decomposition over the cubes of a partition

For a measurable environment function `f` with `|f| ≤ B`, the heat-kernel average `H_t f`
splits over the cubes `heatCube L z` of the partition from `HeatCubeMasses`. The piece of the
cube `z` is `heatCubePiece L t f z`. The pieces sum to `H_t f`, each piece is bounded by `B`
times the mass of its cube, and each piece has zero mean under a stationary law when `f` has
zero mean. Cubes whose indices agree modulo `N` in every coordinate, and which are distinct,
are at least `(N - 1) L` apart. This is the colouring of the clock spatial averages
(`paper/main.tex:1155-1161`).
-/

open MeasureTheory
open EinsteinRelation.Correctors (euclideanHeatKernel heatSmoothed)

namespace EinsteinRelation.Clock

/-! ### Continuity of translation on coefficient pairs -/

/-- Translation by `x` as a continuous self-map of the coordinate space. -/
private def heatShift {d : ℕ} (x : Vec d) : C(Vec d, Vec d) :=
  ⟨fun y => x + y, continuous_const.add continuous_id⟩

private lemma continuous_heatShift {d : ℕ} : Continuous fun x : Vec d => heatShift x := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  show Continuous fun p : Vec d × Vec d => p.1 + p.2
  exact continuous_fst.add continuous_snd

private lemma translate_eq_comp_heatShift {d : ℕ} (x : Vec d) (ω : FieldPair d) :
    translate x ω = (ω.1.comp (heatShift x), ω.2.comp (heatShift x)) :=
  rfl

/-- Translation of a coefficient pair is jointly continuous in the shift and the pair. -/
private lemma continuous_translate_joint {d : ℕ} :
    Continuous fun p : Vec d × FieldPair d => translate p.1 p.2 := by
  have hx : Continuous fun p : Vec d × FieldPair d => heatShift p.1 :=
    continuous_heatShift.comp continuous_fst
  have h1 : Continuous fun p : Vec d × FieldPair d => p.2.1.comp (heatShift p.1) :=
    ContinuousMap.continuous_comp'.comp (hx.prodMk continuous_snd.fst)
  have h2 : Continuous fun p : Vec d × FieldPair d => p.2.2.comp (heatShift p.1) :=
    ContinuousMap.continuous_comp'.comp (hx.prodMk continuous_snd.snd)
  exact (h1.prodMk h2).congr fun p => (translate_eq_comp_heatShift p.1 p.2).symm

private lemma continuous_translate_shift {d : ℕ} (ω : FieldPair d) :
    Continuous fun x : Vec d => translate x ω := by
  have h : Continuous fun x : Vec d => (x, ω) := continuous_id.prodMk continuous_const
  exact (continuous_translate_joint (d := d)).comp h

private lemma continuous_translate_pair {d : ℕ} (x : Vec d) :
    Continuous fun ω : FieldPair d => translate x ω := by
  have h : Continuous fun ω : FieldPair d => (x, ω) := continuous_const.prodMk continuous_id
  exact (continuous_translate_joint (d := d)).comp h

private lemma measurable_translate_joint {d : ℕ} :
    Measurable fun p : Vec d × FieldPair d => translate p.1 p.2 :=
  (continuous_translate_joint (d := d)).measurable

/-! ### The heat kernel: continuity -/

private lemma continuous_euclideanSq {d : ℕ} : Continuous fun x : Vec d => euclideanSq x := by
  unfold euclideanSq dot
  exact continuous_finset_sum Finset.univ fun i _ =>
    (continuous_apply i).mul (continuous_apply i)

private lemma continuous_euclideanHeatKernel {d : ℕ} (t : ℝ) :
    Continuous fun x : Vec d => euclideanHeatKernel t x := by
  unfold euclideanHeatKernel
  exact continuous_const.mul
    (Real.continuous_exp.comp ((continuous_euclideanSq (d := d)).neg.div_const (4 * t)))

/-! ### The cube pieces -/

/-- The contribution of the cube `heatCube L z` to the heat-kernel average of `f` at `ω`. -/
noncomputable def heatCubePiece {d : ℕ} (L t : ℝ) (f : FieldPair d → ℝ) (z : Fin d → ℤ)
    (ω : FieldPair d) : ℝ :=
  ∫ x in heatCube L z, euclideanHeatKernel t x * f (translate x ω)

/-- The kernel-weighted integrand is dominated by the kernel times the bound `B`. -/
private lemma norm_kernel_mul_translate_le {d : ℕ} {t B : ℝ} (ht : 0 < t)
    {f : FieldPair d → ℝ} (hfB : ∀ ω, |f ω| ≤ B) (ω : FieldPair d) (x : Vec d) :
    ‖euclideanHeatKernel t x * f (translate x ω)‖ ≤ euclideanHeatKernel t x * B := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg ht x)]
  exact mul_le_mul_of_nonneg_left (hfB _) (euclideanHeatKernel_nonneg ht x)

private lemma measurable_kernel_mul_translate {d : ℕ} {t : ℝ} {f : FieldPair d → ℝ}
    (hf : Measurable f) (ω : FieldPair d) :
    Measurable fun x : Vec d => euclideanHeatKernel t x * f (translate x ω) :=
  (continuous_euclideanHeatKernel t).measurable.mul
    (hf.comp (continuous_translate_shift ω).measurable)

/-- The kernel-weighted translated field is integrable on `Vec d`. -/
private lemma integrable_kernel_mul_translate {d : ℕ} {t B : ℝ} (ht : 0 < t)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfB : ∀ ω, |f ω| ≤ B) (ω : FieldPair d) :
    Integrable (fun x : Vec d => euclideanHeatKernel t x * f (translate x ω)) volume :=
  Integrable.mono' ((integrable_euclideanHeatKernel (d := d) ht).mul_const B)
    (measurable_kernel_mul_translate (t := t) hf ω).aestronglyMeasurable
    (ae_of_all _ fun x => norm_kernel_mul_translate_le ht hfB ω x)

/-- The kernel-weighted translated field is integrable on the product of a probability law
with the Lebesgue measure restricted to a set. -/
private lemma integrable_translate_prod {d : ℕ} {t B : ℝ} (ht : 0 < t)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfB : ∀ ω, |f ω| ≤ B)
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (S : Set (Vec d)) :
    Integrable (Function.uncurry fun (ω : FieldPair d) (x : Vec d) =>
      euclideanHeatKernel t x * f (translate x ω)) (Q.prod (volume.restrict S)) := by
  have hK : Integrable (fun x : Vec d => euclideanHeatKernel t x * B) (volume.restrict S) :=
    ((integrable_euclideanHeatKernel (d := d) ht).mul_const B).restrict
  have hbound : Integrable (fun p : FieldPair d × Vec d => euclideanHeatKernel t p.2 * B)
      (Q.prod (volume.restrict S)) :=
    hK.comp_snd Q
  have hmeas : Measurable (fun p : FieldPair d × Vec d =>
      euclideanHeatKernel t p.2 * f (translate p.2 p.1)) :=
    ((continuous_euclideanHeatKernel t).measurable.comp measurable_snd).mul
      (hf.comp ((measurable_translate_joint (d := d)).comp measurable_swap))
  exact Integrable.mono' hbound hmeas.aestronglyMeasurable
    (ae_of_all _ fun p => norm_kernel_mul_translate_le ht hfB p.1 p.2)

/-- The cube pieces sum to the heat-kernel average `H_t f(ω)`, for every environment `ω`. -/
theorem hasSum_heatCubePiece {d : ℕ} {L t B : ℝ} (hL : 0 < L) (ht : 0 < t)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfB : ∀ ω, |f ω| ≤ B) :
    ∀ ω : FieldPair d, HasSum (fun z => heatCubePiece L t f z ω) (heatSmoothed t f ω) := by
  intro ω
  have hint : IntegrableOn (fun x : Vec d => euclideanHeatKernel t x * f (translate x ω))
      (⋃ z : Fin d → ℤ, heatCube L z) volume :=
    (integrable_kernel_mul_translate ht hf hfB ω).integrableOn
  have h := hasSum_integral_iUnion (fun z : Fin d → ℤ => measurableSet_heatCube L z)
    (pairwise_disjoint_heatCube hL) hint
  rw [iUnion_heatCube hL, Measure.restrict_univ] at h
  have hsm : heatSmoothed t f ω = ∫ x : Vec d, euclideanHeatKernel t x * f (translate x ω) := by
    unfold heatSmoothed
    rw [if_neg ht.ne']
  rw [hsm]
  exact h

/-- Each cube piece is bounded by `B` times the mass of its cube. -/
theorem abs_heatCubePiece_le {d : ℕ} {L t B : ℝ} (ht : 0 < t) {f : FieldPair d → ℝ}
    (hfB : ∀ ω, |f ω| ≤ B) (z : Fin d → ℤ) (ω : FieldPair d) :
    |heatCubePiece L t f z ω| ≤ B * heatCubeMass L t z := by
  have hg : Integrable (fun x : Vec d => euclideanHeatKernel t x * B)
      (volume.restrict (heatCube L z)) :=
    ((integrable_euclideanHeatKernel (d := d) ht).mul_const B).restrict
  have hpt : ∀ᵐ x ∂(volume.restrict (heatCube L z)),
      ‖euclideanHeatKernel t x * f (translate x ω)‖ ≤ euclideanHeatKernel t x * B :=
    ae_of_all _ fun x => norm_kernel_mul_translate_le ht hfB ω x
  have hle := norm_integral_le_of_norm_le hg hpt
  rw [integral_mul_const, Real.norm_eq_abs] at hle
  unfold heatCubePiece heatCubeMass
  rw [mul_comm B]
  exact hle

/-- Translating a stationary law by a fixed vector keeps the mean of `f` at zero. -/
private lemma integral_translate_eq_zero {d : ℕ} {f : FieldPair d → ℝ} (hf : Measurable f)
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (hmean : ∫ ω, f ω ∂Q = 0) (x : Vec d) :
    ∫ ω, f (translate x ω) ∂Q = 0 := by
  have hφ : AEMeasurable (translate x) Q :=
    (continuous_translate_pair x).measurable.aemeasurable
  have hmap : ∫ y, f y ∂(Measure.map (translate x) Q) = ∫ ω, f (translate x ω) ∂Q :=
    integral_map hφ hf.aestronglyMeasurable
  rw [hQ x] at hmap
  exact hmap.symm.trans hmean

/-- Under a stationary law with zero mean for `f`, each cube piece has zero mean. -/
theorem integral_heatCubePiece_eq_zero {d : ℕ} {L t B : ℝ} (ht : 0 < t)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfB : ∀ ω, |f ω| ≤ B)
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (hmean : ∫ ω, f ω ∂Q = 0) (z : Fin d → ℤ) :
    ∫ ω, heatCubePiece L t f z ω ∂Q = 0 := by
  have hzero : ∀ x : Vec d, ∫ ω, euclideanHeatKernel t x * f (translate x ω) ∂Q = 0 := by
    intro x
    rw [integral_const_mul, integral_translate_eq_zero hf hQ hmean x, mul_zero]
  unfold heatCubePiece
  rw [integral_integral_swap (integrable_translate_prod ht hf hfB Q (heatCube L z))]
  simp only [hzero, integral_zero]

/-- The squared cube pieces are summable, with sum at most `B ^ 2 * C * (1 + t) ^ (-d/2)`. -/
theorem summable_sq_heatCubePiece_bound {d : ℕ} {L C : ℝ} (hL : 0 < L)
    (hC : ∀ t : ℝ, 0 < t → ∀ z : Fin d → ℤ, heatCubeMass L t z ≤ C * (1 + t) ^ (-(d : ℝ) / 2))
    (B : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun z : Fin d → ℤ => (B * heatCubeMass L t z) ^ 2) ∧
      ∑' z : Fin d → ℤ, (B * heatCubeMass L t z) ^ 2 ≤ B ^ 2 * C * (1 + t) ^ (-(d : ℝ) / 2) := by
  obtain ⟨hsum, hle⟩ := tsum_sq_heatCubeMass_le hL hC ht
  simp only [mul_pow]
  refine ⟨hsum.mul_left (B ^ 2), ?_⟩
  rw [tsum_mul_left, mul_assoc]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg B)

/-- A uniform constant bounding the squared cube pieces for every `t > 0`. -/
theorem exists_summable_sq_heatCubePiece_bound {d : ℕ} {L : ℝ} (hL : 0 < L) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Summable (fun z : Fin d → ℤ => (B * heatCubeMass L t z) ^ 2) ∧
        ∑' z : Fin d → ℤ, (B * heatCubeMass L t z) ^ 2 ≤ B ^ 2 * C * (1 + t) ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_heatCubeMass_le (d := d) hL
  exact ⟨C, hC0, fun t ht => summable_sq_heatCubePiece_bound hL hC B ht⟩

/-! ### Colouring of the cubes -/

/-- The residues modulo `N` of the coordinates of a cube index. -/
def heatCubeColour {d : ℕ} (N : ℕ) (z : Fin d → ℤ) : Fin d → ZMod N :=
  fun i => (z i : ZMod N)

/-- Distinct integers with equal residues modulo `N` differ by at least `N` in one order. -/
private lemma le_sub_of_intCast_zmod_eq {N : ℕ} {a b : ℤ} (hab : a ≠ b)
    (h : (a : ZMod N) = (b : ZMod N)) : (N : ℤ) ≤ a - b ∨ (N : ℤ) ≤ b - a := by
  have hdvd : (N : ℤ) ∣ b - a := (ZMod.intCast_eq_intCast_iff_dvd_sub a b N).mp h
  have hpos : 0 < |b - a| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hab))
  have hle : (N : ℤ) ≤ |b - a| := Int.le_of_dvd hpos ((dvd_abs _ _).mpr hdvd)
  by_cases hsign : 0 ≤ b - a
  · rw [abs_of_nonneg hsign] at hle
    exact Or.inr hle
  · rw [abs_of_neg (not_le.mp hsign)] at hle
    exact Or.inl (by linarith)

/-- A coordinate of a vector is bounded in absolute value by its Euclidean norm. -/
private lemma abs_apply_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm
  refine Real.abs_le_sqrt ?_
  unfold euclideanSq dot
  rw [sq]
  exact Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)

/-- Distinct cubes whose indices have equal residues modulo `N` are at distance at least
`(N - 1) L`: every point of the first cube is that far from every point of the second. -/
theorem heatCube_dist_of_same_colour {d : ℕ} {L : ℝ} (hL : 0 < L) (N : ℕ) {z w : Fin d → ℤ}
    (hzw : z ≠ w) (hcol : heatCubeColour N z = heatCubeColour N w) :
    ∀ x ∈ heatCube L z, ∀ y ∈ heatCube L w, ((N : ℝ) - 1) * L ≤ euclideanNorm (x - y) := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ w i := by
    by_contra hcon
    push_neg at hcon
    exact hzw (funext hcon)
  have hmod : (z i : ZMod N) = (w i : ZMod N) := congrFun hcol i
  have hsep := le_sub_of_intCast_zmod_eq hi hmod
  intro x hx y hy
  have hxz : ∀ j, L * (z j : ℝ) ≤ x j ∧ x j < L * ((z j : ℝ) + 1) := hx
  have hyw : ∀ j, L * (w j : ℝ) ≤ y j ∧ y j < L * ((w j : ℝ) + 1) := hy
  have hcoord : ((N : ℝ) - 1) * L ≤ |x i - y i| := by
    rcases hsep with h | h
    · have hR : (N : ℝ) ≤ (z i : ℝ) - (w i : ℝ) := by exact_mod_cast h
      have hmul : L * (N : ℝ) ≤ L * ((z i : ℝ) - (w i : ℝ)) :=
        mul_le_mul_of_nonneg_left hR hL.le
      have hlow : ((N : ℝ) - 1) * L ≤ x i - y i := by
        linarith [(hxz i).1, (hyw i).2]
      exact le_trans hlow (le_abs_self _)
    · have hR : (N : ℝ) ≤ (w i : ℝ) - (z i : ℝ) := by exact_mod_cast h
      have hmul : L * (N : ℝ) ≤ L * ((w i : ℝ) - (z i : ℝ)) :=
        mul_le_mul_of_nonneg_left hR hL.le
      have hlow : ((N : ℝ) - 1) * L ≤ -(x i - y i) := by
        linarith [(hxz i).2, (hyw i).1]
      exact le_trans hlow (neg_le_abs _)
  exact le_trans hcoord (abs_apply_le_euclideanNorm (x - y) i)

end EinsteinRelation.Clock
