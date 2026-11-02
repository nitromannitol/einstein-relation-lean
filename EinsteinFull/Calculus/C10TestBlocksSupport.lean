import EinsteinFull.Calculus.S1RecursionInstantiate
import EinsteinFull.Calculus.C10BlockSupport
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import EinsteinFull.Calculus.SchwartzNormSupport
import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects

/-! Countable lattice block independence for the literal test-block construction. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinFull.Calculus.C10TestBlocks
open EinsteinFull EinsteinRelation EinsteinFull.Blueprint EinsteinFull.Calculus.S1

/-- Distinct lattice centers differ by at least one mesh width in a coordinate. -/
theorem tileCenter_separated {d : ℕ} {L : ℝ} (hL : 0 ≤ L)
    {j k : Fin d → ℤ} (hjk : j ≠ k) :
    ∃ i, L ≤ |covarianceTileCenter L j i - covarianceTileCenter L k i| := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hjk
  refine ⟨i, ?_⟩
  have hz : (1 : ℤ) ≤ |j i - k i| := by
    have hn : j i - k i ≠ 0 := sub_ne_zero.mpr hi
    have hp := abs_pos.mpr hn
    omega
  have hr : (1 : ℝ) ≤ |(j i : ℝ) - (k i : ℝ)| := by exact_mod_cast hz
  simpa only [covarianceTileCenter, ← mul_sub, abs_mul, abs_of_nonneg hL, mul_one]
    using mul_le_mul_of_nonneg_left hr hL

/-- Joint independence of the entire lattice family, using local representatives
of every coordinate and the full joint coefficient sigma algebras. -/
theorem lattice_blocks_iIndepFun {d : ℕ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {V : Vec d → Set (Vec d)} {F : ι → Vec d → FieldPair d → ℝ}
    {r₀ ρ L side : ℝ} (hfr : HasFiniteRange r₀ μ)
    (hV : ∀ y z, z ∈ V y → euclideanNorm (z - y) < ρ)
    (h : ∀ a, LocalStationaryField μ V (F a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (n : ℝ)
    (hL : 0 ≤ L) (hs : r₀ < L - side - 2 * ρ) :
    iIndepFun (fun (j : Fin d → ℤ) ω a =>
      n * ∫ y in clockBlockCube (covarianceTileCenter L j) side, F a y ω) μ := by
  classical
  let U : (Fin d → ℤ) → Set (Vec d) :=
    fun j => clockBlockCube (covarianceTileCenter L j) (side + 2 * ρ)
  have hU : ∀ j, MeasurableSet (U j) := fun j => measurableSet_clockBlockCube _ _
  have hsep : ∀ j k, j ≠ k → ∀ x ∈ U j, ∀ y ∈ U k,
      L - side - 2 * ρ ≤ euclideanNorm (x - y) := by
    intro j k hjk x hx y hy
    obtain ⟨i, hi⟩ := tileCenter_separated hL hjk
    have hx' := (mem_clockBlockCube_iff.mp hx) i
    have hy' := (mem_clockBlockCube_iff.mp hy) i
    have hc := abs_coord_le_euclideanNorm (x - y) i
    apply le_trans _ hc
    rw [Pi.sub_apply]
    rcases le_or_gt (covarianceTileCenter L j i) (covarianceTileCenter L k i) with hle | hgt
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hi
      exact (by linarith : L - side - 2 * ρ ≤ -(x i - y i)).trans (neg_le_abs _)
    · rw [abs_of_nonneg (sub_nonneg.mpr hgt.le)] at hi
      exact (by linarith : L - side - 2 * ρ ≤ x i - y i).trans (le_abs_self _)
  have hloc : ∀ (a : ι) (j : Fin d → ℤ), ∃ H : FieldPair d → ℝ,
      StronglyMeasurable[localSigma (U j)] H ∧
        (fun ω => ∫ y in clockBlockCube (covarianceTileCenter L j) side, F a y ω) =ᵐ[μ] H := by
    intro a j
    refine (h a).block_local hT (measurableSet_clockBlockCube _ _)
      (volume_clockBlockCube_lt_top _ _) (U := U j) ?_
    intro y hy z hz
    have hz' := hV y z hz
    rw [mem_clockBlockCube_iff] at hy
    change z ∈ clockBlockCube (covarianceTileCenter L j) (side + 2 * ρ)
    rw [mem_clockBlockCube_iff]
    intro i
    have hcoord := abs_coord_le_euclideanNorm (z - y) i
    have hdiff := abs_lt.1 (lt_of_le_of_lt hcoord hz')
    have hcube := hy i
    simp only [Pi.sub_apply] at hdiff
    exact ⟨by linarith [hdiff.1, hcube.1], by linarith [hdiff.2, hcube.2]⟩
  choose H hHm hH using hloc
  refine iIndepFun_of_local hfr U hU hs hsep (g := fun j ω a => n * H a j ω) ?_ ?_
  · intro j
    letI : MeasurableSpace (FieldPair d) := localSigma (U j)
    exact measurable_pi_iff.2 fun a =>
      (measurable_const.mul measurable_id).comp (hHm a j).measurable
  · intro j
    have hall : ∀ᵐ ω ∂μ, ∀ a,
        ∫ y in clockBlockCube (covarianceTileCenter L j) side, F a y ω = H a j ω :=
      ae_all_iff.2 fun a => hH a j
    filter_upwards [hall] with ω hω
    funext a
    simp only [hω a]

/-- A product of nonnegative summable one-dimensional lattice weights is
summable over the full integer lattice, including dimension zero. -/
theorem summable_lattice_product (d : ℕ) (u : ℤ → ℝ)
    (hu : Summable u) (hu0 : ∀ n, 0 ≤ u n) :
    Summable (fun j : Fin d → ℤ => ∏ i, u (j i)) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
    have hp := hu.mul_of_nonneg ih hu0 (fun j => Finset.prod_nonneg fun _ _ => hu0 _)
    apply (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff.1
    change Summable (fun p : ℤ × (Fin d → ℤ) => ∏ i, u (Fin.cons (α := fun _ : Fin (d + 1) => ℤ) p.1 p.2 i))
    simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using hp

/-- Tensor factorization of the nonnegative lattice weight preserves the
exact one-dimensional mass in every dimension. -/
theorem tsum_lattice_product (d : ℕ) (u : ℤ → ℝ)
    (hu : Summable u) (hu0 : ∀ n, 0 ≤ u n) :
    (∑' j : Fin d → ℤ, ∏ i, u (j i)) = (∑' n : ℤ, u n) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hs := summable_lattice_product d u hu hu0
    have hp := hu.mul_of_nonneg hs hu0 (fun j => Finset.prod_nonneg fun _ _ => hu0 _)
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).tsum_eq]
    change (∑' p : ℤ × (Fin d → ℤ),
      ∏ i, u (Fin.cons (α := fun _ : Fin (d + 1) => ℤ) p.1 p.2 i)) = _
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [← hu.tsum_mul_tsum hs hp, ih, pow_succ, mul_comm]

/-- Inverse-square decay remains summable on a one-dimensional lattice at
every positive mesh width. -/
theorem summable_lattice_inverse_square {a : ℝ} (ha : 0 < a) :
    Summable (fun j : ℤ => ((1 + a * |(j : ℝ)|) ^ 2)⁻¹) := by
  have hn : Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
      (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2))
  have hz : Summable (fun j : ℤ => ((1 + |(j : ℝ)|) ^ 2)⁻¹) := by
    apply Summable.of_nat_of_neg
    · simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hn
    · simpa only [Int.cast_neg, abs_neg, Int.cast_natCast,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hn
  let C := 1 + a⁻¹
  have hC : 1 ≤ C := le_add_of_nonneg_right (inv_nonneg.mpr ha.le)
  have hCa : 1 ≤ C * a := by dsimp [C]; rw [add_mul, inv_mul_cancel₀ ha.ne']; linarith
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (hz.mul_left (C ^ 2))
  have hlin : 1 + |(j : ℝ)| ≤ C * (1 + a * |(j : ℝ)|) := by
    nlinarith [mul_le_mul_of_nonneg_right hCa (abs_nonneg (j : ℝ))]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |(j : ℝ)|) hlin 2
  rw [mul_pow] at hsq
  apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < (1 + a * |(j : ℝ)|) ^ 2)).2
  rw [mul_right_comm, ← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0 < (1 + |(j : ℝ)|) ^ 2)).2
    (by simpa only [one_mul] using hsq)

/-- The positive half-lattice inverse-square tail is bounded by a telescoping
inverse-linear sequence, with the sharp inverse-mesh scaling. -/
theorem tsum_nat_inverse_square_tail_le {a : ℝ} (ha : 0 < a) :
    ∑' n : ℕ, ((1 + a * (n + 1 : ℕ)) ^ 2)⁻¹ ≤ a⁻¹ := by
  have hstep (n : ℕ) :
      ((1 + a * (n + 1 : ℕ)) ^ 2)⁻¹ ≤
        a⁻¹ * ((1 + a * (n : ℝ))⁻¹ - (1 + a * (n + 1 : ℕ))⁻¹) := by
    have hx : 0 < 1 + a * (n : ℝ) := by positivity
    have hy : 0 < 1 + a * (n + 1 : ℕ) := by positivity
    rw [Nat.cast_add, Nat.cast_one] at hy ⊢
    field_simp
    nlinarith
  have hpartial (m : ℕ) :
      ∑ n ∈ Finset.range m, ((1 + a * (n + 1 : ℕ)) ^ 2)⁻¹ ≤
        a⁻¹ * (1 - (1 + a * (m : ℝ))⁻¹) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hh := hstep m
      push_cast
      push_cast at ih hh
      nlinarith only [ih, hh]
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro m
  exact (hpartial m).trans (by
    have hi : 0 ≤ (1 + a * (m : ℝ))⁻¹ := by positivity
    nlinarith [inv_nonneg.mpr ha.le])

/-- The whole one-dimensional lattice has inverse-square mass of order
one over the mesh width. -/
theorem tsum_lattice_inverse_square_le {a : ℝ} (ha : 0 < a) :
    ∑' j : ℤ, ((1 + a * |(j : ℝ)|) ^ 2)⁻¹ ≤ 1 + 2 * a⁻¹ := by
  have hpos (n : ℕ) : |((n : ℤ) : ℝ)| = (n : ℝ) := by
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  have hneg (n : ℕ) : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  have hn : Summable (fun n : ℕ => ((1 + a * (n : ℝ)) ^ 2)⁻¹) := by
    have hh := (summable_lattice_inverse_square ha).comp_injective
      (show Function.Injective (fun n : ℕ => (n : ℤ)) from fun _ _ => Int.ofNat_inj.mp)
    simpa only [Function.comp_def, hpos] using hh
  have ht := (summable_nat_add_iff 1).2 hn
  have he := tsum_of_nat_of_neg_add_one (f := fun j : ℤ =>
    ((1 + a * |(j : ℝ)|) ^ 2)⁻¹)
    (by simpa only [hpos] using hn)
    (by simpa only [hneg] using ht)
  simp only [hpos, hneg] at he
  rw [he, hn.tsum_eq_zero_add]
  have hb := tsum_nat_inverse_square_tail_le ha
  norm_num only [Nat.cast_zero, mul_zero, add_zero, one_pow, inv_one]
  linarith

/-- Euclidean decay dominates a tensor product of inverse-square coordinate
weights without changing the ambient Euclidean norm. -/
theorem lattice_euclidean_decay_le_product {d N : ℕ} {a : ℝ}
    (ha : 0 < a) (hN : 2 * d ≤ N) (j : Fin d → ℤ) :
    ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹ ≤
      ∏ i, ((1 + a * |(j i : ℝ)|) ^ 2)⁻¹ := by
  have hb : 1 ≤ 1 + euclideanNorm (covarianceTileCenter a j) := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hp : 0 < ∏ i, (1 + a * |(j i : ℝ)|) ^ 2 :=
    Finset.prod_pos fun i _ => by positivity
  rw [Finset.prod_inv_distrib]
  apply (inv_le_inv₀ (by unfold euclideanNorm; positivity) hp).2
  calc
    _ ≤ ∏ _ : Fin d, (1 + euclideanNorm (covarianceTileCenter a j)) ^ 2 := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro i _
      apply pow_le_pow_left₀ (by positivity)
      have hc := abs_coord_le_euclideanNorm (covarianceTileCenter a j) i
      simpa only [covarianceTileCenter, abs_mul, abs_of_pos ha, add_le_add_iff_left]
        using hc
    _ = (1 + euclideanNorm (covarianceTileCenter a j)) ^ (2 * d) := by
      rw [Finset.prod_const, Finset.card_fin, ← pow_mul]
    _ ≤ _ := pow_le_pow_right₀ hb hN

/-- Euclidean polynomial decay of order at least twice the dimension is
summable on every positively scaled lattice. -/
theorem summable_lattice_euclidean_decay {d N : ℕ} {a : ℝ}
    (ha : 0 < a) (hN : 2 * d ≤ N) :
    Summable (fun j : Fin d → ℤ =>
      ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) := by
  have hs := summable_lattice_product d _ (summable_lattice_inverse_square ha)
    (fun j => by positivity)
  refine Summable.of_nonneg_of_le (fun j => by unfold euclideanNorm; positivity)
    (fun j => ?_) hs
  exact lattice_euclidean_decay_le_product ha hN j

/-- The mesh-volume-normalized Euclidean decay sum is uniformly bounded
for every positive mesh at most one. -/
theorem mesh_tsum_lattice_euclidean_decay_le {d N : ℕ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hN : 2 * d ≤ N) :
    a ^ d * (∑' j : Fin d → ℤ,
      ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) ≤ 3 ^ d := by
  have hs := summable_lattice_euclidean_decay ha hN
  have hp := summable_lattice_product d _ (summable_lattice_inverse_square ha)
    (fun j => by positivity)
  have ht := hs.tsum_le_tsum (lattice_euclidean_decay_le_product ha hN) hp
  rw [tsum_lattice_product d _ (summable_lattice_inverse_square ha)
    (fun j => by positivity)] at ht
  calc
    _ ≤ a ^ d * (∑' j : ℤ, ((1 + a * |(j : ℝ)|) ^ 2)⁻¹) ^ d :=
      mul_le_mul_of_nonneg_left ht (pow_nonneg ha.le _)
    _ ≤ a ^ d * (1 + 2 * a⁻¹) ^ d := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha.le _)
      exact pow_le_pow_left₀ (tsum_nonneg fun j => by positivity)
        (tsum_lattice_inverse_square_le ha) _
    _ = (a + 2) ^ d := by
      rw [← mul_pow]
      congr 1
      field_simp
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) _

/-- The original order-N Schwartz test norm controls lattice absolute
summability whenever N is at least twice the spatial dimension. -/
theorem summable_schwartz_lattice_norm {d N : ℕ} {a : ℝ}
    (ha : 0 < a) (hN : 2 * d ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Summable (fun j : Fin d → ℤ => ‖F (covarianceTileCenter a j)‖) := by
  have hs := (summable_lattice_euclidean_decay ha hN).mul_left (schwartzTestNorm N F)
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hs
  have hw : (1 + euclideanNorm (covarianceTileCenter a j)) ^ N *
      ‖F (covarianceTileCenter a j)‖ ≤ schwartzTestNorm N F := by
    apply le_csSup (schwartzTestNorm_set_bddAbove N F)
    exact ⟨⟨0, by omega⟩, Fin.elim0, covarianceTileCenter a j,
      by simp only [iteratedFDeriv_zero_apply]⟩
  have hp : 0 < (1 + euclideanNorm (covarianceTileCenter a j)) ^ N := by
    unfold euclideanNorm; positivity
  exact (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hw)

/-- Squared Schwartz values admit the Euclidean decay majorant at twice
the original order; this uses only the order-N value bound. -/
theorem schwartz_lattice_norm_sq_le {d N : ℕ} (a : ℝ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (j : Fin d → ℤ) :
    ‖F (covarianceTileCenter a j)‖ ^ 2 ≤ schwartzTestNorm N F ^ 2 *
      ((1 + euclideanNorm (covarianceTileCenter a j)) ^ (2 * N))⁻¹ := by
  have hw : (1 + euclideanNorm (covarianceTileCenter a j)) ^ N *
      ‖F (covarianceTileCenter a j)‖ ≤ schwartzTestNorm N F := by
    apply le_csSup (schwartzTestNorm_set_bddAbove N F)
    exact ⟨⟨0, by omega⟩, Fin.elim0, covarianceTileCenter a j,
      by simp only [iteratedFDeriv_zero_apply]⟩
  have hp : 0 < 1 + euclideanNorm (covarianceTileCenter a j) := by
    unfold euclideanNorm; positivity
  have hsq := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hp.le _) (norm_nonneg _)) hw 2
  rw [mul_pow, ← pow_mul] at hsq
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hp _)).2 (by simpa only [Nat.mul_comm, mul_comm] using hsq)

/-- Squared Schwartz values are summable whenever the original order is at
least the spatial dimension. -/
theorem summable_schwartz_lattice_norm_sq {d N : ℕ} {a : ℝ}
    (ha : 0 < a) (hN : d ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Summable (fun j : Fin d → ℤ => ‖F (covarianceTileCenter a j)‖ ^ 2) := by
  exact Summable.of_nonneg_of_le (fun j => sq_nonneg _)
    (schwartz_lattice_norm_sq_le a F)
    ((summable_lattice_euclidean_decay ha (Nat.mul_le_mul_left 2 hN)).mul_left _)

/-- The mesh-volume-normalized square sum is controlled by the original
Schwartz norm, uniformly over every positive mesh at most one. -/
theorem mesh_tsum_schwartz_lattice_norm_sq_le {d N : ℕ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hN : d ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    a ^ d * (∑' j : Fin d → ℤ, ‖F (covarianceTileCenter a j)‖ ^ 2) ≤
      3 ^ d * schwartzTestNorm N F ^ 2 := by
  have hs := summable_schwartz_lattice_norm_sq ha hN F
  have hd := summable_lattice_euclidean_decay ha (Nat.mul_le_mul_left 2 hN)
  have ht := hs.tsum_le_tsum (schwartz_lattice_norm_sq_le a F)
    (hd.mul_left (schwartzTestNorm N F ^ 2))
  rw [hd.tsum_mul_left] at ht
  calc
    _ ≤ a ^ d * (schwartzTestNorm N F ^ 2 *
        ∑' j : Fin d → ℤ, ((1 + euclideanNorm (covarianceTileCenter a j)) ^ (2 * N))⁻¹) :=
      mul_le_mul_of_nonneg_left ht (pow_nonneg ha.le _)
    _ = schwartzTestNorm N F ^ 2 * (a ^ d *
        ∑' j : Fin d → ℤ, ((1 + euclideanNorm (covarianceTileCenter a j)) ^ (2 * N))⁻¹) := by ring
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (mesh_tsum_lattice_euclidean_decay_le ha ha1 (Nat.mul_le_mul_left 2 hN))
        (sq_nonneg (schwartzTestNorm N F))

/-- The square-sum estimate in the literal rescaled coordinates of
`covarianceTestBlocks`. -/
theorem testBlocks_mesh_square_sum_le {d N : ℕ} {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hLR : L ≤ R) (hN : d ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    (L / R) ^ d * (∑' j : Fin d → ℤ,
      ‖F (R⁻¹ • covarianceTileCenter L j)‖ ^ 2) ≤
        3 ^ d * schwartzTestNorm N F ^ 2 := by
  have hx (j : Fin d → ℤ) :
      R⁻¹ • covarianceTileCenter L j = covarianceTileCenter (L / R) j := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, covarianceTileCenter, div_eq_mul_inv]
    ring
  simp_rw [hx]
  exact mesh_tsum_schwartz_lattice_norm_sq_le (div_pos hL hR)
    ((div_le_one hR).2 hLR) hN F

/-- An absolutely summable family of actual L² functions has both an a.e.
Bochner-summable pointwise series and a square-integrable literal sum. -/
theorem summable_memLp_tsum {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    {μ : Measure Ω} {f : J → Ω → ℂ} (hf : ∀ j, MemLp (f j) 2 μ)
    (hnorm : ∑' j, eLpNorm (f j) 2 μ ≠ ⊤) :
    (∀ᵐ ω ∂μ, Summable (fun j => f j ω)) ∧
      MemLp (fun ω => ∑' j, f j ω) 2 μ := by
  have ha := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2) hnorm
  refine ⟨ha.mono fun _ hω => hω.of_norm, ?_⟩
  let g : J → Lp ℂ 2 μ := fun j => (hf j).toLp (f j)
  have hg : ∑' j, ‖g j‖ₑ ≠ ⊤ := by
    simpa only [g, Lp.enorm_toLp] using hnorm
  have he := Lp.coeFn_tsum hg
  have hall : ∀ᵐ ω ∂μ, ∀ j, g j ω = f j ω :=
    ae_all_iff.2 fun j => (hf j).coeFn_toLp
  have heq : (fun ω => (∑' j, g j) ω) =ᵐ[μ] fun ω => ∑' j, f j ω := by
    filter_upwards [he, hall] with ω hω hωall
    exact hω.trans (tsum_congr hωall)
  exact (Lp.memLp (∑' j, g j)).ae_eq heq

/-- Absolute L² summability of the literal weighted finite-coordinate block
terms, with one common finite coordinate bound. -/
theorem weighted_series_eLpNorm_tsum_ne_top {Ω J ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {μ : Measure Ω} {X : J → Ω → ι → ℝ}
    (hX : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (C : ι → ℝ≥0∞) (hC : ∀ a, C a ≠ ⊤)
    (hbound : ∀ j a, eLpNorm (fun ω => X j ω a) 2 μ ≤ C a)
    (w : J → ι → ℂ) (hw : ∀ a, Summable (fun j => ‖w j a‖)) :
    (∑' j, eLpNorm (fun ω => ∑ a, w j a * (X j ω a : ℂ)) 2 μ) ≠ ⊤ := by
  classical
  have hm : ∀ j a, MemLp (fun ω => (X j ω a : ℂ)) 2 μ := fun j a => (hX j a).ofReal
  have he : ∀ j a, eLpNorm (fun ω => (X j ω a : ℂ)) 2 μ =
      eLpNorm (fun ω => X j ω a) 2 μ := fun j a =>
    eLpNorm_congr_norm_ae (hm j a).aestronglyMeasurable (hX j a).aestronglyMeasurable (.of_forall fun ω => by simp)
  refine ne_top_of_le_ne_top (b := ∑ a, (∑' j, ‖w j a‖ₑ) * C a) ?_ ?_
  · apply ENNReal.sum_ne_top.2
    intro a _
    exact ENNReal.mul_ne_top (by simpa only [ofReal_norm] using (hw a).tsum_ofReal_ne_top)
      (hC a)
  · calc
      _ ≤ ∑' j, ∑ a, ‖w j a‖ₑ * C a := by
        apply ENNReal.tsum_le_tsum
        intro j
        have hs : eLpNorm (fun ω => ∑ a, w j a * (X j ω a : ℂ)) 2 μ ≤
            ∑ a, eLpNorm (fun ω => w j a * (X j ω a : ℂ)) 2 μ := by
          simpa only [Finset.sum_fn] using
            (eLpNorm_sum_le (μ := μ) (s := Finset.univ)
              (f := fun a ω => w j a * (X j ω a : ℂ))
              (by norm_num : (1 : ℝ≥0∞) ≤ 2))
        refine hs.trans ?_
        apply Finset.sum_le_sum
        intro a _
        change eLpNorm (w j a • (fun ω => (X j ω a : ℂ))) 2 μ ≤ _
        rw [eLpNorm_const_smul, he j a]
        exact mul_le_mul_right (hbound j a) ‖w j a‖ₑ
      _ = ∑' j, ∑' a, ‖w j a‖ₑ * C a := by simp only [tsum_fintype]
      _ = ∑' a, ∑' j, ‖w j a‖ₑ * C a := ENNReal.tsum_comm
      _ = _ := by simp_rw [ENNReal.tsum_mul_right]; rw [tsum_fintype]

/-- Summable deterministic coefficients and a common finite coordinate L² bound
produce a genuine a.e. summable complex block series and its L² membership. -/
theorem weighted_series_memLp {Ω J ι : Type*} [MeasurableSpace Ω]
    [Countable J] [Fintype ι] {μ : Measure Ω} {X : J → Ω → ι → ℝ}
    (hX : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (C : ι → ℝ≥0∞) (hC : ∀ a, C a ≠ ⊤)
    (hbound : ∀ j a, eLpNorm (fun ω => X j ω a) 2 μ ≤ C a)
    (w : J → ι → ℂ) (hw : ∀ a, Summable (fun j => ‖w j a‖)) :
    (∀ᵐ ω ∂μ, Summable (fun j => ∑ a, w j a * (X j ω a : ℂ))) ∧
      MemLp (fun ω => ∑' j, ∑ a, w j a * (X j ω a : ℂ)) 2 μ := by
  apply summable_memLp_tsum
  · intro j
    exact memLp_finsetSum Finset.univ (fun a _ => ((hX j a).ofReal).const_mul (w j a))
  · exact weighted_series_eLpNorm_tsum_ne_top hX C hC hbound w hw

/-- An absolutely summable orthogonal family satisfies the infinite
Pythagorean identity for its actual sum. -/
theorem norm_tsum_sq_eq_of_pairwise_inner_zero {J E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : J → E} (hf : Summable f)
    (horth : Pairwise (fun i j => inner ℝ (f i) (f j) = 0)) :
    ‖∑' j, f j‖ ^ 2 = ∑' j, ‖f j‖ ^ 2 := by
  calc
    _ = inner ℝ (∑' j, f j) (∑' j, f j) := (real_inner_self_eq_norm_sq _).symm
    _ = ∑' i, inner ℝ (f i) (∑' j, f j) :=
      (innerSLFlip ℝ (∑' j, f j)).map_tsum hf
    _ = ∑' i, ∑' j, inner ℝ (f i) (f j) := by
      apply tsum_congr
      intro i
      exact (innerSL ℝ (f i)).map_tsum hf
    _ = _ := by
      apply tsum_congr
      intro i
      rw [tsum_eq_single i (fun j hj => horth hj.symm), real_inner_self_eq_norm_sq]

/-- Centered independent complex random variables have orthogonal genuine
L² representatives. The inner product here is used only for the L² bound. -/
theorem indepFun_inner_toLp_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hind : IndepFun f g μ) (hmean : (∫ ω, f ω ∂μ) = 0) :
    inner ℂ (hf.toLp f) (hg.toLp g) = 0 := by
  have hz : (∫ ω, g ω * (starRingEnd ℂ) (f ω) ∂μ) = 0 := by
    have he' := hind.symm.comp measurable_id (show Measurable (starRingEnd ℂ) from by fun_prop)
    have hh := he'.integral_fun_mul_eq_mul_integral
      hg.aestronglyMeasurable hf.aestronglyMeasurable.star
    simpa only [Function.comp_def, id_eq, integral_conj, hmean, map_zero, mul_zero] using hh
  rw [L2.inner_def]
  calc
    _ = ∫ ω, g ω * (starRingEnd ℂ) (f ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hωf hωg
      rw [hωf, hωg, RCLike.inner_apply]
    _ = 0 := hz

/-- The literal pointwise sum of centered independent complex L² functions
has the sum of their squared L² sizes. Absolute L² summability also certifies
the representative of the pointwise series. -/
theorem l2Size_tsum_sq_eq_of_indepFun {Ω J : Type*} [MeasurableSpace Ω]
    [Countable J] {μ : Measure Ω} {f : J → Ω → ℂ}
    (hf : ∀ j, MemLp (f j) 2 μ)
    (hnorm : ∑' j, eLpNorm (f j) 2 μ ≠ ⊤)
    (hind : Pairwise (fun i j => IndepFun (f i) (f j) μ))
    (hmean : ∀ j, (∫ ω, f j ω ∂μ) = 0) :
    l2Size μ (fun ω => ∑' j, f j ω) ^ 2 = ∑' j, l2Size μ (f j) ^ 2 := by
  let g : J → Lp ℂ 2 μ := fun j => (hf j).toLp (f j)
  have hg : ∑' j, ‖g j‖ₑ ≠ ⊤ := by
    simpa only [g, Lp.enorm_toLp] using hnorm
  have hgs : Summable g := (tsum_enorm_ne_top_iff_summable_norm.1 hg).of_norm
  letI : InnerProductSpace ℝ (Lp ℂ 2 μ) := InnerProductSpace.rclikeToReal ℂ _
  letI : Inner ℝ (Lp ℂ 2 μ) := Inner.rclikeToReal ℂ _
  have horth : Pairwise (fun i j => inner ℝ (g i) (g j) = 0) := by
    intro i j hij
    rw [real_inner_eq_re_inner ℂ]
    rw [indepFun_inner_toLp_eq_zero (hf i) (hf j) (hind hij) (hmean i)]
    rfl
  have he := Lp.coeFn_tsum hg
  have hall : ∀ᵐ ω ∂μ, ∀ j, g j ω = f j ω :=
    ae_all_iff.2 fun j => (hf j).coeFn_toLp
  have hm := (summable_memLp_tsum hf hnorm).2
  have heq : hm.toLp (fun ω => ∑' j, f j ω) = ∑' j, g j := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp, he, hall] with ω hω hωsum hωall
    exact hω.trans ((tsum_congr hωall).symm.trans hωsum.symm)
  rw [l2Size_eq_norm_toLp hm, heq, norm_tsum_sq_eq_of_pairwise_inner_zero hgs horth]
  apply tsum_congr
  intro j
  rw [l2Size_eq_norm_toLp (hf j)]

/-- Applying deterministic complex linear functionals to a centered
independent vector family preserves the exact infinite L² square identity. -/
theorem weighted_series_l2Size_sq_eq {Ω J ι : Type*} [MeasurableSpace Ω]
    [Countable J] [Fintype ι] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : J → Ω → ι → ℝ}
    (hX : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (C : ι → ℝ≥0∞) (hC : ∀ a, C a ≠ ⊤)
    (hbound : ∀ j a, eLpNorm (fun ω => X j ω a) 2 μ ≤ C a)
    (w : J → ι → ℂ) (hw : ∀ a, Summable (fun j => ‖w j a‖))
    (hind : iIndepFun X μ) (hmean : ∀ j a, (∫ ω, X j ω a ∂μ) = 0) :
    l2Size μ (fun ω => ∑' j, ∑ a, w j a * (X j ω a : ℂ)) ^ 2 =
      ∑' j, l2Size μ (fun ω => ∑ a, w j a * (X j ω a : ℂ)) ^ 2 := by
  apply l2Size_tsum_sq_eq_of_indepFun
  · intro j
    exact memLp_finsetSum Finset.univ (fun a _ => ((hX j a).ofReal).const_mul (w j a))
  · exact weighted_series_eLpNorm_tsum_ne_top hX C hC hbound w hw
  · intro i j hij
    exact (hind.indepFun hij).comp
      (show Measurable (fun v : ι → ℝ => ∑ a, w i a * (v a : ℂ)) from by fun_prop)
      (show Measurable (fun v : ι → ℝ => ∑ a, w j a * (v a : ℂ)) from by fun_prop)
  · intro j
    rw [integral_finsetSum (f := fun a ω => w j a * (X j ω a : ℂ))
      Finset.univ (fun a _ =>
      (((hX j a).ofReal).const_mul (w j a)).integrable (by norm_num))]
    apply Finset.sum_eq_zero
    intro a _
    have he : (∫ ω, (X j ω a : ℂ) ∂μ) = (((∫ ω, X j ω a ∂μ) : ℝ) : ℂ) :=
      integral_ofReal (μ := μ) (𝕜 := ℂ) (f := fun ω => X j ω a)
    rw [integral_const_mul, he, hmean j a]
    simp

/-- A complex finite-coordinate contraction is controlled by the genuine
Euclidean L² size of the real vector. The dimension factor is harmless for
the structural constant in the test-block estimate. -/
theorem l2Size_coord_contraction_sq_le {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {μ : Measure Ω} {X : Ω → ι → ℝ} (hX : L2Vec μ X)
    (w : EuclideanSpace ℂ ι) :
    l2Size μ (fun ω => ∑ a, w a * (X ω a : ℂ)) ^ 2 ≤
      ((Fintype.card ι : ℝ) * ‖w‖) ^ 2 * vl2 μ X ^ 2 := by
  let K : ℝ := (Fintype.card ι : ℝ) * ‖w‖
  have hm : MemLp (fun ω => ∑ a, w a * (X ω a : ℂ)) 2 μ :=
    memLp_finsetSum Finset.univ (fun a _ => ((hX.coord_memLp a).ofReal).const_mul (w a))
  have hp (ω : Ω) : ‖∑ a, w a * (X ω a : ℂ)‖ ≤ K * vsize (X ω) := by
    calc
      _ ≤ ∑ a, ‖w a * (X ω a : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : ι, ‖w‖ * vsize (X ω) := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
          mul_le_mul (PiLp.norm_apply_le w a) (abs_le_vsize (X ω) a)
            (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K, mul_assoc]
  change _ ≤ K ^ 2 * vl2 μ X ^ 2
  rw [l2Size, Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)]
  calc
    _ ≤ ∫ ω, (K * vsize (X ω)) ^ 2 ∂μ :=
      integral_mono hm.norm.integrable_sq (hX.size_memLp.const_mul K).integrable_sq
        (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hp ω) 2)
    _ = K ^ 2 * ∫ ω, vsize (X ω) ^ 2 ∂μ := by
      simp_rw [mul_pow]
      exact integral_const_mul _ _
    _ = _ := by rw [vl2, Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)]


/-- The square size of a centered independent weighted vector series is
bounded by its deterministic coefficient square sum. -/
theorem weighted_series_l2Size_sq_le {Ω J ι : Type*} [MeasurableSpace Ω]
    [Countable J] [Fintype ι] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : J → Ω → ι → ℝ} (hX : ∀ j, L2Vec μ (X j))
    (C : ι → ℝ≥0∞) (hC : ∀ a, C a ≠ ⊤)
    (hbound : ∀ j a, eLpNorm (fun ω => X j ω a) 2 μ ≤ C a)
    (w : J → EuclideanSpace ℂ ι)
    (hw : ∀ a, Summable (fun j => ‖w j a‖))
    (hw2 : Summable (fun j => ‖w j‖ ^ 2))
    (hind : iIndepFun X μ) (hmean : ∀ j a, (∫ ω, X j ω a ∂μ) = 0)
    {B : ℝ} (_hB : 0 ≤ B) (hsize : ∀ j, vl2 μ (X j) ≤ B) :
    l2Size μ (fun ω => ∑' j, ∑ a, w j a * (X j ω a : ℂ)) ^ 2 ≤
      (Fintype.card ι : ℝ) ^ 2 * B ^ 2 * ∑' j, ‖w j‖ ^ 2 := by
  rw [weighted_series_l2Size_sq_eq (fun j a => (hX j).coord_memLp a)
    C hC hbound (fun j a => w j a) hw hind hmean]
  have hp (j : J) :
      l2Size μ (fun ω => ∑ a, w j a * (X j ω a : ℂ)) ^ 2 ≤
        ((Fintype.card ι : ℝ) ^ 2 * B ^ 2) * ‖w j‖ ^ 2 := by
    calc
      _ ≤ ((Fintype.card ι : ℝ) * ‖w j‖) ^ 2 * vl2 μ (X j) ^ 2 :=
        l2Size_coord_contraction_sq_le (hX j) (w j)
      _ ≤ ((Fintype.card ι : ℝ) * ‖w j‖) ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.sqrt_nonneg _) (hsize j) 2) (sq_nonneg _)
      _ = _ := by ring
  have hs := hw2.mul_left ((Fintype.card ι : ℝ) ^ 2 * B ^ 2)
  have hf := Summable.of_nonneg_of_le (fun j => sq_nonneg _) hp hs
  exact (hf.tsum_le_tsum hp hs).trans_eq (tsum_mul_left)


/-- Independence and centering give the uniform mesh-normalized square bound
for the literal Schwartz-weighted block series. -/
theorem testBlocks_mesh_l2Size_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {d N : ℕ} {R L : ℝ}
    {X : (Fin d → ℤ) → Ω → JointObservationIndex d → ℝ}
    (hX : ∀ j, L2Vec μ (X j))
    (C : JointObservationIndex d → ℝ≥0∞) (hC : ∀ a, C a ≠ ⊤)
    (hbound : ∀ j a, eLpNorm (fun ω => X j ω a) 2 μ ≤ C a)
    (hind : iIndepFun X μ) (hmean : ∀ j a, (∫ ω, X j ω a ∂μ) = 0)
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ j, vl2 μ (X j) ≤ B)
    (hR : 0 < R) (hL : 0 < L) (hLR : L ≤ R) (hN : 2 * d ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    (L / R) ^ d * l2Size μ (fun ω => ∑' j : Fin d → ℤ,
      ∑ a, F (R⁻¹ • covarianceTileCenter L j) a * (X j ω a : ℂ)) ^ 2 ≤
      (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * B ^ 2 *
        3 ^ d * schwartzTestNorm N F ^ 2 := by
  have hx (j : Fin d → ℤ) :
      R⁻¹ • covarianceTileCenter L j = covarianceTileCenter (L / R) j := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, covarianceTileCenter, div_eq_mul_inv]
    ring
  have hNd : d ≤ N := by omega
  have hw : ∀ a : JointObservationIndex d,
      Summable (fun j : Fin d → ℤ => ‖F (R⁻¹ • covarianceTileCenter L j) a‖) := by
    intro a
    simp_rw [hx]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => PiLp.norm_apply_le (F (covarianceTileCenter (L / R) j)) a)
      (summable_schwartz_lattice_norm (div_pos hL hR) hN F)
  have hw2 : Summable (fun j : Fin d → ℤ =>
      ‖F (R⁻¹ • covarianceTileCenter L j)‖ ^ 2) := by
    simp_rw [hx]
    exact summable_schwartz_lattice_norm_sq (div_pos hL hR) hNd F
  have ht := weighted_series_l2Size_sq_le hX C hC hbound
    (fun j => F (R⁻¹ • covarianceTileCenter L j)) hw hw2 hind hmean hB hsize
  calc
    _ ≤ (L / R) ^ d * ((Fintype.card (JointObservationIndex d) : ℝ) ^ 2 *
        B ^ 2 * ∑' j : Fin d → ℤ, ‖F (R⁻¹ • covarianceTileCenter L j)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left ht (pow_nonneg (div_pos hL hR).le _)
    _ = ((Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * B ^ 2) *
        ((L / R) ^ d * ∑' j : Fin d → ℤ, ‖F (R⁻¹ • covarianceTileCenter L j)‖ ^ 2) := by ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (testBlocks_mesh_square_sum_le hR hL hLR hNd F)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))


/-- The literal complex block normalization contributes exactly one mesh
volume to the squared L² size. -/
theorem l2Size_mesh_normalization_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℂ) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    l2Size μ (fun ω => ((a ^ ((d : ℝ) / 2) : ℝ) : ℂ) * f ω) ^ 2 =
      a ^ d * l2Size μ f ^ 2 := by
  have he : l2Size μ (fun ω => ((a ^ ((d : ℝ) / 2) : ℝ) : ℂ) * f ω) =
      ‖((a ^ ((d : ℝ) / 2) : ℝ) : ℂ)‖ * l2Size μ f := by
    unfold l2Size
    simp_rw [norm_mul, mul_pow]
    rw [integral_const_mul, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
  rw [he, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hp : (a ^ ((d : ℝ) / 2)) ^ 2 = a ^ d := by
    calc
      _ = a ^ (((d : ℝ) / 2) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast ha ((d : ℝ) / 2) 2).symm
      _ = a ^ (d : ℝ) := by congr 1; ring
      _ = a ^ d := Real.rpow_natCast a d
  rw [hp]


/-- The complex bilinear integral is represented by an L² inner product only
after conjugating its first representative. No conjugation remains in the
integral. -/
theorem inner_star_toLp_eq_integral_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hf.star.toLp (star f)) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.star.coeFn_toLp, hg.coeFn_toLp] with ω hωf hωg
  rw [hωf, hωg, RCLike.inner_apply]
  simp [mul_comm]

/-- Cross-orthogonal summable families have a diagonal inner-product sum. -/
theorem inner_tsum_eq_tsum_diagonal {J E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {f g : J → E} (hf : Summable f) (hg : Summable g)
    (hoff : ∀ i j, i ≠ j → inner ℂ (f i) (g j) = 0) :
    inner ℂ (∑' j, f j) (∑' j, g j) = ∑' j, inner ℂ (f j) (g j) := by
  calc
    _ = ∑' i, inner ℂ (f i) (∑' j, g j) :=
      (innerSLFlip ℂ (∑' j, g j)).map_tsum hf
    _ = ∑' i, ∑' j, inner ℂ (f i) (g j) := by
      apply tsum_congr
      intro i
      exact (innerSL ℂ (f i)).map_tsum hg
    _ = _ := by
      apply tsum_congr
      intro i
      exact tsum_eq_single i (fun j hj => hoff i j hj.symm)

/-- The literal bilinear covariance of two absolutely L²-summable centered
series is the diagonal sum whenever different indices are independent. -/
theorem integral_mul_tsum_eq_tsum_diagonal {Ω J : Type*} [MeasurableSpace Ω]
    [Countable J] {μ : Measure Ω} {f g : J → Ω → ℂ}
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : ∀ j, MemLp (g j) 2 μ)
    (hnf : ∑' j, eLpNorm (f j) 2 μ ≠ ⊤)
    (hng : ∑' j, eLpNorm (g j) 2 μ ≠ ⊤)
    (hind : ∀ i j, i ≠ j → IndepFun (f i) (g j) μ)
    (hmean : ∀ j, (∫ ω, f j ω ∂μ) = 0) :
    (∫ ω, (∑' j, f j ω) * (∑' j, g j ω) ∂μ) =
      ∑' j, ∫ ω, f j ω * g j ω ∂μ := by
  let u : J → Lp ℂ 2 μ := fun j => (hf j).star.toLp (star (f j))
  let v : J → Lp ℂ 2 μ := fun j => (hg j).toLp (g j)
  have hnu : ∑' j, ‖u j‖ₑ ≠ ⊤ := by
    simpa only [u, Lp.enorm_toLp, eLpNorm_star] using hnf
  have hnv : ∑' j, ‖v j‖ₑ ≠ ⊤ := by
    simpa only [v, Lp.enorm_toLp] using hng
  have hsu : Summable u := (tsum_enorm_ne_top_iff_summable_norm.1 hnu).of_norm
  have hsv : Summable v := (tsum_enorm_ne_top_iff_summable_norm.1 hnv).of_norm
  have hau : ∀ᵐ ω ∂μ, ∀ j, u j ω = star (f j ω) :=
    ae_all_iff.2 fun j => (hf j).star.coeFn_toLp
  have hav : ∀ᵐ ω ∂μ, ∀ j, v j ω = g j ω :=
    ae_all_iff.2 fun j => (hg j).coeFn_toLp
  have hrep : inner ℂ (∑' j, u j) (∑' j, v j) =
      ∫ ω, (∑' j, f j ω) * (∑' j, g j ω) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_tsum hnu, Lp.coeFn_tsum hnv, hau, hav]
      with ω hωu hωv hωuf hωvg
    rw [hωu, hωv, tsum_congr hωuf, tsum_congr hωvg, ← tsum_star]
    simp [RCLike.inner_apply, mul_comm]
  have hoff : ∀ i j, i ≠ j → inner ℂ (u i) (v j) = 0 := by
    intro i j hij
    rw [inner_star_toLp_eq_integral_mul (hf i) (hg j)]
    rw [(hind i j hij).integral_fun_mul_eq_mul_integral
      (hf i).aestronglyMeasurable (hg j).aestronglyMeasurable, hmean i, zero_mul]
  rw [← hrep, inner_tsum_eq_tsum_diagonal hsu hsv hoff]
  apply tsum_congr
  intro j
  exact inner_star_toLp_eq_integral_mul (hf j) (hg j)


/-- A finite complex bilinear contraction retains every cross-coordinate of
the actual real second-moment matrix. -/
theorem integral_coord_contractions {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {μ : Measure Ω} {X : Ω → ι → ℝ} (hX : L2Vec μ X)
    (w z : ι → ℂ) :
    (∫ ω, (∑ a, w a * (X ω a : ℂ)) * (∑ b, z b * (X ω b : ℂ)) ∂μ) =
      ∑ a, ∑ b, w a * (covMat μ X a b : ℂ) * z b := by
  have ht (a b : ι) : Integrable
      (fun ω => (w a * (X ω a : ℂ)) * (z b * (X ω b : ℂ))) μ :=
    ((hX.coord_memLp a).ofReal.const_mul (w a)).integrable_mul
      ((hX.coord_memLp b).ofReal.const_mul (z b))
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum (f := fun a ω => ∑ b,
    (w a * (X ω a : ℂ)) * (z b * (X ω b : ℂ))) Finset.univ
    (fun a _ => integrable_finsetSum _ (fun b _ => ht a b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum (f := fun b ω =>
    (w a * (X ω a : ℂ)) * (z b * (X ω b : ℂ))) Finset.univ (fun b _ => ht a b)]
  apply Finset.sum_congr rfl
  intro b _
  have he : (∫ ω, (X ω a : ℂ) * (X ω b : ℂ) ∂μ) = (covMat μ X a b : ℂ) := by
    change (∫ ω, (X ω a : ℂ) * (X ω b : ℂ) ∂μ) =
      (((∫ ω, X ω a * X ω b ∂μ) : ℝ) : ℂ)
    have hfun : (fun ω => (X ω a : ℂ) * (X ω b : ℂ)) =
        (fun ω => ((X ω a * X ω b : ℝ) : ℂ)) := by
      funext ω
      exact (Complex.ofReal_mul _ _).symm
    rw [hfun]
    exact integral_ofReal (μ := μ) (𝕜 := ℂ) (f := fun ω => X ω a * X ω b)
  calc
    _ = ∫ ω, (w a * z b) * ((X ω a : ℂ) * (X ω b : ℂ)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by ring)
    _ = _ := by rw [integral_const_mul, he]; ring

/-- The literal bilinear covariance of two weighted independent vector series
is the diagonal lattice sum of the complete coordinate covariance matrix. -/
theorem weighted_series_bilinear_covariance {Ω J ι : Type*} [MeasurableSpace Ω]
    [Countable J] [Fintype ι] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : J → Ω → ι → ℝ} (hX : ∀ j, L2Vec μ (X j))
    (C : ι → ℝ≥0∞) (hC : ∀ a, C a ≠ ⊤)
    (hbound : ∀ j a, eLpNorm (fun ω => X j ω a) 2 μ ≤ C a)
    (w z : J → ι → ℂ) (hw : ∀ a, Summable (fun j => ‖w j a‖))
    (hz : ∀ a, Summable (fun j => ‖z j a‖))
    (hind : iIndepFun X μ) (hmean : ∀ j a, (∫ ω, X j ω a ∂μ) = 0) :
    (∫ ω, (∑' j, ∑ a, w j a * (X j ω a : ℂ)) *
      (∑' j, ∑ a, z j a * (X j ω a : ℂ)) ∂μ) =
      ∑' j, ∑ a, ∑ b, w j a * (covMat μ (X j) a b : ℂ) * z j b := by
  have hf (j : J) : MemLp (fun ω => ∑ a, w j a * (X j ω a : ℂ)) 2 μ :=
    memLp_finsetSum Finset.univ (fun a _ => ((hX j).coord_memLp a).ofReal.const_mul (w j a))
  have hg (j : J) : MemLp (fun ω => ∑ a, z j a * (X j ω a : ℂ)) 2 μ :=
    memLp_finsetSum Finset.univ (fun a _ => ((hX j).coord_memLp a).ofReal.const_mul (z j a))
  have hm (j : J) : (∫ ω, ∑ a, w j a * (X j ω a : ℂ) ∂μ) = 0 := by
    rw [integral_finsetSum (f := fun a ω => w j a * (X j ω a : ℂ)) Finset.univ
      (fun a _ => (((hX j).coord_memLp a).ofReal.const_mul (w j a)).integrable (by norm_num))]
    apply Finset.sum_eq_zero
    intro a _
    have he : (∫ ω, (X j ω a : ℂ) ∂μ) = (((∫ ω, X j ω a ∂μ) : ℝ) : ℂ) :=
      integral_ofReal (μ := μ) (𝕜 := ℂ) (f := fun ω => X j ω a)
    rw [integral_const_mul, he, hmean j a]
    simp
  have hi : ∀ i j, i ≠ j → IndepFun
      (fun ω => ∑ a, w i a * (X i ω a : ℂ))
      (fun ω => ∑ a, z j a * (X j ω a : ℂ)) μ := by
    intro i j hij
    exact (hind.indepFun hij).comp
      (show Measurable (fun v : ι → ℝ => ∑ a, w i a * (v a : ℂ)) from by fun_prop)
      (show Measurable (fun v : ι → ℝ => ∑ a, z j a * (v a : ℂ)) from by fun_prop)
  rw [integral_mul_tsum_eq_tsum_diagonal hf hg
    (weighted_series_eLpNorm_tsum_ne_top (fun j a => (hX j).coord_memLp a) C hC hbound w hw)
    (weighted_series_eLpNorm_tsum_ne_top (fun j a => (hX j).coord_memLp a) C hC hbound z hz) hi hm]
  apply tsum_congr
  intro j
  exact integral_coord_contractions (hX j) (w j) (z j)

theorem schwartz_norm_nonneg {d : ℕ} (N : ℕ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    0 ≤ schwartzTestNorm N F := by
  have hv : (1 + euclideanNorm (0 : Vec d)) ^ N * ‖F 0‖ ≤ schwartzTestNorm N F := by
    apply le_csSup (schwartzTestNorm_set_bddAbove N F)
    exact ⟨⟨0, by omega⟩, Fin.elim0, 0, by simp only [iteratedFDeriv_zero_apply]⟩
  exact (mul_nonneg (pow_nonneg (by unfold euclideanNorm; positivity) _) (norm_nonneg _)).trans hv

/-- Products of Schwartz values retain twice the original value decay without
requesting any higher derivative seminorm. -/
theorem schwartz_norm_mul_le {d N : ℕ}
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (x : Vec d) :
    ‖F x‖ * ‖G x‖ ≤ schwartzTestNorm N F * schwartzTestNorm N G *
      ((1 + euclideanNorm x) ^ (2 * N))⁻¹ := by
  have hv (H : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
      (1 + euclideanNorm x) ^ N * ‖H x‖ ≤ schwartzTestNorm N H := by
    apply le_csSup (schwartzTestNorm_set_bddAbove N H)
    exact ⟨⟨0, by omega⟩, Fin.elim0, x, by simp only [iteratedFDeriv_zero_apply]⟩
  have hp : 0 < 1 + euclideanNorm x := by unfold euclideanNorm; positivity
  have hh := mul_le_mul (hv F) (hv G)
    (mul_nonneg (pow_nonneg hp.le _) (norm_nonneg _))
    ((mul_nonneg (pow_nonneg hp.le _) (norm_nonneg _)).trans (hv F))
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hp _)).2
  rw [show 2 * N = N * 2 by omega, pow_mul]
  convert hh using 1 <;> ring

/-- The complete bilinear contraction is bounded by the Frobenius matrix size.
The harmless coordinate count is structural and includes all cross entries. -/
theorem norm_bilinear_matrix_le {d : ℕ}
    (M : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (u v : EuclideanSpace ℂ (JointObservationIndex d)) :
    ‖∑ a, ∑ b, u a * (M a b : ℂ) * v b‖ ≤
      (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M *
        ‖u‖ * ‖v‖ := by
  calc
    _ ≤ ∑ a, ∑ b, ‖u a * (M a b : ℂ) * v b‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : JointObservationIndex d, ∑ _b : JointObservationIndex d,
        ‖u‖ * covarianceMatrixSize M * ‖v‖ := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul (PiLp.norm_apply_le u a)
        (C10.abs_entry_le_frob M a b) (abs_nonneg _) (norm_nonneg _))
        (PiLp.norm_apply_le v b) (norm_nonneg _) (by unfold covarianceMatrixSize; positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Absolute summability of the full matrix contraction on the literal lattice. -/
theorem summable_bilinear_matrix_lattice {d N : ℕ} {a : ℝ}
    (ha : 0 < a) (hN : d ≤ N)
    (M : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Summable (fun j : Fin d → ℤ => ∑ i, ∑ k,
      F (covarianceTileCenter a j) i * (M i k : ℂ) * G (covarianceTileCenter a j) k) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    ((summable_lattice_euclidean_decay ha (Nat.mul_le_mul_left 2 hN)).mul_left
      ((Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M *
        (schwartzTestNorm N F * schwartzTestNorm N G)))
  calc
    _ ≤ (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M *
        (‖F (covarianceTileCenter a j)‖ * ‖G (covarianceTileCenter a j)‖) := by
      simpa only [mul_assoc] using norm_bilinear_matrix_le M
        (F (covarianceTileCenter a j)) (G (covarianceTileCenter a j))
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (schwartz_norm_mul_le (N := N) F G (covarianceTileCenter a j))
        (by unfold covarianceMatrixSize; positivity :
          0 ≤ (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M)

/-- A uniform mesh-volume bound for the literal bilinear covariance lattice sum. -/
theorem mesh_bilinear_matrix_tsum_le {d N : ℕ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hN : d ≤ N)
    (M : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    ‖((a ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ i, ∑ k,
      F (covarianceTileCenter a j) i * (M i k : ℂ) * G (covarianceTileCenter a j) k‖ ≤
      (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * 3 ^ d *
        covarianceMatrixSize M * schwartzTestNorm N F * schwartzTestNorm N G := by
  let K := (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M *
    (schwartzTestNorm N F * schwartzTestNorm N G)
  have hK : 0 ≤ K := by
    dsimp only [K]
    unfold covarianceMatrixSize
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (schwartz_norm_nonneg N F) (schwartz_norm_nonneg N G))
  have hd := summable_lattice_euclidean_decay ha (Nat.mul_le_mul_left 2 hN)
  have hs := summable_bilinear_matrix_lattice ha hN M F G
  have ht : (∑' j : Fin d → ℤ, ‖∑ i, ∑ k,
      F (covarianceTileCenter a j) i * (M i k : ℂ) * G (covarianceTileCenter a j) k‖) ≤
      K * ∑' j : Fin d → ℤ, ((1 + euclideanNorm (covarianceTileCenter a j)) ^ (2 * N))⁻¹ := by
    rw [← hd.tsum_mul_left]
    apply hs.norm.tsum_le_tsum _ (hd.mul_left K)
    intro j
    exact (norm_bilinear_matrix_le M _ _).trans (by
      simpa only [K, mul_assoc] using mul_le_mul_of_nonneg_left
        (schwartz_norm_mul_le (N := N) F G (covarianceTileCenter a j))
        (by unfold covarianceMatrixSize; positivity :
          0 ≤ (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M))
  calc
    _ = a ^ d * ‖∑' j : Fin d → ℤ, ∑ i, ∑ k,
        F (covarianceTileCenter a j) i * (M i k : ℂ) * G (covarianceTileCenter a j) k‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha.le _)]
    _ ≤ a ^ d * (K * ∑' j : Fin d → ℤ,
        ((1 + euclideanNorm (covarianceTileCenter a j)) ^ (2 * N))⁻¹) :=
      mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hs.norm).trans ht) (pow_nonneg ha.le _)
    _ = K * (a ^ d * ∑' j : Fin d → ℤ,
        ((1 + euclideanNorm (covarianceTileCenter a j)) ^ (2 * N))⁻¹) := by ring
    _ ≤ K * 3 ^ d := mul_le_mul_of_nonneg_left
      (mesh_tsum_lattice_euclidean_decay_le ha ha1 (Nat.mul_le_mul_left 2 hN)) hK
    _ = _ := by dsimp only [K]; ring

/-- Replacing a covariance matrix in the actual rescaled lattice sum costs
its Frobenius error times the original two Schwartz norms. -/
theorem testBlocks_mesh_matrix_sub_le {d N : ℕ} {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hLR : L ≤ R) (hN : d ≤ N)
    (B A : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    ‖(((L / R) ^ d : ℝ) : ℂ) * (∑' j : Fin d → ℤ, ∑ i, ∑ k,
        F (R⁻¹ • covarianceTileCenter L j) i * (B i k : ℂ) *
          G (R⁻¹ • covarianceTileCenter L j) k) -
      (((L / R) ^ d : ℝ) : ℂ) * (∑' j : Fin d → ℤ, ∑ i, ∑ k,
        F (R⁻¹ • covarianceTileCenter L j) i * (A i k : ℂ) *
          G (R⁻¹ • covarianceTileCenter L j) k)‖ ≤
      (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * 3 ^ d *
        covarianceMatrixSize (B - A) * schwartzTestNorm N F * schwartzTestNorm N G := by
  have hx (j : Fin d → ℤ) :
      R⁻¹ • covarianceTileCenter L j = covarianceTileCenter (L / R) j := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, covarianceTileCenter, div_eq_mul_inv]
    ring
  simp_rw [hx]
  have hsB := summable_bilinear_matrix_lattice (div_pos hL hR) hN B F G
  have hsA := summable_bilinear_matrix_lattice (div_pos hL hR) hN A F G
  rw [← mul_sub, ← hsB.tsum_sub hsA]
  have he (j : Fin d → ℤ) :
      (∑ i, ∑ k, F (covarianceTileCenter (L / R) j) i * (B i k : ℂ) *
        G (covarianceTileCenter (L / R) j) k) -
      (∑ i, ∑ k, F (covarianceTileCenter (L / R) j) i * (A i k : ℂ) *
        G (covarianceTileCenter (L / R) j) k) =
      ∑ i, ∑ k, F (covarianceTileCenter (L / R) j) i * ((B - A) i k : ℂ) *
        G (covarianceTileCenter (L / R) j) k := by
    simp only [Matrix.sub_apply, Complex.ofReal_sub, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  simp_rw [he]
  exact mesh_bilinear_matrix_tsum_le (div_pos hL hR) ((div_le_one hR).2 hLR) hN (B - A) F G

/-- Open lattice cubes are literally disjoint; no boundary convention is
changed to establish the tiling. -/
theorem lattice_cubes_pairwise_disjoint {d : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    Pairwise (fun j k : Fin d → ℤ => Disjoint
      (clockBlockCube (covarianceTileCenter L j) L)
      (clockBlockCube (covarianceTileCenter L k) L)) := by
  intro j k hjk
  rw [Set.disjoint_left]
  intro x hxj hxk
  obtain ⟨i, hi⟩ := tileCenter_separated hL hjk
  have hj := mem_clockBlockCube_iff.mp hxj i
  have hk := mem_clockBlockCube_iff.mp hxk i
  have he : |covarianceTileCenter L j i - covarianceTileCenter L k i| < L :=
    abs_lt.mpr ⟨by linarith [hj.2, hk.1], by linarith [hj.1, hk.2]⟩
  exact (not_lt_of_ge hi) he

/-- The excluded faces of all open lattice cubes form a null set. -/
theorem ae_mem_lattice_cube {d : ℕ} {L : ℝ} (hL : 0 < L) :
    ∀ᵐ x : Vec d ∂volume, ∃ j : Fin d → ℤ,
      x ∈ clockBlockCube (covarianceTileCenter L j) L := by
  have hne : ∀ᵐ x : Vec d ∂volume, ∀ i, ∀ n : ℤ,
      x i ≠ L * (n : ℝ) - L / 2 := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro n
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i _
  filter_upwards [hne] with x hx
  let j : Fin d → ℤ := fun i => Int.floor (x i / L + 1 / 2)
  refine ⟨j, mem_clockBlockCube_iff.mpr fun i => ?_⟩
  have hlo : (j i : ℝ) - 1 / 2 ≤ x i / L := by
    have hh := Int.floor_le (x i / L + 1 / 2)
    dsimp only [j]
    linarith
  have hup : x i / L < (j i : ℝ) + 1 / 2 := by
    have hh := Int.lt_floor_add_one (x i / L + 1 / 2)
    dsimp only [j]
    linarith
  have hleft : L * (j i : ℝ) - L / 2 ≤ x i := by
    have hh := (le_div_iff₀ hL).mp hlo
    nlinarith only [hh]
  have hright : x i < L * (j i : ℝ) + L / 2 := by
    have hh := (div_lt_iff₀ hL).mp hup
    nlinarith only [hh]
  exact ⟨lt_of_le_of_ne hleft (Ne.symm (hx i (j i))), hright⟩

/-- The literal union of the original open lattice cubes equals all of space
modulo their null faces. -/
theorem lattice_cubes_ae_univ {d : ℕ} {L : ℝ} (hL : 0 < L) :
    (⋃ j : Fin d → ℤ, clockBlockCube (covarianceTileCenter L j) L) =ᵐ[volume]
      (Set.univ : Set (Vec d)) := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [ae_mem_lattice_cube (d := d) hL] with x hx
  exact ⟨fun _ => Set.mem_univ x, fun _ => Set.mem_iUnion.mpr hx⟩

/-- Bochner integration splits over the actual countable open-cube tiling. -/
theorem integral_eq_tsum_lattice_cubes {d : ℕ} {L : ℝ} (hL : 0 < L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec d → E} (hf : Integrable f volume) :
    (∫ x, f x) = ∑' j : Fin d → ℤ,
      ∫ x in clockBlockCube (covarianceTileCenter L j) L, f x := by
  have he := integral_iUnion (fun j : Fin d → ℤ =>
    measurableSet_clockBlockCube (covarianceTileCenter L j) L)
    (lattice_cubes_pairwise_disjoint hL.le) hf.integrableOn
  rw [setIntegral_congr_set (lattice_cubes_ae_univ hL), setIntegral_univ] at he
  exact he

/-- Integrability gives genuine summability of the open-cube integrals. -/
theorem hasSum_integral_lattice_cubes {d : ℕ} {L : ℝ} (hL : 0 < L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec d → E} (hf : Integrable f volume) :
    HasSum (fun j : Fin d → ℤ =>
      ∫ x in clockBlockCube (covarianceTileCenter L j) L, f x) (∫ x, f x) := by
  have he := hasSum_integral_iUnion (fun j : Fin d → ℤ =>
    measurableSet_clockBlockCube (covarianceTileCenter L j) L)
    (lattice_cubes_pairwise_disjoint hL.le) hf.integrableOn
  rw [setIntegral_congr_set (lattice_cubes_ae_univ hL), setIntegral_univ] at he
  exact he

/-- A deterministic quadrature bound on the literal open-cube tiling. The
pointwise oscillation majorants will be supplied by Schwartz derivative bounds. -/
theorem lattice_quadrature_error_le {d : ℕ} {L : ℝ} (hL : 0 < L)
    {f : Vec d → ℂ} (hf : Integrable f volume)
    (c : (Fin d → ℤ) → ℂ) (hc : Summable c)
    (e : (Fin d → ℤ) → ℝ) (he : Summable e)
    (hosc : ∀ j x, x ∈ clockBlockCube (covarianceTileCenter L j) L →
      ‖f x - c j‖ ≤ e j) :
    ‖(∫ x, f x) - ((L ^ d : ℝ) : ℂ) * ∑' j, c j‖ ≤ L ^ d * ∑' j, e j := by
  let v := fun j : Fin d → ℤ =>
    ∫ x in clockBlockCube (covarianceTileCenter L j) L, f x
  have hv : Summable v := (hasSum_integral_lattice_cubes hL hf).summable
  have hconst (j : Fin d → ℤ) :
      (∫ _x in clockBlockCube (covarianceTileCenter L j) L, c j) =
        ((L ^ d : ℝ) : ℂ) * c j := by
    rw [setIntegral_const, volumeReal_clockBlockCube _ hL.le, Complex.real_smul]
  have hlocal (j : Fin d → ℤ) : ‖v j - ((L ^ d : ℝ) : ℂ) * c j‖ ≤ e j * L ^ d := by
    have hi : IntegrableOn (fun _x : Vec d => c j)
        (clockBlockCube (covarianceTileCenter L j) L) volume :=
      integrableOn_const (volume_clockBlockCube_lt_top _ _).ne
    rw [← hconst j, ← integral_sub hf.integrableOn hi]
    simpa only [volumeReal_clockBlockCube _ hL.le] using
      norm_setIntegral_le_of_norm_le_const (volume_clockBlockCube_lt_top _ _) (hosc j)
  rw [integral_eq_tsum_lattice_cubes hL hf, ← hc.tsum_mul_left,
    ← hv.tsum_sub (hc.mul_left (((L ^ d : ℝ) : ℂ)))]
  calc
    _ ≤ ∑' j, ‖v j - ((L ^ d : ℝ) : ℂ) * c j‖ :=
      norm_tsum_le_tsum_norm (hv.sub (hc.mul_left _)).norm
    _ ≤ ∑' j, e j * L ^ d :=
      (hv.sub (hc.mul_left _)).norm.tsum_le_tsum hlocal (he.mul_right _)
    _ = L ^ d * ∑' j, e j := by rw [he.tsum_mul_right]; ring

/-- The coordinate derivatives already present in the original Schwartz norm
control the full derivative on the existing coordinate carrier. -/
theorem schwartz_fderiv_norm_le {d N : ℕ} (hN : 1 ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) (x : Vec d) :
    ‖fderiv ℝ (fun y => F y) x‖ ≤ (d : ℝ) * schwartzTestNorm N F *
      ((1 + euclideanNorm x) ^ N)⁻¹ := by
  have hp : 0 < (1 + euclideanNorm x) ^ N := by unfold euclideanNorm; positivity
  let C := schwartzTestNorm N F / (1 + euclideanNorm x) ^ N
  have hC : 0 ≤ C := div_nonneg (schwartz_norm_nonneg N F) hp.le
  have hc (i : Fin d) : ‖fderiv ℝ (fun y => F y) x (unitVector i)‖ ≤ C := by
    apply (le_div_iff₀ hp).mpr
    have hv : (1 + euclideanNorm x) ^ N *
        ‖fderiv ℝ (fun y => F y) x (unitVector i)‖ ≤ schwartzTestNorm N F := by
      apply le_csSup (schwartzTestNorm_set_bddAbove N F)
      refine ⟨⟨1, by omega⟩, (fun _ => i), x, ?_⟩
      simp only [iteratedFDeriv_one_apply]
    simpa only [mul_comm] using hv
  have hb : ‖fderiv ℝ (fun y => F y) x‖ ≤ (d : ℝ) * C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hC)
    intro v
    have hexp : v = ∑ i : Fin d, v i • unitVector i := by
      ext k
      simp [unitVector, Pi.single_apply, Finset.sum_apply]
    calc
      _ = ‖∑ i : Fin d, v i • fderiv ℝ (fun y => F y) x (unitVector i)‖ := by
        conv_lhs => rw [hexp]
        rw [map_sum]
        simp only [map_smul]
      _ ≤ ∑ i : Fin d, ‖v i‖ * ‖fderiv ℝ (fun y => F y) x (unitVector i)‖ := by
        simpa only [norm_smul] using norm_sum_le Finset.univ
          (fun i : Fin d => v i • fderiv ℝ (fun y => F y) x (unitVector i))
      _ ≤ ∑ _i : Fin d, ‖v‖ * C := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul (norm_le_pi_norm v i) (hc i) (norm_nonneg _) (norm_nonneg _)
      _ = ((d : ℝ) * C) * ‖v‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  simpa only [C, div_eq_mul_inv, mul_assoc] using hb

/-- The existing coordinate norm measures at most half a side length inside
an open cube. Euclidean estimates below retain their explicit dimension factor. -/
theorem norm_sub_center_le_of_mem_cube {d : ℕ} {L : ℝ} (hL : 0 ≤ L)
    {x c : Vec d} (hx : x ∈ clockBlockCube c L) : ‖x - c‖ ≤ L / 2 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ L / 2)).mpr
  intro i
  have hi := mem_clockBlockCube_iff.mp hx i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩ : |x i - c i| ≤ L / 2)

/-- Schwartz weights at a point and its cube center are uniformly comparable
for meshes at most one, using the explicit Euclidean norm. -/
theorem cube_center_weight_le {d : ℕ} {L : ℝ} (hL : 0 ≤ L) (hL1 : L ≤ 1)
    {x c : Vec d} (hx : x ∈ clockBlockCube c L) :
    1 + euclideanNorm c ≤ (2 + (d : ℝ)) * (1 + euclideanNorm x) := by
  have hd : euclideanNorm (c - x) ≤ ((d : ℝ) + 1) * (L / 2) := by
    apply (euclideanNorm_le_dimension_mul_norm (c - x)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [norm_sub_rev]
    exact norm_sub_center_le_of_mem_cube hL hx
  have ht : euclideanNorm c ≤ euclideanNorm (c - x) + euclideanNorm x := by
    have he (v : Vec d) : euclideanNorm v = vsize v := by
      simp only [euclideanNorm, euclideanSq, dot, vsize, pow_two]
    have hadd : (WithLp.toLp 2 (c - x) : EuclideanSpace ℝ (Fin d)) +
        WithLp.toLp 2 x = WithLp.toLp 2 c := by
      ext i
      change c i - x i + x i = c i
      ring
    have hh := norm_add_le (WithLp.toLp 2 (c - x) : EuclideanSpace ℝ (Fin d))
      (WithLp.toLp 2 x)
    rw [hadd] at hh
    simpa only [← vsize_eq_norm, ← he] using hh
  have hx0 : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- A weighted bound valid throughout a small cube transfers to its center's
weight without any change of the exponent. -/
theorem cube_weighted_bound {d N : ℕ} {L t S : ℝ}
    (hL : 0 ≤ L) (hL1 : L ≤ 1) {x c : Vec d}
    (hx : x ∈ clockBlockCube c L) (ht : 0 ≤ t)
    (hbound : (1 + euclideanNorm x) ^ N * t ≤ S) :
    t ≤ (2 + (d : ℝ)) ^ N * S * ((1 + euclideanNorm c) ^ N)⁻¹ := by
  have hp : 0 < (1 + euclideanNorm c) ^ N := by unfold euclideanNorm; positivity
  have hw := pow_le_pow_left₀ (by unfold euclideanNorm; positivity : 0 ≤ 1 + euclideanNorm c)
    (cube_center_weight_le hL hL1 hx) N
  rw [mul_pow] at hw
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  calc
    t * (1 + euclideanNorm c) ^ N ≤
        t * ((2 + (d : ℝ)) ^ N * (1 + euclideanNorm x) ^ N) :=
      mul_le_mul_of_nonneg_left hw ht
    _ = (2 + (d : ℝ)) ^ N * ((1 + euclideanNorm x) ^ N * t) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)


/-- Original order-N value decay, transferred to the center of a small cube. -/
theorem schwartz_cube_value_le {d N : ℕ} {L : ℝ} (hL : 0 ≤ L) (hL1 : L ≤ 1)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    {x c : Vec d} (hx : x ∈ clockBlockCube c L) :
    ‖F x‖ ≤ (2 + (d : ℝ)) ^ N * schwartzTestNorm N F *
      ((1 + euclideanNorm c) ^ N)⁻¹ := by
  apply cube_weighted_bound hL hL1 hx (norm_nonneg _)
  apply le_csSup (schwartzTestNorm_set_bddAbove N F)
  exact ⟨⟨0, by omega⟩, Fin.elim0, x, by simp only [iteratedFDeriv_zero_apply]⟩

/-- Schwartz oscillation on a mesh cube, at the original derivative order.
The decay is measured at its center and the mesh contributes one power. -/
theorem schwartz_cube_oscillation_le {d N : ℕ} (hN : 1 ≤ N)
    {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    {x c : Vec d} (hx : x ∈ clockBlockCube c L) :
    ‖F x - F c‖ ≤ ((2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) *
      ((1 + euclideanNorm c) ^ N)⁻¹) * (L / 2) := by
  let C := (2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) *
    ((1 + euclideanNorm c) ^ N)⁻¹
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by positivity)
      (mul_nonneg (Nat.cast_nonneg _) (schwartz_norm_nonneg N F)))
      (by unfold euclideanNorm; positivity)
  have hb (y : Vec d) (hy : y ∈ clockBlockCube c L) :
      ‖fderiv ℝ (fun z => F z) y‖ ≤ C := by
    apply cube_weighted_bound hL.le hL1 hy (norm_nonneg _)
    have hp : 0 < (1 + euclideanNorm y) ^ N := by unfold euclideanNorm; positivity
    have hd : ‖fderiv ℝ (fun z => F z) y‖ ≤
        (d : ℝ) * schwartzTestNorm N F / (1 + euclideanNorm y) ^ N := by
      simpa only [div_eq_mul_inv] using schwartz_fderiv_norm_le hN F y
    simpa only [mul_comm] using (le_div_iff₀ hp).mp hd
  have hs : Convex ℝ (clockBlockCube c L) := by
    exact convex_pi (fun _ _ => convex_Ioo _ _)
  have hc : c ∈ clockBlockCube c L := by
    apply mem_clockBlockCube_iff.mpr
    intro i
    constructor <;> linarith
  have hh := hs.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => F.differentiableAt) hb hc hx
  exact hh.trans (mul_le_mul_of_nonneg_left
    (norm_sub_center_le_of_mem_cube hL.le hx) hC)


/-- The full bilinear spatial integrand is genuinely Bochner integrable.
Only boundedness of one Schwartz factor and integrability of the other are used. -/
theorem integrable_bilinear_matrix {d : ℕ}
    (M : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Integrable (fun x => ∑ a, ∑ b, F x a * (M a b : ℂ) * G x b) volume := by
  let K := (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M
  have hK : 0 ≤ K := by dsimp [K, covarianceMatrixSize]; positivity
  have hG (x : Vec d) : ‖G x‖ ≤ schwartzTestNorm 0 G := by
    have hv : (1 + euclideanNorm x) ^ 0 * ‖G x‖ ≤ schwartzTestNorm 0 G := by
      apply le_csSup (schwartzTestNorm_set_bddAbove 0 G)
      exact ⟨⟨0, by omega⟩, Fin.elim0, x, by simp only [iteratedFDeriv_zero_apply]⟩
    simpa only [pow_zero, one_mul] using hv
  have hi : Integrable (fun x => K * schwartzTestNorm 0 G * ‖F x‖) volume :=
    F.integrable.norm.const_mul _
  apply hi.mono' (by fun_prop)
  filter_upwards [] with x
  calc
    _ ≤ K * ‖F x‖ * ‖G x‖ := norm_bilinear_matrix_le M _ _
    _ ≤ K * ‖F x‖ * schwartzTestNorm 0 G :=
      mul_le_mul_of_nonneg_left (hG x) (mul_nonneg hK (norm_nonneg _))
    _ = _ := by ring


/-- Bilinear variation retains all matrix entries and uses no conjugation. -/
theorem norm_bilinear_matrix_sub_le {d : ℕ}
    (M : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (u v u' v' : EuclideanSpace ℂ (JointObservationIndex d)) :
    ‖(∑ a, ∑ b, u a * (M a b : ℂ) * v b) -
        (∑ a, ∑ b, u' a * (M a b : ℂ) * v' b)‖ ≤
      ((Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M) *
        (‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖) := by
  have he : (∑ a, ∑ b, u a * (M a b : ℂ) * v b) -
      (∑ a, ∑ b, u' a * (M a b : ℂ) * v' b) =
      (∑ a, ∑ b, (u - u') a * (M a b : ℂ) * v b) +
      (∑ a, ∑ b, u' a * (M a b : ℂ) * (v - v') b) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    simp only [PiLp.sub_apply]
    ring
  rw [he]
  exact (norm_add_le _ _).trans
    ((add_le_add (norm_bilinear_matrix_le M _ _) (norm_bilinear_matrix_le M _ _)).trans_eq
      (by ring))


/-- First-order oscillation of the full bilinear integrand on an actual mesh
cube, retaining twice the original value decay and all cross entries. -/
theorem bilinear_matrix_cube_oscillation_le {d N : ℕ} (hN : 1 ≤ N)
    {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (M : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    {x c : Vec d} (hx : x ∈ clockBlockCube c L) :
    ‖(∑ a, ∑ b, F x a * (M a b : ℂ) * G x b) -
        (∑ a, ∑ b, F c a * (M a b : ℂ) * G c b)‖ ≤
      ((Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M) *
        ((d : ℝ) * (2 + (d : ℝ)) ^ (2 * N) * schwartzTestNorm N F *
          schwartzTestNorm N G) * L * ((1 + euclideanNorm c) ^ (2 * N))⁻¹ := by
  let H := (2 + (d : ℝ)) ^ N
  let w := ((1 + euclideanNorm c) ^ N)⁻¹
  let A := H * schwartzTestNorm N F * w
  let B := H * schwartzTestNorm N G * w
  have hA : 0 ≤ A := by
    dsimp [A, H, w]
    exact mul_nonneg (mul_nonneg (by positivity) (schwartz_norm_nonneg N F))
      (by unfold euclideanNorm; positivity)
  have hB : 0 ≤ B := by
    dsimp [B, H, w]
    exact mul_nonneg (mul_nonneg (by positivity) (schwartz_norm_nonneg N G))
      (by unfold euclideanNorm; positivity)
  have hc : c ∈ clockBlockCube c L := by
    apply mem_clockBlockCube_iff.mpr
    intro i
    constructor <;> linarith
  have hFx : ‖F x - F c‖ ≤ (d : ℝ) * A * (L / 2) := by
    simpa only [A, H, w, mul_assoc, mul_left_comm, mul_comm] using
      schwartz_cube_oscillation_le hN hL hL1 F hx
  have hGx : ‖G x - G c‖ ≤ (d : ℝ) * B * (L / 2) := by
    simpa only [B, H, w, mul_assoc, mul_left_comm, mul_comm] using
      schwartz_cube_oscillation_le hN hL hL1 G hx
  have hFc : ‖F c‖ ≤ A := schwartz_cube_value_le hL.le hL1 F hc
  have hGv : ‖G x‖ ≤ B := schwartz_cube_value_le hL.le hL1 G hx
  have hp : ‖F x - F c‖ * ‖G x‖ + ‖F c‖ * ‖G x - G c‖ ≤
      ((d : ℝ) * A * (L / 2)) * B + A * ((d : ℝ) * B * (L / 2)) :=
    add_le_add (mul_le_mul hFx hGv (norm_nonneg _) (by positivity))
      (mul_le_mul hFc hGx (norm_nonneg _) hA)
  have hK : 0 ≤ (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 *
      covarianceMatrixSize M := by unfold covarianceMatrixSize; positivity
  apply (norm_bilinear_matrix_sub_le M (F x) (G x) (F c) (G c)).trans
  apply (mul_le_mul_of_nonneg_left hp hK).trans_eq
  dsimp only [A, B, H, w]
  simp only [two_mul, pow_add, mul_inv]
  ring

/-- Quantitative Riemann error for the literal bilinear lattice sum. Constants
are structural; neither the order N nor the anisotropic matrix is replaced. -/
theorem bilinear_matrix_riemann_error_le {d N : ℕ} (hN : 1 ≤ N) (hdN : d ≤ N)
    {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (M : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    ‖(∫ x, ∑ a, ∑ b, F x a * (M a b : ℂ) * G x b) -
        ((L ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ a, ∑ b,
          F (covarianceTileCenter L j) a * (M a b : ℂ) *
            G (covarianceTileCenter L j) b‖ ≤
      ((Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M) *
        ((d : ℝ) * (2 + (d : ℝ)) ^ (2 * N) * schwartzTestNorm N F *
          schwartzTestNorm N G) * L * 3 ^ d := by
  let K := ((Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M) *
    ((d : ℝ) * (2 + (d : ℝ)) ^ (2 * N) * schwartzTestNorm N F * schwartzTestNorm N G) * L
  have hK : 0 ≤ K := by
    dsimp only [K]
    unfold covarianceMatrixSize
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
        (schwartz_norm_nonneg N F)) (schwartz_norm_nonneg N G))) hL.le
  have hs := summable_lattice_euclidean_decay hL (Nat.mul_le_mul_left 2 hdN)
  have hh := lattice_quadrature_error_le hL (integrable_bilinear_matrix M F G)
    _ (summable_bilinear_matrix_lattice hL hdN M F G)
    (fun j => K * ((1 + euclideanNorm (covarianceTileCenter L j)) ^ (2 * N))⁻¹)
    (hs.mul_left K) (fun j x hx => bilinear_matrix_cube_oscillation_le hN hL hL1 M F G hx)
  rw [hs.tsum_mul_left] at hh
  calc
    _ ≤ L ^ d * (K * ∑' j : Fin d → ℤ,
        ((1 + euclideanNorm (covarianceTileCenter L j)) ^ (2 * N))⁻¹) := hh
    _ = K * (L ^ d * ∑' j : Fin d → ℤ,
        ((1 + euclideanNorm (covarianceTileCenter L j)) ^ (2 * N))⁻¹) := by ring
    _ ≤ K * 3 ^ d := mul_le_mul_of_nonneg_left
      (mesh_tsum_lattice_euclidean_decay_le hL hL1 (Nat.mul_le_mul_left 2 hdN)) hK


/-- The spatial Riemann bound in the literal rescaled coordinates of the
infinite test-block construction. -/
theorem testBlocks_mesh_riemann_error_le {d N : ℕ} (hN : 1 ≤ N) (hdN : d ≤ N)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (hLR : L ≤ R)
    (M : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    ‖(((L / R) ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ a, ∑ b,
        F (R⁻¹ • covarianceTileCenter L j) a * (M a b : ℂ) *
          G (R⁻¹ • covarianceTileCenter L j) b -
        (∫ x, ∑ a, ∑ b, F x a * (M a b : ℂ) * G x b)‖ ≤
      ((Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * covarianceMatrixSize M) *
        ((d : ℝ) * (2 + (d : ℝ)) ^ (2 * N) * schwartzTestNorm N F *
          schwartzTestNorm N G) * (L / R) * 3 ^ d := by
  have hx (j : Fin d → ℤ) :
      R⁻¹ • covarianceTileCenter L j = covarianceTileCenter (L / R) j := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, covarianceTileCenter, div_eq_mul_inv]
    ring
  simp_rw [hx]
  rw [norm_sub_rev]
  exact bilinear_matrix_riemann_error_le hN hdN (div_pos hL hR)
    ((div_le_one hR).mpr hLR) M F G

end EinsteinFull.Calculus.C10TestBlocks
