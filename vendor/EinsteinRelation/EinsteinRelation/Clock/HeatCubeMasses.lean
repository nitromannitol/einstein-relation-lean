import EinsteinRelation.Correctors.HeatSmoothing
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Heat-kernel masses of the cubes of a partition

The Euclidean heat kernel `euclideanHeatKernel t` is a probability density on `Vec d` for
every `t > 0`. Partition `Vec d` into the half-open cubes `heatCube L z` of side `L`, indexed by
`z : Fin d → ℤ`. The masses `heatCubeMass L t z` of these cubes sum to one, and each is at most
`min {1, L ^ d * (4 π t) ^ (-d/2)}`. Hence the sum of their squares is at most a constant times
`(1 + t) ^ (-d/2)` (`paper/main.tex:1155-1159`, clock spatial averages).
-/

open MeasureTheory
open EinsteinRelation.Correctors (euclideanHeatKernel)

namespace EinsteinRelation.Clock

/-- The half-open cube of side `L` with index `z`. -/
def heatCube {d : ℕ} (L : ℝ) (z : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ i, L * z i ≤ x i ∧ x i < L * (z i + 1)}

/-- The mass that the heat kernel at time `t` gives to the cube `heatCube L z`. -/
noncomputable def heatCubeMass {d : ℕ} (L t : ℝ) (z : Fin d → ℤ) : ℝ :=
  ∫ x in heatCube L z, euclideanHeatKernel t x

/-! ### Membership and the Euclidean norm -/

private lemma mem_heatCube_iff {d : ℕ} {L : ℝ} {z : Fin d → ℤ} {x : Vec d} :
    x ∈ heatCube L z ↔ ∀ i, L * (z i : ℝ) ≤ x i ∧ x i < L * ((z i : ℝ) + 1) :=
  Iff.rfl

private lemma heatSq_nonneg {d : ℕ} (x : Vec d) : 0 ≤ euclideanSq x := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

private lemma heatSq_eq_sum_sq {d : ℕ} (x : Vec d) : euclideanSq x = ∑ i, x i ^ 2 := by
  unfold euclideanSq dot
  exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm

private lemma heatKernel_base_pos {t : ℝ} (ht : 0 < t) : 0 < 4 * Real.pi * t :=
  mul_pos (mul_pos (by norm_num) Real.pi_pos) ht

/-! ### The heat kernel is a probability density -/

/-- The Euclidean heat kernel is nonnegative for `t > 0`. -/
theorem euclideanHeatKernel_nonneg {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Vec d) :
    0 ≤ euclideanHeatKernel t x := by
  unfold euclideanHeatKernel
  exact mul_nonneg (Real.rpow_nonneg (heatKernel_base_pos ht).le _) (Real.exp_pos _).le

/-- The Euclidean heat kernel is at most its value at the origin. -/
private lemma euclideanHeatKernel_le_value {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Vec d) :
    euclideanHeatKernel t x ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
  unfold euclideanHeatKernel
  refine mul_le_of_le_one_right (Real.rpow_nonneg (heatKernel_base_pos ht).le _) ?_
  refine Real.exp_le_one_iff.mpr ?_
  rw [neg_div]
  exact neg_nonpos.mpr (div_nonneg (heatSq_nonneg x) (by linarith))

/-- The heat kernel written as a product over coordinates. -/
private lemma euclideanHeatKernel_eq_prod {d : ℕ} (t : ℝ) (x : Vec d) :
    euclideanHeatKernel t x =
      (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * ∏ i, Real.exp (-(1 / (4 * t)) * x i ^ 2) := by
  have hmul : ∑ i, -(1 / (4 * t)) * x i ^ 2 = -(1 / (4 * t)) * euclideanSq x := by
    rw [heatSq_eq_sum_sq, Finset.mul_sum]
  have hS : -(euclideanSq x) / (4 * t) = ∑ i, -(1 / (4 * t)) * x i ^ 2 := by
    rw [hmul]
    ring
  unfold euclideanHeatKernel
  rw [← Real.exp_sum, hS]

/-- The one-dimensional Gaussian integral with variance `2t`. -/
private lemma integral_gauss_heat (t : ℝ) :
    (∫ y : ℝ, Real.exp (-(1 / (4 * t)) * y ^ 2)) = Real.sqrt (4 * Real.pi * t) := by
  rw [integral_gaussian]
  congr 1
  rw [one_div, div_inv_eq_mul]
  ring

/-- The Gaussian integral over `Vec d` factors over the coordinates. -/
private lemma integral_prod_heat (d : ℕ) (t : ℝ) :
    (∫ x : Vec d, ∏ i, Real.exp (-(1 / (4 * t)) * x i ^ 2)) =
      (∫ y : ℝ, Real.exp (-(1 / (4 * t)) * y ^ 2)) ^ d := by
  rw [volume_pi,
    integral_fintype_prod_eq_prod (fun (_ : Fin d) (y : ℝ) => Real.exp (-(1 / (4 * t)) * y ^ 2))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The product Gaussian is integrable on `Vec d` for `t > 0`. -/
private lemma integrable_prod_heat (d : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec d => ∏ i, Real.exp (-(1 / (4 * t)) * x i ^ 2)) volume := by
  have hb : 0 < 1 / (4 * t) := div_pos one_pos (mul_pos (by norm_num) ht)
  rw [volume_pi]
  exact Integrable.fintype_prod
    (f := fun (_ : Fin d) (y : ℝ) => Real.exp (-(1 / (4 * t)) * y ^ 2))
    (fun _ => integrable_exp_neg_mul_sq hb)

/-- `(4 π t) ^ (-d/2)` times the `d`-th power of `√(4 π t)` is one. -/
private lemma rpow_neg_half_mul_sqrt_pow (A : ℝ) (hA : 0 < A) (d : ℕ) :
    A ^ (-(d : ℝ) / 2) * Real.sqrt A ^ d = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hA.le, ← Real.rpow_add hA]
  have h0 : -(d : ℝ) / 2 + 1 / 2 * (d : ℝ) = 0 := by ring
  rw [h0, Real.rpow_zero]

/-- The heat kernel is integrable for `t > 0`. -/
theorem integrable_euclideanHeatKernel {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec d => euclideanHeatKernel t x) volume := by
  have hprod := integrable_prod_heat d ht
  simp only [euclideanHeatKernel_eq_prod]
  exact hprod.const_mul _

/-- The heat kernel integrates to one for `t > 0`. -/
theorem integral_euclideanHeatKernel {d : ℕ} {t : ℝ} (ht : 0 < t) :
    ∫ x : Vec d, euclideanHeatKernel t x = 1 := by
  simp only [euclideanHeatKernel_eq_prod]
  rw [integral_const_mul, integral_prod_heat d t, integral_gauss_heat t]
  exact rpow_neg_half_mul_sqrt_pow _ (heatKernel_base_pos ht) d

/-! ### The cubes: measurability, volume, and partition -/

/-- The cubes are Borel sets. -/
theorem measurableSet_heatCube {d : ℕ} (L : ℝ) (z : Fin d → ℤ) :
    MeasurableSet (heatCube L z) := by
  have h : heatCube L z =
      ⋂ i : Fin d, (fun x : Vec d => x i) ⁻¹' Set.Ico (L * z i) (L * (z i + 1)) := by
    ext x
    simp [heatCube]
  rw [h]
  exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ico

/-- The cube is the product of the coordinate intervals. -/
private lemma volume_heatCube {d : ℕ} {L : ℝ} (hL : 0 < L) (z : Fin d → ℤ) :
    volume (heatCube L z) = ENNReal.ofReal (L ^ d) := by
  have hset :
      heatCube L z = Set.pi Set.univ fun i : Fin d => Set.Ico (L * z i) (L * (z i + 1)) := by
    ext x
    simp [heatCube, Set.mem_pi]
  have hdiff : ∀ i : Fin d,
      ENNReal.ofReal (L * ((z i : ℝ) + 1) - L * (z i : ℝ)) = ENNReal.ofReal L := by
    intro i
    congr 1
    ring
  rw [hset, Real.volume_pi_Ico]
  simp only [hdiff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hL.le]

/-- The floor of `x i / L` recovers the index of a cube containing `x`. -/
private lemma floor_div_eq_of_mem_heatCube {d : ℕ} {L : ℝ} (hL : 0 < L) {z : Fin d → ℤ}
    {x : Vec d} (hx : x ∈ heatCube L z) (i : Fin d) : ⌊x i / L⌋ = z i := by
  obtain ⟨h1, h2⟩ := mem_heatCube_iff.mp hx i
  rw [Int.floor_eq_iff, le_div_iff₀ hL, div_lt_iff₀ hL]
  exact ⟨(mul_comm _ _).trans_le h1, h2.trans_eq (mul_comm _ _)⟩

/-- Every point lies in the cube indexed by the floors of its scaled coordinates. -/
private lemma mem_heatCube_floor {d : ℕ} {L : ℝ} (hL : 0 < L) (x : Vec d) :
    x ∈ heatCube L (fun i => ⌊x i / L⌋) := by
  refine mem_heatCube_iff.mpr fun i => ⟨?_, ?_⟩
  · exact (mul_comm _ _).trans_le ((le_div_iff₀ hL).mp (Int.floor_le (x i / L)))
  · exact ((div_lt_iff₀ hL).mp (Int.lt_floor_add_one (x i / L))).trans_eq (mul_comm _ _)

/-- Distinct indices give disjoint cubes. -/
theorem pairwise_disjoint_heatCube {d : ℕ} {L : ℝ} (hL : 0 < L) :
    Pairwise fun z w : Fin d → ℤ => Disjoint (heatCube L z) (heatCube L w) := by
  intro z w hzw
  refine Set.disjoint_left.mpr fun x hz hw => hzw ?_
  funext i
  exact (floor_div_eq_of_mem_heatCube hL hz i).symm.trans
    (floor_div_eq_of_mem_heatCube hL hw i)

/-- The cubes cover `Vec d`. -/
theorem iUnion_heatCube {d : ℕ} {L : ℝ} (hL : 0 < L) :
    ⋃ z : Fin d → ℤ, heatCube L z = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.mpr ⟨fun i => ⌊x i / L⌋, mem_heatCube_floor hL x⟩

/-! ### Masses of the cubes -/

/-- Each cube mass is nonnegative. -/
theorem heatCubeMass_nonneg {d : ℕ} (L : ℝ) {t : ℝ} (ht : 0 < t) (z : Fin d → ℤ) :
    0 ≤ heatCubeMass L t z := by
  unfold heatCubeMass
  exact setIntegral_nonneg (measurableSet_heatCube L z) fun x _ =>
    euclideanHeatKernel_nonneg ht x

/-- The masses of the cubes sum to one. -/
theorem hasSum_heatCubeMass {d : ℕ} {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    HasSum (heatCubeMass (d := d) L t) 1 := by
  have hint : IntegrableOn (fun x : Vec d => euclideanHeatKernel t x)
      (⋃ z : Fin d → ℤ, heatCube L z) volume := by
    rw [iUnion_heatCube hL]
    exact (integrable_euclideanHeatKernel ht).integrableOn
  have h := hasSum_integral_iUnion (fun z : Fin d → ℤ => measurableSet_heatCube L z)
    (pairwise_disjoint_heatCube hL) hint
  rw [iUnion_heatCube hL, Measure.restrict_univ, integral_euclideanHeatKernel ht] at h
  exact h

/-- Each cube mass is at most one. -/
theorem heatCubeMass_le_one {d : ℕ} {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (z : Fin d → ℤ) :
    heatCubeMass L t z ≤ 1 :=
  le_hasSum (hasSum_heatCubeMass (d := d) hL ht) z fun j _ => heatCubeMass_nonneg L ht j

/-- Each cube mass is at most the kernel value at the origin times the cube volume. -/
theorem heatCubeMass_le_volume_bound {d : ℕ} {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (z : Fin d → ℤ) :
    heatCubeMass L t z ≤ L ^ d * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
  have hvol : volume (heatCube L z) = ENNReal.ofReal (L ^ d) := volume_heatCube hL z
  have hfin : volume (heatCube L z) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  unfold heatCubeMass
  calc ∫ x in heatCube L z, euclideanHeatKernel t x
      ≤ ∫ _ in heatCube L z, (4 * Real.pi * t) ^ (-(d : ℝ) / 2) :=
        setIntegral_mono_on (integrable_euclideanHeatKernel ht).integrableOn
          (integrableOn_const hfin) (measurableSet_heatCube L z)
          fun x _ => euclideanHeatKernel_le_value ht x
    _ = L ^ d * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
        rw [setIntegral_const, measureReal_def, hvol,
          ENNReal.toReal_ofReal (pow_nonneg hL.le d), smul_eq_mul]

/-- Rewrite a power with exponent `-d/2` as the inverse of the power with exponent `d/2`. -/
private lemma rpow_neg_half_eq_inv {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    x ^ (-(d : ℝ) / 2) = (x ^ ((d : ℝ) / 2))⁻¹ := by
  rw [neg_div, Real.rpow_neg hx]

/-- The uniform bound `C (1 + t) ^ (-d/2)` on the cube masses. -/
theorem exists_heatCubeMass_le {d : ℕ} {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ z : Fin d → ℤ,
      heatCubeMass L t z ≤ C * (1 + t) ^ (-(d : ℝ) / 2) := by
  refine ⟨L ^ d + (2 : ℝ) ^ ((d : ℝ) / 2),
    add_nonneg (pow_nonneg hL.le d) (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro t ht z
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hLd : 0 ≤ L ^ d := pow_nonneg hL.le d
  have hpos : 0 < 1 + t := by linarith
  rcases le_total t 1 with ht1 | ht1
  · -- For `t ≤ 1` the mass is at most one, and `(1 + t) ^ (-d/2) ≥ 2 ^ (-d/2)`.
    have hu : 0 < (1 + t) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hpos _
    have hus : (1 + t) ^ ((d : ℝ) / 2) ≤ (2 : ℝ) ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow hpos.le (by linarith) (by positivity)
    rw [rpow_neg_half_eq_inv hpos.le d]
    calc heatCubeMass L t z ≤ 1 := heatCubeMass_le_one hL ht z
      _ = (1 + t) ^ ((d : ℝ) / 2) * ((1 + t) ^ ((d : ℝ) / 2))⁻¹ :=
          (mul_inv_cancel₀ hu.ne').symm
      _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * ((1 + t) ^ ((d : ℝ) / 2))⁻¹ :=
          mul_le_mul_of_nonneg_right hus (inv_nonneg.mpr hu.le)
      _ ≤ (L ^ d + (2 : ℝ) ^ ((d : ℝ) / 2)) * ((1 + t) ^ ((d : ℝ) / 2))⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hu.le)
  · -- For `1 ≤ t` we have `1 + t ≤ 4 π t`, so the volume bound gives the claim.
    have hpi : 3 * t ≤ Real.pi * t :=
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le ht.le
    have hle : 1 + t ≤ 4 * Real.pi * t := by linarith
    have hexp : -(d : ℝ) / 2 ≤ 0 := by linarith
    have hpow : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) ≤ (1 + t) ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hpos hle hexp
    calc heatCubeMass L t z ≤ L ^ d * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) :=
          heatCubeMass_le_volume_bound hL ht z
      _ ≤ L ^ d * (1 + t) ^ (-(d : ℝ) / 2) := mul_le_mul_of_nonneg_left hpow hLd
      _ ≤ (L ^ d + (2 : ℝ) ^ ((d : ℝ) / 2)) * (1 + t) ^ (-(d : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hpos.le _)

/-- Summability of the squared cube masses, and the bound
`∑ w_z ^ 2 ≤ max_z w_z ≤ C (1 + t) ^ (-d/2)`, for any constant `C` bounding every mass. -/
theorem tsum_sq_heatCubeMass_le {d : ℕ} {L C : ℝ} (hL : 0 < L)
    (hC : ∀ t : ℝ, 0 < t → ∀ z : Fin d → ℤ, heatCubeMass L t z ≤ C * (1 + t) ^ (-(d : ℝ) / 2))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun z : Fin d → ℤ => heatCubeMass L t z ^ 2) ∧
      ∑' z : Fin d → ℤ, heatCubeMass L t z ^ 2 ≤ C * (1 + t) ^ (-(d : ℝ) / 2) := by
  have hw : HasSum (heatCubeMass (d := d) L t) 1 := hasSum_heatCubeMass hL ht
  have hM : HasSum (fun z : Fin d → ℤ => heatCubeMass L t z * (C * (1 + t) ^ (-(d : ℝ) / 2)))
      (1 * (C * (1 + t) ^ (-(d : ℝ) / 2))) := hw.mul_right _
  have hle : ∀ z : Fin d → ℤ, heatCubeMass L t z ^ 2 ≤
      heatCubeMass L t z * (C * (1 + t) ^ (-(d : ℝ) / 2)) := by
    intro z
    rw [sq]
    exact mul_le_mul_of_nonneg_left (hC t ht z) (heatCubeMass_nonneg L ht z)
  have hsum : Summable (fun z : Fin d → ℤ => heatCubeMass L t z ^ 2) :=
    Summable.of_nonneg_of_le (fun z => sq_nonneg _) hle hM.summable
  refine ⟨hsum, ?_⟩
  have h := hasSum_le hle hsum.hasSum hM
  rwa [one_mul] at h

/-- The uniform bound on the squared cube masses, with an explicit constant. -/
theorem exists_tsum_sq_heatCubeMass_le {d : ℕ} {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Summable (fun z : Fin d → ℤ => heatCubeMass L t z ^ 2) ∧
        ∑' z : Fin d → ℤ, heatCubeMass L t z ^ 2 ≤ C * (1 + t) ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_heatCubeMass_le (d := d) hL
  exact ⟨C, hC0, fun t ht => tsum_sq_heatCubeMass_le hL hC ht⟩

end EinsteinRelation.Clock
