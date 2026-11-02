import EinsteinFull.Calculus.S1VectorL2Support
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Geometric summation of covariance increments. These lemmas need no
measurability of the underlying random vectors. -/

open Filter Topology MeasureTheory

namespace EinsteinFull.Calculus.C10

theorem abs_entry_le_frob {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a b : ι) : |A a b| ≤ S1.frob A := by
  apply Real.abs_le_sqrt
  exact (Finset.single_le_sum (fun j _ => sq_nonneg (A a j))
    (Finset.mem_univ b)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j))
        (Finset.mem_univ a))

/-- An eventual geometric increment bound determines the actual `limUnder`.
The finitely many initial terms need no bound. -/
theorem tendsto_limUnder_of_geometric_increments (f : ℕ → ℝ) (C r : ℝ)
    (hr : r < 1) (N : ℕ)
    (h : ∀ n, N ≤ n → |f (n + 1) - f n| ≤ C * r ^ n) :
    Tendsto f atTop (nhds (limUnder atTop f)) := by
  have hs : ∀ n, dist (f (n + N)) (f (n + 1 + N)) ≤ (C * r ^ N) * r ^ n := by
    intro n
    have hn := h (n + N) (Nat.le_add_left N n)
    rw [show n + N + 1 = n + 1 + N by omega, pow_add] at hn
    simpa only [Real.dist_eq, abs_sub_comm, mul_assoc, mul_comm, mul_left_comm] using hn
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric r (C * r ^ N) hr hs)
  exact tendsto_nhds_limUnder ⟨a, (tendsto_add_atTop_iff_nat N).1 ha⟩

/-- Quantitative tail bound with the original geometric coefficient, even
when the increment estimate starts only at `N`. -/
theorem abs_sub_limUnder_le_of_geometric_increments (f : ℕ → ℝ) (C r : ℝ)
    (hr : r < 1) (N : ℕ)
    (h : ∀ n, N ≤ n → |f (n + 1) - f n| ≤ C * r ^ n)
    (n : ℕ) (hn : N ≤ n) :
    |f n - limUnder atTop f| ≤ C * r ^ n / (1 - r) := by
  have hs : ∀ k, dist (f (k + N)) (f (k + 1 + N)) ≤ (C * r ^ N) * r ^ k := by
    intro k
    have hk := h (k + N) (Nat.le_add_left N k)
    rw [show k + N + 1 = k + 1 + N by omega, pow_add] at hk
    simpa only [Real.dist_eq, abs_sub_comm, mul_assoc, mul_comm, mul_left_comm] using hk
  have ht := (tendsto_add_atTop_iff_nat N).2
    (tendsto_limUnder_of_geometric_increments f C r hr N h)
  have hb := dist_le_of_le_geometric_of_tendsto r (C * r ^ N) hr hs ht (n - N)
  rw [Nat.sub_add_cancel hn, Real.dist_eq] at hb
  calc
    |f n - limUnder atTop f| ≤ (C * r ^ N) * r ^ (n - N) / (1 - r) := hb
    _ = C * r ^ n / (1 - r) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hn]

theorem frob_le_of_entry_abs {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    {t : ℝ} (ht : 0 ≤ t) (h : ∀ a b, |A a b| ≤ t) :
    S1.frob A ≤ (Fintype.card ι : ℝ) * t := by
  apply (Real.sqrt_le_iff).2
  refine ⟨mul_nonneg (Nat.cast_nonneg _) ht, ?_⟩
  calc
    ∑ a, ∑ b, A a b ^ 2 ≤ ∑ _a : ι, ∑ _b : ι, t ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      nlinarith [h a b, abs_nonneg (A a b), sq_abs (A a b)]
    _ = ((Fintype.card ι : ℝ) * t) ^ 2 := by simp; ring

theorem tendsto_frob {ι : Type*} [Fintype ι] {M : ℕ → Matrix ι ι ℝ}
    {A : Matrix ι ι ℝ} (h : ∀ a b, Tendsto (fun n => M n a b) atTop (nhds (A a b))) :
    Tendsto (fun n => S1.frob (M n)) atTop (nhds (S1.frob A)) := by
  apply Real.continuous_sqrt.continuousAt.tendsto.comp
  exact tendsto_finset_sum _ fun a _ => tendsto_finset_sum _ fun b _ => (h a b).pow 2

theorem vl2_sub_comm {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (U V : Ω → ι → ℝ) :
    S1.vl2 μ (fun ω => U ω - V ω) = S1.vl2 μ (fun ω => V ω - U ω) := by
  have he (a b : ℝ) : (a - b) ^ 2 = (b - a) ^ 2 := by ring
  simp only [S1.vl2, S1.vsize, Pi.sub_apply, he]

theorem vl2_le_add_sub {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {U V : Ω → ι → ℝ} (hU : S1.L2Vec μ U) (hV : S1.L2Vec μ V) :
    S1.vl2 μ U ≤ S1.vl2 μ V + S1.vl2 μ (fun ω => U ω - V ω) := by
  have he : (fun ω => V ω + (U ω - V ω)) = U := by ext ω a; simp
  simpa only [he] using S1.vl2_add_le hV (hU.sub hV)

theorem covariance_quadratic_integral {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {X : Ω → ι → ℝ} (hX : S1.L2Vec μ X) (x : ι → ℝ) :
    ∑ a, ∑ b, x a * S1.covMat μ X a b * x b =
      ∫ ω, (∑ a, x a * X ω a) ^ 2 ∂μ := by
  have hi : ∀ a b, Integrable (fun ω => x a * (X ω a * X ω b) * x b) μ :=
    fun a b => (((hX.coord_memLp a).integrable_mul (hX.coord_memLp b)).const_mul _).mul_const _
  have he : ∀ ω, (∑ a, x a * X ω a) ^ 2 =
      ∑ a, ∑ b, x a * (X ω a * X ω b) * x b := by
    intro ω
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hi a b)]
  simp_rw [integral_finset_sum _ (fun b _ => hi _ b), integral_mul_const, integral_const_mul]
  rfl

theorem covMat_posSemidef {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {X : Ω → ι → ℝ} (hX : S1.L2Vec μ X) :
    (S1.covMat μ X).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial, S1.covMat, mul_comm]
  · intro x
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
      mul_assoc] using
      (show 0 ≤ ∑ a, ∑ b, x a * S1.covMat μ X a b * x b by
        rw [covariance_quadratic_integral hX x]
        exact integral_nonneg fun ω => sq_nonneg _)

theorem posSemidef_of_entrywise_tendsto {ι : Type*} [Fintype ι]
    {M : ℕ → Matrix ι ι ℝ} {A : Matrix ι ι ℝ}
    (h : ∀ a b, Tendsto (fun n => M n a b) atTop (nhds (A a b)))
    (hp : ∀ᶠ n in atTop, (M n).PosSemidef) : A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial]
    apply tendsto_nhds_unique (h b a)
    apply (h a b).congr'
    filter_upwards [hp] with n hn
    have he := congrArg (fun B : Matrix ι ι ℝ => B a b) hn.1
    simpa only [Matrix.conjTranspose_apply, star_trivial] using he.symm
  · intro x
    have ht := tendsto_finset_sum Finset.univ fun a _ =>
      tendsto_finset_sum Finset.univ fun b _ => ((h a b).const_mul (x a)).mul_const (x b)
    have hp' : ∀ᶠ n in atTop, 0 ≤ ∑ a, ∑ b, x a * M n a b * x b := by
      filter_upwards [hp] with n hn
      simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        Finset.mul_sum, mul_assoc] using hn.dotProduct_mulVec_nonneg x
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc] using ge_of_tendsto ht hp'

end EinsteinFull.Calculus.C10
