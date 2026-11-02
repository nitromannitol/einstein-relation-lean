import EinsteinFull.Calculus.S1ClosureArithmeticSupport

/-! Mean-square calculus for finite-dimensional random vectors with the Euclidean size
`vsize v = √(∑ a, v a ^ 2)`: triangle inequality, finite sums and scalar multiples, and
the Frobenius bound for the difference of two second-moment matrices. The definitions
agree with `covarianceVectorSize`, `covarianceL2Size`, `covarianceBlockMatrix` and
`covarianceMatrixSize` by unfolding. -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]

/-- The Euclidean size of a finite real vector. -/
noncomputable def vsize (v : ι → ℝ) : ℝ := Real.sqrt (∑ a, v a ^ 2)

/-- The `L²(μ)` size of a vector-valued function. -/
noncomputable def vl2 (μ : Measure Ω) (v : Ω → ι → ℝ) : ℝ :=
  Real.sqrt (∫ ω, vsize (v ω) ^ 2 ∂μ)

/-- The second-moment matrix of a vector-valued function. -/
noncomputable def covMat (μ : Measure Ω) (v : Ω → ι → ℝ) : Matrix ι ι ℝ :=
  fun a b => ∫ ω, v ω a * v ω b ∂μ

/-- The Frobenius norm of a square matrix. -/
noncomputable def frob (A : Matrix ι ι ℝ) : ℝ := Real.sqrt (∑ a, ∑ b, A a b ^ 2)

theorem vsize_nonneg (v : ι → ℝ) : 0 ≤ vsize v := Real.sqrt_nonneg _

theorem vsize_eq_norm (v : ι → ℝ) : vsize v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

theorem vsize_add_le (u v : ι → ℝ) : vsize (u + v) ≤ vsize u + vsize v := by
  rw [vsize_eq_norm, vsize_eq_norm, vsize_eq_norm]
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℝ ι) (WithLp.toLp 2 v)

theorem vsize_smul (c : ℝ) (v : ι → ℝ) : vsize (c • v) = |c| * vsize v := by
  rw [vsize_eq_norm, vsize_eq_norm]
  have := norm_smul c (WithLp.toLp 2 v : EuclideanSpace ℝ ι)
  rw [Real.norm_eq_abs] at this
  exact this

theorem vsize_zero : vsize (0 : ι → ℝ) = 0 := by
  simp [vsize]

theorem abs_le_vsize (v : ι → ℝ) (a : ι) : |v a| ≤ vsize v := by
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun a => v a ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ a)

theorem vsize_sq (v : ι → ℝ) : vsize v ^ 2 = ∑ a, v a ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg _)

theorem aestronglyMeasurable_vsize {μ : Measure Ω} {v : Ω → ι → ℝ}
    (h : ∀ a, AEStronglyMeasurable (fun ω => v ω a) μ) :
    AEStronglyMeasurable (fun ω => vsize (v ω)) μ := by
  unfold vsize
  exact Real.continuous_sqrt.comp_aestronglyMeasurable
    (Finset.aestronglyMeasurable_fun_sum _ fun a _ =>
      (continuous_pow 2).comp_aestronglyMeasurable (h a))

/-- A random vector with measurable coordinates and square-integrable Euclidean size. -/
structure L2Vec (μ : Measure Ω) (v : Ω → ι → ℝ) : Prop where
  coord_meas : ∀ a, AEStronglyMeasurable (fun ω => v ω a) μ
  size_memLp : MemLp (fun ω => vsize (v ω)) 2 μ

theorem L2Vec.coord_memLp {μ : Measure Ω} {v : Ω → ι → ℝ} (h : L2Vec μ v) (a : ι) :
    MemLp (fun ω => v ω a) 2 μ :=
  h.size_memLp.mono (h.coord_meas a) (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (vsize_nonneg _)]
    exact abs_le_vsize _ a)

theorem L2Vec.add {μ : Measure Ω} {u v : Ω → ι → ℝ} (hu : L2Vec μ u) (hv : L2Vec μ v) :
    L2Vec μ (fun ω => u ω + v ω) := by
  refine ⟨fun a => (hu.coord_meas a).add (hv.coord_meas a), ?_⟩
  have hm : AEStronglyMeasurable (fun ω => vsize ((fun ω => u ω + v ω) ω)) μ :=
    aestronglyMeasurable_vsize fun a => (hu.coord_meas a).add (hv.coord_meas a)
  exact (hu.size_memLp.add hv.size_memLp).mono hm (Filter.Eventually.of_forall fun ω => by
    show ‖vsize (u ω + v ω)‖ ≤ ‖vsize (u ω) + vsize (v ω)‖
    rw [Real.norm_of_nonneg (vsize_nonneg _), Real.norm_of_nonneg
      (add_nonneg (vsize_nonneg _) (vsize_nonneg _))]
    exact vsize_add_le _ _)

theorem L2Vec.smul {μ : Measure Ω} {u : Ω → ι → ℝ} (hu : L2Vec μ u) (c : ℝ) :
    L2Vec μ (fun ω => c • u ω) := by
  refine ⟨fun a => (hu.coord_meas a).const_smul c, ?_⟩
  have : (fun ω => vsize ((fun ω => c • u ω) ω)) = fun ω => |c| * vsize (u ω) := by
    funext ω
    exact vsize_smul c _
  rw [this]
  exact hu.size_memLp.const_mul |c|

theorem L2Vec.sub {μ : Measure Ω} {u v : Ω → ι → ℝ} (hu : L2Vec μ u) (hv : L2Vec μ v) :
    L2Vec μ (fun ω => u ω - v ω) := by
  have h : L2Vec μ (fun ω => u ω + (-1 : ℝ) • v ω) := hu.add (hv.smul (-1))
  have e : (fun ω => u ω + (-1 : ℝ) • v ω) = fun ω => u ω - v ω := by
    funext ω
    simp [sub_eq_add_neg]
  rw [e] at h
  exact h

theorem L2Vec.zero {μ : Measure Ω} : L2Vec μ (fun _ : Ω => (0 : ι → ℝ)) := by
  refine ⟨fun a => aestronglyMeasurable_const, ?_⟩
  simp only [vsize_zero]
  exact MemLp.zero

theorem L2Vec.sum {κ : Type*} {μ : Measure Ω} (S : Finset κ) {u : κ → Ω → ι → ℝ}
    (hu : ∀ j, L2Vec μ (u j)) : L2Vec μ (fun ω => ∑ j ∈ S, u j ω) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (L2Vec.zero : L2Vec μ (fun _ : Ω => (0 : ι → ℝ)))
  | insert j S hj ih =>
    have := (hu j).add ih
    simpa only [Finset.sum_insert hj] using this

theorem vl2_eq_l2Size (μ : Measure Ω) (v : Ω → ι → ℝ) :
    vl2 μ v = S1.l2Size μ (fun ω => vsize (v ω)) := by
  unfold vl2 S1.l2Size
  have : ∀ ω, ‖vsize (v ω)‖ = vsize (v ω) := fun ω => Real.norm_of_nonneg (vsize_nonneg _)
  simp only [this]

theorem vl2_nonneg (μ : Measure Ω) (v : Ω → ι → ℝ) : 0 ≤ vl2 μ v := Real.sqrt_nonneg _

theorem vl2_add_le {μ : Measure Ω} {u v : Ω → ι → ℝ} (hu : L2Vec μ u) (hv : L2Vec μ v) :
    vl2 μ (fun ω => u ω + v ω) ≤ vl2 μ u + vl2 μ v := by
  have hs : MemLp (fun ω => vsize (u ω) + vsize (v ω)) 2 μ :=
    hu.size_memLp.add hv.size_memLp
  have h1 : ∫ ω, vsize (u ω + v ω) ^ 2 ∂μ ≤ ∫ ω, (vsize (u ω) + vsize (v ω)) ^ 2 ∂μ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact hs.integrable_sq
    · exact pow_le_pow_left₀ (vsize_nonneg _) (vsize_add_le _ _) 2
  calc vl2 μ (fun ω => u ω + v ω)
      = Real.sqrt (∫ ω, vsize (u ω + v ω) ^ 2 ∂μ) := rfl
    _ ≤ Real.sqrt (∫ ω, (vsize (u ω) + vsize (v ω)) ^ 2 ∂μ) := Real.sqrt_le_sqrt h1
    _ = S1.l2Size μ ((fun ω => vsize (u ω)) + fun ω => vsize (v ω)) := by
        unfold S1.l2Size
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only [Pi.add_apply, Real.norm_eq_abs, sq_abs]
    _ ≤ S1.l2Size μ (fun ω => vsize (u ω)) + S1.l2Size μ (fun ω => vsize (v ω)) :=
        S1.l2Size_add_le hu.size_memLp hv.size_memLp
    _ = vl2 μ u + vl2 μ v := by rw [vl2_eq_l2Size, vl2_eq_l2Size]

theorem vl2_smul (μ : Measure Ω) (u : Ω → ι → ℝ) (c : ℝ) :
    vl2 μ (fun ω => c • u ω) = |c| * vl2 μ u := by
  unfold vl2
  have : ∀ ω, vsize (c • u ω) ^ 2 = c ^ 2 * vsize (u ω) ^ 2 := fun ω => by
    rw [vsize_smul, mul_pow, sq_abs]
  simp only [this]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem vl2_sum_le {κ : Type*} {μ : Measure Ω} (S : Finset κ) {u : κ → Ω → ι → ℝ}
    (hu : ∀ j, L2Vec μ (u j)) :
    vl2 μ (fun ω => ∑ j ∈ S, u j ω) ≤ ∑ j ∈ S, vl2 μ (u j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [vl2, vsize_zero]
  | insert j S hj ih =>
    have h := vl2_add_le (hu j) (L2Vec.sum S hu)
    simp only [Finset.sum_insert hj]
    exact h.trans (add_le_add le_rfl ih)

/-! ### Frobenius bound for second-moment matrices -/

theorem abs_double_sum_le (A : ι → ι → ℝ) (u v : ι → ℝ) :
    |∑ a, ∑ b, u a * A a b * v b| ≤
      Real.sqrt (∑ a, ∑ b, A a b ^ 2) * (vsize u * vsize v) := by
  have hF : 0 ≤ ∑ a, ∑ b, A a b ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hs := sum_sq_mulVec_le (fun a b => |A a b|) (fun b => |v b|)
  simp only [sq_abs] at hs
  calc |∑ a, ∑ b, u a * A a b * v b|
      ≤ ∑ a, |∑ b, u a * A a b * v b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |u a| * ∑ b, |A a b| * |v b| := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_mul]
        exact le_of_eq (mul_assoc _ _ _)
    _ ≤ Real.sqrt (∑ a, |u a| ^ 2) * Real.sqrt (∑ a, (∑ b, |A a b| * |v b|) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ a, |u a| ^ 2) *
          Real.sqrt ((∑ a, ∑ b, A a b ^ 2) * ∑ b, v b ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ a, ∑ b, A a b ^ 2) * (vsize u * vsize v) := by
        rw [Real.sqrt_mul hF]
        simp only [vsize, sq_abs]
        ring

theorem frob_cross_le {μ : Measure Ω} {P Q : Ω → ι → ℝ}
    (hP : L2Vec μ P) (hQ : L2Vec μ Q) :
    frob (fun a b => ∫ ω, P ω a * Q ω b ∂μ) ≤ vl2 μ P * vl2 μ Q := by
  set M : ι → ι → ℝ := fun a b => ∫ ω, P ω a * Q ω b ∂μ with hM
  have hMint : ∀ a b, Integrable (fun ω => P ω a * Q ω b) μ := fun a b =>
    (hP.coord_memLp a).integrable_mul (hQ.coord_memLp b)
  have hFnn : 0 ≤ frob M := Real.sqrt_nonneg _
  have hint_ab : ∀ a b, Integrable (fun ω => P ω a * M a b * Q ω b) μ := fun a b =>
    ((hMint a b).const_mul (M a b)).congr (Filter.Eventually.of_forall fun ω =>
      (by ring : M a b * (P ω a * Q ω b) = P ω a * M a b * Q ω b))
  have hinner : ∀ a, Integrable (fun ω => ∑ b, P ω a * M a b * Q ω b) μ := fun a =>
    integrable_finset_sum _ fun b _ => hint_ab a b
  have hterm : ∀ a b, M a b ^ 2 = ∫ ω, P ω a * M a b * Q ω b ∂μ := by
    intro a b
    have : ∫ ω, P ω a * M a b * Q ω b ∂μ = M a b * ∫ ω, P ω a * Q ω b ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (by ring : P ω a * M a b * Q ω b = M a b * (P ω a * Q ω b)))
    rw [this, sq]
  have hF2 : frob M ^ 2 = ∫ ω, ∑ a, ∑ b, P ω a * M a b * Q ω b ∂μ := by
    calc frob M ^ 2 = ∑ a, ∑ b, M a b ^ 2 :=
          Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
      _ = ∑ a, ∑ b, ∫ ω, P ω a * M a b * Q ω b ∂μ :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
      _ = ∫ ω, ∑ a, ∑ b, P ω a * M a b * Q ω b ∂μ := by
          rw [integral_finset_sum _ (fun a _ => hinner a)]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [integral_finset_sum _ (fun b _ => hint_ab a b)]
  have hpt : ∀ ω, ∑ a, ∑ b, P ω a * M a b * Q ω b ≤
      frob M * (vsize (P ω) * vsize (Q ω)) := fun ω =>
    (le_abs_self _).trans (abs_double_sum_le M (P ω) (Q ω))
  have hint1 : Integrable (fun ω => ∑ a, ∑ b, P ω a * M a b * Q ω b) μ :=
    integrable_finset_sum _ fun a _ => hinner a
  have hsizeint : Integrable (fun ω => vsize (P ω) * vsize (Q ω)) μ :=
    hP.size_memLp.integrable_mul hQ.size_memLp
  have h1 : frob M ^ 2 ≤ frob M * (vl2 μ P * vl2 μ Q) := by
    rw [hF2]
    calc ∫ ω, ∑ a, ∑ b, P ω a * M a b * Q ω b ∂μ
        ≤ ∫ ω, frob M * (vsize (P ω) * vsize (Q ω)) ∂μ :=
          integral_mono hint1 (hsizeint.const_mul _) hpt
      _ = frob M * ∫ ω, vsize (P ω) * vsize (Q ω) ∂μ := integral_const_mul _ _
      _ ≤ frob M * (vl2 μ P * vl2 μ Q) := by
          refine mul_le_mul_of_nonneg_left ?_ hFnn
          rw [vl2_eq_l2Size, vl2_eq_l2Size]
          exact S1.integral_mul_le_l2Size_real hP.size_memLp hQ.size_memLp
  by_cases h0 : frob M = 0
  · rw [h0]
    exact mul_nonneg (vl2_nonneg _ _) (vl2_nonneg _ _)
  · have hpos : 0 < frob M := lt_of_le_of_ne hFnn (Ne.symm h0)
    refine le_of_mul_le_mul_left ?_ hpos
    nlinarith [h1]

theorem frob_add_le (A B : Matrix ι ι ℝ) : frob (A + B) ≤ frob A + frob B := by
  have e : ∀ C : Matrix ι ι ℝ, frob C = vsize (fun p : ι × ι => C p.1 p.2) := by
    intro C
    show Real.sqrt (∑ a, ∑ b, C a b ^ 2) = Real.sqrt (∑ p : ι × ι, C p.1 p.2 ^ 2)
    exact congrArg Real.sqrt (Fintype.sum_prod_type' (f := fun a b => C a b ^ 2)).symm
  rw [e, e, e]
  exact vsize_add_le (fun p : ι × ι => A p.1 p.2) (fun p : ι × ι => B p.1 p.2)

/-- The Frobenius distance of two second-moment matrices is controlled by the
mean-square distance of the vectors and their sizes. -/
theorem frob_covMat_sub_le {μ : Measure Ω} {U V : Ω → ι → ℝ}
    (hU : L2Vec μ U) (hV : L2Vec μ V) :
    frob (covMat μ U - covMat μ V) ≤ vl2 μ (fun ω => U ω - V ω) * (vl2 μ U + vl2 μ V) := by
  have hD : L2Vec μ (fun ω => U ω - V ω) := hU.sub hV
  have e : covMat μ U - covMat μ V =
      ((fun a b => ∫ ω, (U ω - V ω) a * U ω b ∂μ : Matrix ι ι ℝ) +
        (fun a b => ∫ ω, V ω a * (U ω - V ω) b ∂μ : Matrix ι ι ℝ)) := by
    ext a b
    have i1 : Integrable (fun ω => U ω a * U ω b) μ :=
      (hU.coord_memLp a).integrable_mul (hU.coord_memLp b)
    have i2 : Integrable (fun ω => V ω a * V ω b) μ :=
      (hV.coord_memLp a).integrable_mul (hV.coord_memLp b)
    have i3 : Integrable (fun ω => (U ω - V ω) a * U ω b) μ :=
      ((hU.coord_memLp a).sub (hV.coord_memLp a)).integrable_mul (hU.coord_memLp b)
    have i4 : Integrable (fun ω => V ω a * (U ω - V ω) b) μ :=
      (hV.coord_memLp a).integrable_mul ((hU.coord_memLp b).sub (hV.coord_memLp b))
    show (∫ ω, U ω a * U ω b ∂μ) - ∫ ω, V ω a * V ω b ∂μ =
      (∫ ω, (U ω - V ω) a * U ω b ∂μ) + ∫ ω, V ω a * (U ω - V ω) b ∂μ
    rw [← integral_sub i1 i2, ← integral_add i3 i4]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (by simp only [Pi.sub_apply]; ring :
        U ω a * U ω b - V ω a * V ω b =
          (U ω - V ω) a * U ω b + V ω a * (U ω - V ω) b))
  rw [e]
  refine (frob_add_le _ _).trans ?_
  have h1 := frob_cross_le hD hU
  have h2 := frob_cross_le hV hD
  nlinarith [h1, h2, vl2_nonneg μ (fun ω => U ω - V ω), vl2_nonneg μ U, vl2_nonneg μ V]

end EinsteinFull.Calculus.S1
