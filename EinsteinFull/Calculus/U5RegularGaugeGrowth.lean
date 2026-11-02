import MarkovProcess.Semigroup.ExponentialComparison
import EinsteinFull.Calculus.U5RegularKernelInvariance
import EinsteinFull.Calculus.U2GMPEnvironmentRealization
import EinsteinFull.Calculus.C16SourceExponentialMax
import EinsteinRelation.Environment.SourceReducedBoundSupport

noncomputable section

namespace EinsteinFull

open EinsteinRelation MeasureTheory ProbabilityTheory Blueprint
open EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet
open scoped ENNReal NNReal Topology

/-- Derivatives of a dilated compact test vanish uniformly as the dilation tends to zero. -/
theorem u5_dilated_cutoff_derivative_bound {d : ℕ} {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ (y : Vec d) (i j : Fin d),
      |fderiv ℝ (fun z => χ (c • z)) y (unitVector j)| ≤ c * M ∧
      |fderiv ℝ (fun z => fderiv ℝ (fun z => χ (c • z)) z (unitVector j)) y
        (unitVector i)| ≤ c * M := by
  have hF : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun w => fderiv ℝ χ w (unitVector j)) :=
    fun j => (hχ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have h1 : ∀ j : Fin d, ∃ B : ℝ, ∀ w, |fderiv ℝ χ w (unitVector j)| ≤ B := fun j => by
    obtain ⟨B, hB⟩ := (hF j).continuous.bounded_above_of_compact_support
      (hc.fderiv_apply ℝ (unitVector j))
    exact ⟨B, fun w => by simpa only [Real.norm_eq_abs] using hB w⟩
  have h2 : ∀ i j : Fin d, ∃ B : ℝ, ∀ w,
      |fderiv ℝ (fun w => fderiv ℝ χ w (unitVector j)) w (unitVector i)| ≤ B := fun i j => by
    have hcs : HasCompactSupport (fun w => fderiv ℝ χ w (unitVector j)) :=
      hc.fderiv_apply ℝ (unitVector j)
    have hcont : Continuous (fun w => fderiv ℝ (fun w => fderiv ℝ χ w (unitVector j)) w
        (unitVector i)) :=
      ((hF j).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.clm_apply continuous_const
    obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support (hcs.fderiv_apply ℝ (unitVector i))
    exact ⟨B, fun w => by simpa only [Real.norm_eq_abs] using hB w⟩
  choose B1 hB1 using h1
  choose B2 hB2 using h2
  let M := ∑ j, |B1 j| + ∑ i, ∑ j, |B2 i j|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, fun c hc0 hc1 y i j => ?_⟩
  have hs1 : |B1 j| ≤ M := by
    dsimp [M]
    have h := Finset.single_le_sum (f := fun j => |B1 j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have hn : 0 ≤ ∑ i, ∑ j, |B2 i j| := by positivity
    linarith
  have hs2 : |B2 i j| ≤ M := by
    dsimp [M]
    have h := (Finset.single_le_sum (f := fun j => |B2 i j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |B2 i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    have hn : 0 ≤ ∑ j, |B1 j| := by positivity
    linarith
  have hfd : ∀ z, fderiv ℝ (fun z => χ (c • z)) z (unitVector j) =
      c * fderiv ℝ χ (c • z) (unitVector j) := fun z => by
    rw [fderiv_comp_smul]; simp
  constructor
  · rw [hfd, abs_mul, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left ((hB1 j _).trans ((le_abs_self _).trans hs1)) hc0.le
  · have heq : (fun z => fderiv ℝ (fun z => χ (c • z)) z (unitVector j)) =
        fun z => c * (fun w => fderiv ℝ χ w (unitVector j)) (c • z) := funext hfd
    have hdiff : DifferentiableAt ℝ (fun z => (fun w => fderiv ℝ χ w (unitVector j)) (c • z)) y :=
      (((hF j).differentiable (by simp)).comp (differentiable_id.const_smul c)) y
    have h3 : fderiv ℝ (fun z => (fun w => fderiv ℝ χ w (unitVector j)) (c • z)) y =
        c • fderiv ℝ (fun w => fderiv ℝ χ w (unitVector j)) (c • y) :=
      fderiv_comp_smul (f := fun w => fderiv ℝ χ w (unitVector j)) (x := y) c
    rw [heq, fderiv_const_mul hdiff, h3]
    simp only [smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc0]
    calc
      c * (c * |fderiv ℝ (fun w => fderiv ℝ χ w (unitVector j)) (c • y) (unitVector i)|)
          ≤ c * (c * M) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ((hB2 i j _).trans ((le_abs_self _).trans hs2)) hc0.le) hc0.le
      _ ≤ c * M := mul_le_mul_of_nonneg_left (by nlinarith) hc0.le

/-- The regular generator of a dilated compact cutoff vanishes uniformly with the scale. -/
theorem u5_regular_generator_dilated_cutoff_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ c : ℝ, 0 < c → c ≤ 1 →
        |physicalGenerator (firstCoordinateIndex hd) ω lam (fun z => χ (c • z)) x| ≤ c * D := by
  obtain ⟨M, hM, hder⟩ := u5_dilated_cutoff_derivative_bound hχ hc
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  refine ⟨(C₁ + C₂) * M, by positivity, ?_⟩
  filter_upwards [hgen] with x hx
  intro c hc0 hc1
  have hs : ContDiff ℝ 2 (fun z => χ (c • z)) :=
    (hχ.comp (contDiff_const_smul c)).of_le (WithTop.coe_le_coe.2 le_top)
  have hb := hx _ hs (c * M) (c * M) (mul_nonneg hc0.le hM) (mul_nonneg hc0.le hM)
    (fun j => (hder c hc0 hc1 x j j).1) (fun i j => (hder c hc0 hc1 x i j).2)
  convert hb using 1 <;> ring

/-- Cutting off a bounded relative-derivative test adds a vanishing generator error. -/
theorem u5_regular_generator_cutoff_product_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ h : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (H A B : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ x, 0 ≤ h x ∧ h x ≤ H)
    (hfirst : ∀ x j, |fderiv ℝ h x (unitVector j)| ≤ A * h x)
    (hsecond : ∀ x i j, |fderiv ℝ (fun y => fderiv ℝ h y (unitVector j)) x
      (unitVector i)| ≤ B * h x) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ c : ℝ, 0 < c → c ≤ 1 →
        |physicalGenerator (firstCoordinateIndex hd) ω lam
          (fun z => χ (c • z) * h z) x| ≤ C * (χ (c • x) * h x) + c * D := by
  obtain ⟨M, hM, hder⟩ := u5_dilated_cutoff_derivative_bound hχ hc
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  refine ⟨C₁ * A + C₂ * B, C₁ * (M * H) + C₂ * (M * H + 2 * M * (A * H)),
    by positivity, by positivity, ?_⟩
  filter_upwards [hgen] with x hx
  intro c hc0 hc1
  let f : Vec d → ℝ := fun z => χ (c • z)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hχ.comp (contDiff_const_smul c)
  have hf0 : 0 ≤ f x := (hχ01 (c • x)).1
  have hf1 : f x ≤ 1 := (hχ01 (c • x)).2
  have hh0 : 0 ≤ h x := (hbound x).1
  have hhH : h x ≤ H := (hbound x).2
  have hprod : 0 ≤ f x * h x := mul_nonneg hf0 hh0
  have hD : 0 ≤ c * M := mul_nonneg hc0.le hM
  have hfirst' (i : Fin d) :
      |fderiv ℝ (fun z => f z * h z) x (unitVector i)| ≤
        A * (f x * h x) + c * (M * H) := by
    rw [(gmpPhysical_coordinate_product_derivatives f h hf hh x i i).1]
    have hf' := (hder c hc0 hc1 x i i).1
    change |fderiv ℝ f x (unitVector i)| ≤ c * M at hf'
    have ha := hfirst x i
    have hfa : |fderiv ℝ f x (unitVector i) * h x| ≤ (c * M) * H := by
      rw [abs_mul, abs_of_nonneg hh0]
      exact mul_le_mul hf' hhH hh0 hD
    have hfb : |f x * fderiv ℝ h x (unitVector i)| ≤ f x * (A * h x) := by
      rw [abs_mul, abs_of_nonneg hf0]
      exact mul_le_mul_of_nonneg_left ha hf0
    have := (abs_add_le _ _).trans (add_le_add hfa hfb)
    nlinarith
  have hsecond' (i j : Fin d) :
      |fderiv ℝ (fun y => fderiv ℝ (fun z => f z * h z) y (unitVector j)) x
        (unitVector i)| ≤ B * (f x * h x) + c * (M * H + 2 * M * (A * H)) := by
    rw [(gmpPhysical_coordinate_product_derivatives f h hf hh x i j).2]
    have hfi := (hder c hc0 hc1 x i j).1
    have hfj := (hder c hc0 hc1 x j i).1
    have hfij := (hder c hc0 hc1 x i j).2
    change |fderiv ℝ f x (unitVector j)| ≤ c * M at hfi
    change |fderiv ℝ f x (unitVector i)| ≤ c * M at hfj
    change |fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i)| ≤ c * M at hfij
    have hhj : |fderiv ℝ h x (unitVector j)| ≤ A * H :=
      (hfirst x j).trans (mul_le_mul_of_nonneg_left hhH hA)
    have hhi : |fderiv ℝ h x (unitVector i)| ≤ A * H :=
      (hfirst x i).trans (mul_le_mul_of_nonneg_left hhH hA)
    have h1 : |fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) * h x| ≤ (c * M) * H := by
      rw [abs_mul, abs_of_nonneg hh0]
      exact mul_le_mul hfij hhH hh0 hD
    have h2 : |fderiv ℝ f x (unitVector j) * fderiv ℝ h x (unitVector i)| ≤ (c * M) * (A * H) := by
      rw [abs_mul]
      exact mul_le_mul hfi hhi (abs_nonneg _) hD
    have h3 : |fderiv ℝ f x (unitVector i) * fderiv ℝ h x (unitVector j)| ≤ (c * M) * (A * H) := by
      rw [abs_mul]
      exact mul_le_mul hfj hhj (abs_nonneg _) hD
    have h4 : |f x * fderiv ℝ (fun y => fderiv ℝ h y (unitVector j)) x (unitVector i)| ≤ f x * (B * h x) := by
      rw [abs_mul, abs_of_nonneg hf0]
      exact mul_le_mul_of_nonneg_left (hsecond x i j) hf0
    have ht := (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)
    nlinarith
  have h1 : 0 ≤ A * (f x * h x) + c * (M * H) := by positivity
  have h2 : 0 ≤ B * (f x * h x) + c * (M * H + 2 * M * (A * H)) := by positivity
  have hs : ContDiff ℝ 2 (fun z => f z * h z) :=
    (hf.mul hh).of_le (WithTop.coe_le_coe.2 le_top)
  have hb := hx _ hs _ _ h1 h2 hfirst' hsecond'
  convert hb using 1 <;> ring

/-- The cutoff-product growth constant is independent of the bounded test and its height. -/
theorem u5_regular_generator_cutoff_product_uniform {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (h : Vec d → ℝ) (H : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ H →
      (∀ x, 0 ≤ h x ∧ h x ≤ H) →
      (∀ x j, |fderiv ℝ h x (unitVector j)| ≤ A * h x) →
      (∀ x i j, |fderiv ℝ (fun y => fderiv ℝ h y (unitVector j)) x
        (unitVector i)| ≤ B * h x) →
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ c : ℝ, 0 < c → c ≤ 1 →
        |physicalGenerator (firstCoordinateIndex hd) ω lam
          (fun z => χ (c • z) * h z) x| ≤ C * (χ (c • x) * h x) + c * (E * H) := by
  obtain ⟨M, hM, hder⟩ := u5_dilated_cutoff_derivative_bound hχ hc
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  refine ⟨C₁ * A + C₂ * B, C₁ * M + C₂ * (M + 2 * M * A), by positivity, by positivity, ?_⟩
  intro h H hh hH hbound hfirst hsecond
  filter_upwards [hgen] with x hx
  intro c hc0 hc1
  let f : Vec d → ℝ := fun z => χ (c • z)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hχ.comp (contDiff_const_smul c)
  have hf0 : 0 ≤ f x := (hχ01 (c • x)).1
  have hf1 : f x ≤ 1 := (hχ01 (c • x)).2
  have hh0 : 0 ≤ h x := (hbound x).1
  have hhH : h x ≤ H := (hbound x).2
  have hprod : 0 ≤ f x * h x := mul_nonneg hf0 hh0
  have hD : 0 ≤ c * M := mul_nonneg hc0.le hM
  have hfirst' (i : Fin d) :
      |fderiv ℝ (fun z => f z * h z) x (unitVector i)| ≤
        A * (f x * h x) + c * (M * H) := by
    rw [(gmpPhysical_coordinate_product_derivatives f h hf hh x i i).1]
    have hf' := (hder c hc0 hc1 x i i).1
    change |fderiv ℝ f x (unitVector i)| ≤ c * M at hf'
    have ha := hfirst x i
    have hfa : |fderiv ℝ f x (unitVector i) * h x| ≤ (c * M) * H := by
      rw [abs_mul, abs_of_nonneg hh0]
      exact mul_le_mul hf' hhH hh0 hD
    have hfb : |f x * fderiv ℝ h x (unitVector i)| ≤ f x * (A * h x) := by
      rw [abs_mul, abs_of_nonneg hf0]
      exact mul_le_mul_of_nonneg_left ha hf0
    have := (abs_add_le _ _).trans (add_le_add hfa hfb)
    nlinarith
  have hsecond' (i j : Fin d) :
      |fderiv ℝ (fun y => fderiv ℝ (fun z => f z * h z) y (unitVector j)) x
        (unitVector i)| ≤ B * (f x * h x) + c * (M * H + 2 * M * (A * H)) := by
    rw [(gmpPhysical_coordinate_product_derivatives f h hf hh x i j).2]
    have hfi := (hder c hc0 hc1 x i j).1
    have hfj := (hder c hc0 hc1 x j i).1
    have hfij := (hder c hc0 hc1 x i j).2
    change |fderiv ℝ f x (unitVector j)| ≤ c * M at hfi
    change |fderiv ℝ f x (unitVector i)| ≤ c * M at hfj
    change |fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i)| ≤ c * M at hfij
    have hhj : |fderiv ℝ h x (unitVector j)| ≤ A * H :=
      (hfirst x j).trans (mul_le_mul_of_nonneg_left hhH hA)
    have hhi : |fderiv ℝ h x (unitVector i)| ≤ A * H :=
      (hfirst x i).trans (mul_le_mul_of_nonneg_left hhH hA)
    have h1 : |fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) * h x| ≤ (c * M) * H := by
      rw [abs_mul, abs_of_nonneg hh0]
      exact mul_le_mul hfij hhH hh0 hD
    have h2 : |fderiv ℝ f x (unitVector j) * fderiv ℝ h x (unitVector i)| ≤ (c * M) * (A * H) := by
      rw [abs_mul]
      exact mul_le_mul hfi hhi (abs_nonneg _) hD
    have h3 : |fderiv ℝ f x (unitVector i) * fderiv ℝ h x (unitVector j)| ≤ (c * M) * (A * H) := by
      rw [abs_mul]
      exact mul_le_mul hfj hhj (abs_nonneg _) hD
    have h4 : |f x * fderiv ℝ (fun y => fderiv ℝ h y (unitVector j)) x (unitVector i)| ≤ f x * (B * h x) := by
      rw [abs_mul, abs_of_nonneg hf0]
      exact mul_le_mul_of_nonneg_left (hsecond x i j) hf0
    have ht := (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)
    nlinarith
  have h1 : 0 ≤ A * (f x * h x) + c * (M * H) := by positivity
  have h2 : 0 ≤ B * (f x * h x) + c * (M * H + 2 * M * (A * H)) := by positivity
  have hs : ContDiff ℝ 2 (fun z => f z * h z) :=
    (hf.mul hh).of_le (WithTop.coe_le_coe.2 le_top)
  have hb := hx _ hs _ _ h1 h2 hfirst' hsecond'
  convert hb using 1 <;> ring

#print axioms u5_regular_generator_cutoff_product_uniform

/-- A bounded smooth approximation of the positive exponential. -/
def u5BoundedExp (a t : ℝ) : ℝ := Real.exp t / (1 + a * Real.exp t)

/-- The first two derivatives of the bounded exponential approximation. -/
theorem u5_bounded_exp_derivatives (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    HasDerivAt (u5BoundedExp a) (Real.exp t / (1 + a * Real.exp t) ^ 2) t ∧
    HasDerivAt (fun s => Real.exp s / (1 + a * Real.exp s) ^ 2)
      (Real.exp t * (1 - a * Real.exp t) / (1 + a * Real.exp t) ^ 3) t := by
  have hp : 0 < 1 + a * Real.exp t := by positivity
  have he := Real.hasDerivAt_exp t
  have hd := (he.const_mul a).const_add 1
  constructor
  · have h := he.div hd (ne_of_gt hp)
    convert h using 1 <;> (try simp only [u5BoundedExp, Pi.pow_apply]) <;> field_simp [ne_of_gt hp] <;> ring <;> (try { ext x; rfl })
  · have h := he.div (hd.pow 2) (pow_ne_zero _ (ne_of_gt hp))
    convert h using 1 <;> (try simp only [Pi.pow_apply]) <;> field_simp [ne_of_gt hp] <;> ring

/-- The approximation and both derivatives are controlled by the approximation itself. -/
theorem u5_bounded_exp_bounds (a : ℝ) (ha : 0 < a) (t : ℝ) :
    0 ≤ u5BoundedExp a t ∧ u5BoundedExp a t ≤ a⁻¹ ∧
    Real.exp t / (1 + a * Real.exp t) ^ 2 ≤ u5BoundedExp a t ∧
    |Real.exp t * (1 - a * Real.exp t) / (1 + a * Real.exp t) ^ 3| ≤
      u5BoundedExp a t := by
  let e := Real.exp t
  let d := 1 + a * e
  have he : 0 < e := Real.exp_pos _
  have hd1 : 1 ≤ d := by dsimp [d]; nlinarith [mul_nonneg ha.le he.le]
  have hd : 0 < d := by linarith
  have hf : 0 ≤ e / d := div_nonneg he.le hd.le
  have hden2 : 0 < d ^ 2 := by positivity
  have hden3 : 0 < d ^ 3 := by positivity
  have hda : |1 - a * e| ≤ d := by
    apply abs_le.mpr
    dsimp [d]
    constructor <;> nlinarith [mul_nonneg ha.le he.le]
  have hds : d ≤ d ^ 2 := by nlinarith
  change 0 ≤ e / d ∧ e / d ≤ a⁻¹ ∧ e / d ^ 2 ≤ e / d ∧
    |e * (1 - a * e) / d ^ 3| ≤ e / d
  refine ⟨hf, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hd).2
    have h := mul_inv_cancel₀ (ne_of_gt ha)
    dsimp [d]
    nlinarith
  · apply (div_le_iff₀ hden2).2
    have hh : e / d * d ^ 2 = e * d := by field_simp [ne_of_gt hd] <;> ring
    rw [hh]
    nlinarith
  · have hr : |1 - a * e| / d ^ 2 ≤ 1 := by
      apply (div_le_iff₀ hden2).2
      simpa using hda.trans hds
    calc
      |e * (1 - a * e) / d ^ 3| = (e / d) * (|1 - a * e| / d ^ 2) := by
        rw [abs_div, abs_mul, abs_of_pos he, abs_of_pos hden3]
        field_simp [ne_of_gt hd] <;> ring
      _ ≤ e / d * 1 := mul_le_mul_of_nonneg_left hr hf
      _ = _ := mul_one _

#print axioms u5_bounded_exp_bounds

#print axioms u5_bounded_exp_derivatives

/-- Bounded coordinate exponentials have the relative derivative bounds required for cutoffs. -/
theorem u5_bounded_coordinate_exp_properties {d : ℕ} (a q : ℝ) (ha : 0 < a) (k : Fin d) :
    let h : Vec d → ℝ := fun x => u5BoundedExp a (q * x k)
    ContDiff ℝ (⊤ : ℕ∞) h ∧
    (∀ x, 0 ≤ h x ∧ h x ≤ a⁻¹) ∧
    (∀ x j, |fderiv ℝ h x (unitVector j)| ≤ |q| * h x) ∧
    (∀ x i j, |fderiv ℝ (fun y => fderiv ℝ h y (unitVector j)) x
      (unitVector i)| ≤ q ^ 2 * h x) := by
  let h : Vec d → ℝ := fun x => u5BoundedExp a (q * x k)
  let E : ℝ → ℝ := fun t => Real.exp t / (1 + a * Real.exp t) ^ 2
  let F : ℝ → ℝ := fun t => Real.exp t * (1 - a * Real.exp t) / (1 + a * Real.exp t) ^ 3
  have hq (x : Vec d) : HasFDerivAt (fun y : Vec d => q * y k)
      (q • ContinuousLinearMap.proj k) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) k x).const_mul q
  have he (x : Vec d) (j : Fin d) : fderiv ℝ h x (unitVector j) =
      (if k = j then q else 0) * E (q * x k) := by
    have hd := ((u5_bounded_exp_derivatives a ha.le (q * x k)).1.comp_hasFDerivAt x (hq x)).fderiv
    have hh := congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector j)) hd
    simpa [h, E, Function.comp_def, unitVector, Pi.single_apply, smul_eq_mul, mul_comm] using hh
  have he2 (x : Vec d) (i j : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ h y (unitVector j)) x (unitVector i) =
        (if k = j then q else 0) * (if k = i then q else 0) * F (q * x k) := by
    have hfun : (fun y => fderiv ℝ h y (unitVector j)) =
        fun y => (if k = j then q else 0) * E (q * y k) := funext (fun y => he y j)
    rw [hfun, fderiv_const_mul]
    · have hd := ((u5_bounded_exp_derivatives a ha.le (q * x k)).2.comp_hasFDerivAt x (hq x)).fderiv
      have hh := congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector i)) hd
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hh' : fderiv ℝ (fun y : Vec d => E (q * y k)) x (unitVector i) =
          (if k = i then q else 0) * F (q * x k) := by
        simpa [E, F, Function.comp_def, unitVector, Pi.single_apply, smul_eq_mul, mul_comm] using hh
      rw [hh']
      ring
    · exact ((u5_bounded_exp_derivatives a ha.le (q * x k)).2.comp_hasFDerivAt x (hq x)).differentiableAt
  have hs : ContDiff ℝ (⊤ : ℕ∞) h := by
    dsimp [h, u5BoundedExp]
    apply ContDiff.div
    · exact (contDiff_const.mul (contDiff_apply ℝ ℝ k)).exp
    · exact contDiff_const.add (contDiff_const.mul (contDiff_const.mul (contDiff_apply ℝ ℝ k)).exp)
    · intro x
      positivity
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(u5_bounded_exp_bounds a ha _).1, (u5_bounded_exp_bounds a ha _).2.1⟩
  · intro x j
    have hh0 : 0 ≤ h x := (u5_bounded_exp_bounds a ha _).1
    rw [he, abs_mul]
    have hE : 0 ≤ E (q * x k) := by dsimp [E]; positivity
    rw [abs_of_nonneg hE]
    split_ifs <;> simp only [abs_zero, zero_mul]
    · exact mul_le_mul_of_nonneg_left (u5_bounded_exp_bounds a ha _).2.2.1 (abs_nonneg q)
    · exact mul_nonneg (abs_nonneg q) hh0
  · intro x i j
    have hh0 : 0 ≤ h x := (u5_bounded_exp_bounds a ha _).1
    rw [he2, abs_mul, abs_mul]
    split_ifs <;> simp only [abs_zero, zero_mul, mul_zero]
    · have hb := (u5_bounded_exp_bounds a ha (q * x k)).2.2.2
      have hsq : |q| * |q| = q ^ 2 := by rw [← abs_mul, ← pow_two, abs_of_nonneg (sq_nonneg q)]
      rw [hsq]
      exact mul_le_mul_of_nonneg_left hb (sq_nonneg q)
    all_goals exact mul_nonneg (sq_nonneg q) hh0

#print axioms u5_bounded_coordinate_exp_properties

/-- Cutoff coordinate truncations have a common growth constant and a vanishing cutoff error. -/
theorem u5_regular_generator_cutoff_bounded_coordinate_exp {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (k : Fin d) (q : ℝ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ a : ℝ, 0 < a →
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ c : ℝ, 0 < c → c ≤ 1 →
        |physicalGenerator (firstCoordinateIndex hd) ω lam
          (fun z => χ (c • z) * u5BoundedExp a (q * z k)) x| ≤
          C * (χ (c • x) * u5BoundedExp a (q * x k)) + c * (E * a⁻¹) := by
  obtain ⟨C, E, hC, hE, hu⟩ := u5_regular_generator_cutoff_product_uniform
    hd ω lam Λ hΛ hω hχ hc hχ01 |q| (q ^ 2) (abs_nonneg q) (sq_nonneg q)
  refine ⟨C, E, hC, hE, ?_⟩
  intro a ha
  have hp := u5_bounded_coordinate_exp_properties a q ha k
  exact hu _ _ hp.1 (inv_nonneg.mpr ha.le) hp.2.1 hp.2.2.1 hp.2.2.2

#print axioms u5_regular_generator_cutoff_bounded_coordinate_exp

/-- The actual regular-field generator has a uniform relative bound on
coordinate exponentials at almost every spatial point. -/
theorem u5_regular_generator_coordinate_exp_abs_le {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (i : Fin d) (q : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ x ∂(volume : Measure (Vec d)),
      |physicalGenerator (firstCoordinateIndex hd) ω lam
        (fun y => Real.exp (q * y i)) x| ≤ Real.exp (q * x i) * K := by
  obtain ⟨_, _, ⟨Ma, hMa⟩, _, _, ⟨Mb, hMb⟩⟩ :=
    physical_svHypotheses (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam
  let K : ℝ := max 1 (|q| * Mb + q ^ 2 / 2 * Ma)
  refine ⟨K, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  filter_upwards [u2_regular_physical_generator_ae_textbook hd ω lam Λ hΛ hω] with x hx
  have he : ContDiff ℝ 2 (fun y : Vec d => Real.exp (q * y i)) :=
    (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp
  rw [hx _ he]
  exact (c16_svGenerator_coordinate_exp_abs_le _ _ i q x (hMa x i i) (hMb x i)).trans
    (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_nonneg _))


/-- Relative derivative bounds give a relative regular-generator bound. -/
theorem u5_regular_generator_relative_derivative_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (D₁ D₂ : ℝ)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ (φ : Vec d → ℝ), ContDiff ℝ 2 φ → 0 ≤ φ x →
      (∀ i, |fderiv ℝ φ x (unitVector i)| ≤ D₁ * φ x) →
      (∀ i j, |fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| ≤
        D₂ * φ x) →
      |physicalGenerator (firstCoordinateIndex hd) ω lam φ x| ≤ K * φ x := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  refine ⟨C₁ * D₁ + C₂ * D₂, by positivity, ?_⟩
  filter_upwards [hgen] with x hx
  intro φ hφ hφ0 hfirst hsecond
  have h := hx φ hφ (D₁ * φ x) (D₂ * φ x)
    (mul_nonneg hD₁ hφ0) (mul_nonneg hD₂ hφ0) hfirst hsecond
  convert h using 1 <;> ring

/-- The regular generator bound is uniform across the coordinate truncation parameter. -/
theorem u5_regular_generator_bounded_coordinate_exp {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (k : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ a : ℝ, 0 < a →
        |physicalGenerator (firstCoordinateIndex hd) ω lam
          (fun y => u5BoundedExp a (q * y k)) x| ≤
          C * u5BoundedExp a (q * x k) := by
  obtain ⟨C, hC, hgen⟩ := u5_regular_generator_relative_derivative_bound
    hd ω lam Λ hΛ hω |q| (q ^ 2) (abs_nonneg q) (sq_nonneg q)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hgen] with x hx
  intro a ha
  have hp := u5_bounded_coordinate_exp_properties a q ha k
  exact hx _ (hp.1.of_le (WithTop.coe_le_coe.2 le_top)) (hp.2.1 x).1
    (hp.2.2.1 x) (hp.2.2.2 x)

#print axioms u5_regular_generator_bounded_coordinate_exp

/-- An almost-everywhere upper bound is preserved by the physical resolvent. -/
theorem u5_regular_physical_resolvent_upper_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (B : ℝ) (hB : 0 < B)
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x ≤ B) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x ≤ B / α := by
  let p := f ⊔ 0
  have hp : (p : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] fun x => max (f x) 0 := by
    filter_upwards [Lp.coeFn_sup f 0, Lp.coeFn_zero ℝ 2 (physicalReversibleMeasure ω hd lam)] with x hx hz
    simpa only [p, Pi.sup_apply, hz, Pi.zero_apply] using hx
  have hp0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] p := by
    filter_upwards [hp] with x hx
    rw [hx]
    exact le_max_right _ _
  have hpB : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, p x ≤ B := by
    filter_upwards [hp, hf] with x hx hf'
    rw [hx]
    exact max_le hf' hB.le
  have hfp : f ≤ᵐ[physicalReversibleMeasure ω hd lam] p := by
    filter_upwards [hp] with x hx
    rw [hx]
    exact le_max_left _ _
  have hm := gmpPhysicalResolvent_mono hd ω lam Λ hΛ hω α hα hfp
  have hb := gmpPhysicalResolvent_nonneg_le hd ω lam Λ hΛ hω α hα hB hp0 hpB
  filter_upwards [hm, hb] with x hx hy
  exact hx.trans hy.2

/-- A generator upper bound yields a one-sided compact-test resolvent bound. -/
theorem u5_regular_resolvent_compactTest_upper {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : ZeroAtInftyContinuousMap (Vec d) ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (C B : ℝ) (hB : 0 < B)
    (hgen : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ x - C * φ x ≤ B)
    (α : ℝ) (hα : 0 < α) :
    ∀ x, (α - C) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ x ≤ φ x + B / α := by
  let u := gmpPhysicalH1Value hd ω lam Λ hω
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)
  let g := sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam φ hφ hc
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  let z := g - C • u
  have hz : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, z x ≤ B := by
    filter_upwards [hgen, (sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd)
      (lt_of_lt_of_le zero_lt_one hΛ) hω lam hφ hc).coeFn_toLp,
      gmpPhysicalCompactTest_value_ae hd ω lam Λ hω φ hφ hc,
      Lp.coeFn_sub g (C • u), Lp.coeFn_smul C u] with x hg hge hu hs hm
    change g x = physicalGenerator (firstCoordinateIndex hd) ω lam φ x at hge
    change u x = φ x at hu
    change (g - C • u) x ≤ B
    rw [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hge, hu]
    exact hg
  have hb := u5_regular_physical_resolvent_upper_bound hd ω lam Λ hΛ hω α hα z B hB hz
  have hid : α • G u - u = G g :=
    u2_regular_physical_resolvent_compactTest_sub hd ω lam Λ hΛ hω α hα φ hφ hc
  have hzid : G z = α • G u - u - C • G u := by
    dsimp [z]
    rw [map_sub, map_smul, ← hid]
  have hzid' : (G z : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
      (α • G u - u - C • G u : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :=
    Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) =>
      (z : Vec d → ℝ)) hzid)
  let v := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ
  have hv := u2_regular_c0_resolvent_ae hd ω lam Λ hΛ hω α hα φ hc u
    (gmpPhysicalH1Value_compactTest hd ω lam Λ hω φ hφ hc)
  have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, (α - C) * v x ≤ φ x + B / α := by
    filter_upwards [hb, hzid', Lp.coeFn_sub (α • G u - u) (C • G u),
      Lp.coeFn_sub (α • G u) u, Lp.coeFn_smul α (G u), Lp.coeFn_smul C (G u),
      gmpPhysicalCompactTest_value_ae hd ω lam Λ hω φ hφ hc, hv] with x hb' he hs hs' hm hm' hu hvx
    change G z x ≤ B / α at hb'
    change G z x = (α • G u - u - C • G u) x at he
    rw [hs, Pi.sub_apply, hs', Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul,
      hm', Pi.smul_apply, smul_eq_mul, hu] at he
    change v x = G u x at hvx
    rw [hvx]
    linarith
  have hvol := (gmpPhysical_ae_iff_volume hd ω lam _).mp hae
  have hclosed : IsClosed {x : Vec d | (α - C) * v x ≤ φ x + B / α} :=
    isClosed_le (continuous_const.mul v.continuous) (φ.continuous.add continuous_const)
  have hfull : {x : Vec d | (α - C) * v x ≤ φ x + B / α} = Set.univ :=
    (hclosed.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hvol)
  intro x
  have hx : x ∈ {x : Vec d | (α - C) * v x ≤ φ x + B / α} := by
    rw [hfull]
    exact Set.mem_univ x
  exact hx

/-- A compact cutoff of the bounded coordinate exponential as a C₀ test. -/
def u5CutoffBoundedCoordinateTest {d : ℕ} (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (a q : ℝ) (ha : 0 < a) (k : Fin d) (c : ℝ) (hc0 : 0 < c) :
    ZeroAtInftyContinuousMap (Vec d) ℝ :=
  gmpPhysicalCompactC0 (fun x => χ (c • x) * u5BoundedExp a (q * x k))
    (((hχ.comp (contDiff_const_smul c)).mul
      (u5_bounded_coordinate_exp_properties a q ha k).1).continuous)
    ((hc.comp_smul (ne_of_gt hc0)).mul_right)

/-- Compact-test resolvent comparison for the truncated coordinate barrier. -/
theorem u5_regular_resolvent_cutoff_bounded_coordinate_exp {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (k : Fin d) (q : ℝ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (a : ℝ) (ha : 0 < a)
      (c : ℝ) (hc0 : 0 < c), c ≤ 1 → ∀ (α : ℝ) (hα : 0 < α) x,
        let φ := u5CutoffBoundedCoordinateTest χ hχ hc a q ha k c hc0
        (α - C) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ x ≤
          φ x + c * (E * a⁻¹ + 1) / α := by
  obtain ⟨C, E, hC, hE, hgen⟩ := u5_regular_generator_cutoff_bounded_coordinate_exp
    hd ω lam Λ hΛ hω hχ hc hχ01 k q
  refine ⟨C, E, hC, hE, ?_⟩
  intro a ha c hc0 hc1 α hα x
  let φ := u5CutoffBoundedCoordinateTest χ hχ hc a q ha k c hc0
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => χ (c • x) * u5BoundedExp a (q * x k))
    exact (hχ.comp (contDiff_const_smul c)).mul (u5_bounded_coordinate_exp_properties a q ha k).1
  have hφc : HasCompactSupport φ := by
    change HasCompactSupport (fun x => χ (c • x) * u5BoundedExp a (q * x k))
    exact (hc.comp_smul (ne_of_gt hc0)).mul_right
  have hB : 0 < c * (E * a⁻¹ + 1) := by positivity
  have haegen : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ x - C * φ x ≤
        c * (E * a⁻¹ + 1) := by
    apply (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mpr
    filter_upwards [hgen a ha] with y hy
    have hh := hy c hc0 hc1
    change |physicalGenerator (firstCoordinateIndex hd) ω lam φ y| ≤ C * φ y + c * (E * a⁻¹) at hh
    have hl := le_abs_self (physicalGenerator (firstCoordinateIndex hd) ω lam φ y)
    nlinarith
  exact u5_regular_resolvent_compactTest_upper hd ω lam Λ hΛ hω φ hφ hφc
    C (c * (E * a⁻¹ + 1)) hB haegen α hα x

/-- A dilated unit-plateau cutoff eventually dominates any compactly supported
nonnegative test bounded by the truncated exponential. -/
theorem u5_cutoff_bounded_coordinate_dominates_compact {d : ℕ}
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ0 : ∀ y, 0 ≤ χ y)
    (a q : ℝ) (ha : 0 < a) (k : Fin d)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hfc : HasCompactSupport (f : Vec d → ℝ))
    (hf : ∀ x, f x ≤ u5BoundedExp a (q * x k)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ c : ℝ, ∀ (hc0 : 0 < c), c ≤ δ →
      ∀ x, f x ≤ u5CutoffBoundedCoordinateTest χ hχ hc a q ha k c hc0 x := by
  obtain ⟨R, hR, hbound⟩ := hfc.isBounded.exists_pos_norm_le
  let δ : ℝ := min 1 R⁻¹
  have hδ : 0 < δ := lt_min one_pos (inv_pos.mpr hR)
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro c hc0 hcδ x
  change f x ≤ χ (c • x) * u5BoundedExp a (q * x k)
  by_cases hx : x ∈ Function.support (f : Vec d → ℝ)
  · have hxR : ‖x‖ ≤ R := hbound x (subset_closure hx)
    have hcR : c ≤ R⁻¹ := hcδ.trans (min_le_right _ _)
    have hn : ‖c • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
      calc
        c * ‖x‖ ≤ R⁻¹ * R := mul_le_mul hcR hxR (norm_nonneg _) (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hR)
    rw [hχone _ hn, one_mul]
    exact hf x
  · have hfx : f x = 0 := by simpa [Function.mem_support] using hx
    rw [hfx]
    exact mul_nonneg (hχ0 _) ((u5_bounded_exp_bounds a ha (q * x k)).1)

#print axioms u5_cutoff_bounded_coordinate_dominates_compact

/-- Removing the cutoff in the resolvent estimate for compactly supported tests. -/
theorem u5_regular_resolvent_compact_below_bounded_coordinate_exp {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (_ha : 0 < a)
      (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
      (_hfc : HasCompactSupport (f : Vec d → ℝ))
      (_hf : ∀ x, f x ≤ u5BoundedExp a (q * x k))
      (α : ℝ) (hα : 0 < α), C < α → ∀ x,
      (α - C) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x ≤
        u5BoundedExp a (q * x k) := by
  obtain ⟨C, E, hC, hE, hres⟩ :=
    u5_regular_resolvent_cutoff_bounded_coordinate_exp hd ω lam Λ hΛ hω hχ hc hχ01 k q
  refine ⟨C, hC, ?_⟩
  intro a ha f hfc hf α hα hαC x
  obtain ⟨δ, hδ, hδ1, hdom⟩ :=
    u5_cutoff_bounded_coordinate_dominates_compact hχ hc hχone
      (fun y => (hχ01 y).1) a q ha k f hfc hf
  let D := E * a⁻¹ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  let c := min δ (ε * α / (2 * D))
  have hc0 : 0 < c := lt_min hδ (by positivity)
  have hcδ : c ≤ δ := min_le_left _ _
  have hc1 : c ≤ 1 := hcδ.trans hδ1
  let φ := u5CutoffBoundedCoordinateTest χ hχ hc a q ha k c hc0
  have hcmp : ∀ y, f y ≤ φ y := hdom c hc0 hcδ
  have hR : u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x ≤
      u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ x := by
    have hp := u2_regular_c0_resolvent_positive hd ω lam Λ hΛ hω α hα (φ - f)
      (fun y => by change 0 ≤ φ y - f y; linarith [hcmp y]) x
    rw [map_sub] at hp
    change 0 ≤ u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ x -
      u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x at hp
    linarith
  have hφ : φ x ≤ u5BoundedExp a (q * x k) := by
    change χ (c • x) * u5BoundedExp a (q * x k) ≤ _
    nlinarith [(hχ01 (c • x)).2, (u5_bounded_exp_bounds a ha (q * x k)).1]
  have he : c * D / α ≤ ε := by
    have hcε : c ≤ ε * α / (2 * D) := min_le_right _ _
    have hm : c * (2 * D) ≤ ε * α := (le_div_iff₀ (by positivity)).mp hcε
    apply (div_le_iff₀ hα).2
    nlinarith [mul_nonneg hc0.le hD.le]
  have hr := hres a ha c hc0 hc1 α hα x
  change (α - C) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ x ≤
    φ x + c * D / α at hr
  have hm := mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr hαC.le)
  linarith

#print axioms u5_regular_resolvent_compact_below_bounded_coordinate_exp

/-- The bounded exponential controls the resolvent of every dominated C₀ test. -/
theorem u5_regular_resolvent_below_bounded_coordinate_exp {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (_ha : 0 < a)
      (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
      (_hf : ∀ x, f x ≤ u5BoundedExp a (q * x k))
      (α : ℝ) (hα : 0 < α), C < α → ∀ x,
      (α - C) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x ≤
        u5BoundedExp a (q * x k) := by
  obtain ⟨C, hC, hres⟩ := u5_regular_resolvent_compact_below_bounded_coordinate_exp
    hd ω lam Λ hΛ hω hχ hc hχone hχ01 k q
  refine ⟨C, hC, ?_⟩
  intro a ha f hf α hα hαC x
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Filter.Tendsto ε Filter.atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose g hgc hgb hgK hga using fun n : ℕ =>
    gmpC0_exists_bounded_compact_cutoff f ∅ isCompact_empty (hε n)
  let fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ := fun n => f * g n
  have hb (n : ℕ) : ‖fn n - f‖ ≤ ε n := by
    change ‖(fn n - f).toBCF‖ ≤ ε n
    apply (BoundedContinuousFunction.norm_le (le_of_lt (hε n))).2
    intro y
    change ‖(f * g n) y - f y‖ ≤ ε n
    simpa only [Real.norm_eq_abs] using hga n y
  have hconv : Filter.Tendsto fn Filter.atTop (𝓝 f) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) hb hεlim
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα
  have heval : Continuous (fun v : ZeroAtInftyContinuousMap (Vec d) ℝ => v x) :=
    (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
      (ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
  have hlim : Filter.Tendsto (fun n => (α - C) * R (fn n) x) Filter.atTop
      (𝓝 ((α - C) * R f x)) :=
    ((heval.tendsto (R f)).comp (R.continuous.tendsto f |>.comp hconv)).const_mul _
  apply le_of_tendsto' hlim
  intro n
  apply hres a ha (fn n) (HasCompactSupport.mul_left (hgc n)) ?_ α hα hαC x
  intro y
  change f y * g n y ≤ u5BoundedExp a (q * y k)
  have hp := (u5_bounded_exp_bounds a ha (q * y k)).1
  have hg := hgb n y
  nlinarith [mul_nonneg (sub_nonneg.mpr hg.2) hp,
    mul_nonneg (sub_nonneg.mpr (hf y)) hg.1]

#print axioms u5_regular_resolvent_below_bounded_coordinate_exp

#print axioms u5_regular_resolvent_cutoff_bounded_coordinate_exp

/-- A comparison for all C₀ functions below a positive barrier iterates. -/
theorem u5_operator_pow_below_barrier {X : Type*} [TopologicalSpace X]
    (T : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ZeroAtInftyContinuousMap X ℝ)
    (h : X → ℝ) (a : ℝ) (ha : 0 < a)
    (hT : ∀ f : ZeroAtInftyContinuousMap X ℝ, (∀ x, f x ≤ h x) →
      ∀ x, T f x ≤ a * h x)
    (f : ZeroAtInftyContinuousMap X ℝ) (hf : ∀ x, f x ≤ h x) :
    ∀ n x, (T ^ n) f x ≤ a ^ n * h x := by
  intro n
  induction n with
  | zero =>
      intro x
      simpa using hf x
  | succ n ih =>
      have hp : 0 < a ^ n := pow_pos ha n
      let g : ZeroAtInftyContinuousMap X ℝ := (a ^ n)⁻¹ • (T ^ n) f
      have hg : ∀ x, g x ≤ h x := by
        intro x
        change (a ^ n)⁻¹ * (T ^ n) f x ≤ h x
        rw [mul_comm, ← div_eq_mul_inv]
        exact (div_le_iff₀ hp).2 (by simpa [mul_comm] using ih x)
      have hh := hT g hg
      intro x
      have heq : T g x = (a ^ n)⁻¹ * (T ((T ^ n) f)) x := by
        simp [g]
      have hhx := hh x
      rw [heq] at hhx
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      have hhx' := mul_le_mul_of_nonneg_left hhx hp.le
      have hi : a ^ n * (a ^ n)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
      rw [← mul_assoc, hi, one_mul] at hhx'
      calc
        T ((T ^ n) f) x ≤ a ^ n * (a * h x) := hhx'
        _ = a ^ (n + 1) * h x := by rw [pow_succ]; ring

#print axioms u5_operator_pow_below_barrier

/-- Every normalized regular resolvent iterate obeys the bounded exponential barrier. -/
theorem u5_regular_scaled_resolvent_pow_below_bounded_coordinate_exp {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 0 < a →
      ∀ (f : ZeroAtInftyContinuousMap (Vec d) ℝ),
      (∀ x, f x ≤ u5BoundedExp a (q * x k)) →
      ∀ (α : MarkovProcess.Semigroup.PositiveShift), C < (α : ℝ) → ∀ n x,
      (((u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω).scaledOperator α) ^ n) f x ≤
        ((α : ℝ) / ((α : ℝ) - C)) ^ n * u5BoundedExp a (q * x k) := by
  obtain ⟨C, hC, hres⟩ := u5_regular_resolvent_below_bounded_coordinate_exp
    hd ω lam Λ hΛ hω hχ hc hχone hχ01 k q
  refine ⟨C, hC, ?_⟩
  intro a ha f hf α hαC
  have hden : 0 < (α : ℝ) - C := sub_pos.mpr hαC
  apply u5_operator_pow_below_barrier _ _ _ (div_pos α.property hden) ?_ f hf
  intro g hg x
  have hr := hres a ha g hg α α.property hαC x
  change (α : ℝ) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α α.property g x ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith [mul_le_mul_of_nonneg_left hr α.property.le]

#print axioms u5_regular_scaled_resolvent_pow_below_bounded_coordinate_exp

open Filter Set Topology NormedSpace MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

/-- The scalar sum obtained by weighting geometric powers with the Poisson coefficients. -/
private theorem u5_tsum_poissonWeight_mul_pow (c a : ℝ) :
    ∑' n : ℕ, poissonWeight c n * a ^ n = Real.exp (c * (a - 1)) := by
  have hsum : ∑' n : ℕ, (c * a) ^ n / n.factorial = Real.exp (c * a) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    apply tsum_congr
    intro n
    simp only [div_eq_mul_inv, smul_eq_mul]
    ring
  unfold poissonWeight
  rw [show (fun n : ℕ ↦ Real.exp (-c) * (c ^ n / n.factorial) * a ^ n) =
      fun n ↦ Real.exp (-c) * ((c * a) ^ n / n.factorial) by
    funext n
    rw [mul_pow]
    ring]
  rw [tsum_mul_left, hsum, ← Real.exp_add]
  congr 1
  ring

/-- The scalar exponent in the Yosida comparison converges to its semigroup counterpart. -/
private theorem u5_tendsto_mul_naturalShift_div_sub (b theta : ℝ) :
    Tendsto (fun n : ℕ ↦
      b * (naturalShift n : ℝ) / ((naturalShift n : ℝ) - theta))
      atTop (nhds b) := by
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + (1 - theta)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 - theta) tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ ↦ theta / ((n : ℝ) + (1 - theta)))
      atTop (nhds 0) := hden.const_div_atTop theta
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hmain : Tendsto (fun n : ℕ ↦
      b * (1 + theta / ((n : ℝ) + (1 - theta)))) atTop (nhds b) := by
    simpa only [add_zero, mul_one] using (hone.add hsmall).const_mul b
  apply hmain.congr'
  filter_upwards [hden.eventually (eventually_gt_atTop 0)] with n hn
  rw [naturalShift_coe]
  have hden' : 0 < (n : ℝ) + 1 - theta := by
    linarith only [hn]
  field_simp [hden'.ne']
  ring

/-- The Poisson representation transfers iterated resolvent bounds to Yosida approximants. -/
theorem u5_yosida_below_barrier {X : Type*} [TopologicalSpace X]
    (R : ContractiveResolvent C₀(X, ℝ)) (theta : ℝ) (h : X → ℝ) (f : C₀(X, ℝ))
    (mu : PositiveShift) (hmu : theta < (mu : ℝ))
    (hpowers : ∀ n x, (R.scaledOperator mu ^ n) f x ≤
      ((mu : ℝ) / ((mu : ℝ) - theta)) ^ n * h x)
    (t : ℝ≥0) (x : X) :
    R.yosidaOperator mu t f x ≤
      Real.exp (theta * (t : ℝ) * (mu : ℝ) / ((mu : ℝ) - theta)) * h x := by
  let Q := R.scaledOperator mu
  let c : ℝ := (t : ℝ) * (mu : ℝ)
  let a : ℝ := (mu : ℝ) / ((mu : ℝ) - theta)
  have hden : 0 < (mu : ℝ) - theta := sub_pos.mpr hmu
  have hleftC0 : Summable fun n : ℕ ↦ poissonWeight c n • (Q ^ n) f :=
    summable_poissonWeight_smul_pow_apply Q c f
  have hleft : Summable fun n : ℕ ↦ poissonWeight c n * (Q ^ n) f x := by
    simpa only [Function.comp_apply, smul_apply, smul_eq_mul] using!
      hleftC0.map (c0EvalCLM x) (c0EvalCLM x).continuous
  have hright : Summable fun n : ℕ ↦ poissonWeight c n * (a ^ n * h x) := by
    have hscalar : Summable fun n : ℕ ↦ poissonWeight c n * a ^ n := by
      unfold poissonWeight
      rw [show (fun n : ℕ ↦ Real.exp (-c) * (c ^ n / n.factorial) * a ^ n) =
          fun n ↦ Real.exp (-c) * ((c * a) ^ n / n.factorial) by
        funext n
        rw [mul_pow]
        ring]
      exact (Real.summable_pow_div_factorial (c * a)).mul_left _
    simpa only [mul_assoc] using hscalar.mul_right (h x)
  rw [ContractiveResolvent.yosidaOperator, ContractiveResolvent.yosidaGenerator, smul_smul]
  change exp (c • (Q - ContinuousLinearMap.id ℝ C₀(X, ℝ))) f x ≤ _
  rw [exp_smul_sub_id_apply_eq_tsum]
  change (∑' n : ℕ, poissonWeight c n • (Q ^ n) f) x ≤ _
  rw [show (∑' n : ℕ, poissonWeight c n • (Q ^ n) f) x =
      ∑' n : ℕ, poissonWeight c n * (Q ^ n) f x by
    change c0EvalCLM x (∑' n : ℕ, poissonWeight c n • (Q ^ n) f) = _
    rw [(c0EvalCLM x).map_tsum hleftC0]
    apply tsum_congr
    intro n
    rfl]
  calc
    (∑' n : ℕ, poissonWeight c n * (Q ^ n) f x) ≤
        ∑' n : ℕ, poissonWeight c n * (a ^ n * h x) :=
      hleft.tsum_le_tsum (fun n ↦
        mul_le_mul_of_nonneg_left (hpowers n x) (poissonWeight_nonneg
          (mul_nonneg t.property mu.property.le) n)) hright
    _ = (∑' n : ℕ, poissonWeight c n * a ^ n) * h x := by
      rw [show (fun n : ℕ ↦ poissonWeight c n * (a ^ n * h x)) =
          fun n ↦ (poissonWeight c n * a ^ n) * h x by
        funext n
        ring]
      rw [tsum_mul_right]
    _ = Real.exp (c * (a - 1)) * h x := by rw [u5_tsum_poissonWeight_mul_pow]
    _ = Real.exp (theta * (t : ℝ) * (mu : ℝ) / ((mu : ℝ) - theta)) * h x := by
      congr 2
      dsimp only [c, a]
      field_simp
      ring

/-- Strong convergence transfers the uniform Yosida barrier to the generated semigroup. -/
theorem u5_generated_semigroup_below_barrier {X : Type*} [TopologicalSpace X]
    (R : ContractiveResolvent C₀(X, ℝ)) (theta : ℝ) (h : X → ℝ) (f : C₀(X, ℝ))
    (hpowers : ∀ mu : PositiveShift, theta < (mu : ℝ) → ∀ n x,
      (R.scaledOperator mu ^ n) f x ≤
        ((mu : ℝ) / ((mu : ℝ) - theta)) ^ n * h x)
    (t : ℝ≥0) (x : X) :
    R.generatedSemigroup t f x ≤ Real.exp (theta * (t : ℝ)) * h x := by
  have hleft : Tendsto (fun n ↦ R.yosidaSemigroup (naturalShift n) t f x)
      atTop (nhds (R.generatedSemigroup t f x)) := by
    change Tendsto (fun n ↦ c0EvalCLM x (R.yosidaSemigroup (naturalShift n) t f)) _ _
    exact (c0EvalCLM x).continuous.continuousAt.tendsto.comp
      (R.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t f)
  have hscalar := u5_tendsto_mul_naturalShift_div_sub (theta * (t : ℝ)) theta
  have hright : Tendsto (fun n ↦
      Real.exp (theta * (t : ℝ) * (naturalShift n : ℝ) /
        ((naturalShift n : ℝ) - theta)) * h x)
      atTop (nhds (Real.exp (theta * (t : ℝ)) * h x)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp hscalar).mul_const (h x)
  apply le_of_tendsto_of_tendsto hleft hright
  have hmuTop : Tendsto (fun n : ℕ ↦ (naturalShift n : ℝ)) atTop atTop :=
    tendsto_positiveShift_coe_atTop.comp tendsto_naturalShift_atTop
  filter_upwards [hmuTop.eventually (eventually_gt_atTop theta)] with n hn
  exact u5_yosida_below_barrier R theta h f (naturalShift n) hn
    (hpowers (naturalShift n) hn) t x

#print axioms u5_yosida_below_barrier
#print axioms u5_generated_semigroup_below_barrier

/-- The regular C₀ semigroup preserves the bounded exponential barrier up to growth. -/
theorem u5_regular_semigroup_below_bounded_coordinate_exp {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 0 < a →
      ∀ (f : C₀(Vec d, ℝ)), (∀ x, f x ≤ u5BoundedExp a (q * x k)) →
      ∀ (t : ℝ≥0) x, u2RegularC0Semigroup hd ω lam Λ hΛ hω t f x ≤
        Real.exp (C * (t : ℝ)) * u5BoundedExp a (q * x k) := by
  obtain ⟨C, hC, hpow⟩ := u5_regular_scaled_resolvent_pow_below_bounded_coordinate_exp
    hd ω lam Λ hΛ hω hχ hc hχone hχ01 k q
  refine ⟨C, hC, ?_⟩
  intro a ha f hf t x
  exact u5_generated_semigroup_below_barrier
    (u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω) C
    (fun y => u5BoundedExp a (q * y k)) f (hpow a ha f hf) t x

#print axioms u5_regular_semigroup_below_bounded_coordinate_exp

/-- The regular kernel integrates the bounded coordinate barrier with exponential growth. -/
theorem u5_regular_kernel_integral_bounded_coordinate_exp {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 0 < a → ∀ (t : ℝ≥0) x,
      (∫ y, u5BoundedExp a (q * y k)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      Real.exp (C * (t : ℝ)) * u5BoundedExp a (q * x k) := by
  obtain ⟨C, hC, hsem⟩ := u5_regular_semigroup_below_bounded_coordinate_exp
    hd ω lam Λ hΛ hω hχ hc hχone hχ01 k q
  refine ⟨C, hC, ?_⟩
  intro a ha t x
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsFiniteMeasure (P t x) :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  let c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hcpos (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  have hclim : Tendsto c atTop (𝓝 0) := by
    simpa [c] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let f : ℕ → C₀(Vec d, ℝ) := fun n =>
    u5CutoffBoundedCoordinateTest χ hχ hc a q ha k (c n) (hcpos n)
  have hχzero : χ 0 = 1 := hχone 0 (by simp)
  have hpoint (y : Vec d) : Tendsto (fun n => f n y) atTop
      (𝓝 (u5BoundedExp a (q * y k))) := by
    have hsmul : Tendsto (fun n => c n • y) atTop (𝓝 (0 : Vec d)) := by
      simpa using hclim.smul (tendsto_const_nhds (x := y))
    have hlim := (hχ.continuous.tendsto 0).comp hsmul
    have hh := hlim.mul_const (u5BoundedExp a (q * y k))
    change Tendsto (fun n => χ (c n • y) * u5BoundedExp a (q * y k)) atTop _
    simpa [hχzero] using hh
  have hbounded (n : ℕ) (y : Vec d) : 0 ≤ f n y ∧ f n y ≤ a⁻¹ := by
    change 0 ≤ χ (c n • y) * u5BoundedExp a (q * y k) ∧
      χ (c n • y) * u5BoundedExp a (q * y k) ≤ a⁻¹
    have hcut := hχ01 (c n • y)
    have hb := u5_bounded_exp_bounds a ha (q * y k)
    constructor
    · exact mul_nonneg hcut.1 hb.1
    · nlinarith [mul_nonneg (sub_nonneg.mpr hcut.2) hb.1]
  have hlim : Tendsto (fun n => ∫ y, f n y ∂P t x) atTop
      (𝓝 (∫ y, u5BoundedExp a (q * y k) ∂P t x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => a⁻¹)
    · intro n
      exact (f n).continuous.measurable.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbounded n y).1]
        exact (hbounded n y).2
    · exact Filter.Eventually.of_forall hpoint
  apply le_of_tendsto' hlim
  intro n
  rw [u2RegularC0KernelSemigroup_integral]
  apply hsem a ha (f n) ?_ t x
  intro y
  change χ (c n • y) * u5BoundedExp a (q * y k) ≤ u5BoundedExp a (q * y k)
  have hcut := hχ01 (c n • y)
  have hb := (u5_bounded_exp_bounds a ha (q * y k)).1
  nlinarith [mul_nonneg (sub_nonneg.mpr hcut.2) hb]

#print axioms u5_regular_kernel_integral_bounded_coordinate_exp

/-- The untruncated coordinate exponential has a finite kernel growth bound. -/
theorem u5_regular_kernel_coordinate_exp_growth {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (k : Fin d) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) x,
      (∫⁻ y, ENNReal.ofReal (Real.exp (q * y k))
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (q * x k)) * ENNReal.ofReal (Real.exp (C * (t : ℝ))) := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb1 : ∀ y : Vec d, ‖y‖ ≤ 1 → b y = 1 := by
    intro y hy
    apply b.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, dist_zero_right, b] using hy
  have hb01 : ∀ y : Vec d, 0 ≤ b y ∧ b y ≤ 1 := fun _ => ⟨b.nonneg, b.le_one⟩
  obtain ⟨C, hC, hbound⟩ := u5_regular_kernel_integral_bounded_coordinate_exp
    hd ω lam Λ hΛ hω b.contDiff b.hasCompactSupport hb1 hb01 k q
  refine ⟨C, hC, ?_⟩
  intro t x
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsFiniteMeasure (P t x) :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have halim : Tendsto a atTop (𝓝 0) := by
    simpa [a] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let F : ℕ → Vec d → ℝ := fun n y => u5BoundedExp (a n) (q * y k)
  have hcont (n : ℕ) : Continuous (F n) :=
    (u5_bounded_coordinate_exp_properties (a n) q (ha n) k).1.continuous
  have hF0 (n : ℕ) (y : Vec d) : 0 ≤ F n y :=
    (u5_bounded_exp_bounds (a n) (ha n) (q * y k)).1
  have hFi (n : ℕ) : Integrable (F n) (P t x) := by
    apply (integrable_const ((a n)⁻¹)).mono' (hcont n).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n y)]
      simpa only [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (ha n).le)] using
        (u5_bounded_exp_bounds (a n) (ha n) (q * y k)).2.1
  have hFle (n : ℕ) (y : Vec d) : F n y ≤ Real.exp (q * y k) := by
    change Real.exp (q * y k) / (1 + a n * Real.exp (q * y k)) ≤ _
    apply div_le_self (Real.exp_nonneg _)
    nlinarith [mul_nonneg (ha n).le (Real.exp_nonneg (q * y k))]
  have hFlim (y : Vec d) : Tendsto (fun n => F n y) atTop
      (𝓝 (Real.exp (q * y k))) := by
    have hdlim : Tendsto (fun n => 1 + a n * Real.exp (q * y k)) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add (halim.mul_const (Real.exp (q * y k)))
    have hh := (tendsto_const_nhds (x := Real.exp (q * y k))).div hdlim
      (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun n : ℕ => Real.exp (q * y k) /
      (1 + a n * Real.exp (q * y k))) atTop
      (𝓝 (Real.exp (q * y k) / 1)) at hh
    simpa [F, u5BoundedExp] using hh
  have hlin (n : ℕ) : (∫⁻ y, ENNReal.ofReal (F n y) ∂P t x) ≤
      ENNReal.ofReal (Real.exp (q * x k) * Real.exp (C * (t : ℝ))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi n) (ae_of_all _ (hF0 n))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.exp (C * (t : ℝ)) * F n x := hbound (a n) (ha n) t x
      _ ≤ Real.exp (C * (t : ℝ)) * Real.exp (q * x k) :=
        mul_le_mul_of_nonneg_left (hFle n x) (Real.exp_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ = ∫⁻ y, liminf (fun n => ENNReal.ofReal (F n y)) atTop ∂P t x := by
      apply lintegral_congr
      intro y
      exact ((ENNReal.continuous_ofReal.tendsto _).comp (hFlim y)).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (F n y) ∂P t x) atTop :=
      lintegral_liminf_le (fun n => (hcont n).measurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal (Real.exp (q * x k) * Real.exp (C * (t : ℝ))) := by
      have h : liminf (fun n => ∫⁻ y, ENNReal.ofReal (F n y) ∂P t x) atTop ≤
          liminf (fun _ : ℕ => ENNReal.ofReal (Real.exp (q * x k) * Real.exp (C * (t : ℝ)))) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hlin)
      simpa only [Filter.liminf_const] using h
    _ = _ := ENNReal.ofReal_mul (Real.exp_nonneg _)

#print axioms u5_regular_kernel_coordinate_exp_growth

/-- The physical clock density is comparable with the signed force density. -/
theorem u5_regular_force_measure_comparable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    physicalReversibleMeasure ω hd lam ≤ ENNReal.ofReal (Real.exp (2 * Λ)) •
        physicalForceMeasure (firstCoordinateIndex hd) lam ∧
    physicalForceMeasure (firstCoordinateIndex hd) lam ≤
      ENNReal.ofReal (Real.exp (2 * Λ)) • physicalReversibleMeasure ω hd lam := by
  have hm : densityWeightedMeasure (sourcePhysicalDensity ω hd lam) =
      physicalReversibleMeasure ω hd lam := by
    simp [densityWeightedMeasure, sourcePhysicalDensity, sourceForceWeight,
      physicalReversibleMeasure, physicalReversibleDensity, physicalForceWeight,
      firstCoordinateIndex]
  have hr : densityWeightedMeasure (sourceReducedDensity hd lam) =
      physicalForceMeasure (firstCoordinateIndex hd) lam := by rfl
  constructor
  · simpa only [hm, hr] using sourcePhysicalMeasure_le_reduced ω hd lam Λ hω
  · simpa only [hm, hr] using sourceReducedMeasure_le_physical ω hd lam Λ hω

/-- The inverse force weight turns the force measure into the Lebesgue gauge. -/
theorem u5_regular_gauge_lintegral_identity {d : ℕ} (i : Fin d)
    (lam : ℝ) (f : Vec d → ℝ≥0∞) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-lam * x i)) * f x
      ∂physicalForceMeasure i lam) =
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x i)) * f x := by
  unfold physicalForceMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume
    (show Measurable (fun x : Vec d =>
      ENNReal.ofReal (Real.exp (2 * lam * x i))) from
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_apply i)))).measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (Real.exp (2 * lam * x i)) *
    (ENNReal.ofReal (Real.exp (-lam * x i)) * f x) = _
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

/-- A pointwise exponential barrier and reversibility imply the gauge mass bound. -/
theorem u5_regular_signed_kernel_gauge_growth_of_barrier {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (C : ℝ)
    (hbarrier : ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (-lam * y (firstCoordinateIndex hd))) ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd))) *
        ENNReal.ofReal (Real.exp (C * (t : ℝ)))) :
    ∀ (t : ℝ≥0) (f : Vec d → ℝ≥0∞), Measurable f →
      (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
        (∫⁻ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
      (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * f x := by
  intro t f hf
  let μ := physicalReversibleMeasure ω hd lam
  let ν := physicalForceMeasure (firstCoordinateIndex hd) lam
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let w : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-lam * x (firstCoordinateIndex hd)))
  let A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * Λ))
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (C * (t : ℝ)))
  have hw : Measurable w := (ENNReal.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply (firstCoordinateIndex hd))))).measurable
  have hc := u5_regular_force_measure_comparable hd ω lam Λ hω
  have hb : (∫⁻ x, w x * (∫⁻ y, f y ∂K x) ∂μ) ≤
      B * ∫⁻ x, w x * f x ∂μ := by
    rw [u5_regular_kernel_full_reversibility hd ω lam Λ hΛ hω t w f hw hf]
    calc
      _ ≤ ∫⁻ x, f x * (w x * B) ∂μ := by
        apply lintegral_mono
        intro x
        simpa only [mul_comm] using mul_le_mul_left (hbarrier t x) (f x)
      _ = ∫⁻ x, B * (w x * f x) ∂μ := by congr 1; funext x; ac_rfl
      _ = _ := lintegral_const_mul _ (hw.mul hf)
  calc
    _ = ∫⁻ x, w x * (∫⁻ y, f y ∂K x) ∂ν :=
      (u5_regular_gauge_lintegral_identity (firstCoordinateIndex hd) lam _).symm
    _ ≤ A * ∫⁻ x, w x * (∫⁻ y, f y ∂K x) ∂μ := by
      have h := lintegral_mono' hc.2 (le_refl (fun x => w x * (∫⁻ y, f y ∂K x)))
      simpa only [lintegral_smul_measure, smul_eq_mul] using h
    _ ≤ A * (B * ∫⁻ x, w x * f x ∂μ) := by simpa only [mul_comm] using mul_le_mul_left hb A
    _ ≤ A * (B * (A * ∫⁻ x, w x * f x ∂ν)) := by
      gcongr
      have h := lintegral_mono' hc.1 (le_refl (fun x => w x * f x))
      simpa only [lintegral_smul_measure, smul_eq_mul] using h
    _ = _ := by
      rw [u5_regular_gauge_lintegral_identity (firstCoordinateIndex hd) lam f]
      simp only [pow_two]
      dsimp only [A, B]
      ac_rfl

/-- Signed-force regular kernels obey the physical exponential gauge bound. -/
theorem u5_regular_signed_kernel_gauge_growth {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (f : Vec d → ℝ≥0∞), Measurable f →
      (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
        (∫⁻ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
      (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * f x := by
  obtain ⟨C, hC, hbarrier⟩ := u5_regular_kernel_coordinate_exp_growth
    hd ω lam Λ hΛ hω (firstCoordinateIndex hd) (-lam)
  exact ⟨C, hC, u5_regular_signed_kernel_gauge_growth_of_barrier
    hd ω lam Λ hΛ hω C hbarrier⟩


/-- The regular kernel gauge estimate transfers to the physical L² semigroup. -/
theorem u5_regular_signed_semigroup_gauge_lintegral_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
        ENNReal.ofReal |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f x|) ≤
      (ENNReal.ofReal (Real.exp (2 * Λ))) ^ 2 *
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * ENNReal.ofReal |f x| := by
  obtain ⟨C, hC, hb⟩ := u5_regular_signed_kernel_gauge_growth hd ω lam Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro t f
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let F : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal |f y|
  have hF : Measurable F := by
    simpa only [F, Real.norm_eq_abs] using (Lp.stronglyMeasurable f).measurable.norm.ennreal_ofReal
  have hpoint : ∀ᵐ x ∂(volume : Measure (Vec d)),
      ENNReal.ofReal |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f x| ≤
        ∫⁻ y, F y ∂K x := by
    have ha := u2_regular_kernel_integral_ae_of_L2 hd ω lam Λ hΛ hω t f
    have hv := (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp ha
    filter_upwards [hv] with x hx
    rw [← hx.2, ← ofReal_integral_eq_lintegral_ofReal hx.1.abs
      (ae_of_all _ fun y => abs_nonneg (f y))]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := fun y => f y) (μ := K x)))
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) *
      (∫⁻ y, F y ∂K x) := by
        apply lintegral_mono_ae
        filter_upwards [hpoint] with x hx
        simpa only [mul_comm] using mul_le_mul_left hx
          (ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))))
    _ ≤ _ := hb t F hF

/-- Gauge integrability is preserved by the regular physical semigroup. -/
theorem u5_regular_signed_semigroup_gauge_integrable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hfi : Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume) :
    Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f x) volume := by
  let G : Vec d → ℝ := fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x
  let H : Vec d → ℝ := fun x => Real.exp (lam * x (firstCoordinateIndex hd)) *
    Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f x
  have hG : (∫⁻ x, ENNReal.ofReal |G x|) < ∞ := by
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => abs_nonneg (G x))).mp
    simpa only [Real.norm_eq_abs] using hfi.hasFiniteIntegral.norm
  obtain ⟨C, _, hb⟩ := u5_regular_signed_semigroup_gauge_lintegral_le hd ω lam Λ hΛ hω
  have hrewrite (a : ℝ) (x : Vec d) :
      ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * ENNReal.ofReal |a| =
        ENNReal.ofReal |Real.exp (lam * x (firstCoordinateIndex hd)) * a| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hH : (∫⁻ x, ENNReal.ofReal |H x|) < ∞ := by
    have h := hb t f
    simp_rw [hrewrite] at h
    exact lt_of_le_of_lt h (by
      apply ENNReal.mul_lt_top
      · apply ENNReal.mul_lt_top
        · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
        · exact ENNReal.ofReal_lt_top
      · exact hG)
  have hm : AEStronglyMeasurable H volume := by
    apply Measurable.aestronglyMeasurable
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_apply (firstCoordinateIndex hd)))).measurable.mul
      (Lp.stronglyMeasurable _).measurable
  refine ⟨hm, (hasFiniteIntegral_norm_iff H).mp ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => abs_nonneg (H x))).mpr
  simpa only [Real.norm_eq_abs] using hH

/-- Real-valued gauge L¹ growth for the regular signed physical semigroup. -/
theorem u5_regular_signed_semigroup_gauge_L1_growth {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0)
      (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      Integrable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) volume →
      (∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f x|) ≤
      (Real.exp (2 * Λ)) ^ 2 * Real.exp (C * (t : ℝ)) *
        ∫ x, |Real.exp (lam * x (firstCoordinateIndex hd)) * f x| := by
  obtain ⟨C, hC, hb⟩ := u5_regular_signed_semigroup_gauge_lintegral_le hd ω lam Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro t f hfi
  have hfo := u5_regular_signed_semigroup_gauge_integrable hd ω lam Λ hΛ hω t f hfi
  have hrewrite (a : ℝ) (x : Vec d) :
      ENNReal.ofReal (Real.exp (lam * x (firstCoordinateIndex hd))) * ENNReal.ofReal |a| =
        ENNReal.ofReal |Real.exp (lam * x (firstCoordinateIndex hd)) * a| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have h := hb t f
  simp_rw [hrewrite] at h
  rw [← ofReal_integral_eq_lintegral_ofReal hfo.abs (ae_of_all _ fun x => abs_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hfi.abs (ae_of_all _ fun x => abs_nonneg _),
    ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

#print axioms u5_regular_signed_semigroup_gauge_L1_growth

#print axioms u5_regular_signed_kernel_gauge_growth

end EinsteinFull

#print axioms EinsteinFull.u5_regular_physical_resolvent_upper_bound
#print axioms EinsteinFull.u5_regular_generator_relative_derivative_bound
#print axioms EinsteinFull.u5_regular_generator_coordinate_exp_abs_le
#print axioms EinsteinFull.u5_regular_signed_kernel_gauge_growth_of_barrier

#print axioms EinsteinFull.u5_regular_resolvent_compactTest_upper

#print axioms EinsteinFull.u5_dilated_cutoff_derivative_bound

#print axioms EinsteinFull.u5_regular_generator_dilated_cutoff_bound

#print axioms EinsteinFull.u5_regular_generator_cutoff_product_bound
