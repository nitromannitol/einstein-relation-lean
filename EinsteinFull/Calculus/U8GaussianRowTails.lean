import EinsteinFull.Calculus.U5RegularReversibleDensity
import EinsteinFull.Calculus.U8RegularSignedMoments

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- The unforced kernel has a uniformly bounded reversible density. -/
theorem u8_unforced_kernel_bounded_reversible_density {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t →
      ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
        (∀ x y, 0 ≤ p x y ∧ p x y ≤
          C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))) ∧
        ∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x =
          (physicalReversibleMeasure ω hd 0).withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨D, hD, hdom⟩ := u7_unforced_kernel_quantitative_domination hd ω Λ hΛ hω
  let A := Real.exp (2 * Λ)
  have hA : 0 < A := Real.exp_pos _
  refine ⟨D * A, mul_pos hD hA, ?_⟩
  intro t ht
  let μ := physicalReversibleMeasure ω hd 0
  let K := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t
  let : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω 0
  let B := D * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))
  let M := (D * A) * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))
  have hh : (0 : ℝ) < ((t / 2 : ℝ≥0) : ℝ) := by positivity
  have hB : 0 ≤ B := mul_nonneg hD.le (Real.rpow_nonneg hh.le _)
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hD.le hA.le) (Real.rpow_nonneg hh.le _)
  have hac : ∀ x, K x ≪ (volume : Measure (Vec d)) :=
    fun x => Measure.absolutelyContinuous_of_le_smul (hdom t ht x)
  obtain ⟨p, hp, hn, _, hr⟩ :=
    u5_regular_reversible_density_of_ac hd ω 0 Λ hΛ hω t hac
  have hm (x : Vec d) : K x ≤ ENNReal.ofReal M • μ := by
    calc
      K x ≤ ENNReal.ofReal B • (volume : Measure (Vec d)) := hdom t ht x
      _ ≤ ENNReal.ofReal B • (ENNReal.ofReal A • μ) := by
        apply Measure.le_iff.mpr
        intro s hs
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
        exact Measure.le_iff.mp
          (u4_unforced_physical_measure_comparable hd ω Λ hω).2 s hs
      _ = ENNReal.ofReal M • μ := by
        rw [smul_smul, ← ENNReal.ofReal_mul hB]
        congr 1
        dsimp [M, B]
        ring
  refine ⟨fun x y => min (p x y) M, hp.min measurable_const, ?_, ?_⟩
  · intro x y
    exact ⟨le_min (hn x y) hM, min_le_right _ _⟩
  · intro x
    have hpx : Measurable (p x) := hp.comp (measurable_const.prodMk measurable_id)
    have hae : (fun y => ENNReal.ofReal (p x y)) ≤ᵐ[μ] fun _ => ENNReal.ofReal M := by
      apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hpx.ennreal_ofReal.aemeasurable
      intro s hs _
      rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, ← hr x]
      simpa only [withDensity_const] using Measure.le_iff.mp (hm x) s hs
    rw [hr x]
    apply withDensity_congr_ae
    filter_upwards [hae] with y hy
    have hle : p x y ≤ M := (ENNReal.ofReal_le_ofReal_iff hM).mp hy
    simp only [min_eq_left hle]

#print axioms u8_unforced_kernel_bounded_reversible_density

/-- The unforced kernel has a uniformly bounded almost-everywhere symmetric reversible density. -/
theorem u8_unforced_kernel_bounded_symmetric_density {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t →
      ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
        (∀ x y, 0 ≤ p x y ∧ p x y ≤
          C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))) ∧
        (∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x =
          (physicalReversibleMeasure ω hd 0).withDensity (fun y => ENNReal.ofReal (p x y))) ∧
        ∀ᵐ z ∂(physicalReversibleMeasure ω hd 0).prod
          (physicalReversibleMeasure ω hd 0), p z.1 z.2 = p z.2 z.1 := by
  obtain ⟨D, hD, hdom⟩ := u7_unforced_kernel_quantitative_domination hd ω Λ hΛ hω
  let A := Real.exp (2 * Λ)
  have hA : 0 < A := Real.exp_pos _
  refine ⟨D * A, mul_pos hD hA, ?_⟩
  intro t ht
  let μ := physicalReversibleMeasure ω hd 0
  let K := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t
  let : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω 0
  let B := D * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))
  let M := (D * A) * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))
  have hh : (0 : ℝ) < ((t / 2 : ℝ≥0) : ℝ) := by positivity
  have hB : 0 ≤ B := mul_nonneg hD.le (Real.rpow_nonneg hh.le _)
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hD.le hA.le) (Real.rpow_nonneg hh.le _)
  have hac : ∀ x, K x ≪ (volume : Measure (Vec d)) :=
    fun x => Measure.absolutelyContinuous_of_le_smul (hdom t ht x)
  obtain ⟨p, hp, hn, _, hr, hs⟩ :=
    u5_regular_symmetric_density_of_ac hd ω 0 Λ hΛ hω t hac
  have hm (x : Vec d) : K x ≤ ENNReal.ofReal M • μ := by
    calc
      K x ≤ ENNReal.ofReal B • (volume : Measure (Vec d)) := hdom t ht x
      _ ≤ ENNReal.ofReal B • (ENNReal.ofReal A • μ) := by
        apply Measure.le_iff.mpr
        intro s hs
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
        exact Measure.le_iff.mp
          (u4_unforced_physical_measure_comparable hd ω Λ hω).2 s hs
      _ = ENNReal.ofReal M • μ := by
        rw [smul_smul, ← ENNReal.ofReal_mul hB]
        congr 1
        dsimp [M, B]
        ring
  refine ⟨fun x y => min (p x y) M, hp.min measurable_const, ?_, ?_, ?_⟩
  · intro x y
    exact ⟨le_min (hn x y) hM, min_le_right _ _⟩
  · intro x
    have hpx : Measurable (p x) := hp.comp (measurable_const.prodMk measurable_id)
    have hae : (fun y => ENNReal.ofReal (p x y)) ≤ᵐ[μ] fun _ => ENNReal.ofReal M := by
      apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hpx.ennreal_ofReal.aemeasurable
      intro s hs _
      rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, ← hr x]
      simpa only [withDensity_const] using Measure.le_iff.mp (hm x) s hs
    rw [hr x]
    apply withDensity_congr_ae
    filter_upwards [hae] with y hy
    have hle : p x y ≤ M := (ENNReal.ofReal_le_ofReal_iff hM).mp hy
    simp only [min_eq_left hle]

  · filter_upwards [hs] with z hz
    rw [hz]

#print axioms u8_unforced_kernel_bounded_symmetric_density

/-- A bounded nonnegative density has a squared row tail controlled by its mass. -/
theorem u8_bounded_density_square_tail {d : ℕ}
    (μ ν : Measure (Vec d)) (p : Vec d → ℝ) (M : ℝ)
    (hn : ∀ y, 0 ≤ p y) (hM : 0 ≤ M)
    (hb : ∀ y, p y ≤ M)
    (hrep : ν = μ.withDensity (fun y => ENNReal.ofReal (p y)))
    (s : Set (Vec d)) (hs : MeasurableSet s) :
    (∫⁻ y in s, ENNReal.ofReal (p y ^ 2) ∂μ) ≤ ENNReal.ofReal M * ν s := by
  calc
    _ ≤ ∫⁻ y in s, ENNReal.ofReal M * ENNReal.ofReal (p y) ∂μ := by
      apply lintegral_mono
      intro y
      change ENNReal.ofReal (p y ^ 2) ≤ ENNReal.ofReal M * ENNReal.ofReal (p y)
      rw [← ENNReal.ofReal_mul hM]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [hn y, hb y]
    _ = ENNReal.ofReal M * (∫⁻ y in s, ENNReal.ofReal (p y) ∂μ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by rw [hrep, withDensity_apply _ hs]

#print axioms u8_bounded_density_square_tail

/-- Gaussian squared-density tails for the actual unforced physical kernel. -/
theorem u8_unforced_physical_L2_gaussian_row_tails
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t →
      ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
        (∀ x y, 0 ≤ p x y ∧ p x y ≤ C * (t : ℝ) ^ (-(d : ℝ) / 2)) ∧
        (∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x =
          (physicalReversibleMeasure ω hd 0).withDensity
            (fun y => ENNReal.ofReal (p x y))) ∧
        ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
          (∫⁻ y in {y | R ≤ euclideanNorm (y - x)},
            ENNReal.ofReal (p x y ^ 2) ∂physicalReversibleMeasure ω hd 0) ≤
            ENNReal.ofReal (C * (t : ℝ) ^ (-(d : ℝ) / 2) *
              Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
  obtain ⟨D, hD, hdens⟩ := u8_unforced_kernel_bounded_reversible_density hd ω Λ hΛ hω
  obtain ⟨A, c, hA, hc, htail⟩ := u8_regular_signed_kernel_gaussian_tail hd ω 0 Λ hΛ hω
  let B : ℝ := D * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)
  have hB : 0 < B := by dsimp [B]; positivity
  let C : ℝ := B + A + B * A + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; nlinarith
  have hAC : A ≤ C := by dsimp [C]; nlinarith
  have hBAC : B * A ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, c, hC, hc, ?_⟩
  intro t ht
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpow : 0 ≤ (t : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg htR.le _
  have hscale : D * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) =
      B * (t : ℝ) ^ (-(d : ℝ) / 2) := by
    have heq : (((t / 2 : ℝ≥0) : ℝ)) = (t : ℝ) * (1 / 2 : ℝ) := by simp; ring
    rw [heq, Real.mul_rpow htR.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    dsimp [B]
    ring
  obtain ⟨p, hp, hb, hr⟩ := hdens t ht
  have hbound (x y : Vec d) : p x y ≤ B * (t : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [← hscale]
    exact (hb x y).2
  refine ⟨p, hp, ?_, hr, ?_⟩
  · intro x y
    exact ⟨(hb x y).1, (hbound x y).trans (mul_le_mul_of_nonneg_right hBC hpow)⟩
  · intro x R hR
    have hs : MeasurableSet {y : Vec d | R ≤ euclideanNorm (y - x)} :=
      (isClosed_le continuous_const
        ((EinsteinFull.Calculus.Feller.continuous_euclideanNorm d).comp
          (continuous_id.sub continuous_const))).measurableSet
    have hm : 0 ≤ B * (t : ℝ) ^ (-(d : ℝ) / 2) := mul_nonneg hB.le hpow
    calc
      _ ≤ ENNReal.ofReal (B * (t : ℝ) ^ (-(d : ℝ) / 2)) *
          u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x
            {y | R ≤ euclideanNorm (y - x)} :=
        u8_bounded_density_square_tail _ _ (p x) _ (fun y => (hb x y).1) hm
          (hbound x) (hr x) _ hs
      _ ≤ ENNReal.ofReal (B * (t : ℝ) ^ (-(d : ℝ) / 2)) *
          ENNReal.ofReal (A * Real.exp (A * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
        simpa only [mul_comm] using
          mul_le_mul_left (htail t ht x R hR)
            (ENNReal.ofReal (B * (t : ℝ) ^ (-(d : ℝ) / 2)))
      _ = ENNReal.ofReal ((B * (t : ℝ) ^ (-(d : ℝ) / 2)) *
          (A * Real.exp (A * (t : ℝ) - c * R ^ 2 / (t : ℝ)))) :=
        (ENNReal.ofReal_mul hm).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have he : Real.exp (A * (t : ℝ) - c * R ^ 2 / (t : ℝ)) ≤
            Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_right hAC htR.le]
        have hcoeff : B * A * (t : ℝ) ^ (-(d : ℝ) / 2) ≤
            C * (t : ℝ) ^ (-(d : ℝ) / 2) := mul_le_mul_of_nonneg_right hBAC hpow
        nlinarith [Real.exp_pos (A * (t : ℝ) - c * R ^ 2 / (t : ℝ)),
          Real.exp_pos (C * (t : ℝ) - c * R ^ 2 / (t : ℝ)),
          mul_nonneg hB.le hpow, mul_nonneg hA.le (mul_nonneg hB.le hpow),
          mul_nonneg hC.le hpow,
          mul_nonneg (sub_nonneg.mpr he) (mul_nonneg hA.le (mul_nonneg hB.le hpow)),
          mul_nonneg (sub_nonneg.mpr hcoeff)
            (Real.exp_pos (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))).le]

#print axioms u8_unforced_physical_L2_gaussian_row_tails

/-- Gaussian squared-density tails for the actual unforced physical kernel, with symmetric density. -/
theorem u8_unforced_physical_symmetric_L2_gaussian_row_tails
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t →
      ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
        (∀ x y, 0 ≤ p x y ∧ p x y ≤ C * (t : ℝ) ^ (-(d : ℝ) / 2)) ∧
        (∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x =
          (physicalReversibleMeasure ω hd 0).withDensity
            (fun y => ENNReal.ofReal (p x y))) ∧
        (∀ᵐ z ∂(physicalReversibleMeasure ω hd 0).prod
          (physicalReversibleMeasure ω hd 0), p z.1 z.2 = p z.2 z.1) ∧
        ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
          (∫⁻ y in {y | R ≤ euclideanNorm (y - x)},
            ENNReal.ofReal (p x y ^ 2) ∂physicalReversibleMeasure ω hd 0) ≤
            ENNReal.ofReal (C * (t : ℝ) ^ (-(d : ℝ) / 2) *
              Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
  obtain ⟨D, hD, hdens⟩ := u8_unforced_kernel_bounded_symmetric_density hd ω Λ hΛ hω
  obtain ⟨A, c, hA, hc, htail⟩ := u8_regular_signed_kernel_gaussian_tail hd ω 0 Λ hΛ hω
  let B : ℝ := D * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)
  have hB : 0 < B := by dsimp [B]; positivity
  let C : ℝ := B + A + B * A + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; nlinarith
  have hAC : A ≤ C := by dsimp [C]; nlinarith
  have hBAC : B * A ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, c, hC, hc, ?_⟩
  intro t ht
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpow : 0 ≤ (t : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg htR.le _
  have hscale : D * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) =
      B * (t : ℝ) ^ (-(d : ℝ) / 2) := by
    have heq : (((t / 2 : ℝ≥0) : ℝ)) = (t : ℝ) * (1 / 2 : ℝ) := by simp; ring
    rw [heq, Real.mul_rpow htR.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    dsimp [B]
    ring
  obtain ⟨p, hp, hb, hr, hs⟩ := hdens t ht
  have hbound (x y : Vec d) : p x y ≤ B * (t : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [← hscale]
    exact (hb x y).2
  refine ⟨p, hp, ?_, hr, hs, ?_⟩
  · intro x y
    exact ⟨(hb x y).1, (hbound x y).trans (mul_le_mul_of_nonneg_right hBC hpow)⟩
  · intro x R hR
    have hs : MeasurableSet {y : Vec d | R ≤ euclideanNorm (y - x)} :=
      (isClosed_le continuous_const
        ((EinsteinFull.Calculus.Feller.continuous_euclideanNorm d).comp
          (continuous_id.sub continuous_const))).measurableSet
    have hm : 0 ≤ B * (t : ℝ) ^ (-(d : ℝ) / 2) := mul_nonneg hB.le hpow
    calc
      _ ≤ ENNReal.ofReal (B * (t : ℝ) ^ (-(d : ℝ) / 2)) *
          u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x
            {y | R ≤ euclideanNorm (y - x)} :=
        u8_bounded_density_square_tail _ _ (p x) _ (fun y => (hb x y).1) hm
          (hbound x) (hr x) _ hs
      _ ≤ ENNReal.ofReal (B * (t : ℝ) ^ (-(d : ℝ) / 2)) *
          ENNReal.ofReal (A * Real.exp (A * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
        simpa only [mul_comm] using
          mul_le_mul_left (htail t ht x R hR)
            (ENNReal.ofReal (B * (t : ℝ) ^ (-(d : ℝ) / 2)))
      _ = ENNReal.ofReal ((B * (t : ℝ) ^ (-(d : ℝ) / 2)) *
          (A * Real.exp (A * (t : ℝ) - c * R ^ 2 / (t : ℝ)))) :=
        (ENNReal.ofReal_mul hm).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have he : Real.exp (A * (t : ℝ) - c * R ^ 2 / (t : ℝ)) ≤
            Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_right hAC htR.le]
        have hcoeff : B * A * (t : ℝ) ^ (-(d : ℝ) / 2) ≤
            C * (t : ℝ) ^ (-(d : ℝ) / 2) := mul_le_mul_of_nonneg_right hBAC hpow
        nlinarith [Real.exp_pos (A * (t : ℝ) - c * R ^ 2 / (t : ℝ)),
          Real.exp_pos (C * (t : ℝ) - c * R ^ 2 / (t : ℝ)),
          mul_nonneg hB.le hpow, mul_nonneg hA.le (mul_nonneg hB.le hpow),
          mul_nonneg hC.le hpow,
          mul_nonneg (sub_nonneg.mpr he) (mul_nonneg hA.le (mul_nonneg hB.le hpow)),
          mul_nonneg (sub_nonneg.mpr hcoeff)
            (Real.exp_pos (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))).le]

#print axioms u8_unforced_physical_symmetric_L2_gaussian_row_tails

/-- Composition of a kernel with a jointly measurable density has the
corresponding convolution density, at every starting point. -/
theorem u8_kernel_comp_density {d : ℕ}
    (μ : Measure (Vec d)) [SigmaFinite μ] (K : Kernel (Vec d) (Vec d))
    (p : Vec d → Vec d → ℝ≥0∞) (hp : Measurable (Function.uncurry p))
    (hrep : ∀ x, K x = μ.withDensity (p x)) :
    Measurable (fun w : Vec d × Vec d => ∫⁻ z, p w.1 z * p z w.2 ∂μ) ∧
      ∀ x, (K.comp K) x = μ.withDensity (fun y => ∫⁻ z, p x z * p z y ∂μ) := by
  have hf : Measurable (fun w : (Vec d × Vec d) × Vec d =>
      p w.1.1 w.2 * p w.2 w.1.2) := by
    exact (hp.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hp.comp (measurable_snd.prodMk measurable_fst.snd))
  refine ⟨hf.lintegral_prod_right', ?_⟩
  intro x
  have hpx : Measurable (p x) := hp.comp (measurable_const.prodMk measurable_id)
  ext s hs
  rw [Kernel.comp_apply' K K x hs, hrep x,
    lintegral_withDensity_eq_lintegral_mul μ hpx (Kernel.measurable_coe K hs),
    withDensity_apply _ hs]
  simp_rw [hrep, withDensity_apply _ hs]
  have hprod : Measurable (fun w : Vec d × Vec d => p x w.1 * p w.1 w.2) :=
    (hpx.comp measurable_fst).mul hp
  calc
    _ = ∫⁻ z, ∫⁻ y in s, p x z * p z y ∂μ ∂μ := by
      apply lintegral_congr
      intro z
      change p x z * (∫⁻ y in s, p z y ∂μ) = _
      have hpz : Measurable (p z) := hp.comp (measurable_const.prodMk measurable_id)
      exact (lintegral_const_mul (p x z) hpz).symm
    _ = ∫⁻ y in s, ∫⁻ z, p x z * p z y ∂μ ∂μ :=
      lintegral_lintegral_swap hprod.aemeasurable

#print axioms u8_kernel_comp_density

/-- Symmetry transfers to almost every endpoint and every starting row. -/
theorem u8_symmetric_density_row_transfer {d : ℕ}
    (μ : Measure (Vec d)) [SigmaFinite μ] (K : Kernel (Vec d) (Vec d))
    (p : Vec d → Vec d → ℝ)
    (hrep : ∀ x, K x = μ.withDensity (fun y => ENNReal.ofReal (p x y)))
    (hs : ∀ᵐ z ∂μ.prod μ, p z.1 z.2 = p z.2 z.1) :
    ∀ x, ∀ᵐ y ∂μ, ∀ᵐ z ∂K x, p z y = p y z := by
  intro x
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hs
  have hfib := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hfib] with y hy
  have hac : K x ≪ μ := by
    rw [hrep x]
    exact withDensity_absolutelyContinuous μ _
  exact hac.ae_le hy

#print axioms u8_symmetric_density_row_transfer

/-- One of the two legs of a path has at least half its endpoint distance. -/
theorem u8_half_distance_split {d : ℕ} (x y z : Vec d) :
    euclideanNorm (y - x) / 2 ≤ euclideanNorm (z - x) ∨
      euclideanNorm (y - x) / 2 ≤ euclideanNorm (z - y) := by
  have htri := TimeChange.euclideanNorm_add_le (z - x) (y - z)
  have heq : z - x + (y - z) = y - x := by abel
  rw [heq, ← neg_sub z y, Entropy.euclideanNorm_neg'] at htri
  rcases le_total (euclideanNorm (y - x) / 2) (euclideanNorm (z - x)) with h | h
  · exact Or.inl h
  · right
    linarith

#print axioms u8_half_distance_split

/-- Split a product integral into two Cauchy–Schwarz bounds. -/
theorem u8_lintegral_product_split {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (A B : Set α) (hA : MeasurableSet A) (hAB : Aᶜ ⊆ B) :
    (∫⁻ z, f z * g z ∂μ) ≤
      (∫⁻ z in A, f z ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ z, g z ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) +
      (∫⁻ z, f z ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ z in B, g z ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict A)
    Real.HolderConjugate.two_two hf.aemeasurable.restrict hg.aemeasurable.restrict
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict Aᶜ)
    Real.HolderConjugate.two_two hf.aemeasurable.restrict hg.aemeasurable.restrict
  simp only [Pi.mul_apply] at h1 h2
  have hgt : (∫⁻ z in A, g z ^ (2 : ℝ) ∂μ) ≤ ∫⁻ z, g z ^ (2 : ℝ) ∂μ :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  have hft : (∫⁻ z in Aᶜ, f z ^ (2 : ℝ) ∂μ) ≤ ∫⁻ z, f z ^ (2 : ℝ) ∂μ :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  have hgb : (∫⁻ z in Aᶜ, g z ^ (2 : ℝ) ∂μ) ≤ ∫⁻ z in B, g z ^ (2 : ℝ) ∂μ :=
    lintegral_mono' (Measure.restrict_mono hAB le_rfl) le_rfl
  rw [← lintegral_add_compl (fun z => f z * g z) hA]
  refine add_le_add (h1.trans ?_) (h2.trans ?_)
  · gcongr
  · gcongr

#print axioms u8_lintegral_product_split

/-- Almost every endpoint admits the symmetric convolution at every chosen start. -/
theorem u8_symmetric_density_convolution {d : ℕ}
    (μ : Measure (Vec d)) [SigmaFinite μ] (K : Kernel (Vec d) (Vec d))
    (p : Vec d → Vec d → ℝ) (hp : Measurable (Function.uncurry p))
    (hrep : ∀ x, K x = μ.withDensity (fun y => ENNReal.ofReal (p x y)))
    (hs : ∀ᵐ z ∂μ.prod μ, p z.1 z.2 = p z.2 z.1) (x : Vec d) :
    ∀ᵐ y ∂μ,
      (∫⁻ z, ENNReal.ofReal (p x z) * ENNReal.ofReal (p z y) ∂μ) =
        ∫⁻ z, ENNReal.ofReal (p x z) * ENNReal.ofReal (p y z) ∂μ := by
  have hpx : Measurable (fun z => ENNReal.ofReal (p x z)) :=
    (hp.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  filter_upwards [u8_symmetric_density_row_transfer μ K p hrep hs x] with y hy
  have hf : Measurable (fun z => ENNReal.ofReal (p z y)) :=
    (hp.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
  have hg : Measurable (fun z => ENNReal.ofReal (p y z)) :=
    (hp.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  calc
    _ = ∫⁻ z, ENNReal.ofReal (p z y) ∂K x := by
      rw [hrep x, lintegral_withDensity_eq_lintegral_mul μ hpx hf]
      rfl
    _ = ∫⁻ z, ENNReal.ofReal (p y z) ∂K x := by
      apply lintegral_congr_ae
      filter_upwards [hy] with z hz
      rw [hz]
    _ = _ := by
      rw [hrep x, lintegral_withDensity_eq_lintegral_mul μ hpx hg]
      rfl

#print axioms u8_symmetric_density_convolution

/-- Squared row bounds and a half-distance split control a symmetric convolution. -/
theorem u8_symmetric_convolution_L2_bound {d : ℕ} (μ : Measure (Vec d))
    (p : Vec d → Vec d → ℝ) (hp : Measurable (Function.uncurry p))
    (hn : ∀ x y, 0 ≤ p x y) (x y : Vec d) (M T : ℝ≥0∞)
    (hglobal : ∀ a, (∫⁻ z, ENNReal.ofReal (p a z ^ 2) ∂μ) ≤ M)
    (htail : ∀ a, (∫⁻ z in {z | euclideanNorm (y - x) / 2 ≤ euclideanNorm (z - a)},
      ENNReal.ofReal (p a z ^ 2) ∂μ) ≤ T) :
    (∫⁻ z, ENNReal.ofReal (p x z) * ENNReal.ofReal (p y z) ∂μ) ≤
      T ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) +
        M ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) := by
  let f : Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (p x z)
  let g : Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (p y z)
  let A : Set (Vec d) := {z | euclideanNorm (y - x) / 2 ≤ euclideanNorm (z - x)}
  let B : Set (Vec d) := {z | euclideanNorm (y - x) / 2 ≤ euclideanNorm (z - y)}
  have hf : Measurable f := (hp.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hg : Measurable g := (hp.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hA : MeasurableSet A := (isClosed_le continuous_const
    ((EinsteinFull.Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const))).measurableSet
  have hAB : Aᶜ ⊆ B := by
    intro z hz
    rcases u8_half_distance_split x y z with ha | hb
    · exact False.elim (hz ha)
    · exact hb
  have hsquare (a z : Vec d) : (ENNReal.ofReal (p a z)) ^ (2 : ℝ) =
      ENNReal.ofReal (p a z ^ 2) := by
    rw [ENNReal.rpow_two, pow_two, ← ENNReal.ofReal_mul (hn a z), ← pow_two]
  have h := u8_lintegral_product_split μ f g hf hg A B hA hAB
  have hfa : (∫⁻ z in A, f z ^ (2 : ℝ) ∂μ) ≤ T := by
    simpa only [f, hsquare] using htail x
  have hgb : (∫⁻ z in B, g z ^ (2 : ℝ) ∂μ) ≤ T := by
    simpa only [g, hsquare] using htail y
  have hfm : (∫⁻ z, f z ^ (2 : ℝ) ∂μ) ≤ M := by
    simpa only [f, hsquare] using hglobal x
  have hgm : (∫⁻ z, g z ^ (2 : ℝ) ∂μ) ≤ M := by
    simpa only [g, hsquare] using hglobal y
  exact h.trans (by gcongr)

#print axioms u8_symmetric_convolution_L2_bound

/-- The square-root factors in the two Cauchy–Schwarz pieces recombine. -/
theorem u8_ennreal_sqrt_product (m q : ℝ≥0∞) :
    (m * q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ) +
      m ^ (1 / 2 : ℝ) * (m * q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      2 * m * q := by
  have hm : m ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ) = m := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hq : (q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = q := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hq]
  calc
    _ = (m ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ)) * q +
        (m ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ)) * q := by ac_rfl
    _ = 2 * m * q := by rw [hm]; simp [two_mul, add_mul]

#print axioms u8_ennreal_sqrt_product

/-- Factor the half-distance Gaussian tail into a square. -/
theorem u8_gaussian_tail_factor (a b c s R : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (a * Real.exp (b - c * (R / 2) ^ 2 / s)) =
      ENNReal.ofReal (a * Real.exp b) *
        (ENNReal.ofReal (Real.exp (-(c * R ^ 2 / (8 * s))))) ^ (2 : ℝ) := by
  have he : ENNReal.ofReal (Real.exp (-(c * R ^ 2 / (8 * s)))) ^ 2 =
      ENNReal.ofReal (Real.exp (-(c * R ^ 2 / (8 * s)) +
        -(c * R ^ 2 / (8 * s)))) := by
    rw [pow_two, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  rw [ENNReal.rpow_two, he,
    ← ENNReal.ofReal_mul (mul_nonneg ha (Real.exp_nonneg _))]
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

#print axioms u8_gaussian_tail_factor

/-- Gaussian row tails yield Gaussian decay for the symmetric convolution. -/
theorem u8_symmetric_convolution_gaussian_bound {d : ℕ} (μ : Measure (Vec d))
    (p : Vec d → Vec d → ℝ) (hp : Measurable (Function.uncurry p))
    (hn : ∀ x y, 0 ≤ p x y) (s C c : ℝ) (hs : 0 < s) (hC : 0 ≤ C)
    (htail : ∀ a R, 0 ≤ R →
      (∫⁻ z in {z | R ≤ euclideanNorm (z - a)}, ENNReal.ofReal (p a z ^ 2) ∂μ) ≤
        ENNReal.ofReal (C * s ^ (-(d : ℝ) / 2) * Real.exp (C * s - c * R ^ 2 / s)))
    (x y : Vec d) :
    (∫⁻ z, ENNReal.ofReal (p x z) * ENNReal.ofReal (p y z) ∂μ) ≤
      2 * ENNReal.ofReal (C * s ^ (-(d : ℝ) / 2) * Real.exp (C * s)) *
        ENNReal.ofReal (Real.exp (-(c * euclideanNorm (y - x) ^ 2 / (8 * s)))) := by
  let a := C * s ^ (-(d : ℝ) / 2)
  let R := euclideanNorm (y - x)
  let m := ENNReal.ofReal (a * Real.exp (C * s))
  let q := ENNReal.ofReal (Real.exp (-(c * R ^ 2 / (8 * s))))
  have ha : 0 ≤ a := mul_nonneg hC (Real.rpow_nonneg hs.le _)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hglobal (z : Vec d) : (∫⁻ w, ENNReal.ofReal (p z w ^ 2) ∂μ) ≤ m := by
    have huniv : {w : Vec d | (0 : ℝ) ≤ euclideanNorm (w - z)} = Set.univ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact Real.sqrt_nonneg _
    have h := htail z 0 le_rfl
    simpa [huniv, a, m] using h
  have htail' (z : Vec d) :
      (∫⁻ w in {w | R / 2 ≤ euclideanNorm (w - z)}, ENNReal.ofReal (p z w ^ 2) ∂μ) ≤
        m * q ^ (2 : ℝ) := by
    have h := htail z (R / 2) (by positivity)
    have he := u8_gaussian_tail_factor a (C * s) c s R ha
    exact h.trans_eq he
  calc
    _ ≤ (m * q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ) +
        m ^ (1 / 2 : ℝ) * (m * q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
      u8_symmetric_convolution_L2_bound μ p hp hn x y m (m * q ^ (2 : ℝ)) hglobal htail'
    _ = _ := u8_ennreal_sqrt_product m q

#print axioms u8_symmetric_convolution_gaussian_bound

/-- The actual unforced kernel has a Gaussian envelope relative to its reversible measure. -/
theorem u8_unforced_physical_reversible_gaussian_envelope
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≤
        (physicalReversibleMeasure ω hd 0).withDensity (fun y =>
          2 * ENNReal.ofReal (C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) *
            Real.exp (C * ((t / 2 : ℝ≥0) : ℝ))) *
          ENNReal.ofReal (Real.exp (-(c * euclideanNorm (y - x) ^ 2 /
            (8 * ((t / 2 : ℝ≥0) : ℝ)))))) := by
  obtain ⟨C, c, hC, hc, htail⟩ :=
    u8_unforced_physical_symmetric_L2_gaussian_row_tails hd ω Λ hΛ hω
  refine ⟨C, c, hC, hc, ?_⟩
  intro t ht x
  let s : ℝ≥0 := t / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨p, hp, hn, hr, hsym, hrow⟩ := htail s hs
  let μ := physicalReversibleMeasure ω hd 0
  let K := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω s
  let : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω 0
  let q : Vec d → Vec d → ℝ≥0∞ := fun a b => ENNReal.ofReal (p a b)
  have hq : Measurable (Function.uncurry q) := hp.ennreal_ofReal
  have hrep : ∀ a, K a = μ.withDensity (q a) := hr
  have hcomp := (u8_kernel_comp_density μ K q hq hrep).2 x
  have hadd : s + s = t := by dsimp [s]; exact add_halves t
  have hkernel : u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t = K.comp K := by
    rw [← hadd, (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω).kernel_add]
  rw [hkernel, hcomp]
  apply withDensity_mono
  filter_upwards [u8_symmetric_density_convolution μ K p hp hrep hsym x] with y hy
  rw [hy]
  exact u8_symmetric_convolution_gaussian_bound μ p hp (fun a b => (hn a b).1)
    (s : ℝ) C c hsR hC.le hrow x y

#print axioms u8_unforced_physical_reversible_gaussian_envelope

/-- Gaussian domination of every unforced physical kernel row by Lebesgue measure. -/
theorem u8_unforced_physical_gaussian_kernel_domination
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≤
        (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal
          (C * (t : ℝ) ^ (-(d : ℝ) / 2) *
            Real.exp (C * (t : ℝ) - c * euclideanNorm (y - x) ^ 2 / (t : ℝ)))) := by
  obtain ⟨A, b, hA, hb, henv⟩ :=
    u8_unforced_physical_reversible_gaussian_envelope hd ω Λ hΛ hω
  let E := Real.exp (2 * Λ)
  let D := 2 * E * A * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)
  let C := D + A + 1
  have hE : 0 < E := Real.exp_pos _
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  refine ⟨C, b / 4, hC, by positivity, ?_⟩
  intro t ht x
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hsR : (0 : ℝ) < ((t / 2 : ℝ≥0) : ℝ) := by positivity
  let μ := physicalReversibleMeasure ω hd 0
  let f : Vec d → ℝ≥0∞ := fun y => 2 *
    ENNReal.ofReal (A * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) *
      Real.exp (A * ((t / 2 : ℝ≥0) : ℝ))) *
    ENNReal.ofReal (Real.exp (-(b * euclideanNorm (y - x) ^ 2 /
      (8 * ((t / 2 : ℝ≥0) : ℝ)))))
  have hμ : μ ≤ ENNReal.ofReal E • (volume : Measure (Vec d)) :=
    (u4_unforced_physical_measure_comparable hd ω Λ hω).1
  have hmeasure : μ.withDensity f ≤
      (ENNReal.ofReal E • (volume : Measure (Vec d))).withDensity f := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [withDensity_apply _ hs, withDensity_apply _ hs]
    exact lintegral_mono' (Measure.restrict_mono le_rfl hμ) le_rfl
  have hscale : (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) =
      (t : ℝ) ^ (-(d : ℝ) / 2) * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := by
    have heq : (((t / 2 : ℝ≥0) : ℝ)) = (t : ℝ) * (1 / 2 : ℝ) := by simp; ring
    rw [heq, Real.mul_rpow htR.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hpow : 0 ≤ (t : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg htR.le _
  have hhalf : ((t / 2 : ℝ≥0) : ℝ) = (t : ℝ) / 2 := by simp
  calc
    _ ≤ μ.withDensity f := henv t ht x
    _ ≤ (ENNReal.ofReal E • (volume : Measure (Vec d))).withDensity f := hmeasure
    _ = (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal E * f y) := by
      rw [withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ _ := by
      apply withDensity_mono
      filter_upwards [] with y
      have heval : ENNReal.ofReal E * f y = ENNReal.ofReal
          (E * (2 * (A * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) *
            Real.exp (A * ((t / 2 : ℝ≥0) : ℝ))) *
            Real.exp (-(b * euclideanNorm (y - x) ^ 2 /
              (8 * ((t / 2 : ℝ≥0) : ℝ)))))) := by
        dsimp [f]
        rw [ENNReal.ofReal_mul hE.le,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 *
            (A * ((t : ℝ) / 2) ^ (-(d : ℝ) / 2) *
              Real.exp (A * ((t : ℝ) / 2)))),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [heval]
      apply ENNReal.ofReal_le_ofReal
      rw [hscale, hhalf]
      have hexp : A * ((t : ℝ) / 2) +
          -(b * euclideanNorm (y - x) ^ 2 / (8 * ((t : ℝ) / 2))) ≤
          C * (t : ℝ) - (b / 4) * euclideanNorm (y - x) ^ 2 / (t : ℝ) := by
        have ha : A * ((t : ℝ) / 2) ≤ C * (t : ℝ) := by nlinarith
        have heq : b * euclideanNorm (y - x) ^ 2 / (8 * ((t : ℝ) / 2)) =
            (b / 4) * euclideanNorm (y - x) ^ 2 / (t : ℝ) := by
          field_simp
          ring
        linarith
      have hcoef : D * (t : ℝ) ^ (-(d : ℝ) / 2) ≤
          C * (t : ℝ) ^ (-(d : ℝ) / 2) := mul_le_mul_of_nonneg_right hDC hpow
      have hreal := Real.exp_le_exp.mpr hexp
      have hnonneg : 0 ≤ C * (t : ℝ) ^ (-(d : ℝ) / 2) := mul_nonneg hC.le hpow
      have hproduct := mul_le_mul hcoef hreal (Real.exp_nonneg _) hnonneg
      rw [Real.exp_add] at hproduct
      convert hproduct using 1; dsimp [D]; ring

#print axioms u8_unforced_physical_gaussian_kernel_domination

/-- Time scaling turns a fourth-increment estimate into a quadratic modulus on the unit interval. -/
theorem u8_normalized_fourth_increment_scalar (T h : ℝ)
    (hT : 0 ≤ T) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (T * h) ^ 2 + (T * h) ^ 4 ≤ (T ^ 2 + T ^ 4) * h ^ 2 := by
  have hh2 : h ^ 2 ≤ 1 := by nlinarith
  have hh4 : h ^ 4 ≤ h ^ 2 := by
    have hb := mul_le_mul_of_nonneg_left hh2 (sq_nonneg h)
    nlinarith
  calc
    (T * h) ^ 2 + (T * h) ^ 4 = T ^ 2 * h ^ 2 + T ^ 4 * h ^ 4 := by ring
    _ ≤ T ^ 2 * h ^ 2 + T ^ 4 * h ^ 2 :=
      add_le_add_right (mul_le_mul_of_nonneg_left hh4 (pow_nonneg hT 4)) _
    _ = (T ^ 2 + T ^ 4) * h ^ 2 := by ring

/-- Clipping nonnegative times at one preserves order and does not increase increments. -/
theorem u8_clip_unit_increment (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ min t 1 - min s 1 ∧
      min t 1 - min s 1 ≤ 1 ∧ min t 1 - min s 1 ≤ t - s := by
  rcases le_total s 1 with hs1 | h1s
  · rcases le_total t 1 with ht1 | h1t
    · simp only [min_eq_left hs1, min_eq_left ht1]
      constructor
      · linarith
      constructor <;> linarith
    · simp only [min_eq_left hs1, min_eq_right h1t]
      constructor
      · linarith
      constructor <;> linarith
  · have h1t : 1 ≤ t := le_trans h1s hst
    simp only [min_eq_right h1s, min_eq_right h1t, sub_self]
    constructor
    · exact le_rfl
    constructor <;> linarith

/-- The clipped scaled increment has a global quadratic fourth-moment modulus. -/
theorem u8_clipped_normalized_fourth_scalar (T s t : ℝ)
    (hT : 0 ≤ T) (hs : 0 ≤ s) (hst : s ≤ t) :
    (T * (min t 1 - min s 1)) ^ 2 +
        (T * (min t 1 - min s 1)) ^ 4 ≤
      (T ^ 2 + T ^ 4) * (t - s) ^ 2 := by
  obtain ⟨h0, h1, hle⟩ := u8_clip_unit_increment s t hs hst
  have hsq : (min t 1 - min s 1) ^ 2 ≤ (t - s) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hle)
      (add_nonneg (sub_nonneg.mpr hst) h0)
    nlinarith
  exact (u8_normalized_fourth_increment_scalar T (min t 1 - min s 1) hT h0 h1).trans
    (mul_le_mul_of_nonneg_left hsq (by positivity))

end EinsteinFull
