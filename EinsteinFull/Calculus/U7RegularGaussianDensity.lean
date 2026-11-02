import EinsteinFull.Calculus.U5RegularReversibleDensity
import EinsteinFull.Calculus.U8RegularSignedMoments
import EinsteinFull.Calculus.U6JointSignedKernelDensity
import EinsteinFull.Calculus.U8GaussianRowTails

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- The unforced kernel has a quantitatively bounded reversible density which is
symmetric almost everywhere. -/
theorem u7_unforced_kernel_bounded_symmetric_density {d : ℕ}
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

#print axioms u7_unforced_kernel_bounded_symmetric_density


/-- Composition of a kernel with a jointly measurable density has the
corresponding convolution density, at every starting point. -/
theorem u7_kernel_comp_density {d : ℕ}
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

#print axioms u7_kernel_comp_density


/-- An unforced row envelope transfers through the actual signed gauge. -/
theorem u7_regular_signed_kernel_gauge_envelope
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (b : Vec d → Vec d → ℝ),
      Measurable (Function.uncurry b) → (∀ x y, 0 ≤ b x y) →
      (∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≤
        volume.withDensity (fun y => ENNReal.ofReal (b x y))) →
      ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≤
        volume.withDensity (fun y => ENNReal.ofReal
          (Real.exp (C * (t : ℝ)) * Real.exp (lam * ((y - x) ⟨0, by omega⟩)) * b x y)) := by
  obtain ⟨C, hC, hgauge⟩ := u7_regular_signed_kernel_gauge_domination hd ω lam Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro t b hb hb0 hdom x
  let w : Vec d → ℝ := fun y => Real.exp (lam * ((y - x) ⟨0, by omega⟩))
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hbx : Measurable (b x) := hb.comp (measurable_const.prodMk measurable_id)
  apply Measure.le_iff.mpr
  intro s hs
  calc
    _ ≤ ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
        ∫⁻ y in s, ENNReal.ofReal (w y)
          ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x := hgauge t x s hs
    _ ≤ ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
        ∫⁻ y in s, ENNReal.ofReal (w y)
          ∂volume.withDensity (fun y => ENNReal.ofReal (b x y)) := by
      gcongr
      exact hdom x
    _ = volume.withDensity (fun y => ENNReal.ofReal
        (Real.exp (C * (t : ℝ)) * Real.exp (lam * ((y - x) ⟨0, by omega⟩)) * b x y)) s := by
      rw [setLIntegral_withDensity_eq_setLIntegral_mul volume hbx.ennreal_ofReal hw.ennreal_ofReal hs,
        withDensity_apply _ hs, ← lintegral_const_mul _ (hbx.ennreal_ofReal.mul hw.ennreal_ofReal)]
      congr 1
      funext y
      simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (hb0 x y),
        ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 1
      dsimp [w]
      ring

#print axioms u7_regular_signed_kernel_gauge_envelope

/-- The transferred gauge envelope can be realized by a jointly measurable density. -/
theorem u7_regular_signed_density_of_unforced_envelope
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t →
      ∀ (b : Vec d → Vec d → ℝ),
      Measurable (Function.uncurry b) → (∀ x y, 0 ≤ b x y) →
      (∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≤
        volume.withDensity (fun y => ENNReal.ofReal (b x y))) →
      ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
        (∀ x y, 0 ≤ p x y ∧ p x y ≤
          Real.exp (C * (t : ℝ)) * Real.exp (lam * ((y - x) ⟨0, by omega⟩)) * b x y) ∧
        ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨C, hC, hdom⟩ := u7_regular_signed_kernel_gauge_envelope hd ω lam Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro t ht b hb hb0 hbound
  obtain ⟨p, hp, hp0, _, hrep⟩ :=
    u7_regular_signed_kernel_normalized_density hd ω lam Λ hΛ hω t ht
  let envelope : Vec d → Vec d → ℝ := fun x y =>
    Real.exp (C * (t : ℝ)) * Real.exp (lam * ((y - x) ⟨0, by omega⟩)) * b x y
  have he : Measurable (Function.uncurry envelope) := by
    dsimp [envelope]
    fun_prop
  have he0 : ∀ x y, 0 ≤ envelope x y := by
    intro x y
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (hb0 x y)
  exact u7_real_density_clipped_of_domination _ p envelope hp he hp0 he0 hrep
    (hdom t b hb hb0 hbound)

#print axioms u7_regular_signed_density_of_unforced_envelope

/-- A linear displacement term is absorbed into a quadratic Gaussian exponent. -/
theorem u7_gaussian_absorb_linear (lam c t r z : ℝ)
    (hc : 0 < c) (ht : 0 < t) (hz : |z| ≤ r) :
    lam * z - c * r ^ 2 / t ≤
      (lam ^ 2 / (2 * c)) * t - (c / 2) * r ^ 2 / t := by
  have hl : lam * z ≤ |lam| * r :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hz (abs_nonneg _))
  have hs : 0 ≤ (c * r - |lam| * t) ^ 2 := sq_nonneg _
  have habs : |lam| ^ 2 = lam ^ 2 := sq_abs lam
  have hd : 0 < 2 * c * t := by positivity
  have hq : |lam| * r ≤ (c ^ 2 * r ^ 2 + lam ^ 2 * t ^ 2) / (2 * c * t) := by
    apply (le_div_iff₀ hd).2
    nlinarith
  have heq : (c ^ 2 * r ^ 2 + lam ^ 2 * t ^ 2) / (2 * c * t) =
      (lam ^ 2 / (2 * c)) * t + (c / 2) * r ^ 2 / t := by
    field_simp; ring
  rw [heq] at hq
  have he : c * r ^ 2 / t = 2 * ((c / 2) * r ^ 2 / t) := by ring
  linarith

#print axioms u7_gaussian_absorb_linear

/-- Gaussian unforced domination yields the full signed Gaussian density estimate. -/
theorem u7_regular_signed_gaussian_density_of_unforced_domination
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hunforced : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t →
      ∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≤
        volume.withDensity (fun y => ENNReal.ofReal
          (A * (t : ℝ) ^ (-(d : ℝ) / 2) *
            Real.exp (A * (t : ℝ) - c * euclideanNorm (y - x) ^ 2 / (t : ℝ))))) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t →
      ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
        (∀ x y, 0 ≤ p x y ∧ p x y ≤
          C * (t : ℝ) ^ (-(d : ℝ) / 2) *
            Real.exp (C * (t : ℝ) - c * euclideanNorm (y - x) ^ 2 / (t : ℝ))) ∧
        ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨A, c, hA, hc, hdom⟩ := hunforced
  obtain ⟨G, hG, htransfer⟩ :=
    u7_regular_signed_density_of_unforced_envelope hd ω lam Λ hΛ hω
  let C : ℝ := A + G + lam ^ 2 / (2 * c) + 1
  have htilt : 0 ≤ lam ^ 2 / (2 * c) := by positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hCG : A + G + lam ^ 2 / (2 * c) ≤ C := by dsimp [C]; linarith
  refine ⟨C, c / 2, hC, by positivity, ?_⟩
  intro t ht
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  let b : Vec d → Vec d → ℝ := fun x y =>
    A * (t : ℝ) ^ (-(d : ℝ) / 2) *
      Real.exp (A * (t : ℝ) - c * euclideanNorm (y - x) ^ 2 / (t : ℝ))
  have hnorm : Continuous (fun z : Vec d × Vec d => euclideanNorm (z.2 - z.1)) :=
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_snd.sub continuous_fst)
  have hb : Measurable (Function.uncurry b) := by
    dsimp [b, Function.uncurry]
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.sub
      ((continuous_const.mul (hnorm.pow 2)).div_const _)))).measurable
  have hb0 : ∀ x y, 0 ≤ b x y := by
    intro x y
    dsimp [b]
    positivity
  obtain ⟨p, hp, hpbound, hrep⟩ := htransfer t ht b hb hb0 (hdom t ht)
  refine ⟨p, hp, ?_, hrep⟩
  intro x y
  refine ⟨(hpbound x y).1, (hpbound x y).2.trans ?_⟩
  have hz := Regeneration.coordinate_abs_le_euclideanNorm (y - x) (⟨0, by omega⟩ : Fin d)
  have habs := u7_gaussian_absorb_linear lam c (t : ℝ) (euclideanNorm (y - x))
    ((y - x) ⟨0, by omega⟩) hc htR hz
  have htime := mul_le_mul_of_nonneg_right hCG htR.le
  have hexp : G * (t : ℝ) + lam * ((y - x) ⟨0, by omega⟩) +
      (A * (t : ℝ) - c * euclideanNorm (y - x) ^ 2 / (t : ℝ)) ≤
      C * (t : ℝ) - (c / 2) * euclideanNorm (y - x) ^ 2 / (t : ℝ) := by
    nlinarith
  have hcoeff : A * (t : ℝ) ^ (-(d : ℝ) / 2) ≤
      C * (t : ℝ) ^ (-(d : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg htR.le _)
  dsimp [b]
  calc
    _ = (A * (t : ℝ) ^ (-(d : ℝ) / 2)) *
        Real.exp (G * (t : ℝ) + lam * ((y - x) ⟨0, by omega⟩) +
          (A * (t : ℝ) - c * euclideanNorm (y - x) ^ 2 / (t : ℝ))) := by
      rw [Real.exp_add, Real.exp_add]
      ac_rfl
    _ ≤ (C * (t : ℝ) ^ (-(d : ℝ) / 2)) *
        Real.exp (C * (t : ℝ) - (c / 2) * euclideanNorm (y - x) ^ 2 / (t : ℝ)) :=
      mul_le_mul hcoeff (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)

#print axioms u7_regular_signed_gaussian_density_of_unforced_domination

/-- A jointly measurable envelope can clip a single time-space density while
preserving every positive-time transition measure. -/
theorem u7_joint_density_clipped_of_domination
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (b : ℝ≥0 → Vec d → Vec d → ℝ)
    (hb : Measurable (fun z : ℝ≥0 × Vec d × Vec d => b z.1 z.2.1 z.2.2))
    (hb0 : ∀ t x y, 0 ≤ b t x y)
    (hdom : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≤
        volume.withDensity (fun y => ENNReal.ofReal (b t x y))) :
    ∃ p : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ p t x y ∧ p t x y ≤ b t x y) ∧
      ∀ (t : ℝ≥0), 0 < t → ∀ x,
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y)) := by
  obtain ⟨q, hq, hq0, hrep⟩ :=
    u6_regular_signed_joint_time_space_density hd ω lam Λ hΛ hω
  refine ⟨fun t x y => min (q t x y) (b t x y), hq.min hb, ?_, ?_⟩
  · intro t x y
    exact ⟨le_min (hq0 t x y) (hb0 t x y), min_le_right _ _⟩
  · intro t ht x
    have hqx : Measurable (q t x) := hq.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hae : (fun y => ENNReal.ofReal (q t x y)) ≤ᵐ[volume]
        (fun y => ENNReal.ofReal (b t x y)) := by
      apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hqx.ennreal_ofReal.aemeasurable
      intro s hs _
      rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, ← (hrep t ht x).2.2]
      exact Measure.le_iff.mp (hdom t ht x) s hs
    rw [(hrep t ht x).2.2]
    apply withDensity_congr_ae
    filter_upwards [hae] with y hy
    have hle : q t x y ≤ b t x y := (ENNReal.ofReal_le_ofReal_iff (hb0 t x y)).mp hy
    simp only [min_eq_left hle]

#print axioms u7_joint_density_clipped_of_domination

/-- The row-wise Gaussian estimate can be realized by one jointly measurable
clipped density for all positive times. -/
theorem u7_joint_gaussian_density_of_unforced_domination
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hunforced : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t →
      ∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≤
        volume.withDensity (fun y => ENNReal.ofReal
          (A * (t : ℝ) ^ (-(d : ℝ) / 2) *
            Real.exp (A * (t : ℝ) - c * euclideanNorm (y - x) ^ 2 / (t : ℝ))))) :
    ∃ (C c : ℝ) (p : ℝ≥0 → Vec d → Vec d → ℝ),
      0 < C ∧ 0 < c ∧
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x y,
        0 ≤ p t x y ∧ p t x y ≤
          C * (t : ℝ) ^ (-((d : ℝ) / 2)) *
            Real.exp (C * (t : ℝ) - c * ‖WithLp.toLp 2 (y - x)‖ ^ 2 / (t : ℝ))) ∧
      ∀ (t : ℝ≥0), 0 < t → ∀ x,
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y)) := by
  obtain ⟨C, c, hC, hc, hrows⟩ :=
    u7_regular_signed_gaussian_density_of_unforced_domination hd ω lam Λ hΛ hω hunforced
  let b : ℝ≥0 → Vec d → Vec d → ℝ := fun t x y =>
    C * (t : ℝ) ^ (-(d : ℝ) / 2) *
      Real.exp (C * (t : ℝ) - c * euclideanNorm (y - x) ^ 2 / (t : ℝ))
  have hpw : Measurable (fun t : ℝ => t ^ (-(d : ℝ) / 2)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro t ht
    exact (Real.continuousAt_rpow_const t _ (Or.inl ht)).continuousWithinAt
  have htime : Measurable (fun z : ℝ≥0 × Vec d × Vec d => (z.1 : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_fst
  have hnorm : Measurable (fun z : ℝ≥0 × Vec d × Vec d =>
      euclideanNorm (z.2.2 - z.2.1)) :=
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d).measurable.comp
      (measurable_snd.snd.sub measurable_snd.fst)
  have hb : Measurable (fun z : ℝ≥0 × Vec d × Vec d => b z.1 z.2.1 z.2.2) := by
    dsimp [b]
    exact (measurable_const.mul (hpw.comp htime)).mul
      ((measurable_const.mul htime).sub
        ((measurable_const.mul (hnorm.pow_const 2)).div htime)).exp
  have hb0 : ∀ t x y, 0 ≤ b t x y := by
    intro t x y
    dsimp [b]
    positivity
  have hdom : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≤
        volume.withDensity (fun y => ENNReal.ofReal (b t x y)) := by
    intro t ht x
    obtain ⟨q, hq, hbound, hrep⟩ := hrows t ht
    rw [hrep x]
    apply withDensity_mono
    filter_upwards [] with y
    exact ENNReal.ofReal_le_ofReal (hbound x y).2
  obtain ⟨p, hp, hbound, hrep⟩ :=
    u7_joint_density_clipped_of_domination hd ω lam Λ hΛ hω b hb hb0 hdom
  refine ⟨C, c, p, hC, hc, hp, ?_, hrep⟩
  intro t ht x y
  simpa only [b, neg_div, TimeChange.euclideanNorm_eq_norm_toLp] using hbound t x y

#print axioms u7_joint_gaussian_density_of_unforced_domination

/-- A single jointly measurable signed transition density satisfies the
Gaussian upper bound at every positive time and every pair of points. -/
theorem u7_regular_signed_joint_gaussian_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ (C c : ℝ) (p : ℝ≥0 → Vec d → Vec d → ℝ),
      0 < C ∧ 0 < c ∧
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x y,
        0 ≤ p t x y ∧ p t x y ≤
          C * (t : ℝ) ^ (-((d : ℝ) / 2)) *
            Real.exp (C * (t : ℝ) - c * ‖WithLp.toLp 2 (y - x)‖ ^ 2 / (t : ℝ))) ∧
      ∀ (t : ℝ≥0), 0 < t → ∀ x,
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y)) :=
  u7_joint_gaussian_density_of_unforced_domination hd ω lam Λ hΛ hω
    (u8_unforced_physical_gaussian_kernel_domination hd ω Λ hΛ hω)

#print axioms u7_regular_signed_joint_gaussian_density

end EinsteinFull
