import EinsteinFull.Calculus.U7RegularGaussianDensity
import EinsteinFull.Calculus.U1GMPFullRealization

open EinsteinRelation EinsteinRelation.SpatialDirichlet MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- A weighted squared bounded density is controlled by the corresponding weighted measure. -/
theorem u1_weighted_density_square_bound {d : ℕ}
    (μ ν : Measure (Vec d)) (p : Vec d → ℝ) (M : ℝ)
    (hp : Measurable p) (hn : ∀ y, 0 ≤ p y) (hM : 0 ≤ M)
    (hb : ∀ y, p y ≤ M)
    (hrep : ν = μ.withDensity (fun y => ENNReal.ofReal (p y)))
    (w : Vec d → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ y, w y * ENNReal.ofReal (p y ^ 2) ∂μ) ≤
      ENNReal.ofReal M * (∫⁻ y, w y ∂ν) := by
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal M * (ENNReal.ofReal (p y) * w y) ∂μ := by
      apply lintegral_mono
      intro y
      have h : ENNReal.ofReal (p y ^ 2) ≤ ENNReal.ofReal M * ENNReal.ofReal (p y) := by
        rw [← ENNReal.ofReal_mul hM]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [hn y, hb y]
      calc
        _ ≤ w y * (ENNReal.ofReal M * ENNReal.ofReal (p y)) := by simpa only [mul_comm] using mul_le_mul_left h (w y)
        _ = _ := by ac_rfl
    _ = ENNReal.ofReal M * (∫⁻ y, ENNReal.ofReal (p y) * w y ∂μ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
      rw [hrep, lintegral_withDensity_eq_lintegral_mul μ hp.ennreal_ofReal hw]
      rfl

#print axioms u1_weighted_density_square_bound

/-- An actual unforced row inherits a weighted squared-density bound from its coordinate moment. -/
theorem u1_unforced_weighted_density_square_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℝ) (t : ℝ≥0) (x : Vec d)
      (p : Vec d → ℝ) (M : ℝ),
      Measurable p → (∀ y, 0 ≤ p y) → 0 ≤ M → (∀ y, p y ≤ M) →
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x =
        (physicalReversibleMeasure ω hd 0).withDensity
          (fun y => ENNReal.ofReal (p y)) →
      (∫⁻ y, ENNReal.ofReal (Real.exp (q * ((y - x) (firstCoordinateIndex hd)))) *
        ENNReal.ofReal (p y ^ 2) ∂physicalReversibleMeasure ω hd 0) ≤
        ENNReal.ofReal M * ENNReal.ofReal
          (Real.exp (A * (|q| + q ^ 2) * (t : ℝ))) := by
  obtain ⟨A, hA, hm⟩ := u8_regular_signed_uniform_coordinate_mgf hd ω 0 Λ hΛ hω
  refine ⟨A, hA, ?_⟩
  intro q t x p M hp hn hM hb hrep
  let w : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal
    (Real.exp (q * ((y - x) (firstCoordinateIndex hd))))
  have hw : Measurable w := (Real.continuous_exp.comp (continuous_const.mul
    ((continuous_apply _).sub continuous_const))).measurable.ennreal_ofReal
  exact (u1_weighted_density_square_bound _ _ p M hp hn hM hb hrep w hw).trans
    (mul_le_mul_right (hm q (firstCoordinateIndex hd) t x) _)

#print axioms u1_unforced_weighted_density_square_bound

/-- Two nonnegative rows with the same squared-integral bound have bounded pairing. -/
theorem u1_lintegral_pairing_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ≥0∞) (B : ℝ≥0∞)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfB : (∫⁻ z, f z ^ (2 : ℝ) ∂μ) ≤ B)
    (hgB : (∫⁻ z, g z ^ (2 : ℝ) ∂μ) ≤ B) :
    (∫⁻ z, f z * g z ∂μ) ≤ B := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  calc
    _ ≤ (∫⁻ z, f z ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ z, g z ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by simpa only [Pi.mul_apply] using hh
    _ ≤ B ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hfB (by norm_num))
        (ENNReal.rpow_le_rpow hgB (by norm_num))
    _ = B := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

#print axioms u1_lintegral_pairing_bound

/-- Squaring a gauged row doubles its tilt. -/
theorem u1_gauged_row_square {d : ℕ} (i : Fin d) (q : ℝ)
    (p : Vec d → ℝ) (x z : Vec d) (hp : 0 ≤ p z) :
    (ENNReal.ofReal (Real.exp (q * ((z - x) i))) * ENNReal.ofReal (p z)) ^ (2 : ℝ) =
      ENNReal.ofReal (Real.exp ((2 * q) * ((z - x) i))) * ENNReal.ofReal (p z ^ 2) := by
  rw [ENNReal.rpow_two, mul_pow, pow_two, pow_two, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul hp, ← Real.exp_add]
  congr 2 <;> ring

#print axioms u1_gauged_row_square

/-- Oppositely gauged rows control their symmetric convolution at almost every endpoint. -/
theorem u1_unforced_weighted_convolution_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℝ) (t : ℝ≥0) (p : Vec d → Vec d → ℝ) (M : ℝ),
      Measurable (Function.uncurry p) → (∀ x z, 0 ≤ p x z) → 0 ≤ M →
      (∀ x z, p x z ≤ M) →
      (∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x =
        (physicalReversibleMeasure ω hd 0).withDensity (fun z => ENNReal.ofReal (p x z))) →
      (∀ᵐ z ∂(physicalReversibleMeasure ω hd 0).prod (physicalReversibleMeasure ω hd 0),
        p z.1 z.2 = p z.2 z.1) →
      ∀ x, ∀ᵐ y ∂physicalReversibleMeasure ω hd 0,
        (∫⁻ z, ENNReal.ofReal (Real.exp (q * ((y - x) (firstCoordinateIndex hd)))) *
          (ENNReal.ofReal (p x z) * ENNReal.ofReal (p z y))
          ∂physicalReversibleMeasure ω hd 0) ≤
          ENNReal.ofReal M * ENNReal.ofReal
            (Real.exp (A * (|2 * q| + (2 * q) ^ 2) * (t : ℝ))) := by
  obtain ⟨A, hA, hr⟩ := u1_unforced_weighted_density_square_bound hd ω Λ hΛ hω
  refine ⟨A, hA, ?_⟩
  intro q t p M hp hn hM hb hrep hs x
  let μ := physicalReversibleMeasure ω hd 0
  let : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω 0
  have hs' := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hs)
  filter_upwards [hs'] with y hy
  let f : Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal
    (Real.exp (q * ((z - x) (firstCoordinateIndex hd)))) * ENNReal.ofReal (p x z)
  let g : Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal
    (Real.exp ((-q) * ((z - y) (firstCoordinateIndex hd)))) * ENNReal.ofReal (p y z)
  let B := ENNReal.ofReal M * ENNReal.ofReal
    (Real.exp (A * (|2 * q| + (2 * q) ^ 2) * (t : ℝ)))
  have hp' (a : Vec d) : Measurable (p a) := hp.comp (measurable_const.prodMk measurable_id)
  have hf : AEMeasurable f μ := ((Real.continuous_exp.comp (continuous_const.mul
    ((continuous_apply _).sub continuous_const))).measurable.ennreal_ofReal.mul
    (hp' x).ennreal_ofReal).aemeasurable
  have hg : AEMeasurable g μ := ((Real.continuous_exp.comp (continuous_const.mul
    ((continuous_apply _).sub continuous_const))).measurable.ennreal_ofReal.mul
    (hp' y).ennreal_ofReal).aemeasurable
  have hfB : (∫⁻ z, f z ^ (2 : ℝ) ∂μ) ≤ B := by
    simp_rw [f, u1_gauged_row_square _ _ _ _ _ (hn x _)]
    exact hr (2 * q) t x (p x) M (hp' x) (hn x) hM (hb x) (hrep x)
  have hgB : (∫⁻ z, g z ^ (2 : ℝ) ∂μ) ≤ B := by
    simp_rw [g, u1_gauged_row_square _ _ _ _ _ (hn y _)]
    simpa only [mul_neg, abs_neg, neg_sq] using
      hr (2 * (-q)) t y (p y) M (hp' y) (hn y) hM (hb y) (hrep y)
  have hpair := u1_lintegral_pairing_bound μ f g B hf hg hfB hgB
  calc
    _ = ∫⁻ z, f z * g z ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hy] with z hz
      change p z y = p y z at hz
      dsimp [f, g]
      rw [hz]
      have he : q * ((z - x) (firstCoordinateIndex hd)) +
          -q * ((z - y) (firstCoordinateIndex hd)) =
            q * ((y - x) (firstCoordinateIndex hd)) := by
        simp only [Pi.sub_apply]; ring
      calc
        _ = (ENNReal.ofReal (Real.exp (q * ((z - x) (firstCoordinateIndex hd)))) *
             ENNReal.ofReal (Real.exp (-q * ((z - y) (firstCoordinateIndex hd))))) *
             (ENNReal.ofReal (p x z) * ENNReal.ofReal (p y z)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, he]
          simp only [Pi.sub_apply]
        _ = _ := by ac_rfl
    _ ≤ _ := hpair

#print axioms u1_unforced_weighted_convolution_bound


/-- The weighted actual kernel has a uniform half-time density bound. -/
theorem u1_weighted_unforced_kernel_half_time_domination
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧ ∀ (t : ℝ≥0), 0 < t → ∀ x,
      (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x).withDensity
        (fun y => ENNReal.ofReal
          (Real.exp (lam * ((y - x) (firstCoordinateIndex hd))))) ≤
      ENNReal.ofReal (D * (((t / 4 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) *
        Real.exp (A * (|2 * lam| + (2 * lam) ^ 2) * ((t / 2 : ℝ≥0) : ℝ))) •
          physicalReversibleMeasure ω hd 0 := by
  obtain ⟨D, hD, hp⟩ := u7_unforced_kernel_bounded_symmetric_density hd ω Λ hΛ hω
  obtain ⟨A, hA, hc⟩ := u1_unforced_weighted_convolution_bound hd ω Λ hΛ hω
  refine ⟨D, A, hD, hA, ?_⟩
  intro t ht x
  let s : ℝ≥0 := t / 2
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨p, hpmeas, hb, hrep, hsym⟩ := hp s hs
  let μ := physicalReversibleMeasure ω hd 0
  let K := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω s
  let : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω 0
  let q : Vec d → Vec d → ℝ≥0∞ := fun a b => ENNReal.ofReal (p a b)
  have hq : Measurable (Function.uncurry q) := hpmeas.ennreal_ofReal
  have hcomp := u7_kernel_comp_density μ K q hq hrep
  have hadd : s + s = t := by dsimp [s]; exact add_halves t
  have hkernel : u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t = K.comp K := by
    rw [← hadd, (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω).kernel_add]
  let f : Vec d → ℝ≥0∞ := fun y => ∫⁻ z, q x z * q z y ∂μ
  let w : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal
    (Real.exp (lam * ((y - x) (firstCoordinateIndex hd))))
  have hf : Measurable f := hcomp.1.comp (measurable_const.prodMk measurable_id)
  have hw : Measurable w := (Real.continuous_exp.comp (continuous_const.mul
    ((continuous_apply _).sub continuous_const))).measurable.ennreal_ofReal
  have hbound := hc lam s p (D * (((s / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)))
    hpmeas (fun a b => (hb a b).1) (by positivity) (fun a b => (hb a b).2) hrep hsym x
  have hscale : (s / 2 : ℝ≥0) = t / 4 := by dsimp [s]; ring
  rw [hkernel, hcomp.2 x, ← withDensity_mul μ hf hw]
  calc
    _ ≤ μ.withDensity (fun _ => ENNReal.ofReal
        (D * (((s / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))) * ENNReal.ofReal
        (Real.exp (A * (|2 * lam| + (2 * lam) ^ 2) * (s : ℝ)))) := by
      apply withDensity_mono
      filter_upwards [hbound] with y hy
      change f y * w y ≤ _
      dsimp only [f]
      rw [mul_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact hy
    _ = _ := by
      rw [withDensity_const, ← ENNReal.ofReal_mul (by positivity), hscale]

#print axioms u1_weighted_unforced_kernel_half_time_domination


theorem u1_weighted_unforced_kernel_uniform_domination
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ x,
      (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x).withDensity
        (fun y => ENNReal.ofReal
          (Real.exp (lam * ((y - x) (firstCoordinateIndex hd))))) ≤
        ENNReal.ofReal (C * (t : ℝ) ^ (-(d : ℝ) / 2) *
          Real.exp (C * (t : ℝ))) • (volume : Measure (Vec d)) := by
  obtain ⟨D, A, hD, hA, hdom⟩ :=
    u1_weighted_unforced_kernel_half_time_domination hd ω lam Λ hΛ hω
  let E := Real.exp (2 * Λ)
  let F := D * (1 / 4 : ℝ) ^ (-(d : ℝ) / 2) * E
  let B := A * (|2 * lam| + (2 * lam) ^ 2)
  let C := F + B + 1
  have hE : 0 < E := Real.exp_pos _
  have hF : 0 < F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hFC : F ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpow : 0 ≤ (t : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg htR.le _
  have hscale : (((t / 4 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) =
      (t : ℝ) ^ (-(d : ℝ) / 2) * (1 / 4 : ℝ) ^ (-(d : ℝ) / 2) := by
    have heq : (((t / 4 : ℝ≥0) : ℝ)) = (t : ℝ) * (1 / 4 : ℝ) := by simp; ring
    rw [heq, Real.mul_rpow htR.le (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hhalf : ((t / 2 : ℝ≥0) : ℝ) = (t : ℝ) / 2 := by simp
  have hnum : D * (((t / 4 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) *
        Real.exp (A * (|2 * lam| + (2 * lam) ^ 2) * ((t / 2 : ℝ≥0) : ℝ)) * E ≤
      C * (t : ℝ) ^ (-(d : ℝ) / 2) * Real.exp (C * (t : ℝ)) := by
    have hcoef : F * (t : ℝ) ^ (-(d : ℝ) / 2) ≤
        C * (t : ℝ) ^ (-(d : ℝ) / 2) := mul_le_mul_of_nonneg_right hFC hpow
    have he : B * ((t : ℝ) / 2) ≤ C * (t : ℝ) := by nlinarith
    have hh := mul_le_mul hcoef (Real.exp_le_exp.mpr he) (Real.exp_nonneg _)
      (mul_nonneg hC.le hpow)
    rw [hscale, hhalf]
    convert hh using 1; dsimp [F, B]; ring
  calc
    _ ≤ ENNReal.ofReal (D * (((t / 4 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) *
        Real.exp (A * (|2 * lam| + (2 * lam) ^ 2) * ((t / 2 : ℝ≥0) : ℝ))) •
          physicalReversibleMeasure ω hd 0 := hdom t ht x
    _ ≤ ENNReal.ofReal (D * (((t / 4 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) *
        Real.exp (A * (|2 * lam| + (2 * lam) ^ 2) * ((t / 2 : ℝ≥0) : ℝ))) •
          (ENNReal.ofReal E • (volume : Measure (Vec d))) := by
      gcongr
      exact (u4_unforced_physical_measure_comparable hd ω Λ hω).1
    _ ≤ _ := by
      rw [smul_smul, ← ENNReal.ofReal_mul (by positivity)]
      apply Measure.le_iff.mpr
      intro s hs
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hnum) _

#print axioms u1_weighted_unforced_kernel_uniform_domination


/-- Every positive-time signed kernel has a uniformly bounded normalized density. -/
theorem u1_regular_signed_bounded_normalized_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ (M : ℝ) (p : Vec d → Vec d → ℝ), 0 < M ∧
      Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨C, hC, hweighted⟩ :=
    u1_weighted_unforced_kernel_uniform_domination hd ω lam Λ hΛ hω
  obtain ⟨A, hA, hgauge⟩ := u7_regular_signed_kernel_gauge_domination hd ω lam Λ hΛ hω
  let B := C * (t : ℝ) ^ (-(d : ℝ) / 2) * Real.exp (C * (t : ℝ))
  let M := Real.exp (A * (t : ℝ)) * B
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hB : 0 < B := by dsimp [B]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hdom : ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≤
      ENNReal.ofReal M • (volume : Measure (Vec d)) := by
    intro x
    have hfirst : u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≤
        ENNReal.ofReal (Real.exp (A * (t : ℝ))) •
          ((u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x).withDensity
            (fun y => ENNReal.ofReal
              (Real.exp (lam * ((y - x) (firstCoordinateIndex hd)))))) := by
      apply Measure.le_iff.mpr
      intro s hs
      rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
      simpa only [firstCoordinateIndex] using hgauge t x s hs
    calc
      _ ≤ _ := hfirst
      _ ≤ ENNReal.ofReal (Real.exp (A * (t : ℝ))) •
          (ENNReal.ofReal B • (volume : Measure (Vec d))) := by
        apply Measure.le_iff.mpr
        intro s hs
        simp only [Measure.smul_apply, smul_eq_mul]
        simpa only [Measure.smul_apply, smul_eq_mul] using
          mul_le_mul_right (Measure.le_iff.mp (hweighted t ht x) s hs)
            (ENNReal.ofReal (Real.exp (A * (t : ℝ))))
      _ = _ := by rw [smul_smul, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  obtain ⟨p, hp, hb, hi, hr⟩ :=
    u1_regular_signed_bounded_normalized_density_of_domination hd ω lam Λ hΛ hω t M hM hdom
  exact ⟨M, p, hM, hp, hb, hi, hr⟩

#print axioms u1_regular_signed_bounded_normalized_density

/-- The regular signed kernel has a bounded normalized density at every start. -/
theorem u1_regular_signed_kernel_bounded_normalized_density {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ (M : ℝ) (p : Vec d → Vec d → ℝ), 0 < M ∧
      Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (p x y)) :=
  u1_regular_signed_bounded_normalized_density hd ω lam Λ hΛ hω t ht

#print axioms u1_regular_signed_kernel_bounded_normalized_density


/-- The positive-time signed kernel acts on every Lebesgue-integrable function
with a bound uniform in the starting point. -/
theorem u1_regular_signed_kernel_L1_to_pointwise_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f : Vec d → ℝ), Integrable f volume →
      ∀ x, Integrable f (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
        |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
          M * ∫ y, |f y| := by
  obtain ⟨M, p, hM, hp, hb, hi, hr⟩ :=
    u1_regular_signed_kernel_bounded_normalized_density hd ω lam Λ hΛ hω t ht
  have hdom : ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≤
      ENNReal.ofReal M • (volume : Measure (Vec d)) := by
    intro x
    rw [hr x, ← withDensity_const]
    apply withDensity_mono
    exact Filter.Eventually.of_forall fun y => ENNReal.ofReal_le_ofReal (hb x y).2
  refine ⟨M, hM, ?_⟩
  intro f hf x
  refine ⟨memLp_one_iff_integrable.mp <| (memLp_one_iff_integrable.mpr hf).of_measure_le_smul
    (c := ENNReal.ofReal M) ENNReal.ofReal_ne_top (hdom x), ?_⟩
  calc
    |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        ∫ y, |f y| ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
    _ ≤ M * ∫ y, |f y| := by
      apply integral_le_const_mul_of_measure_le
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) volume M hM.le (hdom x)
        (fun y => |f y|) (Filter.Eventually.of_forall fun y => abs_nonneg _)
      simpa only [Real.norm_eq_abs] using hf.norm

#print axioms u1_regular_signed_kernel_L1_to_pointwise_bound

end EinsteinFull
