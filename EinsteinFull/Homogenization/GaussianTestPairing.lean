import EinsteinFull.Homogenization.HeatKernelThirdDerivative
import EinsteinFull.Homogenization.HeatFormulaLargeTime
import EinsteinRelation.Correctors.ReferenceSpatialCutoff
import EinsteinRelation.Correctors.RescaledSpatialCutoff
import EinsteinRelation.TimeChange.EuclideanTransport

/-!
# Pairing Gaussian tests with fields of small negative Sobolev norm

A field `F` has a pairing bound at the scales above `R₀` if its integral against a smooth test
supported in the centered ball `B_ρ`, `ρ ≥ R₀`, is at most
`A ρ^(d/2+1) (ρ/R₀)^(-κ) (ρ⁻² ‖η‖₂² + ‖∇η‖₂²)^(1/2)`: this is a normalized `H⁻¹(B_ρ)` bound of
size `ρ (ρ/R₀)^(-κ)`, the form of the corrector estimates of homogenization theory. A smooth
kernel `Ψ` with `|Ψ| ≤ B Φ_{2s}` and `|∇Ψ| ≤ B' Φ_{2s}` is not compactly supported, but cutting it
into the pieces of a partition of unity subordinate to the balls `B_{4(k+1)R}`, whose `k`-th piece
vanishes on `B_{(k+1)R}`, and summing the pairing bounds of the pieces against their Gaussian
decay, bounds `|∫ Ψ(x - y) F(y) dy|` by `C A R^(d/2+1) (R/R₀)^(-κ) (B/R + B') (8πs)^(-d/4)` for
`R ≥ R₀`, `|x| ≤ R` and `s ≤ R²`. With the heat-kernel Hessian as `Ψ` this is the large-time
decay of the heat formula (6.7) of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

/-- **Pairing bound at the scales above `R₀`**: the integral of `F` against every smooth test
supported in `B_ρ`, `ρ ≥ R₀`, is bounded by `A ρ^(d/2+1) (ρ/R₀)^(-κ)` times the `H¹` norm of the
test normalized at scale `ρ`. -/
def HasScalePairingBound (F : Vec d → ℝ) (R₀ A κ : ℝ) : Prop :=
  ∀ ρ : ℝ, R₀ ≤ ρ → ∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    tsupport η ⊆ ball 0 ρ →
      |∫ y, η y * F y| ≤ A * ρ ^ ((d : ℝ) / 2 + 1) * (ρ / R₀) ^ (-κ) *
        Real.sqrt (ρ⁻¹ ^ 2 * (∫ y, η y ^ 2) + ∫ y, euclideanSq (gradient η y))

section Calculus

theorem euclideanNorm_nonneg (x : Vec d) : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _

theorem euclideanNorm_le_add_sub (x y : Vec d) :
    euclideanNorm y ≤ euclideanNorm x + euclideanNorm (x - y) := by
  have h := TimeChange.euclideanNorm_add_le x ((-1 : ℝ) • (x - y))
  rw [TimeChange.euclideanNorm_smul, abs_neg, abs_one, one_mul] at h
  have hxy : x + (-1 : ℝ) • (x - y) = y := by
    funext l
    simp
  rwa [hxy] at h

theorem isOpen_originBall (r : ℝ) : IsOpen (originBall d r) :=
  isOpen_lt continuous_euclideanNorm continuous_const

theorem originBall_eq_ball (r : ℝ) : originBall d r = ball (0 : Vec d) r := by
  ext y
  simp [originBall, ball]

/-- The gradient of `y ↦ θ(y) Ψ(x - y)`. -/
theorem gradient_mul_comp_sub {θ Ψ : Vec d → ℝ} (hθ : Differentiable ℝ θ)
    (hΨ : Differentiable ℝ Ψ) (x y : Vec d) :
    gradient (fun z => θ z * Ψ (x - z)) y =
      (-θ y) • gradient Ψ (x - y) + Ψ (x - y) • gradient θ y := by
  have h1 := (hΨ (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  have h := ((hθ y).hasFDerivAt.mul h1).congr_of_eventuallyEq
    (f₁ := fun z => θ z * Ψ (x - z)) (Filter.Eventually.of_forall fun _ => rfl)
  funext l
  change fderiv ℝ (fun z => θ z * Ψ (x - z)) y (unitVector l) = _
  rw [h.fderiv]
  simp [gradient, coordinateDerivative]

theorem gradient_eq_zero_of_notMem_tsupport {η : Vec d → ℝ} {y : Vec d} (hy : y ∉ tsupport η) :
    gradient η y = 0 := by
  have h : fderiv ℝ η y = 0 := by
    by_contra hne
    exact hy (support_fderiv_subset ℝ hne)
  funext l
  change fderiv ℝ η y (unitVector l) = 0
  rw [h]
  rfl

theorem continuous_euclideanSq_gradient {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    Continuous (fun y => euclideanSq (gradient η y)) := by
  have hcont : Continuous (fun y => fderiv ℝ η y) := hη.continuous_fderiv (by simp)
  have hl : ∀ l : Fin d, Continuous (fun y => gradient η y l) := fun l =>
    hcont.clm_apply continuous_const
  unfold euclideanSq dot
  exact continuous_finsetSum _ fun l _ => (hl l).mul (hl l)

theorem integrable_euclideanSq_gradient {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) : Integrable (fun y => euclideanSq (gradient η y)) volume := by
  refine (continuous_euclideanSq_gradient hη).integrable_of_hasCompactSupport
    (hηc.mono' fun y hy => ?_)
  by_contra hyt
  apply hy
  simp only [gradient_eq_zero_of_notMem_tsupport hyt, euclideanSq, dot, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero]

theorem integrable_sq_of_hasCompactSupport {η : Vec d → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) : Integrable (fun y => η y ^ 2) volume :=
  (integrable_mul_of_hasCompactSupport_right hη hη hηc).congr
    (Filter.Eventually.of_forall fun y => (sq (η y)).symm)

end Calculus

section Gaussian

theorem euclideanHeatKernel_le_of_le_norm {s μ : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ) {z : Vec d}
    (hz : μ ≤ euclideanNorm z) :
    euclideanHeatKernel (2 * s) z ≤
      (8 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-μ ^ 2 / (8 * s)) := by
  unfold euclideanHeatKernel
  rw [show 4 * Real.pi * (2 * s) = 8 * Real.pi * s by ring, show 4 * (2 * s) = 8 * s by ring]
  gcongr
  rw [euclideanSq_eq_euclideanNorm_sq]
  exact pow_le_pow_left₀ hμ hz 2

theorem euclideanHeatKernel_sq_le {s μ : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ) {z : Vec d}
    (hz : μ ≤ euclideanNorm z) :
    euclideanHeatKernel (2 * s) z ^ 2 ≤
      (8 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-μ ^ 2 / (8 * s)) *
        euclideanHeatKernel (2 * s) z := by
  have h0 : 0 ≤ euclideanHeatKernel (2 * s) z := euclideanHeatKernel_nonneg (by positivity) z
  rw [sq]
  exact mul_le_mul_of_nonneg_right (euclideanHeatKernel_le_of_le_norm hs hμ hz) h0

theorem integral_euclideanHeatKernel_sub {s : ℝ} (hs : 0 < s) (x : Vec d) :
    ∫ y, euclideanHeatKernel s (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun z => euclideanHeatKernel s z) (μ := volume) x]
  exact integral_euclideanHeatKernel hs

theorem integrable_euclideanHeatKernel_sub {s : ℝ} (hs : 0 < s) (x : Vec d) :
    Integrable (fun y => euclideanHeatKernel s (x - y)) volume :=
  (integrable_euclideanHeatKernel hs).comp_sub_left x

theorem sqrt_sq_add_sq_mul_le {a b : ℝ} (E : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 * E + b ^ 2 * E) ≤ (a + b) * Real.sqrt E := by
  rw [← add_mul, Real.sqrt_mul (by positivity), ← Real.sqrt_sq (by positivity : 0 ≤ a + b)]
  gcongr
  nlinarith [mul_nonneg ha hb]

end Gaussian

section Piece

variable {F : Vec d → ℝ} {R₀ A κ : ℝ}

/-- **Pairing bound for one piece of a Gaussian test.** -/
theorem HasScalePairingBound.abs_integral_piece_le (hF : HasScalePairingBound F R₀ A κ)
    (hA : 0 ≤ A) (hR₀ : 0 < R₀) {Ψ : Vec d → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {s B B' : ℝ}
    (hs : 0 < s) (hB0 : 0 ≤ B) (hB'0 : 0 ≤ B')
    (hB : ∀ z, |Ψ z| ≤ B * euclideanHeatKernel (2 * s) z)
    (hB' : ∀ z, euclideanNorm (gradient Ψ z) ≤ B' * euclideanHeatKernel (2 * s) z)
    {θ : Vec d → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) {ρ G μ : ℝ}
    (hρ : R₀ ≤ ρ) (hθρ : tsupport θ ⊆ ball 0 ρ) (hθ1 : ∀ y, |θ y| ≤ 1) (hG0 : 0 ≤ G)
    (hG : ∀ y, euclideanNorm (gradient θ y) ≤ G) (hμ : 0 ≤ μ) (x : Vec d)
    (hθμ : ∀ y, euclideanNorm (x - y) < μ → θ =ᶠ[𝓝 y] 0) :
    |∫ y, θ y * Ψ (x - y) * F y| ≤ A * ρ ^ ((d : ℝ) / 2 + 1) * (ρ / R₀) ^ (-κ) *
      ((ρ⁻¹ * B + (G * B + B')) * Real.sqrt ((8 * Real.pi * s) ^ (-(d : ℝ) / 2) *
        Real.exp (-μ ^ 2 / (8 * s)))) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hR₀ hρ
  set E := (8 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-μ ^ 2 / (8 * s))
  have hE0 : 0 ≤ E := by positivity
  have hθd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hΨx : ContDiff ℝ (⊤ : ℕ∞) (fun y => Ψ (x - y)) := hΨ.comp (contDiff_const.sub contDiff_id)
  have hηs : ContDiff ℝ (⊤ : ℕ∞) (fun y => θ y * Ψ (x - y)) := hθ.mul hΨx
  have hηc : HasCompactSupport (fun y => θ y * Ψ (x - y)) := hθc.mul_right
  have hηρ : tsupport (fun y => θ y * Ψ (x - y)) ⊆ ball 0 ρ :=
    (tsupport_mul_subset_left).trans hθρ
  have hpair := hF ρ hρ _ hηs hηc hηρ
  have hzero : ∀ y, euclideanNorm (x - y) < μ → θ y = 0 ∧ gradient θ y = 0 := by
    intro y hy
    refine ⟨(hθμ y hy).eq_of_nhds, ?_⟩
    funext l
    change fderiv ℝ θ y (unitVector l) = 0
    rw [(hθμ y hy).fderiv_eq]
    simp
  have hK (y : Vec d) : 0 ≤ euclideanHeatKernel (2 * s) (x - y) :=
    euclideanHeatKernel_nonneg (by positivity) _
  have hL2 : ∫ y, (θ y * Ψ (x - y)) ^ 2 ≤ B ^ 2 * E := by
    have hint := (integrable_euclideanHeatKernel_sub (by positivity : 0 < 2 * s) x).const_mul
      (B ^ 2 * E)
    refine (integral_mono (integrable_sq_of_hasCompactSupport hηs.continuous hηc) hint
      fun y => ?_).trans ?_
    · by_cases hy : μ ≤ euclideanNorm (x - y)
      · have h1 : θ y ^ 2 ≤ 1 := by
          have := hθ1 y
          nlinarith [abs_nonneg (θ y), sq_abs (θ y)]
        have h2 : Ψ (x - y) ^ 2 ≤ (B * euclideanHeatKernel (2 * s) (x - y)) ^ 2 := by
          have := hB (x - y)
          nlinarith [abs_nonneg (Ψ (x - y)), sq_abs (Ψ (x - y))]
        have h3 := euclideanHeatKernel_sq_le hs hμ hy
        calc (θ y * Ψ (x - y)) ^ 2 = θ y ^ 2 * Ψ (x - y) ^ 2 := by ring
          _ ≤ 1 * (B * euclideanHeatKernel (2 * s) (x - y)) ^ 2 :=
            mul_le_mul h1 h2 (sq_nonneg _) zero_le_one
          _ = B ^ 2 * euclideanHeatKernel (2 * s) (x - y) ^ 2 := by ring
          _ ≤ B ^ 2 * (E * euclideanHeatKernel (2 * s) (x - y)) := by gcongr
          _ = B ^ 2 * E * euclideanHeatKernel (2 * s) (x - y) := by ring
      · rw [(hzero y (not_le.mp hy)).1, zero_mul]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact mul_nonneg (by positivity) (hK y)
    · rw [integral_const_mul, integral_euclideanHeatKernel_sub (by positivity) x, mul_one]
  have hgradle : ∫ y, euclideanSq (gradient (fun z => θ z * Ψ (x - z)) y) ≤
      (G * B + B') ^ 2 * E := by
    have hint := (integrable_euclideanHeatKernel_sub (by positivity : 0 < 2 * s) x).const_mul
      ((G * B + B') ^ 2 * E)
    refine (integral_mono (integrable_euclideanSq_gradient hηs hηc) hint fun y => ?_).trans ?_
    · rw [gradient_mul_comp_sub hθd hΨd x y]
      by_cases hy : μ ≤ euclideanNorm (x - y)
      · have hn : euclideanNorm ((-θ y) • gradient Ψ (x - y) + Ψ (x - y) • gradient θ y) ≤
            (G * B + B') * euclideanHeatKernel (2 * s) (x - y) := by
          refine (TimeChange.euclideanNorm_add_le _ _).trans ?_
          rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul, abs_neg]
          have h1 := mul_le_mul (hθ1 y) (hB' (x - y)) (euclideanNorm_nonneg _) zero_le_one
          have h2 := mul_le_mul (hB (x - y)) (hG y) (euclideanNorm_nonneg _)
            (mul_nonneg hB0 (hK y))
          nlinarith [hK y]
        have h3 := euclideanHeatKernel_sq_le hs hμ hy
        rw [euclideanSq_eq_euclideanNorm_sq]
        calc euclideanNorm ((-θ y) • gradient Ψ (x - y) + Ψ (x - y) • gradient θ y) ^ 2
            ≤ ((G * B + B') * euclideanHeatKernel (2 * s) (x - y)) ^ 2 :=
              pow_le_pow_left₀ (euclideanNorm_nonneg _) hn 2
          _ = (G * B + B') ^ 2 * euclideanHeatKernel (2 * s) (x - y) ^ 2 := by ring
          _ ≤ (G * B + B') ^ 2 * (E * euclideanHeatKernel (2 * s) (x - y)) := by gcongr
          _ = (G * B + B') ^ 2 * E * euclideanHeatKernel (2 * s) (x - y) := by ring
      · obtain ⟨h0, hg0⟩ := hzero y (not_le.mp hy)
        rw [h0, hg0]
        have : (-(0 : ℝ)) • gradient Ψ (x - y) + Ψ (x - y) • (0 : Vec d) = 0 := by simp
        rw [this]
        simp only [euclideanSq, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        exact mul_nonneg (by positivity) (hK y)
    · rw [integral_const_mul, integral_euclideanHeatKernel_sub (by positivity) x, mul_one]
  have hsqrt : Real.sqrt (ρ⁻¹ ^ 2 * (∫ y, (θ y * Ψ (x - y)) ^ 2) +
      ∫ y, euclideanSq (gradient (fun z => θ z * Ψ (x - z)) y)) ≤
      (ρ⁻¹ * B + (G * B + B')) * Real.sqrt E := by
    refine (Real.sqrt_le_sqrt (add_le_add (mul_le_mul_of_nonneg_left hL2 (sq_nonneg ρ⁻¹))
      hgradle)).trans ?_
    rw [← mul_assoc, ← mul_pow]
    exact sqrt_sq_add_sq_mul_le E (by positivity) (by positivity)
  have hfac : 0 ≤ A * ρ ^ ((d : ℝ) / 2 + 1) * (ρ / R₀) ^ (-κ) := by positivity
  have hint_eq : ∫ y, θ y * Ψ (x - y) * F y = ∫ y, (fun z => θ z * Ψ (x - z)) y * F y := rfl
  rw [hint_eq]
  exact hpair.trans (mul_le_mul_of_nonneg_left hsqrt hfac)

end Piece


section Dyadic

/-- The rescaled reference cutoff equal to one on `B_{2(k+1)R}`. -/
noncomputable def ringCutoff (χ : Vec d → ℝ) (R : ℝ) (k : ℕ) (y : Vec d) : ℝ :=
  χ ((2 * (((k : ℝ) + 1) * R))⁻¹ • y)

/-- The pieces of the partition of unity defined by the cutoffs `ringCutoff`. -/
noncomputable def ringPiece (χ : Vec d → ℝ) (R : ℝ) : ℕ → Vec d → ℝ
  | 0 => ringCutoff χ R 0
  | k + 1 => fun y => ringCutoff χ R (k + 1) y - ringCutoff χ R k y

theorem sum_ringPiece (χ : Vec d → ℝ) (R : ℝ) (N : ℕ) (y : Vec d) :
    ∑ k ∈ Finset.range (N + 1), ringPiece χ R k y = ringCutoff χ R N y := by
  induction N with
  | zero => simp [ringPiece]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp [ringPiece]

theorem euclideanNorm_sub_le' (u v : Vec d) :
    euclideanNorm (u - v) ≤ euclideanNorm u + euclideanNorm v := by
  have h := TimeChange.euclideanNorm_add_le u ((-1 : ℝ) • v)
  rw [TimeChange.euclideanNorm_smul, abs_neg, abs_one, one_mul] at h
  have huv : u + (-1 : ℝ) • v = u - v := by
    funext l
    simp [sub_eq_add_neg]
  rwa [huv] at h

theorem summable_succ_pow_mul_exp (n : ℕ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ n * Real.exp (-(k : ℝ) / 16)) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul n (r := 1 / 16) (by norm_num)
  have h1 := (summable_nat_add_iff 1).mpr h
  refine (h1.mul_left (Real.exp (1 / 16))).congr fun k => ?_
  push_cast
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- The weights of the pieces of a Gaussian test. -/
noncomputable def ringWeight (m : ℝ) (k : ℕ) : ℝ :=
  (4 * ((k : ℝ) + 1)) ^ m * Real.exp (-(k : ℝ) ^ 2 / 16)

theorem ringWeight_nonneg (m : ℝ) (k : ℕ) : 0 ≤ ringWeight m k := by
  unfold ringWeight
  positivity

theorem summable_ringWeight (m : ℝ) : Summable (ringWeight m) := by
  set n := ⌈m⌉₊
  refine ((summable_succ_pow_mul_exp n).mul_left ((4 : ℝ) ^ n)).of_nonneg_of_le
    (ringWeight_nonneg m) fun k => ?_
  unfold ringWeight
  have h1 : (1 : ℝ) ≤ 4 * ((k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h2 : (4 * ((k : ℝ) + 1)) ^ m ≤ (4 * ((k : ℝ) + 1)) ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil m)
  have h3 : Real.exp (-(k : ℝ) ^ 2 / 16) ≤ Real.exp (-(k : ℝ) / 16) := by
    refine Real.exp_le_exp.mpr ?_
    have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero k
    linarith
  calc (4 * ((k : ℝ) + 1)) ^ m * Real.exp (-(k : ℝ) ^ 2 / 16)
      ≤ (4 * ((k : ℝ) + 1)) ^ n * Real.exp (-(k : ℝ) / 16) :=
        mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
    _ = (4 : ℝ) ^ n * (((k : ℝ) + 1) ^ n * Real.exp (-(k : ℝ) / 16)) := by
        rw [mul_pow]
        ring

end Dyadic


section Main

theorem integrable_mul_comp_sub_mul {Ψ F θ : Vec d → ℝ} (hΨ : Continuous Ψ) (hFm : Measurable F)
    (hθ : Continuous θ) (hθ1 : ∀ y, |θ y| ≤ 1) {s B : ℝ}
    (hB : ∀ z, |Ψ z| ≤ B * euclideanHeatKernel (2 * s) z) {x : Vec d}
    (hint : Integrable (fun y => euclideanHeatKernel (2 * s) (x - y) * |F y|) volume) :
    Integrable (fun y => θ y * Ψ (x - y) * F y) volume := by
  refine (hint.const_mul B).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((hθ.mul (hΨ.comp (continuous_const.sub continuous_id))).measurable.mul
      hFm).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |θ y| * |Ψ (x - y)| * |F y|
        ≤ 1 * (B * euclideanHeatKernel (2 * s) (x - y)) * |F y| := by
          gcongr
          · exact hθ1 y
          · exact hB (x - y)
      _ = B * (euclideanHeatKernel (2 * s) (x - y) * |F y|) := by ring

theorem originBall_subset_originBall {r r' : ℝ} (h : r ≤ r') :
    originBall d r ⊆ originBall d r' := fun _ hy => lt_of_lt_of_le hy h

/-- **Pairing of a Gaussian test with a field of small negative Sobolev norm.** There is a
constant `C` depending only on the dimension such that, if `F` has a pairing bound at the
scales above `R₀`, then for every smooth kernel with `|Ψ| ≤ B Φ_{2s}` and `|∇Ψ| ≤ B' Φ_{2s}`,
`|∫ Ψ(x - y) F(y) dy| ≤ C A R^(d/2+1) (R/R₀)^(-κ) (B/R + B') (8πs)^(-d/4)` for `R ≥ R₀`,
`|x| ≤ R` and `s ≤ R²`. -/
theorem exists_gaussianPairing_const (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Vec d → ℝ} {R₀ A κ : ℝ}, HasScalePairingBound F R₀ A κ →
      0 < R₀ → 0 ≤ A → 0 ≤ κ → Measurable F → ∀ {Ψ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Ψ →
      ∀ {s B B' : ℝ}, 0 < s → 0 ≤ B → 0 ≤ B' →
      (∀ z, |Ψ z| ≤ B * euclideanHeatKernel (2 * s) z) →
      (∀ z, euclideanNorm (gradient Ψ z) ≤ B' * euclideanHeatKernel (2 * s) z) →
      ∀ x : Vec d, Integrable (fun y => euclideanHeatKernel (2 * s) (x - y) * |F y|) volume →
      ∀ {R : ℝ}, R₀ ≤ R → euclideanNorm x ≤ R → s ≤ R ^ 2 →
      |∫ y, Ψ (x - y) * F y| ≤ C * A * R ^ ((d : ℝ) / 2 + 1) * (R / R₀) ^ (-κ) *
        (B / R + B') * (8 * Real.pi * s) ^ (-(d : ℝ) / 4) := by
  obtain ⟨χ, D, hD, hχtest, hχb, hχ1, hχD⟩ := exists_nonnegative_reference_spatial_cutoff d
  set m : ℝ := (d : ℝ) / 2 + 1 with hm
  refine ⟨(∑' k, ringWeight m k) * (1 + 2 * D),
    mul_nonneg (tsum_nonneg (ringWeight_nonneg m)) (by linarith), ?_⟩
  intro F R₀ A κ hF hR₀ hA hκ hFm Ψ hΨ s B B' hs hB0 hB'0 hB hB' x hint R hR hxR hsR
  have hR0 : 0 < R := lt_of_lt_of_le hR₀ hR
  have hDR : 0 ≤ D / R := div_nonneg hD.le hR0.le
  have hcut : ∀ k : ℕ, IsSpatialTest (originBall d (4 * (((k : ℝ) + 1) * R)))
        (ringCutoff χ R k) ∧
      (∀ y, 0 ≤ ringCutoff χ R k y ∧ ringCutoff χ R k y ≤ 1) ∧
      (∀ y ∈ originBall d (2 * (((k : ℝ) + 1) * R)), ringCutoff χ R k y = 1) ∧
      ∀ y, euclideanNorm (gradient (ringCutoff χ R k) y) ≤ D / R := by
    intro k
    have hr : 0 < ((k : ℝ) + 1) * R := by positivity
    obtain ⟨h1, h2, h3, h4⟩ := rescale_reference_spatial_cutoff hr hχtest hχb hχ1 hχD
    refine ⟨h1, h2, h3, fun y => ?_⟩
    have h5 := h4 y
    have hDr : 0 ≤ D / (((k : ℝ) + 1) * R) := by positivity
    calc euclideanNorm (gradient (ringCutoff χ R k) y) ≤ D / (((k : ℝ) + 1) * R) := by
          unfold euclideanNorm
          rw [← Real.sqrt_sq hDr]
          exact Real.sqrt_le_sqrt h5
      _ ≤ D / R := by
          refine div_le_div_of_nonneg_left hD.le hR0 ?_
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
  have hpiece : ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞) (ringPiece χ R k) ∧
      HasCompactSupport (ringPiece χ R k) ∧
      tsupport (ringPiece χ R k) ⊆ ball 0 (4 * (((k : ℝ) + 1) * R)) ∧
      (∀ y, |ringPiece χ R k y| ≤ 1) ∧
      (∀ y, euclideanNorm (gradient (ringPiece χ R k) y) ≤ 2 * D / R) ∧
      (∀ y, euclideanNorm (x - y) < (k : ℝ) * R → ringPiece χ R k =ᶠ[𝓝 y] 0) := by
    intro k
    cases k with
    | zero =>
      obtain ⟨⟨hs1, hs2, hs3⟩, hb, -, hg⟩ := hcut 0
      refine ⟨hs1, hs2, ?_, fun y => ?_, fun y => ?_, fun y hy => ?_⟩
      · rw [← originBall_eq_ball]
        exact hs3
      · change |ringCutoff χ R 0 y| ≤ 1
        rw [abs_le]
        exact ⟨by linarith [(hb y).1], (hb y).2⟩
      · refine (hg y).trans ?_
        rw [mul_div_assoc]
        linarith
      · exact absurd hy (by simpa using euclideanNorm_nonneg (x - y))
    | succ k =>
      obtain ⟨⟨h1s, h1c, h1t⟩, h1b, h1one, h1g⟩ := hcut (k + 1)
      obtain ⟨⟨h0s, h0c, h0t⟩, h0b, h0one, h0g⟩ := hcut k
      have hfun : ringPiece χ R (k + 1) =
          fun z => ringCutoff χ R (k + 1) z - ringCutoff χ R k z := rfl
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      refine ⟨?_, ?_, ?_, fun y => ?_, fun y => ?_, fun y hy => ?_⟩
      · rw [hfun]
        exact h1s.sub h0s
      · rw [hfun]
        exact h1c.sub h0c
      · rw [hfun]
        refine (tsupport_sub _ _).trans (Set.union_subset ?_ ?_)
        · rw [← originBall_eq_ball]
          refine h1t.trans (originBall_subset_originBall (le_of_eq ?_))
          push_cast
          ring
        · rw [← originBall_eq_ball]
          refine h0t.trans (originBall_subset_originBall ?_)
          push_cast
          nlinarith
      · rw [hfun, abs_le]
        constructor <;> linarith [(h1b y).1, (h1b y).2, (h0b y).1, (h0b y).2]
      · have hd1 := (h1s.differentiable (by simp) y).hasFDerivAt
        have hd0 := (h0s.differentiable (by simp) y).hasFDerivAt
        have hgs : gradient (ringPiece χ R (k + 1)) y =
            gradient (ringCutoff χ R (k + 1)) y - gradient (ringCutoff χ R k) y := by
          funext l
          change fderiv ℝ (ringPiece χ R (k + 1)) y (unitVector l) = _
          rw [hfun, (hd1.fun_sub hd0).fderiv]
          rfl
        rw [hgs, mul_div_assoc]
        refine (euclideanNorm_sub_le' _ _).trans ?_
        linarith [h1g y, h0g y]
      · have hyU : y ∈ originBall d (((k : ℝ) + 2) * R) := by
          have h := euclideanNorm_le_add_sub x y
          have hy' : euclideanNorm (x - y) < ((k : ℝ) + 1) * R := by
            push_cast at hy
            exact hy
          show euclideanNorm y < ((k : ℝ) + 2) * R
          nlinarith
        refine Filter.eventuallyEq_of_mem ((isOpen_originBall _).mem_nhds hyU) fun z hz => ?_
        have hz1 : ringCutoff χ R (k + 1) z = 1 := h1one z
          (originBall_subset_originBall (by push_cast; nlinarith) hz)
        have hz0 : ringCutoff χ R k z = 1 := h0one z
          (originBall_subset_originBall (by nlinarith) hz)
        rw [hfun]
        simp [hz1, hz0]
  set Z := (1 + 2 * D) * A * R ^ m * (R / R₀) ^ (-κ) * (B / R + B') *
    (8 * Real.pi * s) ^ (-(d : ℝ) / 4) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hb : ∀ k : ℕ, |∫ y, ringPiece χ R k y * Ψ (x - y) * F y| ≤ ringWeight m k * Z := by
    intro k
    obtain ⟨hθs, hθc, hθt, hθ1, hθg, hθμ⟩ := hpiece k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    set ρ := 4 * (((k : ℝ) + 1) * R) with hρ
    have hRρ : R ≤ ρ := by rw [hρ]; nlinarith
    have hρ0 : 0 < ρ := lt_of_lt_of_le hR0 hRρ
    have h := hF.abs_integral_piece_le hA hR₀ hΨ hs hB0 hB'0 hB hB' hθs hθc (hR.trans hRρ) hθt
      hθ1 (by positivity) hθg (by positivity) x hθμ
    refine h.trans ?_
    have e1 : (ρ / R₀) ^ (-κ) ≤ (R / R₀) ^ (-κ) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hR0 hR₀) (div_le_div_of_nonneg_right hRρ hR₀.le)
        (by linarith)
    have e2 : ρ⁻¹ * B + (2 * D / R * B + B') ≤ (1 + 2 * D) * (B / R + B') := by
      have h1 : ρ⁻¹ * B ≤ B / R := by
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_right (inv_anti₀ hR0 hRρ) hB0
      have h2 : 2 * D / R * B = 2 * D * (B / R) := by ring
      have h3 : 0 ≤ B / R := div_nonneg hB0 hR0.le
      nlinarith
    have e3 : Real.sqrt ((8 * Real.pi * s) ^ (-(d : ℝ) / 2) *
        Real.exp (-((k : ℝ) * R) ^ 2 / (8 * s))) ≤
        (8 * Real.pi * s) ^ (-(d : ℝ) / 4) * Real.exp (-(k : ℝ) ^ 2 / 16) := by
      rw [Real.sqrt_mul (by positivity)]
      have hs1 : Real.sqrt ((8 * Real.pi * s) ^ (-(d : ℝ) / 2)) =
          (8 * Real.pi * s) ^ (-(d : ℝ) / 4) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      have hs2 : Real.sqrt (Real.exp (-((k : ℝ) * R) ^ 2 / (8 * s))) ≤
          Real.exp (-(k : ℝ) ^ 2 / 16) := by
        rw [← Real.sqrt_sq (Real.exp_pos (-(k : ℝ) ^ 2 / 16)).le]
        refine Real.sqrt_le_sqrt ?_
        have hsq2 : Real.exp (-(k : ℝ) ^ 2 / 16) ^ 2 =
            Real.exp (-(k : ℝ) ^ 2 / 16 + -(k : ℝ) ^ 2 / 16) := by
          rw [sq, Real.exp_add]
        rw [hsq2]
        refine Real.exp_le_exp.mpr ?_
        have h8 : 0 < 8 * s := by positivity
        have hks : (k : ℝ) ^ 2 * s ≤ (k : ℝ) ^ 2 * R ^ 2 :=
          mul_le_mul_of_nonneg_left hsR (sq_nonneg _)
        rw [div_le_iff₀ h8]
        nlinarith
      rw [hs1]
      exact mul_le_mul_of_nonneg_left hs2 (by positivity)
    have e4 : ρ ^ m = (4 * ((k : ℝ) + 1)) ^ m * R ^ m := by
      rw [hρ, ← mul_assoc, Real.mul_rpow (by positivity) hR0.le]
    calc A * ρ ^ ((d : ℝ) / 2 + 1) * (ρ / R₀) ^ (-κ) *
          ((ρ⁻¹ * B + (2 * D / R * B + B')) * Real.sqrt ((8 * Real.pi * s) ^ (-(d : ℝ) / 2) *
            Real.exp (-((k : ℝ) * R) ^ 2 / (8 * s))))
        ≤ A * ρ ^ ((d : ℝ) / 2 + 1) * (R / R₀) ^ (-κ) *
          (((1 + 2 * D) * (B / R + B')) * ((8 * Real.pi * s) ^ (-(d : ℝ) / 4) *
            Real.exp (-(k : ℝ) ^ 2 / 16))) := by
          gcongr
      _ = ringWeight m k * Z := by
          rw [← hm, e4, hZ]
          unfold ringWeight
          ring
  have hpieceint : ∀ k : ℕ, Integrable (fun y => ringPiece χ R k y * Ψ (x - y) * F y) volume :=
    fun k => integrable_mul_comp_sub_mul hΨ.continuous hFm (hpiece k).1.continuous
      (hpiece k).2.2.2.1 hB hint
  have hsum : ∀ N : ℕ, ∫ y, ringCutoff χ R N y * Ψ (x - y) * F y =
      ∑ k ∈ Finset.range (N + 1), ∫ y, ringPiece χ R k y * Ψ (x - y) * F y := by
    intro N
    rw [← integral_finsetSum _ fun k _ => hpieceint k]
    congr 1
    funext y
    rw [← sum_ringPiece χ R N y, Finset.sum_mul, Finset.sum_mul]
  have hbound : ∀ N : ℕ, |∫ y, ringCutoff χ R N y * Ψ (x - y) * F y| ≤
      (∑' k, ringWeight m k) * Z := by
    intro N
    rw [hsum N]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hb k).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right ((summable_ringWeight m).sum_le_tsum _
      fun k _ => ringWeight_nonneg m k) hZ0
  have hlim : Tendsto (fun N : ℕ => ∫ y, ringCutoff χ R N y * Ψ (x - y) * F y) atTop
      (𝓝 (∫ y, Ψ (x - y) * F y)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => B * (euclideanHeatKernel (2 * s) (x - y) * |F y|)) (fun N => ?_)
      (hint.const_mul B) (fun N => Filter.Eventually.of_forall fun y => ?_)
      (Filter.Eventually.of_forall fun y => ?_)
    · exact (integrable_mul_comp_sub_mul hΨ.continuous hFm (hcut N).1.1.continuous
        (fun y => by rw [abs_le]; exact ⟨by linarith [((hcut N).2.1 y).1], ((hcut N).2.1 y).2⟩)
        hB hint).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |ringCutoff χ R N y| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [((hcut N).2.1 y).1], ((hcut N).2.1 y).2⟩
      calc |ringCutoff χ R N y| * |Ψ (x - y)| * |F y|
          ≤ 1 * (B * euclideanHeatKernel (2 * s) (x - y)) * |F y| := by
            gcongr
            exact hB (x - y)
        _ = B * (euclideanHeatKernel (2 * s) (x - y) * |F y|) := by ring
    · obtain ⟨N₀, hN₀⟩ := exists_nat_gt (euclideanNorm y / (2 * R))
      refine tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩)
      have hNy : y ∈ originBall d (2 * (((N : ℝ) + 1) * R)) := by
        have h1 : euclideanNorm y < 2 * R * N₀ := by
          rw [div_lt_iff₀ (by positivity)] at hN₀
          linarith
        have h2 : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
        show euclideanNorm y < 2 * (((N : ℝ) + 1) * R)
        nlinarith
      simp only [(hcut N).2.2.1 y hNy, one_mul]
  have hfinal := le_of_tendsto ((continuous_abs.tendsto _).comp hlim)
    (Filter.Eventually.of_forall hbound)
  refine hfinal.trans (le_of_eq ?_)
  simp only [hZ]
  ring

end Main


section Decay

theorem sqrt_rpow_mul_rpow_eq {t R₀ κ : ℝ} (ht : 0 < t) (hR₀ : 0 < R₀) :
    Real.sqrt t ^ ((d : ℝ) / 2 + 1) * (Real.sqrt t / R₀) ^ (-κ) * (t * Real.sqrt t)⁻¹ *
      (8 * Real.pi * t) ^ (-(d : ℝ) / 4) =
      R₀ ^ κ * (8 * Real.pi) ^ (-(d : ℝ) / 4) * t ^ (-(1 + κ / 2)) := by
  rw [Real.sqrt_eq_rpow]
  have e1 : (t ^ (1 / 2 : ℝ)) ^ ((d : ℝ) / 2 + 1) = t ^ ((d : ℝ) / 4 + 1 / 2) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    ring
  have e2 : (t ^ (1 / 2 : ℝ) / R₀) ^ (-κ) = R₀ ^ κ * t ^ (-κ / 2) := by
    rw [Real.div_rpow (by positivity) hR₀.le, ← Real.rpow_mul ht.le, Real.rpow_neg hR₀.le,
      div_inv_eq_mul, mul_comm]
    congr 2
    ring
  have e3 : (t * t ^ (1 / 2 : ℝ))⁻¹ = t ^ (-(3 / 2 : ℝ)) := by
    rw [Real.rpow_neg ht.le]
    congr 1
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one]
  have e4 : (8 * Real.pi * t) ^ (-(d : ℝ) / 4) =
      (8 * Real.pi) ^ (-(d : ℝ) / 4) * t ^ (-(d : ℝ) / 4) :=
    Real.mul_rpow (by positivity) ht.le
  rw [e1, e2, e3, e4]
  have e5 : t ^ ((d : ℝ) / 4 + 1 / 2) * t ^ (-κ / 2) * t ^ (-(3 / 2 : ℝ)) * t ^ (-(d : ℝ) / 4) =
      t ^ (-(1 + κ / 2)) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  rw [← e5]
  ring

/-- **Large-time decay of the heat Hessian of a field with a pairing bound.** -/
theorem exists_heatHessianConv_le (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Vec d → ℝ} {R₀ A κ : ℝ}, HasScalePairingBound F R₀ A κ →
      0 < R₀ → 0 ≤ A → 0 ≤ κ → Measurable F → HasGaussianMoments F →
      ∀ (i j : Fin d) (t : ℝ) (x : Vec d), R₀ ^ 2 ≤ t → euclideanNorm x ^ 2 ≤ t →
        |heatHessianConv t i j F x| ≤ C * A * R₀ ^ κ * t ^ (-(1 + κ / 2)) := by
  obtain ⟨C, hC, hpair⟩ := exists_gaussianPairing_const d
  refine ⟨C * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 + Real.sqrt d * 10)) *
    (8 * Real.pi) ^ (-(d : ℝ) / 4), by positivity, ?_⟩
  intro F R₀ A κ hF hR₀ hA hκ hFm hmom i j t x hRt hxt
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hRt
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  obtain ⟨Bm, hBm⟩ := hmom (2 * t) (by positivity) (euclideanNorm x)
  have hint := (hBm x le_rfl).1
  have hR : R₀ ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hRt
  have hxR : euclideanNorm x ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hxt
  have h := hpair hF hR₀ hA hκ hFm (contDiff_heatHessian t i j) ht
    (B := (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t))
    (B' := Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * (10 / (t * Real.sqrt t))))
    (by positivity) (by positivity) (fun z => abs_heatHessian_le ht i j z)
    (fun z => euclideanNorm_gradient_heatHessian_le ht i j z) x hint hR hxR
    (by rw [Real.sq_sqrt ht.le])
  have hsum : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) / Real.sqrt t +
      Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * (10 / (t * Real.sqrt t))) =
      (2 : ℝ) ^ ((d : ℝ) / 2) * (2 + Real.sqrt d * 10) * (t * Real.sqrt t)⁻¹ := by
    field_simp
  have hkey := sqrt_rpow_mul_rpow_eq (d := d) (κ := κ) ht hR₀
  calc |heatHessianConv t i j F x|
      ≤ C * A * Real.sqrt t ^ ((d : ℝ) / 2 + 1) * (Real.sqrt t / R₀) ^ (-κ) *
          ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) / Real.sqrt t +
            Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * (10 / (t * Real.sqrt t)))) *
          (8 * Real.pi * t) ^ (-(d : ℝ) / 4) := h
    _ = C * A * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 + Real.sqrt d * 10)) *
          (Real.sqrt t ^ ((d : ℝ) / 2 + 1) * (Real.sqrt t / R₀) ^ (-κ) * (t * Real.sqrt t)⁻¹ *
            (8 * Real.pi * t) ^ (-(d : ℝ) / 4)) := by
        rw [hsum]
        ring
    _ = C * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 + Real.sqrt d * 10)) * (8 * Real.pi) ^ (-(d : ℝ) / 4) *
          A * R₀ ^ κ * t ^ (-(1 + κ / 2)) := by
        rw [hkey]
        ring

/-- A field with a pairing bound at the scales above `R₀` and Gaussian moments has heat
Hessians that decay at large times on the parabolic region. -/
theorem HasScalePairingBound.hasHeatHessianDecay {F : Vec d → ℝ} {R₀ A κ : ℝ}
    (hF : HasScalePairingBound F R₀ A κ) (hR₀ : 0 < R₀) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hFm : Measurable F) (hmom : HasGaussianMoments F) (i j : Fin d) :
    HasHeatHessianDecay F i j := by
  obtain ⟨C, hC, h⟩ := exists_heatHessianConv_le d
  exact ⟨C * A * R₀ ^ κ, κ / 2, R₀ ^ 2, by positivity, by positivity, by positivity,
    fun t ht x hx => h hF hR₀ hA hκ.le hFm hmom i j t x ht hx⟩

end Decay

end EinsteinFull.Homogenization
