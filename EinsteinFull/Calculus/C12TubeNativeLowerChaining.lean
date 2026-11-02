import EinsteinFull.Calculus.C12TubeGaussianLowerScaling
import PDEFoundation.Measure.BallVolume

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology

namespace EinsteinFull.Calculus

/-- The Gaussian bound in the near-diagonal region, with a constant chosen
before the cylinder, density, and kernel. The off-diagonal chain is separate. -/
theorem c12_native_gaussian_lower_near_diagonal (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), 0 < t → ∀ (x y : Vec d) (q : ℝ),
      c * Real.rpow t (-(d : ℝ)/2) ≤ q →
      C⁻¹ * Real.rpow t (-(d : ℝ)/2) *
        Real.exp (-C * euclideanSq (x-y) / t) ≤ q := by
  let C : ℝ := max 1 c⁻¹
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hCc : C⁻¹ ≤ c := by
    have h := le_max_right (1 : ℝ) c⁻¹
    have := (inv_le_inv₀ hC (inv_pos.mpr hc)).2 h
    simpa using this
  refine ⟨C, hC, ?_⟩
  intro t ht x y q hq
  have hsq : 0 ≤ euclideanSq (x-y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hexp : Real.exp (-C * euclideanSq (x-y) / t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ ht.le
    simpa only [neg_mul] using (neg_nonpos.mpr (mul_nonneg hC.le hsq))
  have hp : 0 ≤ Real.rpow t (-(d : ℝ)/2) := (Real.rpow_pos_of_pos ht _).le
  calc
    C⁻¹ * Real.rpow t (-(d : ℝ)/2) * Real.exp (-C * euclideanSq (x-y) / t)
        ≤ C⁻¹ * Real.rpow t (-(d : ℝ)/2) * 1 :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (inv_nonneg.mpr hC.le) hp)
    _ ≤ c * Real.rpow t (-(d : ℝ)/2) := by simpa using mul_le_mul_of_nonneg_right hCc hp
    _ ≤ q := hq

/-- A positive integrable convolution is bounded below by its uniform lower
bound on any measurable intermediate region. -/
theorem c12_integral_lower_on_region {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (S : Set α) (hS : MeasurableSet S)
    (f : α → ℝ) (hf : Integrable f μ) (hnonneg : ∀ x, 0 ≤ f x)
    (a : ℝ) (ha : ∀ x ∈ S, a ≤ f x) :
    a * (μ S).toReal ≤ ∫ x, f x ∂μ := by
  have hrestrict : Integrable f (μ.restrict S) := hf.mono_measure Measure.restrict_le_self
  have hbound : ∀ᵐ x ∂μ.restrict S, a ≤ f x := by
    filter_upwards [ae_restrict_mem hS] with x hx
    exact ha x hx
  have hlo := integral_mono_ae (integrable_const a) hrestrict hbound
  have hhi : (∫ x in S, f x ∂μ) ≤ ∫ x, f x ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall hnonneg) hf
  have hconst : (∫ _ in S, a ∂μ) = a * (μ S).toReal := by
    simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul,
      mul_comm]
  exact hconst ▸ hlo.trans hhi

/-- A weighted convolution gains the volume of a region on which both
kernel factors and the density have positive lower bounds. -/
theorem c12_weighted_convolution_lower_on_region {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (S : Set α) (hS : MeasurableSet S)
    (f g ρ : α → ℝ) (a b κ : ℝ) (hb : 0 ≤ b) (hκ : 0 ≤ κ)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z) (hρ : ∀ z, 0 ≤ ρ z)
    (hint : Integrable (fun z => f z * g z * ρ z) μ)
    (hfa : ∀ z ∈ S, a ≤ f z) (hgb : ∀ z ∈ S, b ≤ g z)
    (hρκ : ∀ z ∈ S, κ ≤ ρ z) :
    (a * b * κ) * (μ S).toReal ≤ ∫ z, f z * g z * ρ z ∂μ := by
  apply c12_integral_lower_on_region μ S hS _ hint
    (fun z => mul_nonneg (mul_nonneg (hf z) (hg z)) (hρ z))
  intro z hz
  have hfg : a * b ≤ f z * g z := mul_le_mul (hfa z hz) (hgb z hz) hb (hf z)
  exact mul_le_mul hfg (hρκ z hz) hκ (mul_nonneg (hf z) (hg z))

/-- Finite chaining for a weighted discrete semigroup over measurable regions.
The sets, times, and lower bounds are supplied by the geometric construction. -/
theorem c12_weighted_semigroup_finite_chain {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (ρ : α → ℝ) (κ a v : ℝ)
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hv : 0 ≤ v)
    (hρ : ∀ z, κ ≤ ρ z) (q : ℕ → α → α → ℝ)
    (hq : ∀ n, 0 < n → ∀ x y, 0 ≤ q n x y)
    (S : ℕ → Set α) (hS : ∀ n, MeasurableSet (S n))
    (hvol : ∀ n, v ≤ (μ (S n)).toReal)
    (hstep : ∀ n, ∀ x ∈ S n, ∀ y ∈ S (n+1), a ≤ q 1 x y)
    (hint : ∀ n, ∀ x ∈ S 0, ∀ y ∈ S (n+2),
      Integrable (fun z => q (n+1) x z * q 1 z y * ρ z) μ)
    (hsemi : ∀ n, ∀ x ∈ S 0, ∀ y ∈ S (n+2),
      q (n+2) x y = ∫ z, q (n+1) x z * q 1 z y * ρ z ∂μ)
    (x : α) (hx : x ∈ S 0) :
    ∀ n y, y ∈ S (n+1) → a * (a * κ * v)^n ≤ q (n+1) x y := by
  have hρ0 (z : α) : 0 ≤ ρ z := hκ.trans (hρ z)
  intro n
  induction n with
  | zero =>
      intro y hy
      simpa using hstep 0 x hx y hy
  | succ n ih =>
      intro y hy
      have hconv := c12_weighted_convolution_lower_on_region μ (S (n+1)) (hS (n+1))
        (fun z => q (n+1) x z) (fun z => q 1 z y) ρ
        (a * (a * κ * v)^n) a κ ha hκ
        (fun z => hq (n+1) (by omega) x z) (fun z => hq 1 (by omega) z y) hρ0
        (hint n x hx y (by simpa [Nat.add_assoc] using hy)) (fun z hz => ih z hz)
        (fun z hz => hstep (n+1) z hz y (by simpa [Nat.add_assoc] using hy))
        (fun z _ => hρ z)
      have hfactor : 0 ≤ a * (a * κ * v)^n * a * κ := by positivity
      have hmeasure := mul_le_mul_of_nonneg_left (hvol (n+1)) hfactor
      have hcalc : a * (a * κ * v)^(n+1) =
          (a * (a * κ * v)^n * a * κ) * v := by rw [pow_succ]; ring
      rw [hcalc]
      calc
        _ ≤ (a * (a * κ * v)^n * a * κ) * (μ (S (n+1))).toReal := hmeasure
        _ ≤ ∫ z, q (n+1) x z * q 1 z y * ρ z ∂μ := hconv
        _ = q (n+1+1) x y := by
          simpa [Nat.add_assoc] using (hsemi n x hx y (by simpa [Nat.add_assoc] using hy)).symm

/-- Apply the discrete weighted chain to equal subdivisions of real time. -/
theorem c12_weighted_real_semigroup_finite_chain {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (ρ : α → ℝ) (κ a v h : ℝ)
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hv : 0 ≤ v) (hh : 0 < h)
    (hρ : ∀ z, κ ≤ ρ z) (q : ℝ → α → α → ℝ)
    (hq : ∀ t, 0 < t → ∀ x y, 0 ≤ q t x y)
    (U : Set α) (S : ℕ → Set α) (hS : ∀ n, MeasurableSet (S n))
    (hSU : ∀ n, S n ⊆ U) (hvol : ∀ n, v ≤ (μ (S n)).toReal)
    (hstep : ∀ n, ∀ x ∈ S n, ∀ y ∈ S (n+1), a ≤ q h x y)
    (hint : ∀ s t, 0 < s → 0 < t → ∀ x ∈ U, ∀ y ∈ U,
      Integrable (fun z => q s x z * q t z y * ρ z) μ)
    (hsemi : ∀ s t, 0 < s → 0 < t → ∀ x ∈ U, ∀ y ∈ U,
      q (s+t) x y = ∫ z, q s x z * q t z y * ρ z ∂μ)
    (x : α) (hx : x ∈ S 0) :
    ∀ n y, y ∈ S (n+1) → a * (a * κ * v)^n ≤ q ((n+1 : ℕ) * h) x y := by
  let Q : ℕ → α → α → ℝ := fun n => q (n * h)
  have hQ : ∀ n, 0 < n → ∀ x y, 0 ≤ Q n x y := by
    intro n hn x y
    apply hq _ (mul_pos (Nat.cast_pos.mpr hn) hh)
  have hs : ∀ n, ∀ x ∈ S n, ∀ y ∈ S (n+1), a ≤ Q 1 x y := by
    simpa [Q] using hstep
  have hi : ∀ n, ∀ x ∈ S 0, ∀ y ∈ S (n+2),
      Integrable (fun z => Q (n+1) x z * Q 1 z y * ρ z) μ := by
    intro n x hx y hy
    have hp : 0 < ((n+1 : ℕ) : ℝ) * h := mul_pos (by positivity) hh
    simpa [Q] using hint _ _ hp hh x (hSU 0 hx) y (hSU (n+2) hy)
  have he : ∀ n, ∀ x ∈ S 0, ∀ y ∈ S (n+2),
      Q (n+2) x y = ∫ z, Q (n+1) x z * Q 1 z y * ρ z ∂μ := by
    intro n x hx y hy
    have hp : 0 < ((n+1 : ℕ) : ℝ) * h := mul_pos (by positivity) hh
    have ht : ((n+1 : ℕ) : ℝ) * h + h = ((n+2 : ℕ) : ℝ) * h := by
      push_cast
      ring
    have hhsemi := hsemi _ _ hp hh x (hSU 0 hx) y (hSU (n+2) hy)
    rw [ht] at hhsemi
    simpa [Q] using hhsemi
  exact c12_weighted_semigroup_finite_chain μ ρ κ a v hκ ha hv hρ Q hQ S hS hvol hs hi he x hx

/-- A straight interpolation of two points stays in the same source ball. -/
theorem c12_sourceBall_segment {d : ℕ} (r u : ℝ) (x y : Vec d)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hx : x ∈ sourceBall (0 : Vec d) r) (hy : y ∈ sourceBall (0 : Vec d) r) :
    (1-u) • x + u • y ∈ sourceBall (0 : Vec d) r := by
  change euclideanNorm (x - 0) < r at hx
  change euclideanNorm (y - 0) < r at hy
  change euclideanNorm ((1-u) • x + u • y - 0) < r
  simp only [sub_zero] at hx hy ⊢
  have hu : 0 ≤ 1-u := by linarith
  have htri := TimeChange.euclideanNorm_add_le ((1-u) • x) (u • y)
  rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul,
    abs_of_nonneg hu, abs_of_nonneg hu0] at htri
  have hbound : (1-u) * euclideanNorm x + u * euclideanNorm y < r := by
    by_cases h : u = 0
    · subst u; simpa using hx
    · have hu' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm h)
      have hy' := mul_lt_mul_of_pos_left hy hu'
      have hx' := mul_le_mul_of_nonneg_left hx.le hu
      nlinarith
  exact htri.trans_lt hbound

/-- Distances between points on the segment scale with their parameter gap. -/
theorem c12_segment_distance {d : ℕ} (u v : ℝ) (x y : Vec d) :
    euclideanNorm ((1-v) • x + v • y - ((1-u) • x + u • y)) =
      |v-u| * euclideanNorm (y-x) := by
  have hid : (1-v) • x + v • y - ((1-u) • x + u • y) =
      (v-u) • (y-x) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hid, TimeChange.euclideanNorm_smul]

/-- A ball around an interior point lies in the corresponding enlarged ball. -/
theorem c12_sourceBall_nested {d : ℕ} (r δ : ℝ) (a z : Vec d)
    (ha : a ∈ sourceBall (0 : Vec d) r) (hz : z ∈ sourceBall a δ) :
    z ∈ sourceBall (0 : Vec d) (r + δ) := by
  change euclideanNorm (a - 0) < r at ha
  change euclideanNorm (z - a) < δ at hz
  change euclideanNorm (z - 0) < r + δ
  simp only [sub_zero] at ha ⊢
  have htri := TimeChange.euclideanNorm_add_le (z-a) a
  have heq : z-a+a = z := by abel
  rw [heq] at htri
  linarith

/-- Choose a positive number of steps comparable to squared distance over time. -/
theorem c12_chain_step_count (D t : ℝ) (hD : 0 ≤ D) (ht : 0 < t) :
    ∃ N : ℕ, 0 < N ∧ 4 * D / t ≤ (N : ℝ) ∧ (N : ℝ) ≤ 4 * D / t + 2 := by
  let A : ℝ := 4 * D / t
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let N : ℕ := ⌈A⌉₊ + 1
  have hlo : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have hhi : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hA
  refine ⟨N, by dsimp [N]; omega, ?_, ?_⟩
  · dsimp [N, A] at *
    push_cast
    linarith
  · dsimp [N, A] at *
    push_cast
    linarith

/-- Source balls have the Euclidean volume scaling used at each chain step. -/
theorem c12_sourceBall_volume {d : ℕ} (x : Vec d) {r : ℝ} (hr : 0 < r) :
    MeasurableSet (sourceBall x r) ∧
    volume (sourceBall x r) ≠ ⊤ ∧
    0 < (volume (sourceBall x r)).toReal ∧
    (volume (sourceBall x r)).toReal =
      r ^ d * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal := by
  have heq : sourceBall x r = PDE.euclideanBall x r := by
    ext y
    change Real.sqrt (euclideanSq (y - x)) < r ↔ PDE.vecNormSq (y - x) < r ^ 2
    rw [Real.sqrt_lt' hr]
    rfl
  rw [heq]
  exact ⟨(PDE.isOpen_euclideanBall x r).measurableSet,
    PDE.volume_euclideanBall_ne_top x hr.le,
    PDE.volume_euclideanBall_toReal_pos x hr,
    PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos x hr⟩

/-- Points in two equal-radius balls are separated by at most the center
separation plus twice the radius. -/
theorem c12_sourceBall_pair_distance {d : ℕ} (δ : ℝ) (a b x y : Vec d)
    (hx : x ∈ sourceBall a δ) (hy : y ∈ sourceBall b δ) :
    euclideanNorm (y - x) < euclideanNorm (b - a) + 2 * δ := by
  change euclideanNorm (x - a) < δ at hx
  change euclideanNorm (y - b) < δ at hy
  have h₁ := TimeChange.euclideanNorm_add_le (y-b) (b-a)
  have h₂ := TimeChange.euclideanNorm_add_le (y-a) (a-x)
  have he₁ : y-b+(b-a) = y-a := by abel
  have he₂ : y-a+(a-x) = y-x := by abel
  rw [he₁] at h₁
  have hn : euclideanNorm (-(x-a)) = euclideanNorm (x-a) := by
    have h : -(x-a) = (-1 : ℝ) • (x-a) := by
      ext i
      simp
    rw [h, TimeChange.euclideanNorm_smul]
    norm_num
  rw [he₂, ← neg_sub x a, hn] at h₂
  linarith

/-- Neighboring small balls satisfy the squared-distance condition for a
near-diagonal estimate at the given time. -/
theorem c12_sourceBall_pair_near_diagonal {d : ℕ} (h : ℝ) (hh : 0 < h)
    (a b x y : Vec d) (hab : euclideanNorm (b-a) ≤ Real.sqrt h / 2)
    (hx : x ∈ sourceBall a (Real.sqrt h / 8))
    (hy : y ∈ sourceBall b (Real.sqrt h / 8)) :
    euclideanSq (y-x) ≤ h := by
  have hp := c12_sourceBall_pair_distance (Real.sqrt h / 8) a b x y hx hy
  have hs := Real.sq_sqrt hh.le
  have hr : 0 ≤ Real.sqrt h := Real.sqrt_nonneg h
  have hn : 0 ≤ euclideanNorm (y-x) := Real.sqrt_nonneg _
  rw [TimeChange.euclideanSq_eq_sq_euclideanNorm]
  nlinarith

/-- A positive factor raised to a natural power has an exponential lower bound. -/
theorem c12_positive_power_exp_lower (b : ℝ) (hb : 0 < b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, Real.exp (-L * n) ≤ b ^ n := by
  let L : ℝ := max 0 (-Real.log b)
  have hL : 0 ≤ L := le_max_left _ _
  have hlog : -L ≤ Real.log b := by
    have h := le_max_right (0 : ℝ) (-Real.log b)
    linarith
  refine ⟨L, hL, ?_⟩
  intro n
  have h := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have he : -L * n ≤ Real.log b * n := by linarith
  calc
    Real.exp (-L * n) ≤ Real.exp (Real.log b * n) := Real.exp_le_exp.mpr he
    _ = b ^ n := by rw [mul_comm, Real.exp_nat_mul, Real.exp_log hb]

/-- An upper bound on the chain length yields Gaussian-scale decay. -/
theorem c12_chain_power_gaussian_lower (b : ℝ) (hb : 0 < b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (u : ℝ) (n : ℕ),
      (n : ℝ) ≤ 4 * u + 2 →
      Real.exp (-2 * L) * Real.exp (-4 * L * u) ≤ b ^ n := by
  obtain ⟨L, hL, hpow⟩ := c12_positive_power_exp_lower b hb
  refine ⟨L, hL, ?_⟩
  intro u n hn
  have he : -2 * L + -4 * L * u ≤ -L * n := by
    have h := mul_le_mul_of_nonneg_left hn hL
    nlinarith
  calc
    Real.exp (-2 * L) * Real.exp (-4 * L * u) =
        Real.exp (-2 * L + -4 * L * u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-L * n) := Real.exp_le_exp.mpr he
    _ ≤ b ^ n := hpow n

/-- The volume scale cancels the near-diagonal time power. -/
theorem c12_chain_volume_time_cancellation (d : ℕ) (h : ℝ) (hh : 0 < h) :
    Real.rpow h (-(d : ℝ) / 2) * (Real.sqrt h / 8)^d = (8 : ℝ)⁻¹ ^ d := by
  have hp : Real.rpow h ((d : ℝ) / 2) = (Real.sqrt h)^d := by
    rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt (d : ℝ) hh.le, Real.rpow_natCast]
  have hs : (Real.sqrt h)^d ≠ 0 := ne_of_gt (pow_pos (Real.sqrt_pos.2 hh) d)
  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_eq_pow, Real.rpow_neg hh.le, ← Real.rpow_eq_pow, hp, div_pow]
  field_simp
  rw [← mul_pow]
  norm_num

/-- The chosen step count makes each center displacement at most half a
square-root time step. -/
theorem c12_chain_step_length (a t N : ℝ) (ha : 0 ≤ a) (ht : 0 < t)
    (hN : 0 < N) (hsize : 4 * a^2 ≤ N * t) :
    a / N ≤ Real.sqrt (t / N) / 2 := by
  have hs : (Real.sqrt (t / N))^2 = t / N :=
    Real.sq_sqrt (div_nonneg ht.le hN.le)
  have hs0 := Real.sqrt_nonneg (t / N)
  have haN : 0 ≤ a / N := div_nonneg ha hN.le
  have hbound : 4 * (a / N)^2 ≤ t / N := by
    apply (le_div_iff₀ hN).2
    field_simp
    nlinarith
  nlinarith

/-- Clamped segment parameters remain in the unit interval and move by at
most one subdivision at each step. -/
theorem c12_chain_parameter_bounds (N : ℕ) (hN : 0 < N) (n : ℕ) :
    let u : ℕ → ℝ := fun k => (min k N : ℕ) / (N : ℝ)
    0 ≤ u n ∧ u n ≤ 1 ∧ 0 ≤ u (n+1) - u n ∧
      u (n+1) - u n ≤ 1 / (N : ℝ) := by
  dsimp
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h₁ : min n N ≤ N := Nat.min_le_right _ _
  have h₂ : min n N ≤ min (n+1) N := by omega
  have h₃ : min (n+1) N ≤ min n N + 1 := by omega
  have h₁r : ((min n N : ℕ) : ℝ) ≤ N := by exact_mod_cast h₁
  have h₂r : ((min n N : ℕ) : ℝ) ≤ ((min (n+1) N : ℕ) : ℝ) := by exact_mod_cast h₂
  have h₃r : ((min (n+1) N : ℕ) : ℝ) ≤ ((min n N : ℕ) : ℝ) + 1 := by exact_mod_cast h₃
  constructor
  · positivity
  constructor
  · exact (div_le_one hNr).2 h₁r
  constructor
  · exact sub_nonneg.mpr (div_le_div_of_nonneg_right h₂r hNr.le)
  · rw [← sub_div]
    exact (div_le_div_iff_of_pos_right hNr).2 (by linarith)

/-- The clamped straight-line centers stay inside the ball and have the
prescribed maximum separation. -/
theorem c12_chain_centers {d : ℕ} (N : ℕ) (hN : 0 < N)
    (r h : ℝ) (x y : Vec d)
    (hx : x ∈ sourceBall (0 : Vec d) r) (hy : y ∈ sourceBall (0 : Vec d) r)
    (hstep : euclideanNorm (y-x) / (N : ℝ) ≤ Real.sqrt h / 2) :
    let u : ℕ → ℝ := fun k => (min k N : ℕ) / (N : ℝ)
    let a : ℕ → Vec d := fun k => (1-u k) • x + u k • y
    (∀ n, a n ∈ sourceBall (0 : Vec d) r) ∧
    (∀ n, euclideanNorm (a (n+1) - a n) ≤ Real.sqrt h / 2) := by
  dsimp
  constructor
  · intro n
    have hp := c12_chain_parameter_bounds N hN n
    exact c12_sourceBall_segment r _ x y hp.1 hp.2.1 hx hy
  · intro n
    have hp := c12_chain_parameter_bounds N hN n
    rw [c12_segment_distance, abs_of_nonneg hp.2.2.1]
    have hd : 0 ≤ euclideanNorm (y-x) := Real.sqrt_nonneg _
    calc
      _ ≤ (1 / (N : ℝ)) * euclideanNorm (y-x) :=
        mul_le_mul_of_nonneg_right hp.2.2.2 hd
      _ = euclideanNorm (y-x) / (N : ℝ) := by ring
      _ ≤ Real.sqrt h / 2 := hstep

/-- Balls about admissible chain centers have uniform volume, remain in the
large ball, and satisfy the near-diagonal condition between consecutive balls. -/
theorem c12_chain_balls {d : ℕ} (N : ℕ) (r R h : ℝ) (hh : 0 < h)
    (a : ℕ → Vec d) (x y : Vec d) (ha0 : a 0 = x) (haN : a N = y)
    (hc : ∀ n, a n ∈ sourceBall (0 : Vec d) r)
    (hstep : ∀ n, euclideanNorm (a (n+1)-a n) ≤ Real.sqrt h / 2)
    (hR : r + Real.sqrt h / 8 ≤ R) :
    let S : ℕ → Set (Vec d) := fun n => sourceBall (a n) (Real.sqrt h / 8)
    (∀ n, MeasurableSet (S n) ∧ S n ⊆ sourceBall 0 R ∧
      (volume (S n)).toReal = (Real.sqrt h / 8)^d *
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ∧
      ∀ z ∈ S n, ∀ w ∈ S (n+1), euclideanSq (w-z) ≤ h) ∧
    x ∈ S 0 ∧ y ∈ S N := by
  have hδ : 0 < Real.sqrt h / 8 := by positivity
  dsimp only
  constructor
  · intro n
    have hv := c12_sourceBall_volume (a n) hδ
    refine ⟨hv.1, ?_, hv.2.2.2, ?_⟩
    · intro z hz
      have hz' := c12_sourceBall_nested r (Real.sqrt h / 8) (a n) z (hc n) hz
      change euclideanNorm (z - 0) < R
      change euclideanNorm (z - 0) < r + Real.sqrt h / 8 at hz'
      exact hz'.trans_le hR
    · intro z hz w hw
      exact c12_sourceBall_pair_near_diagonal h hh (a n) (a (n+1)) z w (hstep n) hz hw
  · constructor
    · change euclideanNorm (x-a 0) < Real.sqrt h / 8
      rw [ha0, sub_self]
      simpa [euclideanNorm, euclideanSq, dot] using hδ
    · change euclideanNorm (y-a N) < Real.sqrt h / 8
      rw [haN, sub_self]
      simpa [euclideanNorm, euclideanSq, dot] using hδ

/-- The native near-diagonal bound iterates along measurable intermediate sets
inside the domain, retaining their common volume contribution. -/
theorem c12_native_near_diagonal_finite_chain {d : ℕ} (R h κ c v : ℝ)
    (hR : 0 < R) (hh : 0 < h) (hhR : h ≤ R^2) (hκ : 0 < κ) (hc : 0 < c)
    (hv : 0 ≤ v) (ρ : Vec d → ℝ) (q : ℝ → Vec d → Vec d → ℝ)
    (hρ : ∀ z, κ ≤ ρ z) (hq : ∀ s, 0 < s → ∀ x y, 0 ≤ q s x y)
    (hint : ∀ s t, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      IntegrableOn (fun z => q s x z * q t z y * ρ z) (sourceBall 0 R))
    (hsemi : ∀ s t, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      q (s+t) x y = ∫ z in sourceBall 0 R, q s x z * q t z y * ρ z)
    (hnear : ∀ s, 0 < s → s ≤ R^2 → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      euclideanSq (x-y) ≤ s → c * Real.rpow s (-(d : ℝ)/2) ≤ q s x y)
    (S : ℕ → Set (Vec d)) (hS : ∀ n, MeasurableSet (S n))
    (hSU : ∀ n, S n ⊆ sourceBall 0 R)
    (hvol : ∀ n, v ≤ (volume (S n)).toReal)
    (hstep : ∀ n, ∀ x ∈ S n, ∀ y ∈ S (n+1), euclideanSq (x-y) ≤ h)
    (x : Vec d) (hx : x ∈ S 0) :
    ∀ n y, y ∈ S (n+1) →
      (c * Real.rpow h (-(d : ℝ)/2)) *
        ((c * Real.rpow h (-(d : ℝ)/2)) * κ * v)^n ≤ q ((n+1 : ℕ) * h) x y := by
  let U : Set (Vec d) := sourceBall 0 R
  have hfin : volume U ≠ ⊤ := (c12_sourceBall_volume (0 : Vec d) hR).2.1
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hfin
  have hv' : ∀ n, v ≤ ((volume.restrict U) (S n)).toReal := by
    intro n
    rw [Measure.restrict_apply (hS n), Set.inter_eq_left.mpr (hSU n)]
    exact hvol n
  have hstep' : ∀ n, ∀ x ∈ S n, ∀ y ∈ S (n+1),
      c * Real.rpow h (-(d : ℝ)/2) ≤ q h x y := by
    intro n x hx y hy
    exact hnear h hh hhR x (hSU n hx) y (hSU (n+1) hy) (hstep n x hx y hy)
  exact c12_weighted_real_semigroup_finite_chain (volume.restrict U) ρ κ
    (c * Real.rpow h (-(d : ℝ)/2)) v h hκ.le
    (mul_nonneg hc.le (Real.rpow_pos_of_pos hh _).le) hv hh hρ q hq U S hS hSU
    hv' hstep' hint hsemi x hx

/-- A time subdivision and segment balls adapted to two endpoints. -/
theorem c12_chain_admissible_balls {d : ℕ} (R t : ℝ) (hR : 0 < R)
    (ht : 0 < t) (htR : t ≤ R^2 / 64) (x y : Vec d)
    (hx : x ∈ sourceBall 0 (R/2)) (hy : y ∈ sourceBall 0 (R/2)) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 4 * euclideanSq (x-y) / t + 2 ∧
      let h := t / (N : ℝ)
      ∃ S : ℕ → Set (Vec d),
        (∀ n, MeasurableSet (S n) ∧ S n ⊆ sourceBall 0 R ∧
          (volume (S n)).toReal = (Real.sqrt h / 8)^d *
            (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ∧
          ∀ z ∈ S n, ∀ w ∈ S (n+1), euclideanSq (z-w) ≤ h) ∧
        x ∈ S 0 ∧ y ∈ S N := by
  have hsym (z w : Vec d) : euclideanSq (z-w) = euclideanSq (w-z) := by
    unfold euclideanSq dot
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.sub_apply]
    ring
  have hD : 0 ≤ euclideanSq (x-y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  obtain ⟨N, hN, hlo, hhi⟩ := c12_chain_step_count (euclideanSq (x-y)) t hD ht
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let h : ℝ := t / N
  have hh : 0 < h := div_pos ht hNr
  have hNt : 4 * euclideanNorm (y-x)^2 ≤ (N : ℝ) * t := by
    rw [← TimeChange.euclideanSq_eq_sq_euclideanNorm, ← hsym]
    exact (div_le_iff₀ ht).1 hlo
  have hstep := c12_chain_step_length (euclideanNorm (y-x)) t N
    (Real.sqrt_nonneg _) ht hNr hNt
  let u : ℕ → ℝ := fun k => (min k N : ℕ) / (N : ℝ)
  let a : ℕ → Vec d := fun k => (1-u k) • x + u k • y
  have ha0 : a 0 = x := by simp [a, u]
  have haN : a N = y := by simp [a, u, ne_of_gt hNr]
  have hcent := c12_chain_centers N hN (R/2) h x y hx hy hstep
  have hle : h ≤ t := by
    dsimp [h]
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact div_le_self ht.le hn
  have hs : Real.sqrt h ≤ R := by
    have hs2 := Real.sq_sqrt hh.le
    have hs0 := Real.sqrt_nonneg h
    nlinarith [sq_nonneg R]
  have hball := c12_chain_balls N (R/2) R h hh a x y ha0 haN hcent.1 hcent.2 (by linarith)
  refine ⟨N, hN, hhi, ?_⟩
  let S : ℕ → Set (Vec d) := fun n => sourceBall (a n) (Real.sqrt h / 8)
  refine ⟨S, ?_, hball.2⟩
  intro n
  obtain ⟨hm, hsub, hv, hd⟩ := hball.1 n
  refine ⟨hm, hsub, hv, ?_⟩
  intro z hz w hw
  rw [hsym z w]
  exact hd z hz w hw

/-- Uniform constants absorb the geometric chain factor into a Gaussian. -/
theorem c12_gaussian_absorb_chain (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ) (n : ℕ) (p : ℝ),
      0 ≤ u → 0 ≤ p → (n : ℝ) ≤ 4*u+2 →
      C⁻¹ * p * Real.exp (-C*u) ≤ c * p * b^n := by
  obtain ⟨L, hL, hpow⟩ := c12_chain_power_gaussian_lower b hb
  let A := c * Real.exp (-2*L)
  have hA : 0 < A := mul_pos hc (Real.exp_pos _)
  let C := max (4*L) (max 1 A⁻¹)
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) hC1
  have hCL : 4*L ≤ C := le_max_left _ _
  have hCA : A⁻¹ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCA' : C⁻¹ ≤ A := by
    have hh := (inv_le_inv₀ hC (inv_pos.mpr hA)).2 hCA
    simpa using hh
  refine ⟨C, hC, ?_⟩
  intro u n p hu hp hn
  have he : Real.exp (-C*u) ≤ Real.exp (-4*L*u) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow' := hpow u n hn
  have h₁ : C⁻¹ * p * Real.exp (-C*u) ≤ A * p * Real.exp (-4*L*u) := by
    gcongr
  have h₂ : A * p * Real.exp (-4*L*u) ≤ c * p * b^n := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hpow' (mul_nonneg hc.le hp)]
  exact h₁.trans h₂

/-- A native near-diagonal estimate propagates to a Gaussian lower bound. -/
theorem c12_native_gaussian_lower_of_near_diagonal {d : ℕ}
 (κ c : ℝ) (hκ : 0 < κ) (hc : 0 < c) :
 ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R →
 ∀ (ρ : Vec d → ℝ) (q : ℝ → Vec d → Vec d → ℝ),
 Measurable ρ → (∀ z, κ ≤ ρ z) →
 (∀ s, 0 < s → ∀ x y, 0 ≤ q s x y) →
 (∀ s t, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
   IntegrableOn (fun z => q s x z*q t z y*ρ z) (sourceBall 0 R)) →
 (∀ s t, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
   q (s+t) x y=∫ z in sourceBall 0 R, q s x z*q t z y*ρ z) →
 (∀ s, 0 < s → s ≤ R^2 → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
   euclideanSq (x-y) ≤ s → c*Real.rpow s (-(d:ℝ)/2) ≤ q s x y) →
 ∀ t, 0 < t → t ≤ R^2/64 → ∀ x ∈ sourceBall 0 (R/2),
 ∀ y ∈ sourceBall 0 (R/2),
 C⁻¹*Real.rpow t (-(d:ℝ)/2)*Real.exp (-C * euclideanSq (x-y) / t) ≤ q t x y := by
  let V : ℝ := (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
  have hV : 0 < V := by
    have hv := c12_sourceBall_volume (0 : Vec d) (by norm_num : (0 : ℝ) < 1)
    have hp := hv.2.2.1
    rw [hv.2.2.2] at hp
    simpa [V] using hp
  let b : ℝ := c * κ * (8 : ℝ)⁻¹^d * V
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨C, hC, habs⟩ := c12_gaussian_absorb_chain c b hc hb
  refine ⟨C, hC, ?_⟩
  intro R hR ρ q hmeas hρ hq hint hsemi hnear t ht htR x hx y hy
  obtain ⟨N, hN, hNupper, S, hS, hxS, hyS⟩ :=
    c12_chain_admissible_balls R t hR ht htR x y hx hy
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  let h : ℝ := t / (n+1 : ℕ)
  have hNr : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hh : 0 < h := div_pos ht hNr
  have hle : h ≤ t := by
    dsimp [h]
    exact div_le_self ht.le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hhR : h ≤ R^2 := by nlinarith [sq_nonneg R]
  let v : ℝ := (Real.sqrt h / 8)^d * V
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hchain := c12_native_near_diagonal_finite_chain R h κ c v hR hh hhR hκ hc hv
    ρ q hρ hq hint hsemi hnear S (fun n => (hS n).1) (fun n => (hS n).2.1)
    (fun n => by rw [(hS n).2.2.1]) (fun n => (hS n).2.2.2) x hxS n y hyS
  have htime : ((n+1 : ℕ) : ℝ) * h = t := by dsimp [h]; field_simp
  rw [htime] at hchain
  have hfactor : (c * Real.rpow h (-(d : ℝ)/2)) * κ * v = b := by
    dsimp [v, b]
    have hcanc := c12_chain_volume_time_cancellation d h hh
    calc
      _ = c * κ * (Real.rpow h (-(d : ℝ)/2) * (Real.sqrt h / 8)^d) * V := by
        simp only [Real.rpow_eq_pow]
        ac_rfl
      _ = _ := by rw [hcanc]
  rw [hfactor] at hchain
  have hD : 0 ≤ euclideanSq (x-y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hn : (n : ℝ) ≤ 4 * (euclideanSq (x-y) / t) + 2 := by
    calc
      (n : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast Nat.le_succ n
      _ ≤ 4 * (euclideanSq (x-y) / t) + 2 := by simpa only [mul_div_assoc] using hNupper
  have hexp : -(d : ℝ)/2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num)
  have hp := Real.rpow_le_rpow_of_nonpos hh hle hexp
  have hbound := habs (euclideanSq (x-y)/t) n (Real.rpow t (-(d : ℝ)/2))
    (div_nonneg hD ht.le) (Real.rpow_pos_of_pos ht _).le hn
  have hbpow : 0 ≤ b^n := pow_nonneg hb.le _
  calc
    _ = C⁻¹ * Real.rpow t (-(d : ℝ)/2) * Real.exp (-C * (euclideanSq (x-y)/t)) := by congr 2 <;> ring
    _ ≤ c * Real.rpow t (-(d : ℝ)/2) * b^n := hbound
    _ ≤ c * Real.rpow h (-(d : ℝ)/2) * b^n := by
      gcongr
      exact hp
    _ ≤ q t x y := hchain

end EinsteinFull.Calculus
