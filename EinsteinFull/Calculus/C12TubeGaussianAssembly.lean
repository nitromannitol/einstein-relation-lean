import EinsteinFull.Calculus.C12TubeWeightedGaussianUpper
import EinsteinFull.Calculus.C9TubeNativeDyadicRowTails
import EinsteinFull.Calculus.FellerRegularSet
import EinsteinFull.Calculus.C17TubeCountableExteriorCover

open EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull.Calculus

/-- A Gaussian upper envelope holding almost everywhere extends to all interior
pairs, with the ellipticity loss from the supplied kernel's weighted symmetry. -/
theorem c12_supplied_gaussian_envelope_pointwise {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t A B : ℝ) (ht : 0 < t) (hA : 0 ≤ A)
    (hae : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      ∀ᵐ y ∂volume.restrict (sourceBall (0 : Vec d) R),
        K t x y ≤ A * Real.exp (-(euclideanNorm (x-y))^2 / B)) :
    ∀ x ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
      K t x y ≤ κ⁻¹ * ((A * Real.exp (-(euclideanNorm (x-y))^2 / B)) / κ) := by
  apply c12_supplied_kernel_envelope_pointwise hκ h K G hK t ht
    (fun x y => A * Real.exp (-(euclideanNorm (x-y))^2 / B))
  · intro x hx y hy
    exact mul_nonneg hA (Real.exp_pos _).le
  · intro y
    exact ((continuous_const.mul
      (((Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)).pow 2 |>.neg |>.div_const B |>.rexp)).continuousOn)
  · intro x
    exact ((continuous_const.mul
      (((Feller.continuous_euclideanNorm d).comp
        (continuous_const.sub continuous_id)).pow 2 |>.neg |>.div_const B |>.rexp)).continuousOn)
  · exact hae

#print axioms c12_supplied_gaussian_envelope_pointwise

/-- Nested Euclidean exterior sets are separated by the difference of their
radii. This is the spatial separation used in the tail iteration. -/
theorem c12_exterior_separation {d : ℕ} (c z y : Vec d) (r δ : ℝ)
    (hz : r + δ ≤ euclideanNorm (z - c))
    (hy : euclideanNorm (y - c) < r) :
    δ ≤ euclideanNorm (z - y) := by
  have ht := TimeChange.euclideanNorm_add_le (z - y) (y - c)
  have he : (z - y) + (y - c) = z - c := by abel
  rw [he] at ht
  linarith

#print axioms c12_exterior_separation

/-- The decreasing exterior radii have a geometric separation at each step. -/
theorem c12_geometric_exterior_radius_step (r : ℝ) (n : ℕ) :
    r * (1 + (3 / 4 : ℝ) ^ (n + 1)) + (r / 4) * (3 / 4 : ℝ) ^ n =
      r * (1 + (3 / 4 : ℝ) ^ n) := by
  rw [pow_succ]
  ring

/-- The dyadic time step splits into a positive heat-flow interval and the
next time in the iteration. -/
theorem c12_dyadic_time_step (t : ℝ) (n : ℕ) :
    t / (4 : ℝ) ^ n = 3 * t / (4 : ℝ) ^ (n + 1) +
      t / (4 : ℝ) ^ (n + 1) := by
  rw [pow_succ]
  have h : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  <;> ring

#print axioms c12_geometric_exterior_radius_step
#print axioms c12_dyadic_time_step

/-- A tail recurrence with geometrically bounded leakage and vanishing
remainder gives a Gaussian estimate, uniformly in the iteration depth. -/
theorem c12_geometric_tail_bound (r b : ℝ) (hr : 0 < r) (hb : 1 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a H X : ℝ) (q e : ℕ → ℝ),
      1 ≤ a → 0 ≤ H → Filter.Tendsto q Filter.atTop (𝓝 0) →
      (∀ n, e n ≤ H * (r ^ n * Real.exp (-a * b ^ n))) →
      (∀ N, X ≤ (∑ n ∈ Finset.range N, e n) + q N) →
      X ≤ H * (C * Real.exp (-a / 2)) := by
  obtain ⟨C, hC, hleak⟩ := c12_geometric_gaussian_leakage_sum r b hr hb
  refine ⟨C, hC, ?_⟩
  intro a H X q e ha hH hq he hi
  have hl : Filter.Tendsto (fun N : ℕ => H * (C * Real.exp (-a / 2)) + q N)
      Filter.atTop (𝓝 (H * (C * Real.exp (-a / 2)) + 0)) :=
    tendsto_const_nhds.add hq
  have hbound : ∀ N, X ≤ H * (C * Real.exp (-a / 2)) + q N := by
    intro N
    calc
      X ≤ (∑ n ∈ Finset.range N, e n) + q N := hi N
      _ ≤ (∑ n ∈ Finset.range N, H * (r ^ n * Real.exp (-a * b ^ n))) + q N := by
        simpa only [add_comm] using
          add_le_add_right (Finset.sum_le_sum (s := Finset.range N) fun n _ => he n) (q N)
      _ = H * (∑ n ∈ Finset.range N, r ^ n * Real.exp (-a * b ^ n)) + q N := by
        rw [Finset.mul_sum]
      _ ≤ H * (C * Real.exp (-a / 2)) + q N := by
        simpa only [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_left (hleak a ha N) hH) (q N)
  have hlim := ge_of_tendsto hl (Filter.Eventually.of_forall hbound)
  simpa only [add_zero] using hlim

#print axioms c12_geometric_tail_bound

/-- The squared norm of a restricted spectral row is its literal squared
spectral-series integral. -/
theorem c12_restricted_spectral_row_norm_sq {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (t : ℝ) (ht : 0 < t)
    (x : Vec d) (hx : x ∈ sourceBall 0 R) (B : Set (Vec d))
    (hB : MeasurableSet B) :
    let row := spectralHeatRow s t x
    ‖((Lp.memLp row).indicator hB).toLp (B.indicator fun y => row y)‖ ^ 2 =
      ∫ y in B, (∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n x * s.eigenfunction n y)^2 ∂dirichletVolume ρ R := by
  let row := spectralHeatRow s t x
  let f := B.indicator fun y => row y
  have hf : MemLp f 2 (dirichletVolume ρ R) := (Lp.memLp row).indicator hB
  have hnorm : ‖hf.toLp f‖ ^ 2 = ∫ y, f y ^ 2 ∂dirichletVolume ρ R := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with y hy
    rw [hy]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  change ‖hf.toLp f‖ ^ 2 = _
  rw [hnorm, ← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht x hx] with y hy
  change row y = _ at hy
  by_cases hyB : y ∈ B
  · simp only [Set.indicator_of_mem hyB, f]
    rw [hy]
  · simp [f, hyB]

#print axioms c12_restricted_spectral_row_norm_sq

/-- If the squared mass in a fixed set tends to zero, then the restricted
row norms tend to zero for any measurable subsets of that set. -/
theorem c12_restricted_spectral_row_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (x : Vec d) (hx : x ∈ sourceBall 0 R) (B : Set (Vec d))
    (hB : MeasurableSet B) (A : ℕ → Set (Vec d))
    (hA : ∀ n, MeasurableSet (A n))
    (hAB : ∀ n, ∀ᵐ y ∂dirichletVolume ρ R, y ∈ A n → y ∈ B)
    (hlim : Tendsto (fun n : ℕ => ∫ y in B,
      (∑' i, Real.exp (-s.eigenvalue i * t n) *
        s.eigenfunction i x * s.eigenfunction i y)^2 ∂dirichletVolume ρ R)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ‖((Lp.memLp (spectralHeatRow s (t n) x)).indicator (hA n)).toLp
        ((A n).indicator fun y => spectralHeatRow s (t n) x y)‖) atTop (𝓝 0) := by
  let row (n : ℕ) := spectralHeatRow s (t n) x
  let f (n : ℕ) := ((Lp.memLp (row n)).indicator (hA n)).toLp
    ((A n).indicator fun y => row n y)
  let g (n : ℕ) := ((Lp.memLp (row n)).indicator hB).toLp
    (B.indicator fun y => row n y)
  have hnorm (n : ℕ) : ‖f n‖ ≤ ‖g n‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [((Lp.memLp (row n)).indicator (hA n)).coeFn_toLp,
      ((Lp.memLp (row n)).indicator hB).coeFn_toLp, hAB n] with y hyA hyB hyAB
    change ‖f n y‖ ≤ ‖g n y‖
    rw [hyA, hyB]
    by_cases hy : y ∈ A n
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hyAB hy)]
    · simp [hy]
  have hg : Tendsto (fun n => ‖g n‖ ^ 2) atTop (𝓝 0) := by
    apply hlim.congr'
    exact Filter.Eventually.of_forall fun n =>
      (c12_restricted_spectral_row_norm_sq hd hκ hR h s (t n) (ht n) x hx B hB).symm
  have hroot : Tendsto (fun n => Real.sqrt (‖g n‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hg
  have hg0 : Tendsto (fun n => ‖g n‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hroot
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg (f n))
    (Filter.Eventually.of_forall hnorm) hg0

#print axioms c12_restricted_spectral_row_tendsto_zero

/-- The dyadic initial-tail theorem supplies the vanishing remainder required
by the nested-exterior iteration. -/
theorem c12_dyadic_restricted_row_remainder_ae {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (s : DirichletSpectralResolution ρ α R)
    (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAb : A ⊆ sourceBall 0 R) (hBb : B ⊆ sourceBall 0 R)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x-y))
    (t₀ : ℝ) (ht₀ : 0 < t₀) (E : ℕ → Set (Vec d))
    (hE : ∀ n, MeasurableSet (E n))
    (hEB : ∀ n, E n ∩ sourceBall (0 : Vec d) R ⊆ B) :
    ∀ᵐ x ∂dirichletVolume ρ R, x ∈ A →
      Tendsto (fun n : ℕ =>
        ‖((Lp.memLp (spectralHeatRow s (t₀ / (4 : ℝ)^n) x)).indicator (hE n)).toLp
          ((E n).indicator fun y => spectralHeatRow s (t₀ / (4 : ℝ)^n) x y)‖)
        atTop (𝓝 0) := by
  filter_upwards [c9_native_offdiagonal_row_L2_dyadic_zero hd hκ hR h K G hK s hs
    A B hA hB hAb hBb δ hδ hsep t₀ ht₀] with x hx hxA
  apply c12_restricted_spectral_row_tendsto_zero hd hκ hR h s
    (fun n => t₀ / (4 : ℝ)^n) (fun n => by positivity) x (hAb hxA) B hB E hE
  · intro n
    have hball : MeasurableSet (sourceBall (0 : Vec d) R) :=
      (dirichletBall (d := d) R).isOpen.measurableSet
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hball)]
      with y hy hyE
    exact hEB n ⟨hyE, hy⟩
  · exact hx hxA

#print axioms c12_dyadic_restricted_row_remainder_ae

/-- The finite spectral tail iteration for the geometric exterior sets and
dyadic time steps used in the Gaussian estimate. -/
theorem c12_geometric_spectral_tail_iteration {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (x : Vec d) (hx : x ∈ sourceBall 0 R) (c : Vec d)
    (r t₀ : ℝ) (hr : 0 < r) (ht₀ : 0 < t₀)
    (E : ℕ → Set (Vec d)) (hE : ∀ n, MeasurableSet (E n))
    (hshape : ∀ n, E n = {z | r * (1 + (3 / 4 : ℝ)^n) ≤ euclideanNorm (z-c)})
    (N : ℕ) :
    let row := fun n => spectralHeatRow s (t₀ / (4 : ℝ)^n) x
    let restrict := fun n => ((Lp.memLp (row n)).indicator (hE n)).toLp
      ((E n).indicator fun z => row n z)
    ‖restrict 0‖ ≤ (∑ n ∈ Finset.range N,
      Real.exp (-((r / 4 * (3 / 4 : ℝ)^n)^2) /
        ((16 * κ⁻¹ ^ 2) * (3 * t₀ / (4 : ℝ)^(n+1)))) * ‖row (n+1)‖) +
        ‖restrict N‖ := by
  let δ (n : ℕ) : ℝ := r / 4 * (3 / 4 : ℝ)^n
  let p (n : ℕ) : ℝ≥0 := ⟨3 * t₀ / (4 : ℝ)^(n+1), by positivity⟩
  let t (n : ℕ) : ℝ := t₀ / (4 : ℝ)^n
  have hδ : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  have hp : ∀ n, 0 < p n := by intro n; change 0 < 3 * t₀ / (4 : ℝ)^(n+1); positivity
  have ht : ∀ n, 0 < t n := by intro n; dsimp [t]; positivity
  have hstep : ∀ n, t n = (p n : ℝ) + t (n+1) := by
    intro n
    exact c12_dyadic_time_step t₀ n
  have hnonempty : ∀ n, (E (n+1))ᶜ.Nonempty := by
    intro n
    refine ⟨c, ?_⟩
    rw [hshape]
    change ¬ r * (1 + (3 / 4 : ℝ)^(n+1)) ≤ euclideanNorm (c-c)
    have hz : euclideanNorm (c-c) = 0 := by simp [euclideanNorm, euclideanSq, dot]
    rw [hz]
    have : 0 < r * (1 + (3 / 4 : ℝ)^(n+1)) := by positivity
    linarith
  have hsep : ∀ n, ∀ z ∈ E n, ∀ y ∈ (E (n+1))ᶜ,
      δ n ≤ euclideanNorm (z-y) := by
    intro n z hz y hy
    rw [hshape] at hz hy
    change r * (1 + (3 / 4 : ℝ)^n) ≤ euclideanNorm (z-c) at hz
    change ¬ r * (1 + (3 / 4 : ℝ)^(n+1)) ≤ euclideanNorm (y-c) at hy
    apply c12_exterior_separation c z y
      (r * (1 + (3 / 4 : ℝ)^(n+1))) (δ n)
    · rw [show r * (1 + (3 / 4 : ℝ)^(n+1)) + δ n =
        r * (1 + (3 / 4 : ℝ)^n) from c12_geometric_exterior_radius_step r n]
      exact hz
    · exact lt_of_not_ge hy
  have hh := c12_supplied_spectral_heat_tail_iteration hd hκ hR h s hspec x hx E hE
    hnonempty δ hδ hsep p hp t ht hstep N
  dsimp [δ, p, t] at hh
  exact hh

#print axioms c12_geometric_spectral_tail_iteration

/-- The separation-to-time ratio in the dyadic iteration grows by `9/4`
at each step. -/
theorem c12_geometric_separation_time_ratio (r t κ : ℝ)
    (ht : 0 < t) (hκ : 0 < κ) (n : ℕ) :
    (r / 4 * (3 / 4 : ℝ)^n)^2 /
      ((16 * κ⁻¹ ^ 2) * (3 * t / (4 : ℝ)^(n+1))) =
      (r^2 / (192 * κ⁻¹^2 * t)) * (9 / 4 : ℝ)^n := by
  have hgeom : ((3 / 4 : ℝ)^n)^2 * (4 : ℝ)^n = (9 / 4 : ℝ)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow]
    norm_num
  have hfour : (4 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hkinv : κ⁻¹ ≠ 0 := inv_ne_zero hκ.ne'
  rw [← hgeom, pow_succ]
  field_simp
  ring

#print axioms c12_geometric_separation_time_ratio

/-- Taking the square root of a dyadic Nash bound gives geometric growth of
the row norm. -/
theorem c12_dyadic_nash_sqrt (C t D : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (n : ℕ) :
    Real.sqrt (C * (t / (4 : ℝ)^n) ^ (-D / 2)) =
      Real.sqrt C * t ^ (-D / 4) * ((4 : ℝ) ^ (D / 4))^n := by
  rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow ((t / (4 : ℝ)^n) ^ (-D / 2)),
    ← Real.rpow_mul (div_nonneg ht.le (pow_nonneg (by norm_num) n))]
  have hexp : (-D / 2) * (1 / 2 : ℝ) = -D / 4 := by ring
  have hn : -D / 4 = -(D / 4) := by ring
  rw [hexp, hn, Real.div_rpow ht.le (pow_nonneg (by norm_num) n),
    Real.rpow_neg (pow_nonneg (by norm_num) n), div_inv_eq_mul]
  have hp : ((4 : ℝ)^n) ^ (D / 4) = ((4 : ℝ) ^ (D / 4))^n := by
    rw [← Real.rpow_natCast (4 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
      mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_natCast]
  rw [hp]
  ring

#print axioms c12_dyadic_nash_sqrt

/-- A geometric exterior row has Gaussian L² decay once its initial tail
vanishes; the latter is supplied by the native dyadic off-diagonal theorem. -/
theorem c12_geometric_exterior_row_bound_ae {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R : ℝ} (hR : 0 < R)
      {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) ∧
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hAb : A ⊆ sourceBall 0 R) (hBb : B ⊆ sourceBall 0 R)
      (δ : ℝ) (hδ : 0 < δ)
      (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x-y))
      (c : Vec d) (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
      (E : ℕ → Set (Vec d)) (hE : ∀ n, MeasurableSet (E n))
      (hshape : ∀ n, E n = {z | r * (1 + (3 / 4 : ℝ)^n) ≤ euclideanNorm (z-c)})
      (hEB : ∀ n, E n ∩ sourceBall (0 : Vec d) R ⊆ B)
      (ha : 1 ≤ r^2 / (192 * κ⁻¹^2 * t)),
      ∀ᵐ x ∂dirichletVolume ρ R, x ∈ A →
        ‖((Lp.memLp (spectralHeatRow s t x)).indicator (hE 0)).toLp
          ((E 0).indicator fun y => spectralHeatRow s t x y)‖ ≤
        C * t ^ (-(d : ℝ) / 4) *
          Real.exp (-(r^2 / (192 * κ⁻¹^2 * t)) / 2) := by
  obtain ⟨C₀, hC₀, hNash⟩ := c12_supplied_heat_row_L2_decay_pointwise hd hκ
  let b : ℝ := (4 : ℝ) ^ ((d : ℝ) / 4)
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨C₁, hC₁, htail⟩ := c12_geometric_tail_bound b (9 / 4) hb (by norm_num)
  refine ⟨Real.sqrt C₀ * b * C₁, by positivity, ?_⟩
  intro R hR ρ α h K G hK s hs A B hA hB hAb hBb δ hδ hsep c r t hr ht E hE hshape hEB ha
  filter_upwards [c12_dyadic_restricted_row_remainder_ae hd hκ hR h K G hK s
    (fun t ht x hx y hy => (hs t ht x hx y hy).2)
    A B hA hB hAb hBb δ hδ hsep t ht E hE hEB] with x hx hxA
  let row (n : ℕ) := spectralHeatRow s (t / (4 : ℝ)^n) x
  let q (n : ℕ) := ‖((Lp.memLp (row n)).indicator (hE n)).toLp
    ((E n).indicator fun y => row n y)‖
  let a : ℝ := r^2 / (192 * κ⁻¹^2 * t)
  let H : ℝ := Real.sqrt C₀ * t ^ (-(d : ℝ) / 4) * b
  let e (n : ℕ) := Real.exp (-a * (9 / 4 : ℝ)^n) * ‖row (n+1)‖
  have hq : Tendsto q atTop (𝓝 0) := hx hxA
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have he : ∀ n, e n ≤ H * (b^n * Real.exp (-a * (9 / 4 : ℝ)^n)) := by
    intro n
    have hn := hNash R hR ρ α h K G hK s hs (t / (4 : ℝ)^(n+1))
      (by positivity) x (hAb hxA)
    have hn' : ‖row (n+1)‖ ≤ Real.sqrt (C₀ * (t / (4 : ℝ)^(n+1)) ^ (-(d : ℝ) / 2)) := by
      apply (Real.le_sqrt (norm_nonneg _) (by positivity)).2
      exact hn
    rw [c12_dyadic_nash_sqrt C₀ t (d : ℝ) hC₀.le ht (n+1)] at hn'
    have hrow : ‖row (n+1)‖ ≤ H * b^n := by
      calc
        _ ≤ Real.sqrt C₀ * t ^ (-(d : ℝ) / 4) * b^(n+1) := hn'
        _ = H * b^n := by dsimp [H]; rw [pow_succ]; ring
    dsimp [e]
    calc
      _ ≤ Real.exp (-a * (9 / 4 : ℝ)^n) * (H * b^n) :=
        mul_le_mul_of_nonneg_left hrow (Real.exp_pos _).le
      _ = _ := by ring
  have hi : ∀ N, q 0 ≤ (∑ n ∈ Finset.range N, e n) + q N := by
    intro N
    have hh := c12_geometric_spectral_tail_iteration hd hκ hR h s
      (fun t ht x hx y hy => (hs t ht x hx y hy).1)
      x (hAb hxA) c r t hr ht E hE hshape N
    simpa only [q, row, e, a, neg_div, c12_geometric_separation_time_ratio r t κ ht hκ, neg_mul] using hh
  have hh := htail a H (q 0) q e ha hH hq he hi
  simpa only [q, row, pow_zero, div_one, H, a] using (show q 0 ≤
    (Real.sqrt C₀ * b * C₁) * t ^ (-(d : ℝ) / 4) * Real.exp (-a / 2) by
      calc
        q 0 ≤ H * (C₁ * Real.exp (-a / 2)) := hh
        _ = _ := by dsimp [H]; ring)

#print axioms c12_geometric_exterior_row_bound_ae

/-- The geometric exterior estimate for a ball of starting points and its
concentric exterior, with the native initial-tail theorem discharged. -/
theorem c12_concentric_exterior_row_bound_ae {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R : ℝ} (hR : 0 < R)
      {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) ∧
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (c : Vec d) (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
      (ha : 1 ≤ r^2 / (192 * κ⁻¹^2 * t)),
      ∀ᵐ x ∂dirichletVolume ρ R,
        x ∈ sourceBall (0 : Vec d) R → euclideanNorm (x-c) < r/2 →
        ‖((Lp.memLp (spectralHeatRow s t x)).indicator
          ((isClosed_le continuous_const ((Feller.continuous_euclideanNorm d).comp
            (continuous_id.sub continuous_const))).measurableSet)).toLp
          ({z | 2*r ≤ euclideanNorm (z-c)}.indicator fun y => spectralHeatRow s t x y)‖ ≤
        C * t ^ (-(d : ℝ) / 4) *
          Real.exp (-(r^2 / (192 * κ⁻¹^2 * t)) / 2) := by
  obtain ⟨C, hC, hrow⟩ := c12_geometric_exterior_row_bound_ae hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK s hs c r t hr ht ha
  let A : Set (Vec d) := sourceBall 0 R ∩ {z | euclideanNorm (z-c) < r/2}
  let B : Set (Vec d) := sourceBall 0 R ∩ {z | r ≤ euclideanNorm (z-c)}
  let E (n : ℕ) : Set (Vec d) := {z | r * (1 + (3 / 4 : ℝ)^n) ≤ euclideanNorm (z-c)}
  have hcont : Continuous (fun z : Vec d => euclideanNorm (z-c)) :=
    (Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const)
  have hball : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hA : MeasurableSet A := hball.inter (isOpen_lt hcont continuous_const).measurableSet
  have hB : MeasurableSet B := hball.inter (isClosed_le continuous_const hcont).measurableSet
  have hE : ∀ n, MeasurableSet (E n) := fun n => (isClosed_le continuous_const hcont).measurableSet
  have hsep : ∀ x ∈ A, ∀ y ∈ B, r/2 ≤ euclideanNorm (x-y) := by
    intro x hx y hy
    have hh : r/2 ≤ euclideanNorm (y-x) := by
      apply c12_exterior_separation c y x (r/2) (r/2)
      · have : r / 2 + r / 2 = r := by ring
        rw [this]
        exact hy.2
      · exact hx.2
    have hneg (z : Vec d) : euclideanNorm (-z) = euclideanNorm z := by
      have hz := TimeChange.euclideanNorm_smul (-1 : ℝ) z
      simpa using hz
    rw [← neg_sub x y, hneg] at hh
    exact hh
  have hEB : ∀ n, E n ∩ sourceBall (0 : Vec d) R ⊆ B := by
    intro n z hz
    refine ⟨hz.2, ?_⟩
    have hp : 0 ≤ (3 / 4 : ℝ)^n := by positivity
    have he : r ≤ r * (1 + (3 / 4 : ℝ)^n) := by nlinarith
    exact he.trans hz.1
  have hres := hrow hR h K G hK s hs A B hA hB
    (fun _ hx => hx.1) (fun _ hx => hx.1) (r/2) (by positivity) hsep
    c r t hr ht E hE (fun _ => rfl) hEB ha
  filter_upwards [hres] with x hx hxball hxc
  have hh := hx ⟨hxball, hxc⟩
  simpa only [E, pow_zero, show r * (1 + (1 : ℝ)) = 2 * r by ring] using hh

#print axioms c12_concentric_exterior_row_bound_ae

/-- A countable cover transfers the concentric row bound to almost every
center, with a larger exterior radius. -/
theorem c12_global_exterior_row_bound_ae {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R : ℝ} (hR : 0 < R)
      {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) ∧
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
      (ha : 1 ≤ r^2 / (192 * κ⁻¹^2 * t)),
      ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall (0 : Vec d) R →
        ‖((Lp.memLp (spectralHeatRow s t x)).indicator
          ((isClosed_le continuous_const ((Feller.continuous_euclideanNorm d).comp
            (continuous_id.sub continuous_const))).measurableSet)).toLp
          ({z | 3*r ≤ euclideanNorm (z-x)}.indicator fun y => spectralHeatRow s t x y)‖ ≤
        C * t ^ (-(d : ℝ) / 4) *
          Real.exp (-(r^2 / (192 * κ⁻¹^2 * t)) / 2) := by
  obtain ⟨C, hC, hlocal⟩ := c12_concentric_exterior_row_bound_ae hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK s hs r t hr ht ha
  obtain ⟨q, hcover⟩ := c17_countable_sourceBall_cover (d := d) hr
  have hall : ∀ᵐ x ∂dirichletVolume ρ R, ∀ n, x ∈ sourceBall (0 : Vec d) R →
      euclideanNorm (x-q n) < r/2 →
      ‖((Lp.memLp (spectralHeatRow s t x)).indicator
        ((isClosed_le continuous_const ((Feller.continuous_euclideanNorm d).comp
          (continuous_id.sub continuous_const))).measurableSet)).toLp
        ({z | 2*r ≤ euclideanNorm (z-q n)}.indicator fun y => spectralHeatRow s t x y)‖ ≤
      C * t ^ (-(d : ℝ) / 4) * Real.exp (-(r^2 / (192 * κ⁻¹^2 * t)) / 2) := by
    apply ae_all_iff.mpr
    intro n
    exact hlocal hR h K G hK s hs (q n) r t hr ht ha
  filter_upwards [hall] with x hx hxball
  obtain ⟨n, hn⟩ := hcover x
  change euclideanNorm (x-q n) < r/2 at hn
  let A : Set (Vec d) := {z | 3*r ≤ euclideanNorm (z-x)}
  let B : Set (Vec d) := {z | 2*r ≤ euclideanNorm (z-q n)}
  have hA : MeasurableSet A := (isClosed_le continuous_const
    ((Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const))).measurableSet
  have hB : MeasurableSet B := (isClosed_le continuous_const
    ((Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const))).measurableSet
  have hAB : A ⊆ B := by
    intro z hz
    change 3*r ≤ euclideanNorm (z-x) at hz
    change 2*r ≤ euclideanNorm (z-q n)
    have hneg (v : Vec d) : euclideanNorm (-v) = euclideanNorm v := by
      simpa using TimeChange.euclideanNorm_smul (-1 : ℝ) v
    have ht' := TimeChange.euclideanNorm_add_le (z-q n) (q n-x)
    have he : (z-q n) + (q n-x) = z-x := by abel
    rw [he, ← neg_sub x (q n), hneg] at ht'
    linarith
  have hnorm : ‖((Lp.memLp (spectralHeatRow s t x)).indicator hA).toLp
        (A.indicator fun y => spectralHeatRow s t x y)‖ ≤
      ‖((Lp.memLp (spectralHeatRow s t x)).indicator hB).toLp
        (B.indicator fun y => spectralHeatRow s t x y)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [((Lp.memLp (spectralHeatRow s t x)).indicator hA).coeFn_toLp,
      ((Lp.memLp (spectralHeatRow s t x)).indicator hB).coeFn_toLp] with z hzA hzB
    rw [hzA, hzB]
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hAB hz)]
    · simp [hz]
  exact hnorm.trans (hx n hxball hn)

#print axioms c12_global_exterior_row_bound_ae

/-- Splitting the intermediate point between two measurable exterior sets
bounds the row-pair inner product by two Cauchy–Schwarz terms. -/
theorem c12_L2_inner_exterior_split {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : Lp ℝ 2 μ) (A B : Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Aᶜ ⊆ B) :
    let fa := ((Lp.memLp f).indicator hA).toLp (A.indicator fun z => f z)
    let gb := ((Lp.memLp g).indicator hB).toLp (B.indicator fun z => g z)
    inner ℝ f g ≤ ‖fa‖ * ‖g‖ + ‖f‖ * ‖gb‖ := by
  let fa := ((Lp.memLp f).indicator hA).toLp (A.indicator fun z => f z)
  let fc := ((Lp.memLp f).indicator hA.compl).toLp (Aᶜ.indicator fun z => f z)
  let gb := ((Lp.memLp g).indicator hB).toLp (B.indicator fun z => g z)
  have hsplit : fa + fc = f := by
    apply Lp.ext
    filter_upwards [((Lp.memLp f).indicator hA).coeFn_toLp,
      ((Lp.memLp f).indicator hA.compl).coeFn_toLp, Lp.coeFn_add fa fc] with z hz1 hz2 hz3
    change (fa + fc) z = f z
    rw [hz3]
    change fa z + fc z = f z
    rw [hz1, hz2]
    by_cases hz : z ∈ A <;> simp [hz]
  have hfc : ‖fc‖ ≤ ‖f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [((Lp.memLp f).indicator hA.compl).coeFn_toLp] with z hz
    change ‖fc z‖ ≤ ‖f z‖
    rw [hz]
    by_cases hza : z ∈ A <;> simp [hza]
  have heq : inner ℝ fc g = inner ℝ fc gb := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((Lp.memLp f).indicator hA.compl).coeFn_toLp,
      ((Lp.memLp g).indicator hB).coeFn_toLp] with z hz1 hz2
    change inner ℝ (fc z) (g z) = inner ℝ (fc z) (gb z)
    rw [hz1, hz2]
    by_cases hza : z ∈ A
    · simp [hza]
    · have hzb : z ∈ B := hAB hza
      simp [hza, hzb]
  change inner ℝ f g ≤ ‖fa‖ * ‖g‖ + ‖f‖ * ‖gb‖
  rw [← hsplit, inner_add_left, heq]
  have h1 := real_inner_le_norm fa g
  have h2 := real_inner_le_norm fc gb
  have h3 := mul_le_mul_of_nonneg_right hfc (norm_nonneg gb)
  rw [hsplit]
  linarith

#print axioms c12_L2_inner_exterior_split

/-- Every intermediate point lies at least half the endpoint distance from
one of the two endpoints. -/
theorem c12_half_distance_exterior_split {d : ℕ} (x y z : Vec d) :
    euclideanNorm (y-x) / 2 ≤ euclideanNorm (z-x) ∨
      euclideanNorm (y-x) / 2 ≤ euclideanNorm (z-y) := by
  have hneg (v : Vec d) : euclideanNorm (-v) = euclideanNorm v := by
    have hv := TimeChange.euclideanNorm_smul (-1 : ℝ) v
    simpa using hv
  have ht := TimeChange.euclideanNorm_add_le (z-x) (y-z)
  have he : (z-x) + (y-z) = y-x := by abel
  rw [he, ← neg_sub z y, hneg] at ht
  rcases le_total (euclideanNorm (y-x) / 2) (euclideanNorm (z-x)) with h | h
  · exact Or.inl h
  · right
    linarith

#print axioms c12_half_distance_exterior_split

/-- Two exterior row bounds and two full-row bounds give the corresponding
spectral kernel bound at twice the row time. -/
theorem c12_spectral_kernel_pair_from_exterior_rows {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ)
    (s : DirichletSpectralResolution ρ α R)
    (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
    (t : ℝ) (ht : 0 < t) (x y : Vec d)
    (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R)
    (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hfullx : ‖spectralHeatRow s t x‖ ≤ M)
    (hfully : ‖spectralHeatRow s t y‖ ≤ M)
    (htail : ∀ a ∈ ({x, y} : Set (Vec d)),
      ‖((Lp.memLp (spectralHeatRow s t a)).indicator
        ((isClosed_le continuous_const ((Feller.continuous_euclideanNorm d).comp
          (continuous_id.sub continuous_const))).measurableSet)).toLp
        ({z | euclideanNorm (y-x) / 2 ≤ euclideanNorm (z-a)}.indicator
          fun z => spectralHeatRow s t a z)‖ ≤ T) :
    K (t+t) x y ≤ 2 * κ⁻¹ * M * T := by
  let A : Set (Vec d) := {z | euclideanNorm (y-x) / 2 ≤ euclideanNorm (z-x)}
  let B : Set (Vec d) := {z | euclideanNorm (y-x) / 2 ≤ euclideanNorm (z-y)}
  have hA : MeasurableSet A := (isClosed_le continuous_const
    ((Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const))).measurableSet
  have hB : MeasurableSet B := (isClosed_le continuous_const
    ((Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const))).measurableSet
  have hAB : Aᶜ ⊆ B := by
    intro z hz
    rcases c12_half_distance_exterior_split x y z with hzx | hzy
    · exact False.elim (hz hzx)
    · exact hzy
  have hinner := c12_L2_inner_exterior_split (dirichletVolume ρ R)
    (spectralHeatRow s t x) (spectralHeatRow s t y) A B hA hB hAB
  have htx := htail x (by simp)
  have hty := htail y (by simp)
  have hb : inner ℝ (spectralHeatRow s t x) (spectralHeatRow s t y) ≤ 2 * M * T := by
    calc
      _ ≤ _ := hinner
      _ ≤ T * M + M * T := add_le_add
        (mul_le_mul htx hfully (norm_nonneg _) hT)
        (mul_le_mul hfullx hty (norm_nonneg _) hM)
      _ = _ := by ring
  rw [hs (t+t) (add_pos ht ht) x hx y hy,
    ← spectral_heat_row_inner hd hκ h hR s t t ht ht x y hx hy]
  have hρ : 0 ≤ ρ y := (lt_of_lt_of_le hκ (h.2.2 y).1).le
  calc
    _ ≤ ρ y * (2 * M * T) := mul_le_mul_of_nonneg_left hb hρ
    _ ≤ κ⁻¹ * (2 * M * T) :=
      mul_le_mul_of_nonneg_right (h.2.2 y).2.1 (by positivity)
    _ = _ := by ring

#print axioms c12_spectral_kernel_pair_from_exterior_rows

/-- Restricting a spectral row to a smaller measurable set cannot increase
its L² norm. -/
theorem c12_restricted_spectral_row_mono {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {R : ℝ} (s : DirichletSpectralResolution ρ α R) (t : ℝ) (x : Vec d)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    ‖((Lp.memLp (spectralHeatRow s t x)).indicator hA).toLp
      (A.indicator fun y => spectralHeatRow s t x y)‖ ≤
    ‖((Lp.memLp (spectralHeatRow s t x)).indicator hB).toLp
      (B.indicator fun y => spectralHeatRow s t x y)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [((Lp.memLp (spectralHeatRow s t x)).indicator hA).coeFn_toLp,
    ((Lp.memLp (spectralHeatRow s t x)).indicator hB).coeFn_toLp] with z hzA hzB
  rw [hzA, hzB]
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hAB hz)]
  · simp [hz]

#print axioms c12_restricted_spectral_row_mono

/-- A fixed exterior radius yields an almost-everywhere off-diagonal bound
for the native spectral kernel at twice the row time. -/
theorem c12_fixed_radius_spectral_kernel_bound_ae {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C M : ℝ, 0 < C ∧ 0 < M ∧ ∀ {R : ℝ} (hR : 0 < R)
      {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) ∧
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
      (ha : 1 ≤ r^2 / (192 * κ⁻¹^2 * t)),
      ∀ᵐ x ∂dirichletVolume ρ R, ∀ᵐ y ∂dirichletVolume ρ R,
        x ∈ sourceBall (0 : Vec d) R → y ∈ sourceBall (0 : Vec d) R →
        6*r ≤ euclideanNorm (y-x) →
        K (t+t) x y ≤ 2 * κ⁻¹ * (M * t ^ (-(d : ℝ)/4)) *
          (C * t ^ (-(d : ℝ)/4) *
            Real.exp (-(r^2 / (192 * κ⁻¹^2 * t)) / 2)) := by
  obtain ⟨C, hC, hrow⟩ := c12_global_exterior_row_bound_ae hd hκ
  obtain ⟨N, hN, hfull⟩ := c12_supplied_heat_row_L2_decay_pointwise hd hκ
  refine ⟨C, Real.sqrt N, hC, Real.sqrt_pos.2 hN, ?_⟩
  intro R hR ρ α h K G hK s hs r t hr ht ha
  let m : ℝ := Real.sqrt N * t ^ (-(d : ℝ)/4)
  let b : ℝ := C * t ^ (-(d : ℝ)/4) *
    Real.exp (-(r^2 / (192 * κ⁻¹^2 * t)) / 2)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hnorm (x : Vec d) (hx : x ∈ sourceBall (0 : Vec d) R) :
      ‖spectralHeatRow s t x‖ ≤ m := by
    have hh := hfull R hR ρ α h K G hK s hs t ht x hx
    have hroot := Real.sqrt_le_sqrt hh
    rw [Real.sqrt_sq (norm_nonneg _)] at hroot
    have he := c12_dyadic_nash_sqrt N t (d : ℝ) hN.le ht 0
    simp only [pow_zero, div_one, mul_one] at he
    exact hroot.trans_eq he
  have hrows := hrow hR h K G hK s hs r t hr ht ha
  filter_upwards [hrows] with x hx
  filter_upwards [hrows] with y hy hxball hyball hdist
  apply c12_spectral_kernel_pair_from_exterior_rows hd hκ hR h K s
    (fun t ht x hx y hy => (hs t ht x hx y hy).2) t ht x y hxball hyball m b hm hb
    (hnorm x hxball) (hnorm y hyball)
  intro a ha'
  have hle : 3*r ≤ euclideanNorm (y-x)/2 := by linarith
  let A : Set (Vec d) := {z | euclideanNorm (y-x)/2 ≤ euclideanNorm (z-a)}
  let B : Set (Vec d) := {z | 3*r ≤ euclideanNorm (z-a)}
  have hA : MeasurableSet A := (isClosed_le continuous_const
    ((Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const))).measurableSet
  have hB : MeasurableSet B := (isClosed_le continuous_const
    ((Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const))).measurableSet
  have hAB : A ⊆ B := fun z hz => hle.trans hz
  have hmono := c12_restricted_spectral_row_mono s t a A B hA hB hAB
  have htail : ‖((Lp.memLp (spectralHeatRow s t a)).indicator hB).toLp
      (B.indicator fun z => spectralHeatRow s t a z)‖ ≤ b := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
    rcases ha' with rfl | rfl
    · exact hx hxball
    · exact hy hyball
  exact hmono.trans htail

#print axioms c12_fixed_radius_spectral_kernel_bound_ae

/-- A single exceptional set of pairs works simultaneously for every
positive rational exterior radius satisfying the tail threshold. -/
theorem c12_rational_radius_spectral_kernel_bound_ae {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C M : ℝ, 0 < C ∧ 0 < M ∧ ∀ {R : ℝ} (hR : 0 < R)
      {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) ∧
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (t : ℝ) (ht : 0 < t),
      ∀ᵐ x ∂dirichletVolume ρ R, ∀ᵐ y ∂dirichletVolume ρ R,
        ∀ q : ℚ, 0 < (q : ℝ) → 1 ≤ (q : ℝ)^2 / (192 * κ⁻¹^2 * t) →
        x ∈ sourceBall (0 : Vec d) R → y ∈ sourceBall (0 : Vec d) R →
        6*(q : ℝ) ≤ euclideanNorm (y-x) →
        K (t+t) x y ≤ 2 * κ⁻¹ * (M * t ^ (-(d : ℝ)/4)) *
          (C * t ^ (-(d : ℝ)/4) *
            Real.exp (-((q : ℝ)^2 / (192 * κ⁻¹^2 * t)) / 2)) := by
  obtain ⟨C, M, hC, hM, hfixed⟩ := c12_fixed_radius_spectral_kernel_bound_ae hd hκ
  refine ⟨C, M, hC, hM, ?_⟩
  intro R hR ρ α h K G hK s hs t ht
  have hq (q : ℚ) : ∀ᵐ x ∂dirichletVolume ρ R, ∀ᵐ y ∂dirichletVolume ρ R,
      0 < (q : ℝ) → 1 ≤ (q : ℝ)^2 / (192 * κ⁻¹^2 * t) →
      x ∈ sourceBall (0 : Vec d) R → y ∈ sourceBall (0 : Vec d) R →
      6*(q : ℝ) ≤ euclideanNorm (y-x) →
      K (t+t) x y ≤ 2 * κ⁻¹ * (M * t ^ (-(d : ℝ)/4)) *
        (C * t ^ (-(d : ℝ)/4) *
          Real.exp (-((q : ℝ)^2 / (192 * κ⁻¹^2 * t)) / 2)) := by
    by_cases hp : 0 < (q : ℝ)
    · by_cases ha : 1 ≤ (q : ℝ)^2 / (192 * κ⁻¹^2 * t)
      · filter_upwards [hfixed hR h K G hK s hs (q : ℝ) t hp ht ha] with x hx
        filter_upwards [hx] with y hy hp' ha'
        exact hy
      · exact Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun y _ ha' => False.elim (ha ha')
    · exact Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun y hp' => False.elim (hp hp')
  have hx : ∀ᵐ x ∂dirichletVolume ρ R,
      ∀ q : ℚ, ∀ᵐ y ∂dirichletVolume ρ R,
      0 < (q : ℝ) → 1 ≤ (q : ℝ)^2 / (192 * κ⁻¹^2 * t) →
      x ∈ sourceBall (0 : Vec d) R → y ∈ sourceBall (0 : Vec d) R →
      6*(q : ℝ) ≤ euclideanNorm (y-x) →
      K (t+t) x y ≤ 2 * κ⁻¹ * (M * t ^ (-(d : ℝ)/4)) *
        (C * t ^ (-(d : ℝ)/4) *
          Real.exp (-((q : ℝ)^2 / (192 * κ⁻¹^2 * t)) / 2)) :=
    ae_all_iff.mpr hq
  filter_upwards [hx] with x hx
  exact ae_all_iff.mpr hx

#print axioms c12_rational_radius_spectral_kernel_bound_ae

/-- A rational radius comparable to a sufficiently large separation satisfies
both the geometric separation and the initial-tail threshold. -/
theorem c12_choose_far_rational_radius (D κ t : ℝ) (hD : 0 < D)
    (hκ : 0 < κ) (ht : 0 < t)
    (hfar : 27648 * κ⁻¹^2 * t ≤ D^2) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ 6 * (q : ℝ) ≤ D ∧
      1 ≤ (q : ℝ)^2 / (192 * κ⁻¹^2 * t) ∧
      -( (q : ℝ)^2 / (192 * κ⁻¹^2 * t)) / 2 ≤
        -(D^2 / (55296 * κ⁻¹^2 * t)) := by
  have hlt : D / 12 < D / 6 := by linarith
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hlt
  have hq : 0 < (q : ℝ) := by linarith
  have hk : 0 < κ⁻¹^2 := by positivity
  have hden : 0 < 192 * κ⁻¹^2 * t := by positivity
  have hsq : D^2 ≤ 144 * (q : ℝ)^2 := by nlinarith [sq_nonneg (D / 12 + (q : ℝ))]
  refine ⟨q, hq, by linarith, ?_, ?_⟩
  · apply (le_div_iff₀ hden).2
    nlinarith
  · have hb : D^2 / (144 * (192 * κ⁻¹^2 * t)) ≤
        (q : ℝ)^2 / (192 * κ⁻¹^2 * t) := by
      apply (div_le_div_iff₀ (by positivity) hden).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hden.le]
    have he : D^2 / (144 * (192 * κ⁻¹^2 * t)) / 2 =
        D^2 / (55296 * κ⁻¹^2 * t) := by ring
    linarith

#print axioms c12_choose_far_rational_radius

/-- The simultaneous rational-radius bounds yield Gaussian decay for all
sufficiently separated pairs outside a single null set. -/
theorem c12_far_spectral_kernel_bound_ae {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C M : ℝ, 0 < C ∧ 0 < M ∧ ∀ {R : ℝ} (hR : 0 < R)
      {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) ∧
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (t : ℝ) (ht : 0 < t),
      ∀ᵐ x ∂dirichletVolume ρ R, ∀ᵐ y ∂dirichletVolume ρ R,
        x ∈ sourceBall (0 : Vec d) R → y ∈ sourceBall (0 : Vec d) R →
        27648 * κ⁻¹^2 * t ≤ (euclideanNorm (y-x))^2 →
        K (t+t) x y ≤ 2 * κ⁻¹ * (M * t ^ (-(d : ℝ)/4)) *
          (C * t ^ (-(d : ℝ)/4) *
            Real.exp (-(euclideanNorm (y-x))^2 / (55296 * κ⁻¹^2 * t))) := by
  obtain ⟨C, M, hC, hM, hrat⟩ := c12_rational_radius_spectral_kernel_bound_ae hd hκ
  refine ⟨C, M, hC, hM, ?_⟩
  intro R hR ρ α h K G hK s hs t ht
  filter_upwards [hrat hR h K G hK s hs t ht] with x hx
  filter_upwards [hx] with y hy hxball hyball hfar
  have hD : 0 < euclideanNorm (y-x) := by
    have hn : 0 ≤ euclideanNorm (y-x) := Real.sqrt_nonneg _
    have hp : 0 < 27648 * κ⁻¹^2 * t := by positivity
    nlinarith
  obtain ⟨q, hq, hsep, hthreshold, hexp⟩ :=
    c12_choose_far_rational_radius (euclideanNorm (y-x)) κ t hD hκ ht hfar
  have hh := hy q hq hthreshold hxball hyball hsep
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using hexp

#print axioms c12_far_spectral_kernel_bound_ae

/-- A uniform near-diagonal estimate and an exponentially decaying far
estimate combine into one Gaussian envelope. -/
theorem c12_combine_near_far_bound (k U F Q a : ℝ)
    (hU : 0 ≤ U) (hF : 0 ≤ F) (hQ : 0 ≤ Q)
    (hnear : k ≤ U * Q)
    (hfar : (1 / 2 : ℝ) ≤ a → k ≤ F * Q * Real.exp (-a)) :
    k ≤ (F + Real.exp 1 * U) * Q * Real.exp (-a) := by
  by_cases h : (1 / 2 : ℝ) ≤ a
  · have hh := hfar h
    calc
      k ≤ F * Q * Real.exp (-a) := hh
      _ ≤ (F + Real.exp 1 * U) * Q * Real.exp (-a) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ hQ
        nlinarith [mul_nonneg (Real.exp_pos 1).le hU]
  · have he : 1 ≤ Real.exp 1 * Real.exp (-a) := by
      calc
        1 = Real.exp 0 := by simp
        _ ≤ Real.exp (1 + -a) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp 1 * Real.exp (-a) := Real.exp_add _ _
    have hUQ : 0 ≤ U * Q := mul_nonneg hU hQ
    have hh : U * Q ≤ U * Q * (Real.exp 1 * Real.exp (-a)) := by
      nlinarith [mul_nonneg hUQ (sub_nonneg.mpr he)]
    calc
      k ≤ U * Q := hnear
      _ ≤ U * Q * (Real.exp 1 * Real.exp (-a)) := hh
      _ ≤ (F + Real.exp 1 * U) * Q * Real.exp (-a) := by
        nlinarith [mul_nonneg (mul_nonneg hF hQ) (Real.exp_pos (-a)).le]

#print axioms c12_combine_near_far_bound

/-- The native spectral kernel has an almost-everywhere Gaussian envelope,
uniform in the domain and coefficients. -/
theorem c12_spectral_gaussian_envelope_ae {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ {R : ℝ} (hR : 0 < R)
      {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          Summable (fun n => Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y) ∧
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (t : ℝ) (ht : 0 < t),
      ∀ᵐ x ∂dirichletVolume ρ R, ∀ᵐ y ∂dirichletVolume ρ R,
        x ∈ sourceBall (0 : Vec d) R → y ∈ sourceBall (0 : Vec d) R →
        K (t+t) x y ≤ A * t ^ (-(d : ℝ)/2) *
          Real.exp (-(euclideanNorm (y-x))^2 / (B*t)) := by
  obtain ⟨C, M, hC, hM, hfar⟩ := c12_far_spectral_kernel_bound_ae hd hκ
  obtain ⟨U, hU, hnear⟩ := c12_supplied_kernel_ultracontractive hd hκ
  let p : ℝ := -(d : ℝ)/2
  let F : ℝ := 2 * κ⁻¹ * M * C
  let V : ℝ := U * (2 : ℝ)^p
  let B : ℝ := 55296 * κ⁻¹^2
  refine ⟨F + Real.exp 1 * V, B, by dsimp [F, V]; positivity,
    by dsimp [B]; positivity, ?_⟩
  intro R hR ρ α h K G hK s hs t ht
  filter_upwards [hfar hR h K G hK s hs t ht] with x hx
  filter_upwards [hx] with y hy hxball hyball
  let D : ℝ := euclideanNorm (y-x)
  let z : ℝ := D^2 / (B*t)
  have hBt : 0 < B*t := by dsimp [B]; positivity
  have hz : 0 ≤ z := div_nonneg (sq_nonneg D) hBt.le
  have hp : t ^ (-(d : ℝ)/4) * t ^ (-(d : ℝ)/4) = t ^ p := by
    rw [← Real.rpow_add ht]
    congr 1 <;> dsimp [p] <;> ring
  have hnear' : K (t+t) x y ≤ V * t ^ p := by
    have hh := hnear R hR ρ α h K G hK (t+t) (by positivity) x hxball y hyball
    have he : t+t = 2*t := by ring
    rw [he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le] at hh
    dsimp [V, p] at *
    simpa only [he, mul_assoc] using hh
  have hfar' : (1/2 : ℝ) ≤ z → K (t+t) x y ≤ F * t ^ p * Real.exp (-z) := by
    intro hzfar
    have hdistance : 27648 * κ⁻¹^2 * t ≤ D^2 := by
      have hh := (le_div_iff₀ hBt).mp hzfar
      dsimp [B] at hh
      nlinarith
    have hh := hy hxball hyball hdistance
    dsimp [F, z, B, D, p] at *
    rw [← hp]
    convert hh using 1 <;> ring
  have hh := c12_combine_near_far_bound (K (t+t) x y) V F (t ^ p) z
    (by dsimp [V]; positivity) (by dsimp [F]; positivity) (by positivity) hnear' hfar'
  simpa only [F, V, B, z, D, p, neg_div] using hh

#print axioms c12_spectral_gaussian_envelope_ae

/-- The spectral Gaussian envelope extends from almost every pair to every
interior pair. -/
theorem c12_spectral_gaussian_envelope_pointwise {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ {R : ℝ} (hR : 0 < R)
      {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (t : ℝ) (ht : 0 < t), ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
        K (t+t) x y ≤ κ⁻¹ * ((A * t ^ (-(d : ℝ)/2) *
          Real.exp (-(euclideanNorm (x-y))^2 / (B*t))) / κ) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := c12_spectral_gaussian_envelope_ae hd hκ
  refine ⟨A, B, hA, hB, ?_⟩
  intro R hR ρ α h K G hK t ht
  obtain ⟨s, hs⟩ := hK.2
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    change volume.restrict (sourceBall (0 : Vec d) R) ≪
      (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun y => ENNReal.ofReal (ρ y))
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun y => ne_of_gt
      (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hκ (h.2.2 y).1))
  have hball : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      x ∈ sourceBall (0 : Vec d) R := ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet
  have hae := hac.ae_le (hbound hR h K G hK s hs t ht)
  have hvol : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      ∀ᵐ y ∂volume.restrict (sourceBall (0 : Vec d) R),
        K (t+t) x y ≤ A * t ^ (-(d : ℝ)/2) *
          Real.exp (-(euclideanNorm (x-y))^2 / (B*t)) := by
    filter_upwards [hae, hball] with x hx hxb
    filter_upwards [hac.ae_le hx, hball] with y hy hyb
    have hn : euclideanNorm (y-x) = euclideanNorm (x-y) := by
      rw [← neg_sub x y]
      simpa using TimeChange.euclideanNorm_smul (-1 : ℝ) (x-y)
    simpa only [hn] using hy hxb hyb
  exact c12_supplied_gaussian_envelope_pointwise hκ h K G hK (t+t)
    (A * t ^ (-(d : ℝ)/2)) (B*t) (by positivity) (by positivity) hvol

#print axioms c12_spectral_gaussian_envelope_pointwise

/-- Uniform Gaussian upper bound for the supplied spectral Dirichlet kernel. -/
theorem c12_native_weighted_gaussian_upper (d : ℕ) (hd : 2 ≤ d)
    (κ R : ℝ) (hκ : 0 < κ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      K t x y ≤ C * Real.rpow t (-(d : ℝ)/2) *
        Real.exp (-(euclideanNorm (x-y))^2/(C*t)) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := c12_spectral_gaussian_envelope_pointwise hd hκ
  let p : ℝ := -(d : ℝ)/2
  let P : ℝ := κ⁻¹ * (A * ((1/2 : ℝ) ^ p) / κ)
  let Q : ℝ := 2 * B
  let C : ℝ := P + Q + 1
  have hP : 0 < P := by dsimp [P]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ρ α h K G hK t ht x hx y hy
  have hh := hbound hR h K G hK (t/2) (by positivity) x hx y hy
  have htime : t/2+t/2 = t := by ring
  rw [htime] at hh
  have hrpow : (t/2) ^ p = (1/2 : ℝ)^p * t^p := by
    have he : t/2 = (1/2 : ℝ)*t := by ring
    rw [he, Real.mul_rpow (by norm_num) ht.le]
  have hden : B * (t/2) = Q*t/4 := by dsimp [Q]; ring
  have hratio : -(euclideanNorm (x-y))^2 / (B*(t/2)) ≤
      -(euclideanNorm (x-y))^2 / (C*t) := by
    have hbt : 0 < B*(t/2) := by positivity
    have hct : 0 < C*t := by positivity
    have hle : B*(t/2) ≤ C*t := by dsimp [C, Q]; nlinarith
    have hn : 0 ≤ (euclideanNorm (x-y))^2 := sq_nonneg _
    apply (div_le_div_iff₀ hbt hct).2
    nlinarith
  have hexp := Real.exp_le_exp.mpr hratio
  have hp : 0 ≤ t^p := Real.rpow_nonneg ht.le _
  have hPC : P ≤ C := by dsimp [C]; linarith
  have hcoeff : P*t^p ≤ C*t^p := mul_le_mul_of_nonneg_right hPC hp
  have hbase : K t x y ≤ P*t^p * Real.exp (-(euclideanNorm (x-y))^2/(B*(t/2))) := by
    rw [show (t/2) ^ (-(d : ℝ)/2) = (t/2)^p by rfl, hrpow] at hh
    dsimp [P]
    convert hh using 1 <;> ring
  calc
    K t x y ≤ P*t^p * Real.exp (-(euclideanNorm (x-y))^2/(B*(t/2))) := hbase
    _ ≤ P*t^p * Real.exp (-(euclideanNorm (x-y))^2/(C*t)) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hP.le hp)
    _ ≤ C*t^p * Real.exp (-(euclideanNorm (x-y))^2/(C*t)) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le

#print axioms c12_native_weighted_gaussian_upper

end EinsteinFull.Calculus
